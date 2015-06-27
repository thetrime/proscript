/* Need to implement recorda/3, recorded/3 and erase/1 */
var database_ptr = 0;
var database_references = {};
var databases = {};

/* 
   Because we don't have access to pointers in Javascript, this is quite hard to do efficiently. It's quite hard to do at all!
   database_references contains a key-value pair with uniquely generated integer keys. The key is returned as a clause reference.
   The database_reference:value is an object containing two values: Array and Index.
   Array is a key into the databases object. The database:value is an array. Index is the index into that array of the actual value
   stored in the clause reference.
   Eventually I will move the code into databases[0]
*/

function recorda(key, term, ref)
{
    // Get the database associated with key. 
    var d = databases[key];
    var i = 0;
    debug_msg("recording...");
    if (d === undefined)
    {
        debug_msg("Creating new database...");
        // No such database yet. Create one, and store it in databases
        databases[key] = {data:{},
                          keys:new Array(),
                          ptr: 0};
        d = databases[key];
        debug_msg("Created databases[" + key + "] as " + JSON.stringify(databases[key]));
    }
    else
    {
        i = d.ptr;
    }
    debug_msg("Storing value with key " + i + " and reference " + database_ptr);
    // Now store the term in d at i
    d.data[i] = {value: record_term(term),
                 ref: database_ptr};
    // And finally, store the key in the keys arrays, putting it at the front
    d.keys.unshift(i);

    debug_msg("stored " + JSON.stringify(d));
    
    d.ptr++;
    // Next, save the clause reference in database_references
    database_references[database_ptr] = {array: key,
                                         index: i};
    debug_msg("database_references[" + database_ptr + "] = " + JSON.stringify(database_references[database_ptr]));
    // And now we can unify it with ref
    var result = unify(ref, database_ptr ^ (TAG_INT << WORD_BITS));
    // And increment it
    database_ptr++;
    return result;
}


function recordz(key, term, ref)
{
    // Get the database associated with key. 
    var d = databases[key];
    var i = 1;
    debug_msg("recording...");
    if (d === undefined)
    {
        debug_msg("Creating new database...");
        // No such database yet. Create one, and store it in databases
        databases[key] = {data:{},
                          keys:new Array(),
                          ptr: 0};
        d = databases[key];
        debug_msg("Created databases[" + key + "] as " + JSON.stringify(databases[key]));
    }
    else
    {
        i = d.ptr;
    }
    debug_msg("Storing value with key " + i + " and reference " + database_ptr);
    // Now store the term in d at i
    d.data[i] = {value: record_term(term),
                 ref: database_ptr};
    // And finally, store the key in the keys arrays, putting it at the front
    d.keys.push(i);

    debug_msg("stored " + JSON.stringify(d));
    
    databases[key].ptr++;
    // Next, save the clause reference in database_references
    database_references[database_ptr] = {array: key,
                                         index: i};
    // And now we can unify it with ref
    var result = unify(ref, database_ptr ^ (TAG_INT << WORD_BITS));
    // And increment it
    database_ptr++;
    return result;
}

function recorded(key, term, ref)
{
    debug_msg("Retrieving");
    // Ok, first find the database
    var d = databases[key];
    // Check if there is anything recorded. If not, fail.
    if (d === undefined)
    {
        debug_msg("No terms");
        return false; 
    }
    // Ok, now we can get the actual array
    var data = d.data;
    // We need the first actual key. This may not be [0] if something has been erased
    debug_msg("Keys: " + JSON.stringify(Object.keys(data)));
    var index = d.keys[0];
    debug_msg("Returning reference " + d.data[index].ref);
    var result = unify(recall_term(d.data[index].value, {}), term) && unify(d.data[index].ref ^ (TAG_INT << WORD_BITS), ref);
    debug_msg("Result: " + result + " => " + term_to_string(term) + " ====> " + term_to_string(ref));
    return result;
}

function erase(ref)
{
    // First find the array
    debug_msg("Erasing reference " + VAL(ref));
    var dr = database_references[VAL(ref)];
    if (dr === undefined)
        return false;
    debug_msg("Got reference " + JSON.stringify(dr));
    var d = databases[dr.array];
    debug_msg("Got database " + d);
    // Now set to undefined
    delete d.data[dr.index];
    // Now we must also delete the keys entry. This requires a search, unfortunately since there is no way to keep track of indices if we allow unshifting
    debug_msg("Deleting key " + dr.index);
    for (i = 0; i < d.keys.length; i++)
    {
        if (d.keys[i] == dr.index)
        {
            d.keys.splice(i, 1);
            break;
        }
    }

    debug_msg("Success");
    return true;
}

// record_term returns a new object which is a javascript representation of the term
function record_term(t)
{
    t = deref(t);
    switch(TAG(t))
    {
    case TAG_REF:
        return {type: TAG_REF,
                key: VAL(t)};
    case TAG_ATM:
        return {type: TAG_ATM,
                value: atable[VAL(t)]};
    case TAG_FLT:
        return {type: TAG_FLT,
                value: floats[VAL(t)]};
    case TAG_INT:
        return {type: TAG_INT,
                value: VAL(t)};
    case TAG_LST:
        var value = [];
        var list = {type: TAG_LST,
                    value: value};
        while (TAG(t) == TAG_LST)
        {
            value.push(record_term(VAL(t)));
            t = memory[VAL(t)+1];
        }
        list.tail = record_term(t);
        return list;
    case TAG_STR:
        var ftor = ftable[VAL(memory[VAL(t)])];
        var args = [];
        var result = {type: TAG_STR,
                      name: atable[ftor[0]],
                      args: args};        
        for (var i = 0; i < ftor[1]; i++)
        {
            args.push(record_term(memory[VAL(t)+1+i]));
        }       
        return result;
    }
}

function recall_term(e, varmap)
{
    // return a reference to an equivalent WAM term to the expression e
    switch(e.type)
    {
    case TAG_REF:
        var result;
        if (varmap[e.key] !== undefined)
        {
            result = state.H;            
            memory[state.H] = varmap[e.key];
            state.H++;
        }
        else
        {
            result = alloc_var();
            varmap[e.key] = result;            
        }
        return result;
    case TAG_ATM:
        return lookup_atom(e.value);
    case TAG_FLT:
        return lookup_float(e.value);
    case TAG_INT:
        return e.value ^ (TAG_INT << WORD_BITS);
    case TAG_LST:
        var result = alloc_var();
        var tail = result;
        var head;
        for (var i = 0; i < e.value.length; i++)
        {
            unify(tail, state.H ^ (TAG_LST << WORD_BITS));
            head = alloc_var();
            tail = alloc_var();
            unify(head, recall_term(e.value[i], varmap));
        }
        unify(tail, recall_term(e.tail, varmap));
        return result;    
    case TAG_STR:
        var t = (state.H ^ TAG_STR << WORD_BITS);
        memory[state.H++] = lookup_functor(e.name, e.args.length);
        // Reserve space for the args
        var var_args = [];
        for (var i = 0; i < e.args.length; i++)
            var_args[i] = alloc_var();
        for (var i = 0; i < e.args.length; i++)
        {
            z = recall_term(e.args[i], varmap);
            unify(z, var_args[i]);
        }
        return t;
    default:
        abort("invalid term type: " + JSON.stringify(e));
    }
}
