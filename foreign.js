// Round toward zero by default
function round(a)
{
    if (a < 0)
        return Math.ceil(a);
    else
        return Math.floor(a);
}


function evaluate_expression(expression, evaluated)
{
    expression = deref(expression);
    if (TAG(expression) == TAG_INT)
    {
        if ((VAL(expression) & (1 << (WORD_BITS-1))) == (1 << (WORD_BITS-1)))
            evaluated.value = VAL(expression) - (1 << WORD_BITS);
        else
            evaluated.value = VAL(expression);
        return true;
    }
    if (TAG(expression) == TAG_FLT)
    {
        evaluated.value = floats[VAL(expression)];
        return true;
    }
    if (TAG(expression) == TAG_REF)
    {
        return instantiation_error(expression);
    }
    else if (TAG(expression) == TAG_ATM && expression == lookup_atom("pi"))
    {
        evaluated.value = Math.PI;
        return true;
    }
    else if (TAG(expression) == TAG_STR)
    {
        var v = [];
        var value = 0;
        var arity = ftable[VAL(memory[VAL(expression)])][1];
        var name = atable[ftable[VAL(memory[VAL(expression)])][0]];
        for (var i = 0; i < arity; i++)
        {
            var t = {};
            if (!evaluate_expression(memory[VAL(expression)+i+1], t))
                return false;
            else
                v[i] = t.value;
        }
        if (name == "+" && arity == 2)
            evaluated.value = v[0] + v[1];
        else if (name == "-" && arity == 2)
            evaluated.value = v[0] - v[1];
        else if (name == "*" && arity == 2)
            evaluated.value = v[0] * v[1];
        else if (name == "//" && arity == 2)
            evaluated.value = ~~(v[0] / v[1]);
        else if (name == "/" && arity == 2)
            evaluated.value = v[0] / v[1];
        else if (name == "rem" && arity == 2)
        {
            if (v[1] == 0)
                return evaluation_error("zero_divisor");
            evaluated.value = v[0] - (round(v[0]/v[1]) * v[1]);            
        }
        else if (name == "mod" && arity == 2)
        {
            if (v[1] == 0)
                return evaluation_error("zero_divisor");            
            evaluated.value = v[0] - (Math.floor(v[0]/v[1]) * v[1]);
        }
        else if (name == "-" && arity == 1)
            evaluated.value = -v[0];
        else if (name == "abs" && arity == 1)
            evaluated.value = Math.abs(v[0]);
        else if (name == "sign" && arity == 1)
        {
            if (v[0] == 0)
                evaluated.value = 0;
            else if (v[0] > 0)
                evaluated.value = 1;
            else
                evaluated.value = -1;
        }
        else if (name == "float_integer_part" && arity == 1)
            evaluated.value = ~~v[0];
        else if (name == "float_fractional_part" && arity == 1)
            evaluated.value = v[0] % 1;
        else if (name == "float" && arity == 1)
            evaluated.value = v[0];
        else if (name == "floor" && arity == 1)
            evaluated.value = Math.floor(v[0]);
        else if (name == "truncate" && arity == 1)
            evaluated.value = ~~v[0];
        else if (name == "round" && arity == 1)
            evaluated.value = Math.round(v[0]);
        else if (name == "ceiling" && arity == 1)
            evaluated.value = Math.ceil(v[0]);
        else if (name == "**" && arity == 2)
            evaluated.value = Math.pow(v[0], v[1]);
        else if (name == "sin" && arity == 1)
            evaluated.value = Math.sin(v[0]);
        else if (name == "cos" && arity == 1)
            evaluated.value = Math.cos(v[0]);
        else if (name == "atan" && arity == 1)
            evaluated.value = Math.atan(v[0]);
        else if (name == "exp" && arity == 1)
            evaluated.value = Math.exp(v[0]);
        else if (name == "log" && arity == 1)
            evaluated.value = Math.log(v[0]);
        else if (name == "sqrt" && arity == 1)
            evaluated.value = Math.sqrt(v[0]);
        else if (name == ">>" && arity == 2)
            evaluated.value = v[0] >> [v1];
        else if (name == "<<" && arity == 2)
            evaluated.value = v[0] << [v1];
        else if (name == "/\\" && arity == 2)
            evaluated.value = v[0] & [v1];
        else if (name == "\\/" && arity == 2)
            evaluated.value = v[0] | [v1];
        else if (name == "\\" && arity == 1)
            evaluated.value = ~v[0];
        // Corrigendum
        else if (name == "+" && arity == 1)
            evaluated.value = v[0];
        else if (name == "max" && arity == 2)
            evaluated.value = Math.max(v[0], v[1]);
        else if (name == "min" && arity == 2)
            evaluated.value = Math.min(v[0], v[1]);
        else if (name == "acos" && arity == 2)
            evaluated.value = Math.acos(v[0], v[1]);
        else if (name == "asin" && arity == 2)
            evaluated.value = Math.asin(v[0], v[1]);
        else if (name == "tan" && arity == 2)
            evaluated.value = Math.tan(v[0], v[1]);
        else if (name == "xor" && arity == 2)
            evaluated.value = v[0] ^ v[1];
        else if (name == "atan2" && arity == 2)
            evaluated.value = Math.atan2(v[0], v[1]);
        else if (name == "^" && arity == 2)
            evaluated.value = Math.pow(v[0], v[1]);
        else if (name == "div" && arity == 2)
        {
            if (v[1] == 0)
                return evaluation_error("zero_divisor");
            evaluated.value = round(v[0] /v[1]);        
        }
        else
        {
            var indicator = state.H ^ (TAG_STR << WORD_BITS);
            memory[state.H++] = lookup_functor("/", 2);
            memory[state.H++] = lookup_atom(name);
            memory[state.H++] = arity ^ (TAG_INT << WORD_BITS);
            return type_error("evaluable", indicator)
        }
        return true;            
    }
    else if (TAG(expression) == TAG_ATM)
    {
        var indicator = state.H ^ (TAG_STR << WORD_BITS);
        memory[state.H++] = lookup_functor("/", 2);
        memory[state.H++] = expression;
        memory[state.H++] = 0 ^ (TAG_INT << WORD_BITS);
        return type_error("evaluable", indicator)
    }
    else if (TAG(expression) == TAG_STR)
    {
        return type_error("evaluable", expression);
    }
    abort("Illegal type");
    return {status:0};
}

function term_from_list(list, tail)
{
    var tmp = state.H;
    for (var i = 0; i < list.length; i++)
    {
        alloc_list();
        memory[state.H++] = list[i];        
    }
    memory[state.H++] = tail;
    return memory[tmp];
}

function predicate_fail()
{
    return false;
}

function predicate_true()
{
    return true;
}


function predicate_is(value, expression)
{
    var e = {};
    if (!evaluate_expression(expression, e))
        return false;
//    if (e.status)
//        debug_msg("Evaluated " + term_to_string(expression) + " to " + e.value);
//    else
//        debug_msg("Failed to evaluate " + term_to_string(expression));
    // Note that e.value may be negative. Have to AND to get rid of any high bits
    if (e.value == ~~e.value)
    {
        // FIXME: Is this right?! This just truncates to WORD_BITS bits!
        e.value &= ((1 << WORD_BITS) -1);
        return (e.status != 0 && unify(e.value ^ (TAG_INT << WORD_BITS), value));
    }
    else
    {
        return (e.status != 0 && unify(lookup_float(e.value), value));
    }
}


function predicate_ne(a, b)
{
    var ae = {};
    var be = {};
    if (evaluate_expression(a, ae) && evaluate_expression(b, be))
        return ae.value != be.value;
    return false;
}

function predicate_gt(a, b)
{
    var ae = {};
    var be = {};
    if (evaluate_expression(a, ae) && evaluate_expression(b, be))
        return ae.value > be.value;
    return false;
}

function predicate_lt(a, b)
{
    var ae = {};
    var be = {};
    if (evaluate_expression(a, ae) && evaluate_expression(b, be))
        return ae.value < be.value;
    return false;
}

function predicate_elt(a, b)
{
    var ae = {};
    var be = {};
    if (evaluate_expression(a, ae) && evaluate_expression(b, be))
        return ae.value <= be.value;
    return false;
}

function predicate_egt(a, b)
{
    var ae = {};
    var be = {};
    if (evaluate_expression(a, ae) && evaluate_expression(b, be))
    {
        debug(ae.value + " >= " + be.value);
        return ae.value >= be.value;
    }
    return false;
}


function predicate_eq(a, b)
{
    var ae = {};
    var be = {};
    if (evaluate_expression(a, ae) && evaluate_expression(b, be))
        return ae.value == be.value;
    return false;
}

function predicate_term_variables(t, vt)
{    
    return unify(term_from_list(term_variables(t), NIL), vt);
}

function term_variables(z)
{
    var pdl = [z];
    var vars = [];
    while (pdl.length != 0)
    {
        var t = deref(pdl.pop());
        if (TAG(t) == TAG_REF)
        {
            if (vars.indexOf(t) == -1)
            {
                vars.push(t);
            }
        }
        else if (TAG(t) == TAG_LST)
        {
            pdl.push(memory[VAL(t)+1]);
            pdl.push(memory[VAL(t)]);
        }
        else if (TAG(t) == TAG_STR)
        {
            ftor = VAL(memory[VAL(t)]);
            for (var i = ftable[ftor][1]-1; i >= 0 ; i--)
                pdl.push(memory[VAL(t) + 1 + i]);
        }
    }
    return vars;
}

function writeln(t)
{
    debug_msg("writeln(" + hex(t) +")");
    debug_msg("memory[" + VAL(t) +"] = " + hex(memory[VAL(t)]));
    stdout(format_term(t, {numbervars: true, ignore_ops: false, quoted:false}) + "\n");
    return true;
}

function predicate_halt(n)
{
    state.running = false;
    return true;
}

function predicate_univ(term, list_term)
{
    debug_msg("Univ : " + hex(term));
    debug_msg(" ...... = " + term_to_string(term));
    if (term & M_BIT)
        abort("GC exception: M bit is still set");
    switch(TAG(term))
    {
    case TAG_ATM:
    case TAG_INT:
    case TAG_FLT:
        var list = term_from_list([term], NIL);
        return unify(list_term, list);
    case TAG_REF:
        // Save space on heap for ftor
        var tmp = state.H;
        state.H++;
        var arity = 0;
        if (TAG(list_term) != TAG_LST)
            return type_error("list", list_term);
        if (TAG(deref(memory[VAL(list_term)])) != TAG_ATM)
            return type_error("atom", deref(memory[VAL(list_term)]));
        var ftor_name = atable[VAL(deref(memory[VAL(list_term)]))];
        list_term = memory[VAL(list_term)+1];
        // Now write the args
        while (TAG(list_term) == TAG_LST)
        {
            // Write head
            memory[state.H++] = memory[VAL(list_term)];
            // Update tail
            list_term = memory[VAL(list_term)+1];
            arity++;
        }
        // Check tail
        if (list_term != NIL)
        {
            if (TAG(list_term) == TAG_REF)
                return instantiation_error(list_term);
            else
                return type_error("list", list_term);
        }
        memory[tmp] = lookup_functor(ftor_name, arity);
        return unify(term, tmp ^ (TAG_STR << WORD_BITS));
    case TAG_STR:
        var ftor = VAL(memory[VAL(term)]);
        if (ftable[ftor] === undefined)
            abort("Garbage functor " + hex(ftor) + " pointed at by " + hex(term));
        var list = [ftable[ftor][0] ^ (TAG_ATM << WORD_BITS)];
        for (var i = 0; i < ftable[ftor][1]; i++)
        {
            debug_msg("Arg " + i + " is at " + (VAL(term)+1+i) + " and has value " + hex(memory[VAL(term)+1+i]));
            list.push(memory[VAL(term)+1+i]);
        }
        return unify(list_term, term_from_list(list, NIL));
    case TAG_LST:
        var list = [lookup_atom(".")];
        list.push(memory[VAL(term)]);
        list.push(memory[VAL(term)+1]);
        return unify(list_term, term_from_list(list, NIL));
    }
}

function predicate_functor(term, name, arity)
{
    switch(TAG(term))
    {
    case TAG_REF:
        if (TAG(name) == TAG_ATM && TAG(arity) == TAG_INT)
        {
            var name_string = atable[VAL(name)];
            var ftor = lookup_functor(name_string, VAL(arity));
            var t = state.H ^ (TAG_STR << WORD_BITS);
            memory[state.H++] = ftor;
            for (i = 0; i < VAL(arity); i++)
                alloc_var();
            return unify(term, t);
        }
        else if (TAG(name) == TAG_REF)
            return instantiation_error(name);
        else if (TAG(arity) == TAG_REF)
            return instantiation_error(arity);
        else if (TAG(name) != TAG_ATM)
            return type_error("atom", name);
        else if (TAG(arity) != TAG_INT)
            return type_error("integer", arity);
    case TAG_ATM:
    case TAG_INT:
    case TAG_FLT:
        return unify(name, term) && unify(arity, 0 ^ (TAG_INT << WORD_BITS));        
    case TAG_STR:
        var ftor = VAL(memory[VAL(term)]);
        return unify(name, ftable[ftor][0] ^ (TAG_ATM << WORD_BITS)) && unify(arity, ftable[ftor][1] ^ (TAG_INT << WORD_BITS));
    case TAG_LST:
        return unify(name, NIL) && unify(arity, 2 ^ (TAG_INT << WORD_BITS));        
    }
}

function predicate_arg(n, t, a)
{
    if (TAG(n) == TAG_REF)
        return instantiation_error(n);
    if (TAG(t) == TAG_REF)
        return instantiation_error(t);
    if (TAG(n) != TAG_INT)
        return type_error("integer", n);
    if (TAG(t) != TAG_STR)
        return type_error("compound", t);
    if (VAL(n) < 0)
        return domain_error("not_less_than_zero", n);
    var ftor = VAL(memory[VAL(t)]);
    if (VAL(n) == 0 || VAL(n) > ftable[ftor][1])
        return false;
    return unify(memory[VAL(t) + VAL(n)], a);
}

function predicate_var(v)
{
    return TAG(v) == TAG_REF;
}

function predicate_atom(v)
{
    return TAG(v) == TAG_ATM;
}

function predicate_integer(v)
{
    return TAG(v) == TAG_INT;
}

function predicate_float(v)
{
    return TAG(v) == TAG_FLT;
}

function predicate_compound(v)
{
    return TAG(V) == TAG_STR;
}

function predicate_ground(x)
{
    var args = [x];
    while(args.length > 0)
    {
        arg = args.pop();
        switch (TAG(arg))
        {
        case TAG_REF:
            return false;
        case TAG_INT:
        case TAG_FLT:
        case TAG_ATM:
            return true;
        case TAG_LST:
            args.push(memory[VAL(arg)]);
            args.push(memory[VAL(arg)+1]);
            continue;
        case TAG_STR:
            ftor = VAL(memory[VAL(arg)]);
            for (i = 0; i < ftable[ftor][1]; i++)
                args.push(memory[VAL(arg)+1+i]);
            continue;        
        }
    }
}

function predicate_unify(a, b)
{
    return unify(a,b);
}

function predicate_match(a, b)
{
    var match_pdl = [];
    match_pdl.push(a);
    match_pdl.push(b);
    while (match_pdl.length != 0)
    {
        var d1 = deref(match_pdl.pop());
        var d2 = deref(match_pdl.pop());
        if (d1 != d2)
        {
            type1 = TAG(d1);
            val1 = VAL(d1);
            type2 = TAG(d2);
            val2 = VAL(d2);          
            // If either is a variable or atomic then they must be equal in order to match. They are not equal if we get to this line, so bail.
            if (type1 == TAG_REF || type2 == TAG_REF || type2 == TAG_ATM || type2 == TAG_INT || type2 == TAG_FLT)
                return false;

            if (type1 != type2) // Types must be equal for matching
                return false;

            if (type1 == TAG_LST)
            {                        
                match_pdl.push(memory[val1]); // unify heads
                match_pdl.push(memory[val2]);
                match_pdl.push(memory[val1+1]); // unify tails
                match_pdl.push(memory[val2+1]);
            }
            else if (type1 == TAG_STR)
            {
                f1 = VAL(memory[val1]);
                f2 = VAL(memory[val2]);
                if (f1 == f2)
                {
                    for (var i = 0; i < ftable[f1][1]; i++)
                    {
                        match_pdl.push(val1 + 1 + i);
                        match_pdl.push(val2 + 1 + i);
                    }
                }
                else
                    return false;
            }
            else
                abort("Illegal tag");
        }
    }
    return true;
}

// gets the i-th arg of a term. First arg is index=1, not index=0.
function get_arg(term, index)
{
    return deref(memory[VAL(term) + index]);
}

function lookup_atom(name)
{
    var i;
    for (i = 0; i < atable.length; i++)
    {
        if (atable[i] == name)
            return i ^ (TAG_ATM << WORD_BITS);
    }
    i = atable.length;
    atable[i] = name;
    return i ^ (TAG_ATM << WORD_BITS);
}

function lookup_functor(name, arity) 
{
    var a = VAL(lookup_atom(name));
    var i;
    for (i = 0; i < ftable.length; i++)
        if (ftable[i][0] == a && ftable[i][1] == arity)
            return i ^ (TAG_ATM << WORD_BITS);
    i = ftable.length;
    ftable[i] = [a, arity];
    return i ^ (TAG_ATM << WORD_BITS);    
}


/* Memory files */
var memory_files = [];

function toByteArray(str)
{
    var byteArray = [];
    for (var i = 0; i < str.length; i++)
    {
        if (str.charCodeAt(i) <= 0x7F)
        {
            byteArray.push(str.charCodeAt(i));
        }
        else 
        {
            var h = encodeURIComponent(str.charAt(i)).substr(1).split('%');
            for (var j = 0; j < h.length; j++)
            {
                byteArray.push(parseInt(h[j], 16));
            }
        }
    }
    return byteArray;
}

function JSfromByteArray(byteArray)
{
    var str = '';
    for (var i = 0; i < byteArray.length; i++)
    {
        str +=  byteArray[i] <= 0x7F?
                byteArray[i] === 0x25 ? "%25" : // %
                String.fromCharCode(byteArray[i]) :
                "%" + byteArray[i].toString(16).toUpperCase();
    }
    return decodeURIComponent(str);
}

function fromByteArray(byteArray)
{
    var str = '';
    for (i = 0; i < byteArray.length; i++)
    {
        if (byteArray[i] <= 0x7F)
        {
            str += String.fromCharCode(byteArray[i]);
        }
        else
        {
            // Have to decode manually
            var ch = 0;
            var mask = 0x20;
            var j = 0;
            for (var mask = 0x20; mask != 0; mask >>=1 )
            {        
                var next = byteArray[j+1];
                if (next == undefined)
                {
                    abort("Unicode break in fromByteArray. The input is garbage");
                }
                ch = (ch << 6) ^ (next & 0x3f);
                if ((byteArray[i] & mask) == 0)
                    break;
                j++;
            }
            ch ^= (b & (0xff >> (i+3))) << (6*(i+1));
            str += String.fromCharCode(ch);
        }
    }
    return str;
}

function atom_to_memory_file(atom, memfile)
{
    var index = memory_files.length;
    memory_files[index] = {data:toByteArray(atable[VAL(atom)]),
                           ptr:0};
    var ftor = lookup_functor('$memory_file', 1);
    var ref = alloc_structure(ftor);
    memory[state.H++] = index ^ (TAG_INT << WORD_BITS);
    return unify(memfile, ref);
}

function memory_file_to_atom(memfile, atom)
{
    if (TAG(memfile) != TAG_STR)
        return type_error("memory_file", memfile);
    ftor = VAL(memory[VAL(memfile)]);
    if (atable[ftable[ftor][0]] == "$memory_file" && ftable[ftor][1] == 1)
    {
        f = memory_files[VAL(memory[VAL(memfile)+1])];        
        return unify(atom, lookup_atom(fromByteArray(f.data)));
    }
    return type_error("memory_file", memfile);
}

function new_memory_file(memfile)
{
    var index = memory_files.length;
    memory_files[index] = {data:[],
                           ptr:0};
    var ftor = lookup_functor('$memory_file', 1);
    var ref = alloc_structure(ftor);
    memory[state.H++] = index ^ (TAG_INT << WORD_BITS);
    return unify(memfile, ref);
}

function close_memory_file(stream)
{
    return true;
}

function read_memory_file(stream, size, count, buffer)
{
    var bytes_read = 0;
    var records_read;
    var memfile = memory_files[stream.data];
    for (records_read = 0; records_read < count; records_read++)
    {
        for (var b = 0; b < size; b++)
        {
            t = memfile.data[memfile.ptr++];            
            if (t === undefined)
                return records_read;
            buffer[bytes_read++] = t;
        }
    }
    return records_read;
}

function write_memory_file(stream, size, count, buffer)
{
    var bytes_written = 0;
    var records_written;
    var memfile = memory_files[stream.data];
    for (records_written = 0; records_written < count; records_written++)
    {
        for (var b = 0; b < size; b++)
        {
            memfile.data[memfile.ptr++] = buffer[bytes_written++];
        }
    }
    return records_written;
}

function tell_memory_file(stream)
{
    return memory_files[stream.data].ptr;
}


function open_memory_file(memfile, mode, stream)
{
    var index = streams.length;
    if (TAG(memfile) == TAG_REF)
        return instantiation_error(memfile);
    if (TAG(memfile) != TAG_STR || memory[VAL(memfile)] != lookup_functor("$memory_file", 1))
        return type_error("memory_file", memfile);
    var memindex = get_arg(memfile, 1);
    if (TAG(memindex) != TAG_INT)
        return type_error("memory_file", memfile);
    memindex = VAL(memindex);
    if (TAG(mode) == TAG_REF)
        return instantiation_error(mode);
    else if (TAG(mode) != TAG_ATM)
        return type_error("atom", mode);
    if (atable[VAL(mode)] == 'read')
    {
        streams[index] = new_stream(read_memory_file, null, null, close_memory_file, tell_memory_file, memindex);
        
    }
    else if (atable[VAL(mode)] == 'write')
    {
        streams[index] = new_stream(null, write_memory_file, null, close_memory_file, tell_memory_file, memindex);
    }
    else
        return type_error("io_mode", mode);
    var ftor = lookup_functor('$stream', 1);
    var ref = alloc_structure(ftor);
    memory[state.H++] = index ^ (TAG_INT << WORD_BITS);
    debug_msg("Allocated stream " + index + " from memory file " + get_arg(memfile, 1));
    return unify(stream, ref);   
}

function free_memory_file(memfile)
{
    var m = memory_files[VAL(get_arg(memfile, 1))];
    memory_files[m] = null;
    return true;
}

function emit_code(address, c)
{
    // Not checking. Lets assume we know what we are doing!
    compile_buffer[VAL(address)] = VAL(c);
    return true;
}

function predicate_lookup_atom(atom, index)
{
    return unify(VAL(atom) ^ (TAG_INT << WORD_BITS), index);
}

function predicate_lookup_float(f, index)
{
    return unify(VAL(f) ^ (TAG_INT << WORD_BITS), index);
}

function predicate_lookup_functor(fname, arity, index)
{
    if (atable[VAL(fname)] === undefined)
        abort("Atom out of range: " + hex(deref(fname)));
    var i;
    for (i = 0; i < ftable.length; i++)
    {
        if (ftable[i][0] == VAL(fname) && ftable[i][1] == VAL(arity))
        {
            return unify(index, i ^ (TAG_INT << WORD_BITS));            
        }
    }
    i = ftable.length;
    ftable[i] = [VAL(fname), VAL(arity)];
    return unify(index, i ^ (TAG_INT << WORD_BITS));
}


function predicate_trace_unify(a, b)
{
    stdout("tracing unification of " + hex(a) + " and " + hex(b) + "\n");
    stdout("before, LHS = " + term_to_string(a) + "\n");
    stdout("before, RHS = " + term_to_string(b) + "\n");
    if (unify(a,b))
    {
        stdout("after, LHS = " + term_to_string(a) + "\n");
        stdout("after, RHS = " + term_to_string(b) + "\n");
        return true;
    }
    stdout("Failed to unify\n");
    return false;
}

function predicate_op(precedence, fixity, name)
{
    var names
    if (TAG(fixity) == TAG_REF)
        return instantiation_error(fixity);
    if (TAG(precedence) == TAG_REF)
        return instantiation_error(precedence);
    if (TAG(precedence) != TAG_INT)
        return type_error("integer", precedence);

    var op_precedence = VAL(precedence);
    var fixity = atable[VAL(fixity)];
    if (op_precedence < 0 || op_precedence > 1200)
        return domain_error("operator_priority", precedence);

    if (TAG(name) == TAG_ATM)
    {
        var n = atable[VAL(name)];
        if (n == ",")
            return permission_error("modify", "operator", name);
        else if (op_name == "|" && op_precedence < 1001)
            return permission_error("modify", "operator", name);
        names = [n];
    }
    else if (TAG(name) == TAG_LST)
    {
        names = [];
        var head = name;
        while (TAG(head) == TAG_LST)
        {
            if (TAG(deref(memory[VAL(head)])) == TAG_ATM)
            {
                var n = atable[deref(memory[VAL(head)])];
                if (n == ",")
                    return permission_error("modify", "operator", name);
                else if (op_name == "|" && op_precedence < 1001)
                    return permission_error("modify", "operator", name);                
                names.push(n);
            }
            else
                return type_error("atom", head);                
        }
        if (head != NIL)
        {
            if (TAG(head) == TAG_REF)
                return instantiation_error(head);
            else
                return type_error("atom", head);
        }
    }
    else
        return type_error("list", name);

    for (var i = 0; i < names.length; i++)
    {
        var op_name = names[i];

        if (fixity == "fx" || fixity == "fy")
        {
            if (op_precedence == 0)
                prefix_operators[op_name] = undefined;
            else
                prefix_operators[op_name] = {precedence: op_precedence, fixity:fixity};
        }
        else
        {
            if (op_precedence == 0)
                infix_operators[op_name] = undefined;
            else
                infix_operators[op_name] = {precedence: op_precedence, fixity:fixity};
        }
    } while (TAG(name) == TAG_LST);

    return true;
}

var gensyms = {};

function predicate_gensym(root, sym)
{
    if (gensyms[root] === undefined)
        gensyms[root] = 0;
    return unify(lookup_atom(atable[VAL(root)] + gensyms[root]), sym);
}

function prepend_clause_to_predicate(predicate, head, body)
{
    var predicate = VAL(lookup_functor(atable[VAL(deref(memory[VAL(predicate)+1]))], VAL(deref(memory[VAL(predicate)+2]))));
    if (predicates[predicate] === undefined)
    {
        // Easy case. New predicate. Add it to the table then set up the <NOP,0> header
        compile_buffer[0] = 254;
        compile_buffer[1] = 0;
        predicates[predicate] = {clauses: {0:{code:compile_buffer.slice(0), 
                                              key:0, 
                                              head:record_term(head), 
                                              body:record_term(body)}},
                                 clause_keys: [0],
                                 key:predicate,
                                 is_public: true,
                                 next_key: 1};
    }
    else
    {
        var first_key = predicates[predicate].clause_keys[0];
        var first_clause = predicates[predicate].clauses[first_key];
        if (first_clause.code[0] == 254)
        {
            // First clause was NOP - ie only clause. Make it trust_me, and the new clause is try_me_else
            compile_buffer[0] = 28;
            compile_buffer[1] = first_key;
            first_clause.code[0] = 30;
            first_clause.code[1] = 0;
            predicates[predicate].clauses[predicates[predicate].next_key] = {code:compile_buffer.slice(0),
                                                                             key: predicates[predicate].next_key,
                                                                             head:record_term(head), 
                                                                             body:record_term(body)};
            predicates[predicate].clause_keys.unshift(predicates[predicate].next_key);
            predicates[predicate].next_key++;
            
        }
        else if (first_clause.code[0] == 28)
        {
            // first clause was try_me_else. It becomes retry_me_else
            // Our new clause is try_me_else
            compile_buffer[0] = 28;
            compile_buffer[1] = first_key;
            first_clause.code[0] = 29;
            predicates[predicate].clauses[predicates[predicate].next_key] = {code:compile_buffer.slice(0),
                                                                             key: predicates[predicate].next_key,
                                                                             head:record_term(head), 
                                                                             body:record_term(body)};
            predicates[predicate].clause_keys.unshift(predicates[predicate].next_key);
            predicates[predicate].next_key++;            
        }
        else
            abort("Garbage clauses in prepend: " + first_clause.code[0]);
    }
    return true;
}

function check_compile_buffer(head, body)
{
    // Paranoia
    for (var z = 0; z < compile_buffer.length; z++)
    {
        if (compile_buffer[z] == null)
        {
            debug(term_to_string(head) + ":- " + term_to_string(body));
            debug(JSON.stringify(compile_buffer));
            abort("Illegal compile buffer: Address " + z + " is null!");
        }
    }
}
function add_clause_to_predicate(predicate, head, body)
{
    var predicate = VAL(lookup_functor(atable[VAL(deref(memory[VAL(predicate)+1]))], VAL(deref(memory[VAL(predicate)+2]))));
    if (predicates[predicate] === undefined)
    {
        // Easy case. New predicate. Add it to the table then set up the <NOP,0> header
        compile_buffer[0] = 254;
        compile_buffer[1] = 0;
        check_compile_buffer(head, body);
        predicates[predicate] = {clauses: {0:{code:compile_buffer.slice(0), 
                                              key:0, 
                                              head:record_term(head), 
                                              body:record_term(body)}},
                                 key:predicate,
                                 clause_keys: [0],
                                 is_public: true,
                                 next_key: 1};
    }
    else
    {
        var last_key = predicates[predicate].clause_keys[predicates[predicate].clause_keys.length-1];
        var last_clause = predicates[predicate].clauses[last_key];
        if (last_clause.code[0] == 254)
        {
            // Last clause was NOP - ie only clause. Make it try_me_else, and the new clause is trust_me
            last_clause.code[0] = 28;
            last_clause.code[1] = predicates[predicate].next_key;
            compile_buffer[0] = 30;
            compile_buffer[1] = 0;
            check_compile_buffer(head, body);            
            predicates[predicate].clauses[predicates[predicate].next_key] = {code:compile_buffer.slice(0),
                                                                             key: predicates[predicate].next_key,
                                                                             head:record_term(head), 
                                                                             body:record_term(body)};
            predicates[predicate].clause_keys.push(predicates[predicate].next_key);
            predicates[predicate].next_key++;
            
        }
        else if (last_clause.code[0] == 30)
        {
            // last clause was trust_me, so there is already a try_me_else. Make it retry_me_else and add new clause as trust_me
            last_clause.code[0] = 29;
            last_clause.code[1] = predicates[predicate].next_key;
            compile_buffer[0] = 30;
            compile_buffer[1] = 0;
            //compile_buffer.unshift(predicates[predicate].next_key); WHAT?
            check_compile_buffer(head, body);            
            predicates[predicate].clauses[predicates[predicate].next_key] = {code:compile_buffer.slice(0),
                                                                             key: predicates[predicate].next_key,
                                                                             head:record_term(head), 
                                                                             body:record_term(body)};
            predicates[predicate].clause_keys.push(predicates[predicate].next_key);
            predicates[predicate].next_key++;            
        }
        else
            abort("Garbage clauses: " + last_clause.code[0]);
    }

    return true;
}

function add_clause_to_aux(label, n, l, lt)
{
    debug_msg("Adding clause to aux: " + term_to_string(label) + " at " + VAL(n));
    if (TAG(label) == TAG_STR && memory[VAL(label)] == lookup_functor("defined", 1))
    {
        debug_msg("Aux code is at " + VAL(n));
        debug_msg("This is " + (VAL(n) ^ 0x80000000) & 0x7fffffff);
        add_clause_to_existing(VAL(memory[VAL(label)+1]), VAL(n) ^ 0x80000000);
        unify(l, lt);
    }
    else
    {
        debug_msg("Adding first clause");
        compile_buffer[VAL(n)] = 254;
        compile_buffer[VAL(n)+1] = 0;
        var ptr = state.H;
        memory[state.H++] = lookup_functor("defined", 1);
        memory[state.H++] = n;
        unify(label, ptr ^ (TAG_STR << WORD_BITS));

        var ptr2 = state.H;
        var ftor = lookup_functor("label", 2);
        memory[state.H++] = ftor;
        memory[state.H++] = label;
        memory[state.H++] = n;

        var ptr3 = state.H; // should unify with l
        memory[state.H++] = (ptr2) ^ (TAG_STR << WORD_BITS);

        var ptr4 = state.H;
        alloc_var();
        unify(ptr4, lt);

        unify(l, ptr3 ^ (TAG_LST << WORD_BITS));
    }
    return true;
}

function add_clause_to_existing(address, offset)
{
    while(true)
    {
        debug_msg("Examining address " + address + " with value " + compile_buffer[address] + " and offset " + offset) ;
        switch(compile_buffer[address])
        {
        case 254:
            // Change <NOP,0> -> try_me_else offset
            compile_buffer[address] = 28;
            compile_buffer[address+1] = offset;
            // Add <trust_me,0> for new clause
            compile_buffer[offset ^ 0x80000000] = 30;
            compile_buffer[(offset ^ 0x80000000)+1] = 0;
            return;
        case 30:
            // Change <trust_me,0> -> <retry_me_else, N>
            compile_buffer[address] = 29
            compile_buffer[address+1] = offset;
            // Add <trust_me,0> for new clause
            compile_buffer[offset ^ 0x80000000] = 30;
            compile_buffer[(offset ^ 0x80000000)+1] = 0;
            return;
        case 28:
        case 29:
            address = compile_buffer[address+1] ^ 0x80000000;
            break;
        default:
            abort("Garbage in code array: " + compile_buffer[address]);
        }        
    }
}


function create_choicepoint()
{
    // Create a choicepoint
    if (state.E > state.B)
    {
        newB = state.E + state.CP.code[state.CP.offset - 1] + 2;
        debug_msg("top frame is an environment at " + state.E + " state.CP.code[state.CP.offset-1] = " + state.CP.code[state.CP.offset-1]);
    } 
    else
    {
        debug_msg("top frame is a choicepoint at" + state.B);
        newB = state.B + memory[state.B] + 8;
    }
    debug_msg("Creating foreign choicepoint on the stack at " + newB);
    memory[newB] = state.num_of_args+2;
    var n = memory[newB];
    memory[newB + 1] = 0;
    debug_msg("Reserved @" + (newB + 1) + " for value");
    memory[newB + 2] = {code: code,
                        offset: state.P};
    debug_msg("Saving " + n + " args including the two specials");
    for (i = 0; i < state.num_of_args; i++)
    {
        debug_msg("Saving register " + i + "(" + hex(register[i]) + ") to " + (newB + 3 + i));
        memory[newB + 3 + i] = register[i];
    }
    // Save the current context
    memory[newB+n+1] = state.E;
    memory[newB+n+2] = state.CP;
    memory[newB+n+3] = state.B;
//    memory[newB+n+4] = retry_foreign;
    memory[newB+n+4] = {code: bootstrap_code,                        
                        predicate:state.current_predicate,  // Suspect
                        offset:retry_foreign_offset};
    memory[newB+n+5] = state.TR;
    memory[newB+n+6] = state.H;
    memory[newB+n+7] = state.B0;
    state.B = newB;
    state.HB = state.H;
    return true;
}

function update_choicepoint_data(value)
{
    memory[state.B+1] = value;
    return true;
}


function destroy_choicepoint()
{
    debug_msg("Destroying choicepoint at " + state.B);
    n = memory[state.B];
    unwind_trail(memory[state.B + n + 5], state.TR);
    state.B = memory[state.B + n + 3];
    state.HB = memory[state.B+ memory[state.B] + 6];
    debug_msg("B is now " + state.B);
}

// For testing only! Assumes -,+ mode
function member(element, list)
{
    if (state.foreign_retry)
    {
        list = state.foreign_value;
        debug_msg("Is retry! Setting ptr back to " + hex(list) + " = " + term_to_string(list));
    }
    else
    {
        debug_msg("Not a retry");
        create_choicepoint();
    }    
    while(TAG(list) == TAG_LST)
    {
        head = memory[VAL(list)];
        if (unify(head, element))
        {
            debug_msg("Unification succeeded. Setting choicepoint value @" +(state.B+1) + " to " + hex(memory[VAL(list)+1]));
            update_choicepoint_data(memory[VAL(list)+1]);
            return true;
        }
        list = memory[VAL(list)+1]
    }
    destroy_choicepoint();
    return false;
}



function predicate_debug()
{
    debugging = true;
    return true;
}

function predicate_nodebug()
{
    debugging = false;
    return true;
}

function predicate_jmp(vars)
{
    state.P = -1; // PC will be incremented by 3 after this if we succeed to 2. This is where queries are compiled from, since the first two bytes are for try/retry/trust
    code = compile_buffer.slice(0);
    register[0] = vars;
    return true;
}

function mark_top_choicepoint(vars_list, markpoint)
{
    var vars = [];
    while(TAG(vars_list) == TAG_LST)
    {        
        vars.push(memory[VAL(vars_list)]);        
        vars_list = memory[VAL(vars_list) + 1];
    }
    if (vars_list != NIL)
        abort("Invalid list in mark_top_choicepoint");

    debug_msg("Marking choicepoint " + state.B+ " with cleanup at " + (state.P+3) + " and code = " + code);
    mark = {B: state.B,
            V: vars,
            P: state.P+3,
            code: code};
    cleanups.unshift(mark);
    // Skip the cleanup code
    state.P += 4;
    return unify(markpoint, state.B ^ (TAG_INT << WORD_BITS));
}

// FIXME: Not implemented: [c, d, D, e, E, I, N, p, s, @, t, |, +]
function predicate_format(stream, fmt, args)
{
    var s = {};
    if (!get_stream(stream, s))
        return false;
    stream = s.value;
    result = "";
    fmt = atable[VAL(fmt)];
    var arg = args;
    var numarg = undefined;
    for (i = 0; i < fmt.length; i++)
    {
        c = fmt.charAt(i);
        if (c == '~')
        {
            while (true)
            {
                switch (fmt.charAt(i+1))
                {
                case 'a':
                    if (TAG(memory[VAL(arg)]) != TAG_ATM)
                        return type_error("atom", arg);
                    // fall-through
                case 'w':
                    result += format_term(memory[VAL(arg)], {ignore_ops:false, numbervars:true, quoted:false});
                    arg = memory[VAL(arg)+1];
                    break;
                case 'W':
                    var a = memory[VAL(arg)];
                    arg = memory[VAL(arg)+1];
                    var options = parse_term_options(memory[VAL(arg)]);
                    result += format_term(a, options);
                    arg = memory[VAL(arg)+1];
                    break;
                    
                case 'i':
                    arg = memory[VAL(arg)+1];
                    break;
                case 'q':
                    result += format_term(memory[VAL(arg)], {ignore_ops:false, numbervars:true, quoted:true});
                    arg = memory[VAL(arg)+1];
                    break;
                case 'k':
                    result += format_term(memory[VAL(arg)], {ignore_ops:true, numbervars:true, quoted:true});
                    arg = memory[VAL(arg)+1];
                    break;
                case 'n':
                    result += "\n";
                    break;
                case '~':
                    result += "~";
                    break;
                case 'r':
                case 'R':
                    if (numarg == undefined)
                        return format_error("r,R requires radix specifier");
                    var e = {};
                    if (!evaluate_expression(memory[VAL(arg)], e))
                        return false;
                    if (fmt.charAt(i+1) == 'R')
                        result += e.value.toString(numarg).toUpperCase();
                    else
                        result += e.value.toString(numarg);
                    break;
                case '0':
                case '1':
                case '2':
                case '3':
                case '4':
                case '5':
                case '6':
                case '7':
                case '8':
                case '9':
                    numarg = fmt.charAt(i+1) - '0';
                    i+=2;
                    while (fmt.charAt(i) >= '0' && fmt.charAt(i) <= '9')
                    {
                        numarg = (numarg * 10) + (fmt.charAt(i)-'0');
                        i++;
                    }
                    i--;
                    continue;                
                default:
                    return existence_error("format_character", lookup_atom(fmt.charAt(i+1)));
                }
                i++;
                break; // Really this is just a goto for the numarg reading
            }
        }
        else if (c == '\\')
        {
            switch(fmt.charAt(i+1))
            {
            case '\\':
                result += "\\";
                break;
            case "n":
                result += "\n";
                break;
            default:
                abort("Unimplemented or escape character: " + fmt.charAt(i+1));
            }
            i++;
        }
        else
            result += c;
    }
    var bytes = toByteArray(result);
    return (stream.write(stream, 1, bytes.length, bytes) >= 0)
}

function unmark_choicepoint(mark)
{
    debug_msg("Unmarking: " + term_to_string(mark));
    mark = VAL(mark);    
    for (var i = 0; i < cleanups.length; i++)
    {
        if (cleanups[i].B == mark)
        {
            cleanups.splice(i, 1);
            // Additionally, we have to actually cut this choicepoint as well. This deserves an explanation!
            // Suppose we nest setup_call_cleanup(true, setup_call_cleanup(true, true, true), true).
            // Once we complete the inner true, we will unmark the choicepoint that allows us to distinguish exit from _.
            // but unless we cut the parent choicepoint (which allows us to distinguish success from error/failure)
            // this will persist. The outer cleanup will then see a choicepoint, even though the inner one has succeeded 
            // deterministically, and will exit with unbound port.
            state.B = memory[mark + memory[mark]+3];
            if (state.B > 0)
                tidy_trail();
            return true;
        }
    }
    debug("Looking for " + mark);
    debug(JSON.stringify(cleanups));
    abort("nope");
}

// This is used in the failure port. Since we have failed into the failure branch of the cleanup, there cannot be any choicepoints around except for the 
// one that got us here. Therefore, we can just delete the first cleanup handler (I hope!)
function unmark_top_choicepoint()
{
    cleanups.shift();
    return true;
}

function predicate_copy_term(t1, t2)
{
    return unify(t2, recall_term(record_term(t1), {}));
}


function predicate_repeat()
{
    // Create a choicepoint that points to itself
    if (state.E > state.B)
    {
        newB = state.E + state.CP.code[state.CP.offset - 1] + 2;
    } 
    else
    {
        newB = state.B + memory[state.B] + 8;
    }
    debug_msg("Creating foreign choicepoint on the stack at " + newB);
    memory[newB] = state.num_of_args+2;
    var n = memory[newB];
    memory[newB + 1] = 0;
    debug_msg("Reserved @" + (newB + 1) + " for value");
    memory[newB + 2] = {code: code,
                        offset: state.P};
    debug_msg("Saving " + n + " args including the two specials");
    for (i = 0; i < state.num_of_args; i++)
    {
        debug_msg("Saving register " + i + "(" + hex(register[i]) + ") to " + (newB + 3 + i));
        memory[newB + 3 + i] = register[i];
    }
    // Save the current context
    memory[newB+n+1] = state.E;
    memory[newB+n+2] = state.CP;
    memory[newB+n+3] = state.B;
    memory[newB+n+4] = {code: code,
                        predicate: state.current_predicate, // suspect!
                        offset: state.P}; // Retry will just create the choicepoint again!
    memory[newB+n+5] = state.TR;
    memory[newB+n+6] = state.H;
    memory[newB+n+7] = state.B0;
    state.B = newB;
    state.HB = state.H;
    return true;
}

var flags = [];

function predicate_flag(key, old_value, new_value)
{
    if (TAG(key) == TAG_REF)
        return instantiation_error(key);
    if (TAG(key) != TAG_ATM)
        return type_error("atom", key);
    key = atable[VAL(key)];
    var o = (TAG_INT << WORD_BITS);
    if (flags[key] !== undefined)
        o = flags[key] ^ (TAG_INT << WORD_BITS)
    if (!unify(o, old_value))
        return false;
    var n = {};
    if (evaluate_expression(new_value, n))
        flags[key] = n.value;
    else 
        return false;
    return true;
}

function predicate_atom_length(atom, length)
{
    if (TAG(atom) == TAG_REF)
        return instantiation_error(atom);
    if (TAG(atom) != TAG_ATM)
        return type_error("atom", atom);
    return unify(atable[VAL(atom)].length ^ (TAG_INT << WORD_BITS), length);    
}

function predicate_atom_concat(atom1, atom2, atom12)
{
    var index;
    if (!state.foreign_retry)
    {        
        // First call, or deterministic
        if (TAG(atom1) == TAG_REF && TAG(atom12) == TAG_REF)
            return instantiation_error(atom1);
        if (TAG(atom1) != TAG_REF && TAG(atom1) != TAG_ATM)
            return type_error("atom", atom1);
        if (TAG(atom2) != TAG_REF && TAG(atom2) != TAG_ATM)
            return type_error("atom", atom2);
        if (TAG(atom12) != TAG_REF && TAG(atom12) != TAG_ATM)
            return type_error("atom", atom12);
        if (TAG(atom1) == TAG_ATM && TAG(atom2) == TAG_ATM)
        {
            // Deterministic case
            return unify(atom12, lookup_atom(atable[VAL(atom1)] + atable[VAL(atom2)]));
        }
        else 
        {
            // Nondeterministic case. Need a choicepoint:
            create_choicepoint();
            index = 0;
        }
    }
    else
    {
        index = state.foreign_value+1;
    }
    update_choicepoint_data(index);
    // Drop through to general nondeterministic case
    if (index == atable[VAL(atom12)].length+1)
    {
        destroy_choicepoint();
        return false;
    }
    if (unify(atom1, lookup_atom(atable[VAL(atom12)].substring(0, index))) && unify(atom2, lookup_atom(atable[VAL(atom12)].substring(index))))
        return true;
    return false;
}

function predicate_char_code(atom, code)
{
    if (TAG(atom) == TAG_REF && TAG(code) == TAG_REF)
        return instantiation_error(atom);
    if (TAG(atom) == TAG_ATOM)
    {
        a = atable[VAL(atom)];
        if (a.length != 1)
            return type_error("character", atom);
        return unify(code, a.charCodeAt(0) ^ (TAG_INT << WORD_BITS));
    }
    else if (TAG(code) == TAG_INT)
    {
        if (VAL(code) < 0)
            return representation_error("character_code", code);
        return unify(atom, lookup_atom(String.fromCharCode(VAL(code))));
    }
}

function predicate_atom_chars(atom, chars)
{
    if (TAG(chars) == TAG_REF)
    {
        // Atom -> chars
        if (TAG(atom) != TAG_ATM)
            return type_error("atom", atom);
        var a = atable[VAL(atom)].split('');
        var tmp = state.H;
        for (i = 0; i < a.length; i++)
        {
            memory[state.H] = lookup_atom(a[i]);
            memory[state.H+1] = ((state.H+2) ^ (TAG_LST << WORD_BITS));
            state.H += 2;
        }
        memory[state.H-1] = NIL;
        return unify(chars, tmp ^ (TAG_LST << WORD_BITS));
    }
    else
    {
        // Chars -> Atom
        var a = [];
        while (TAG(chars) == TAG_LST)
        {
            a.push(atable[VAL(memory[VAL(chars)])]);
            chars = memory[VAL(chars)+1];
        }
        if (chars != NIL)
            return type_error("list", chars);
        return unify(atom, lookup_atom(a.join('')));            
    }
}

function predicate_atom_codes(atom, codes)
{
    if (TAG(codes) == TAG_REF)
    {
        // Atom -> codes
        if (TAG(atom) != TAG_ATM)
            return type_error("atom", atom);
        var a = atable[VAL(atom)];
        var tmp = state.H ^ (TAG_LST << WORD_BITS);
        for (i = 0; i < a.length; i++)
        {
            memory[state.H] = a.charCodeAt(i) ^ (TAG_INT << WORD_BITS);
            // If there are no more items we will overwrite the last entry with [] when we exit the loop
            memory[state.H+1] = ((state.H+2) ^ (TAG_LST << WORD_BITS));
            state.H += 2;
        }
        memory[state.H-1] = NIL;
        return unify(codes, tmp);
    }
    else
    {
        // Codes -> Atom
        var a = [];
        while (TAG(codes) == TAG_LST)
        {
            a.push(String.fromCharCode(memory[VAL(codes)]));
            codes = memory[VAL(codes)+1];
        }
        if (codes != NIL)
            return type_error("list", codes);
        return unify(atom, lookup_atom(a.join('')));            
    }
}
// return -1 if a < b
// return 0 if a == b
// return 1 if a > b
//
function compare_terms(a, b)
{
    switch(TAG(a))
    {
    case TAG_REF:
        if (TAG(b) == TAG_REF)
        {
            if (a == b)
                return 0;
            else if (a > b)
                return 1;
        }
        return -1;
    case TAG_FLT:
        if (TAG(b) == TAG_REF)
            return 1;
        if (TAG(b) == TAG_FLT)
        {
            if (floats[VAL(a)] == floats[VAL(b)])
                return 0;
            else if (floats[VAL(a)] > floats[VAL(b)])
                return 1;
        }
        return -1;
    case TAG_INT:
        if (TAG(b) == TAG_REF || TAG(b) == TAG_FLT)
            return 1;
        if (TAG(b) == TAG_INT)
        {
            if (VAL(a) == VAL(b))
                return 0;
            else if (VAL(a) > VAL(b))
                return 1;
        }
        return -1;
    case TAG_ATM:
        if (TAG(b) == TAG_REF || TAG(b) == TAG_FLT || TAG(b) == TAG_INT)
            return 1;
        if (TAG(b) == TAG_ATM)
        {
            if (atable[VAL(a)] == atable[VAL(b)])
                return 0;
            else if (atable[VAL(a)] > atable[VAL(b)])
                return 1;
        }
        return -1;
    case TAG_STR:
    case TAG_LST:
        if (TAG(b) == TAG_REF || TAG(b) == TAG_FLT || TAG(b) == TAG_INT || TAG(b) == TAG_ATM)
            return 1;
        var aftor;
        var bftor;
        if (TAG(a) == TAG_LST)
            aftor = lookup_functor(".", 2);
        else
            aftor = memory[VAL(a)];
        if (TAG(b) == TAG_LST)
            bftor = lookup_functor(".", 2);
        else
            bftor = memory[VAL(b)];
        if (ftable[VAL(aftor)][1] > ftable[VAL(bftor)][1])
            return 1;
        else if (ftable[VAL(aftor)][1] < ftable[VAL(bftor)][1])
            return -1;
        // At this point the arity is equal and we must compare the functor names
        if (atable[ftable[VAL(aftor)][0]] > atable[ftable[VAL(bftor)][0]])
            return 1;
        else (atable[ftable[VAL(aftor)][0]] < atable[ftable[VAL(bftor)][0]])
            return -1;
        // So the functors are the same and we must compare the arguments.
        for (i = 0; i < ftable[VAL(aftor)][1]; i++)
        {
            var result = compare_terms(memory[VAL(a)+1+i], memory[VAL(b)+1+i]);
            if (result != 0)
                return result;
        }
    }
    return 0;
}

function predicate_compare(x, a, b)
{
    var i = compare_terms(a,b);
    if (i > 0) 
        return unify(x, lookup_atom(">"));
    else if (i < 0) 
        return unify(x, lookup_atom("<"));
    else
        return unify(x, lookup_atom("="));
}

function predicate_term_lt(a, b)
{
    return compare_terms(a,b) == -1;
}

function predicate_term_elt(a, b)
{
    return compare_terms(a,b) != 1;
}

function predicate_term_gt(a, b)
{
    return compare_terms(a,b) == 1;
}

function predicate_term_egt(a, b)
{
    return compare_terms(a,b) != -1;
}


function predicate_acyclic_term(t)
{
    var visited_cells = [];
    var stack = [t];
    while (stack.length != 0)
    {        
        var arg = stack.pop();
        switch (TAG(arg))
        {
        case TAG_INT:
        case TAG_FLT:
        case TAG_ATM:
            continue;
        case TAG_REF:
            var needle = deref(arg);
            for (var i = 0; i < visited_cells.length; i++)
            {
                if (visited_cells[i] == needle)
                {
                    return false;
                }
            }
            continue;
        case TAG_LST:
            visited_cells.push(arg);
            stack.push(memory[VAL(arg)]);
            stack.push(memory[VAL(arg)+1]);
            continue;
        case TAG_STR:
            visited_cells.push(arg);
            var arity = ftable[VAL(memory[VAL(arg)])][1];
            for (var i = 0; i < arity; i++)
                stack.push(memory[VAL(arg)+1+i]);
            continue;
        }
    }
    return true;
}

function predicate_number_chars(n, chars)
{
    if (TAG(chars) == TAG_REF)
    {
        // Atom -> chars
        var a;
        if (TAG(n) == TAG_INT)
            a = (VAL(n) + "").split('');
        else if (TAG(n) == TAG_FLT)
            a = (floats[VAL(n)] + "").split('');
        else
            return type_error("number", n);
        var tmp = state.H;
        for (i = 0; i < a.length; i++)
        {
            memory[state.H] = lookup_atom(a[i]);
            memory[state.H+1] = ((state.H+2) ^ (TAG_LST << WORD_BITS));
            state.H += 2;
        }
        memory[state.H-1] = NIL;
        return unify(chars, tmp ^ (TAG_LST << WORD_BITS));
    }
    else
    {
        // Chars -> Atom
        var a = [];
        while (TAG(chars) == TAG_LST)
        {
            a.push(atable[VAL(memory[VAL(chars)])]);
            chars = memory[VAL(chars)+1];
        }
        if (chars != NIL)
            return type_error("list", chars);
        var f = parseFloat(a.join(''));
        // FIXME: Overflows
        if (~~f == f)
            return unify(n, f ^ (TAG_INT << WORD_BITS));
        else
        {            
            return unify(n, lookup_float(f));
        }
    }
}

function lookup_float(f)
{
    for (var i = 0; i < floats.length+1; i++)
    {
        if (floats[i] == f)
        {
            return i ^ (TAG_FLT << WORD_BITS);
        }
        if (floats[i] === undefined)
        {
            floats[i] = f;
            return i ^ (TAG_FLT << WORD_BITS);
        }
    }
    abort("Should not get here");
}

function predicate_number_codes(n, codes)
{
    if (TAG(codes) == TAG_REF)
    {
        // Atom -> codes
        var a;
        if (TAG(n) == TAG_INT)
        {
            a = VAL(n) + "";
        }
        else if (TAG(n) == TAG_FLT)
        {
            a = floats[VAL(n)] + "";
        }
        else
            return type_error("number", n);
        var a = (VAL(n) + "");
        var tmp = state.H;
        for (i = 0; i < a.length; i++)
        {
            memory[state.H] = a.charCodeAt(i) ^ (TAG_INT << WORD_BITS);
            memory[state.H+1] = ((state.H+2) ^ (TAG_LST << WORD_BITS));
            state.H += 2;
        }
        memory[state.H-1] = NIL;
        return unify(codes, tmp ^ (TAG_LST << WORD_BITS));
    }
    else
    {
        // Codes -> Atom
        var a = [];
        while (TAG(codes) == TAG_LST)
        {
            a.push(String.fromCharCode(memory[VAL(codes)]));
            codes = memory[VAL(codes)+1];
        }
        if (codes != NIL)
            return type_error("list", codes);
        var f = parseFloat(a.join(''));
        // FIXME: Overflows
        if (~~f == f)
            return unify(n, f ^ (TAG_INT << WORD_BITS));
        else
            return unify(n, lookup_float(f));
    }
}

function predicate_subsumes_term(a, b)
{
    var before = term_variables(b);
    create_choicepoint();
    if (!unify(a,b))
    {
        destroy_choicepoint();
        return false;
    }
    if (!predicate_acyclic_term(b))
    {
        destroy_choicepoint();
        return false;
    }
    var after = term_variables(b);
    // We need to save a bit of info for this backtrack to not cause us some serious problems
    var oldP = state.P;
    var oldcode = code;
    var oldPred = state.current_predicate;
    backtrack();
    state.P = oldP;
    code = oldcode;
    state.current_predicate = oldPred;

    destroy_choicepoint();
    return (after.length == before.length);
}


function predicate_current_op(precedence, fixity, name)
{
    if (state.foreign_retry)
    {
        index = state.foreign_value + 1;         
    }
    else
    {
        create_choicepoint();
        index = 0;
    }
    update_choicepoint_data(index);
    // This is horrific
    var infix_count = Object.keys(infix_operators).length;
    var prefix_count = Object.keys(prefix_operators).length;
    if (index >= infix_count + prefix_count)
    {
        destroy_choicepoint();
        return false;
    }
    else if (index >= infix_count)
    {
        try_name = Object.keys(prefix_operators)[index - infix_count];
        try_fixity = prefix_operators[try_name].fixity;
        try_precedence = prefix_operators[try_name].precedence;
    }
    else
    {
        try_name = Object.keys(infix_operators)[index];
        try_fixity = infix_operators[try_name].fixity;
        try_precedence = infix_operators[try_name].precedence;
    }
    return unify(name, lookup_atom(try_name)) && unify(fixity, lookup_atom(try_fixity)) && unify(precedence, try_precedence ^ (TAG_INT<<WORD_BITS));
}

var prolog_flags = [{name:"bounded", fn:flag_bounded},
                    {name:"max_integer", fn:flag_max_integer},
                    {name:"min_integer", fn:flag_min_integer},
                    {name:"integer_rounding_function", fn:flag_integer_rounding_function},
                    {name:"char_conversion", fn:flag_char_conversion},
                    {name:"debug", fn:flag_debug},
                    {name:"max_arity", fn:flag_max_arity},
                    {name:"unknown", fn:flag_unknown},
                    {name:"double_quotes", fn:flag_double_quotes}];

var prolog_flag_values = {char_conversion: false,
                          debug: false,
                          unknown: "error",
                          double_quotes: "codes"};

function flag_bounded(set, value)
{
    if (set) return permission_error("prolog_flag");
    return unify(value, lookup_atom("true"));
}

function flag_max_integer(set, value)
{
    if (set) return permission_error("prolog_flag");
    return unify(value, (268435455) ^ (TAG_INT<<WORD_BITS));
}

function flag_min_integer(set, value)
{
    if (set) return permission_error("prolog_flag");
    return unify(value, (536870911) ^ (TAG_INT<<WORD_BITS));
}

function flag_integer_rounding_function(set, value)
{
    if (set) return permission_error("prolog_flag");
    return unify(value, lookup_atom("toward_zero"));
}

function flag_char_conversion(set, value)
{
    if (set) 
    {
        if (TAG(value) == TAG_ATM && atable[VAL(value)] == "on")
            prolog_flag_values.char_conversion = true;
        else if (TAG(value) == TAG_ATM && atable[VAL(value)] == "off")
            prolog_flag_values.char_conversion = false;
        else
            return type_error("flag_value", value);
        return true;
    }
    return unify(value, prolog_flag_values.char_conversion?lookup_atom("on"):lookup_atom("off"));
}

function flag_debug(set, value)
{
    if (set) 
    {
        if (TAG(value) == TAG_ATM && atable[VAL(value)] == "on")
            prolog_flag_values.debug = true;
        else if (TAG(value) == TAG_ATM && atable[VAL(value)] == "off")
            prolog_flag_values.debug = false;
        else
        {
            return type_error("flag_value", value);
        }
        return true;
    }
    return unify(value, prolog_flag_values.debug?lookup_atom("on"):lookup_atom("off"));
}

function flag_max_arity(set, value)
{
    if (set) return permission_error("prolog_flag");
    return unify(value, lookup_atom("unbounded"));
}

function flag_unknown(set, value)
{
    if (set) 
    {
        if (TAG(value) == TAG_ATM && atable[VAL(value)] == "error")
            prolog_flag_values.unknown = "error";
        else if (TAG(value) == TAG_ATM && atable[VAL(value)] == "fail")
            prolog_flag_values.unknown = "fail";
        else if (TAG(value) == TAG_ATM && atable[VAL(value)] == "warning")
            prolog_flag_values.unknown = "warning";
        else
            return type_error("flag_value", value);
        return true;
    }
    return unify(value, lookup_atom(prolog_flag_values.unknown));
}

function flag_double_quotes(set, value)
{
    if (set) 
    {
        if (TAG(value) == TAG_ATM && atable[VAL(value)] == "chars")
            prolog_flag_values.double_quotes = "chars";
        else if (TAG(value) == TAG_ATM && atable[VAL(value)] == "codes")
            prolog_flag_values.double_quotes = "codes";
        else if (TAG(value) == TAG_ATM && atable[VAL(value)] == "atom")
            prolog_flag_values.double_quotes = "atom";
        else
            return type_error("flag_value", value);
        return true;
    }
    return unify(value, lookup_atom(prolog_flag_values.double_quotes));
}

function predicate_set_prolog_flag(key, value)
{
    if (TAG(key) != TAG_ATM)
        return type_error("atom", key);
    keyname = atable[VAL(key)];    
    
    for (var i = 0; i < prolog_flags.length; i++)
    {
        if (prolog_flags[i].name == keyname)
        {
            return prolog_flags[i].fn(true, value);
        }
    }
    debug("No such flag");
    return false;
}

function predicate_current_prolog_flag(key, value)
{
    if (TAG(key) == TAG_REF)
    {
        if (state.foreign_retry)
        {
            index = state.foreign_value + 1;         
        }
        else
        {
            create_choicepoint();
            index = 0;
        }
        update_choicepoint_data(index);        
        if (index >= prolog_flags.length)
        {
            destroy_choicepoint();
            return false;
        }
        unify(key, lookup_atom(prolog_flags[index].name));
        return prolog_flags[index].fn(false, value);        
    }
    else if (TAG(key) == TAG_ATM)
    {
        keyname = atable[VAL(key)];    
        var index = 0;
        for (var i = 0; i < prolog_flags.length; i++)
        {
            if (prolog_flags[index].name == keyname)
                return prolog_flags[index].fn(false, value);
        }
        return false;
    }
    else
        return type_error("atom", key);
}

function predicate_clause(head, body)
{
    var ftor;
    var index;
    if (TAG(head) == TAG_REF)
        return instantiation_error(head);
    else if (TAG(head) == TAG_ATM)
    {
        ftor = VAL(lookup_functor(atable[VAL(head)], 0));
    }
    else if (TAG(head) == TAG_STR)
    {
        ftor = VAL(memory[VAL(head)]);
    }
    else
        return type_error("callable", head);
    if (predicates[ftor].is_public != true)
        return permission_error("access", "private_procedure", head);
    if (!state.foreign_retry)
    {
        create_choicepoint();
        index = 0;
    }
    else
    {
        index = state.foreign_value + 1;
    }
    update_choicepoint_data(index);
    if (index >= predicates[ftor].clause_keys.length)
    {
        destroy_choicepoint();
        return false;
    }
    var key = predicates[ftor].clause_keys[index];
    var varmap = {};
    var head_ref = recall_term(predicates[ftor].clauses[key].head, varmap);
    if (unify(head_ref, head))
    {
        if (unify(recall_term(predicates[ftor].clauses[key].body, varmap), body))
        {
            return true;
        }
        return false;
            
    }
    else
    {
        return false;    
    }
}


function predicate_current_predicate(indicator)
{
    var slash2 = lookup_functor("/", 2);
    if (!state.foreign_retry)
    {
        if (TAG(indicator) == TAG_STR)
        {
            if (memory[VAL(indicator)] == slash2)
            {
                var name = memory[VAL(indicator) + 1];
                var arity = memory[VAL(indicator) + 2];
                if (TAG(arity) != TAG_INT && TAG(arity) != TAG_REF)
                    return type_error("integer", arity);
                if (TAG(name) != TAG_ATM && TAG(name) != TAG_REF)
                    return type_error("atom", name);
                
                if (TAG(name) == TAG_ATM && TAG(arity) == TAG_INT)
                {
                    // Deterministic
                    var ftor = VAL(lookup_functor(atable[VAL(name)], VAL(arity)));
                    if (predicates[ftor] !== undefined)
                        return true;
                    else if (foreign_predicates[ftor] !== undefined)
                        return true;
                    return false;
                }
            }
            else
                return type_error("predicate_indicator", indicator);
        }
        // We are going to have to enumerate all predicates
        create_choicepoint();
        index = 0;
    }
    else
        index = state.foreign_value + 1;
    // Horrific :(

    if (index >= Object.keys(predicates).length)
    {
        destroy_choicepoint();
        return false;
    }
    update_choicepoint_data(index);
    var key = Object.keys(predicates)[index];
    var result = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = slash2;
    memory[state.H++] = ftable[key][0] ^ (TAG_ATM << WORD_BITS);
    memory[state.H++] = ftable[key][1] ^ (TAG_INT << WORD_BITS);;
    return unify(result, indicator);
}

function predicate_abolish(indicator)
{
    var slash2 = lookup_functor("/", 2);
    if (TAG(indicator) == TAG_STR && memory[VAL(indicator)] == slash2)
    {
        var name = deref(memory[VAL(indicator) + 1]);
        var arity = deref(memory[VAL(indicator) + 2]);
        if (TAG(name) == TAG_ATM && TAG(arity) == TAG_INT)
        {
            if (VAL(arity) < 0)
                return domain_error("not_less_than_zero", arity);
            var ftor = VAL(lookup_functor(atable[VAL(name)], VAL(arity)));
            if (predicates[ftor].is_public !== true)
                return permission_error("modify", "static_procedure", indicator);
            predicates[ftor] = undefined;
            return true;
        }
        else if (TAG(name) == TAG_REF)
            return instantiation_error(name);
        else if (TAG(name) != TAG_ATM)
            return type_error("atom", name);
        else if (TAG(arity) == TAG_REF)
            return instantiation_error(arity);
        else if (TAG(arity) != TAG_INT)
            return type_error("integer", arity);
    }
    else if (TAG(indicator) == TAG_REF)
        return instantiation_error(indicator);
    else
        return type_error("predicate_indicator", indicator);
}

function predicate_retract_clause(head, body)
{
    var ftor;
    var index;
    if (TAG(head) == TAG_REF)
        return instantiation_error(head);
    else if (TAG(head) == TAG_ATM)
    {
        ftor = VAL(lookup_functor(atable[VAL(head)], 0));
    }
    else if (TAG(head) == TAG_STR)
    {
        ftor = VAL(memory[VAL(head)]);
    }
    else
        return type_error("callable", head);
    if (predicates[ftor].is_public != true)
        return permission_error("access", "static_procedure", head);
    if (!state.foreign_retry)
    {
        create_choicepoint();
        index = 0;
    }
    else
    {
        index = state.foreign_value + 1;
    }
    update_choicepoint_data(index);
    if (index >= predicates[ftor].clause_keys.length)
    {
        destroy_choicepoint();
        return false;
    }
    var key = predicates[ftor].clause_keys[index];
    var varmap = {};
    var head_ref = recall_term(predicates[ftor].clauses[key].head, varmap);
    if (unify(head_ref, head))
    {
        var body_ref = recall_term(predicates[ftor].clauses[key].body, varmap);
        if (unify(body_ref, body))
        {
            // Delete this clause. This is not a trivial operation!
            var p = predicates[ftor];
            // First case: This is the only predicate
            if (p.clause_keys.length == 1)
            {
                predicates[ftor] = undefined;
                destroy_choicepoint();
                return true;
            }
            else if (index == 0)
            {
                // Delete the first clause. Update the second clause from either:
                // 1) trust_me -> NOP
                // 2) retry_me_else -> try_me_else
                if (p.clauses[p.clause_keys[1]].code[0] == 30)
                    p.clauses[p.clause_keys[1]].code[0] = 254;
                else if (p.clauses[p.clause_keys[1]].code[0] == 29)
                    p.clauses[p.clause_keys[1]].code[0] = 28;
                else
                    abort("Garbage clauses in retract: " + p.clauses[p.clause_keys[1]].code[0]);
                p.clauses[key] = undefined;
                // and remove the key
                p.clauses[key] = undefined;
                p.clause_keys.shift();
                update_choicepoint_data(index-1);
                return true;
            }
            else if (index == p.clause_keys.length-1)
            {
                // Remove the last clause. Update the second-to-last clause from either:
                // 1) try_me_else -> NOP
                // 2) retry_me_else -> trust_me
                if (p.clauses[p.clause_keys[p.clause_keys.length-2]].code[0] == 28)
                    p.clauses[p.clause_keys[p.clause_keys.length-2]].code[0] = 254;
                else if (p.clauses[p.clause_keys[p.clause_keys.length-2]].code[0] == 29)
                    p.clauses[p.clause_keys[p.clause_keys.length-2]].code[0] = 30;
                else
                    abort("Garbage clauses in retract: " + p.clauses[p.clause_keys[p.clause_keys.length-2]].code[0]);            
                // and remove the key
                p.clauses[key] = undefined;
                p.clause_keys.pop();
                destroy_choicepoint();
                return true;
            }
            else
            {
                // Delete a clause from the middle. Update the previous clause from either:
                // try_me_else N -> try_me_else <following clause key>
                // retry_me_else N -> retry_me_else <following clause key>
                p.clauses[p.clause_keys[index-1]].code[1] = p.clause_keys[index+1];
                // and remove the key
                p.clauses[key] = undefined;
                for (var i = 0; i < p.clause_keys.length; i++)
                {
                    if (p.clause_keys[i] == key)
                    {
                        p.clause_keys.splice(i, 1);
                        update_choicepoint_data(index-1);
                        return true;
                    }
                }
                abort("No such key?!");
            }
        }
    }
    return false; // Nothing to retract
}

function predicate_sub_atom(source, start, length, remaining, subatom)
{
    var index;
    if (TAG(source) == TAG_REF)
        return instantiation_error(source);
    else if (TAG(source) != TAG_ATM)
        return type_error("atom", source);
    if (TAG(subatom) != TAG_ATM && TAG(subatom) != TAG_REF)
        return type_error("atom", subatom);
    var input = atable[VAL(source)];
    if (!state.foreign_retry)
    {
        index = {start:0, fixed_start:false, length:0, fixed_length:false, remaining:input.length, fixed_remaining:false};
        if (TAG(start) == TAG_INT)
        {
            index.fixed_start = true;
            index.start = VAL(start);
        }
        if (TAG(length) == TAG_INT)
        {
            index.fixed_length = true;
            index.length = VAL(length);
        }
        if (TAG(remaining) == TAG_INT)
        {
            index.fixed_remaining = true;
            index.remaining = VAL(remaining);
        }
        if (index.fixed_start && index.fixed_remaining && !index.fixed_length)
        {
            // Deterministic: Fall through to bottom case
            index.length = input.length-index.start-index.remaining;
            index.fixed_length = true;
        }
        if (index.fixed_remaining && index.fixed_length && !index.fixed_start)
        {
            // Deterministic: Fall through to bottom case
            index.start = input.length-index.length-index.remaining;
            index.fixed_start = true;
        }
        if (index.fixed_start && index.fixed_length)
        {
            // Deterministic general case.
            return unify(remaining, (input.length-index.start-index.length) ^ (TAG_INT << WORD_BITS)) && 
                unify(start, (index.start) ^ (TAG_INT << WORD_BITS)) && 
                unify(length, (index.length) ^ (TAG_INT << WORD_BITS)) && 
                unify(subatom, lookup_atom(input.substring(index.start, index.start+index.length)));
        }
        // Otherwise nondeterministic
        create_choicepoint();
    }
    else
    {
        index = state.foreign_value;
        if (!index.fixed_length)
        {
            index.length++;
            if (index.start + index.length > input.length)
            {
                index.length = 0;
                if (!index.fixed_start)
                {
                    index.start++;
                    if (index.start > input.length)
                    {
                        destroy_choicepoint();
                        return false;
                    }
                }
                else
                {
                    // start is fixed, so length and remaining are free
                    // but remaining is always just computed
                    destroy_choicepoint();
                    return false;
                }
            }
        }
        else
        {
            // length is fixed, so start and remaining must be free
            index.start++;
            index.remaining--;
            if (index.length + index.start > input.length)
            {
                destroy_choicepoint();
                return false;
            }
        }
    }
    update_choicepoint_data(index);
    return unify(remaining, (input.length-index.start-index.length) ^ (TAG_INT << WORD_BITS)) && 
        unify(start, (index.start) ^ (TAG_INT << WORD_BITS)) && 
        unify(length, (index.length) ^ (TAG_INT << WORD_BITS)) && 
        unify(subatom, lookup_atom(input.substring(index.start, index.start+index.length)));
}

/* errors */
function type_error(expected, got)
{
    var ftor = lookup_functor('type_error', 2);
    var ref = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    memory[state.H++] = lookup_atom(expected);
    memory[state.H++] = got;
    return predicate_throw(ref);
}

function permission_error(action, type, instance)
{
    var ftor = lookup_functor('permission_error', 3);
    var ref = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    memory[state.H++] = lookup_atom(action);
    memory[state.H++] = lookup_atom(type);
    memory[state.H++] = instance;
    return predicate_throw(ref);
}

function instantiation_error(v)
{
    var ftor = lookup_functor('instantiation_error', 1);
    var ref = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    memory[state.H++] = v;
    return predicate_throw(ref);
}

function domain_error(domain, got)
{
    var ftor = lookup_functor('domain_error', 2);
    var ref = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    memory[state.H++] = lookup_atom(domain);
    memory[state.H++] = got;
    return predicate_throw(ref);

}

function format_error(message)
{
    var ftor = lookup_functor('format_error', 1);
    var ref = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    memory[state.H++] = lookup_atom(message);
    return predicate_throw(ref);
}

function existence_error(type, instance)
{
    var ftor = lookup_functor('existence_error', 2);
    var ref = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    memory[state.H++] = lookup_atom(type);
    memory[state.H++] = instance;
    return predicate_throw(ref);
}

function representation_error(type, instance)
{
    var ftor = lookup_functor('representation_error', 2);
    var ref = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    memory[state.H++] = lookup_atom(type);
    memory[state.H++] = instance;
    return predicate_throw(ref);
}

function syntax_error(message)
{
    var ftor = lookup_functor('syntax_error', 1);
    var ref = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    memory[state.H++] = lookup_atom(message);
    return predicate_throw(ref);
}

function io_error(message)
{
    var ftor = lookup_functor('io_error', 1);
    var ref = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    memory[state.H++] = lookup_atom(message);
    return predicate_throw(ref);
}
