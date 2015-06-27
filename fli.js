/* Not implemented:
   All the nondet foreign stuff. That is supported, but not using the SWI-Prolog interface
   Strings
   Floats
   Pointers
   PL_get_chars
   PL_predicate_info
   PL_copy_term_ref
   PL_reset_term_refs
*/

function PL_new_term_ref()
{
    // FIXME: Should this go on the heap or the stack?
    return alloc_var();
}

function PL_new_term_refs(n)
{
    var first = alloc_var();
    for (i = 0; i < n-1; i++)
        alloc_var();
        
}

function PL_succeed()
{
    return true;
}

function PL_fail()
{
    return true;
}

function PL_new_atom(chars)
{
    return lookup_atom(chars);
}

function PL_atom_chars(atom)
{
    return atable[VAL(atom)];
}

function PL_new_functor(name, arity)
{
    return lookup_functor(atable[name], arity);
}

function PL_functor_name(ftor)
{
    return ftable[VAL(ftor)][0];
}

function PL_functor_arity(ftor)
{
    return ftable[VAL(ftor)][1];
}

function PL_term_type(term)
{
    return TAG(term);
}

function PL_is_variable(term)
{
    return TAG(term) == TAG_REF;
}

function PL_is_atom(term)
{
    return TAG(term) == TAG_ATM;
}

function PL_is_integer(term)
{
    return TAG(term) == TAG_INT;
}

function PL_is_compound(term)
{
    return TAG(term) == TAG_STR;
}

function PL_is_functor(term, ftor)
{
    return TAG(term) == TAG_STR && memory[VAL(term)] == ftor;
}

function PL_is_list(term)
{
    return TAG(term) == TAG_LST;
}

function PL_is_atomic(term)
{
    return TAG(term) != TAG_STR && TAG(term) != TAG_REF;
}

function PL_is_number(term)
{
    return TAG(term) == TAG_INT; // At the moment
}

function PL_get_atom(term)
{
    if (TAG(term) == TAG_ATM)
        return atom;
    throw("type_error: atom");
}

function PL_get_atom_chars(term)
{
    if (TAG(term) == TAG_ATOM)
        return atable[VAL(term)];
    throw("type_error: atom");
}

function PL_get_integer(term)
{
    if (TAG(term) == TAG_INT)
        return VAL(term);
    throw("type_error: integer");
}

function PL_get_functor(term)
{
    if (TAG(term) == TAG_STR)
        return memory[VAL(term)];
    throw("type_error: term");
}

function PL_get_arg(index, term)
{
    if (index < 1)
        throw("domain_error: term arity");
    if (TAG(term) == TAG_STR)
    {
        if (index > ftable[VAL(memory[VAL(term)])][1])  // Check arity is OK
            throw("type_error: term arity");
        return memory[VAL(term) + index];
    }
    throw("type_error: term");
}

// Returns an object with head and tail keys
function PL_get_list(list)
{
    if (TAG(list) == TAG_LST)
        return {head: memory[VAL(list)],
                tail: memory[VAL(list)+1]};
    return null;
}

function PL_get_head(list)
{
    if (TAG(list) == TAG_LST)
        return memory[VAL(list)];
    return null;
}

function PL_get_tail(list)
{
    if (TAG(list) == TAG_LST)
        return memory[VAL(list)+1];
    return null;
}

function PL_get_nil()
{
    return NIL;
}

function PL_put_variable()
{
    return alloc_var();
}

function PL_put_atom(atom)
{
    return atom;
}

function PL_put_atom_chars(chars)
{
    return lookup_atom(chars);
}

function PL_put_integer(integer)
{
    return integer ^ (TAG_INT << WORD_BITS);
}

function PL_put_functor(term, ftor)
{
    var r = alloc_structure(ftor);
    for (i = 0; i < ftable[VAL(ftor)][1]; i++)
        alloc_var();
}

function PL_put_list()
{
    var r = alloc_list();
    alloc_var();
    alloc_var();
}

function PL_put_nil()
{
    return NIL;
}

function PL_cons_functor(ftor)
{
    if (state.H + arguments.length + 1 >= HEAP_SIZE)
        return false; // Not enough heap
    var r = state.H ^ (TAG_STR << WORD_BITS);
    memory[state.H++] = ftor;
    for (i = 1; i < arguments.length; i++)
        memory[state.H++] = arguments[i];
}

function PL_cons_list(head, tail)
{
    if (state.H +2 >= HEAP_SIZE)
        return false;
    var result = state.H ^ (TAG_LST << WORD_BITS);
    memory[state.H++] = head;
    memory[state.H++] = tail;
    return result;
}

function PL_unify_integer(term, integer)
{
    return unify(term, integer ^ (TAG_INT << WORD_BITS));
}

function PL_unify_atom_chars(term, chars)
{
    return unify(term, lookup_atom(string));
}

function PL_unify(t1, t2)
{
    return unify(t1, t2);
}

function PL_unify_atom(term, atom)
{
    return unify(term, atom);
}

function PL_unify_nil(term)
{
    return unify(term, NIL);
}

function PL_unify_arg(index, term, arg)
{
    return unify(memory[VAL(term) + 1 + index], arg);
}

function PL_unify_list(list, head, tail)
{
    return (TAG(list) == TAG_LST) && unify(memory[VAL(list)], head) && unify(memory[VAL(list) + 1], tail);            
}

function PL_pred(ftor, module)
{
    if (predicates[ftor] === undefined)
        throw("Undefined predicate");
    return ftor;
}

function PL_predicate(name, arity, module)
{
    return PL_pred(lookup_functor(name, arity), module);
}

function PL_open_query(module, debug, predicate, args)
{
    initialize();
    allocate_first_frame();
    state.P = predicates[predicate];
    for (i = 0; i < ftable[predicate][1]; i++)
        register[i] = args[i];
    return {fresh:true};
}

function PL_next_solution(qid)
{    
    if (!qid.fresh)
        backtrack();
    qid.fresh = false;
    return wam();
}

function PL_call(term, module)
{
    ftor = VAL(memory[VAL(term)]);
    initialize();
    allocate_first_frame();
    state.P = predicates[ftor];
    for (i = 0; i < ftable[ftor][1]; i++)
        register[i] = memory[VAL(term) + 1 + i];
    return wam();    
}

function PL_cut_query(qid)
{
    // This is not implemented
}

function PL_close_query(qid)
{
    // This is not implemented either
}


function PL_call_predicate(module, debug, predicate, args)
{
    var qid = PL_open_query(module, debug, predicate, args);
    var result = PL_next_solution(qid);
    PL_cut_query(qud);
    return result;
}
