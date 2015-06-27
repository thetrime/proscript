/* Term reading */
// See http://journal.stuffwithstuff.com/2011/03/19/pratt-parsers-expression-parsing-made-easy/
// Parsers return either:
// 1) An string, in case of an atom
// 2) An integer, in case of an integer
// 3) An object with .list and .tail if a list (because apparently it is not easy to determine if the type of something is a list at runtime!?)
//      If it is a proper list, .tail == NIL
// 4) An object with .variable_name, if a variable
// 5) An object with .functor (a string) and .args (an array) defined if a term

function parse_infix(s, lhs, precedence)
{
    var token = {};
    if (!read_token(s, token))
        return false;
    token = token.value;
    var rhs = {};
    if (!read_expression(s, precedence, false, false, rhs))
        return false;
    return {functor: token,
            args: [lhs, rhs.value]};
}

function parse_postfix(s, lhs)
{
    var token = {};
    if (!read_token(s, token))
        return false;
    return {functor: token.value,
            args: [lhs]};
}

// A reminder: yfx means an infix operator f, with precedence p, where the lhs has a precendece <= p and the rhs has a precedence < p.

var prefix_operators = {":-": {precedence: 1200, fixity: "fx"},
                        "?-": {precedence: 1200, fixity: "fx"},
                        "dynamic": {precedence: 1150, fixity: "fx"},
                        "discontiguous": {precedence: 1150, fixity: "fx"},
                        "initialization": {precedence: 1150, fixity: "fx"},
                        "meta_predicate": {precedence: 1150, fixity: "fx"},
                        "module_transparent": {precedence: 1150, fixity: "fx"},
                        "multifile": {precedence: 1150, fixity: "fx"},
                        "thread_local": {precedence: 1150, fixity: "fx"},
                        "volatile": {precedence: 1150, fixity: "fx"},
                        "\+": {precedence: 900, fixity: "fy"},
                        "~": {precedence: 900, fixity: "fx"},
                        "?": {precedence: 500, fixity: "fx"},
                        "+": {precedence: 200, fixity: "fy"},
                        "-": {precedence: 200, fixity: "fy"},
                        "\\": {precedence: 200, fixity: "fy"}};


var infix_operators = {":-": {precedence: 1200, fixity: "xfx"},
                       "-->": {precedence: 1200, fixity: "xfx"},
                       ";": {precedence: 1100, fixity: "xfy"},
                       "|": {precedence: 1100, fixity: "xfy"},
                       "->": {precedence: 1050, fixity: "xfy"},
                       "*->": {precedence: 1050, fixity: "xfy"},
                       ",": {precedence: 1000, fixity: "xfy"},
                       ":=": {precedence: 990, fixity: "xfx"},
                       "<": {precedence: 700, fixity: "xfx"},
                       "=": {precedence: 700, fixity: "xfx"},
                       "=..": {precedence: 700, fixity: "xfx"},
                       "=@=": {precedence: 700, fixity: "xfx"},
                       "=:=": {precedence: 700, fixity: "xfx"},
                       "=<": {precedence: 700, fixity: "xfx"},
                       "==": {precedence: 700, fixity: "xfx"},
                       "=\=": {precedence: 700, fixity: "xfx"},
                       ">": {precedence: 700, fixity: "xfx"},
                       ">=": {precedence: 700, fixity: "xfx"},
                       "@<": {precedence: 700, fixity: "xfx"},
                       "@=<": {precedence: 700, fixity: "xfx"},
                       "@>": {precedence: 700, fixity: "xfx"},
                       "@>=": {precedence: 700, fixity: "xfx"},
                       "\=": {precedence: 700, fixity: "xfx"},
                       "\==": {precedence: 700, fixity: "xfx"},
                       "is": {precedence: 700, fixity: "xfx"},
                       ">:<": {precedence: 700, fixity: "xfx"},
                       ":<": {precedence: 700, fixity: "xfx"},
                       ":": {precedence: 600, fixity: "xfy"},
                       "+": {precedence: 500, fixity: "yfx"},
                       "-": {precedence: 500, fixity: "yfx"},
                       "/\\": {precedence: 500, fixity: "yfx"},
                       "\\/": {precedence: 500, fixity: "yfx"},
                       "xor": {precedence: 500, fixity: "yfx"},
                       "*": {precedence: 400, fixity: "yfx"},
                       "/": {precedence: 400, fixity: "yfx"},
                       "//": {precedence: 400, fixity: "yfx"},
                       "rdiv": {precedence: 400, fixity: "yfx"},
                       "<<": {precedence: 400, fixity: "yfx"},
                       ">>": {precedence: 400, fixity: "yfx"},
                       "mod": {precedence: 400, fixity: "yfx"},
                       "rem": {precedence: 400, fixity: "yfx"},
                       "**": {precedence: 200, fixity: "xfx"},
                       "^": {precedence: 200, fixity: "xfy"}};

// This returns a javascript object representation of the term. It takes the two extra args because of some oddities with Prolog:
// 1) If we are reading foo(a, b) and we are at the a, we would accept the , as part of the LHS. ie, we think (a,b) is the sole argument. Instead, we should make , have
//    very high precedence if we are reading an arg. Of course, () can reduce this again, so that foo((a,b)) does indeed read ,(a,b) as the single argument
// 2) | behaves slightly differently in lists, in a similar sort of way
function read_expression(s, precedence, isarg, islist, expression)
{
    var token = {};
    if (!read_token(s, token))
        return false;
    token = token.value;
    if (token == null)
    {        
        expression.value = {end_of_file:true};
        return true;
    }
    var lhs;
    // Either the token is an operator, or it must be an atom (or the start of a list or curly-list)
    var op = prefix_operators[token];
    if (op === undefined)
    {  
        if (token == "\"")
        {
            // We have to just read chars until we get a close " (taking care with \" in the middle)
            var args = [];
            var t = 0;
            var mode = 0;
            if (prolog_flag_values['double_quotes'] == "chars")
                mode = 0;
            else if (prolog_flag_values['double_quotes'] == "codes")
                mode = 1;
            else if (prolog_flag_values['double_quotes'] == "atom")
                mode = 2;
            while (true)
            {
                t = get_raw_char_with_conversion(s.stream);
                if (t == '"')
                    break;
                if (t == "\\")
                {
                    if (peek_raw_char_with_conversion(s.stream) == '"')
                    {
                        get_raw_char_with_conversion(s.stream);
                        if (mode == 1)
                            args.push('"'.charCodeAt(0));
                        else
                            args.push('"');
                        continue;
                    }
                }
                if (mode == 1)
                    args.push(t.charCodeAt(0));                
                else
                    args.push(t);
            }
            if (mode == 2)
                lhs = args.join('');
            else
                lhs = {list: args, tail: "[]"};
        }
        else if (token == "[" || token == "{")
        {
            // The principle for both of these is very similar
            var args = [];
            var next = {};
            while(true)
            {
                var t = {};
                if (!read_expression(s, Infinity, true, true, t))
                    return false;
                t = t.value;
                if (t == "]")
                {
                    lhs = "[]";
                    break;
                    // Special case for the empty list, since the first argument is ']'
                }
                args.push(t);
                next = {};
                if (!read_token(s, next))
                    return false;               
                next = next.value;
                if (next == ',')
                    continue;
                else if (next == "]" && token == "[")
                {
                    lhs = {list: args, tail: "[]"};
                    break;
                }
                else if (next == "}" && token == "{")
                {
                    lhs = {functor: "{}", args:args};
                    break;
                }
                else if (next == "|" && token == "[")
                {
                    var tail = {};
                    if (!read_expression(s, Infinity, true, true, tail))
                        return false;
                    lhs = {list: args, tail: tail.value},
                    next = {};
                    if (!read_token(s, next))
                        return false;
                    next = next.value;
                    if (next == "]")
                        break;
                    else
                        return syntax_error("missing ]");
                }
                else
                    return syntax_error("mismatched " + token + " at " + next);
            }
        }
        else if (token == "(")
        {
            // Is this right? () just increases the precedence to infinity and reads another term?
            var lhs = {};
            if (!read_expression(s, Infinity, false, false, lhs))
                return false;
            lhs = lhs.value;
            next = {};
            if (!read_token(s, next))
                return false;
            next = next.value;
            if (next != ")")
                return syntax_error("mismatched ( at " + next);
        }
        else
        {
            // It is an atom
            lhs = token;
        }
    }
    else if (op.fixity == "fx")
    {
        var arg = {};
        if (!read_expression(s, op.precedence, isarg, islist, arg))
            return false;
        lhs = {functor: token, args:[arg.value]};
    }
    else if (op.fixity == "fy")
    {
        var arg = {};
        if (!read_expression(s, op.precedence+0.5, isarg, islist, arg))
            return false;
        lhs = {functor: token, args:[arg.value]};
    }
    else
        return false; // Parse error    
    while (true)
    {
        var infix_operator = {};
        if (!peek_token(s, infix_operator))
            return false;
        infix_operator = infix_operator.value;
        if (typeof(infix_operator) == "number" && infix_operator <= 0)
        {
            // Yuck. This is when we read something like X is A-1. Really the - is -/2 in this case
            read_token(s, {});
            unread_token(s, Math.abs(infix_operator));
            unread_token(s, "-");
            infix_operator = "-";
        }
        if (infix_operator == '(')
        {
            // We are reading a term. Keep reading expressions: After each one we should
            // either get , or )
            // First though, consume the (
            read_token(s, {});
            var args = [];
            var next = {};
            while (true)
            {
                var arg = {};
                if (!read_expression(s, Infinity, true, false, arg))
                    return false;
                args.push(arg.value);
                next = {};
                if (!read_token(s, next))
                    return false;
                next = next.value;
                if (next == ')')
                    break;
                else if (next == ',')
                    continue;
                else
                {
                    if (next == null)
                        return syntax_error("end_of_file");
                    else
                        return syntax_error(next);
                }
            }
            // ./2 is a list
            if (lhs == "." && args.length == 2)
            {
                lhs = {list: args[0],
                       tail: args[1]};
            }
            else
            {
                lhs = {functor: lhs,
                       args:args};
            }
            // Now, where were we?
            infix_operator = {};
            if (!peek_token(s, infix_operator))
                return false;
            infix_operator = infix_operator.value;
        }
        // Pretend that . is an operator with infinite precedence
        if (infix_operator == ".")
        {
            expression.value = lhs;
            return true;
        }
        if (infix_operator == "," && isarg)
        {
            expression.value = lhs;
            return true;
        }
        if (infix_operator == "|" && islist)
        {
            expression.value = lhs;
            return true;
        }
        if (infix_operator == null)
        {
            expression.value = lhs;
            return true;
        }            
        op = infix_operators[infix_operator];
        if (op !== undefined)
        {
            if (op.fixity == "xfx" && precedence > op.precedence)
            {
                lhs = parse_infix(s, lhs, op.precedence);
                if (lhs == false)
                    return false;
            }
            else if (op.fixity == "xfy" && precedence > op.precedence)
            {
                // Is this 0.5 thing right? Will it eventually drive up precedence to the wrong place? We never want to reach the next integer...
                lhs = parse_infix(s, lhs, op.precedence+0.5); 
                if (lhs == false)
                    return false;
            }
            else if (op.fixity == "yfx" && precedence >= op.precedence)
            {
                lhs = parse_infix(s, lhs, op.precedence);
                if (lhs == false)
                    return false;
            }
            else if (op.fixity == "xf" && precedence > op.precedence)
            {
                lhs = parse_postfix(s, lhs, op.precedence);
                if (lhs == false)
                    return false;
            }
            else if (op.fixity == "yf" && precedence >= op.precedence)
            {
                lhs = parse_postfix(s, lhs, op.precedence);
                if (lhs == false)
                    return false;
            }
            else
            {
                expression.value = lhs;
                return true;
            }
        }
        else
        {
            expression.value = lhs;
            return true;
        }
    }
}

function parse_term_options(options)
{
    var result = {};
    var yes = lookup_atom("true");
    while (options != NIL)
    {
        if (TAG(options) != TAG_LST)
            return type_error("list", options);
        var head = memory[VAL(options)];
        if (TAG(head) != TAG_STR)
            return type_error("option", head);
        var ftor = memory[VAL(head)];
        if (ftor == lookup_functor("quoted",1))
        {
            result.quoted = (memory[VAL(head)+1] == yes)
        } 
        else if (ftor == lookup_functor("ignore_ops",1))
        {
            result.ignore_ops = (memory[VAL(head)+1] == yes)
        }
        else if (ftor == lookup_functor("numbervars",1))
        {
            result.numbervars = (memory[VAL(head)+1] == yes)
        }
        else if (ftor == lookup_functor("variables",1))
        {
            result.variables = memory[VAL(head)+1];
        }
        else if (ftor == lookup_functor("variable_names",1))
        {
            result.variable_names = memory[VAL(head)+1];
        }
        else if (ftor == lookup_functor("singletons",1))
        {
            result.singletons = memory[VAL(head)+1];
        }
        else
        {
            return type_error(option, head);
        }
        options =  memory[VAL(options)+1];
    }
    return result;
}

function read_term(stream, term, options)
{
    if (!(options = parse_term_options(options)))
        return false;
    var streamindex = VAL(get_arg(stream, 1));
    var s = streams[streamindex];
    var context = {stream:s, peeked_token: undefined};
    var expression = {};
    if (!read_expression(context, Infinity, false, false, expression))
        return false;
    expression = expression.value;
    // Depending on the situation, we may expect a . now on the stream. 
    // There will not be one if we are going to return end_of_file because it is actually the eof
    // (Of course, if the file contains end_of_file. then we will return end_of_file AND read the .
    // Luckily we can distinguish the two cases
    // There will also not be one if we are in atom_to_term mode, which is not yet implemented    
    if (expression.end_of_file === undefined)
    {
        var period = {};
        if (!read_token(context, period))
            return false;
        if (period.value != ".") // Missing period === eof
            return syntax_error("end_of_file");
    }
    else
        expression = "end_of_file";
    debug_msg("Read expression: " + expression_to_string(expression));
    
    var varmap = {};
    var singletons = {};
    t1 = expression_to_term(expression, varmap, singletons);
    var rc = 1;
    if (options.variables !== undefined || options.singletons !== undefined)
    {
        var equals2 = lookup_functor("=", 2);
        var keys = Object.keys(varmap);
        for (var i = 0; i < keys.length; i++)
        {
            var varname = keys[i];
            if (options.variables !== undefined)
            {                
                if (!unify(state.H ^ (TAG_LST << WORD_BITS), options.variables))
                    return false;
                memory[state.H] = varmap[varname];
                memory[state.H+1] = (state.H+1) ^ (TAG_REF << WORD_BITS);
                options.variables = memory[state.H+1];
                state.H+=2;
            }
            if (options.variable_names !== undefined)
            {                
                if (!unify(state.H ^ (TAG_LST << WORD_BITS), options.variable_names))
                {
                    debug("not unifiable: " + term_to_string(options.variable_names));
                    return false;
                }
                memory[state.H] = (state.H+2) ^ (TAG_STR << WORD_BITS);
                memory[state.H+1] = (state.H+1) ^ (TAG_REF << WORD_BITS);
                options.variable_names = memory[state.H+1];
                memory[state.H+2] = equals2;
                memory[state.H+3] = lookup_atom(varname);
                memory[state.H+4] = varmap[varname];
                state.H+=5;
            }
        }
        if (options.variables !== undefined)
            if (!unify(options.variables, NIL))
                return false;
        if (options.variable_names !== undefined)
            if (!unify(options.variable_names, NIL))
                return false;       
    }
    if (options.singletons !== undefined)
    {
        var keys = Object.keys(singletons);
        for (var i = 0; i < keys.length; i++)
        {
            var varname = keys[i];
            if (singletons[varname] == 1)
            {
                if (!unify(state.H ^ (TAG_LST << WORD_BITS), options.singletons))
                    return false;
                memory[state.H] = (state.H+2) ^ (TAG_STR << WORD_BITS);
                memory[state.H+1] = (state.H+1) ^ (TAG_REF << WORD_BITS);
                options.singletons = memory[state.H+1];
                memory[state.H+2] = equals2;
                memory[state.H+3] = lookup_atom(varname);
                memory[state.H+4] = varmap[varname];
                state.H+=5;
            }
        }
        if (!unify(options.singletons, NIL))
            return false;      
    }
    debug_msg("A term has been created ( " + VAL(t1) + " ). Reading it back from the heap gives: " + term_to_string(t1));
    return unify(term, t1);
}

function predicate_write_term(stream, term, options)
{
    if (!(options = parse_term_options(options)))
        return false;
    var value = format_term(term, options);
    var s = {};
    if (!get_stream(stream, s))
        return false;
    s = s.value;
    if (s.write == null)
        return permission_error("output", "stream", stream);
    
    var bytes = toByteArray(value);
    return (s.write(s, 1, bytes.length, bytes) >= 0)
}

function escape_atom(a)
{
    chars = a.split('');
    var result = "";
    for (var i = 0; i < chars.length; i++)
    {
        if (chars[i] == "'")
            result += "\\'";
        else
            result += chars[i];       
    }
    return result;
}

function quote_atom(a)
{
    if (a.charAt(0) >= "A" && a.charAt(0) <= "Z")
        return "'" + escape_atom(a) + "'";
    chars = a.split('');
    if (is_punctuation(chars[0]))
    {
        for (var i = 0; i < chars.length; i++)
        {
            if (!is_punctuation(chars[i]))
                return "'" + escape_atom(a) + "'";
        }
    }
    else
    {
        for (var i = 0; i < chars.length; i++)
        {
            if (is_punctuation(chars[i]) || chars[i] == ' ')
                return "'" + escape_atom(a) + "'";
        }
    }
    return a;
}

function is_operator(ftor)
{
    ftor = VAL(ftor);
    if (ftable[ftor][1] == 2 && infix_operators[atable[ftable[ftor][0]]] != undefined)
        return true;
    if (ftable[ftor][1] == 1 && prefix_operators[atable[ftable[ftor][0]]] != undefined)
        return true;
    return false;
}


function format_term(value, options)
{
    if (value == undefined)
        abort("Illegal memory access in format_term: " + hex(value) + ". Dumping...");
    value = deref(value);
    switch(TAG(value))
    {
    case TAG_REF:
        if (VAL(value) > HEAP_SIZE)
        {
            if (state.E > state.B)
                lTop = state.E + state.CP.code[state.CP.offset - 1] + 2;
            else
                lTop = state.B + memory[state.B] + 8;
            return "_L" + (lTop - VAL(value));
        }
        else
            return "_G" + VAL(value);
    case TAG_ATM:
        atom = atable[VAL(value)];
        if (atom == undefined)
            abort("No such atom: " + VAL(value));
        if (options.quoted === true)
            return quote_atom(atom);
        return atom;
    case TAG_INT:
        if ((VAL(value) & (1 << (WORD_BITS-1))) == (1 << (WORD_BITS-1)))
            return (VAL(value) - (1 << WORD_BITS)) + "";
        else
            return VAL(value) + "";
        // fall-through
    case TAG_FLT:
        return floats[VAL(value)] + "";
    case TAG_STR:
        var ftor = VAL(memory[VAL(value)]);
        if (options.numbervars === true && ftor == lookup_functor('$VAR', 1) && TAG(memory[VAL(value)+1]) == TAG_INT)
        {
            var index = VAL(memory[VAL(value)+1]);
            var result = String.fromCharCode(65 + (index % 26));
            if (index >= 26)
                result = result + Math.floor(index / 26);
            return result;
        }
        if (!is_operator(ftor) || options.ignore_ops === true)
        {
            // Print in canonical form functor(arg1, arg2, ...)
            var result = format_term(ftable[ftor][0] ^ (TAG_ATM << WORD_BITS), options) + "(";
            for (var i = 0; i < ftable[ftor][1]; i++)
            {
                result += format_term(memory[VAL(value)+1+i], options);
                if (i+1 < ftable[ftor][1])
                    result += ",";
            }
            return result + ")";            
        }
        else
        {
            // Print as an operator
            var fname = atable[ftable[ftor][0]];
            if (ftable[ftor][1] == 2 && infix_operators[fname] != undefined)
            {
                // Infix operator
                var lhs = format_term(memory[VAL(value)+1], options);
                if (is_punctuation(lhs.charAt(lhs.length-1)) && !is_punctuation(fname.charAt(0)))
                    result = lhs + fname;
                else if (!is_punctuation(lhs.charAt(lhs.length-1)) && is_punctuation(fname.charAt(0)))
                    result = lhs + fname;
                else
                {
                    result = lhs + " " + fname;
                }
                var rhs = format_term(memory[VAL(value)+2], options);
                if (is_punctuation(rhs.charAt(0)) && !is_punctuation(fname.charAt(fname.length-1)))
                    return result + rhs;
                else if (!is_punctuation(rhs.charAt(0)) && is_punctuation(fname.charAt(fname.length-1)))
                    return result + rhs;
                else
                    return result + " " + rhs;
            }
            else if (ftable[ftor][1] == 1 && prefix_operators[fname] != undefined)
            {
                // Prefix operator
                var rhs = format_term(memory[VAL(value)+1], options);
                if (is_punctuation(rhs.charAt(0)) && !is_punctuation(fname.charAt(fname.length-1)))
                    return fname + rhs;
                else if (!is_punctuation(rhs.charAt(0)) && is_punctuation(fname.charAt(fname.length-1)))
                    return fname + rhs;
                else
                    return fname + " " + rhs;

            }
        }
    case TAG_LST:
        if (options.ignore_ops)
            return "'.'(" + format_term(memory[VAL(value)], options) + "," + format_term(memory[VAL(value)+1], options) + ")";
        // Otherwise we need to print the list in list-form
        var result = "[";
        var head = memory[VAL(value)];
        var tail = memory[VAL(value)+1];
        while (true)
        {
            result += format_term(head, options);
            if (tail == NIL)
                return result + "]";
            else if (TAG(tail) == TAG_LST)
            {
                head = memory[VAL(tail)];
                tail = memory[VAL(tail)+1];
                result += ",";
            }
            else 
                return result + "|" + format_term(tail, options) + "]";
        }        
    }
}


function expression_to_term(s, varmap, singletons)
{
    if (typeof(s) == "string")
        return lookup_atom(s);
    else if (typeof(s) == "number")
    {
        if (s == ~~s)
        {
            return (s & ((1 << WORD_BITS)-1)) ^ (TAG_INT << WORD_BITS);
        }
        else
        {
            return lookup_float(s);
        }
    }
    else if (s.variable_name !== undefined)
    {
        if (varmap[s.variable_name] !== undefined)
        {
            result = state.H;            
            memory[state.H] = varmap[s.variable_name];
            state.H++;
        }
        else
        {
            result = alloc_var();
            varmap[s.variable_name] = result;            
        }
        if (singletons[s.variable_name] === undefined)
            singletons[s.variable_name] = 1;
        else
            singletons[s.variable_name]++;
        return result;
    }
    else if (s.list !== undefined)
    {   
        // Special case for [], as usual, since we do not actually allocate any lists!
        if (s.list.length == 0)
            return NIL;

        var result = alloc_var();
        var tail = result;
        var head;
        for (var i = 0; i < s.list.length; i++)
        {
            unify(tail, state.H ^ (TAG_LST << WORD_BITS));
            head = alloc_var();
            tail = alloc_var();
            unify(head, expression_to_term(s.list[i], varmap, singletons));
        }
        unify(tail, expression_to_term(s.tail, varmap, singletons));
        return result;
    }
    else if (s.functor !== undefined)
    {
        var t = (state.H ^ TAG_STR << WORD_BITS);
        memory[state.H++] = lookup_functor(s.functor, s.args.length);
        // Reserve space for the args
        var var_args = [];
        for (var i = 0; i < s.args.length; i++)
            var_args[i] = alloc_var();
        for (var i = 0; i < s.args.length; i++)
        {
            z = expression_to_term(s.args[i], varmap, singletons);
            unify(z, var_args[i]);
        }
        return t;
    }
    else
        abort("Invalid expression: " + JSON.stringify(s));
}

function peek_token(s, t)
{
    if (s.peek_tokens === undefined || s.peeked_tokens.length == 0 )
    {
        var tt = {};
        if (!read_token(s, tt))
            return false;
        s.peeked_tokens = [tt.value];
    }
    t.value = s.peeked_tokens[0];
    return true;
}

function unread_token(s, t)
{
    if (s.peeked_tokens === undefined)
        s.peeked_tokens = [t];
    else
        s.peeked_tokens.push(t);
}

function read_token(s, t)
{
    if (s.peeked_tokens !== undefined && s.peeked_tokens.length != 0)
    {
        t.value = s.peeked_tokens.pop();
        return true;
    }
    if (!lex(s.stream, t))
        return false;
    return true;
}

function is_char(c)
{
    return ((c >= 'a' && c <= 'z') ||
            (c >= 'A' && c <= 'Z') ||
            (c >= '0' && c <= '9') ||
            c == '_');
}

var punctuation_array = ['`', '~', '@', '#', '$', '^', '&', '*', '-', '+', '=', '<', '>', '/', '?', ':', ',', '\\', '.'];

function is_punctuation(c)
{
    return punctuation_array.indexOf(c) != -1;
}

// lex(stream, t) returns a single token in t.value and fails if an exception is raised
function lex(s, t)
{
    var token;
    while(true)
    {
        var c = get_raw_char_with_conversion(s);
        if (c == -1)
        {
            t.value = null;
            return true;
        }
        // Consume any whitespace
        if (c == ' ' || c == '\n' || c == '\t')
            continue;        
        else if (c == '%')
        {
            do
            {
                d = get_raw_char_with_conversion(s);
                if (d == -1)
                {
                    t.value = null;
                    return true;
                }
            } while(d != '\n');
            continue;
        }
        else if (c == '/')
        {
            d = peek_raw_char_with_conversion(s);
            if (d == '*')
            {
                // Block comment
                get_raw_char_with_conversion(s);
                while(true)
                {
                    d = get_raw_char_with_conversion(s);
                    if (d == -1)
                        return syntax_error("end of file in block comment");
                    if (d == '*' && get_raw_char_with_conversion(s) == '/')
                        break;
                }
                continue;
            }
            else
            {
                // My mistake, the term actually begins with /. c is still set to the right thing
                break;
            }
        }
        break;
    }    
    if ((c >= 'A' && c <= 'Z') || c == '_')
    {
        token = {variable_name: "" + c};
        // Variable. May contain a-zA-Z0-9_
        while (true)
        {
            c = peek_raw_char_with_conversion(s);
            if (is_char(c))
            {
                token.variable_name += get_raw_char_with_conversion(s);
            }
            else
            {
                t.value = token; 
                return true;
            }
        } 
    }
    else if ((c >= '0' && c <= '9') || (c == '-' && peek_raw_char_with_conversion(s) >= '0' && peek_raw_char_with_conversion(s) <= '9'))
    {
        // Integer. May contain 0-9 only. Floats complicate this a bit
        var negate = false;
        if (c == '-')
        {
            token = '';
            negate = true;
        }
        else
            token = c - '0';
        var decimal_places = 0;
        var seen_decimal = false;
        while (true)
        {            
            c = peek_raw_char_with_conversion(s);       
            if (seen_decimal)
                decimal_places++;
            if ((c >= '0' && c <= '9'))
            {
                token = token * 10 + (get_raw_char_with_conversion(s) - '0');
            }
            else if (c == '.' && !seen_decimal)
            {
                // Fixme: Also must check that the next char is actually a number. Otherwise 'X = 3.' will confuse things somewhat.
                seen_decimal = true;
                get_raw_char_with_conversion(s);
                continue;
            }
            else if (is_char(c))
                return syntax_error("illegal number" + token + ": " + c);
            else
            {
                if (seen_decimal)
                {
                    for (var i = 1; i < decimal_places; i++)
                        token = token / 10;
                }
                t.value = negate?(-token):token;
                return true;
            }
        }
    }
    else 
    {
        // Either:
        // 1) a term
        // 2) an atom (which is a term with no arguments) 
        // 3) An operator
        // In all cases, first we have to read an atom
        var buffer = "";
        var state = 0;
        if (c == '\'')
        {
            // Easy. The atom is quoted!
            while(true)
            {
                c = get_raw_char_with_conversion(s);
                if (c == '\\')
                    state = (state + 1) % 2;
                if (c == -1)
                    return syntax_error("end of file in atom");
                if (c == '\'' && state == 0)
                    break;
                buffer += c;
            }
            
        }
        else // Not so simple. Have to read an atom using rules, which are actually available only for a fee from ISO...
        {
            buffer += c;
            // An unquoted atom may contain either all punctuation or all A-Za-z0-9_. There are probably more complicated rules, but this will do
            char_atom = is_char(c);
            punctuation_atom = is_punctuation(c);
            while (true)
            {                
                c = peek_raw_char_with_conversion(s);                
                if (c == -1)
                    break;
                if (char_atom && is_char(c))
                    buffer += get_raw_char_with_conversion(s);
                else if (punctuation_atom && is_punctuation(c))
                    buffer += get_raw_char_with_conversion(s);
                else
                    break;
            }            
        }
        t.value=buffer;
        return true;
    }
}

// This is one of the more ridiculous things in the ISO standard
var char_conversion_override = {};
function predicate_char_conversion(a, b)
{
    if (TAG(a) != TAG_ATM)
        return type_error("atom", a);
    if (TAG(b) != TAG_ATM)
        return type_error("atom", b);
    char_conversion_override[atable[VAL(a)]] = atable[VAL(b)];
    return true;
}

function predicate_current_char_conversion(a, b)
{
    if (TAG(a) == TAG_ATM)
    {
        var aname = atable[VAL(a)];
        if (char_conversion_override[aname] === undefined)
            return unify(a, b);
        else
            return unify(lookup_atom(char_conversion_override[aname]), b);
    }
    else if (TAG(b) == TAG_ATM)
    {
        var bname = btable[VAL(b)];
        var keys = Object.keys(char_conversion_override);
        for (var i = 0; i < keys.length; i++)
        {
            if (char_conversion_override[keys[i]] == bname)
                return unify(lookup_atom(keys[i]), a);
        }
        return unify(a,b);
    }
    if (TAG(a) == TAG_REF && TAG(b) == TAG_REF)
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
        aname = String.fromCharCode(index);
        unify(a, lookup_atom(aname));
        if (char_conversion_override[aname] === undefined)
            return unify(a, b);
        else
            return unify(lookup_atom(char_conversion_override[aname]), b);

    }
    else
        return type_error(a);
}

function get_raw_char_with_conversion(s)
{
    if (!prolog_flag_values['char_conversion'])
        return get_raw_char(s);    
    var t = get_raw_char(s);
    var tt = char_conversion_override[t];
    if (tt === undefined)
        return t;
    else
        return tt;
}

function peek_raw_char_with_conversion(s)
{
    if (!prolog_flag_values['char_conversion'])
        return peek_raw_char(s);    
    var t = peek_raw_char(s);
    var tt = char_conversion_override[t];
    if (tt === undefined)
        return t;
    else
        return tt;
}


function parser_test()
{
    //do_parser_test("test(1,1).\ntest(1:-1).\ntest:- test, test.\ntest((1,1)).");
    //do_parser_test("foo:- a, b, c.");
    do_parser_test("foo([a|b]).");
}

function parser_test_read(stream, size, count, buffer)
{
    var bytes_read = 0;
    var records_read;
    for (records_read = 0; records_read < count; records_read++)
    {
        for (var b = 0; b < size; b++)
        {
            t = stream.data.shift();
            if (t === undefined)
            {                
                return records_read;
            }
            buffer[bytes_read++] = t;
        }
    }
    return records_read;
}

function do_parser_test(input_string)
{
    s = {peeked_token: undefined,
         stream: new_stream(parser_test_read,
                            null,
                            null,
                            null,
                            null,
                            toByteArray(input_string))};
    state = {H:0};
    while(true)
    {        
        var e = {};
        if (!read_expression(s, Infinity, false, false, e))
        {
            debug("Failed to parse");
            return false;
        }
        e = e.value;
        if (e.end_of_file == true)
            break;
        debug("Read expression: " + expression_to_string(e));
        
        var p = {};
        if (!read_token(s, p))
        {
            debug("Failed to parse");
            return false;
        }
        p = p.value;
        if (p == ".")
        {
            debug_msg("Expression terminated with fullstop")
        }
        else
        {
            debug("Error: Expression terminated with >" + p + "<");
        }
        debug_msg(expression_to_string(e));
        if (e.end_of_file !== undefined)
            break;
    }
}

function expression_to_string(s)
{
    if (typeof(s) == "string")
        return s;
    if (typeof(s) == "number")
        return s;
    if (s.variable_name !== undefined)
        return "_" + s.variable_name;
    if (s.list !== undefined)
    {
        t = "[";
        for (var i = 0; i < s.list.length; i++)
        {
            if (i+1 < s.list.length)
                t += expression_to_string(s.list[i]) + ", ";
            else
            {
                t += expression_to_string(s.list[i]) 
                if (s.tail == "[]")
                    t += "]";
                else
                    t += "|" + expression_to_string(s.tail) + "]";
            }
        }
        return t;
    }
    if (s.functor !== undefined)
    {
        t = "" + s.functor + "(";
        for (var i = 0; i < s.args.length; i++)
        {
            if (i+1 < s.args.length)
            {
                t += expression_to_string(s.args[i]) + ", ";
            }
            else
                t += expression_to_string(s.args[i]) + ")";
        }
        return t;
    }
}


function atom_to_term(atom, term, bindings)
{
    var stream = new_stream(read_atom, null, null, null, null, {data:toByteArray(atable[VAL(atom)]), ptr:0});
    var context = {stream:stream, peeked_token: undefined};
    var expression = {};
    if (!read_expression(context, Infinity, false, false, expression))
        return false;
    expression = expression.value;
    b = {};
    t1 = expression_to_term(expression, b, {});
    arglist = [];
    keys = Object.keys(b);
    for (var i = 0 ; i < keys.length; i++)
        arglist.push({functor:"=", args:[keys[i], {variable_name:keys[i]}]});
    t2 = expression_to_term({list:arglist, tail:{list: []}}, b, {});
    debug_msg("Expression: " + expression_to_string({list:arglist, tail:[]}));
    debug_msg("Bindings have been created ( " + VAL(t2) + " ). Reading it back from the heap gives: " + term_to_string(t2));
    return unify(term, t1) && unify(bindings, t2);
}

function read_atom(stream, size, count, buffer)
{
    var bytes_read = 0;
    var records_read;
    var info = stream.data;
    for (records_read = 0; records_read < count; records_read++)
    {
        for (var b = 0; b < size; b++)
        {
            t = info.data[info.ptr++];            
            if (t === undefined)
                return records_read;
            buffer[bytes_read++] = t;
        }
    }
    return records_read;
}

