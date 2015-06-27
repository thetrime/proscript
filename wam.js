/* For general documentation, see wam_compiler.pl

Some helpful diagrams:
Environment frame looks like this:
              -----------
    state.E ->|0  | CE  |
              |1  | CP  |
              |2  | Y0  |
              |...|     |
              |n+1| Yn  |
              -----------

Choicepoint frame where we have tried something but can try 'Next' if it fails looks like this:
(There are n arguments, labelled from A0 to An-1)

              -------------
    state.B ->|0  | n     |
              |1  | A0    |
              |2  | A1    |
              |...|       |
              |n  | An-1  |
              |n+1| E     |
              |n+2| CP    |
              |n+3| B     |
              |n+4| Next  |
              |n+5| TR    |
              |n+6| H     |
              |n+7| B0    |
              -------------

*/



var ftable = [];
var atable = ['[]']; // Reserve first atom as [].
var floats = [];
var predicates = {};
var exception = null;

/* Constants. Should be auto-generated */
var HEAP_SIZE = 131070;
var STACK_SIZE = 65535;
var TRAIL_SIZE = 1000;
var READ = 0;
var WRITE = 1;
var TAG_REF = 0; // 0x00000000
var TAG_STR = 1; // 0x08000000
var TAG_LST = 2; // 0x10000000
var TAG_INT = 3; // 0x18000000
var TAG_ATM = 4; // 0x20000000
var TAG_FLT = 5; // 0x28000000
///////////// 6 is currently unused
var TAG_EXT = 7; // Reserved!
var TAG_MASK = 7;
// 3 bits are used for the tag
// 2 bits are used for GC
// This leaves 27 for the actual value, since javascript does not have 64-bit integers
var WORD_BITS = 27;
var M_BIT = 1 << 30;
var F_BIT = 1 << 31;
var NV_MASK = M_BIT | F_BIT | (TAG_MASK << WORD_BITS);

var NIL = (TAG_ATM << WORD_BITS); // atable[0] = '[]', so NIL is 0 xor TAG_ATM, which is just TAG_ATM.

var memory = new Array(HEAP_SIZE + STACK_SIZE + TRAIL_SIZE);
var code = [255];
var register = new Array(256);
var state;
var PDL = [];

// Stack for managing cleanup handlers needed during a cut
var cleanups = [];

/* Special purpose machine registers:

   P: Pointer to the next opcode to execute (in the code[] array)
  CP: Continuation Pointer. Points to the next code to execute if the current environment succeeds (basically the return address when calling a function)
mode: READ or WRITE depending on whether are matching or creating an exemplar on the heap
   H: Pointer to the next available heap cell
  HB: Pointer to where the heap should be truncated to if we backtrack
  TR: Pointer to the next available trail cell
   S: Pointer to the next symbol on the heap to match when unifying
   E: Pointer to the top environment frame   
   B: Pointer to the top choicepoint
  B0: Pointer to the choicepoint to return to after backtracking over a cut (ie the choicepoint created by the most recent call opcode)


  It is important to note that B and E do not point to the *next available* place to put an environment frame or choicepoint, but the *current* one.
*/
var debugging = true;
function debug_msg(msg)
{
    if (debugging)
        debug(msg);
}

function initialize()
{
    state = {H: 0,
             HB: 0,
             S: 0,
             P: 2,             
             CP: {code: bootstrap_code, 
                  predicate: null,
                  offset:1}, // halt
             B0: 0, // No backtrack frame
             B: 0,  // No backtrack frame
             E: HEAP_SIZE,
             TR: HEAP_SIZE + STACK_SIZE,
             mode: READ,
             running: true,
             foreign_retry: false,
             num_of_args: 0,
             S: 0,
             current_predicate: null};
    code = bootstrap_code;
}

function abort(why)
{        
    debug(why);
    throw why;
}

function bind(a, b)
{
    if (TAG(a) == TAG_REF && (TAG(b) != TAG_REF || VAL(b) < VAL(a)))
    {
        memory[VAL(a)] = b;
        trail(a);
    }
    else
    {
        memory[VAL(b)] = a;
        trail(b);
    }
}

function tidy_trail()
{
    t = memory[state.B + memory[state.B] + 5];
    if (t < HEAP_SIZE + STACK_SIZE)
        abort("Backtrack pointer " + state.B + " has garbage for TR: " + hex(t));
    while (t < state.TR)
    {
        if ((memory[t] < state.HB) || (state.H < memory[t] && memory[t] < state.B))
        {
            // This trailing is still required
            t = t + 1;
        }
        else
        {
            memory[t] = memory[state.TR - 1];
            state.TR = state.TR - 1;
        }
    }   
}

function trail(v)
{
    if (v < state.HB || (state.H < v && v < state.B))
    {
        debug_msg("Trailing " + v);
        memory[state.TR++] = v;
    }
    else
    {
        debug_msg("NOT Trailing " + v + " because neither v < " + state.HB + " nor " + state.H + " < v < " + state.B);
    }
}

function unwind_trail(from, to)
{
    debug_msg("unwinding trail from " + from + " to " + to);
    for (var i = from; i < to; i++)
    {
        memory[memory[i]] = memory[i] ^ (TAG_REF << WORD_BITS);
    }
}

// Returns boolean
function unify(a, b)
{
    PDL.push(a);
    PDL.push(b);
    var failed = false;
    while (PDL.length != 0 && !failed)
    {
        var d1 = deref(PDL.pop());
        var d2 = deref(PDL.pop());
        // if d1 == d2 then just proceed with the rest of the PDL. Otherwise we need to try and unify them, or fail
        if (d1 != d2)
        {
            type1 = TAG(d1);
            val1 = VAL(d1);
            type2 = TAG(d2);
            val2 = VAL(d2);          
            if (type1 == TAG_REF)
            {
                bind(d1, d2);
            }
            else
            {
                switch(type2)
                {
                case TAG_REF:
                    bind(d1, d2);
                    break;
                case TAG_ATM:
                case TAG_INT:
                    failed = true;
                    break;
                case TAG_FLT:
                    if (type1 == TAG_FLT) 
                    {
                        debug(floats[val1] + " vs " + floats[val2]);
                    }
                    failed = true;
                    break;
                case TAG_LST:
                    if (type1 == TAG_LST)
                    {                        
                        PDL.push(memory[val1]); // unify heads
                        PDL.push(memory[val2]);
                        PDL.push(memory[val1+1]); // unify tails
                        PDL.push(memory[val2+1]);
                    }
                    else
                        failed = true; // list and non-list
                    break;
                case TAG_STR:
                    if (type1 == TAG_STR)
                    {
                        f1 = VAL(memory[val1]);
                        f2 = VAL(memory[val2]);
                        if (f1 == f2)
                        {
                            for (var i = 0; i < ftable[f1][1]; i++)
                            {
                                PDL.push(val1 + 1 + i);
                                PDL.push(val2 + 1 + i);
                            }
                        }
                        else
                            failed = true; // different functors
                    }
                    else
                        failed = true; // str and atom/list
                }
            }
        }
    }
    return !failed;
}

function deref(p)
{
    while(TAG(p) == TAG_REF && VAL(p) != memory[VAL(p)])
    {
        q = memory[VAL(p)];
        if (q === undefined) // FIXME: Check that q =< p?
        {
            debug_msg("Illegal memory access in deref: " + hex(p) + ". Dumping...");
            abort("Bad memory access: @" + p);
        }
        else
            p = q;
    }
    return p;
}

function explicit_deref(p)
{
    while(TAG(p) == TAG_REF && VAL(p) != memory[VAL(p)])
    {
        q = memory[VAL(p)];
        debug_msg("Dereferencing " + hex(p) + " -> " + hex(q));
        if (q === undefined)
        {
            abort("Bad memory access: @" + p);
        }
        else
            p = q;
    }
    return p;
}


// This should be a macro
function TAG(p)
{
    // >>> is unsigned-right-shift. Nice.
    return (p >>> WORD_BITS) & TAG_MASK;
}

// This should be a macro
function VAL(p)
{
    return p & ((1 << WORD_BITS)-1);
}

// Ideally this would be inlined, but javascript does not support macros. Ultimately this could be generated dynamically.
function backtrack()
{    
    debug_msg("Backtracking. State.B is " + state.B);
    if (state.B <= HEAP_SIZE)
    {
        return false;
    }
    debug_msg("Choicepoint has " + memory[state.B] + " saved args");
    state.B0 = memory[state.B + memory[state.B] + 7];
    // Also unwind any trailed bindings
    unwind_trail(memory[state.B + memory[state.B] + 5], state.TR);
    var next = memory[state.B + memory[state.B] + 4];
    state.P = next.offset;
    code = next.code;
    state.current_predicate = next.predicate;
    debug_msg("Set state.P to " + state.P);
    return true;
}

// Returns a <STR, f/n> cell. This MUST be followed (eventually) by n args. Attempting to print the term (or otherwise use) the term before then will result in chaos
// ftor must have the ATM tag!
function alloc_structure(ftor)
{
    var tmp = state.H;
    memory[state.H++] = ftor;
    return tmp ^ (TAG_STR << WORD_BITS);
}

function alloc_var()
{
    var result = state.H ^ (TAG_REF << WORD_BITS);
    memory[state.H] = result;    
    state.H++;
    return result;
}

function alloc_list()
{
    var result = (state.H+1) ^ (TAG_LST << WORD_BITS);
    memory[state.H] = result;    
    state.H++;
    return result;
}

function wam()
{
    state.running = true;
    while (state.running)
    {
        debug_msg("---");        
        debug_msg("P=" + (((state.current_predicate == null)?("no predicate"):(atable[ftable[state.current_predicate.key][0]] + "/" + ftable[state.current_predicate.key][1])) + "@" + state.P + ": " + code[state.P]) + ", H=" + state.H + ", B=" + state.B + ", B0=" + state.B0 + ", E=" + state.E);
        // Decode an instruction
        switch(code[state.P])
        {
        case 1: // allocate
            var tmpE;
            if (state.E > state.B)
            {
                debug_msg("P=" + state.P + " Top frame is an environment, at " + state.E + " with previous environment of " + memory[state.E] + " and CP of " + memory[state.E+1]);
                tmpE = state.E + state.CP.code[state.CP.offset - 1] + 2;
            }
            else
            {
                debug_msg("Top frame is a choicepoint, at " + state.B);
                tmpE = state.B + memory[state.B] + 8;
            }
            debug_msg("Environment size is: " + state.CP.code[state.CP.offset-1]);
            if (tmpE === undefined || isNaN(tmpE))
                abort("Top of frame is garbage: " + tmpE);
            if (tmpE < HEAP_SIZE || tmpE > HEAP_SIZE + STACK_SIZE)
                abort("Top of frame exceeds bounds in allocate: " + hex(tmpE));

            debug_msg("Allocating an environment at " + tmpE + " Y0 is at " + (tmpE + 2) + " state.B is " + state.B);
            // Save old environment and continuation
            memory[tmpE] = state.E;
            memory[tmpE + 1] = state.CP
            state.E = tmpE;
            state.P += 1;
            continue;

        case 2: // deallocate
            debug_msg("state.B is currently " + state.B);
            debug_msg("state.E is currently " + state.E);
            state.CP = memory[state.E + 1];
            debug_msg("state.CP set to " + state.CP + " from memory[" + (state.E + 1)+"]");
            if (memory[state.E] < HEAP_SIZE || memory[state.E] > HEAP_SIZE + STACK_SIZE)
                abort("Top of frame " + memory[state.E] + " exceeds bounds in deallocate. Environment is " + state.E + " P = " + state.P);

            state.E = memory[state.E];
            debug_msg("Deallocate: E is reduced to " + state.E);
            state.P += 1;
            continue;

        case 3: // call
            var predicate = predicates[code[state.P+1]];
            if (predicate !== undefined)
            {
                // Set CP to the next instruction so that when the predicate is finished executing we know where to come back to
                state.CP = {code: code,
                            predicate: state.current_predicate,
                            offset: state.P + 3};
                debug_msg("Calling " + atable[ftable[code[state.P+1]][0]] + "/" + ftable[code[state.P+1]][1] + " so setting CP to " + (state.P+3) + ", argument is " + code[state.P+2]);
                state.num_of_args = ftable[code[state.P+1]][1];
                state.B0 = state.B;
                state.current_predicate = predicate;
                code = predicate.clauses[predicate.clause_keys[0]].code;
                state.P = 0;
            }
            else if (foreign_predicates[code[state.P+1]] !== undefined)
            {
                state.num_of_args = ftable[code[state.P+1]][1];
                var fargs = new Array(state.num_of_args);
                for (i = 0; i < state.num_of_args; i++)
                {
                    fargs[i] = deref(register[i]);
                }
                // This is a bit counter-intuitive since it seems like we are never going to get a proceed to use the CP.
                // Remember that any time we might need CP to be saved, it will be. (If there is more than one goal, there will be an environment).
                // If there is only one goal (ie a chain rule) then we will be in exeucte already, not call.
                // This means it is never unsafe to set CP in a call port.
                // Further, rememebr that state.CP is used to create choicepoints (and environments), and since foreign frames may create these, we must set CP to
                // something sensible, even though we never expect to use it to actually continue execution from.
                state.CP = {code: code,
                            predicate: state.current_predicate,
                            offset:state.P + 3};
                debug_msg("Calling (foreign) " + atable[ftable[code[state.P+1]][0]] + "/" + ftable[code[state.P+1]][1] + " and setting CP to " + (state.P + 3));
                result = foreign_predicates[code[state.P+1]].apply(null, fargs);
                state.foreign_retry = false;
                if (result)
                    state.P = state.P + 3;
                else if (!backtrack())
                    return false;
            }
            else
            {
                if (!undefined_predicate(code[state.P+1]))
                    return false;
            }
            continue;

        case 4: // execute
            var predicate = predicates[code[state.P+1]];
            if (predicate !== undefined)
            {
                // No need to save continuation for execute
                state.num_of_args = ftable[code[state.P+1]][1];
                state.B0 = state.B;
                debug_msg("Executing " + atable[ftable[code[state.P+1]][0]] + "/" + ftable[code[state.P+1]][1]);
                state.current_predicate = predicate;
                code = predicate.clauses[predicate.clause_keys[0]].code;
                state.P = 0;
            }
            else if (foreign_predicates[code[state.P+1]] !== undefined)
            {
                state.num_of_args = ftable[code[state.P+1]][1];
                debug_msg("Executing (foreign) " + atable[ftable[code[state.P+1]][0]] + "/" + ftable[code[state.P+1]][1]);
                var fargs = new Array(state.num_of_args);
                for (i = 0; i < state.num_of_args; i++)
                    fargs[i] = deref(register[i]);
                result = foreign_predicates[code[state.P+1]].apply(null, fargs);
                state.foreign_retry = false;
                debug_msg("Foreign result: " + result + " and CP: " + state.CP);
                if (result)
                {
                    state.current_predicate = state.CP.predicate;
                    code = state.CP.code;
                    state.P = state.CP.offset;
                }
                else if (!backtrack())
                    return false;
            }
            else
            {
                if (!undefined_predicate(code[state.P+1]))
                    return false;
            }
            continue;

        case 5: // proceed
            state.P = state.CP.offset;
            state.current_predicate = state.CP.predicate;
            code = state.CP.code;
            continue;

        case 6: // put_variable: Initialize a new variable in Yn, and also put it into Ai
            register_location = state.E + code[state.P+1] + 2;
            debug_msg("Putting new variable into Y" + code[state.P+1] + " at " + register_location);
            memory[register_location] = register_location ^ (TAG_REF << WORD_BITS);
            register[code[state.P+2]] = register_location ^ (TAG_REF << WORD_BITS);
            state.P += 3;
            continue;

        case 7: // put_variable: Put fresh var into registers Ai and Xn
            var freshvar = state.H ^ (TAG_REF << WORD_BITS);
            memory[state.H] = freshvar;
            register[code[state.P+1]] = freshvar;
            register[code[state.P+2]] = freshvar;
            state.H++;
            debug_msg("After put_variable, state.H is now " + state.H);            
            state.P += 3;
            continue;

        case 8: // put_value
            var source;
            if (code[state.P+1] == 0) // Y-register
            {
                register_location = state.E + code[state.P+2] + 2;
                if (memory[register_location] === undefined)
                    abort("Invalid memory access in put_value");
                register[code[state.P+3]] = memory[register_location];
                debug_msg("put_value(Y" + code[state.P+2] + ", A" + code[state.P+3] + "): memory[" + register_location + "] = "  + hex(memory[register_location]));
            }
            else
            {
                debug_msg("put_value: " + hex(register[code[state.P+2]]));
                register[code[state.P+3]] = register[code[state.P+2]];
            }
            state.P += 4;
            continue;

        case 9: // put_unsafe_value
            register_location = state.E + code[state.P+1] + 2;
            // This is the unsafe bit. If the value now in register[code[state.P+2]] is on the stack (that is, it is > E) then we have to push a new variables
            // onto the stack to avoid dangling references to things that are about to be cleaned up
            if (memory[register_location] < state.E)
            {
                debug_msg("Value is safe");
                // No, so we can just behave like put_value
                register[code[state.P+2]] = deref(memory[register_location])
            }
            else
            {
                // Yes, so we need to push a new variable instead
                debug_msg("x0 memory[" + state.E + "] = " + memory[state.E]);
                debug_msg("Value is unsafe. Allocating a new unbound variable for it. It will go into Y" + code[state.P+1] + " @ " + register_location + ". E = " + state.E);
                var v = alloc_var();
                debug_msg("x1 memory[" + state.E + "] = " + memory[state.E]);
                debug_msg("Binding " + hex(v) + " and Y" + code[state.P+1] + " = " + hex(memory[register_location]));
                bind(v, memory[register_location]);
                debug_msg("x2 memory[" + state.E + "] = " + memory[state.E]);
                register[code[state.P+2]] = v;
                debug_msg("x3 memory[" + state.E + "] = " + memory[state.E]);
                debug_msg("X" + code[state.P+2] + " <- " + v);
            }
            state.P += 3;
            continue;

        case 10: // put_constant C into Ai            
            register[code[state.P+2]] = code[state.P+1] ^ (TAG_ATM << WORD_BITS);
            state.P += 3;
            continue;

        case 11: // put_nil into Ai
            register[code[state.P+1]] = NIL;
            state.P += 2;
            continue;

        case 12: // put_structure
            register[code[state.P+2]] = alloc_structure(code[state.P+1] ^ (TAG_ATM << WORD_BITS));
            state.mode = WRITE;
            state.P += 3;
            continue;

        case 13: // put_list
            register[code[state.P+1]] = alloc_list();
            state.mode = WRITE;
            state.P += 2;
            continue;

        case 14: // put_integer I into Ai
            register[code[state.P+2]] = (code[state.P+1] & ((1 << WORD_BITS)-1)) ^ (TAG_INT << WORD_BITS);
            state.P += 3;
            continue;           

        case 15: // get_variable
            if (code[state.P+1] == 0) // Y-register
            {
                register_location = state.E + code[state.P+2] + 2;
                debug_msg("Y" + code[state.P+2] + " <- " + hex(register[code[state.P+3]]));
                memory[register_location] = register[code[state.P+3]];
            }
            else
            {
                debug_msg("X" + code[state.P+2] + " <- " + hex(register[code[state.P+3]]));
                register[code[state.P+2]] = register[code[state.P+3]];
            }
            state.P+= 4;
            continue;
            
        case 16: // get_value
            var source;
            var target = register[code[state.P+3]];
            gc_check(target);
            if (code[state.P+1] == 0) // Y-register
            {
                register_location = state.E + code[state.P+2] + 2;
                source = memory[register_location];
            }
            else
            {
                source = register[code[state.P+2]];
            }
            state.P += 4;
            debug_msg("get_value: Unifying " + hex(source) + " and " + hex(target));
            if (!unify(source, target))
                if (!backtrack())
                    return false;
            continue;

        case 17: // get_constant C from Ai            
            // First, get what is in Ai into sym
            var sym = deref(register[code[state.P+2]]);
            // Then get arg. This is an atom index, not a <CON, i> cell. It needs to be made into the latter!
            var arg = code[state.P+1] ^ (TAG_ATM << WORD_BITS);
            state.P += 3;
            if (TAG(sym) == TAG_REF)
            {
                // If Ai is variable, then we need to bind. This is when foo(bar) is called like foo(X).
                bind(sym, arg);
            }
            else if (sym != arg)
            {
                debug_msg("Could not get constant: " + hex(sym) + " from " + hex(arg));
                if (!backtrack())
                    return false;
            }
            continue;

        case 18: // get_nil
            var sym = deref(register[code[state.P+1]]);
            state.P += 1;
            if (TAG(sym) == TAG_REF)
                bind(sym, NIL);
            else if (sym != NIL)
                if (!backtrack())
                    return false;
            continue;
            

        case 19: // get_structure
            var ftor = code[state.P+1] ^ (TAG_ATM << WORD_BITS);
            var addr = deref(register[code[state.P+2]]);
            state.P += 3;
            if (TAG(addr) == TAG_REF)
            {
                debug_msg("Arg passed is unbound. Proceeding in WRITE mode");
                state.mode = WRITE;
                a = alloc_structure(ftor);
                bind(memory[addr], a);
            }
            else if (TAG(addr) == TAG_STR && memory[VAL(addr)] == ftor)
            {
                debug_msg("Arg passed is bound to the right functor. Proceeding in READ mode from " + (VAL(addr)+1));
                state.mode = READ;
                state.S = VAL(addr)+1;
            }                        
            else
            {
                if (!backtrack())
                    return false;
            }
            continue;

        case 20: // get_list from Ai
            var addr = deref(register[code[state.P+1]]);
            state.P += 2;
            if (TAG(addr) == TAG_REF)
            {
                // predicate called with var and we are expecting a list
                var l = state.H ^ (TAG_LST << WORD_BITS);
                bind(memory[addr], l);
                debug_msg("Bound memory[" + addr + "] ( " + memory[addr] + ") to <LST," + state.H + ">");
                state.mode = WRITE;
            }
            else if (TAG(addr) == TAG_LST)
            {   
                debug_msg("get_list will proceed in read mode from " + VAL(addr));
                state.S = VAL(addr);
                state.mode = READ;                
            }
            else
                if (!backtrack())
                    return false;
            continue;

        case 21: // get_integer I from Ai            
            // First, get what is in Ai into sym
            var sym = deref(register[code[state.P+2]]);
            // Then get arg. This is the actual integer, not a <INT, i> cell. It needs to be made into the latter!
            var arg = (code[state.P+1] & ((1 << WORD_BITS)-1)) ^ (TAG_INT << WORD_BITS);
            state.P += 3;
            if (TAG(sym) == TAG_REF)
            {
                // If Ai is variable, then we need to bind. This is when foo(7) is called like foo(X).
                bind(sym, arg);
            }
            else if (sym != arg)
            {
                debug_msg("Could not get constant: " + hex(sym) + " from " + hex(arg));
                if (!backtrack())
                    return false;
            }
            continue;

        case 22: // unify_void
            if (state.mode == READ)
                state.S += code[state.P+1];
            else
                for (i = 0; i < code[state.P+1]; i++)
                    alloc_var();
            state.P += 2;
            continue;

        case 23: //unify_variable
            var source;
            if (state.mode == READ) // If reading, consume the next symbol
            {                
                source = memory[state.S++]; 
                debug_msg("Unifying existing variable: " + hex(source) + " at " + (state.S-1));
                debug_msg(term_to_string(source));
            }
            else
            {
                source = alloc_var(); // If writing, create a new var
                debug_msg("Allocated new variable: " + source);
            }
            if (code[state.P+1] == 0) // Y-register
            {
                debug_msg("... for register Y" + code[state.P+2]);
                register_location = state.E + code[state.P+2] + 2;
                // GC: This needs to be trailed if state.B is not 0, apparently
                bind(memory[register_location], source);
            }
            else
            {
                register[code[state.P+2]] = source;
            }
            state.P += 3;
            continue;

        case 24: // unify_value
            var did_fail = false;
            if (state.mode == READ)
            {
                source = memory[state.S++];
                if (code[state.P+1] == 0) // Y-register
                {
                    register_location = state.E + code[state.P+2] + 2;
                    did_fail = !unify(memory[register_location], source);
                }
                else
                {
                    did_fail = !unify(register[code[state.P+2]], source);
                }
            }
            else
            {
                if (code[state.P+1] == 0) // Y-register
                {
                    register_location = state.E + code[state.P+2] + 2;
                    memory[state.H++] = memory[register_location];
                }
                else
                {
                    memory[state.H++] = register[code[state.P+2]];
                }
            }
            state.P += 3;
            if (did_fail)
                if (!backtrack())
                    return false;
            continue;
        case 25: // unify_local_value
            var did_fail = false;
            if (state.mode == READ)
            {
                source = memory[state.S++];
                if (code[state.P+1] == 0) // Y-register
                {
                    register_location = state.E + code[state.P+2] + 2;
                    did_fail = !unify(memory[register_location], source);
                }
                else
                {
                    did_fail = !unify(register[code[state.P+2]], source);
                }
           }
            else
            {
                var addr;
                if (code[state.P+1] == 0) // Y-register;
                {
                    register_location = state.E + code[state.P+2] + 2;
                    addr = memory[register_location];
                }
                else
                {
                    addr = register[code[state.P+2]];                    
                }
                addr = deref(addr);
                if (VAL(addr) < state.H)
                {
                    debug_msg("Unify local: already safe at " +  hex(addr));
                    // Address is on the heap. Just push the value onto the top of the heap
                    debug_msg(term_to_string(addr));
                    memory[state.H++] = addr;
                }
                else
                {
                    debug_msg("Unify local: unsafe. Globalizing");
                    // Address is on the stack. Push a new variable onto the heap and bind to the value
                    fresh = state.H ^ (TAG_REF << WORD_BITS);
                    memory[state.H++] = fresh;
                    debug_msg("Binding fresh variable " + fresh + " to " + addr);
                    bind(fresh, addr);
                    if (code[state.P+1] == 1)
                        register[code[state.P+2]] = fresh; // also set X(i) if X-register
                }
            }
            state.P += 3;
            if (did_fail)
                if (!backtrack())
                    return false;
            continue;
        case 26: // unify_constant
            if (state.mode == READ)
            {
                var sym = deref(memory[state.S++]);
                var arg = code[state.P+1] ^ (TAG_ATM << WORD_BITS);
                state.P += 2;
                debug_msg("sym: " + hex(sym) + ", arg: " + hex(arg));
                if (TAG(sym) == TAG_REF)
                {
                    debug_msg("Binding " + sym + " and " + arg);
                    bind(sym, arg);
                }
                else if (sym != arg)
                    if (!backtrack())
                        return false;
            }
            else
            {
                memory[state.H++] = code[state.P+1] ^ (TAG_ATM << WORD_BITS);
                state.P += 2;
            }
            continue;
        case 27: // unify_integer
            if (state.mode == READ)
            {
                var sym = deref(memory[state.S++]);
                var arg = (code[state.P+1] & ((1 << WORD_BITS)-1)) ^ (TAG_INT << WORD_BITS)
                state.P += 2;
                if (TAG(sym) == TAG_REF)
                {
                    debug_msg("Binding " + sym + " and " + arg);
                    bind(sym, arg);
                }
                else if (sym != arg)
                    if (!backtrack())
                        return false;
            }
            else
            {
                memory[state.H++] = (code[state.P+1] & ((1 << WORD_BITS)-1)) ^ (TAG_INT << WORD_BITS);
                state.P += 2;
            }
            continue;

        case 28: // try_me_else
            debug_msg("try_me_else at P=" + state.P + " which has branch=" + code[state.P+1]);
            // We need to allocate a new choicepoint, but first we need to determine /where/ to put it, since we do not keep a reference to the top of the stack.
            // The last item on the stack is either an environment, or a choicepoint.
            var newB;
            if (state.E > state.B)
            {
                // In this case, it is an environment. In the real WAM, which does stack trimming (see Ait-Kaci chapter 5.7), we only have CE, CP and then N saved Y-registers. 
                // Therefore, we need to write the new choicepoint at 2 + N. What is N, though? Well, it turns out N gets gradually smaller as time goes on, which
                // is why it is not stored in the frame itself. If call(f) is outfitted with a second argument to become call(f, n) then we can decode this in try_me_else
                // (and ignore it if we did not want to create a new environment) by looking at CP, which points to the instruction after the call() opcode. Therefore,
                // code[CP-1] ought to be N.

                // -----------
                // |0  | CE  |
                // |1  | CP  |
                // |3  | Y0  |
                //  ...
                // |n+2| Yn  |
                // -----------
                debug_msg("P=" + state.P + " Top frame is an environment. Starts at " + state.E + " and has length = " + state.CP.code[state.CP.offset-1] + " + 2. Previous is " + memory[state.E]);
                debug_msg("Top choicepoint is " + state.B);
                newB = state.E + state.CP.code[state.CP.offset - 1] + 2;
            }
            else
            {   
                // In this case, the top frame is a choicepoint. This is a bit easier: A choicepoint contains 7 saved special-purpose registers, the N root arguments
                // for the goal, and, happily, the value of N as the very first argument. Therefore, we can read the 0th entry of the current frae (at state.B)
                // and add 9 to it to get the top of the stack.
                debug_msg("Top frame is a choicepoint: " + state.B);
                debug_msg("Top environment is " + state.E);
                newB = state.B + memory[state.B] + 8;                
            }
            debug_msg("Creating new choicepoint on the stack at " + newB);
            memory[newB] = state.num_of_args;
            var n = memory[newB];
            for (i = 0; i < n; i++)
            {
                //debug_msg("Saving register " + i + "(" + hex(register[i]) + ") to " + (newB + i + 1));
                memory[newB + i + 1] = register[i];
            }
            // Save the current context
            memory[newB+n+1] = state.E;
            memory[newB+n+2] = state.CP;
            memory[newB+n+3] = state.B;
            var next = code[state.P+1];
            if ((next & 0x80000000) == 0)
            {
                // next is a clause index in the current predicate
                memory[newB+n+4] = {code: state.current_predicate.clauses[next].code, 
                                    predicate:state.current_predicate, 
                                    offset:0};
            }
            else
            {
                
                // next is an absolute address in the current clause: Used for auxiliary clauses only
                memory[newB+n+4] = {code: code, 
                                    predicate: state.current_predicate,
                                    offset:next ^ 0x80000000};
            }
            //memory[newB+n+4] = {code: code, offset:code[state.P+1]};
            memory[newB+n+5] = state.TR;
            memory[newB+n+6] = state.H;
            memory[newB+n+7] = state.B0;
            state.B = newB;
            debug_msg("case 28: Before we created the choicepoint, HB was " + state.HB);
            state.HB = state.H;
            state.P += 2;
            debug_msg("try_me_else: state.B is now at " + state.B + " and state.HB is now " + state.HB);
            continue;

        case 29: // retry_me_else
            // Unwind the last goal. The arity if the first thing on the stack, then the saved values for A1...An
            var arity = memory[state.B];
            debug_msg("retry_me_else: " + state.B + " with arity " + memory[state.B] + " and retry point " +  code[state.P+1]);
            for (var i = 0; i < arity; i++)
                register[i] = memory[state.B + i + 1];
            // Now restore all the special-purpose registers
            if (memory[state.B + arity + 1] < HEAP_SIZE)
                abort("Top of frame contains E which is in the heap");
            if (memory[state.B + arity + 1] > HEAP_SIZE + STACK_SIZE)
                abort("Top of frame contains E which exceeds the stack");
            debug_msg("top of frame at " + state.B + " is OK");
            state.E = memory[state.B + arity + 1];       
            state.CP = memory[state.B + arity + 2];      
            var next = code[state.P+1];
            debug_msg("Retry me else: Set CP to " + state.CP);
            // set up the 'else' part of retry_me_else by adjusting the saved value of B            
//            memory[state.B + arity + 4] = {code: state.current_predicate.clauses[state.current_predicate.clause_keys[code[state.P+1]]].code, predicate:state.current_predicate, offset:0};
            if ((next & 0x80000000) == 0)                
            {
                // next is a clause index in the current predicate
                memory[state.B+arity+4] = {code: state.current_predicate.clauses[next].code, 
                                           predicate:state.current_predicate, 
                                           offset:0};
            }
            else
            {
                // next is an absolute address in the current clause: Used for auxiliary clauses only
                memory[state.B+arity+4] = {code: code, 
                                           predicate: state.current_predicate,
                                           offset:next ^ 0x80000000};
            }
            unwind_trail(memory[state.B + arity + 5], state.TR);

            state.TR = memory[state.B + arity + 5];
            state.H = memory[state.B + arity + 6];
            debug_msg("case 29: state.HB <- " + state.HB);
            state.HB = state.H
            state.P += 2;
            continue;
            
        case 30: // trust_me
            // Unwind the last goal. The arity if the first thing on the stack, then the saved values for A1...An
            var n = memory[state.B];
            debug_msg("trusting last clause: " + state.B + " with arity " + memory[state.B] + " and HB was " + state.HB + ". Choicepoint has " + n + " args");
            for (var i = 0; i < n; i++)
            {
                debug_msg("Restoring register " + i + " to " + hex(memory[state.B + i + 1]));
                register[i] = memory[state.B + i + 1];
            }
            // Now restore all the special-purpose registers
            if (memory[state.B + n + 1] < HEAP_SIZE || memory[state.B + n + 1] > HEAP_SIZE + STACK_SIZE)
                abort("Top of frame exceeds bounds in trust. Read from memory[" + (state.B+n+1) + "]. State.B is " + state.B);
            state.E = memory[state.B + n + 1];            
            state.CP = memory[state.B + n + 2];            
            debug_msg("trust_me: Set CP to " + state.CP);
            unwind_trail(memory[state.B + n + 5], state.TR);
            state.TR = memory[state.B + n + 5];
            state.H = memory[state.B + n + 6];
            state.B = memory[state.B + n + 3];
            state.HB = memory[state.B+ memory[state.B] + 6];
            debug_msg("state.B is now set back to " + state.B + " and state.HB is set back to " + state.HB);
            debug_msg("state.E is now set back to " + state.E);
            //state.HB = memory[state.B + n + 6];
            debug_msg("case 30: state.HB reset to " + state.HB);
            state.P += 2;
            continue;

        case 31: // neck_cut
            // Move B back to B0 and tidy the trail. If B == B0 then do nothing (ie if there is a useless cut in the only clause of a predicate)
            var result = true;
            if (state.B > state.B0)
            {
                while (cleanups[0] !== undefined && cleanups[0].B > state.B0 && cleanups[0].B < state.B)
                {
                    result = run_cleanup(cleanups[0]) && result;
                    cleanups.shift();
                }
                state.B = state.B0;
                if (state.B > 0)
                    tidy_trail();                
            }
            if (result)
                state.P += 1;
            else if (!backtrack())
                return false;
            continue;

        case 32: // cut(I)
            y = VAL(memory[state.E + 2 + code[state.P+1]]);
            debug_msg("cut(Y" + code[state.P+1] + "). B = " + state.B + " B0 = " + state.B0);
            debug_msg("Cutting to memory[" + (state.E + 2 + code[state.P+1]) + "] = " + y);
            var result = true;
            if (state.B > y)
            {
                while (cleanups[0] !== undefined && cleanups[0].B > y && cleanups[0].B < state.B0)
                {
                    debug_msg("Cutting to " + y + ", and top cleanup is protecting " + cleanups[0].B + " so executing " + cleanups[0].P);
                    debug_msg("State is currently " + JSON.stringify(state));
                    result = run_cleanup(cleanups[0]) && result;
                    cleanups.shift();
                }    
                state.B = y;
                if (state.B > 0)
                    tidy_trail();
            }
            else
            {
                debug_msg("... has no effect");
            }
            debug_msg("Cut complete. State is " + JSON.stringify(state));
            if (result)
                state.P += 2;
            else if (!backtrack())
                return false;
            continue;

        case 33: // get_level(I)
            debug_msg("Setting memory[" + (state.E + 2 + code[state.P+1]) + "] to B0: " + state.B0 + " (state.B = " + state.B + ")");
            memory[state.E + 2 + code[state.P+1]] = state.B0 ^ (TAG_INT << WORD_BITS);
            state.P += 2;
            continue;

        case 40: // call_aux
            var offset = code[state.P+1];
            state.CP = {code:code,
                        predicate: state.current_predicate,
                        offset:state.P + 4};
            debug_msg("Call_aux: Set CP to " + state.CP);
            debug_msg("Aux offset is " + offset);
            debug_msg("env space still required: " + code[state.P+3])
            state.num_of_args = code[state.P+2];
            state.P = offset;
            state.B0 = state.B;
            continue;

        case 41: // execute_aux
            var offset = code[state.P+1];
            state.num_of_args = code[state.P+2];
            state.P = offset;
            state.B0 = state.B;            
            continue;

        case 42: // retry_foreign
            debug_msg("retry_foreign from " + state.B);
            state.foreign_value = memory[state.B+1];
            state.P = memory[state.B+2].offset;
            code = memory[state.B+2].code;
            state.current_predicate = memory[state.B+2].current_predicate;
            var n = memory[state.B];
            debug_msg("State has " + n + " saved args including the two special");
            state.foreign_retry = true;
            for ( i = 0; i < n-2; i++)
            {
                debug_msg("Restoring register " + i + " from memory[" + (state.B+3+i) + "] = " + hex(memory[state.B+3+i]) + " which is " +term_to_string(memory[state.B+3+i]));
                register[i] = memory[state.B+3+i];
            }
            state.E = memory[state.B + n + 1];
            state.CP = memory[state.B + n + 2];      
            unwind_trail(memory[state.B + n + 5], state.TR);
            state.TR = memory[state.B + n + 5];
            state.H = memory[state.B + n + 6];
            state.HB = state.H
            continue;
        case 43: // get_choicepoint
            var i = code[state.P+1];
            var choice = state.B;
            while (i != 0)
            {
                choice = memory[choice + memory[choice] + 3];
                i--;
            }
            
            debug_msg("Setting " + (state.E + 2 + code[state.P+2]) + " to " + code[state.P+1] + "-to-top choicepoint " + choice);
            memory[state.E + 2 + code[state.P+2]] = (choice ^ TAG_INT << WORD_BITS);
            state.P += 3;
            continue;            
            
         // All the floating point operations are here because I added them as an afterthought!
        case 50: // get_float I from Ai            
            var sym = deref(register[code[state.P+2]]);
            var arg = code[state.P+1] ^ (TAG_FLT << WORD_BITS);
            state.P += 3;
            if (TAG(sym) == TAG_REF)
            {
                // If Ai is variable, then we need to bind. This is when foo(7) is called like foo(X).
                bind(sym, arg);
            }
            else if (sym != arg)
            {
                debug_msg("Could not get constant: " + hex(sym) + " from " + hex(arg));
                if (!backtrack())
                    return false;
            }
            continue;
        case 51: // put_float I into Ai
            register[code[state.P+2]] = code[state.P+1] ^ (TAG_FLT << WORD_BITS);
            state.P += 3;
            continue;           
        case 52: // unify_float
            if (state.mode == READ)
            {
                var sym = deref(memory[state.S++]);
                var arg = code[state.P+1] ^ (TAG_FLT << WORD_BITS);
                state.P += 2;
                if (TAG(sym) == TAG_REF)
                {
                    bind(sym, arg);
                }
                else if (sym != arg)
                    if (!backtrack())
                        return false;
            }
            else
            {
                memory[state.H++] = code[state.P+1] ^ (TAG_FLT << WORD_BITS);
                state.P += 2;
            }
            continue;

        case 60: // put_variable Yn
            // Note that this is different from put_variable(Yn, Ai) in that it ONLY puts a fresh variable into Yn
            // This is needed to make garbage collection safe
            register_location = state.E + code[state.P+1] + 2;
            debug_msg("Putting new variable into Y" + code[state.P+1] + " at " + register_location);
            memory[register_location] = register_location ^ (TAG_REF << WORD_BITS);
            state.P += 2;
            continue;

            

        case 254: // Only clause: NOP
            state.P += 2;
            continue;
        case 255: // halt
            state.running = false;
            continue;
        default:
            abort("unexpected opcode at P=" + (((state.current_predicate == null)?("no predicate"):(atable[ftable[state.current_predicate.key][0]] + "/" + ftable[state.current_predicate.key][1])) + "@" + state.P + ": " + code[state.P]));
        }        
    }
    return true;
}


/* Testing */

function hex(number)
{
    if (number == undefined)
        return "undefined";
    if (number < 0)
    {
    	number = 0xFFFFFFFF + number + 1;
    }
    return "0x" + number.toString(16).toUpperCase();
}

function allocate_first_frame()
{
    // Allocate an environment for the toplevel?
    state.E = HEAP_SIZE; 
    memory[state.E] = 0;     // previous environment = NULL
    memory[state.E + 1] = state.CP;
}

function term_to_string(t)
{
    return format_term(t, {ignore_ops:false, quoted: true, numbervars: false});
}

function copy_state(s)
{
    return {H: s.H,
            HB: s.HB,
            S: s.S,
            P: s.P,
            CP: s.CP, 
            B0: s.B0,
            B: s.B,
            E: s.E,
            TR: s.TR,
            mode: s.mode,
            running: s.running,
            num_of_args: s.num_of_args,
            foreign_retry: s.foreign_retry,
            current_predicate: s.current_predicate};
}

function copy_registers(r)
{
    return r.slice(0);
}


function run_cleanup(c)
{
    debug_msg("Running cleanup...: " + JSON.stringify(c));
    var saved_state = copy_state(state);
    var saved_registers = copy_registers(register);
    var saved_code = code;
    state.P = c.P;
    register = c.V.slice(0);
    code = c.code;
    debugging = true;
    var result = true;

    if (!wam())
    {
        // Failure is ignored, but exceptions are raised
        if (exception != null)
            result = false;
    }
    debug_msg("Finished. Restoring state. Heap is up to " + state.H);
    register = copy_registers(saved_registers);
    var saved_heap = state.H;
    state = copy_state(saved_state);
    state.H = saved_heap;
    code = saved_code;
    return result;
}

// Exceptions are implement as per Bart Demoen's 1989 paper
// http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.57.4354&rep=rep1&type=pdf
function predicate_throw(t)
{
    debug_msg("Setting exception " + hex(t) + "=> "+ term_to_string(t));
    exception = record_term(t);
    return unwind_stack();
}

function unwind_stack()
{
    if (state.block === undefined)
    {
        abort("Uncaught exception: " + term_to_string(recall_term(exception, {})));
    }
    state.B = state.block;
    return false;
}

function get_current_block(b)
{
    return unify(b, state.block ^ (TAG_INT << WORD_BITS));
}

function install_new_block(nb)
{
    state.block = state.B;
    return unify(nb, state.B ^ (TAG_INT << WORD_BITS));
}

function reset_block(x)
{
    state.block = VAL(x);
    return true;
}

function clean_up_block(nb)
{
    // If alternative to B is nb, then select it now
    if (memory[state.B+memory[state.B]+4] == VAL(nb))
        state.B = VAL(memory[VAL(nb)+memory[VAL(nb)]+4]);
    return true;

}
function get_exception(e)
{
    if (exception !== null)
    {
        return unify(e, recall_term(exception, {}));
    }
    else
    {
        return false;
    }
}

function clear_exception()
{
    exception = null;
    return true;
}

function undefined_predicate(ftor)
{
    if (prolog_flag_values.unknown == "error")
    {
        var indicator = state.H ^ (TAG_STR << WORD_BITS);
        memory[state.H++] = lookup_functor("/", 2);
        memory[state.H++] = ftable[ftor][0] ^ (TAG_ATM << WORD_BITS);
        memory[state.H++] = ftable[ftor][1] ^ (TAG_INT << WORD_BITS);
        existence_error("procedure", indicator);
    }
    else if (prolog_flag_values.unknown == "warning")
    {
        stdout("Undefined predicate " + atable[ftable[ftor][0]] + "/" + ftable[ftor][1] + "\n");
    }
    if (!backtrack())
    {
        debug("Could not backtrack");
        return false;
    }
    return true;
}

// End exceptions code

// /System/Library/Frameworks/JavaScriptCore.framework/Versions/A/Resources/jsc foreign.js wam.js bootstrap.js -e "demo()"
function demo(d)
{
    debugging = d;
    load_state();
    stdout("Loaded " + Object.keys(predicates).length + " predicates\n");
    stdout("Loaded " + atable.length + " atoms\n");
    stdout("Loaded " + ftable.length + " functors\n");
    initialize();
    allocate_first_frame();

    var ftor = VAL(lookup_functor("toplevel", 0));
    state.P = 0;
    var pred = predicates[ftor];
    var pi = predicates[ftor].clause_keys[0];
    state.current_predicate = pred;
    code = pred.clauses[pi].code;
    if (wam())
        stdout("Succeeded\n");
    else if (exception == null)
        stdout("Failed\n");
    else
        stdout("Uncaught exception: " + term_to_string(recall_term(exception, {})) +"\n");
}


function unit_tests(d)
{
    debugging = d;
    load_state();
    stdout("Loaded " + Object.keys(predicates).length + " predicates\n");
    stdout("Loaded " + atable.length + " atoms\n");
    stdout("Loaded " + ftable.length + " functors\n");
    initialize();
    allocate_first_frame();

    var ftor = VAL(lookup_functor("toplevel", 0));
    state.P = 0;
    var pred = predicates[ftor];
    var pi = predicates[ftor].clause_keys[0];
    state.current_predicate = pred;
    code = pred.clauses[pi].code;
    if (wam())
        stdout("Succeeded\n");
    else if (exception == null)
        stdout("Failed\n");
    else
        stdout("Uncaught exception: " + term_to_string(recall_term(exception, {})) +"\n");
}


function reset_compile_buffer()
{
    compile_buffer = [];
    return true;
}
