var history = [];
var h_ptr = -1;

var query = "";
debugging = false;
var output_console = null;
load_state();
initialize();
var can_backtrack = false;

function preventBackspace(e)
{
    if (e.keyCode == 8 && e.target == output_console)
    {
        e.preventDefault();
        e.stopPropagation();
        backspace();
        return false;
    }
    return true;
}

var stdout_buffer;

function predicate_flush_stdout()
{
    if (stdout_buffer.innerHTML != "")
        stdout("\n");
    return true;
}

function stdout(msg)
{
    output_console.removeChild(stdout_buffer);
    var lines = (stdout_buffer.innerHTML + msg).split('\n');
    for (var i = 0; i < lines.length-1; i++)
    {
        debug(lines[i]);
    }
    stdout_buffer.innerHTML = lines[lines.length-1];
    output_console.appendChild(stdout_buffer);     

}

function onload()
{
    output_console = document.getElementById('stdout');    
    stdout_buffer = document.createElement('div');
    stdout_buffer.innerHTML = "";
    output_console.appendChild(stdout_buffer);     
    consult();

    query_node = document.createElement('div');
    query_node.className = "query";
    query_node.innerHTML = "?-";
    output_console.appendChild(query_node);     
    scroll_to_bottom();
}

function debug(e) 
{
    var newElement = document.createElement('div');
    newElement.innerHTML = '<div>' + e + '</div>';
    output_console.appendChild(newElement); 
    scroll_to_bottom();
}

function consult()
{
    code_atom = document.getElementById('code').value;
    /* Reset the entire WAM */
    load_state();
    initialize();
    atom = lookup_atom(code_atom);
    ftor = VAL(lookup_functor("consult_atom", 1));
    allocate_first_frame();
    var pred = predicates[ftor];
    var pi = predicates[ftor].clause_keys[0];
    state.current_predicate = pred;
    code = pred.clauses[pi].code;
    state.P = 0;
    register[0] = atom;
    if (wam())
        debug("Buffer consulted");
    else
        debug("Failed to load buffer");
    // FIXME: This is not very good. At the very least setting state.B to 0 should reset state.H to 0 as well?
    state.B = 0;
    can_backtrack = false;
}

function backspace()
{
    if (query.length > 0)
    {
        query = query.substring(0, query.length - 1);
        query_node.innerHTML = "?-" + query;
        output_console.removeChild(query_node);
        output_console.appendChild(query_node);
        scroll_to_bottom();
    }
}

function keydown(e)
{
    if (e.keyCode == 38 && !can_backtrack)
    {
        e.preventDefault();
        e.stopPropagation();
        h_ptr++;
        if (h_ptr >= history.length)
        {
            h_ptr = history.length-1;
        }
        query = history[h_ptr];
        query_node.innerHTML = "?-" + query;
        output_console.removeChild(query_node);
        output_console.appendChild(query_node);
        scroll_to_bottom();
    }
    else if (e.keyCode == 40 && !can_backtrack)
    {
        e.preventDefault();
        e.stopPropagation();
        h_ptr--;
        if (h_ptr < 0)
        {
            h_ptr = -1;
            query = "";
        }
        else
            query = history[h_ptr];
        query_node.innerHTML = "?-" + query;
        output_console.removeChild(query_node);
        output_console.appendChild(query_node);
        scroll_to_bottom();        
    }
}

function keypress(e)
{
    if (e.altKey || e.ctrlKey || e.metaKey)
        return;
    e.preventDefault();
    e.stopPropagation();
    if (e.keyCode == 8)
    {
        backspace();
    }
    else if (e.keyCode == 59 && can_backtrack)
    {
        var old_query = document.createElement('div');
        old_query.innerHTML = ";";
        old_query.className = "old_query";
        output_console.appendChild(old_query);
        scroll_to_bottom();
        if (backtrack())
        {
            try_running();
        }
        else
        {
            stdout("false.\n");
            can_backtrack = false;
            query = "";
            query_node = document.createElement('div');
            query_node.className = "query";
            query_node.innerHTML = "?-";
            output_console.appendChild(query_node);  
            scroll_to_bottom();
        }
    }
    else if (e.keyCode == 13 && can_backtrack)
    {
        // Cut choicepoints (?)
        state.B = 0;
        can_backtrack = false;
        query = "";
        query_node = document.createElement('div');
        query_node.className = "query";
        query_node.innerHTML = "?-";
        output_console.appendChild(query_node);  
        scroll_to_bottom();
    }
    else if (e.keyCode == 13)
    {
        // call the toplevel handler
        // ARGH. MUST reset registers for new query, especially after failure!
        initialize();
        allocate_first_frame();        

        var ftor = VAL(lookup_functor("repl", 1));
        var pred = predicates[ftor];
        var pi = predicates[ftor].clause_keys[0];
        state.current_predicate = pred;
        code = pred.clauses[pi].code;
        register[0] = lookup_atom(query);
        // Make the query a permanent part of the output        
        output_console.removeChild(query_node);
        var old_query = document.createElement('div');
        old_query.innerHTML = "?-" + query;
        old_query.className = "old_query";
        output_console.appendChild(old_query);
        history.unshift(query);
        h_ptr = -1;
        try_running();
    }
    else
    {
        query += String.fromCharCode(e.keyCode);
        query_node.innerHTML = "?-" + query;
        output_console.removeChild(query_node);
        output_console.appendChild(query_node);
        scroll_to_bottom();
    }
}

function try_running()
{
    try
    {
        if (!wam())
        {
            stdout("false.\n");
        }
    }
    catch (anything)
    {
        console.log(anything);
        debug("Error. See javascript console");
    }
    if (state.B != 0)
    {
        debug_msg("Can backtrack");
        can_backtrack = true;
    }
    else
    {
        debug_msg("No more solutions after this");
        can_backtrack = false;
        query = "";
        query_node = document.createElement('div');
        query_node.className = "query";
        query_node.innerHTML = "?-";
        output_console.appendChild(query_node);  
        scroll_to_bottom();
    }
}

function scroll_to_bottom()
{
    output_console.scrollTop = output_console.scrollHeight;    
}
