var stdout_buffer = "";

function stdout(msg)
{
    var lines = (stdout_buffer + msg).split('\n');
    for (var i = 0; i < lines.length-1; i++)
    {
        debug(lines[i]);
    }
    stdout_buffer = lines[lines.length-1];
}

function predicate_flush_stdout()
{
    if (stdout_buffer != "")
        stdout("\n");
    return true;
}
