preprocess(Files, Outfile, Defines):-
        setup_call_cleanup(open(Outfile, write, OutStream),
                           preprocess_1(Files, OutStream, Defines),
                           close(OutStream)).

preprocess_1([], _OutStream, _Defines):- !.
preprocess_1([File|Files], OutStream, Defines):-
        setup_call_cleanup(open(File, read, InStream),
                           ( format(OutStream, '// File ~w~n', [File]),
                             preprocess_2(InStream, OutStream, Defines)
                           ),
                           close(InStream)),
        preprocess_1(Files, OutStream, Defines).


preprocess_2(InStream, _OutStream, _Defines):-
        at_end_of_stream(InStream), !.

preprocess_2(InStream, OutStream, Defines):-
        read_line_to_codes(InStream, Codes),
        ( Codes = [35, 105, 102|If]->
            process_directive(InStream, If, Defines)
        ; Codes == [35, 101, 110, 100, 105, 102] -> % endif            
            true
        ; codes_contain_debug_statement(Codes, [])->
            ( memberchk(debug=true, Defines)->
                format(OutStream, '~s~n', [Codes])
            ; otherwise->
                true
            )
        ; otherwise->
            format(OutStream, '~s~n', [Codes])
        ),
        preprocess_2(InStream, OutStream, Defines).

process_directive(InStream, IfCodes, Defines):-
        atom_codes(IfCodes, IfAtom),
        ( memberchk(IfAtom=true, Defines)->
            % Accept directive
            true
        ; otherwise->
            consume_file(InStream, 1)
        ).

consume_file(_InStream, 0):- !.

consume_file(InStream, N):-
        ( at_end_of_stream(InStream)->
            throw(eof_in_macro)
        ; otherwise->
            true
        ),
        read_line_to_codes(InStream, Codes),
        ( Codes == [35, 101, 110, 100, 105, 102]-> % endif
            NN is N-1
        ; Codes = [35, 105, 102|_]-> % Another if
            NN is N+1
        ; otherwise->
            NN = N
        ),
        consume_file(InStream, NN).


... --> []|[_],... .
codes_contain_debug_statement-->
        "function debug_msg(msg)", !, {fail}.
codes_contain_debug_statement-->
        ..., "debug_msg(", ... .
