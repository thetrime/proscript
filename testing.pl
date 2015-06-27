% Debugging
:-op(920, fy, ?).
:-op(920, fy, ??).

??(Goal):-
        setup_call_catcher_cleanup(format(user_error, 'CALL ~q~n', [Goal]),
                                   Goal,
                                   Catcher,
                                   ( Catcher == fail ->
                                       format(user_error, 'FAIL ~q~n', [Goal])
                                   ; Catcher == exit ->
                                       format(user_error, 'EXIT ~q~n', [Goal])
                                   ; Catcher == ! ->
                                       format(user_error, 'CUT  ~q~n', [Goal])
                                   ; Catcher = error(Error)->
                                       format(user_error, 'ERROR ~q ~p~n', [Goal, Error])
                                   )),
        ( var(Catcher)->
            format(user_error, 'PEND ~q~n', [Goal])
        ; otherwise->
            true
        ).

?(Goal):-
        functor(Goal, Functor, Arity),
        setup_call_catcher_cleanup(format(user_error, 'CALL ~q~n', [Functor/Arity]),
                                   Goal,
                                   Catcher,
                                   ( Catcher == fail ->
                                       format(user_error, 'FAIL ~q~n', [Goal])
                                   ; Catcher == exit ->
                                       format(user_error, 'EXIT ~q~n', [Functor/Arity])
                                   ; Catcher == ! ->
                                       format(user_error, 'CUT  ~q~n', [Functor/Arity])
                                   ; Catcher = error(Error)->
                                       format(user_error, 'ERROR ~q ~p~n', [Functor/Arity, Error])
                                   )),
        ( var(Catcher)->
            format(user_error, 'PEND ~q~n', [Functor/Arity])
        ; otherwise->
            true
        ).
