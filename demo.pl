foo:-
        setup_call_catcher_cleanup(true,
                                   subsumes_term(X, f(X)),
                                   _,
                                   true).

/*
foo:-
        setup_call_catcher_cleanup(true,
                                   ( setup_call_catcher_cleanup(true,
                                                                repeat,
                                                                Catcher,
                                                                writeln(inner_cleanup(Catcher))),
                                     true, !),
                                   Port,
                                   writeln(outer_cleanup(Port))),
        writeln(Port).
*/

/*
deterministic_goal.
nondeterministic_goal.
nondeterministic_goal.
goal_that_fails:- fail.
goal_raising_exception:- throw(egg).

check_value(A, B):- A==B, !.
check_value(A, B):- throw(mismatch(A,B)).


foo:-
        test1,
        writeln(ok(1)),
        test2,
        writeln(ok(2)),
        test3,
        writeln(ok(3)),
        test4,
        writeln(ok(4)),
        test5,
        writeln(ok(5)).

test1:-
        setup_call_catcher_cleanup(Setup=ok,
                                   deterministic_goal,
                                   Catcher,
                                   Cleanup=ok),
        Setup == ok,
        Cleanup == ok,
        Catcher == exit.

test2:-
        setup_call_catcher_cleanup(Setup=ok,
                                   nondeterministic_goal,
                                   Catcher,
                                   Cleanup=ok),
        Setup == ok,
        var(Catcher),
        var(Cleanup),
        !,
        Cleanup == ok,
        Catcher == !.
        
test3:-
        setup_call_catcher_cleanup(Setup=ok,
                                   goal_that_fails,
                                   Catcher,
                                   ( check_value(Setup, ok),
                                     check_value(Catcher, fail))).

test3.

error_setup_call_cleanup_test_1:-
        setup_call_catcher_cleanup(Setup=ok,
                                   goal_raising_exception,
                                   Catcher,
                                   ( check_value(Setup, ok),
                                     check_value(Catcher, exception(egg)))),
        throw(unexpected_success).

test4:-
        catch(error_setup_call_cleanup_test_1,
              Exception,
              Error = Exception),
        check_value(Error, egg).      


test5:-
        setup_call_catcher_cleanup(true,
                                   setup_call_catcher_cleanup(true,
                                                              true,
                                                              C1,
                                                              true),
                                   C2,
                                   true),
        C1 == exit,
        C2 == exit.
*/