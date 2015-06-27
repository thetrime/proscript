term_expansion((test(Label, ExpectedPort):- Body), (test(Label):- (catch(setup_call_catcher_cleanup(format('~w: ', [Label]),
                                                                                                    Body,
                                                                                                    Port,
                                                                                                    check_test_results(Port, ExpectedPort)),
                                                                         _,
                                                                         true)->true ; true))).

run_unit_tests:-
        gc,
        writeln(running_tests),
        debug,
        forall(clause(test(Description), _),
               run_test(Description)),
        statistics.

run_test(Description):-
        test(Description).

check_test_results(A, A):- true, !, format('OK~n', []).
check_test_results(Got, Expected):- format('FAIL: Expected ~q, got ~q~n', [Expected, Got]), throw(failed_test).

once_test_1.
once_test_1.


test(cut, exit):-
        once_test_1,
        !.

findall_test_1(a).
findall_test_1(c).
findall_test_1(b).
findall_test_1(d).
test(findall, exit):-
        findall(X,
                findall_test_1(X),
                Xs),
        Xs == [a,c,b,d].


test(once, exit):-
        once(once_test_1).

test(repeat, exit):-
        flag(foo, _, 0),
        repeat,
        flag(foo, N, N+1),
        writeln(N),
        N =:= 5,
        !.

test(not(1), exit):-
        \+(fail).
test(not(2), fail):-
        \+(true).
test(not(3), exit):-
        \+(\+(A=a)),
        var(A).       

test(arg(1), fail):-
        arg(0, foo(a,b), _).
test(arg(2), exit):-
        arg(1, foo(a,b), a).
test(arg(3), exit):-
        arg(2, foo(a,b,c), b).
test(arg(4), fail):-
        arg(4, foo(a,b,c), _).
test(arg(5), exit):-
        arg(3, foo(a,b,c), c).

test(subsumes_term(1), exit):-
        subsumes_term(a,a).

test(subsumes_term(2), exit):-
        subsumes_term(f(X,Y),f(Z,Z)).

test(subsumes_term(3), fail):-
        subsumes_term(f(Z,Z), f(X,Y)).

test(subsumes_term(4), fail):-
        subsumes_term(g(X),g(f(X))).

test(subsumes_term(5), fail):-
        subsumes_term(X, f(X)).

test(subsumes_term(6), exit):-
        subsumes_term(X, Y),
        subsumes_term(Y, f(X)).

test(sub_atom(1), exit):-
        findall(A-B-C-D,
                sub_atom(splungesp, A, B, C, D),
                R1),
        R1 == [0-0-9-'',0-1-8-s,0-2-7-sp,0-3-6-spl,0-4-5-splu,0-5-4-splun,0-6-3-splung,0-7-2-splunge,0-8-1-splunges,0-9-0-splungesp,1-0-8-'',1-1-7-p,1-2-6-pl,1-3-5-plu,1-4-4-plun,1-5-3-plung,1-6-2-plunge,1-7-1-plunges,1-8-0-plungesp,2-0-7-'',2-1-6-l,2-2-5-lu,2-3-4-lun,2-4-3-lung,2-5-2-lunge,2-6-1-lunges,2-7-0-lungesp,3-0-6-'',3-1-5-u,3-2-4-un,3-3-3-ung,3-4-2-unge,3-5-1-unges,3-6-0-ungesp,4-0-5-'',4-1-4-n,4-2-3-ng,4-3-2-nge,4-4-1-nges,4-5-0-ngesp,5-0-4-'',5-1-3-g,5-2-2-ge,5-3-1-ges,5-4-0-gesp,6-0-3-'',6-1-2-e,6-2-1-es,6-3-0-esp,7-0-2-'',7-1-1-s,7-2-0-sp,8-0-1-'',8-1-0-p,9-0-0-''].

test(sub_atom(2), exit):-
        findall(B-C-D,
                sub_atom(splungesp, 2, B, C, D),
                R2),
        R2 == [0-7-'',1-6-l,2-5-lu,3-4-lun,4-3-lung,5-2-lunge,6-1-lunges,7-0-lungesp].

test(sub_atom(3), exit):-
        findall(B-C-D,
                sub_atom(splungesp, B, 2, C, D),
                R3),
        R3 = [0-7-sp,1-6-pl,2-5-lu,3-4-un,4-3-ng,5-2-ge,6-1-es,7-0-sp].

test(sub_atom(4), exit):-
        findall(B-C-D,
                sub_atom(splungesp, B, C, 2, D),
                R4),
        R4 = [0-7-splunge,1-6-plunge,2-5-lunge,3-4-unge,4-3-nge,5-2-ge,6-1-e,7-0-''].

test(sub_atom(5), exit):-
        findall(B-C-D,
                sub_atom(splungesp, B, C, D, sp),
                R5),
        R5 = [0-2-7,7-2-0].

test(sub_atom(6), exit):-
        findall(C-D,
                sub_atom(splungesp, 2, C, 2, D),
                R6),
        R6 = [5-lunge].

test(sub_atom(7), exit):-
        findall(C-D,
                sub_atom(splungesp, C, 2, 2, D),
                R7),
        R7 == [5-ge].

test(sub_atom(8), exit):-
        findall(C-D,
                sub_atom(splungesp, 2, 2, C, D),
                R8),
        R8 == [5-lu].

test(sub_atom(9), exit):-
        findall(D,
                sub_atom(splungesp, 2, 2, 2, D),
                R9),
        R9 == [].


test(arithmetic_test(1), exit):- 
        X is 1+2,
        X == 3 .
test(arithmetic_test(2), exit):-
        Y is 3*9+1,
        Y == 28 .

test(arithmetic_test(3), exception(type_error(evaluable,t/0))):-
        Z is 3 + t .

test(arithmetic_test(4), exit):-
        Y is max(2, 7),
        Y == 7 .
setup_call_catcher_cleanup(true,
                                   setup_call_catcher_cleanup(true,
                                                              true,
                                                              C1,
                                                              Cleanup = ok),
                                   C2,
                                   Cleanup2 = ok),
        !,
        writeln(C2-Cleanup2).
test(arithmetic_test(5), exit):-
        Y is sin(pi),
        Y < 0.0001,
        Y > -0.0001 .

test(univ(1), exit):-
        foo(bar) =.. A,
        A == [foo, bar].

test(univ(2), exit):-
        foo =.. A,
        A == [foo].

test(univ(3), exit):-
        A =.. [foo, bar],
        A == foo(bar).

test(univ(4), exit):-
        A =.. [foo, bar, baz],
        A == foo(bar, baz).

test(univ(5), exit):-
        [a, b, c] =.. A,
        A == ['.', a, [b,c]].

deterministic_goal.
nondeterministic_goal.
nondeterministic_goal.
goal_that_fails:- fail.
goal_raising_exception:- throw(egg).
check_value(A, B):- A == B, !.
check_value(A, B):- throw(mismatch(A,B)).


test(deterministic_setup_call_cleanup, exit):-
        setup_call_catcher_cleanup(Setup=ok,
                                   deterministic_goal,
                                   Catcher,
                                   Cleanup=ok),
        Setup == ok,
        Cleanup == ok,
        Catcher == exit.

test(nondeterministic_setup_call_cleanup, exit):-
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

test(failing_setup_call_cleanup, fail):-
        setup_call_catcher_cleanup(Setup=ok,
                                   goal_that_fails,
                                   Catcher,
                                   ( check_value(Setup, ok),
                                     check_value(Catcher, fail))).


error_setup_call_cleanup_test_1:-
        setup_call_catcher_cleanup(Setup=ok,
                                   goal_raising_exception,
                                   Catcher,
                                   ( check_value(Setup, ok),
                                     check_value(Catcher, exception(egg)))),
        throw(unexpected_success).

test(error_setup_call_cleanup, exit):-
        catch(error_setup_call_cleanup_test_1,
              Exception,
              Error = Exception),
        check_value(Error, egg).
