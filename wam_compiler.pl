/* To do list
    Garbage collection
    indexing
    Bignums?
    Modules
    Directives
    ISO exceptions
    Fix the 0x80000000 hack. Just make new opcodes for try/retry/trust in aux clauses.
    Environment trimming is not quite right. We cannot trim the environment at the point where it gets deallocated, since
       then !(Var) will not work (since it cannot look up Var, as we deleted it). But at the same time, if we do NOT trim it, EnvSize is wrong
       though it is only too big, not too small, so at least it is just inefficient, rather than dangerous.
*/

/* Overview:
Compilation is fairly direct. Note that a query is a clause without a head, and a fact is a clause without a body.
The machine has only X-registers. I ignore the distinction between A- and X- registers - A0 is the same as X0 (this is true in the paper as well; the A- notation is
purely notational and has no semantic meaning. In other words, 'the arguments to a n-ary predicate are passed in the first n X-registers'.

Compilation has 4 parts: Head, Head-unification, Body, Body-unification.
   * First compile the head. This involves a get_* for each argument to the head.
      * If we get_structure, we may end up needing to get some of the arguments as variables, since foo(bar(x, baz(y))):- ... is effectively compiled into
        foo(X):- X = bar(x, Y), Y = baz(y), ...
        Therefore, after a get_structure we compile in a slightly different mode where we can unify with integers, unify with atoms, unify with existing variables
        and unify with fresh variables which we must later unify with structures via get_structure(FreshVar, ....)
   * Next, compile the body
      * If we put_structure, we must then unify the arguments of the body. This is a bit more complicated; we have to already have them on the heap if we want to use them.
        Because of this, we have to do things slightly backwards: If we want to put_structure and then N arguments to that structure, first we compile the arguments
        into M fresh variables (we only need to do this for arguments which are not variables, constants or integers), and emit opcodes for that BEFORE we do the
        put_structure and its associated arguments (which are now either all fresh variables, constants, integers, or existing variables we just created)

Register allocation is as follows:
   * First, determine permanent variables. I use Ait-Kaci's definition, rather than Warren's, because of the serious flaw pointed out in AK.
      * A variable is permanent if it occurs in more than one goal, where the first goal shares the variables with the head.
      * Any variable which is not permanent is temporary.
   * Before compiling each n-ary body goal, we must reserve n X-registers for the arguments. Anything above that is fair game
      * Since X-registers are temporary, their contents before compiling this particular body goal are irrelevant, and we are allowed to zap any of them we like
      * However, the M-ary head and N-ary first body goal have to be considered a single unit. Really the number of X-registers to reserve is max(N,M), but I use N+M.

In addition to just identifying permanent variables, we must progressively trim them from the list as execution proceeds. This enables us to keep track of what the argument
to call() and call_aux() should be which is used to do generalized LCO (ie environment trimming).

Disjuncts are handled via auxiliary clauses. That is, (A;B) is effectively compiled to aux_N, and later we must define
   * aux_N :- A.
   * aux_N :- B.
The argument sof aux_N are the variables in (A;B), plus optionally the cut variable for the current clause. This brings us to

Cuts are harder than they seem! If we didn't have auxiliary clauses, it would be a lot simpler. ! has to be transparent to these clauses, so we must pass in the point to
cut to as an argument to auxiliary clauses. This introduces quite a bit of complexity to the compilation. First, ! is translated into !(FreshVar) in the compilation. If there
is more than one cut in a body, FreshVar is unified. This is included in the list of 'arguments' to an auxiliary clause, which allows ! in an aux clause to find the right
cut point to cut in the actual clause. Consequently, a local cut is just a cut without this sharing - when compiling the aux clause, we check if a local cut has been detected
and then emit a get_level() there as well. To avoid complete confusion, (A->B->C) is translated with an aux_clause: (aux_1->C), and (aux_1:- A->B)

Multiple clauses are handled by a 2-word reserved space before each clause. The bytes are either:
   * trust_me, 0
   * try_me_else, L
   * retry_me_else, L
   * NOP, 0
The NOP case is for when there is only one clause and we do not need to create or destroy a choicepoint. This holds space for adding a try_me_else if we ever add more clauses
later.

The toplevel is a bit weird. There's no way to create an environment unless we are in a call, there's a chicken-and-egg situation: We cannot have a call unless there are 2
goals in a body, since otherwise it's either a fact or a chain, and neither of those have call() opcodes. Unfortunately, any 2+ goal clause requires an environment!
To resolve this, I have a faux-toplevel which just does call(toplevel/0, 0). Then I must ensure toplevel never returns, or we will be in a right mess, so I add execute(halt/0).
Note that this is essentially illegal, but it is safe since, despite the fact that toplevel/0 will have mucked up CP, it was originally set to garbage, so we don't need to save
it. Calling halt/0 never returns.

Some gotchas:
   * Even if there are no permanent variables, we still need an environment if there is more than one body goal so we can correctly save CP between calls

*/

% Directives are ignored by the WAM currently, so this is safe enough.
:-module(wam_compiler, [build_saved_state/2, bootstrap/2, op(920, fy, ?), op(920, fy, ??)]).
:-ensure_loaded(testing).
:-ensure_loaded(wam_bootstrap).

expand_term(In, Out):-
        current_predicate(term_expansion/2),
        term_expansion(In, Out),
        !.
expand_term(In, In).

compile_clause(Term):-
        format('Compiling ~q~n', [Term]),
        expand_term(Term, Terms),
        gc,
        writeln(done_gc),
        compile_clause_1(Terms).

compile_clause_1([]):- !.
compile_clause_1([Head|Tail]):-
        !,
        compile_clause_2(Head),
        save_clause(Head),
        compile_clause_1(Tail).
compile_clause_1(Term):-
        compile_clause_2(Term),
        !,
        save_clause(Term).

compile_clause_2(?- Body):-
        !,
        transform_body(Body, first, Transformed1, ExtraClauses, [], CutVariable),
        commit_to_cut(CutVariable),
        entail(Transformed1, Transformed),
        permanent_variable_list(true(CutVariable), Transformed, PermanentVariables),
        environment_size_required(PermanentVariables, Transformed, EnvSize),
        allocate_environment(EnvSize, CutVariable, PermanentVariables, Opcodes, O1, [next(Arity)], State),
        first_goal_arity(Body, Arity),
        compile_body(Transformed, PermanentVariables, EnvSize, State, _, O1, O2),
        compile_auxiliary_goals(ExtraClauses, O2, []),
        reset_compile_buffer,
        assemble(Opcodes, 2). % Note that a query is just compiled into the buffer and left there

compile_clause_2(Head :- Body):-
        !,
        transform_body(Body, first, Transformed1, ExtraClauses, [], CutVariable),
        commit_to_cut(CutVariable),
        entail(Transformed1, Transformed),
        permanent_variable_list(Head-CutVariable, Transformed, PermanentVariables),
        environment_size_required(PermanentVariables, Transformed, EnvSize),
        first_goal_arity(Body, BodyArity),
        compile_head(Head, BodyArity, CutVariable, PermanentVariables, EnvSize, State, Opcodes, O1),
        % Do NOT try and change the state size here! Space for the first goal and head are both set
        % aside in compile_head. Just because the head has only N arguments does NOT mean that it
        % only uses N registers!
        compile_body(Transformed, PermanentVariables, EnvSize, State, _, O1, O2),
        compile_auxiliary_goals(ExtraClauses, O2, []),
        reset_compile_buffer,
        !,
        assemble(Opcodes, 2).



compile_clause_2(Head):-
        compile_head(Head, 0, no_cut, [], none, _State, Opcodes, [proceed]),
        reset_compile_buffer,
        assemble(Opcodes, 2).


next_free_variable([next(A)|_], A):- !.
next_free_variable([_|S], A):- next_free_variable(S, A).


commit_to_cut(no_cut):- !.
commit_to_cut(has_cut(_)).

first_goal_arity((A,_), N):- !, first_goal_arity(A, N).
first_goal_arity(A, N):- functor(A, _, N).

transform_body(Body, Position, NewBody, ExtraClauses, Tail, CutVariable):-
        current_predicate(goal_expansion/2),
        goal_expansion(Body, B1),
        B1 \= Body,
        !,
        transform_body(B1, Position, NewBody, ExtraClauses, Tail, CutVariable).

transform_body((Goal, Goals), Position, (NewGoal, NewGoals), ExtraClauses, Tail, CutVariable):-
        !,
        transform_body(Goal, Position, NewGoal, ExtraClauses, T1, CutVariable),
        transform_body(Goals, not_first, NewGoals, T1, Tail, CutVariable).

transform_body(once(Goal), _Position, aux_head(Aux, Variables), [aux_definition(Aux, Variables, local_cut(LocalCutVariable), (Goal1, !(LocalCutVariable)))|ExtraClauses], Tail, CutVariable):-
        !,
        transform_body(Goal, not_first, Goal1, ExtraClauses, Tail, CutVariable),
        term_variables(Goal, V1),
        include_cut_point_as_argument_if_needed(CutVariable, V1, Variables).

% setup_call_catcher_cleanup(Setup, Goal, Catcher, Cleanup).
% This requires a bit of explanation since it is far from obvious how I have implemented it.
% First, we compile the goal into the following: (Operations in angle-brackets are special-purpose opcodes)
% setup_call_catcher_cleanup(Setup, Goal, Catcher, Cleanup):- call(Setup), aux_1.
% aux_1:- <get_choicepoint(B)>, mark_top_choicepoint(CleanupVars, Mark), aux_3, call(Goal), <get_choicepoint(B1)>, aux2(B, B1, Mark).
% aux_1:- Catcher = fail, call(Cleanup), !, fail.
% aux_2(B, B1, Mark):- B == B1, Catcher = exit, call(Cleanup), unmark_choicepoint(Mark).
% aux_2(_,_,_).
% aux_3:- Catcher = !, call(Cleanup), halt.

% Some interesting things:
% A) aux_1, before even calling the goal, appears to call aux_3. The reason for this is that mark_top_choicepoint/2 is extralogical, and saves the information about the *next instruction* to the stack, so that we can go back to it when a cut is detected.
%    >> It then skips the next instruction!
% B) aux_3, the ! case, calls halt/0.
%    This is because we run the aux_3 code with a completely new state (almost - the heap and stack are still present, but all the registers, backtrack pointer, etc, are empty). When the cleanup has finished running, it must resume execution from where we
%    left off, and it does this by exiting out of the main wam() loop by executing halt/0.
% C) aux_3 is called with no arguments, but defined with some. This is because we must have aux_3 immediately after the mark_top_choicepoint/2 call, without any put_* or unify_* instructions. mark_top_choicepoint/2 knows how many arguments there are because
%    they're passed in as an argument.
% D) The catch/2 introduces 2 choicepoints. This is why to check for determinism we must compare state.B before the goal and the third-to-top state.B afterwards!
% E) Because Goal1 may include a !, we can only be sure that the top choicepoint after Goal1 (ie B2) is equal to *or less than* the original one if the goal is deterministic.
%       We can shield the ! from leaking out of the whole goal, but not leaking out of the aux itself. This is why we have >=(B,B1) and not =(B,B1) in aux2.
transform_body(setup_call_catcher_cleanup(Setup, Goal, Catcher, Cleanup), _Position, (Setup1, goal(get_current_block(Block)), aux_head(Aux1, [Block|V1])), AuxClauses, Tail, CutVariable):-
        !,
        AuxClauses = [aux_definition(Aux1, [B1|V1], no_local_cut, (goal(mark_top_choicepoint(MarkVariables, Mark)),
                                                                   aux_head(Aux3, []),
                                                                   goal(install_new_block(NewBlock)),
                                                                   aux_head(GoalAux, GoalVars),
                                                                   get_top_choicepoint(0, B2),
                                                                   goal(end_block(B1, NewBlock)),
                                                                   aux_head(Aux2, [NewBlock, B2, Mark|V2]))),
                      aux_definition(Aux1, [B1|V1], local_cut(CutVar), (goal(reset_block(B1)),
                                                                        goal(get_exception(Ball)),
                                                                        !(CutVar),
                                                                        goal(Catcher = exception(Ball)),
                                                                        Cleanup1,
                                                                        goal(unwind_stack))), % Since we did not clear the exception, this is like rethrowing it
                      aux_definition(Aux1, [_|V1], local_cut(CutVar), (goal(Catcher = fail),
                                                                       goal(unmark_top_choicepoint),
                                                                       Cleanup1,
                                                                       !(CutVar),
                                                                       goal(fail))),
                      aux_definition(GoalAux, GoalVars, MaybeLocalCut, Goal1),
                      aux_definition(Aux2, [B, B1, Mark|V2], no_local_cut, (goal(=(B, B1)),
                                                                                  goal(Catcher = exit),
                                                                                  goal(unmark_choicepoint(Mark)),
                                                                                  Cleanup1)),
                      aux_definition(Aux2, _, no_local_cut, goal(true)),
                      aux_definition(Aux3, MarkVariables, no_local_cut, (goal(Catcher = !), Cleanup1, goal(halt)))|Clauses],
        compile_message(need(Aux1)),
        term_variables(Catcher-Cleanup, MarkVariables),
        transform_body(Setup, not_first, Setup1, Clauses, C1, CutVariable),
        % Shield the parent choicepoint from cuts. Cuts inside the goal should be considered local to the aux1 clause (oddly enough?)
        transform_body(Goal, not_first, Goal1, C1, C2, NewVar),
        instantiate_local_cut(MaybeLocalCut, NewVar), % This is run backwards!
        term_variables(Goal, GoalVars),
        transform_body(Cleanup, not_first, Cleanup1, C2, Tail, CutVariable),
        term_variables(Goal-Catcher-Cleanup, V1a),
        include_cut_point_as_argument_if_needed(CutVariable, V1a, V1),
        term_variables(Catcher-Cleanup, V2a),
        include_cut_point_as_argument_if_needed(CutVariable, V2a, V2).


% catch/3
% catch(Goal, Catcher, Recovery) is translated as follows:
% get_current_block(Block), aux_1(Goal, Catcher, Recovery, Block).
% aux_1(Goal, Catcher, Recovery, Block):- install_new_block(NewBlock), <compilation of Goal>, end_block(Block, NewBlock).
% aux_1(_, Catcher, Recovery, Block):- reset_block(Block), get_exception(Ball), aux_2(Ball, Catcher, Recovery).
% aux_2(Ball, Ball, Recovery):- !, clear_exception, <compilation of Recovery>
% aux_2(_, _, _):- unwind_stack.

transform_body(catch(Goal, Catcher, Recovery), _Position, (goal(get_current_block(Block)), aux_head(Aux1, [Block, Catcher|V1])), [aux_definition(Aux1, [B1, _|V1], no_local_cut, (goal(install_new_block(NewBlock)), Goal1, goal(end_block(B1, NewBlock)))),
                                                                                                                                                               aux_definition(Aux1, [B2, Catcher|V1], no_local_cut, (goal(reset_block(B2)), goal(get_exception(Ball)), aux_head(Aux2, [Ball, Catcher|V1]))),
                                                                                                                                                               aux_definition(Aux2, [Ball, Catcher|V1], local_cut(CutVar), (goal(Ball = Catcher), !(CutVar), goal(clear_exception), Recovery1)),
                                                                                                                                                               aux_definition(Aux2, [_, _|V1], no_local_cut, (goal(unwind_stack)))|Clauses], Tail, CutVariable):-
        transform_body(Goal, not_first, Goal1, Clauses, C1, CutVariable),
        transform_body(Recovery, not_first, Recovery1, C1, Tail, CutVariable),
        term_variables(Goal-Recovery, V1a),
        include_cut_point_as_argument_if_needed(CutVariable, V1a, V1).

% forall/2
% forall(Cond, Action) is simply translated as \+(Cond, \+Action).
transform_body(forall(Cond, Action), Position, Translated, [aux_definition(Aux, Variables, no_local_cut, AuxBody)|ExtraClauses], Tail, CutVariable):-
        !,
        transform_body(\+aux_head(Aux, Variables), Position, Translated, ExtraClauses, E1, CutVariable),
        transform_body((Cond, \+Action), not_first, AuxBody, E1, Tail, CutVariable),
        term_variables(Cond-Action, V1),
        include_cut_point_as_argument_if_needed(CutVariable, V1, Variables).

transform_body((A->B ; C), _Position, aux_head(Aux, Variables), [aux_definition(Aux, Variables, local_cut(LocalCutVariable), (AA, !(LocalCutVariable), BB)),
                                                                 aux_definition(Aux, Variables, no_local_cut, CC)|ExtraClauses], Tail, CutVariable):-
        !,
        transform_body(A, not_first, AA, ExtraClauses, T1, CutVariable),
        transform_body(B, not_first, BB, T1, T2, CutVariable),
        transform_body(C, not_first, CC, T2, Tail, CutVariable),
        term_variables(AA-BB-CC, V1),
        include_cut_point_as_argument_if_needed(CutVariable, V1, Variables).


transform_body((A -> B), _Position, aux_head(Aux, Variables), [aux_definition(Aux, Variables, local_cut(LocalCutVariable), (AA, !(LocalCutVariable), BB))|ExtraClauses], Tail, CutVariable):-
        !,
        transform_body(A, not_first, AA, ExtraClauses, T1, CutVariable),
        transform_body(B, not_first, BB, T1, Tail, CutVariable),
        term_variables(AA-BB, V1),
        include_cut_point_as_argument_if_needed(CutVariable, V1, Variables).

transform_body((LHS ; RHS), _Position, aux_head(Aux, Variables), [aux_definition(Aux, Variables, no_local_cut, LHS1), aux_definition(Aux, Variables, no_local_cut, RHS1)|Clauses], Tail, CutVariable):-
        !,
        transform_body(LHS, not_first, LHS1, Clauses, C1, CutVariable),
        transform_body(RHS, not_first, RHS1, C1, Tail, CutVariable),
        term_variables(LHS-RHS, V1),
        include_cut_point_as_argument_if_needed(CutVariable, V1, Variables).

transform_body(\+(Goal), _Position, aux_head(Aux, Variables), [aux_definition(Aux, Variables, local_cut(LocalCutVariable), (Goal1, !(LocalCutVariable), goal(fail))), aux_definition(Aux, Variables, no_local_cut, goal(true))|T1], Tail, _):-
        !,
        transform_body(Goal, not_first, Goal1, T1, Tail, CutVariable),
        term_variables(Goal, V1),
        include_cut_point_as_argument_if_needed(CutVariable, V1, Variables).

transform_body(!, not_first, !(CutVariable), Tail, Tail, has_cut(CutVariable)):- !.
transform_body(aux_head(Aux, Variables), _Position, aux_head(Aux, Variables), Tail, Tail, _):- !.
transform_body(goal(Goal), _Position, goal(Goal), Tail, Tail, _):- !.
transform_body(Goal, _Position, goal(Goal), Tail, Tail, _).

include_cut_point_as_argument_if_needed(CutVariable, V1, Variables):-
        var(CutVariable), !, Variables = V1.
% If Variables already includes CutVariable then do not include it a second time. This can happen if auxiliary clauses are nested several layers deep - we only need
% a single link to the main clause
include_cut_point_as_argument_if_needed(has_cut(CutVariable), V1, V1):-
        variable_is_in_list(CutVariable, V1), !.
include_cut_point_as_argument_if_needed(has_cut(CutVariable), V1, [CutVariable|V1]).

compile_auxiliary_goals([], O, O):- !.
compile_auxiliary_goals([aux_definition(Label, Variables, LocalCutVariable, Body1)|Aux], [aux_label(Label)|Opcodes], Tail):-
        entail(Body1, Body),
        instantiate_local_cut(LocalCutVariable, LocalCut),
        permanent_variable_list(Variables-LocalCut, Body, PermanentVariables),
        environment_size_required(PermanentVariables, Body, EnvSize),
        list_length(Variables, Arity),
        first_goal_arity(Body, BodyArity),
        include_local_cut_in_arity(Arity, LocalCut, A0),
        A1 is A0 + BodyArity,
        allocate_environment(EnvSize, LocalCut, PermanentVariables, Opcodes, O1, [next(A1)], State),
        compile_head_args(Variables, State, S1, 0, PermanentVariables, O1, O2),
        compile_body(Body, PermanentVariables, EnvSize, S1, _, O2, O3),
        compile_auxiliary_goals(Aux, O3, Tail).

include_local_cut_in_arity(N, no_cut, N):- !.
include_local_cut_in_arity(N, has_cut(_), NN):- NN is N+1.

instantiate_local_cut(no_local_cut, no_cut):- !.
instantiate_local_cut(local_cut(V), has_cut(V)).

environment_size_required(Variables, (_,_), Length):-
        !,
        list_length(Variables, Length).
environment_size_required(Variables, (A;_), Length):-
        environment_size_required(Variables, A, Length),
        Length \== none,
        !.
environment_size_required(Variables, (_;A), Length):-
        environment_size_required(Variables, A, Length),
        Length \== none,
        !.
environment_size_required(Variables, _, Length):-
        list_length(Variables, Length),
        Length > 0,
        !.
environment_size_required(_, _, none).

list_length(A, B):-
        list_length_1(A, 0, B).

list_length_1([], N, N):- !.
list_length_1([_|A], N, L):-
        NN is N+1,
        list_length_1(A, NN, L).

entail(Goal, Flattened):-
        last_goal(Goal, Head, Last),
        !,
        entail(Head, Last, Flattened).
entail(Goal, Goal).

last_goal((A,B), (A, Z), C):- last_goal(B, Z, C), !.
last_goal((A,B), A, B):- !.

entail((Item, Tail), L, Flattened):-
        !,
        entail(Item, L1, Flattened),
        entail(Tail, L, L1).
entail(Item, Flattened, (Item, Flattened)).


permanent_variable_list(Head, (Goal1, Goals), Permanent):-
        !,
        grab_variables_from_goals((Head-Goal1, Goals), [], VariablesInSubgoals),
        list_length(VariablesInSubgoals, L),
        term_variables(VariablesInSubgoals, AllVariables),
        classify_variables(AllVariables, 0, _, VariablesInSubgoals, L, Permanent).

% Chain rules have no permanent variables.
permanent_variable_list(_, _, []):- !.

classify_variables([], I, I, _, _, []):- !.
classify_variables([Variable|Variables], I, N, VariablesInSubgoals, L, [permanent_var(Variable, y(I), last_occurrence(LastOccurrence))|Permanent]):-
        variable_is_permanent(Variable, 0, VariablesInSubgoals, 0, [], RevLastOccurrence),
        % If there are 2 goals, then a variable occurring in the last goal occurs in goal 1, since LastOccurrence is 0-based
        LastOccurrence is L - RevLastOccurrence - 1,
        !,
        II is I+1,
        classify_variables(Variables, II, N, VariablesInSubgoals, L, Permanent).

classify_variables([_|Variables], I, II, VariablesInSubgoals, L, Permanent):-
        classify_variables(Variables, I, II, VariablesInSubgoals, L, Permanent).

variable_is_permanent(_, 2, _, _, [_,I], I):- !.
variable_is_permanent(Variable, OccurrencesSoFar, [VariablesInAGoal|VariablesInOtherGoals], P, T, LastOccurrence):-
        variable_is_in_list(Variable, VariablesInAGoal),
        !,
        Occurrences is OccurrencesSoFar + 1,
        PP is P+1,
        variable_is_permanent(Variable, Occurrences, VariablesInOtherGoals, PP, [P|T], LastOccurrence).
variable_is_permanent(Variable, OccurrencesSoFar, [_|VariablesInOtherGoals], P, T, LastOccurrence):-
        PP is P+1,
        variable_is_permanent(Variable, OccurrencesSoFar, VariablesInOtherGoals, PP, T, LastOccurrence).

% grab_variables_from_goals returns the list of variables in reverse order so as to
% facilitate LCO
grab_variables_from_goals((Goal, Goals), A, B):-
        term_variables(Goal, Vars),
        !,
        grab_variables_from_goals(Goals, [Vars|A], B).
grab_variables_from_goals(LastGoal, A, [Vars|A]):-
        term_variables(LastGoal, Vars).

variable_is_in_list(Var, [V|_]):- V == Var, !.
variable_is_in_list(Var, [_|Vars]):- variable_is_in_list(Var, Vars).

%% compile_head(+Head, +BodyArgCount +HasCut, +PermanentVariables, +EnvSize, -State, -Opcodes, +Tail)
compile_head(Head, BodyArgCount, HasCut, PermanentVariables, EnvSize, State, Opcodes, Tail):-
        allocate_environment(EnvSize, HasCut, PermanentVariables, Opcodes, O1, [next(Reserved)], S1),
        Head =.. [_Functor|Args],
        list_length(Args, Arity),
        Reserved is Arity + BodyArgCount,
        compile_head_args(Args, S1, State, 0, PermanentVariables, O1, Tail).

allocate_environment(none, _, _, A, A, S, S):-!.
allocate_environment(_, no_cut, PermanentVariables, [allocate|Allocations], B, S, S1):- !,
        ensure_vars_allocated(PermanentVariables, Allocations, B, S, S1).
allocate_environment(_, has_cut(Var), PermanentVariables, [allocate|Allocations], C, S, [var(Var, get, R)|ST]):-
        ensure_vars_allocated(PermanentVariables, Allocations, [get_level(R)|C], S, ST),
        variable_is_known_permanent(Var, PermanentVariables, R), !.

%ensure_vars_allocated(_, T, T, S, S):- !.
ensure_vars_allocated([], Tail, Tail, S, S):- !.
ensure_vars_allocated([permanent_var(Variable, y(I), _)|PermanentVariables], [put_variable(y(I))|Opcodes], Tail, S, STail):-
        ensure_vars_allocated(PermanentVariables, Opcodes, Tail, [var(Variable, put, y(I))|S], STail).

deallocate_environment(none, A, A):-!.
deallocate_environment(_, [deallocate|A], A).


atom_or_empty_list(A):- A == [].
atom_or_empty_list(A):- atom(A).

compile_head_args([], S, S, _, _, A, A):-!.
compile_head_args([Arg|Args], State, S2, I, PermanentVariables, Opcodes, Tail):-
        compile_head_arg(Arg, State, S1, x(I), PermanentVariables, Opcodes, O1),
        II is I+1,
        compile_head_args(Args, S1, S2, II, PermanentVariables, O1, Tail).

compile_head_arg(Arg, State, State, Ai, _PermanentVariables, [get_constant(Arg, Ai)|Tail], Tail):-
        atom_or_empty_list(Arg),
        !.
compile_head_arg(Arg, State, State, Ai, _PermanentVariables, [get_integer(Arg, Ai)|Tail], Tail):-
        integer(Arg),
        !.
compile_head_arg(Arg, State, State, Ai, _PermanentVariables, [get_float(Arg, Ai)|Tail], Tail):-
        float(Arg),
        !.
compile_head_arg(Arg, State, S1, Ai, PermanentVariables, Opcodes, Tail):-
        var(Arg),
        !,
        get_variable(Arg, Ai, PermanentVariables, State, S1, Opcodes, Tail).

compile_head_arg([Head|Tail], State, S2, Ai, PermanentVariables, [get_list(Ai)|O1], OpcodesTail):-
        compile_head_unification([Head, Tail], State, S1, PermanentVariables, O1, O2, Unifications),
        complete_head_unification(Unifications, S1, S2, PermanentVariables, O2, OpcodesTail).

compile_head_arg(Arg, State, S2, Ai, PermanentVariables, [get_structure(Functor/Arity, Ai)|O1], Tail):-
        Arg =.. [Functor|Args],
        list_length(Args, Arity),
        compile_head_unification(Args, State, S1, PermanentVariables, O1, O2, Unifications),
        complete_head_unification(Unifications, S1, S2, PermanentVariables, O2, Tail).


compile_head_unification([], S, S, _, O, O, []):- !.
compile_head_unification([Arg|Args], State, S1, PermanentVariables, [unify_constant(Arg)|O1], Tail, Unifications):-
        atom_or_empty_list(Arg),
        !,
        compile_head_unification(Args, State, S1, PermanentVariables, O1, Tail, Unifications).
compile_head_unification([Arg|Args], State, S1, PermanentVariables, [unify_integer(Arg)|O1], Tail, Unifications):-
        integer(Arg),
        !,
        compile_head_unification(Args, State, S1, PermanentVariables, O1, Tail, Unifications).
compile_head_unification([Arg|Args], State, S1, PermanentVariables, [unify_float(Arg)|O1], Tail, Unifications):-
        float(Arg),
        !,
        compile_head_unification(Args, State, S1, PermanentVariables, O1, Tail, Unifications).
compile_head_unification([Arg|Args], State, S2, PermanentVariables, Opcodes, Tail, Unifications):-
        var(Arg),
        !,
        unify_variable(Arg, PermanentVariables, State, S1, Opcodes, O1),
        compile_head_unification(Args, S1, S2, PermanentVariables, O1, Tail, Unifications).
compile_head_unification([Arg|Args], State, S2, PermanentVariables, [unify_variable(Xi)|O1], Tail, [unify(Xi, Arg)|U]):-
        !,
        fresh_variable(State, S1, Xi),
        compile_head_unification(Args, S1, S2, PermanentVariables, O1, Tail, U).
complete_head_unification([], S, S, _PermanentVariables, Tail, Tail).
complete_head_unification([unify(Xi, Arg)|U], S1, S3, PermanentVariables, Opcodes, Tail):-
        compile_head_arg(Arg, S1, S2, Xi, PermanentVariables, Opcodes, O1),
        complete_head_unification(U, S2, S3, PermanentVariables, O1, Tail).

get_variable(Arg, Source, _PermanentVariables, State, State, [get_value(Register, Source)|Tail], Tail):-
        already_used(Arg, State, Register, _), !.
get_variable(Arg, Source, PermanentVariables, State, [var(Arg, get, y(I))|State], [get_variable(y(I), Source)|Tail], Tail):-
        variable_is_known_permanent(Arg, PermanentVariables, y(I)), !.
get_variable(Arg, Source, _PermanentVariables, State, [var(Arg, get, Xi)|S1], [get_variable(Xi, Source)|Tail], Tail):-
        !, fresh_variable(State, S1, Xi).

unify_variable(Arg, _PermanentVariables, State, S1, Opcodes, Tail):-
        already_used(Arg, State, Register, How),
        !,
        unify_possibly_local_variable(How, Register, Opcodes, Arg, State, S1, Tail).
unify_variable(Arg, PermanentVariables, State, [var(Arg, unify, y(I))|State], [unify_variable(y(I))|Tail], Tail):-
        variable_is_known_permanent(Arg, PermanentVariables, y(I)), !.
unify_variable(Arg, _PermanentVariables, State, [var(Arg, unify, Xi)|S1], [unify_variable(Xi)|Tail], Tail):-
        !, fresh_variable(State, S1, Xi).

put_variable(Arg, Position, Source, PermanentVariables, State, S1, Opcodes, Tail):-
        already_used(Arg, State, Register, How),
        !,
        put_possibly_unsafe_value(How, PermanentVariables, Position, Register, Source, Opcodes, Arg, State, S1, Tail).
put_variable(Arg, _, Source, PermanentVariables, State, [var(Arg, put, y(I))|State], [put_variable(y(I), Source)|Tail], Tail):-
        variable_is_known_permanent(Arg, PermanentVariables, y(I)), !.
put_variable(Arg, _, Source, _PermanentVariables, State, [var(Arg, put, Xi)|S1], [put_variable(Xi, Source)|Tail], Tail):-
        !, fresh_variable(State, S1, Xi).

% We need unify_local_value(Vn) rather than unify_value(Vn) if:
%   the variable Vn has not been initialized in this clause with set variable or unify variable, nor, if Vn is temporary, with put variable
unify_possibly_local_variable(unify, Register, [unify_value(Register)|Tail], _, S, S, Tail):- !.
unify_possibly_local_variable(set, Register, [unify_value(Register)|Tail], _, S, S, Tail):- !.
unify_possibly_local_variable(put, x(I), [unify_value(x(I))|Tail], _, S, S, Tail):- !.
unify_possibly_local_variable(_, Register, [unify_local_value(Register)|Tail], Arg, S, S1, Tail):-
        mark_variable_as_safe(Arg, S, S1).

% I think an X register can never be unsafe. We get this with chain rules like foo:- bar(X,X).
% In this case, we have put_variable, put_value. put_unsafe_value is designed to avoid using data in an environment which has been discarded. This is not happening here.
put_possibly_unsafe_value(_, _, _, x(I), Source, [put_value(x(I), Source)|Tail], _, S, S, Tail).
put_possibly_unsafe_value(get, _, _, Register, Source, [put_value(Register, Source)|Tail], _, S, S, Tail).
put_possibly_unsafe_value(unify, _, _, Register, Source, [put_value(Register, Source)|Tail], _, S, S, Tail).
put_possibly_unsafe_value(put, PermanentVariables, Position, Register, Source, [put_value(Register, Source)|Tail], Arg, S, S, Tail):-
        variable_has_not_been_trimmed(Arg, Position, PermanentVariables), !.

put_possibly_unsafe_value(put, _, _, Register, Source, [put_unsafe_value(Register, Source)|Tail], _, S, S, Tail).

variable_has_not_been_trimmed(Arg, Position, [permanent_var(A, _, last_occurrence(L))|_]):- Arg == A, !, L > Position.
variable_has_not_been_trimmed(Arg, Position, [_|PermanentVariables]):- variable_has_not_been_trimmed(Arg, Position, PermanentVariables).

% Variables initialized via put are never safe from the perspective of put[_local]_variable
% If they were initialized via unify, that is another story.
% FIXME: What happens then if we have foo(A):- bar(A), baz(A). A is permanent but the GC requires us to put in the put_variable(Yn). Will this wreck things?
mark_variable_as_safe(Arg, [var(A, put, Register)|Tail], [var(A, put, Register)|Tail]):- Arg == A, !.
mark_variable_as_safe(Arg, [var(A, _, Register)|Tail], [var(A, unify, Register)|Tail]):- Arg == A, !.
mark_variable_as_safe(Arg, [Head|Tail], [Head|Tail1]):- mark_variable_as_safe(Arg, Tail, Tail1).

variable_is_known_permanent(Variable, [permanent_var(V, R, _)|_], R):- Variable == V, !.
variable_is_known_permanent(Variable, [_|Vars], R):- variable_is_known_permanent(Variable, Vars, R).

fresh_variable([next(I)|Tail], [next(II)|Tail], x(I)):- II is I+1, !.
fresh_variable([A|B], [A|C], R):- fresh_variable(B, C, R).

already_used(Arg, [var(A, How, Register)|_], Register, How):- A == Arg, !.
already_used(Arg, [_|A], Register, How):- already_used(Arg, A, Register, How).

% The first goal in the body must NOT resize the state, since it is effectively part of the head still!
resize_state(0, S, _, S):- !.
resize_state(_, [next(_)|T], I, [next(I)|T]):- !.
resize_state(P, [A|T], I, [A|T2]):- resize_state(P, T, I, T2).


trim_environment(_, [], [], EnvSize, EnvSize):- !.
trim_environment(P, [permanent_var(_, _, last_occurrence(C))|PermanentVars], P1, EnvSize, TrimmedEnvSize):-
        C =< P,
        !,
        E1 is EnvSize - 1,
        trim_environment(P, PermanentVars, P1, E1, TrimmedEnvSize).

trim_environment(P, [Var|PermanentVars], [Var|P1], EnvSize, TrimmedEnvSize):-
        !,
        trim_environment(P, PermanentVars, P1, EnvSize, TrimmedEnvSize).

compile_body(Body, PermanentVariables, EnvSize, State, S2, Opcodes, OpcodesTail):-
        compile_body_goals(Body, 0, depart, PermanentVariables, EnvSize, State, S2, Opcodes, OpcodesTail).

% LCO is either 'call' or 'depart' and governs whether we permit the last goal to do LCO or whether it must actually be a call as well.
compile_body_goals((Goal, Goals), Position, LCO, PermanentVariables, EnvSize, State, S2, Opcodes, OpcodesTail):-
        !,
        compile_goal(Goal, Position, call, PermanentVariables, EnvSize, State, S1, Opcodes, O1),
        PP is Position + 1,
        trim_environment(Position, PermanentVariables, RemainingPermanentVariables, EnvSize, TrimmedEnvSize),
        compile_body_goals(Goals, PP, LCO, RemainingPermanentVariables, TrimmedEnvSize, S1, S2, O1, OpcodesTail).

compile_body_goals(LastGoal, Position, LCO, PermanentVariables, EnvSize, State, S1, Opcodes, OpcodesTail):-
        compile_goal(LastGoal, Position, LCO, PermanentVariables, EnvSize, State, S1, Opcodes, OpcodesTail).

compile_goal(aux_head(Label, Variables), Position, LCO, PermanentVariables, EnvSize, State, S2, Opcodes, OpcodesTail):-
        !,
        list_length(Variables, Arity),
        resize_state(Position, State, Arity, S1),
        compile_body_args(Variables, Position, 0, PermanentVariables, S1, S2, Opcodes, O1),
        compile_aux_call(LCO, Arity, EnvSize, Label, O1, OpcodesTail).

% Note that get_top_choicepoint(n, Yn) must mark Yn as seen (similar to get_level).
compile_goal(get_top_choicepoint(N, B), _Position, _LCO, PermanentVariables, _EnvSize, State, [var(B, get, y(Register))|State], [get_choicepoint(N, y(Register))|Tail], Tail):-
        variable_is_known_permanent(B, PermanentVariables, y(Register)).


% If ! is the first goal but NOT a depart, it is a neck_cut.
compile_goal(goal(!), 0, call, _PermanentVariables, _EnvSize, State, State, [neck_cut|OpcodesTail], OpcodesTail):-
        !.
% If ! is the first goal AND depart, then this is basically a fact of the form head:- !.
compile_goal(goal(!), 0, depart, _PermanentVariables, _EnvSize, State, State, [neck_cut, proceed|OpcodesTail], OpcodesTail):-
        !.
% If ! is not the first goal, then it is a deep cut
compile_goal(!(Var), _Position, call, PermanentVariables, _EnvSize, State, State, [cut(y(Register))|OpcodesTail], OpcodesTail):-
        !,
        variable_must_be_known_permanent(Var, PermanentVariables, y(Register)).
% This case kind of wrecks LCO
compile_goal(!(Var), _Position, depart, PermanentVariables, _EnvSize, State, State, [cut(y(Register)), deallocate, proceed|OpcodesTail], OpcodesTail):-
        !,
        variable_must_be_known_permanent(Var, PermanentVariables, y(Register)).

compile_goal(goal(Goal), Position, LCO, PermanentVariables, EnvSize, State, S2, Opcodes, OpcodesTail):-
        !,
        Goal =.. [Functor|Args],
        list_length(Args, Arity),
        resize_state(Position, State, Arity, S1),
        compile_body_args(Args, Position, 0, PermanentVariables, S1, S2, Opcodes, O1),
        compile_predicate_call(LCO, EnvSize, Functor, Arity, O1, OpcodesTail).

% This is possible. For example, consider ((foo, bar), baz).
compile_goal((LHS, RHS), Position, LCO, PermanentVariables, EnvSize, State, S2, Opcodes, OpcodesTail):-
        !,
        compile_body_goals((LHS, RHS), Position, LCO, PermanentVariables, EnvSize, State, S2, Opcodes, OpcodesTail).

compile_goal(AnythingElse, _, _, _, _, _, _, _, _):-
        throw(wrong_type_of_functor(compile_goal, AnythingElse)).

variable_must_be_known_permanent(Var, PermanentVariables, Register):-
        variable_is_known_permanent(Var, PermanentVariables, Register), !.
variable_must_be_known_permanent(Var, PermanentVariables, _):-
        throw(missing_permanent_var(Var, PermanentVariables)).

compile_predicate_call(depart, EnvSize, Functor, Arity, O1, O2):-
        !,
        deallocate_environment(EnvSize, O1, [execute(Functor/Arity)|O2]).
compile_predicate_call(call, EnvSize, Functor, Arity, [call(Functor/Arity, EnvSize)|O2], O2).

compile_aux_call(depart, ArgCount, EnvSize, Label, O1, O2):-
        deallocate_environment(EnvSize, O1, [execute_aux(Label, ArgCount)|O2]).
compile_aux_call(call, ArgCount, EnvSize, Label, O1, O2):-
        O1 = [call_aux(Label, ArgCount, EnvSize)|O2].

compile_body_args([], _, _, _PermanentVariables, State, State, Tail, Tail):- !.
compile_body_args([Arg|Args], Position, I, PermanentVariables, S1, S3, Opcodes, Tail):-
        compile_body_arg(Arg, Position, x(I), PermanentVariables, S1, S2, Opcodes, O1),
        II is I+1,
        compile_body_args(Args, Position, II, PermanentVariables, S2, S3, O1, Tail).

compile_body_arg(Arg, _Position, Dest, _PermanentVariables, State, State, [put_constant(Arg, Dest)|Tail], Tail):-
        atom_or_empty_list(Arg), !.
compile_body_arg(Arg, _Position, Dest, _PermanentVariables, State, State, [put_integer(Arg, Dest)|Tail], Tail):-
        integer(Arg), !.
compile_body_arg(Arg, _Position, Dest, _PermanentVariables, State, State, [put_float(Arg, Dest)|Tail], Tail):-
        float(Arg), !.
compile_body_arg(Arg, Position, Dest, PermanentVariables, State, S1, Opcodes, Tail):-
        var(Arg), !, put_variable(Arg, Position, Dest, PermanentVariables, State, S1, Opcodes, Tail).
compile_body_arg([Head|Tail], Position, Dest, PermanentVariables, State, S1, Opcodes, OpcodesTail):-
        compile_body_unification([Head, Tail], Position, State, S1, PermanentVariables, Opcodes, [put_list(Dest)|R], R, OpcodesTail).

compile_body_arg(Arg, Position, Dest, PermanentVariables, State, S1, Opcodes, Tail):-
        Arg =.. [Functor|Args],
        list_length(Args, Arity),
        compile_body_unification(Args, Position, State, S1, PermanentVariables, Opcodes, [put_structure(Functor/Arity, Dest)|R], R, Tail).

compile_body_unification([], _, State, State, _PermanentVariables, Opcodes, Opcodes, R, R):- !.
compile_body_unification([Arg|Args], Position, State, S1, PermanentVariables, O, OT, [unify_constant(Arg)|R], RT):-
        atom_or_empty_list(Arg), !, compile_body_unification(Args, Position, State, S1, PermanentVariables, O, OT, R, RT).
compile_body_unification([Arg|Args], Position, State, S1, PermanentVariables, O, OT, [unify_integer(Arg)|R], RT):-
        integer(Arg), !, compile_body_unification(Args, Position, State, S1, PermanentVariables, O, OT, R, RT).
compile_body_unification([Arg|Args], Position, State, S2, PermanentVariables, O, OT, R, RT):-
        var(Arg), !,
        unify_variable(Arg, PermanentVariables, State, S1, R, R1),
        compile_body_unification(Args, Position, S1, S2, PermanentVariables, O, OT, R1, RT).
compile_body_unification([Arg|Args], Position, State, S3, PermanentVariables, O, OT, [unify_value(Xi)|R], RT):-
        fresh_variable(State, S1, Xi),
        compile_body_arg(Arg, Position, Xi, PermanentVariables, S1, S2, O, O1),
        compile_body_unification(Args, Position, S2, S3, PermanentVariables, O1, OT, R, RT).


% -------------------- Below is the assembler -----------------------------
% Assemble Opcodes into a state, beginning at memory address N
% The resulting bytes are emitted using emit_code(+Address, +Code)
assemble(Opcodes, N):-
        term_variables(Opcodes, Variables),
        writeln('*********************************a'),
        encode_opcodes_1(Opcodes, N, Labels, [], DanglingReferences, []),
        writeln('*********************************b'),
        % Now build the jump table between clauses
        compile_message(linking(Variables, Labels)),
        link(Labels, DanglingReferences),
        compile_message(linked).

link([], _):- !.
link([label(Label, Address)|Labels], References):-
        link_1(Label, Address, References),
        link(Labels, References).

link_1(_Label, _Address, []):- !.
link_1(Label, Address, [address_of(L, N)|References]):-
        Label == L, !,
        compile_message(emitting_address_1_of(L, Address, to(N))),
        emit_code(N, Address),
        link_1(Label, Address, References).
link_1(Label, Address, [aux_address_of(L, N)|References]):-
        Label == L, !,
        compile_message(emitting_aux_address_2_of(L, Address, to(N))),
        A is Address xor 0x80000000,
        emit_code(N, A),
        link_1(Label, Address, References).
link_1(Label, Address, [_|References]):-
        link_1(Label, Address, References).


emit_codes(_, []):- !.
emit_codes(N, [Code|Codes]):-
        emit_code(N, Code),
        NN is N+1,
        emit_codes(NN, Codes).

encode_register(y(N), [0, N|T], T).
encode_register(x(N), [1, N|T], T).


encode_opcodes_1([], _, L, L, D, D):- !.

encode_opcodes_1([aux_label(Label)|As], N, L, L2, D, D1):-
        !,
        add_clause_to_aux(Label, N, L, L1),
        compile_message(auxiliary(Label, N)),
        NN is N + 2,
        encode_opcodes_1(As, NN, L1, L2, D, D1).

encode_opcodes_1([call_aux(Label, Arity, Trim)|As], N, L, L1, [address_of(Label, Offset)|D], D1):-
        !,
        compile_message('    '(call_aux(Label, Arity, Trim, N))),
        Offset is N+1,
        emit_codes(N, [40]),
        NN is N+2,
        emit_codes(NN, [Arity, Trim]),
        compile_message(need_address_of(Label, at(Offset))),
        NNN is N+4,
        encode_opcodes_1(As, NNN, L, L1, D, D1).

encode_opcodes_1([execute_aux(Label, Arity)|As], N, L, L1, [address_of(Label, NN)|D], D1):-
        !,
        compile_message('    '(execute_aux(Label, Arity, N))),
        NN is N+1,
        emit_codes(N, [41]),
        N2 is N+2,
        emit_codes(N2, [Arity]),
        NNN is N+3,
        encode_opcodes_1(As, NNN, L, L1, D, D1).


encode_opcodes_1([try_me_else(Label)|As], N, L, L1, [address_of(Label, NN)|D], D1):-
        !,
        % We do not necessarily know what Label is. Reserve a byte and add it to the list of things to resolve once compilation has completed.
        compile_message(try_me_else(Label, N)),
        NN is N+1,
        emit_codes(N, [28]),
        NNN is N+2,
        encode_opcodes_1(As, NNN, L, L1, D, D1).

encode_opcodes_1([label(Label)|As], N, [label(Label, N)|L], L1, D, D1):-
        !,
        encode_opcodes_1(As, N, L, L1, D, D1).

encode_opcodes_1([A|As], N, L, L1, D, D1):-
        !,
        compile_message('    '(A, N)),
        encode_opcode(A, OpcodeSize, Codes),
        emit_codes(N, Codes),
        NN is N + OpcodeSize,
        encode_opcodes_1(As, NN, L, L1, D, D1).

% This is used ONLY for printing out partially-compiled instructions
encode_opcode(clause(_), 0, []).

/* Control instructions 1-5 */
encode_opcode(allocate, 1, [1]).
encode_opcode(deallocate, 1, [2]).
encode_opcode(call(Functor/Arity, N), 3, [3, I, N]):-
        lookup_functor(Functor, Arity, I).
encode_opcode(execute(Functor/Arity), 2, [4, I]):-
        lookup_functor(Functor, Arity, I).
encode_opcode(proceed, 1, [5]).

/* Put instructions 6-13 */
encode_opcode(put_variable(y(N), x(I)), 3, [6, N, I]).
encode_opcode(put_variable(y(N)), 2, [60, N]).
encode_opcode(put_variable(x(N), x(I)), 3, [7, N, I]).
encode_opcode(put_value(R, x(I)), 4, [8|S]):-
        encode_register(R, S, [I]).
encode_opcode(put_unsafe_value(y(N), x(I)), 3, [9, N, I]).
encode_opcode(put_unsafe_value(x(N), x(I)), 3, [9, N, I]):-
        throw(illegal_unsafe_value_register(x(N))).
encode_opcode(put_constant(C, x(I)), 3, [10, K, I]):-
        lookup_atom(C, K).
encode_opcode(put_nil(x(I)), 2, [11,I]).
encode_opcode(put_structure(Functor/Arity, x(I)), 3, [12, F, I]):-
        lookup_functor(Functor, Arity, F).
encode_opcode(put_list(x(I)), 2, [13, I]).
encode_opcode(put_integer(C, x(I)), 3, [14, C, I]).
encode_opcode(put_float(C, x(I)), 3, [51, N, I]):-
        lookup_float(C, N).

/* Get instructions 15-21 */
encode_opcode(get_variable(R, x(I)), 4, [15|S]):-
        encode_register(R, S, [I]).
encode_opcode(get_value(R, x(I)), 4, [16|S]):-
        encode_register(R, S, [I]).
encode_opcode(get_constant(C, x(I)), 3, [17, K, I]):-
        lookup_atom(C, K).
encode_opcode(get_nil(x(I)), 2, [18, I]).
encode_opcode(get_structure(Functor/Arity, x(I)), 3, [19, F, I]):-
        lookup_functor(Functor, Arity, F).
encode_opcode(get_list(x(I)), 2, [20, I]).
encode_opcode(get_integer(C, x(I)), 3, [21, C, I]).
encode_opcode(get_float(C, x(I)), 3, [50, N, I]):-
        lookup_float(C, N).

/* Unify instructions 22-27 */
encode_opcode(unify_void(N), 2, [22, N]).
encode_opcode(unify_variable(R), 3, [23|S]):-
        encode_register(R, S, []).
encode_opcode(unify_value(R), 3, [24|S]):-
        encode_register(R, S, []).
encode_opcode(unify_local_value(R), 3, [25|S]):-
        encode_register(R, S, []).
encode_opcode(unify_constant(C), 2, [26, K]):-
        lookup_atom(C, K).
encode_opcode(unify_integer(C), 2, [27, C]).
encode_opcode(unify_float(C), 2, [52, N]):-
        lookup_float(C, N).


/* Indexing instructions 28-30 */
encode_opcode(try_me_else(L), 2, [28, L]).
encode_opcode(retry_me_else(L), 2, [29, L]).
encode_opcode(trust_me, 2, [30, 0]).

/* Cut instructions */
encode_opcode(neck_cut, 1, [31]).
encode_opcode(cut(y(I)), 2, [32, I]).
encode_opcode(get_level(y(I)), 2, [33, I]).

/* Aux instructions. Used for ; and ->. Basically just call with an offset rather than a functor to look up*/
encode_opcode(call_aux(P, A, N), 4, [40, P, A, N]).
encode_opcode(execute_aux(P, A), 3, [41, P, A]).

/* retry_foreign is for foreign predicates with nondeterministic behaviour */
encode_opcode(retry_foreign, 1, [42]).

/* get_choicepoint is used for setup_call_cleanup */
encode_opcode(get_choicepoint(N, y(I)), 3, [43, N, I]).

encode_opcode(nop2, 2, [254, 0]).

%-------------------------- Next we have some utility predicates for bootstrapping ----------------------

compile_files([]):- !.
compile_files([File|Files]):-
        compile_file(File),
        !,
        compile_files(Files).


compile_file(Source):-
        open(Source, read, S),
        compile_stream(S),
        close(S).

compile_stream(Stream):-
        read_term(Stream, Term, []),
        compile_stream_term(Stream, Term).

compile_stream_term(_, end_of_file):- !.
compile_stream_term(Stream, Term):-
        compile_clause(Term),
        !,
        compile_stream(Stream).

compile_atom(Atom):-
        atom_to_memory_file(Atom, MemoryFile),
        open_memory_file(MemoryFile, read, Stream),
        compile_stream(Stream),
        close(Stream),
        free_memory_file(MemoryFile),
        writeln('Compiled atom').

save_clause(Head:-Body):-
        !,
        functor(Head, Name, Arity),
        add_clause_to_predicate(Name/Arity, Head, Body).

save_clause(Fact):-
        !,
        functor(Fact, Name, Arity),
        add_clause_to_predicate(Name/Arity, Fact, true).



%-------------------------- Finally we have a crude toplevel ----------------------
% swipl -f wam_compiler.pl -t "make, bootstrap('demo.pl', call_test), halt" && /System/Library/Frameworks/JavaScriptCore.framework/Versions/A/Resources/jsc foreign.js wam.js bootstrap.js read.js -e "demo(false)"
print_bindings([]):- writeln('true.'), !.
print_bindings(Vars):-
        print_bindings_1(Vars).
print_bindings_1([]):- !.
print_bindings_1([Name=Value|Bindings]):-
        writeln(Name=Value),
        print_bindings_1(Bindings).

repl(Atom):-
        repl_1(Atom),
        true.

repl_1(Atom):-
        atom_to_term(Atom, Query, Bindings),
        call(Query),
        flush_stdout,
        print_bindings(Bindings).
