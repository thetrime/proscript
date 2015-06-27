%-------------------------------------- SWI-Only --------------------
:-dynamic(ftable/2). % functors
:-dynamic(atable/2). % atoms
:-dynamic(ptable/2). % predicates
:-dynamic(fptable/2). % foreign predicates

lookup_functor(Functor/Arity, N):-
        lookup_atom(Functor, F),
        ( ftable(F/Arity, N)->
            true
        ; otherwise->
            flag(ftable, N, N+1),
            assert(ftable(F/Arity, N))
        ).

lookup_atom(Atom, N):-
        ( atable(Atom, N)->
            true
        ; otherwise->
            flag(atable, N, N+1),
            assert(atable(Atom, N))
        ).

add_predicate(Predicate, N):-
        assert(ptable(Predicate, N)).

quote_atom_for_javascript(Atom, QuotedAtom):-
        atom_codes(Atom, Codes),
        quote_atom_for_javascript_1(QuotedCodes, Codes, []),
        atom_codes(QuotedAtom, QuotedCodes).

quote_atom_for_javascript_1([34|Codes])-->
        quote_atom_for_javascript_2(Codes).

quote_atom_for_javascript_2([92, 110|Codes])-->
        "\n", !,
        quote_atom_for_javascript_2(Codes).

quote_atom_for_javascript_2([92, 34|Codes])-->
        [34], !, % '
        quote_atom_for_javascript_2(Codes).

quote_atom_for_javascript_2([Code|Codes])-->
        [Code], 
        quote_atom_for_javascript_2(Codes).

quote_atom_for_javascript_2([34], [], []):- !.


dump_tables(S):-
        ( setof(N-Atom, atable(Atom, N), Atoms)-> true ; otherwise-> Atoms = []),
        findall(QuotedAtom, 
                ( member(_-Atom, Atoms),
                  quote_atom_for_javascript(Atom, QuotedAtom)
                ),
                SortedAtoms),
        atomic_list_concat(SortedAtoms, ', ', AtomAtom),
        format(S, 'atable = [~w];~n', [AtomAtom]),
        ( setof(N-F, ftable(F, N), Functors)-> true ; otherwise-> Functors = []),
        findall(Functor, (member(_-F/A, Functors),
                          format(atom(Functor), '[~w,~w]', [F, A])),
                SortedFunctors),
        atomic_list_concat(SortedFunctors, ', ', FunctorAtom),
        format(S, 'ftable = [~w];~n', [FunctorAtom]),
        findall(PredicateAtom,
                ( ptable(Predicate, N),
                  format(atom(PredicateAtom), '~w: ~w', [Predicate, N])
                ),
                Predicates),
        atomic_list_concat(Predicates, ', ', PredicatesAtom),
        format(S, 'predicates = {~w};~n', [PredicatesAtom]),
        findall(PredicateAtom,
                ( fptable(Predicate, Symbol),
                  format(atom(PredicateAtom), '~w: ~w', [Predicate, Symbol])
                ),
                FPredicates),
        atomic_list_concat(FPredicates, ', ', FPredicatesAtom),
        format(S, 'foreign_predicates = {~w};~n', [FPredicatesAtom]).        


reserve_predicate(Functor, Foreign):-
        lookup_functor(Functor, F),
        assert(fptable(F, Foreign)).
        

reset:-
        retractall(ptable(_,_)),        
        retractall(atable(_,_)),
        retractall(ftable(_,_)),
        retractall(fptable(_,_)),
        % [] is always 0
        assert(atable([], 0)),

        flag(ftable, _, 0),
        flag(atable, _, 1),

        % Then add in some reserved predicates
        reserve_predicate(is/2, predicate_is),
        %reserve_predicate((>)/2, predicate_gt),
        %reserve_predicate((<)/2, predicate_lt),
        reserve_predicate(fail/0, predicate_fail),
        reserve_predicate(true/0, predicate_true),
        %reserve_predicate((=:=)/2, predicate_numeq),
        reserve_predicate(!/0, predicate_cut),
        reserve_predicate(term_variables/2, term_variables),
        reserve_predicate(writeln/1, writeln),
        reserve_predicate((=)/2, predicate_unify),
        reserve_predicate(halt/0, halt),
        reserve_predicate((=..)/2, univ),
        reserve_predicate((==)/2, predicate_match),
        reserve_predicate(functor/3, functor),
        reserve_predicate(var/1, predicate_var),
        reserve_predicate(atom/1, predicate_atom),
        reserve_predicate(integer/1, predicate_integer),
        
        % The big guns!
        reserve_predicate(atom_to_memory_file/2, atom_to_memory_file),
        reserve_predicate(open_memory_file/3, open_memory_file),
        reserve_predicate(read_term/3, read_term),
        reserve_predicate(close/1, predicate_close),
        reserve_predicate(free_memory_file/1, free_memory_file),
        true.
        

               
%---------------------------------------------------------------------

