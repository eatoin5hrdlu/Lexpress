
init_cost(_-PLA, costs(C,C,C,C)-PLA) :-
    compute_cost(PLA,C).

compute_cost(pla(F,_,_,_), cost(NP,NI,NO)) :-
    sum_costs(F, 0, NP, 0, NI, 0, NO).

sum_costs([], P, P, I, I, O, O).
sum_costs([c(In,Out)|Cs], P0, P, I0, I, O0, O) :-
    P1 is P0 + 1,
    length(In, LIin), I1 is LIn + I0,
    length(Out, LOut), O1 is LOut + O0,
    sum_costs(Cs, P1, P, I1, I, O1, O).

cost_changed(N, CostV-PLA, NCostV-PLA) :-
    compute_cost(PLA, Cost),
    \+ arg(N, CostV, Cost),
    change_arg(N, CostV, _, Cost, NCostV).


co_cover([],_,[]).
co_cover([C|Cs], F, [X,Xs]) :-
    cofactor(C,F,X),
    !,
    co_cover(Cs,F,Xs).
co_cover([_|Cs], F, Xs) :-
    co_cover(Cs, F, Xs).

cofactor([], _, []).
cofactor([C+|Cs], F, Xs) :-
    ( C=:= F -> Xs = Cs
    ; C>>1 > F>>1 -> Xs = [C|Cs]
    ; C>>1 < F>>1 -> Xs = [C|X1s],
		     cofactor(Cs, F, X1s)
    ).
			       
% Positive and Negative Co-Factors

cofactors(Cover, Var, C1, C0) :-
    V1 is Var<<1 \/ 1,
    V0 is Var<<1 \/ 0,
    co_cover(Cover, V1, C1),
    co_cover(Cover, V0, C0).

% General Co-Factor Computation

		      
gen_cofactor([], _, []) :- !.
gen_cofactor(_, [], []) :- !.
gen_cofactor([C|Cs], [F|Fs], Xs) :-
    ( C>>1 > F>>1 ->
	  evaluate(default, F, X),
	  Xs = [X|Xs1],
	  gen_cofactor(Cs, F, X1s)
     ; C>>1 < F>>1 ->
	   Xs = [C|X1s],
	   gen_cofactor(Cs, F, X1s)
     ; evaluate(C,F,X) ->
	   Xs = [X|X1s],
	   gen_cofactor(Cs, F, X1s)
     ; gen_cofactor(Cs, Fs, Xs)
     ).

% Recursive Unate Decomposition
% most_binate(+Cover, -Var)

most_binate(Cover, Var) :-
    setof(V, variable(Cover, V), Vars),
    most_binate(Vars, Cover, -1, -1, Var).

variable(Cover, Var) :-
    member(C, Cover),
    member(V, C),
    Var is V>>1.

most_binate([], _, _, Var, Var).
most_binate([V|Vs], Cover, Bsf, Vsf, Var) :-
    Pos is   V<<1 \/ 1,
    Neg is   V<<1 \/ 0,
    binateness(Cover, Pos, Neg, 0, 0, NB),
    ( NB > Bsf
     -> most_binate(Vs, Cover, NB,    V, Var)
     ;	most_binate(Vs, Cover, Bsf, Vsf, Var)
    ).		     

    
    
