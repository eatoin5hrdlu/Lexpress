lexpress --> unwrap,
	     complement,
	     init_cost,
	     expand,
	     essential_primes,
	     iterate,
	     add_to_care,
	     sub_from_dont_care,
	     make_sparse.

iterate --> irredundant,
	    (cost_changed(1) -> reduction ; out).
reduction --> reduce,
	    (cost_changed(2) -> expansion ; out).
expansion --> expand,
	    (cost_changed(3) -> iterate ; out).

out -->     (cost_changed(1) -> last_gasp ; true).

last_gasp --> reduce2,
	    (cost_changed(4) -> init_cost, iterate ; true).
	      


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

double(0, B, R) :- single(B, R).
double(-1,B, R) :- single(B, R).

binateness([], _, _, NPos,    _, R) :- NPos < 1, !.
binateness([], _, _,    _, NNeg, 0) :- NNeg < 1, !.
binateness([], _, _, NPos, NNeg, R) :- R is NPos + NNeg.

binateness([C|Cs], _, _, NPos, NNeg, 0) :-
    ( memberchk(Pos, C)
     -> NNPos is NPos + 1,
	binateness(Cs, Pos, Neg, NNPos, NNeg, R)
     ; memberchk(Neg, C)
       -> NNNeg is NNeg + 1,
	  binateness(Cs, Pos, Neg, MPos, NNNeg, R)
     ; binateness(Cs, Pos, Neg, NPos, NNeg, R)
    ).		 


% Complementation

complement(C-pla(F, _, D, E), C-pla(F,R,D,E)) :-
    complement_cover(F, R).


complement_cover(Cover, Comp) :-
    unate(Cover),
    !,
    unate_complement(Cover, Comp).

complement_cover(Cover, Comp) :-
    most_binate(Cover, Var),
    cofactors(Cover, Var, C0, C1),
    complement_cover(C0, Comp0),
    complement_cover(C1, Comp1),
    merge_complement(Comp0, Comp1, Var, Comp).

% Unate Complementation

unate_complement(Cover, Comp) :-
    special_case(Cover, Comp),
    !.

unate_complement(Cover, Comp) :-
    ucomp_select(Cover, V),
    cofactors(Cover, V, C0, C1),
    unate_complement(C0, Comp0),
    unate_complement(C1, Comp1),
    merge_complement(Comp0, Comp1, Comp).

% ucomp_select(+Cover, -Var)
ucomp_select(Cover, Var) :-
    longest(Cover, 0, [], Cube),
    most_numerous(Cube, Cover, 0, 0, Var).

longest([], _, Cube, Cube).
longest([C|Cs], Lsf, Csf, Out) :-
    length(C,CLen),
    ( CLen > Lsf
     -> longest(Cs, CLen, C, Out)
     ;  longest(Cs, Lsf, Csf, Out)
    ).
	       

most_numerous([], _, _, N, N).
most_numerous([V|Vs],Cover, N0, V0, Var) :-
    occurances(Cover, V, N),
    (N > N0
     -> most_numerous(Vs, Cover, N, V, Var)
     ;  most_numerous(Vs, Cover, N0, V0, Var)
    ).


occurrences([],     _, N, N).
occurrences([C|Cs], V, I, O) :-
    ( memberchk(V, C)
     -> N is I+1,
	occurrences(Cs, V, N, O)
     ;  occurrences(Cs, V, I, O)
    ).
		   
% Personality Matrix
pers_cofactor([], J, [J], []).
pers_cofactor([C|Cs], J, O, I) :-
    ( C > J -> O = [J,C|Cs], I = [C|Cs]
     ; C =:= J  -> O = Cs, I = [C|Cs]
     ; O = [C|Os], I = [C|Cs],
       pers_cofactor(Cs, J, Os, Is)
    ).

unate_comp(F, R) :-
    personality(F, M, V),
    monotone(F, V),
    comp_pers(M, MComp),
    translate(MComp, V, R).

personality([], [], _).
personality([C|Cs], [M|Ms], V) :-
    pers_cube(C, M, V),
    personality(Cs, Ms, V).

pers_cube([], [], []).
pers_cube([C|Cs], [M|Ms], [V|Vs]) :-
    ( C/\1 =:= 1 -> V = '+' ; V = '-'),
    M is C>>1,
    pers_cube(Cs, Ms, Vs).

% Personality Matrix Unate Complementation
comp_pers(M, []) :-       % taut -> empty
    memberchk([], M),
    !.
comp_pers([], [[]]) :- !. % empty -> taut
comp_pers([T], M)   :- !, demorgan(T, M).
comp_pers(M, Mbar) :-
    ucomp_select(M, J),
    pers_cofactor(M, J, M0, M1),
    comp_pers(M0, M0bar),
    comp_pers(M1, M1bar),
    merge(M0bar, M1bar, Mbar).


demorgan([], []).
demorgan([X|Xs], [[NX]|T]) :-
    ( X /\ 1 =:= 0
     -> NX is X \/ 1
     ; NX is X /\ -2
    ),
    demorgan(Xs, T).


% Intersection and Union of Cubes

intersect([], Bs, Bs) :- !.
intersect(As, [], As) :- !.
intersect([A|As], [B|Bs], Xs) :-
    ( A << 1 > B<<1 ->
        Xs = [B|X1s],
	intersect([A|As], Bs, X1s)
      ; A<<1 < B<<1 ->
	  Xs = [A|X1s],
	  intersect(As, [B|Bs], X1s)
      ; A =:= B ->	     
	  Xs = [A|X1s],
	  intersect(As, Bs, X1s)
    ).


cube_intersect([], [], []).
cube_intersect([X|Xs], [Y|Ys], [I|Is]) :-
   intersect(X, Y, I),
   cube_intersect(Xs, Ys, Is).

cover_intersect([], [], []).
cover_intersect([C|Cs], [D|Ds], [I|Is]) :-
    cube_intersect(C, D, I),
    !, 
    cover_intersect(Cs, Ds, Is).
cover_intersect([_|Cs], [_|Ds], [_|Is]) :-
    cover_intersect(Cs, Ds, Is).

cover_union(Cs, Ds, Union) :-
    append(Cs, Ds, Union).

add_to_care(C-pla(F0,R,D,E), C-pla(F1,R,D,E)) :-
    append(F0, E, F1).

% Cube Distance
% The distance between two cubes c and d is equal to the number
% of input conflicts, i.e. of input cube entries that have
% null intersection, plus 1 if the intersection of the output
% parts gives and output part of all 3's (don't cares).

distance(C, D, Distance) :-
    distance(C, D, Din, Dout),
    Distance is Din + Dout.

distance(c(Cin,Cout), c(Din,Dout), In, Out) :-
    distance(Cin, Din, 0, In),
    ( cube_intersect(Cout, Dout, [])
     -> Out = 0
     ;  Out = 1
    ).

distance1([], [], I, I).
distance1([C|Cs], [D|Ds], In, Out) :-
    ( C =:= D
     -> Next = In
     ;  Next = In + 1
    ),
    distance1(Cs, Ds, Next, Out).

% Cube Consensus

consensus(C, D, Consensus) :-
    distance(C, D, In, Out),
    ( In + Out =:= 0 ->
	  cube_intersect(C, D, Consensus)
     ; In =:= 1, Out =:= 0 ->
	   raised_intersection(C, D, Consensus)
     ; In =:= 0, Out =:= 1 ->
	   lower_outputs(C, D, Consensus)
    ).

consensus1(0,0) :- !, cube_intersect(C, D, Consensus).
consensus1(0,1) :-    lower_outputs(C, D, Consensus).
consensus1(1,0) :-    raised_intersection(C, D, Consensus).

% Raising and Lowering

raised_intersect(c(Ci,Co), c(Di, Do), c(Ri, Ro)) :-
    raised_intersect1(Ci, Di, Ri),
    raised_intersect1(Co, Do, Ro).

raised_intersect1([], _, []) :- !.
raised_intersect1(Cs,[], []) :- !.
raised_intersect1([C|Cs],[D|Ds], Xs) :-
    (C =:= D ->
	 Xs = [C|X1s],
	 raised_intersect(Cs, Ds, X1s)
     ; raised_intersect1(Cs, Ds, Xs)
    ).

lower_intersect1([], Ds, Ds) :- !.
lower_intersect1(Cs, [], Cs) :- !.
lower_intersect1([C|Cs],[D|Ds], [L|Ls]) :-
    (C =:= D ->
	 L = C,
	 lower_intersect(Cs, Ds, Ls)
     ; C < D ->
	 L = C,
         lower_intersect1(Cs, [D|Ds], Ls)
     ; L = D,
       lower_intersect1([C|Cs], Ds, Ls)
    ).


% Constant Column Generator

constant_colums(Cover, Cols) :-
    findall(Col, constant(Cover,Col), Cols).

constant([], _).
constant([C|Cs],Col) :-
    member(Col, C),
    constant(Cs, Col).
