options(F) --> option, !, options(F).
options(F) --> [F], !, options(_).
options(_) --> [].

option --> ['-Decho'], !, { assert(echo) }.

option --> ['-eness'], !, { assert(ness) }.

option --> ['-t', Type ], !, { retract(type(_)),
			       assert(type(Type)) }.

option --> ['-o', Type ], !, { retract(outtype(_)),
			       assert(outtype(Type)) }.


runtime_entry(start) :-
    unix(argv(CmdLine)),
    assert(type(fd)),    % default
    assert(outtype(fd)), % default
    options(File, CmdLine, []),
    multiplex_input(File, PLA0)
		   type(Type),
    compute_other(Type, PLA0, PLA1),
    lexpress(_-PLA1, costs(_,_,_,Cost):PLAMin),
    write('Size of Reduced PLA'(Cost)),nl,
    change_suffix(File,'.po', Outfile),
    multiplex_output(OutFile, PLAMin).


