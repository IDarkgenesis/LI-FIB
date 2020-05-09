symbolicOutput(0).  % set to 1 to see symbolic output only; 0 otherwise.

% ELEMENTS PREDEFINITS

numEquipos(16).
nofuera(7,10).
nofuera(6,10).
nofuera(9,10).
nofuera(10,10).
nofuera(11,10).
nofuera(7,30).
nofuera(6,30).
nofuera(9,30).
nofuera(10,30).
nofuera(11,30).
nocasa(7,1).
nocasa(8,1).
nocasa(9,1).
nocasa(10,1).
nocasa(11,1).
nocasa(12,1).
norepes(1,2).
norepes(2,3).
norepes(28,29).
norepes(29,30).
nopartido(1,2,30).
nopartido(1,2,1).
nopartido(1,2,2).
nopartido(1,2,3).
nopartido(1,2,4).
nopartido(1,2,5).
nopartido(1,2,6).
nopartido(1,2,7).
sipartido(2,3,30).
sipartido(4,5,30).

%%%%%% Some helpful definitions to make the code cleaner:
equipo(N):- numEquipos(K), between(1,K,N).
jornada(J):- between(1,38,J).
vuelta(V):- between(1,2,V).
%%%%%%  1. SAT Variables:

satVariable( partido(J,L,V) ):- equipo(L), equipo(V), jornada(J).

%%%%%%  2. Clause generation:

writeClauses:-
    eachJornadaOnceTeam,
    partidoCasa,
    partidoVis,
    nojugarPartido,
    sijugarPartido,
    noRepeticionsLoc,
    noRepeticionsVis,
    %noRepeticions,
    true,!.

writeClauses:- told, nl, write('writeClauses failed!'), nl,nl, halt.

% A cada jornada no hi pot haver un equip repetit
eachJornadaOnceTeam:- jornada(J), equipo(E), 
    findall( partido(J,E,V), (equipo(V), dif(E,V)), Lits), 
    findall( partido(J,L,E), (equipo(L), dif(E,L)), Lits2), 
    append(Lits,Lits2,Res), 
    exactly(1,Res),
    fail.
eachJornadaOnceTeam.

% Hi ha equips que en la jornada J volen jugar a casa
partidoCasa:- 
    jornada(J), nofuera(E,J), 
    findall( partido(J,L,E), 
    equipo(L), Lits), 
    atMost(0,Lits),
    fail.
partidoCasa.

% Hi ha equips que en la jornada J volen jugar de visitant
partidoVis:- 
    jornada(J), nocasa(E,J), 
    findall( partido(J,E,V), 
    equipo(V),Lits), 
    atMost(0,Lits),
    fail.
partidoVis.

% Hi ha partits que no es volen dur a terme
nojugarPartido:-
    jornada(J), nopartido(L,V,J),
    writeClause([-partido(J,L,V)]),
    writeClause([-partido(J,V,L)]),
    fail.
nojugarPartido.


% Hi ha partits que es volen dur a terme
sijugarPartido:-
    jornada(J), sipartido(L,V,J),
    writeClause([partido(J,L,V)]),
    fail.
sijugarPartido.

noRepeticionsLoc:- 
    jornada(J1), norepes(J1,J2), equipo(E),
    findall( partido(J1,E,V), (equipo(V),dif(E,V)), Lits1 ), 
    findall( partido(J2,E,V), (equipo(V),dif(E,V)), Lits2 ), 
    append(Lits1,Lits2,Lits), 
    exactly(1,Lits), 
    fail.
noRepeticionsLoc.

noRepeticionsVis:- 
    jornada(J1), norepes(J1,J2), equipo(E), 
    findall( partido(J1,V,E), (equipo(V),dif(E,V)), Lits1 ), 
    findall( partido(J2,V,E), (equipo(V),dif(E,V)), Lits2), 
    append(Lits1,Lits2,Lits), 
    exactly(1,Lits), 
    fail.
noRepeticionsVis.

noRepeticions:- 
    equipo(E), 
    findall(partido(J,E,V), (equipo(V),jornada(J),dif(E,V)),Lits), 
    exactly(1,Lits),
    fail.
noRepeticions.



%%%%%%  3. DisplaySol: show the solution. Here M contains the literals that are true in the model:

displaySol(M):- nl,jornada(J),equipo(L),equipo(V), member( partido(J,L,V), M),write(J),write(' '),write(L),write(' '),write(V),nl, fail.
displaySol(_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Everything below is given as a standard library, reusable for solving 
%    with SAT many different problems.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Express that Var is equivalent to the disjunction of Lits:
expressOr( Var, Lits) :- symbolicOutput(1), write( Var ), write(' <--> or('), write(Lits), write(')'), nl, !. 
expressOr( Var, Lits ):- member(Lit,Lits), negate(Lit,NLit), writeClause([ NLit, Var ]), fail.
expressOr( Var, Lits ):- negate(Var,NVar), writeClause([ NVar | Lits ]),!.

% Express that Var is equivalent to the conjunction of Lits:
expressAnd( Var, Lits) :- symbolicOutput(1), write( Var ), write(' <--> and('), write(Lits), write(')'), nl, !. 
expressAnd( Var, Lits):- member(Lit,Lits), negate(Var,NVar), writeClause([ NVar, Lit ]), fail.
expressAnd( Var, Lits):- findall(NLit, (member(Lit,Lits), negate(Lit,NLit)), NLits), writeClause([ Var | NLits]), !.


%%%%%% Cardinality constraints on arbitrary sets of literals Lits:

exactly(K,Lits):- symbolicOutput(1), write( exactly(K,Lits) ), nl, !.
exactly(K,Lits):- atLeast(K,Lits), atMost(K,Lits),!.

atMost(K,Lits):- symbolicOutput(1), write( atMost(K,Lits) ), nl, !.
atMost(K,Lits):-   % l1+...+ln <= k:  in all subsets of size k+1, at least one is false:
	negateAll(Lits,NLits),
	K1 is K+1,    subsetOfSize(K1,NLits,Clause), writeClause(Clause),fail.
atMost(_,_).

atLeast(K,Lits):- symbolicOutput(1), write( atLeast(K,Lits) ), nl, !.
atLeast(K,Lits):-  % l1+...+ln >= k: in all subsets of size n-k+1, at least one is true:
	length(Lits,N),
	K1 is N-K+1,  subsetOfSize(K1, Lits,Clause), writeClause(Clause),fail.
atLeast(_,_).

negateAll( [], [] ).
negateAll( [Lit|Lits], [NLit|NLits] ):- negate(Lit,NLit), negateAll( Lits, NLits ),!.

negate( -Var,  Var):-!.
negate(  Var, -Var):-!.

subsetOfSize(0,_,[]):-!.
subsetOfSize(N,[X|L],[X|S]):- N1 is N-1, length(L,Leng), Leng>=N1, subsetOfSize(N1,L,S).
subsetOfSize(N,[_|L],   S ):-            length(L,Leng), Leng>=N,  subsetOfSize( N,L,S).


%%%%%% main:

main:-  symbolicOutput(1), !, writeClauses, halt.   % print the clauses in symbolic form and halt
main:-  initClauseGeneration,
tell(clauses), writeClauses, told,          % generate the (numeric) SAT clauses and call the solver
tell(header),  writeHeader,  told,
numVars(N), numClauses(C),
write('Generated '), write(C), write(' clauses over '), write(N), write(' variables. '),nl,
shell('cat header clauses > infile.cnf',_),
write('Calling solver....'), nl,
shell('picosat -v -o model infile.cnf', Result),  % if sat: Result=10; if unsat: Result=20.
	treatResult(Result),!.

treatResult(20):- write('Unsatisfiable'), nl, halt.
treatResult(10):- write('Solution found: '), nl, see(model), symbolicModel(M), seen, displaySol(M), nl,nl,halt.
treatResult( _):- write('cnf input error. Wrote anything strange in your cnf?'), nl,nl, halt.
    

initClauseGeneration:-  %initialize all info about variables and clauses:
	retractall(numClauses(   _)),
	retractall(numVars(      _)),
	retractall(varNumber(_,_,_)),
	assert(numClauses( 0 )),
	assert(numVars(    0 )),     !.

writeClause([]):- symbolicOutput(1),!, nl.
writeClause([]):- countClause, write(0), nl.
writeClause([Lit|C]):- w(Lit), writeClause(C),!.
w(-Var):- symbolicOutput(1), satVariable(Var), write(-Var), write(' '),!. 
w( Var):- symbolicOutput(1), satVariable(Var), write( Var), write(' '),!. 
w(-Var):- satVariable(Var),  var2num(Var,N),   write(-), write(N), write(' '),!.
w( Var):- satVariable(Var),  var2num(Var,N),             write(N), write(' '),!.
w( Lit):- told, write('ERROR: generating clause with undeclared variable in literal '), write(Lit), nl,nl, halt.


% given the symbolic variable V, find its variable number N in the SAT solver:
:-dynamic(varNumber / 3).
var2num(V,N):- hash_term(V,Key), existsOrCreate(V,Key,N),!.
existsOrCreate(V,Key,N):- varNumber(Key,V,N),!.                            % V already existed with num N
existsOrCreate(V,Key,N):- newVarNumber(N), assert(varNumber(Key,V,N)), !.  % otherwise, introduce new N for V

writeHeader:- numVars(N),numClauses(C), write('p cnf '),write(N), write(' '),write(C),nl.

countClause:-     retract( numClauses(N0) ), N is N0+1, assert( numClauses(N) ),!.
newVarNumber(N):- retract( numVars(   N0) ), N is N0+1, assert(    numVars(N) ),!.

% Getting the symbolic model M from the output file:
symbolicModel(M):- get_code(Char), readWord(Char,W), symbolicModel(M1), addIfPositiveInt(W,M1,M),!.
symbolicModel([]).
addIfPositiveInt(W,L,[Var|L]):- W = [C|_], between(48,57,C), number_codes(N,W), N>0, varNumber(_,Var,N),!.
addIfPositiveInt(_,L,L).
readWord( 99,W):- repeat, get_code(Ch), member(Ch,[-1,10]), !, get_code(Ch1), readWord(Ch1,W),!. % skip line starting w/ c
readWord(115,W):- repeat, get_code(Ch), member(Ch,[-1,10]), !, get_code(Ch1), readWord(Ch1,W),!. % skip line starting w/ s
readWord(-1,_):-!, fail. %end of file
readWord(C,[]):- member(C,[10,32]), !. % newline or white space marks end of word
readWord(Char,[Char|W]):- get_code(Char1), readWord(Char1,W), !.
%========================================================================================
