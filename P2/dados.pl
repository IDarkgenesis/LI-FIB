dados(0,0,[]).
dados(P,N,[X|L]):-
	N > 0,
	member(X,[1,2,3,4,5,6]),
	REM is P - X,
	N1 is N - 1, dados(REM,N1,L).
