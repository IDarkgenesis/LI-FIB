pert_con_resto(X,L,R) :- append(L1,[X|L2],L), append(L1,L2,R).  

sumall([],0).
sumall([X|L1],S):- sumall(L1,S1), S is X + S1.

suma_demas(L):- per t_con_resto(X,L,R), sumall(R,X),!.

suma_ant(L):- append(L1,[X|_],L), suma(L1,X), !.
