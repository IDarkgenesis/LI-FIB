concat([],L,L).
concat([X|L1],L2,[X|L3]):- concat(L1,L2,L3).

last(X,L):- concat(_,[X],L).

inv([],[]).
inv([X|L1],LR):- concat(L2,[X],LR), inv(L2,L1).
