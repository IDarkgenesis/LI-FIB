intersec([],_,[]).
intersec([X|L1],L2,[X|LR]):- member(X,L2),!,intersec(L1,L2,LR). 
    %Posar ! per eliminar recursivitat posible en cas de que falli algo
intersec([_|L1],L2 ,L3):- intersec(L1,L2,L3). %Cas en que X no es de L2


union([],L2,L2).
union([X|L1],L2,L3):- member(X,L2),!,union(L1,L2,L3).
union([X|L1],L2,[X|L3]):- union(L1,L2,L3).
