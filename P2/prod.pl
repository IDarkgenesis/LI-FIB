prod([],P):- P is 1.
prod([X|XS], P):- prod(XS,A), P is X*A.

