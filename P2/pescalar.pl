pescalar([X],[Y],P):- P is X*Y.
pescalar([X|XS],[Y|YS],P):- pescalar(XS,YS,A), P is X*Y+A. 
