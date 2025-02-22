numCursos(4).
numAssignatures(23).
numAules(3).
numProfes(5).

% Sintaxi: assig(curs,assignatura,hores,llistaAules,llistaProfessors).
assig(1,1,3,[3],[2,3,4,5]).
assig(1,2,2,[2,3],[1,2,3,4,5]).
assig(1,3,4,[2,3],[1,2,3,4,5]).
assig(1,4,2,[2,3],[2,3,4,5]).
assig(1,5,2,[1,2,3],[1,5]).

assig(2,6,3,[1,3],[1,4,5]).
assig(2,7,4,[1,2,3],[1,2,3,4,5]).
assig(2,8,2,[1,2,3],[5]).
assig(2,9,3,[1,2,3],[1,2,5]).
assig(2,10,4,[1,3],[4,5]).

assig(3,11,2,[1],[3,4]).
assig(3,12,2,[2],[2,3,4,5]).
assig(3,13,3,[1,2,3],[1,2,3,5]).
assig(3,14,2,[1,2,3],[1,2,3,4,5]).
assig(3,15,2,[1],[2,3,4,5]).
assig(3,16,3,[1],[1]).

assig(4,17,4,[2,3],[5]).
assig(4,18,3,[1],[1,2,4,5]).
assig(4,19,2,[1,2,3],[1,4]).
assig(4,20,2,[1,2,3],[1,2,3]).
assig(4,21,3,[1,2,3],[1,3,5]).
assig(4,22,4,[1],[2,4]).
assig(4,23,2,[1,2,3],[4]).

% Sintaxi: horesProhibides(professor,llistaHores).
horesProhibides(1,[1,10,11,12,17,21,24,27,43,49]).
horesProhibides(2,[4,5,8,9,12,18,19,28,38,46,49,51,53,55,60]).
horesProhibides(3,[2,3,4,7,8,9,11,16,21,25,26,33,37,40,45,52,53,55,57]).
horesProhibides(4,[1,2,9,10,20,23,25,26,29,31,32,34,37,40,42,44,45,47,48,49,50,51,52,53,57,58,59]).
horesProhibides(5,[3,4,8,9,15,24,25,30,32,33,38,39,43,45,46,49,51,52,58]).

