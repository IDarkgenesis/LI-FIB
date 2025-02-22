numCursos(4).
numAssignatures(23).
numAules(3).
numProfes(5).

% Sintaxi: assig(curs,assignatura,hores,llistaAules,llistaProfessors).
assig(1,1,4,[1,2,3],[1,2,3,4,5]).
assig(1,2,2,[2],[3,4]).
assig(1,3,2,[1,3],[1,3,4]).
assig(1,4,2,[1,3],[1,2,3,4,5]).
assig(1,5,3,[2],[1,3]).

assig(2,6,4,[3],[2]).
assig(2,7,2,[1,3],[4]).
assig(2,8,3,[1,2,3],[2,3,4,5]).
assig(2,9,3,[1,3],[1,2,3,4,5]).
assig(2,10,4,[2],[1,2,3,5]).

assig(3,11,2,[1,2,3],[1,4]).
assig(3,12,3,[2,3],[1,2,3,4]).
assig(3,13,4,[2],[2,5]).
assig(3,14,3,[1],[1,2,3,4]).
assig(3,15,2,[1,2,3],[1,2,4,5]).
assig(3,16,4,[2],[1,3]).

assig(4,17,4,[1,2,3],[2]).
assig(4,18,2,[1,3],[2]).
assig(4,19,2,[1,3],[1,3]).
assig(4,20,4,[1,2,3],[2,3,4,5]).
assig(4,21,3,[1,2,3],[1,3]).
assig(4,22,4,[3],[1,3,4,5]).
assig(4,23,4,[2,3],[2]).

% Sintaxi: horesProhibides(professor,llistaHores).
horesProhibides(1,[5,8,9,14,21,22,24,26,30,31,41,55,56]).
horesProhibides(2,[5,7,8,9,12,15,19,20,25,26,27,29,31,33,37,38,42,46,50,55,58,60]).
horesProhibides(3,[10,14,20,23,26,32,37,39,40,43,44,53,55]).
horesProhibides(4,[2,7,14,16,19,23,24,31,32,34,40,42,45,47,48,49,50,51,53,54,56,58,59]).
horesProhibides(5,[7,10,11,12,15,20,22,25,27,34,37,39,41,42,46,49,51,52,60]).

