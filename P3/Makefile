file = miLiga


$(file): $(file).pl
	swipl -q -O -g main --stand_alone=true -o $(file) -c $(file).pl

clean:
	rm $(file) header clauses model infile.cnf
