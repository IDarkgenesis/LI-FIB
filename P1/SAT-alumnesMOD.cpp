#include <iostream>
#include <stdlib.h>
#include <algorithm>
#include <vector>
using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0

struct vector2 {
	vector<int> isT;
	vector<int> isF;
};

uint numVars;
uint numClauses;
vector<vector<int> > clauses;
vector<int> model;

//NOMES ANAR ON CAL EVALUAR SI NEGATIU ANAR A POSITIUS I A AL REVÉS
vector<vector2> ocurrList;

vector<int> conflicts;

//UTILITZAR HEURISTIC
vector<double> heu;
int LIMIT= 250;
int PLUS= 25;
int PEN= 2;

////////////////////////////////////////

vector<int> modelStack;
uint indexOfNextLitToPropagate;
uint decisionLevel;

//INFO PER IMPRIMIR
double elapsed_time;
int decisions=0;

void print_end(){
    cout << "Time: " << double(double(clock()) - elapsed_time) / CLOCKS_PER_SEC << endl;
    cout << "Decisions: " << decisions << endl;
}

void readClauses(){
	// Skip comments
	char c = cin.get();
	
    while (c == 'c') {
		while (c != '\n') c = cin.get();
		c = cin.get();
	}  
	
	// Read "cnf numVars numClauses"
	string aux;
	cin >> aux >> numVars >> numClauses;
	clauses.resize(numClauses);

    ocurrList.resize(numVars+1);
	conflicts= vector<int> (numVars+1, 0);
    
    heu= vector<double> (numVars+1,0);
    
    // Read clauses
	for (uint i = 0; i < numClauses; ++i) {
		int lit;
		while (cin >> lit and lit != 0) {
			clauses[i].push_back(lit);
			if(lit > 0) ocurrList[lit].isT.push_back(i);
			else ocurrList[-lit].isF.push_back(i);
		}
	}
	//cout << "READ" << endl;
}



int currentValueInModel(int lit){
	
    if (lit >= 0) return model[lit];
	
    else {
		if (model[-lit] == UNDEF) return UNDEF;
		else return 1 - model[-lit];
	}
}


void setLiteralToTrue(int lit){
	modelStack.push_back(lit);
	if (lit > 0) model[lit] = TRUE;
	else model[-lit] = FALSE;		
}


bool propagateGivesConflict ( ) {
	while ( indexOfNextLitToPropagate < modelStack.size() ) {
		int lit= modelStack[indexOfNextLitToPropagate];
        vector<int> *OCclauses;
        
        if (lit < 0)  OCclauses= &ocurrList[-lit].isT;
        else OCclauses= &ocurrList[lit].isF;
        
        
		for (uint i = 0; i < (*OCclauses).size(); ++i) {
			bool someLitTrue = false;
			int numUndefs = 0;
			int lastLitUndef = 0;
            int aux= (*OCclauses)[i];
			
            for (uint k = 0; not someLitTrue and k < clauses[aux].size(); ++k){
				int val = currentValueInModel(clauses[aux][k]);
				if (val == TRUE) someLitTrue = true;
				else if (val == UNDEF){ ++numUndefs; lastLitUndef = clauses[aux][k]; }
			}
			
			if (not someLitTrue and numUndefs == 0) {
                
                for(uint f=0; f < clauses[aux].size(); ++f){
                    
                    int aux2=clauses[aux][f];
                    
                    if(aux2 < 0) ++conflicts[-aux2];
                    else ++conflicts[aux2];
                }
                return true;
            } 
            else if (not someLitTrue and numUndefs == 1) setLiteralToTrue(lastLitUndef);	
		}
		//cout << "Una Propagacio" << endl;
        
		++indexOfNextLitToPropagate;
	}
	return false;
}


void backtrack(){
	uint i = modelStack.size() -1;
	int lit = 0;
	while (modelStack[i] != 0){ // 0 is the DL mark
		lit = modelStack[i];
		model[abs(lit)] = UNDEF;
		modelStack.pop_back();
		--i;
	}
	// at this point, lit is the last decision
	modelStack.pop_back(); // remove the DL mark
	--decisionLevel;
	indexOfNextLitToPropagate = modelStack.size();
	setLiteralToTrue(-lit);  // reverse last decision
}


// Heuristic for finding the next decision literal:
int getNextDecisionLiteral(){
    ++decisions;
    
    bool first = true;
    int index =0, max=0;
    
    for(uint i=1; i < conflicts.size(); ++i){
        if(first && model[i] == UNDEF){
            max= conflicts[i];
            index=i;
            first=false;
        }
        if(model[i] == UNDEF && max < conflicts[i]){
            max = conflicts[i];
            index = i;
        }
    }
    conflicts[index]=0;
    
    return index;
    
}

void checkmodel(){
	for (uint i = 0; i < numClauses; ++i){
		bool someTrue = false;
		for (uint j = 0; not someTrue and j < clauses[i].size(); ++j)
			someTrue = (currentValueInModel(clauses[i][j]) == TRUE);
		if (not someTrue) {
			cout << "Error in model, clause is not satisfied:";
			for (uint j = 0; j < clauses[i].size(); ++j) cout << clauses[i][j] << " ";
			cout << endl;
			exit(1);
		}
	}  
}

int main(){ 
	readClauses(); // reads numVars, numClauses and clauses
	model.resize(numVars+1,UNDEF); //LUGAR DONDE GUARDAMOS LAS VARIABLES Y SU ESTADO TRUE/FALSE/INDEF
	indexOfNextLitToPropagate = 0;  
	decisionLevel = 0; //INDICA QUE ENCARA NO HEM DECIDIT RES, A MESURA QUE AVANCEM "DECIDINT" AUGMENTA, NO AUGMENTA SI PROPAGAM
	
	// Take care of initial unit clauses, if any || TRACTA SES CLAUSULES QUE NOMÉS TENEN UN TERME PRIMER
	for (uint i = 0; i < numClauses; ++i) {
		if (clauses[i].size() == 1) {
			int lit = clauses[i][0]; //MIRA QUIN LITERAL ES PER A PODER ACCEDIR A MODEL
			int val = currentValueInModel(lit); // COMPROVAR EN QUIN ESTAT ESTA ES LITERAL
			if (val == FALSE) {cout << "UNSATISFIABLE" << endl; return 10;} //AIXO PASSA PERQUE SES CLAUSULES ESTAN RELACIONADES AMB ANDS I SI UN ES FALSE TOT ES FALSE
			else if (val == UNDEF) setLiteralToTrue(lit); //ELS POSA A TRUE PER A QUE NO SIGUI ISTATISFACTBILE
		}
    }
        elapsed_time=clock();
		
		// DPLL algorithm
		while (true) {
			while ( propagateGivesConflict() ) {
				if ( decisionLevel == 0) { cout << "UNSATISFIABLE" << endl; print_end();return 10; }
				backtrack();
			}
			int decisionLit = getNextDecisionLiteral();
			if (decisionLit == 0) { checkmodel(); cout << "SATISFIABLE" << endl; print_end();return 20; }
			// start new decision level:
			modelStack.push_back(0);  // push mark indicating new DL
			++indexOfNextLitToPropagate;
			++decisionLevel;
			setLiteralToTrue(decisionLit);    // now push decisionLit on top of the mark
		}
}  
