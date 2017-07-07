/*
 * Author: Nir Lipovezky && Fabio Patrizi
 * January 2013
 *
 */
#include <iostream>
#include <sstream>
#include "ltl2pddl.hxx"

using namespace std;


class Coder{
private:
	int nrooms;
	string t_baState, c_baState, p_currentBAstate;

	// ltl formula and engine to tranlate to pddl
	string ltl_formula;
	ltl2pddl translator;

	void header(){// Print file header
		cout << endl;
		cout << ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;" << endl;
		cout << ";; Waldo example for " << nrooms << " rooms" << endl;
		cout << ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;" << endl;
		cout << ";; Taken from" << endl;
		cout << ";; Kress-Gazit, H., Fainekos, G.E., Pappas, G.J." << endl;
		cout << ";; Where's Waldo? Sensor-Based Temporal Logic Motion Planning." << endl;
		cout << ";; ICRA 2007: 3116-3121" << endl;
		cout << ";;" << endl;
		cout << ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;" << endl;
		cout << ";; Goal formula:" << endl;
		cout << ";;" << endl;
		cout << ";; AE(r" << nrooms/2 << " || seen) && AE(r" << nrooms << " || seen)" << endl;
		cout << ";;" << endl;
		cout << ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;" << endl;
	}

	void define_ltl_goal(){
		
		cout << ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;" << endl;
		cout << ";;; LTL format for ltl2pddl tool" << endl;
		cout << ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;" << endl;
		stringstream ss;
		ss << "([]<> (in.r" << nrooms/2 << " | seen)) & " << "([]<> (in.r" << nrooms <<" | seen))";
		ltl_formula = ss.str();
		cout << ";; " << ltl_formula << endl;
		cout << ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;" << endl << endl;
	
		/**
		 * Translate the ltl formula into ba
		 */

		translator.parse_ltl( ltl_formula );
		if( !translator.ba_deterministic() ){
			cerr<< "Resulting Buchi is NON-DETERMINISTIC!! sorry, we cannot generate a compilation for this LTL formula"<<endl<<endl;
			exit(0);
		}
		
	}

	void domain(){// Print domain
		cout << "(define (domain waldo)" << endl;
		domain_declarations();
		
		domain_actions();			
		
		if(encoding == "cross"){
			std::string common_ba_precs;
			std::string common_ba_effects;
			translator.generate_pddl_encoding_xproduct( cout, p_currentBAstate, c_baState, common_ba_precs, common_ba_effects  );
			
		}
		else{
			
			/**
			 * Encodes BA into PDDL
			 */
			std::string common_ba_precs = buchi_precondition_literals2str();
			std::string common_ba_effects = buchi_effect_literals2str();		
			translator.generate_pddl_encoding( cout, p_currentBAstate, c_baState, common_ba_precs, common_ba_effects  );
		}
		
		cout << ")" << endl << endl;
	}

	void domain_declarations(){


		cout << "\t(:requirements :strips :typing :equality)" << endl;

		cout << "\t(:types " << endl;
		cout << "\t\troom" << endl;
		cout << "\t\t" << t_baState << " ;;BAencoding" << endl;
		cout << "\t)" << endl;

		cout << "\t(:constants" << endl;
		cout << "\t\t";
		for (int i = 1; i <= nrooms; i++){
			cout << "r"<< i << " ";
		}
		cout << "- room" << endl;
		cout << "\t\t";
		for (unsigned i = 0; i < translator.ba_states() ; i++){
			cout << c_baState << i << " ";
		}
		cout << " - " << t_baState << " ;;BAencoding" << endl;
		cout << "\t)" << endl;


		cout << "\t(:predicates" << endl;
		cout << "\t\t(seen) ;; found Waldo" << endl;
		cout << "\t\t(in ?r  - room)" << endl;
		cout << "\t\t(move) ;; robot's turn" << endl;
		cout << "\t\t(" << p_currentBAstate << " ?s  - " << t_baState << ") ;;BAencoding" << endl;
		cout << "\t\t(ok) ;;BAencoding" << endl;
		cout << "\t)" << endl << endl;		
	}


	void moveRight(int i){
		cout << "\t(:action move-right-from-r" << i << endl;

		cout << "\t\t:precondition" << endl;
		cout << "\t\t\t(and " << endl;
		cout << "\t\t\t\t(move)" << endl;
		cout << "\t\t\t\t(in r" << i << ")" << endl;
		if (i == nrooms/2 || i == nrooms){
			cout << "\t\t\t\t(not (seen))" << endl;
		}
		cout << "\t\t\t)" << endl;

		cout << "\t\t:effect" << endl;
		cout << "\t\t\t(and" << endl;
		cout << "\t\t\t\t(not (move))" << endl;
		cout << "\t\t\t\t(not (in r" << i <<"))" << endl;
		int succ = (i%nrooms) + 1;
		cout << "\t\t\t\t(in r" << succ <<")" << endl;
		if (succ == nrooms/2 || succ == nrooms){
			cout << "\t\t\t\t(oneof (not (seen)) (seen))" << endl;
		}
		cout << "\t\t\t)" << endl;
		cout << "\t)" << endl << endl;
	}

	void moveLeft(int i){
		cout << "\t(:action move-left-from-r" << i << endl;

		cout << "\t\t:precondition" << endl;
		cout << "\t\t\t(and " << endl;
		cout << "\t\t\t\t(move)" << endl;
		cout << "\t\t\t\t(in r" << i << ")" << endl;
		if (i == nrooms/2 || i == nrooms){
			cout << "\t\t\t\t(not (seen))" << endl;
		}
		cout << "\t\t\t)" << endl;

		cout << "\t\t:effect" << endl;
		cout << "\t\t\t(and" << endl;
		cout << "\t\t\t\t(not (move))" << endl;
		cout << "\t\t\t\t(not (in r" << i <<"))" << endl;
		int succ = (i-1);
		if (succ == 0){
			succ = nrooms;
		}
		cout << "\t\t\t\t(in r" << succ <<")" << endl;
		if (succ == nrooms/2 || succ == nrooms){
			cout << "\t\t\t\t(oneof (not (seen)) (seen))" << endl;
		}
		cout << "\t\t\t)" << endl;
		cout << "\t)" << endl << endl;
	}

	void stay(int i){
		if(i != nrooms/2 && i != nrooms){
			cout << "\t(:action stay" << endl;
			cout << "\t\t:precondition" << endl;
			cout << "\t\t\t(and " << endl;
			cout << "\t\t\t\t(move)" << endl;
			cout << "\t\t\t\t(not (in r" << nrooms/2 << "))" << endl;
			cout << "\t\t\t\t(not (in r" << nrooms << "))" << endl;
			cout << "\t\t\t)" << endl;
			cout << "\t\t:effect" << endl;
			cout << "\t\t\t(and" << endl;
			cout << "\t\t\t\t(not (move))" << endl;
			cout << "\t\t\t)" << endl;
			cout << "\t)" << endl << endl;
			return;
		}

		cout << "\t(:action stay-in-r" << i << "-seen" << endl;
		cout << "\t\t:precondition" << endl;
		cout << "\t\t\t(and " << endl;
		cout << "\t\t\t\t(move)" << endl;
		cout << "\t\t\t\t(in r" << i << ")" << endl;
		cout << "\t\t\t\t(seen)" << endl;
		cout << "\t\t\t)" << endl;
		cout << "\t\t:effect" << endl;
		cout << "\t\t\t(and" << endl;
		cout << "\t\t\t\t(not (move))" << endl;
		cout << "\t\t\t)" << endl;
		cout << "\t)" << endl << endl;

		cout << "\t(:action stay-in-r" << i << "-not-seen" << endl;
		cout << "\t\t:precondition" << endl;
		cout << "\t\t\t(and " << endl;
		cout << "\t\t\t\t(move)" << endl;
		cout << "\t\t\t\t(in r" << i << ")" << endl;
		cout << "\t\t\t\t(not (seen))" << endl;
		cout << "\t\t\t)" << endl;
		cout << "\t\t:effect" << endl;
		cout << "\t\t\t(and" << endl;
		cout << "\t\t\t\t(not (move))" << endl;
		cout << "\t\t\t\t(oneof (not (seen)) (seen))" << endl;
		cout << "\t\t\t)" << endl;
		cout << "\t)" << endl << endl;
	}

	// void stay(int i){
	// 	if(i != nrooms/2 && i != nrooms){
	// 		cout << "\t(:action stay-in-r" << i << endl;
	// 		cout << "\t\t:precondition" << endl;
	// 		cout << "\t\t\t(and " << endl;
	// 		cout << "\t\t\t\t(move)" << endl;
	// 		cout << "\t\t\t\t(in r" << i << ")" << endl;
	// 		cout << "\t\t\t)" << endl;
	// 		cout << "\t\t:effect" << endl;
	// 		cout << "\t\t\t(and" << endl;
	// 		cout << "\t\t\t\t(not (move))" << endl;
	// 		cout << "\t\t\t)" << endl;
	// 		cout << "\t)" << endl << endl;
	// 		return;
	// 	}

	// 	cout << "\t(:action stay-in-r" << i << "-seen" << endl;
	// 	cout << "\t\t:precondition" << endl;
	// 	cout << "\t\t\t(and " << endl;
	// 	cout << "\t\t\t\t(move)" << endl;
	// 	cout << "\t\t\t\t(in r" << i << ")" << endl;
	// 	cout << "\t\t\t\t(seen)" << endl;
	// 	cout << "\t\t\t)" << endl;
	// 	cout << "\t\t:effect" << endl;
	// 	cout << "\t\t\t(and" << endl;
	// 	cout << "\t\t\t\t(not (move))" << endl;
	// 	cout << "\t\t\t)" << endl;
	// 	cout << "\t)" << endl << endl;

	// 	cout << "\t(:action stay-in-r" << i << "-not-seen" << endl;
	// 	cout << "\t\t:precondition" << endl;
	// 	cout << "\t\t\t(and " << endl;
	// 	cout << "\t\t\t\t(move)" << endl;
	// 	cout << "\t\t\t\t(in r" << i << ")" << endl;
	// 	cout << "\t\t\t\t(not (seen))" << endl;
	// 	cout << "\t\t\t)" << endl;
	// 	cout << "\t\t:effect" << endl;
	// 	cout << "\t\t\t(and" << endl;
	// 	cout << "\t\t\t\t(not (move))" << endl;
	// 	cout << "\t\t\t\t(oneof (not (seen)) (seen))" << endl;
	// 	cout << "\t\t\t)" << endl;
	// 	cout << "\t)" << endl << endl;
	// }

	void domain_actions(){
		for (int i = 1; i <= nrooms; i++){
			moveRight(i);
			cout << endl;
			moveLeft(i);
		}
		cout << endl;
		stay(0);
		cout << endl;
		stay(nrooms/2);
		cout << endl;
		stay(nrooms);

	}

	// void request(){
	// 	if(encoding != "cross"){
	// 		cout << "\t(:action request" << endl;
			
	// 		cout << "\t\t:precondition" << endl;
	// 		cout << "\t\t\t(and " << endl;
	// 		cout << "\t\t\t\t(done)" << endl;
	// 		cout << "\t\t\t\t(move)" << endl;
	// 		cout << "\t\t\t)" << endl;
			
	// 		cout << "\t\t:effect" << endl;
	// 		cout << "\t\t\t(and" << endl;
	// 		cout << "\t\t\t\t(not (done))" << endl;
	// 		cout << "\t\t\t\t(not (move))" << endl;
	// 		cout << "\t\t\t\t(oneof" << endl;
	// 		for(int i = 1; i <= npkg; i++)
	// 			cout<<"\t\t\t\t\t(want p"<<i<<")" << endl;
			
	// 		cout << "\t\t\t\t)" << endl;
	// 		cout << "\t\t\t)" << endl;
	// 		cout << "\t)" << endl << endl;
	// 	}
	// 	std::string header = "request";
	// 	std::stringstream ss;
	// 	literal lit;				
		
	// 	cnf_formula prec;
	// 	lit.sign() = true;
	// 	lit.name() = "(done)";
	// 	prec.push_back(lit);
		
	// 	cnf_formula eff;
	// 	lit.sign() = false;
	// 	lit.name() = "(done)";
	// 	eff.push_back(lit);
	// 	lit.sign() = true;
	// 	ss << "(oneof ";

	// 	for(int i = 1; i <= npkg; i++)
	// 		ss << " (want p" << i << ")";
	// 	ss << " )";
	// 	lit.name() = ss.str();
	// 	eff.push_back(lit);		
	// 	translator.add_action( header, prec, eff);
	// }

	std::string buchi_precondition_literals2str(){
		std::stringstream ss;
		ss << "\t\t\t\t(not (move))" << endl;
		return ss.str();
	}

	std::string buchi_effect_literals2str(){
		std::stringstream ss;
		ss << "\t\t\t\t(move)" << endl;
		return ss.str();
	}



public:
	std::string encoding;
	
	Coder(int n){
		nrooms = n;
		
		t_baState = "baState";
		p_currentBAstate = "currentBAstate";
		c_baState = "BA-S";
		encoding = "cross";
	}


	void out(){
		header();
		define_ltl_goal();
		domain();
	}

};

void help(string progname){
	cout << endl << "command line:" << progname << " <num_pkg(>=1)> <cross/sequential>" << endl << endl;
}


int main(int argc, char* argv[]){

	/* Parameters:
	 * argv[1] = num of packages (required)
	 */

	// Check that an input string is provided
	if(argc < 3){
		help(argv[0]);
		return 1;
	}

	// Converts the input string into an int
	istringstream spkg(argv[1]);
	int nrooms = 0;
	spkg >> nrooms;

	// If nrooms < 4 or no integer is provided, exit
	if(nrooms < 1){
		cout << endl << "Please insert a number of packages >= 1" << endl << endl ;
		return 1;
	}

	// output the file
	Coder p(nrooms);

		
	p.encoding = argv[2];
	if(p.encoding == "cross"){
		cout << "Haven't implement it yet, ... tomorrow I'll do it ;)";
		exit(0);
	}

	p.out();

	return 0;
}
