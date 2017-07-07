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
		ss << "[]<> (search_again | seen)";
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
		cout << "\t\t(search_again) ;; searching for Waldo" << endl;
		cout << "\t\t(in ?r  - room)" << endl;
		cout << "\t\t(searched_in ?r  - room)" << endl;
		cout << "\t\t(move) ;; robot's turn" << endl;
		cout << "\t\t(" << p_currentBAstate << " ?s  - " << t_baState << ") ;;BAencoding" << endl;
		cout << "\t\t(ok) ;;BAencoding" << endl;
		cout << "\t)" << endl << endl;		
	}


	void moveRight(int i){
		if(encoding != "cross"){
					
			cout << "\t(:action move-right-from-r" << i << endl;
			
			cout << "\t\t:precondition" << endl;
			cout << "\t\t\t(and " << endl;
			cout << "\t\t\t\t(move)" << endl;
			cout << "\t\t\t\t(in r" << i << ")" << endl;
			if (i == nrooms/2 || i == nrooms){
				cout << "\t\t\t\t(not (seen))" << endl;
			}
			int succ = (i%nrooms) + 1;
			if (succ == nrooms/2 || succ == nrooms){
				cout << "\t\t\t\t(not (searched_in r" << succ << "))" << endl;
			}
			cout << "\t\t\t)" << endl;
			
			cout << "\t\t:effect" << endl;
			cout << "\t\t\t(and" << endl;
			cout << "\t\t\t\t(not (move))" << endl;
			cout << "\t\t\t\t(not (search_again))" << endl;
			cout << "\t\t\t\t(not (in r" << i <<"))" << endl;
			
			cout << "\t\t\t\t(in r" << succ <<")" << endl;
			if (succ == nrooms/2 || succ == nrooms){
				cout << "\t\t\t\t(oneof (not (seen)) (seen))" << endl;
				cout << "\t\t\t\t(searched_in r" << succ << ")" << endl;
			}
			cout << "\t\t\t)" << endl;
			cout << "\t)" << endl << endl;
		}
		std::stringstream ss;
		ss << "move-right-from-r"<<i;
		std::string header = ss.str();
		literal lit;				
		ss.str("");		       			

		
		cnf_formula prec;
		lit.sign() = true;
		ss <<  "(in r" << i << ")";
		lit.name() = ss.str();
		ss.str("");		       			
		prec.push_back(lit);

		if (i == nrooms/2 || i == nrooms){
			lit.sign() = false;
			ss <<  "(seen)";
			lit.name() = ss.str();
			ss.str("");		       			
			prec.push_back(lit);
		}
		int succ = (i%nrooms) + 1;
		if (succ == nrooms/2 || succ == nrooms){
			lit.sign() = false;
			ss <<  "(searched_in r" << succ << ")";
			lit.name() = ss.str();
			ss.str("");		       			
			prec.push_back(lit);
		}
		
		cnf_formula eff;
		lit.sign() = false;
		ss << "(search_again)";
		lit.name() = ss.str();
		ss.str("");		       			
		eff.push_back(lit);
		lit.sign() = false;
		ss <<  "(in r" << i << ")";
		lit.name() = ss.str();
		ss.str("");		       			
		eff.push_back(lit);
		lit.sign() = true;
		ss <<  "(in r" << succ << ")";
		lit.name() = ss.str();
		ss.str("");		       			
		eff.push_back(lit);
		
		if (succ == nrooms/2 || succ == nrooms){
			lit.sign() = true;
			ss <<  "(oneof (not (seen)) (seen))";
			lit.name() = ss.str();
			ss.str("");		       			
			eff.push_back(lit);
			lit.sign() = true;
			ss <<  "(searched_in r" << succ << ")";
			lit.name() = ss.str();
			ss.str("");		       			
			eff.push_back(lit);
		}
		
		translator.add_action( header, prec, eff);

	}

	void moveLeft(int i){
		if(encoding != "cross"){
			
			cout << "\t(:action move-left-from-r" << i << endl;
			
			cout << "\t\t:precondition" << endl;
			cout << "\t\t\t(and " << endl;
			cout << "\t\t\t\t(move)" << endl;
			cout << "\t\t\t\t(in r" << i << ")" << endl;
			if (i == nrooms/2 || i == nrooms){
				cout << "\t\t\t\t(not (seen))" << endl;
			}
			int succ = (i-1);
			if (succ == 0){
				succ = nrooms;
			}
			
			if (succ == nrooms/2 || succ == nrooms){
				cout << "\t\t\t\t(not (searched_in r" << succ << "))" << endl;
			}
			cout << "\t\t\t)" << endl;
			
			cout << "\t\t:effect" << endl;
			cout << "\t\t\t(and" << endl;
			cout << "\t\t\t\t(not (move))" << endl;
			cout << "\t\t\t\t(not (search_again))" << endl;
			cout << "\t\t\t\t(not (in r" << i <<"))" << endl;
			
			cout << "\t\t\t\t(in r" << succ <<")" << endl;
			if (succ == nrooms/2 || succ == nrooms){
				cout << "\t\t\t\t(oneof (not (seen)) (seen))" << endl;
				cout << "\t\t\t\t(searched_in r" << succ << ")" << endl;
			}
			cout << "\t\t\t)" << endl;
			cout << "\t)" << endl << endl;
		}
		std::stringstream ss;
		ss << "move-left-from-r"<<i;
		std::string header = ss.str();
		literal lit;				
		ss.str("");		       			

		
		cnf_formula prec;
		lit.sign() = true;
		ss <<  "(in r" << i << ")";
		lit.name() = ss.str();
		ss.str("");		       			
		prec.push_back(lit);

		if (i == nrooms/2 || i == nrooms){
			lit.sign() = false;
			ss <<  "(seen)";
			lit.name() = ss.str();
			ss.str("");		       			
			prec.push_back(lit);
		}
		int succ = (i - 1);
		if (succ == nrooms/2 || succ == nrooms){
			lit.sign() = false;
			ss <<  "(searched_in r" << succ << ")";
			lit.name() = ss.str();
			ss.str("");		       			
			prec.push_back(lit);
		}
		
		cnf_formula eff;
		lit.sign() = false;
		ss << "(search_again)";
		lit.name() = ss.str();
		ss.str("");		       			
		eff.push_back(lit);
		lit.sign() = false;
		ss <<  "(in r" << i << ")";
		lit.name() = ss.str();
		ss.str("");		       			
		eff.push_back(lit);
		lit.sign() = true;
		ss <<  "(in r" << succ << ")";
		lit.name() = ss.str();
		ss.str("");		       			
		eff.push_back(lit);
		
		if (succ == nrooms/2 || succ == nrooms){
			lit.sign() = true;
			ss <<  "(oneof (not (seen)) (seen))";
			lit.name() = ss.str();
			ss.str("");		       			
			eff.push_back(lit);
			lit.sign() = true;
			ss <<  "(searched_in r" << succ << ")";
			lit.name() = ss.str();
			ss.str("");		       			
			eff.push_back(lit);
		}
		
		translator.add_action( header, prec, eff);

	}

	void stay(){
		if(encoding != "cross"){
			cout << "\t(:action stay" << endl;
			cout << "\t\t:precondition" << endl;
			cout << "\t\t\t(and " << endl;
			cout << "\t\t\t\t(move)" << endl;
			cout << "\t\t\t)" << endl;
			cout << "\t\t:effect" << endl;
			cout << "\t\t\t(and" << endl;
			cout << "\t\t\t\t(not (move))" << endl;
			cout << "\t\t\t)" << endl;
			cout << "\t)" << endl << endl;
		}

		std::stringstream ss;
		ss << "stay";
		std::string header = ss.str();
		literal lit;				
			
		cnf_formula prec;
		cnf_formula eff;
		translator.add_action( header, prec, eff);
		
	}

	void searching_again(){
		if(encoding != "cross"){			
			cout << "\t(:action searching_again" << endl;
			cout << "\t\t:precondition" << endl;
			cout << "\t\t\t(and " << endl;
			cout << "\t\t\t\t(move)" << endl;
			cout << "\t\t\t\t(searched_in r" << nrooms/2 << ")" << endl;
			cout << "\t\t\t\t(searched_in r" << nrooms << ")" << endl;
			cout << "\t\t\t\t(not (seen))" << endl;
			cout << "\t\t\t)" << endl;
			cout << "\t\t:effect" << endl;
			cout << "\t\t\t(and" << endl;
			cout << "\t\t\t\t(not (move))" << endl;
			cout << "\t\t\t\t(not (searched_in r" << nrooms/2 << "))" << endl;
			cout << "\t\t\t\t(not (searched_in r" << nrooms << "))" << endl;
			cout << "\t\t\t\t(search_again)" << endl;
			cout << "\t\t\t)" << endl;
			cout << "\t)" << endl << endl;
		}
		
		std::stringstream ss;
		ss << "searchin_again";
		std::string header = ss.str();
		literal lit;				
		ss.str("");		       			

		
		cnf_formula prec;
		lit.sign() = true;
		ss <<  "(searched_in r" << nrooms/2 << ")";
		lit.name() = ss.str();
		ss.str("");		       			
		prec.push_back(lit);
		lit.sign() = true;
		ss <<  "(searched_in r" << nrooms << ")";
		lit.name() = ss.str();
		ss.str("");		       			
		prec.push_back(lit);
		lit.sign() = false;
		ss <<  "(seen)";
		lit.name() = ss.str();
		ss.str("");		       			
		prec.push_back(lit);
		
		cnf_formula eff;
		lit.sign() = false;
		ss <<  "(searched_in r" << nrooms/2 << ")";
		lit.name() = ss.str();
		ss.str("");		       			
		eff.push_back(lit);
		lit.sign() = false;
		ss <<  "(searched_in r" << nrooms << ")";
		lit.name() = ss.str();
		ss.str("");		       			
		eff.push_back(lit);
		lit.sign() = true;
		ss <<  "(search_again)";
		lit.name() = ss.str();
		ss.str("");		       			
		eff.push_back(lit);
		translator.add_action( header, prec, eff);

	}

	void domain_actions(){
		for (int i = 1; i <= nrooms; i++){
			moveRight(i);
			cout << endl;
			moveLeft(i);
		}
		cout << endl;
		stay();
		cout << endl;
		searching_again();
	}

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

	p.out();

	return 0;
}
