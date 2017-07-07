/*
 * Author: Nir Lipovezky && Fabio Patrizi
 * January 2013
 *
 */

// fluents: p1 .... pn (pkgs in the store) + done
// det actions: pick(pi):  prec pi, want pi, prec not done, effects not pi, add  done, delete want(pi)
// single non-det action with prec=done, non-det effect want(pi) i=1 .. n + not done ..
// (basically requests and picks must alternate)
// LTL goal: always if pi and want(pi) then eventually not pi
// SPOT formula: "[]((p && wantP) -> <> ! p) & ...
// initially = p1 .. pn etc.
#include <iostream>
#include <sstream>
#include "ltl2pddl.hxx"

using namespace std;


class Coder{
private:
	int npkg;
	string t_baState, c_baState, p_currentBAstate;

	// ltl formula and engine to tranlate to pddl
	string ltl_formula;
	ltl2pddl translator;

	void header(){// Print file header
		cout << endl;
		cout << ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;" << endl;
		cout << ";; Store example for " << npkg << " packages" << endl;
		cout << ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;" << endl;
		cout << ";; Goal formula:" << endl;
		cout << ";;" << endl;			
		cout << ";; A( (pkg_requested) --> E (pkg_served) )" << endl;
		cout << ";;" << endl;
		cout << ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;" << endl;
	}

	void define_ltl_goal(){
		cout << ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;" << endl;
		cout << ";;; LTL format for ltl2pddl tool" << endl;
		cout << ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;" << endl;
		stringstream ss;
		ss << "[] ( pkg_requested -> <> pkg_served)";
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
		cout << "(define (domain packages)" << endl;
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
		cout << "\t\tpkg" << endl;
		cout << "\t\t" << t_baState << " ;;BAencoding" << endl;
		cout << "\t)" << endl;

		cout << "\t(:constants" << endl;
		cout << "\t\t";
		for (int i = 1; i <= npkg; i++){
			cout << "p"<< i << " ";
		}
		cout << "- pkg" << endl;
		cout << "\t\t";
		for (unsigned i = 0; i < translator.ba_states() ; i++){
			cout << c_baState << i << " ";
		}
		cout << " - " << t_baState << " ;;BAencoding" << endl;
		cout << "\t)" << endl;

		cout << "\t(:predicates" << endl;
		cout << "\t\t(in_store ?p  - pkg)" << endl;
		cout << "\t\t(want ?p  - pkg)" << endl;
		cout << "\t\t(pkg_served)" << endl;
		cout << "\t\t(pkg_requested)" << endl;
		cout << "\t\t(move) ;; store's turn" << endl;
		cout << "\t\t(" << p_currentBAstate << " ?s  - " << t_baState << ") ;;BAencoding" << endl;
		cout << "\t\t(ok) ;;BAencoding" << endl;
		cout << "\t)" << endl << endl;
	}

	void pick(int i){
		if(encoding != "cross"){
			cout << "\t(:action pick-p" << i << endl;
			
			cout << "\t\t:precondition" << endl;
			cout << "\t\t\t(and " << endl;
			cout << "\t\t\t\t(not (pkg_served))" << endl;
			cout << "\t\t\t\t(move)" << endl;
			cout << "\t\t\t\t(in_store p" << i << ")" << endl;
			cout << "\t\t\t\t(want p" << i << ")" << endl;
			cout << "\t\t\t)" << endl;
			
			cout << "\t\t:effect" << endl;
			cout << "\t\t\t(and" << endl;
			cout << "\t\t\t\t(not (move))" << endl;
			cout << "\t\t\t\t(not (pkg_requested))" << endl;
			cout << "\t\t\t\t(pkg_served)" << endl;
			cout << "\t\t\t\t(not (in_store p" << i <<"))" << endl;
			cout << "\t\t\t\t(not (want p" << i <<"))" << endl;
			cout << "\t\t\t)" << endl;
			cout << "\t)" << endl << endl;
		}
		std::stringstream ss;
		ss << "pick-p" << i;
		std::string header = ss.str();
		ss.str("");

		literal lit;				
		
		cnf_formula prec;
		lit.sign() = false;
		lit.name() = "(pkg_served)";
		prec.push_back(lit);
		lit.sign() = true;
		ss << "(in_store p"<<i<<")";
		lit.name() = ss.str();
		ss.str("");
		prec.push_back(lit);
		ss << "(want p" << i << ")";
		lit.name() = ss.str();
		ss.str("");
		prec.push_back(lit);
		
		cnf_formula eff;
		lit.sign() = true;
		lit.name() = "(pkg_served)";
		eff.push_back(lit);
		lit.sign() = false;
		lit.name() = "(pkg_requested)";
		eff.push_back(lit);
		lit.sign() = false;
		ss << "(in_store p"<<i<<")";
		lit.name() = ss.str();
		ss.str("");
		eff.push_back(lit);
		ss << "(want p" << i << ")";
		lit.name() = ss.str();
		ss.str("");
		eff.push_back(lit);
		
		translator.add_action( header, prec, eff);
		
	}

	void restock(int i){
		if(encoding != "cross"){
			cout << "\t(:action restock-p" << i << endl;
			
			cout << "\t\t:precondition" << endl;
			cout << "\t\t\t(and " << endl;
			cout << "\t\t\t\t(not (pkg_served))" << endl;
			cout << "\t\t\t\t(move)" << endl;
			cout << "\t\t\t\t(not (in_store p" << i << "))" << endl;
			cout << "\t\t\t\t(want p" << i << ")" << endl;
			cout << "\t\t\t)" << endl;
			
			cout << "\t\t:effect" << endl;
			cout << "\t\t\t(and" << endl;
			cout << "\t\t\t\t(in_store p" << i <<")" << endl;
			cout << "\t\t\t)" << endl;
			cout << "\t)" << endl << endl;
		}
		std::stringstream ss;
		ss << "restock-p" << i;
		std::string header = ss.str();
		ss.str("");

		literal lit;				
		
		cnf_formula prec;
		lit.sign() = false;
		lit.name() = "(pkg_served)";
		prec.push_back(lit);
		ss << "(in_store p"<<i<<")";
		lit.name() = ss.str();
		ss.str("");
		prec.push_back(lit);
		lit.sign() = true;
		ss << "(want p" << i << ")";
		lit.name() = ss.str();
		ss.str("");
		prec.push_back(lit);
		
		cnf_formula eff;
		lit.sign() = true;
		ss << "(in_store p"<<i<<")";
		lit.name() = ss.str();
		ss.str("");
		eff.push_back(lit);
		
		translator.add_action( header, prec, eff);
		
	}

	void request(){
		if(encoding != "cross"){
			cout << "\t(:action request" << endl;
			
			cout << "\t\t:precondition" << endl;
			cout << "\t\t\t(and " << endl;
			cout << "\t\t\t\t(pkg_served)" << endl;
			cout << "\t\t\t\t(move)" << endl;
			cout << "\t\t\t)" << endl;
			
			cout << "\t\t:effect" << endl;
			cout << "\t\t\t(and" << endl;
			cout << "\t\t\t\t(not (move))" << endl;
			cout << "\t\t\t\t(pkg_requested)" << endl;
			cout << "\t\t\t\t(not (pkg_served))" << endl;
			cout << "\t\t\t\t(oneof" << endl;
			for(int i = 1; i <= npkg; i++)
				cout<<"\t\t\t\t\t(want p"<<i<<")" << endl;
			
			cout << "\t\t\t\t)" << endl;
			cout << "\t\t\t)" << endl;
			cout << "\t)" << endl << endl;
		}
		std::string header = "request";
		std::stringstream ss;
		literal lit;				
		
		cnf_formula prec;
		lit.sign() = true;
		lit.name() = "(pkg_served)";
		prec.push_back(lit);
		
		cnf_formula eff;
		lit.sign() = false;
		lit.name() = "(pkg_served)";
		eff.push_back(lit);
		lit.sign() = true;
		lit.name() = "(pkg_requested)";
		eff.push_back(lit);
		lit.sign() = true;
		ss << "(oneof ";

		for(int i = 1; i <= npkg; i++)
			ss << " (want p" << i << ")";
		ss << " )";
		lit.name() = ss.str();
		eff.push_back(lit);		
		translator.add_action( header, prec, eff);
	}

	void domain_actions(){
		for (int i = 1; i <= npkg; i++){
			pick(i);
			cout << endl;
			restock(i);
			cout << endl;
		}
		request();
		cout << endl;
			
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
		npkg = n;
		
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
	int npkg = 0;
	spkg >> npkg;

	// If nrooms < 4 or no integer is provided, exit
	if(npkg < 1){
		cout << endl << "Please insert a number of packages >= 1" << endl << endl ;
		return 1;
	}

	// output the file
	Coder p(npkg);

	p.encoding = argv[2];
	p.out();

	return 0;
}
