/*
 * Author: Fabio Patrizi
 * March 2012
 *
 * Updated: Nir Lipovetzky & Fabio Patrizi
 * January 2013
 */

#include <iostream>
#include <sstream>
#include "ltl2pddl.hxx"

using namespace std;


class LiftCoder{
private:
	int floors;

	// types
	string t_floor, t_baState;

	// constants
	string c_floor, c_baState;

	// predicates
	string p_at, p_req, p_turn, p_check, p_move, p_called, p_currentBAstate, p_ok;

	// ltl formula and engine to tranlate to pddl
	string ltl_formula;
	ltl2pddl translator;
	
	void header(){// Print file header
		cout << endl;
		cout << ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;" << endl;
		cout << ";;; Lift for a " << floors << "-floor building" << endl;
		cout << ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;" << endl;
		cout << ";;" << endl;
		cout << ";; Goal formula:" << endl;
		cout << ";;" << endl;
		for (int i = 1; i < floors; i++){
			cout << ";; AE((" << p_req << " " << c_floor << i << ") -> (" << p_at << " " << c_floor << i <<")) &&" << endl;
		}
		cout << ";; AE((" << p_req << " " << c_floor << floors << ") -> (" << p_at << " " << c_floor << 0 <<"))" << endl;		
		cout << ";;" << endl;
		cout << ";; (Same as in Piterman-etal@VMCAI06)" << endl;
		cout << ";;" << endl;
		cout << ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;" << endl;
	}

	void define_ltl_goal(){
		cout << ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;" << endl;
		cout << ";;; LTL format for ltl2pddl tool" << endl;
		cout << ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;" << endl;
		stringstream ss;
		for (int i = 1; i < floors; i++){
			ss << "[] <> (" << p_req << "." << c_floor << i << " -> " << p_at << "." << c_floor << i <<") && ";
		}
		ss << "[] <> (" << p_req << "." << c_floor << floors << " -> " << p_at << "." << c_floor << 0 <<" )";		

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
		cout << "(define (domain lift)" << endl;
		domain_declarations();
		push_actions();
		check_called_actions();
		move_actions();
		no_op();

		/**
		 * Encodes BA into PDDL
		 */
		std::string common_ba_precs = buchi_precondition_literals2str();
		std::string common_ba_effects = buchi_effect_literals2str();		
		translator.generate_pddl_encoding( cout, p_currentBAstate, c_baState, common_ba_precs, common_ba_effects  );

		cout << ")" << endl << endl;

	}

	void domain_declarations(){
		cout << "\t(:requirements :strips :typing :equality)" << endl;

		cout << "\t(:types " << endl;
		cout << "\t\t" << t_floor << endl;
		cout << "\t\t" << t_baState << " ;;BAencoding" << endl;
		cout << "\t)" << endl;

		cout << "\t(:constants" << endl;
		cout << "\t\t";
		for (int i = 1; i <= floors; i++){
			cout << c_floor << i << " ";
		}
		cout << "- floor" << endl;

		cout << "\t\t";
		for (unsigned i = 0; i < translator.ba_states() ; i++){
			cout << c_baState << i << " ";
		}
		cout << " - " << t_baState << " ;;BAencoding" << endl;
		cout << "\t)" << endl;

		cout << "\t(:predicates" << endl;
		cout << "\t\t(" << p_at << " ?f  - " << t_floor << ")" << endl;
		cout << "\t\t(" << p_req << " ?f  - " << t_floor << ")" << endl;
		cout << "\t\t(" << p_turn << " ?f  - " << t_floor << ")" << endl;
		cout << "\t\t(" << p_check << ")" << endl;
		cout << "\t\t(" << p_called << ")" << endl;
		cout << "\t\t(" << p_move << ")" << endl;
		cout << "\t\t(" << p_currentBAstate << " ?s  - " << t_baState << ") ;;BAencoding" << endl;
		cout << "\t\t(ok) ;;BAencoding" << endl;
		cout << "\t)" << endl << endl;
	}

	void push_precondition_literals(int i){
		cout << "\t\t\t\t(" << p_turn << " " << c_floor << i << ")" << endl;
		cout << "\t\t\t\t(not (" << p_check << "))" << endl;
	}

	void push_effect_literals(int i){
		cout << "\t\t\t\t(not (" << p_turn << " " << c_floor << i << "))" << endl;
		if(i < floors){
			cout << "\t\t\t\t(" << p_turn << " " << c_floor << i+1 << ")" << endl;
		}
		else{
			cout << "\t\t\t\t(" << p_turn << " " << c_floor << 1 << ")" << endl;
			cout << "\t\t\t\t(" << p_check <<")" << endl;
		}
	}

	void push_actions(){
		for (int i = 1; i <= floors; i++){
			cout << "\t(:action push_" << c_floor << i << "-" << 1 << endl;
			cout << "\t\t:precondition" << endl;
			cout << "\t\t\t(and " << endl;
			push_precondition_literals(i);
			cout << "\t\t\t\t(not (" << p_at << " " << c_floor << i << "))" << endl;
			cout << "\t\t\t" << ")" << endl;
			cout << "\t\t:effect" << endl;
			cout << "\t\t\t(and" << endl;
			push_effect_literals(i);
			cout << "\t\t\t\t(oneof (and) (" << p_req << " " << c_floor << i << "))" << endl;
			cout << "\t\t\t)" << endl;
			cout << "\t)" << endl;

			cout << "\t(:action push_" << c_floor << i << "-" << 2 << endl;
			cout << "\t\t:precondition" << endl;
			cout << "\t\t\t(and " << endl;
			push_precondition_literals(i);
			cout << "\t\t\t\t(" << p_at << " " << c_floor << i << ")" << endl;
			cout << "\t\t\t" << ")" << endl;
			cout << "\t\t:effect" << endl;
			cout << "\t\t\t(and" << endl;
			push_effect_literals(i);
			cout << "\t\t\t\t(not (" << p_req << " " << c_floor << i << ")); request is reset" << endl;
			cout << "\t\t\t)" << endl;
			cout << "\t)" << endl;

		}
	}

	void check_called_actions(){
		for (int i = 1; i <= floors; i++){
			cout << "\t(:action check_called_true_" << c_floor << i << endl;
			cout << "\t\t:precondition" << endl;
			cout << "\t\t\t(and " << endl;
			cout << "\t\t\t\t(" << p_turn << " " << c_floor << i << ")" << endl;
			cout << "\t\t\t\t(" << p_check << ")" << endl;
			cout << "\t\t\t\t(" << p_req << " " << c_floor << i << ")" << endl;
			cout << "\t\t\t" << ")" << endl;
			cout << "\t\t:effect" << endl;
			cout << "\t\t\t(and" << endl;
			cout << "\t\t\t\t(" << p_called << ")" << endl;
			cout << "\t\t\t\t(not (" << p_turn << " " << c_floor << i << "))" << endl;
			if(i < floors){
				cout << "\t\t\t\t(" << p_turn << " " << c_floor << i+1 << ")" << endl;
			}
			else{
				cout << "\t\t\t\t(not (" << p_check << "))" << endl;
				cout << "\t\t\t\t(" << p_move << ")" << endl;
			}
			cout << "\t\t\t)" << endl;
			cout << "\t)" << endl;

			cout << "\t(:action check_called_false_" << c_floor << i << endl;
			cout << "\t\t:precondition" << endl;
			cout << "\t\t\t(and " << endl;
			cout << "\t\t\t\t(" << p_turn << " " << c_floor << i << ")" << endl;
			cout << "\t\t\t\t(" << p_check << ")" << endl;
			cout << "\t\t\t\t(not (" << p_req << " " << c_floor << i << "))" << endl;
			cout << "\t\t\t" << ")" << endl;
			cout << "\t\t:effect" << endl;
			cout << "\t\t\t(and" << endl;
			cout << "\t\t\t\t(not (" << p_turn << " " << c_floor << i << "))" << endl;
			if(i < floors){
				cout << "\t\t\t\t(" << p_turn << " " << c_floor << i+1 << ")" << endl;
			}
			else{
				cout << "\t\t\t\t(not (" << p_check << "))" << endl;
				cout << "\t\t\t\t(" << p_move << ")" << endl;
			}
			cout << "\t\t\t)" << endl;
			cout << "\t)" << endl;

		}

	}

	void move_actions(){
		for (int i = 1; i < floors; i++){
			move_up(i);
		}
		for (int i = floors; i > 1; i--){
			move_down(i);
		}
	}


	void move_precondition(bool up, int from){
		cout << "\t\t:precondition" << endl;
		cout << "\t\t\t(and" << endl;
		cout << "\t\t\t\t(" << p_at << " " << c_floor << from << ")" << endl;
		if (up){
			cout << "\t\t\t\t(" << p_called << ") ;; can move up only if called" << endl;
		}
		cout << "\t\t\t\t(" << p_move << ")" << endl;
		cout << "\t\t\t)" << endl;
	}

	void move_effect(bool up, int from){
		cout << "\t\t:effect" << endl;
		cout << "\t\t\t(and" << endl;
		cout << "\t\t\t\t(not (" << p_at << " " << c_floor << from << "))" << endl;
		cout << "\t\t\t\t(" << p_at << " " << c_floor;
		if(up){
			cout << from + 1;
		}
		else{// down
			cout << from - 1;
		}
		cout << ")" << endl;

		cout << "\t\t\t\t(not (" << p_move << "))" << endl;
		cout << "\t\t\t)" << endl;
	}

	void move_up(int from){
		cout << "\t(:action move_up_from_" << c_floor << from << endl;
		move_precondition(true, from);
		move_effect(true,from);
		cout << "\t)" << endl;
	}

	void move_down(int from){
		cout << "\t(:action move_down_from_" << c_floor << from << endl;
		move_precondition(false, from);
		move_effect(false,from);
		cout << "\t)" << endl;
	}

	void no_op(){
		cout << "\t(:action no_op" << endl;
		cout << "\t\t:precondition" << endl;
		cout << "\t\t\t(and (" << p_move << "))" << endl;
		cout << "\t\t:effect" << endl;
		cout << "\t\t\t(and (not (" << p_move << ")))" << endl;
		cout << "\t)" << endl;
	}

	std::string buchi_precondition_literals2str(){
		std::stringstream ss;
		for (int i = 1; i <= floors; i++){
			ss << "\t\t\t\t(not (" << p_turn << " " << c_floor << i << "))" << endl;
		}
		ss << "\t\t\t\t(not (" << p_move << "))" << endl;
		return ss.str();
	}

	std::string buchi_effect_literals2str(){
		std::stringstream ss;
		ss << "\t\t\t\t(" << p_turn << " " << c_floor << "1)" << endl;
		ss << "\t\t\t\t(not (" << p_called << ")) ;; reset" << endl;
		return ss.str();
	}




public:
	LiftCoder(int n){
		floors = n;

		// types
		t_floor = "floor";
		t_baState = "baState";

		// constants
		c_floor = "f";
		c_baState = "BA-S";

		// predicates
		p_at = "at";
		p_req = "req";
		p_turn = "turn";
		p_check = "check";
		p_called = "called";
		p_move = "move";
		p_currentBAstate = "currentBAstate";
		p_ok = "ok";
	}


	void out(){
		header();
		define_ltl_goal();
		domain();
	}

};

void help(string progname){
	cout << endl << "command line:" << progname << " <num_floors>" << endl << endl;
}


int main(int argc, char* argv[]){

	/* Parameters:
	 * argv[1] = num of floors (required)
	 */

	// Check that an input string is provided
	if(argc < 2){
		help(argv[0]);
		return 1;
	}

	// Converts the input string into an int
	istringstream sfloors(argv[1]);
	int nfloors = 0;
	sfloors >> nfloors;

	// If floors = 0 (or no integer is provided) exit
	if(nfloors == 0){
		cout << endl << "Please insert a number of floors > 0" << endl << endl ;
		return 1;
	}

	// output the file
	LiftCoder p(nfloors);
	p.out();

	return 0;
}
