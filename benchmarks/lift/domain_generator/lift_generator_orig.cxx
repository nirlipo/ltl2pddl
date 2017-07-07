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

template <typename T>
T pow( T a, unsigned b )
{
        T result = 1;
        while (b){
                if (b & 1)
                        result *= a;
                b >>= 1;
                a *= a;
        }
        return result;
}

class LiftCoder{
private:
	int floors;

	// types
	string t_floor, t_baState;

	// constants
	string c_floor, c_baState;

	// predicates
	string /*p_push, p_served,*/ p_at, p_req, p_turn, p_check, p_move, p_called, p_currentBAstate, p_ok;

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
		for (int i = 1; i <= floors; i++) {
			cout << ";; AE((" << p_req << " " << c_floor << i <<  ") -> (" << p_at << " " << c_floor << i <<"))" << endl;
			cout << ";; &" << endl;
		}
		cout << ";; AE((" << p_at << " " << c_floor << 1 << ") | ( " <<  p_called << "))" << endl;		
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
		
		for (int i = 1; i <= floors; i++) {
			ss << "([] <> (" << p_req << "." << c_floor << i << " -> " << p_at << "." << c_floor << i << " ))";
			ss << " & ";
		}
		ss << "([] <> (" << p_at << "." << c_floor << 1 << " | " << p_called << " ))";		


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
		if(encoding != "cross"){
			push_actions();
			check_called_actions();
		}
		move_actions();
		no_op();
		if(encoding == "cross")
			cancel_called_cross();

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
		//cout << "\t\t\t\t(" << p_push << ")" << endl;
	}

	void push_effect_literals(int i){
		cout << "\t\t\t\t(not (" << p_turn << " " << c_floor << i << "))" << endl;
		if(i < floors){
			cout << "\t\t\t\t(" << p_turn << " " << c_floor << i+1 << ")" << endl;
		}
		else{
			cout << "\t\t\t\t(" << p_check <<")" << endl;
			//cout << "\t\t\t\t(not (" << p_push <<"))" << endl;
			cout << "\t\t\t\t(" << p_turn << " " << c_floor << "1)" << endl;
		}
	}

	void push_actions(){

		for (int i = 1; i <= floors; i++){
			if(encoding != "cross"){
				cout << "\t(:action push_" << c_floor << i  << endl;
				cout << "\t\t:precondition" << endl;
				cout << "\t\t\t(and " << endl;
				push_precondition_literals(i);
				cout << "\t\t\t" << ")" << endl;
				cout << "\t\t:effect" << endl;
				cout << "\t\t\t(and" << endl;
				push_effect_literals(i);
				cout << "\t\t\t\t(oneof"  << endl;
				cout << "\t\t\t\t\t(and)" << endl;
				cout << "\t\t\t\t\t(" << p_req << " " << c_floor << i << ")" << endl;
				cout << "\t\t\t\t)" << endl;
				cout << "\t\t\t)" << endl;
				cout << "\t)" << endl;
			}
	
			std::stringstream ss;
			ss << "push_" << c_floor << i;
			std::string header = ss.str();
			literal lit;				
			ss.str("");		       			
						
			cnf_formula prec;
			lit.sign() = true;
			ss << "(" <<p_turn<<" "<<c_floor<<i<<")";
			lit.name() = ss.str();
			ss.str("");		       			
			prec.push_back(lit);
			lit.sign() = false;
			ss << "(" <<p_check<<")";
			lit.name() = ss.str();
			ss.str("");		       			
			prec.push_back(lit);
			
			cnf_formula eff;
			lit.sign() = false;
			ss << "(" <<p_turn<<" "<<c_floor<<i<<")";
			lit.name() = ss.str();
			ss.str("");	
			eff.push_back(lit);
			if(i < floors){
				lit.sign() = true;
				ss << "(" <<p_turn<<" "<<c_floor<<i+1<<")";
				lit.name() = ss.str();
				ss.str("");	
				eff.push_back(lit);
			}		      
			else{
				lit.sign() = true;
				ss << "(" <<p_turn<<" "<<c_floor<<"1)";
				lit.name() = ss.str();
				ss.str("");	
				eff.push_back(lit);
				lit.sign() = true;
				ss << "(" <<p_check<<")";
				lit.name() = ss.str();
				ss.str("");		       			
				eff.push_back(lit);
			
			}

			lit.sign() = true;
			ss << "(oneof (and) ";			
			ss << "(" << p_req << " " << c_floor << i << ")";
			ss << " )";
			lit.name() = ss.str();
			eff.push_back(lit);		
			translator.add_action( header, prec, eff);
		}
	}

	void check_called_actions(){

		for (int i = 1; i <= floors; i++){
			if(encoding != "cross"){
				cout << "\t(:action check_called_true_" << c_floor << i << endl;
				cout << "\t\t:precondition" << endl;
				cout << "\t\t\t(and " << endl;
				cout << "\t\t\t\t(" << p_check << ")" << endl;
				cout << "\t\t\t\t(" << p_turn << " " << c_floor << i << ")" << endl;
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
				cout << "\t\t\t\t(not (" << p_req << " " << c_floor << i << "))" << endl;
				cout << "\t\t\t\t(" << p_check << ")" << endl;
				cout << "\t\t\t\t(" << p_turn << " " << c_floor << i << ")" << endl;
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

			std::stringstream ss;
			ss << "check_called_true_" << c_floor << i;
			std::string header = ss.str();
			literal lit;				
			ss.str("");		       			

			cnf_formula prec;
			lit.sign() = true;
			ss << "(" <<p_turn<<" "<<c_floor<<i<<")";
			lit.name() = ss.str();
			ss.str("");		       			
			prec.push_back(lit);
			lit.sign() = true;
			ss << "(" <<p_req<<" "<<c_floor<<i<<")";
			lit.name() = ss.str();
			ss.str("");		       			
			prec.push_back(lit);
			lit.sign() = true;
			ss << "(" <<p_check<<")";
			lit.name() = ss.str();
			ss.str("");		       			
			prec.push_back(lit);
			
			cnf_formula eff;
			lit.sign() = false;
			ss << "(" <<p_turn<<" "<<c_floor<<i<<")";
			lit.name() = ss.str();
			ss.str("");	
			eff.push_back(lit);
			lit.sign() = true;
			ss << "(" <<p_called<<")";
			lit.name() = ss.str();
			ss.str("");	
			eff.push_back(lit);
			if(i < floors){
				lit.sign() = true;
				ss << "(" <<p_turn<<" "<<c_floor<<i+1<<")";
				lit.name() = ss.str();
				ss.str("");	
				eff.push_back(lit);
			}		      
			else{
				lit.sign() = false;
				ss << "(" <<p_check<<")";
				lit.name() = ss.str();
				ss.str("");		       			
				eff.push_back(lit);
			
			}
			translator.add_action( header, prec, eff);



			ss << "check_called_false_" << c_floor << i;
			header = ss.str();
			ss.str("");		       			

			
			prec.clear();
			lit.sign() = true;
			ss << "(" <<p_turn<<" "<<c_floor<<i<<")";
			lit.name() = ss.str();
			ss.str("");		       			
			prec.push_back(lit);
			lit.sign() = false;
			ss << "(" <<p_req<<" "<<c_floor<<i<<")";
			lit.name() = ss.str();
			ss.str("");		       			
			prec.push_back(lit);
			lit.sign() = true;
			ss << "(" <<p_check<<")";
			lit.name() = ss.str();
			ss.str("");		       			
			prec.push_back(lit);
			
			eff.clear();
			lit.sign() = false;
			ss << "(" <<p_turn<<" "<<c_floor<<i<<")";
			lit.name() = ss.str();
			ss.str("");	
			eff.push_back(lit);
			if(i < floors){
				lit.sign() = true;
				ss << "(" <<p_turn<<" "<<c_floor<<i+1<<")";
				lit.name() = ss.str();
				ss.str("");	
				eff.push_back(lit);
			}		      
			else{
				lit.sign() = false;
				ss << "(" <<p_check<<")";
				lit.name() = ss.str();
				ss.str("");		       			
				eff.push_back(lit);
			
			}
			translator.add_action( header, prec, eff);

		}




	}

	void move_actions(){
		for (int i = 1; i < floors; i++){
			move_up(i);
			move_up_and_serve(i);
			
		}		
		for (int i = floors; i > 1; i--){
			move_down(i);
			move_down_and_serve(i);
		}
		for (int i = 1; i <= floors; i++)
			stay_and_serve(i);
	}


	void move_precondition(bool served, bool up, int from){
		cout << "\t\t:precondition" << endl;
		cout << "\t\t\t(and" << endl;
		cout << "\t\t\t\t(" << p_at << " " << c_floor << from << ")" << endl;
		cout << "\t\t\t\t";
		if(!served){
			cout << "(not ";
		}
			cout << "(" << p_req << " " << c_floor;
			if(up){
				cout << from + 1;
			}
			else{// down
				cout << from - 1;
			}
		cout << ")";
		if(!served){
			cout << ")";
		}
		cout << endl;

		if (up){
			cout << "\t\t\t\t(" << p_called << ") ;; can move up only if called" << endl;
		}
		cout << "\t\t\t\t(" << p_move << ")" << endl;
		cout << "\t\t\t)" << endl;
	}

	void move_precondition_cross(bool served, bool up, int from, cnf_formula& prec){

		literal lit;				
		std::stringstream ss;
		lit.sign() = true;
		ss << "(" << p_at << " " << c_floor << from << ")";
		lit.name() = ss.str();
		ss.str("");		       			
		prec.push_back(lit);
		
		if(!served){
			lit.sign() = false;
		}
			ss << "(" << p_req << " " << c_floor;
			if(up){
				ss << from + 1;
			}
			else{// down
				ss << from - 1;
			}
		ss << ")";
		lit.name() = ss.str();
		ss.str("");		       			
		prec.push_back(lit);

		if (up){
			lit.sign() = true;
			ss << "(" << p_called << ")";
			lit.name() = ss.str();
			ss.str("");		       			
			prec.push_back(lit);
		}
	}

	void move_effect(bool served, bool up, int from){
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

		
		if(served){
			//cout << "\t\t\t\t(" << p_served << ")" << endl;
			cout << "\t\t\t\t(not (" << p_req << " " << c_floor;
			if(up){
				cout << from + 1;
			}
			else{// down
				cout << from - 1;
			}
			cout << "))" << endl;
			
		}

		cout << "\t\t\t\t(not (" << p_move << "))" << endl;
		//cout << "\t\t\t\t(" << p_turn << " " << c_floor << "1)" << endl;		
		cout << "\t\t\t)" << endl;
	}

	void move_effect_cross(bool served, bool up, int from, cnf_formula& eff){
	
		literal lit;				
		std::stringstream ss;
		lit.sign() = false;
		ss << "(" <<p_at<<" "<<c_floor<<from<<")";
		lit.name() = ss.str();
		ss.str("");	
		eff.push_back(lit);

		lit.sign() = true;
		ss << "(" << p_at << " " << c_floor;
		if(up){
			ss << from + 1;
		}
		else{// down
			ss << from - 1;
		}
		ss << ")" << endl;
		lit.name() = ss.str();
		ss.str("");	
		eff.push_back(lit);

		
		if(served){
			lit.sign() = false;
			ss << "(" << p_req << " " << c_floor;
			if(up){
				ss << from + 1;
			}
			else{// down
				ss << from - 1;
			}
			ss << ")";
			lit.name() = ss.str();
			ss.str("");	
			eff.push_back(lit);
		}

		
	}
	

	void non_det_effect_cross(cnf_formula& cnf){
		literal lit;				
		std::stringstream ss;
		lit.sign() = true;
		ss << "(oneof (and) ";			
		int combinations = pow(2,floors) - 1;
	
		/**
		 * Generate all ((2^floors)-1) possible combination of requests
		 */
		
		for(int i = 0; i <= combinations; i++){
			ss << "(and ";
			for(int j = 0; j < floors; j++){
				int check = pow(2,j);
				if( (i & check) == check) // if j-th bit was true  
					ss << "(" << p_req << " " << c_floor << j+1 << ") ";
					
			}
			ss << " (called) )";
		}
		ss << " )";
		lit.name() = ss.str();
		cnf.push_back(lit);		

	}

	void move_up(int from){
		if(encoding != "cross"){
			cout << "\t(:action move_up_from_" << c_floor << from << endl;
			move_precondition(false,true, from);
			move_effect(false,true,from);
			cout << "\t)" << endl;
		}

		std::stringstream ss;
		ss << "move_up_from_" << c_floor << from;
		std::string header = ss.str();
		literal lit;				
		
		cnf_formula prec;		
		move_precondition_cross(false,true, from, prec);		
		cnf_formula eff;
		move_effect_cross(false,true,from, eff);
		non_det_effect_cross(eff);
		translator.add_action( header, prec, eff);
	}
	
	void move_down(int from){
		if(encoding != "cross"){
			cout << "\t(:action move_down_from_" << c_floor << from << endl;
			move_precondition(false,false, from);
			move_effect(false,false,from);
			cout << "\t)" << endl;
		}

		std::stringstream ss;
		ss << "move_down_from_" << c_floor << from;
		std::string header = ss.str();
		literal lit;				
		
		cnf_formula prec;		
		move_precondition_cross(false,false, from, prec);		
		cnf_formula eff;
		move_effect_cross(false,false,from, eff);
		non_det_effect_cross(eff);
		translator.add_action( header, prec, eff);
	}



	void move_up_and_serve(int from){
		
		if(encoding != "cross"){
			cout << "\t(:action move_up_and_serve_from_" << c_floor << from << endl;
			move_precondition(true,true, from);
			move_effect(true,true,from);
			cout << "\t)" << endl;
		}
		std::stringstream ss;
		ss << "move_up_and_serve_from_" << c_floor << from;
		std::string header = ss.str();
		literal lit;				
		
		cnf_formula prec;		
		move_precondition_cross(true,true, from, prec);		
		cnf_formula eff;
		move_effect_cross(true,true,from, eff);
		non_det_effect_cross(eff);
		translator.add_action( header, prec, eff);
	}

	void move_down_and_serve(int from){

		if(encoding != "cross"){
			cout << "\t(:action move_down_and_serve_from_" << c_floor << from << endl;
			move_precondition(true,false, from);
			move_effect(true,false,from);
			cout << "\t)" << endl;
		}

		std::stringstream ss;
		ss << "move_down_and_serve_from_" << c_floor << from;
		std::string header = ss.str();
		literal lit;				
		
		cnf_formula prec;		
		move_precondition_cross(true,false, from, prec);		
		cnf_formula eff;
		move_effect_cross(true,false,from, eff);
		non_det_effect_cross(eff);
		translator.add_action( header, prec, eff);
	}
	
	void cancel_called_cross(){
		std::stringstream ss;
		ss << "cancel_called";
		std::string header = ss.str();
		literal lit;				
		ss.str("");		       			

		
		cnf_formula prec;
		for(int i = 1; i <= floors; i++ ){		
			lit.sign() = false;
			ss << "(" <<p_req<<" "<<c_floor<<i<<")";
			lit.name() = ss.str();
			ss.str("");		       			
			prec.push_back(lit);
		}
		
		lit.sign() = true;
		ss << "(" <<p_called<<")";
		lit.name() = ss.str();
		ss.str("");		       			
		prec.push_back(lit);
			
		cnf_formula eff;
		lit.sign() = false;
		ss << "(" <<p_called<<")";
		lit.name() = ss.str();
		ss.str("");		       			
		eff.push_back(lit);
		non_det_effect_cross(eff);
		translator.add_action( header, prec, eff);
	
	}


	void stay_and_serve(int from){
		if(encoding != "cross"){

			cout << "\t(:action stay_and_serve_at_" << c_floor << from << endl;
			cout << "\t\t:precondition" << endl;
			cout << "\t\t\t(and" << endl;
			cout << "\t\t\t\t(" << p_at << " " << c_floor << from << ")" << endl;		
			cout << "\t\t\t\t(" << p_req << " " << c_floor << from << ")" << endl;
			cout << "\t\t\t\t(" << p_called << ") ;; can move up only if called" << endl;		
			cout << "\t\t\t\t(" << p_move << ")" << endl;
			cout << "\t\t\t)" << endl;
	
			cout << "\t\t:effect" << endl;
			cout << "\t\t\t(and" << endl;
		

			//cout << "\t\t\t\t(" << p_served << ")" << endl;
			cout << "\t\t\t\t(not (" << p_req << " " << c_floor << from << "))" << endl;
			cout << "\t\t\t\t(not (" << p_move << "))" << endl;
			cout << "\t\t\t\t(" << p_turn << " " << c_floor << "1)" << endl;		
			cout << "\t\t\t)" << endl;

			cout << "\t)" << endl;

		}
		std::stringstream ss;
		ss << "stay_and_serve_at_" << c_floor << from;
		std::string header = ss.str();
		literal lit;				
		ss.str("");		       			

		cnf_formula prec;
		lit.sign() = true;
		ss << "(" <<p_at<<" "<<c_floor<<from<<")";
		lit.name() = ss.str();
		ss.str("");		       			
		prec.push_back(lit);
		lit.sign() = true;
		ss << "(" <<p_req<<" "<<c_floor<<from<<")";
		lit.name() = ss.str();
		ss.str("");		       			
		prec.push_back(lit);
		lit.sign() = true;
		ss << "(" <<p_called<<")";
		lit.name() = ss.str();
		ss.str("");		       			
		prec.push_back(lit);
			
		cnf_formula eff;
		lit.sign() = false;
		ss << "(" <<p_req<<" "<<c_floor<<from<<")";
		lit.name() = ss.str();
		ss.str("");	
		eff.push_back(lit);
		lit.sign() = true;
		ss << "(" <<p_turn << " " << c_floor <<"1)";
		lit.name() = ss.str();
		ss.str("");	
		eff.push_back(lit);
		non_det_effect_cross(eff);
		translator.add_action( header, prec, eff);

	
	}



	void no_op(){
		if(encoding != "cross"){

		cout << "\t(:action no_op" << endl;
		cout << "\t\t:precondition" << endl;
		cout << "\t\t\t(and (" << p_move << "))" << endl;
		cout << "\t\t:effect" << endl;
		cout << "\t\t\t(and (not (" << p_move << ")))" << endl;
		cout << "\t)" << endl;
		}
		
		std::stringstream ss;
		ss << "no_op_";
		std::string header = ss.str();
		literal lit;				
			
		cnf_formula prec;
		cnf_formula eff;
		non_det_effect_cross(eff);
		translator.add_action( header, prec, eff);
		
	}

	std::string buchi_precondition_literals2str(){
		std::stringstream ss;
		//ss << "\t\t\t\t(not (" << p_push << "))" << endl;
		for (int i = 1; i <= floors; i++){
			ss << "\t\t\t\t(not (" << p_turn  << " " << c_floor << i << "))" << endl;						
		}
		ss << "\t\t\t\t(not (" << p_check  << "))" << endl;			
		ss << "\t\t\t\t(not (" << p_move << "))" << endl;
		return ss.str();
	}

	std::string buchi_effect_literals2str(){
		std::stringstream ss;
		ss << "\t\t\t\t(" << p_turn << " " << c_floor << "1)" << endl;
		//ss << "\t\t\t\t(" << p_push << ")" << endl;
		ss << "\t\t\t\t(not (" << p_called << ")) ;; reset" << endl;
		return ss.str();
	}




public:
	std::string encoding;

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
		//p_push = "push";
		//p_served = "served";
		p_currentBAstate = "currentBAstate";
		p_ok = "ok";
		
		encoding = "cross";

	}


	void out(){
		header();
		define_ltl_goal();
		domain();
	}

};

void help(string progname){
	cout << endl << "command line:" << progname << " <num_floors>  <cross/sequential>" << endl << endl;
}


int main(int argc, char* argv[]){

	/* Parameters:
	 * argv[1] = num of floors (required)
	 */

	// Check that an input string is provided
	if(argc < 3){
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
	p.encoding = argv[2];

	p.out();

	return 0;
}
