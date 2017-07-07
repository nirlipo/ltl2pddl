#include "ltl2pddl.hxx"

#include <boost/tokenizer.hpp>
#include <string>
#include <cstdlib>

#include <ltlparse/public.hh>
#include <tgbaalgos/ltl2tgba_fm.hh>

#include <tgbaalgos/save.hh>
#include <tgbaalgos/degen.hh>
#include <tgbaalgos/stats.hh>
#include <tgbaalgos/isdet.hh>
#include <tgbaalgos/postproc.hh>
#include <tgba/bdddict.hh>



#include <tgba/bddprint.hh>
#include <ltlvisit/simplify.hh>
#include <ltlvisit/tostring.hh>
#include <ltlast/atomic_prop.hh>
#include <misc/escape.hh>

/**
 * Use "." symbol to separate predicate and variable.
 * e.g. PDDL: (predicate var) --> predicate.var
 * e.g. PDDL: (predicate var1 var2) --> predicate.var1.var2
 */

//void     ltl2pddl::add_action( std::string& header, cnf_formula& precondition, cnf_formula& effect){	
//}


void ltl2pddl::generate_pddl_encoding( std::ostream& os, std::string& state_pred, std::string& state_constant, std::string& common_precs, std::string& common_effects )
{
	
	for(unsigned i = 0; i < m_transitions.size(); i++){
		ba_transition* t = m_transitions[i];
		os << "\t(:action buchi_move_from_"<< state_constant << t->src() << "-" << t->end() << "_" << i << std::endl;
		os << "\t\t:precondition" << std::endl;
		os << "\t\t\t(and" << std::endl;
		os << common_precs;
		os << "\t\t\t\t(" << state_pred << " " << state_constant << t->src() << ")" << std::endl;
		for(cnf_formula::iterator it = t->cond().begin();
		    it != t->cond().end(); it++){
			os << "\t\t\t\t" << *it << std::endl;
		}
		
		os << "\t\t\t)" << std::endl;

		os << "\t\t:effect" << std::endl;
		os << "\t\t\t(and" << std::endl;
		os << common_effects;
		if (t->src() != t->end()){
			os << "\t\t\t\t(not (" << state_pred << " " << state_constant << t->src() << "))" << std::endl;
			os << "\t\t\t\t(" << state_pred << " " << state_constant << t->end() << ")" << std::endl;
		}			
		if( is_acceptance_ba_state( t->end() ) )
			os << "\t\t\t\t(oneof (and) (ok))" << std::endl;
		os << "\t\t\t)" << std::endl;
		os << "\t)" << std::endl;



	}

	
}

void ltl2pddl::generate_pddl_encoding_xproduct( std::ostream& os, std::string& state_pred, std::string& state_constant, std::string& common_precs, std::string& common_effects )
{

	for(unsigned i = 0; i < m_transitions.size(); i++){
		for(unsigned j = 0; j < m_actions.size(); j++){
			ba_transition* t = m_transitions[i];
			os << "\t(:action "<< m_actions[j]->header() << "_buchi_move_from_"<< state_constant << t->src() << "-" << t->end() << "_" << i << std::endl;
			os << "\t\t:precondition" << std::endl;
			os << "\t\t\t(and" << std::endl;
			os << common_precs;
			os << "\t\t\t\t(" << state_pred << " " << state_constant << t->src() << ")" << std::endl;
			
			for(cnf_formula::iterator it = m_actions[j]->prec().begin();
			    it != m_actions[j]->prec().end(); it++){
				os << "\t\t\t\t" << *it << std::endl;
			}
		
			
			for(cnf_formula::iterator it = t->cond().begin();
			    it != t->cond().end(); it++){
				os << "\t\t\t\t" << *it << std::endl;
			}
		
			os << "\t\t\t)" << std::endl;

			os << "\t\t:effect" << std::endl;
			os << "\t\t\t(and" << std::endl;
			os << common_effects;
			if (t->src() != t->end()){
				os << "\t\t\t\t(not (" << state_pred << " " << state_constant << t->src() << "))" << std::endl;
				os << "\t\t\t\t(" << state_pred << " " << state_constant << t->end() << ")" << std::endl;
			}
			for(cnf_formula::iterator it = m_actions[j]->eff().begin();
			    it != m_actions[j]->eff().end(); it++){
				os << "\t\t\t\t" << *it << std::endl;
			}

			if( is_acceptance_ba_state( t->end() ) )
				os << "\t\t\t\t(oneof (and) (ok))" << std::endl;
			os << "\t\t\t)" << std::endl;
			os << "\t)" << std::endl;

		}

	}

	
}

void ltl2pddl::generate_pddl_encoding_fip( std::ostream& os, std::string& state_pred, std::string& state_constant, std::string& common_precs, std::string& common_effects )
{
	
	for(unsigned i = 0; i < m_transitions.size(); i++){
		ba_transition* t = m_transitions[i];
		if( !is_acceptance_ba_state(t->end()) )
			os << "\t(:action buchi_move_from_"<< state_constant << t->src() << "-" << t->end() << "_" << i << std::endl;
		else
			os << "\t(:action D_1_buchi_move_from_"<< state_constant << t->src() << "-" << t->end() << "_" << i << std::endl;
		os << "\t\t:precondition" << std::endl;
		os << "\t\t\t(and" << std::endl;
		os << common_precs;
		os << "\t\t\t\t(" << state_pred << " " << state_constant << t->src() << ")" << std::endl;
		for(cnf_formula::iterator it = t->cond().begin();
		    it != t->cond().end(); it++){
			os << "\t\t\t\t" << *it << std::endl;
		}
		
		os << "\t\t\t)" << std::endl;

		os << "\t\t:effect" << std::endl;
		os << "\t\t\t(and" << std::endl;
		os << common_effects;
		os << "\t\t\t\t(not (" << state_pred << " " << state_constant << t->src() << "))" << std::endl;
		os << "\t\t\t\t(" << state_pred << " " << state_constant << t->end() << ")" << std::endl;					
		os << "\t\t\t)" << std::endl;
		os << "\t)" << std::endl;


		if( is_acceptance_ba_state(t->end()) ){
			os << "\t(:action D_2_buchi_move_from_"<< state_constant << t->src() << "-" << t->end() << "_" << i << std::endl;
			os << "\t\t:precondition" << std::endl;
			os << "\t\t\t(and" << std::endl;
			os << common_precs;
			os << "\t\t\t\t(" << state_pred << " " << state_constant << t->src() << ")" << std::endl;
			for(cnf_formula::iterator it = t->cond().begin();
			    it != t->cond().end(); it++){
				os << "\t\t\t\t" << *it << std::endl;
			}
			
			os << "\t\t\t)" << std::endl;
			
			os << "\t\t:effect" << std::endl;
			os << "\t\t\t(and" << std::endl;
			os << common_effects;
			os << "\t\t\t\t(not (" << state_pred << " " << state_constant << t->src() << "))" << std::endl;
			os << "\t\t\t\t(" << state_pred << " " << state_constant << t->end() << ")" << std::endl;					
			
			os << "\t\t\t\t(ok)" << std::endl;
			os << "\t\t\t)" << std::endl;
			os << "\t)" << std::endl;
		}
			

	}

	
}

void ltl2pddl::generate_pddl_encoding_xproduct_fip( std::ostream& os, std::string& state_pred, std::string& state_constant, std::string& common_precs, std::string& common_effects )
{


	
}


void ltl2pddl::parse_ltl( std::string& input ){

	m_log.open("parse_ltl.log");
	/**
	 * Below is the code for this call (spot/src/tgbatest/ltl2tgba):
	 * "ltl2tgba -D --stats=%n input"
	 */


	bool debug_opt = false;
	spot::ltl::environment& env(spot::ltl::default_environment::instance());	
	const spot::ltl::formula* f = 0;
	const spot::tgba* a = 0;
	spot::postprocessor post;
	spot::ltl::ltl_simplifier simpl;
	bool exprop = true;
		
	post.set_level(spot::postprocessor::High);
	post.set_type(spot::postprocessor::TGBA);
	post.set_pref(spot::postprocessor::Deterministic);


	/**
	 * Parsing LTL Formula
	 */

	spot::ltl::parse_error_list pel;
	f = spot::ltl::parse(input, pel, env, debug_opt);
	spot::ltl::format_parse_errors(std::cerr, input, pel);

	if(f){
		const spot::ltl::formula* res = simpl.simplify(f);
		f->destroy();
		f = res;

		/** 
		 * This helps ltl_to_tgba_fm() to order BDD variables in a more
		 * natural way (improving the degeneralization).
		 */
		simpl.clear_as_bdd_cache();

		m_log << f->dump() << std::endl << std::endl;
		/**
		 * -x    try to produce a more deterministic automaton (implies -f)
		 */

		a = ltl_to_tgba_fm(f, simpl.get_dict(), exprop);
		/**
		 * -DS   degeneralize the automaton as an SBA
		 */
		
		a = post.run(a, f);
		a = spot::degeneralize(a);
		
		/**
		 * Check if the buchi automata is deterministic 
		 */
		m_deterministic = spot::is_deterministic(a);
		   
		/**
		 * -b    output the automaton in the format of spot
		 */
		//spot::tgba_save_reachable(ss, a);
		std::stringstream ss;
		ba_iter it_ba( a, ss );
		it_ba.run();
		
		m_log<< ss.str() << std::endl;
		
		/**
		 * -kt   display statistics on the automaton (size + subtransitions)
		 */
		m_ba_stats = spot::sub_stats_reachable(a);
				
		if( ba_deterministic() )
			m_log << "Deterministic Automaton :)" << std::endl << std::endl;		
		else
			m_log << "Nondeterministic Automaton :(" << std::endl << std::endl;

		m_ba_stats.dump(m_log);

		/**
		 * Complete data structures of ba
		 */
		
		m_acceptance_states.resize( m_ba_stats.states, false );
		
		std::set<unsigned>& acc = it_ba.acc_states();
		for(std::set<unsigned>::iterator it = acc.begin();
		    it != acc.end(); it++)
			m_acceptance_states[*it]=true;

		
		m_log << "Acceptance states ids: ";
		for(unsigned i = 0; i < m_acceptance_states.size(); i++)
			if(m_acceptance_states[i])
				m_log<< i << ", ";
		m_log<<std::endl<<std::endl;
		
		m_transitions = it_ba.transitions_copy();
		
		m_log << "Transitions: " << std::endl;
		for(unsigned i = 0; i < m_transitions.size(); i++)			
			m_log << *(m_transitions[i]) << std::endl;
	}

	delete a;
	f->destroy();
	m_log.close();
}



void ltl2pddl::ba_iter::start()
{

	bool is_acc;
	m_os << "acc =";
	print_acc(aut_->all_acceptance_conditions(), is_acc) << ";\n";
}


void ltl2pddl::ba_iter::ground_transition(unsigned src, unsigned end, std::string cond )
{
	enum{begin_cnf, lit_pred_name, lit_var_name,lit_sign, end_cnf} cnf_status = begin_cnf;
	cnf_formula cnf;
	literal lit;
	boost::char_delimiters_separator<char> delimiter(true,"< > : .",", \\ \" ");
	boost::tokenizer<boost::char_delimiters_separator<char> > tok(cond, delimiter);

	//std::cout<< cond << std::endl;

	/**
	 * If cond T, there is no condition, like an absorbing state
	 */
	if(cond == "T"){		
		m_transitions.push_back( new ba_transition(src,end,cnf) );
		return;
	}

	for(boost::tokenizer<boost::char_delimiters_separator<char> >::iterator beg=tok.begin(); beg!=tok.end();++beg){
		cnf_status = (*beg == "<") ? begin_cnf :  (*beg == ":") ? lit_sign :  (*beg == ">") ? end_cnf : (*beg == ".") ? lit_var_name : lit_pred_name ;
		switch (cnf_status){
		case begin_cnf:			
			cnf.clear();
			//m_log << *beg << "\n";			
			break;
		case lit_pred_name:
			lit.name() = "(" + *beg;
			//m_log << *beg << "\n";
			break;
		case lit_var_name:
			beg++;
			lit.name() += " " + *beg;
			//m_log << *beg << "\n";
			break;
		case lit_sign:
			lit.name() += ")";
			beg++;
			if(*beg == "0") lit.sign() = false;
			else lit.sign() = true;			
			cnf.push_back(lit);
			//m_log << *beg << "\n";			
			break;
		case end_cnf:
			m_transitions.push_back( new ba_transition(src,end,cnf) );
			//m_log << *beg << "\n";			
			break;

		}
	}
}

void ltl2pddl::ba_iter::process_state(const spot::state* s, int, spot::tgba_succ_iterator* si)
{
	unsigned src;
	unsigned end;
	std::string end_str,cond;
	bool is_acc;
	const spot::bdd_dict* d = aut_->get_dict();
	std::string cur = spot::escape_str(aut_->format_state(s));

	/**
	 * Source State
	 */
	src = str2unsigned( cur );	
	m_states.insert(src);

	
	for (si->first(); !si->done(); si->next()){
		spot::state* dest = si->current_state();
		end_str = spot::escape_str(aut_->format_state(dest));
		end = str2unsigned( end_str );
		
		/**
		 * Ignore transitions that go to the same state
		 */
		//		if(src == end) continue;
		
		m_os << "\"" << cur << "\", \"";

		/**
		 * End State
		 */
		spot::escape_str(m_os, aut_->format_state(dest));
		m_os << "\", \"";

		
		/**
		 * Get Conditions for the transition
		 */
		spot::escape_str(m_os, bdd_format_formula(d, si->current_condition()));
		m_os << "\",";
		cond = spot::escape_str(bdd_format_formula(d, si->current_condition()));

		m_os << "\"";
		cond = spot::escape_str(bdd_format_set(d, si->current_condition()));
	
		/**
		 * Ground Conditions of transition, convert into CNF
		 */

		ground_transition( src, end, cond );

		print_acc(si->current_acceptance_conditions(), is_acc) << ";\n";

		
		/**
		 * Check if Source state is an Acceptance state
		 */
		if(is_acc)
			m_acceptance_states.insert( src );
				
		
		dest->destroy();
	}
}

std::ostream& ltl2pddl::ba_iter::print_acc(bdd acc, bool& is_acc)
{
	const spot::bdd_dict* d = aut_->get_dict();
	is_acc = false;
	while (acc != bddfalse){
		bdd cube = bdd_satone(acc);
		acc -= cube;
		const spot::ltl::formula* f = d->oneacc_to_formula(cube);
		std::string s = spot::ltl::to_string(f);
		if (spot::ltl::is_atomic_prop(f) && s[0] == '"'){
			// Unquote atomic propositions.
			s.erase(s.begin());
			s.resize(s.size() - 1);
		}
		m_os << " \"";
		spot::escape_str(m_os, s)  << "\"";

		std::string acc_str = spot::escape_str(s);
		m_acceptance_conditions.insert( str2unsigned( acc_str ) );
		is_acc = true;
		
	}
	return m_os;
}

