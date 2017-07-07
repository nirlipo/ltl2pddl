#ifndef __LTL2PDDL__
#define __LTL2PDDL__

#include <tgbaalgos/stats.hh>
#include <tgbaalgos/reachiter.hh>
#include <tgba/tgba.hh>
#include <ltlast/atomic_prop.hh>
#include <ostream>
#include <fstream>
#include <sstream>

/**
 * LITERAL
 */
class literal{
public:
	literal(){}
	literal( std::string& n, bool s)
		: m_name(n), m_sign(s) 
	{}
	~literal(){}
	
	std::string& name() {return m_name;}
	bool& sign() {return m_sign;}
private:
	std::string m_name;
	bool        m_sign;
};


inline std::ostream& operator<<(std::ostream &os, literal &lit)
{
	if( lit.sign() == false ) 
		os <<"(not "<< lit.name() << ") ";
	else
		os << lit.name() << " ";		
	
	return os;
}

/**
 * CNF_FORMULA
 */
typedef std::vector<literal> cnf_formula;

inline std::ostream& operator<<(std::ostream &os, cnf_formula &cnf)
{
	for(cnf_formula::iterator it = cnf.begin();
	    it != cnf.end(); it++){		
		 if( it->sign() == false ) 
			 os <<"(not "<< it->name() << ") ";
		 else
			 os << it->name() << " ";		
	}
	return os;
}

/**
 * STRIPS ACTION
 */
class action{
public:

	action(std::string& h, cnf_formula& prec, cnf_formula& eff)
		: m_header( h ), m_precondition( prec ), m_effect( eff )
	{}
	~action(){}
	
	std::string& header() {return m_header;}
	cnf_formula& prec() {return m_precondition;} 
	cnf_formula& eff() {return m_effect;} 

private:
	std::string m_header;
	cnf_formula m_precondition;
	cnf_formula m_effect;
};

inline std::ostream& operator<<(std::ostream &os, action &a)
{
	os << a.header() << " -- " << a.prec()<< " --> " << a.eff();
	return os;
}


/**
 * TRANSITION OF BUCHI AUTOMATA
 */
class ba_transition{
public:

	ba_transition(unsigned src, unsigned end, cnf_formula& cond)
		: m_src_state_idx( src ), m_end_state_idx( end ), m_condition( cond )
	{}
	~ba_transition(){}
	
	unsigned src() {return m_src_state_idx;}
	unsigned end() {return m_end_state_idx;}
	cnf_formula& cond() {return m_condition;}

private:
	unsigned m_src_state_idx;
	unsigned m_end_state_idx;
	cnf_formula m_condition;
};

inline std::ostream& operator<<(std::ostream &os, ba_transition &t)
{
	os << t.src() << " -- " << t.cond()<< " --> " << t.end();
	return os;
}

/**
 * LTL2PDDL TRANSLATOR
 */
class ltl2pddl {
	
	/**
	 * ITERATOR OVER SPOT REPRESENTATION OF TGBA
	 */
	class ba_iter: public spot::tgba_reachable_iterator_breadth_first{
	public:
		ba_iter(const spot::tgba* a, std::ostream& os)
			: tgba_reachable_iterator_breadth_first(a), m_os(os)
		{
		}

		void      start();
		void      process_state(const spot::state* s, int, spot::tgba_succ_iterator* si);		
		std::set<unsigned>&           acc_states() {return m_acceptance_states;}
		std::vector< ba_transition* > transitions_copy(){return m_transitions;}
		std::vector< ba_transition* >& transitions(){return m_transitions;}
	private:
		std::ostream& print_acc(bdd acc, bool& is_acc);
		void ground_transition(unsigned src, unsigned end, std::string cond );
		unsigned str2unsigned( std::string& str ){
			unsigned value;
			m_ss_buff << str;
			m_ss_buff >> value;
			m_ss_buff.clear();
			return value;
		}

		std::ostream& m_os;
		std::stringstream m_ss_buff;
		
		std::set<unsigned>               m_acceptance_conditions;
		std::set<unsigned>               m_states;
		std::set<unsigned>               m_acceptance_states;
		std::vector< ba_transition* >    m_transitions;
	};
	
public:
	ltl2pddl(): m_deterministic(false)
	{
	}

	~ltl2pddl(){}

       
	/**
	 * MAIN FUNCTIONS OF TRANSLATOR
	 */
	void     parse_ltl(std::string& input);
	void     generate_pddl_encoding(std::ostream& os, std::string& state_pred, std::string& state_constant, std::string& common_precs, std::string& common_effects);
	void     generate_pddl_encoding_fip(std::ostream& os, std::string& state_pred, std::string& state_constant, std::string& common_precs, std::string& common_effects);
	
	
	void     generate_pddl_encoding_xproduct(std::ostream& os, std::string& state_pred, std::string& state_constant, std::string& common_precs, std::string& common_effects);
	void     generate_pddl_encoding_xproduct_fip(std::ostream& os, std::string& state_pred, std::string& state_constant, std::string& common_precs, std::string& common_effects);
	
	void     add_action( std::string& header, cnf_formula& precondition, cnf_formula& effect){ m_actions.push_back( new action(header,precondition,effect) );}
	
	bool     ba_deterministic() const {return m_deterministic;}
	bool     is_acceptance_ba_state( unsigned bas ) {return m_acceptance_states[bas];}
	unsigned ba_states() const {return m_ba_stats.states;}
	unsigned ba_transitions() const {return m_ba_stats.transitions;}
	unsigned ba_sub_transitions() const {return m_ba_stats.sub_transitions;}
	
private:
	bool                             m_deterministic;
	spot::tgba_sub_statistics        m_ba_stats;
	
	std::vector<bool>                m_acceptance_states;
	std::vector< ba_transition* >    m_transitions;
	std::vector< action* >           m_actions;
	
	std::ofstream                    m_log;
};

#endif //ltl2pddl.hxx
