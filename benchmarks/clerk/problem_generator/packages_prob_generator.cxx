/*
 * Author: Nir Lipovezky && Fabio Patrizi
 * January 2013
 *
 */
// initially = p1 .. pn etc.

#include <iostream>
#include <sstream>

using namespace std;


void help(string progname){
	cout << endl << "command line:" << progname << " <num_pkg(>=1)>" << endl << endl;
}


int main(int argc, char* argv[]){

	/* Parameters:
	 * argv[1] = num of packages (required)
	 */

	// Check that an input string is provided
	if(argc < 2){
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


	cout << "(define (problem packages)" << endl;
	cout << "\t(:domain packages)" << endl;
	cout << "\t(:objects )" << endl;
	cout << "\t(:INIT" << endl;
	for(int i = 1; i <= npkg; i++ )	
		cout << "\t\t(in_store p"<<i<<")" << endl;
	cout << "\t\t(currentBAstate BA-S0)" << endl;
	cout << "\t\t(pkg_served)" << endl;
	cout << "\t)" << endl;
	cout << "\t(:goal (and (ok)))" << endl;
	cout << ")" << endl;

	return 0;
}
