#include <iostream>
#include <vector>
#include "k-sat.h"

using namespace std;

int main() {
    SatSolver s;
    s.initialize();
    Var a = s.newVar();
    Var b = s.newVar();
    Var c = s.newVar();
    s.addCNF({Lit(a), Lit(b), ~Lit(c)});
    s.addCNF({~Lit(a), Lit(b), Lit(c)});
    s.addCNF({~Lit(a), Lit(b), ~Lit(c)});

    cout << s.solve() << endl;
    cout << "-------" << endl;
    cout << s.getValue(a) << endl;
    cout << s.getValue(b) << endl;
    cout << s.getValue(c) << endl;
    cout << "-------" << endl;

    s.assumeProperty(b, false);
    cout << s.assumpSolve() << endl;
    s.assumeRelease();

    s.addCNF({Lit(a), Lit(b), Lit(c)});
    cout << s.solve() << endl;
    s.assumeProperty(b, false);

    cout << s.assumpSolve() << endl;
    // cout << s.assumpSolve() << endl;

}