#include "bmatchSolver.h"
#include <string>
#include <map>
#include <unordered_map>

void
BMatchSolver::init(ifstream& portMapping, ifstream& aag1, ifstream& aag2, ostream& out) {

    std::ios::sync_with_stdio(false);
    std::cin.tie(0);

    outputSolver.initialize();
    matrixSolver.initialize();
    miterSolver.initialize();

    genCircuitModel(portMapping, aag1, aag2);
    buildMatrix();
    genMiterConstraint();
}

void
BMatchSolver::genFuncSupport(istream& in) {
    /*
    cout << "--------------- Circuit 1 -----------------" << endl;
    cout << "Input:" << endl;
    for (int j = 0; j < x.size(); ++j) {
        cout << x[j].getName() << " ";
    }
    cout << endl;
    cout << "Output:" << endl;
    for (int j = 0; j < f.size(); ++j) {
        cout << f[j].getName() << " ";
    }
    cout << endl;

    cout << "--------------- Circuit 2 -----------------" << endl;
    cout << "Input:" << endl;
    for (int i = 0; i < y.size(); ++i) {
        cout << y[i].getName() << " ";
    }
    cout << endl;
    cout << "Output:" << endl;
    for (int i = 0; i < g.size(); ++i) {
        cout << g[i].getName() << " ";
    }
    cout << endl;
    cout << endl;
    */

    for (int j = 0; j < f.size(); ++j) {
        set<Var> supports;
        string funcSuppVec;

        in >> funcSuppVec;
        assert(funcSuppVec.size() == x.size());
        for (int k = 0; k < x.size(); ++k) {
            if (funcSuppVec[k] == '1') {
                supports.insert(k);
                x[k].addSupport(j);
                f[j].addSupport(k);
            }
        }
        // fSupport.push_back(supports);
    }
    for (int i = 0; i < g.size(); ++i) {
        set<Var> supports;
        string funcSuppVec;

        in >> funcSuppVec;
        assert(funcSuppVec.size() == y.size());
        for (int k = 0; k < y.size(); ++k) {
            if (funcSuppVec[k] == '1') {
                supports.insert(k);
                y[k].addSupport(i);
                g[i].addSupport(k);
            }
        }
        // gSupport.push_back(supports);
    }
    return;
}

class Hash {
public:
    size_t operator() (const pair<int, int>& p) const {
        return p.first ^ p.second;
    }
};

void 
BMatchSolver::inputPreprocess() {
    cerr << "inputPreprocess start..." << endl;

    for (int j = 0; j < x.size(); ++j) {
        for (int i = 0; i < y.size(); ++i) {
            if (x[j].nofSupport() != y[i].nofSupport()) {
                matrixSolver.assertProperty(a[i][j].matrixVar, false);
                matrixSolver.assertProperty(b[i][j].matrixVar, false);
            }

        }
    }
/*
    map<int, int> xSupp;
    map<int, int> ySupp;
    for (int j = 0; j < x.size(); ++j)
        xSupp[x[j].nofSupport()] ++;
    for (int i = 0; i < y.size(); ++i)
        ySupp[y[i].nofSupport()] ++;
    map<int, int>::iterator itx;
    map<int, int>::iterator ity;
    if (xSupp.size() != ySupp.size()) {
        cerr << "not equal" << endl;
        return;
    }
    itx = xSupp.begin();
    ity = ySupp.begin();
    while (itx != xSupp.end()) {
        if (itx->first != ity->first) {
            cerr << "not equal in first" << endl;
            return;
        }
        if (itx->second != ity->second) {
            cerr << "not equal in second" << endl;
            return;
        }
        itx ++;
        ity ++;
    }
//*/

/*  
    unordered_map<PortHashKey, vector<int>, PortHashFunc> portHash;
    int count = 0;
    for (int j = 0; j < x.size(); ++j) {
        portHash[PortHashKey(x, x[j])].push_back(j);
        if (portHash[PortHashKey(x, x[j])].size() != 1) {
            count ++;
        }
    }
    cout << "equal: " << x.size() - count << endl;
    cout << "not equal: " << count << endl;

    for (int i = 0; i < y.size(); ++i) {
        set<int> candidate(portHash[PortHashKey(y, y[i])].begin(), portHash[PortHashKey(y, y[i])].end());
        if (candidate.empty()) {
            cerr << "EMPTY!" << endl;
            return;
        }
        for (int j = 0; j < x.size(); ++j) {
            if (candidate.find(j) != candidate.end()) {
                matrixSolver.assertProperty(a[i][j].matrixVar, false);
                matrixSolver.assertProperty(b[i][j].matrixVar, false);
            }
        }
    }
*/   
    cerr << "inputPreprocess end." << endl;
}

void
BMatchSolver::outputPreprocess() {
    cerr << "outputPreprocess start..." << endl;
    for (int j = 0; j < f.size(); ++j) {
        for (int i = 0; i < g.size(); ++i) {
            if (f[j].nofSupport() != g[i].nofSupport()) {
                outputSolver.assertProperty(outputC[i][j], false);
                outputSolver.assertProperty(outputD[i][j], false);
            }
        }
    }

/*
    map<int, int> fSupp;
    map<int, int> gSupp;
    for (int j = 0; j < f.size(); ++j)
        fSupp[f[j].nofSupport()] ++;
    for (int i = 0; i < g.size(); ++i)
        gSupp[g[i].nofSupport()] ++;
    map<int, int>::iterator itf;
    map<int, int>::iterator itg;
    if (fSupp.size() != gSupp.size()) {
        cerr << "not equal" << endl;
        return;
    }
    itf = fSupp.begin();
    itg = gSupp.begin();
    while (itf != fSupp.end()) {
        if (itf->first != itg->first) {
            cerr << "not equal in first" << endl;
            return;
        }
        if (itf->second != itg->second) {
            cerr << "not equal in second" << endl;
            return;
        }
        itf ++;
        itg ++;
    }
//*/
/*
    unordered_map<PortHashKey, vector<int>, PortHashFunc> portHash;
    int count = 0;
    for (int j = 0; j < f.size(); ++j) {
        portHash[PortHashKey(x, f[j])].push_back(j);
    }

    for (int i = 0; i < g.size(); ++i) {
        set<int> candidate(portHash[PortHashKey(y, g[i])].begin(), portHash[PortHashKey(y, g[i])].end());
        if (candidate.empty()) {
            cerr << "------------------- EMPTY! -------------------------" << endl;
            return;
        }
        for (int j = 0; j < g.size(); ++j) {
            if (candidate.find(j) == candidate.end()) {
                outputSolver.assertProperty(outputC[i][j], false);
                outputSolver.assertProperty(outputD[i][j], false);
            }
        }
    }
//*/
    cerr << "outputPreprocess end" << endl;
}

void 
BMatchSolver::run() {
    cerr << "start run..." << endl;
    scoreGte((g.size() + f.size()));
    while (1) {
        if (bestScore == g.size() + f.size()) {
            cout << "This must be the OPT with (#output_port(Circuit I) + "
                    "#output_port(Circuit II)) = "
                 << bestScore << endl;
            break;
        }
        vector<Var> outputPairs;
        if (!outputSolve(outputPairs)) {
            cout << "No output pairs found!" << endl;
            break;
        }
        set<Var> currentResult;
        for (int k = 0; k < outputPairs.size(); ++k) {
            currentResult.insert(outputPairs[k]);
            // cout << "Solving isValidMo..." << endl;
            // bool result = isValidMo(currentResult);
            // if (!result) {
            //     // TODO: block currentResult
            //     currentResult.erase(outputPairs[k]);
            // }
        }
        isValidMo(currentResult);
    }
    outputAns(cout);
}

void
BMatchSolver::outputAns(ostream& out) {
    if (bestScore == 0) {
        cout << "No matching found!" << endl;
        return;
    }
    cout << "----------Optimal Matching----------" << endl;
    cout << "Best Score: " << bestScore << endl << endl;
    cout << "Input matrix: " << endl;
    for (int i = 0; i < ans_a.size(); ++i) {
        for (int j = 0; j < ans_a[0].size(); ++j) {
            cout << ans_a[i][j] << " ";
            cout << ans_b[i][j] << " ";
        }
        cout << endl;
    }
    cout << endl;
    cout << "Output matrix: " << endl;
    for (int i = 0; i < ans_c.size(); ++i) {
        for (int j = 0; j < ans_c[0].size(); ++j) {
            cout << ans_c[i][j] << " ";
            cout << ans_d[i][j] << " ";
        }
        cout << endl;
    }

    // output to file as required format
    // INGROUP
    for (int j = 0; j < x.size(); ++j) {
        // all input in circuit 1 must be mapped
        out << "INGROUP" << endl;
        out << "1 + <" << x[j].getName() << ">"
            << endl; // include "<>" or not ????
        for (int i = 0; i < y.size(); ++i) {
            if (ans_a[i][j] != 0) {
                out << "2 + <" << y[i].getName() << ">" << endl;
            }
            if (ans_b[i][j] != 0) {
                out << "2 - <" << y[i].getName() << ">" << endl;
            }
        }
        out << "END" << endl << endl;
    }
    // OUTGROUP
    for (int j = 0; j < ans_c[0].size(); ++j) {
        bool circuit1Mapped = false;
        for (int i = 0; i < ans_c.size(); ++i) {
            if (ans_c[i][j] || ans_d[i][j]) {
                if (!circuit1Mapped) {
                    circuit1Mapped = true;
                    out << "OUTGROUP" << endl;
                    out << "1 + <" << f[j].getName() << ">" << endl;
                }
                if (ans_c[i][j]) {
                    out << "2 + <" << g[i].getName() << ">" << endl;
                } else {
                    out << "2 - <" << g[i].getName() << ">" << endl;
                }
            }
        }
        if (circuit1Mapped) out << "END" << endl << endl;
    }
    // CONSTGROUP
    out << "CONSTGROUP" << endl;
    for (int i = 0; i < y.size(); ++i) {
        if (ans_a[i][x.size()])
            out << "+ <" << y[i].getName() << ">" << endl; // + to 0
        if (ans_b[i][x.size()])
            out << "- <" << y[i].getName() << ">" << endl; // - to 1
    }
    out << "END" << endl << endl;
}

void
BMatchSolver::genCircuitModel(ifstream& portMapping, ifstream& aag1, ifstream& aag2) {
    x.clear();
    f.clear();
    y.clear();
    g.clear();
    fStar.clear();
    // TODO: build circuit 1/2 constrains to miter, and add IO port name, Var to
    // x/y, f/g

    readPortMapping(portMapping);
    readAAG(aag1, true);
    readAAG(aag2, false);

    for (int i = 0; i < g.size(); ++i) {
        fStar.push_back(miterSolver.newVar());
    }
}

void
BMatchSolver::readPortMapping(ifstream& in) {
    // <1|2>(int) <"input"|"output">(string) <PortName>(string) <VarInCNF>(int)
    int    one_two;
    string IO;
    string name;
    int    litInAAG;
    while (in >> one_two >> IO >> name >> litInAAG) {
        vector<Port>& IOPorts =
            (one_two == 1 ? (IO == "input" ? x : f) : (IO == "input" ? y : g));
        Var v = AAG2Var(litInAAG / 2, (one_two == 1));
        if (litInAAG % 2 == 1) {                       // inverted output
            Var         invVar = miterSolver.newVar(); // invVar = ~v
            vector<Lit> lits;
            lits.push_back(Lit(invVar));
            lits.push_back(Lit(v));
            miterSolver.addCNF(lits);
            lits.clear();
            lits.push_back(~Lit(invVar));
            lits.push_back(~Lit(v));
            miterSolver.addCNF(lits);
            v = invVar;
            // output port will be the inverted var, and use AAG2VAR will get
            // the original one
        }
        IOPorts.push_back(Port(name, v));
    }
    in.close();
}

void
BMatchSolver::readAAG(ifstream& in, bool circuitOne) {
    int    litInAAG;
    string aag;
    int    M, I, L, O, A;
    in >> aag >> M >> I >> L >> O >> A;
    for (int i = 0; i < I; ++i) {
        int temp;
        in >> temp;
    }
    for (int i = 0; i < O; ++i) {
        int outLit;
        in >> outLit;
    }
    int lf, la, lb;
    for (int i = 0; i < A; ++i) {
        in >> lf >> la >> lb;
        Var  vf = AAG2Var(lf / 2, circuitOne);
        Var  va = AAG2Var(la / 2, circuitOne);
        bool fa = la % 2;
        Var  vb = AAG2Var(lb / 2, circuitOne);
        bool fb = lb % 2;
        miterSolver.addAigCNF(vf, va, fa, vb, fb);
    }
    in.close();
}

void
BMatchSolver::buildMatrix() {
    // TODO: add matrix constraints based on x, f, y, g
    a.clear();
    a.reserve(y.size());
    b.clear();
    b.reserve(y.size());
    c.clear();
    c.reserve(g.size());
    d.clear();
    d.reserve(g.size());

    outputC.clear();
    outputC.reserve(g.size());
    outputD.clear();
    outputD.reserve(g.size());

    // answer matrix
    ans_a.reserve(y.size());
    ans_b.reserve(y.size());
    for (int i = 0; i < y.size(); ++i) {
        ans_a.push_back(vector<bool>(x.size() + 1));
        ans_b.push_back(vector<bool>(x.size() + 1));
    }
    for (int i = 0; i < g.size(); ++i) {
        ans_c.push_back(vector<bool>(f.size()));
        ans_d.push_back(vector<bool>(f.size()));
    }

    // Input matrix
    for (int i = 0; i < y.size(); ++i) {
        vector<mtx2Mit> aTemp(x.size() + 1);
        vector<mtx2Mit> bTemp(x.size() + 1);
        for (int j = 0; j < x.size(); ++j) {
            aTemp[j].matrixVar = matrixSolver.newVar();
            bTemp[j].matrixVar = matrixSolver.newVar();
        }
        aTemp[x.size()].matrixVar = matrixSolver.newVar();
        bTemp[x.size()].matrixVar = matrixSolver.newVar();
        a.push_back(aTemp);
        b.push_back(bTemp);
    }

    // Output matrix
    for (int i = 0; i < fStar.size(); ++i) {
        vector<mtx2Mit> cTemp(f.size());
        vector<mtx2Mit> dTemp(f.size());

        vector<Var> outputCTemp(f.size());
        vector<Var> outputDTemp(f.size());

        for (int j = 0; j < f.size(); ++j) {
            cTemp[j].matrixVar = matrixSolver.newVar();
            dTemp[j].matrixVar = matrixSolver.newVar();

            outputCTemp[j] = outputSolver.newVar();
            outputDTemp[j] = outputSolver.newVar();
        }
        c.push_back(cTemp);
        d.push_back(dTemp);

        outputC.push_back(outputCTemp);
        outputD.push_back(outputDTemp);
    }

    // Input constrints
    // sum >= 1
    vector<Lit> ls;
    ls.reserve(2 * y.size());
    for (int j = 0; j < x.size(); ++j) { // exclude the zero/one column
        ls.clear();
        for (int i = 0; i < y.size(); ++i) {
            ls.push_back(Lit(a[i][j].matrixVar));
            ls.push_back(Lit(b[i][j].matrixVar));
        }
        matrixSolver.addCNF(ls);
    }
    // sum == 1
    // one hot method
    for (int i = 0; i < y.size(); ++i) {
        vector<Lit> oneHot;
        oneHot.reserve(2 * (x.size() + 1));
        for (int j = 0; j < x.size() + 1; ++j) {
            oneHot.push_back(Lit(a[i][j].matrixVar));
            oneHot.push_back(Lit(b[i][j].matrixVar));
        }
        matrixSolver.addOneHot(oneHot);
    }

    // Output constraints on outputSolver
    for (int i = 0; i < fStar.size(); ++i) {
        vector<Lit> lits;
        for (int j = 0; j < f.size(); ++j) {
            lits.clear();
            lits.push_back(~Lit(outputC[i][j]));
            lits.push_back(~Lit(outputD[i][j]));
            outputSolver.addCNF(lits);
            for (int k = j + 1; k < f.size(); ++k) {
                lits.clear();
                lits.push_back(~Lit(outputC[i][j]));
                lits.push_back(~Lit(outputC[i][k]));
                outputSolver.addCNF(lits);

                lits.clear();
                lits.push_back(~Lit(outputC[i][j]));
                lits.push_back(~Lit(outputD[i][k]));
                outputSolver.addCNF(lits);

                lits.clear();
                lits.push_back(~Lit(outputD[i][j]));
                lits.push_back(~Lit(outputC[i][k]));
                outputSolver.addCNF(lits);

                lits.clear();
                lits.push_back(~Lit(outputD[i][j]));
                lits.push_back(~Lit(outputD[i][k]));
                outputSolver.addCNF(lits);
            }
        }
    }

    // update score helper Var

    ansHelper.reserve(f.size());
    // vector<Lit> aggressiveLits;
    for (int j = 0; j < f.size(); ++j) {
        ansHelper.push_back(outputSolver.newVar());
        // v <-> (all c in column) + (all d in column)
        // => (¬p ∨ v) ∧ (¬q ∨ v) ∧ (¬r ∨ v) ∧ (¬s ∨ v) ∧ (¬v ∨ p ∨ q ∨ r ∨ s)
        vector<Lit> lits;
        lits.push_back(~Lit(ansHelper[j]));
        for (int i = 0; i < g.size(); ++i) {
            lits.push_back(Lit(outputC[i][j]));
            lits.push_back(Lit(outputD[i][j]));

            vector<Lit> lits2;
            lits2.push_back(Lit(ansHelper[j]));
            lits2.push_back(~Lit(outputC[i][j])); // (~c + v)
            outputSolver.addCNF(lits2);

            lits2[1] = ~Lit(outputD[i][j]); // (~d + v)
            outputSolver.addCNF(lits2);
        }
        outputSolver.addCNF(lits);
        // aggressiveLits.push_back(Lit(ansHelper[j]));
    }
    // outputSolver.addCNF(aggressiveLits);

}

void
BMatchSolver::genMiterConstraint() {
    // TODO: \phi_a constraints
    // p -> y == x => (~p + x + ~y)(~p + ~x + y)

    // Input contraints
    for (int i = 0; i < y.size(); ++i) {
        for (int j = 0; j < x.size(); ++j) {
            a[i][j].miterVar = miterSolver.newVar();
            vector<Lit> lits;
            lits.push_back(~Lit(a[i][j].miterVar));
            lits.push_back(Lit(x[j].getVar()));
            lits.push_back(~Lit(y[i].getVar()));
            miterSolver.addCNF(lits);

            lits.clear();
            lits.push_back(~Lit(a[i][j].miterVar));
            lits.push_back(~Lit(x[j].getVar()));
            lits.push_back(Lit(y[i].getVar()));
            miterSolver.addCNF(lits);

            b[i][j].miterVar = miterSolver.newVar();
            lits.clear();
            lits.push_back(~Lit(b[i][j].miterVar));
            lits.push_back(~Lit(x[j].getVar()));
            lits.push_back(~Lit(y[i].getVar()));
            miterSolver.addCNF(lits);

            lits.clear();
            lits.push_back(~Lit(b[i][j].miterVar));
            lits.push_back(Lit(x[j].getVar()));
            lits.push_back(Lit(y[i].getVar()));
            miterSolver.addCNF(lits);
        }
        // zero constraint a[i][x.size()] -> ~y[i]
        a[i][x.size()].miterVar = miterSolver.newVar();
        vector<Lit> lits;
        lits.push_back(~Lit(a[i][x.size()].miterVar));
        lits.push_back(~Lit(y[i].getVar()));
        miterSolver.addCNF(lits);

        // one constraint b[i][x.size()] -> y[i]
        b[i][x.size()].miterVar = miterSolver.newVar();
        lits.clear();
        lits.push_back(~Lit(b[i][x.size()].miterVar));
        lits.push_back(Lit(y[i].getVar()));
        miterSolver.addCNF(lits);
    }

    // Output constrints
    for (int i = 0; i < fStar.size(); ++i) {
        for (int j = 0; j < f.size(); ++j) {
            c[i][j].miterVar = miterSolver.newVar();
            vector<Lit> lits;
            lits.push_back(~Lit(c[i][j].miterVar));
            lits.push_back(Lit(fStar[i]));
            lits.push_back(~Lit(f[j].getVar()));
            miterSolver.addCNF(lits);

            lits.clear();
            lits.push_back(~Lit(c[i][j].miterVar));
            lits.push_back(~Lit(fStar[i]));
            lits.push_back(Lit(f[j].getVar()));
            miterSolver.addCNF(lits);

            d[i][j].miterVar = miterSolver.newVar();
            lits.clear();
            lits.push_back(~Lit(d[i][j].miterVar));
            lits.push_back(~Lit(fStar[i]));
            lits.push_back(~Lit(f[j].getVar()));
            miterSolver.addCNF(lits);

            lits.clear();
            lits.push_back(~Lit(d[i][j].miterVar));
            lits.push_back(Lit(fStar[i]));
            lits.push_back(Lit(f[j].getVar()));
            miterSolver.addCNF(lits);
        }
    }

    // TODO: maybe don't need g* f* &@#&$@&#$...
    // x != y => (~x + ~y)(x + y)
    // p <-> (A != B) => (¬A ∨ B ∨ P) ∧ (A ∨ ¬B ∨ P) ∧ (B ∨ A ∨ ¬P) ∧ (¬A ∨ ¬B ∨
    // ¬P)
    vector<Lit> lits;
    for (int i = 0; i < fStar.size(); ++i) {
        Var p = miterSolver.newVar();
        miterSolver.addXorCNF(p, fStar[i], false, g[i].getVar(), false);

        // a <-> b+c+d+e+...+ => (¬B ∨ A) ∧ (¬C ∨ A) ∧ (¬D ∨ A) ∧ (¬E ∨ A) ∧ (¬A
        // ∨ B ∨ C ∨ D ∨ E)
        vector<Lit> lits2;
        Var         care = miterSolver.newVar();
        lits2.push_back(~Lit(care));
        for (int j = 0; j < f.size(); ++j) {
            vector<Lit> lits3;
            lits3.push_back(Lit(care));
            lits3.push_back(~Lit(c[i][j].miterVar));
            miterSolver.addCNF(lits3);
            lits3[1] = ~Lit(d[i][j].miterVar);
            miterSolver.addCNF(lits3);
            lits2.push_back(Lit(c[i][j].miterVar));
            lits2.push_back(Lit(d[i][j].miterVar));
        }
        miterSolver.addCNF(lits2);

        // q <-> care & p
        Var q = miterSolver.newVar();
        miterSolver.addAigCNF(q, care, false, p, false);

        lits.push_back(Lit(q)); // q means real no match
    }
    miterSolver.addCNF(lits);
}

bool 
BMatchSolver::outputSolve(vector<Var>& outputPairs) {
    cerr << "in outputSolve" << endl;
    outputPairs.clear();
    bool result = outputSolver.solve();
    if (!result)
        return false;
    cerr << "in outputSolve finish" << endl;
    for (int i = 0; i < fStar.size(); ++i) {
        for (int j = 0; j < f.size(); ++j) {
            if (outputSolver.getValue(outputC[i][j]) == 1) {
                outputPairs.push_back(c[i][j].matrixVar);
                cout << "c" << i << ", " << j << endl;
            }
            if (outputSolver.getValue(outputD[i][j]) == 1) {
                outputPairs.push_back(d[i][j].matrixVar);
                cout << "d" << i << ", " << j << endl;
            }
        }
    }

    vector<Lit> lits;
    for (int i = 0; i < fStar.size(); ++i) {
        for (int j = 0; j < f.size(); ++j) {
            int value = outputSolver.getValue(outputC[i][j]);
            assert(value != -1);
            if (value != -1) {
                lits.push_back(value ? ~Lit(outputC[i][j])
                                        : Lit(outputC[i][j]));
            }
            value = outputSolver.getValue(outputD[i][j]);
            if (value != -1) {
                lits.push_back(value ? ~Lit(outputD[i][j])
                                        : Lit(outputD[i][j]));
            }
            assert(value != -1);
        }
    }
    outputSolver.addCNF(lits);
    return true;
}

bool 
BMatchSolver::isValidMo(const set<Var>& currentResult) {
    // get input matrix
    matrixSolver.assumeRelease();
    for (int i = 0; i < fStar.size(); ++i) {
        for (int j = 0; j < f.size(); ++j) {
            bool cValue = currentResult.find(c[i][j].matrixVar) != currentResult.end();
            bool dValue = currentResult.find(d[i][j].matrixVar) != currentResult.end();
            matrixSolver.assumeProperty(c[i][j].matrixVar, cValue);
            matrixSolver.assumeProperty(d[i][j].matrixVar, dValue);
        }
    }
    while (1) {
        bool inputResult = matrixSolver.assumpSolve();
        if (!inputResult) {
            cout << "cannot find other input mapping" << endl;
            return false;
        }

        // Assume to miterSolver and solve
        // Assume input mapping
        miterSolver.assumeRelease();
        for (int i = 0; i < y.size(); ++i) {
            for (int j = 0; j < x.size() + 1; ++j) {
                int matrixVarValue = matrixSolver.getValue(a[i][j].matrixVar);
                if (matrixVarValue != -1) { // -1 means unknown
                    miterSolver.assumeProperty(a[i][j].miterVar,
                                                matrixVarValue);
                }
                matrixVarValue = matrixSolver.getValue(b[i][j].matrixVar);
                if (matrixVarValue != -1) { // -1 means unknown
                    miterSolver.assumeProperty(b[i][j].miterVar,
                                                matrixVarValue);
                }
            }
        }
        // Assume output mapping
        for (int i = 0; i < fStar.size(); ++i) {
            for (int j = 0; j < f.size(); ++j) {
                int matrixVarValue = matrixSolver.getValue(c[i][j].matrixVar);
                if (matrixVarValue != -1) { // -1 means unknown
                    miterSolver.assumeProperty(c[i][j].miterVar,
                                                matrixVarValue);
                }
                matrixVarValue = matrixSolver.getValue(d[i][j].matrixVar);
                if (matrixVarValue != -1) { // -1 means unknown
                    miterSolver.assumeProperty(d[i][j].miterVar,
                                                matrixVarValue);
                }
            }
        }
        if (miterSolve()) { // UNSAT -> find a valid mapping
            // Update current answer and block answer
            return true;
        }
        else {
            // cout << "QQ" << endl;
        }
    }
}

bool
BMatchSolver::miterSolve() {
    bool miterResult = miterSolver.assumpSolve();
    if (!miterResult) {
        // UNSAT => find a valid mapping
        // update answer and block this answer from outputSlover
        // Block answer

        cout << "Find a valid mapping!" << endl;
        cout << "Input matrix:" << endl;
        for (int i = 0; i < y.size(); ++i) {
            for (int j = 0; j < x.size() + 1; ++j) {
                cout << matrixSolver.getValue(a[i][j].matrixVar) << " ";
                cout << matrixSolver.getValue(b[i][j].matrixVar) << " ";
                ans_a[i][j] = matrixSolver.getValue(a[i][j].matrixVar);
                ans_b[i][j] = matrixSolver.getValue(b[i][j].matrixVar);
            }
            cout << endl;
        }
        cout << "Output matrix:" << endl;
        vector<Lit> lits;
        for (int i = 0; i < fStar.size(); ++i) {
            for (int j = 0; j < f.size(); ++j) {
                cout << matrixSolver.getValue(c[i][j].matrixVar) << " ";
                cout << matrixSolver.getValue(d[i][j].matrixVar) << " ";
                ans_c[i][j] = matrixSolver.getValue(c[i][j].matrixVar);
                ans_d[i][j] = matrixSolver.getValue(d[i][j].matrixVar);
                lits.push_back(ans_c[i][j] ? ~Lit(outputC[i][j]) : Lit(outputC[i][j]));
                lits.push_back(ans_d[i][j] ? ~Lit(outputD[i][j]) : Lit(outputD[i][j]));
            }
            cout << endl;
        }
        outputSolver.addCNF(lits);
        int score = getScore();
        cout << "Score: " << score << ", Best Score: " << bestScore << endl;
            
        if (score > bestScore) {
            bestScore = score;
            scoreGte(score + 1);
        }
        return true;
    } else {
        // SAT =>
        // AND(l_O + OR(l_I))
        // l_O = (g[i] != f[j]) ? ~c[i][j] : ~d[i][j]
        // l_I = (x[j] != y[i]) ? a[i][j] : b[i][j]
        vector<Lit> lits;
        for (int i = 0; i < fStar.size(); ++i) {
            for (int j = 0; j < f.size(); ++j) {
                if (miterSolver.getValue(g[i].getVar()) !=
                    miterSolver.getValue(f[j].getVar())) {
                    lits.push_back(~Lit(c[i][j].matrixVar));
                } else {
                    lits.push_back(~Lit(d[i][j].matrixVar));
                }
                // TODO: and or or
                for (int k = 0; k < y.size(); ++k) {
                    if (!g[i].isSupport(k))
                        continue;
                    for (int l = 0; l < x.size(); ++l) { // +1 or not
                        if (!f[j].isSupport(l))
                            continue;
                        if (miterSolver.getValue(y[k].getVar()) !=
                            miterSolver.getValue(x[l].getVar())) {
                            lits.push_back(Lit(a[k][l].matrixVar));
                        } else {
                            lits.push_back(Lit(b[k][l].matrixVar));
                        }
                    }
                }
                matrixSolver.addCNF(lits);
                lits.clear();
            }
        }
    }
    return false;
}

Var
BMatchSolver::AAG2Var(int AAGVar, bool circuitOne) {
    if (!circuitOne) AAGVar = -AAGVar;
    if (AAG2VarHashmap.find(AAGVar) == AAG2VarHashmap.end())
        AAG2VarHashmap[AAGVar] = miterSolver.newVar();
    return AAG2VarHashmap[AAGVar];
}

int
BMatchSolver::getScore() {
    // TODO: calcutate current score from c, d and compare it with bestScore

    int score = 0;
    for (int j = 0; j < f.size(); ++j) {
        bool columnMap = false;
        for (int i = 0; i < fStar.size(); ++i) {
            // Not sure these assertions is correct or not
            assert(matrixSolver.getValue(c[i][j].matrixVar) != -1);
            assert(matrixSolver.getValue(d[i][j].matrixVar) != -1);
            //

            score += matrixSolver.getValue(c[i][j].matrixVar);
            score += matrixSolver.getValue(d[i][j].matrixVar);
            if (matrixSolver.getValue(c[i][j].matrixVar) || matrixSolver.getValue(d[i][j].matrixVar))
                columnMap = true;
        }
        if (columnMap)
            score ++;
    }
    cout << "in getScore func: " << score << endl;
    return score;
}

void
BMatchSolver::scoreGte(int x) {
    // return;
    vector<Lit> clause;
    for (int j = 0; j < f.size(); ++j) {
        for (int i = 0; i < fStar.size(); ++i) {
            clause.push_back(Lit(outputC[i][j]));
            clause.push_back(Lit(outputD[i][j]));
        }
        clause.push_back(Lit(ansHelper[j]));
    }
    outputSolver.addGte(clause, x);
}
