#include "sat.h"
#include <fstream>
#include <iostream>
#include <time.h>
#include <unordered_map>
#include <vector>

using namespace std;

double START;

unordered_map<int, Var> AAG2VarHashmap;
unordered_map<int, Var> outputInverted;

class Port
{
    public:
        Port(const string& _name, const Var& _var) {
            name = _name;
            var  = _var;
        }
        ~Port() {}
        string getName() const { return name; }
        Var    getVar() const { return var; }

    private:
        string name;
        Var    var;
};

struct mtx2Mit {
        Var matrixVar;
        Var miterVar;
};

// Global variables

// SAT Solver
SatSolver matrixSolver, miterSolver;

// Circuit 1
vector<Port> x;
vector<Port> f;

// Circuit 2
vector<Port> y;
vector<Port> g;
vector<Var>  fStar;

// I/O Matrix
vector<vector<mtx2Mit>> a, b, c, d;

// Answer
int                  bestScore;
vector<vector<bool>> ans_a, ans_b, ans_c, ans_d;
vector<Var>          ansHelper;

Var
AAG2Var(int AAGVar, bool circuitOne) {
    if (!circuitOne) AAGVar = -AAGVar;
    if (AAG2VarHashmap.find(AAGVar) == AAG2VarHashmap.end())
        AAG2VarHashmap[AAGVar] = miterSolver.newVar();
    return AAG2VarHashmap[AAGVar];
}

void
readPortMapping(ifstream& in) {
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
readAAG(ifstream& in, bool circuitOne) {
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
outputAns(ostream& out) {
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

int
getScore() {
    // TODO: calcutate current score from c, d and compare it with bestScore
    int score = 0;
    for (int j = 0; j < f.size(); ++j) {
        for (int i = 0; i < fStar.size(); ++i) {
            // Not sure these assertions is correct or not
            assert(matrixSolver.getValue(c[i][j].matrixVar) != -1);
            assert(matrixSolver.getValue(d[i][j].matrixVar) != -1);
            //

            score += matrixSolver.getValue(c[i][j].matrixVar);
            score += matrixSolver.getValue(d[i][j].matrixVar);
        }
        score += matrixSolver.getValue(ansHelper[j]);
    }
    return score;
}

void
test1() {
    vector<Lit> lits;
    // (2, 3) (2, 3)
    // f1 = a & b
    // f2 = !a & !b
    Var         temp = miterSolver.newVar();
    x.push_back(Port("a", temp)); // x[0]
    temp = miterSolver.newVar();
    x.push_back(Port("b", temp)); // x[1]
    temp = miterSolver.newVar();
    f.push_back(Port("a & b", temp)); // f[0]
    temp = miterSolver.newVar();
    f.push_back(Port("!a & !b", temp)); // f[1]
    miterSolver.addAigCNF(f[0].getVar(), x[0].getVar(), false, x[1].getVar(),
                          false);
    miterSolver.addAigCNF(f[1].getVar(), x[0].getVar(), true, x[1].getVar(),
                          true);

    // g1 = a & !b
    // g2 = !a & b
    temp = miterSolver.newVar();
    y.push_back(Port("a", temp));
    temp = miterSolver.newVar();
    y.push_back(Port("b", temp));
    temp = miterSolver.newVar();
    g.push_back(Port("a & !b", temp));
    temp = miterSolver.newVar();
    g.push_back(Port("!a & b", temp));
    miterSolver.addAigCNF(g[0].getVar(), y[0].getVar(), false, y[1].getVar(),
                          true);
    miterSolver.addAigCNF(g[1].getVar(), y[0].getVar(), true, y[1].getVar(),
                          false);
}

void
test2() {
    for (int i = 0; i < 3; ++i) {
        x.push_back(Port("x" + to_string(i), miterSolver.newVar()));
    }
    for (int i = 0; i < 3; ++i) {
        f.push_back(Port("f" + to_string(i), miterSolver.newVar()));
    }
    for (int i = 0; i < 4; ++i) {
        y.push_back(Port("y" + to_string(i), miterSolver.newVar()));
    }
    for (int i = 0; i < 4; ++i) {
        g.push_back(Port("g" + to_string(i), miterSolver.newVar()));
    }
    // Circuit 1
    Var a1 = miterSolver.newVar();
    Var a2 = miterSolver.newVar();
    Var a3 = miterSolver.newVar();
    miterSolver.addAigCNF(a1, x[0].getVar(), false, x[1].getVar(), false);
    miterSolver.addAigCNF(a2, x[0].getVar(), true, x[1].getVar(), false);
    miterSolver.addAigCNF(a3, x[2].getVar(), true, a2, false);
    miterSolver.addAigCNF(f[0].getVar(), a1, false, a3, true);
    miterSolver.addAigCNF(f[1].getVar(), a1, true, x[2].getVar(), true);
    miterSolver.addAigCNF(f[2].getVar(), a2, true, a3, true);

    // Circuit 2
    Var b1 = miterSolver.newVar();
    Var b2 = miterSolver.newVar();
    Var b3 = miterSolver.newVar();
    miterSolver.addAigCNF(b1, y[0].getVar(), true, y[1].getVar(), false);
    miterSolver.addAigCNF(b2, y[2].getVar(), false, y[3].getVar(), false);
    miterSolver.addAigCNF(b3, b2, false, y[3].getVar(), false);
    miterSolver.addAigCNF(g[0].getVar(), b1, false, b3, true);
    miterSolver.addAigCNF(g[1].getVar(), b2, false, b1, true);
    miterSolver.addAigCNF(g[2].getVar(), y[0].getVar(), false, b2, true);
    miterSolver.addAigCNF(g[3].getVar(), y[2].getVar(), false, y[3].getVar(),
                          true);
}
void
genCircuitModel(ifstream& portMapping, ifstream& aag1, ifstream& aig2) {
    x.clear();
    f.clear();
    y.clear();
    g.clear();
    fStar.clear();
    // TODO: build circuit 1/2 constrains to miter, and add IO port name, Var to
    // x/y, f/g

    // test1();
    // test2();

    readPortMapping(portMapping);
    readAAG(aag1, true);
    readAAG(aig2, false);

    for (int i = 0; i < g.size(); ++i) {
        fStar.push_back(miterSolver.newVar());
    }
}
void
buildMatrix() {
    // TODO: add matrix constraints based on x, f, y, g
    a.clear();
    a.reserve(y.size());
    b.clear();
    b.reserve(y.size());
    c.clear();
    c.reserve(g.size());
    d.clear();
    d.reserve(g.size());

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
        for (int j = 0; j < f.size(); ++j) {
            cTemp[j].matrixVar = matrixSolver.newVar();
            dTemp[j].matrixVar = matrixSolver.newVar();
        }
        c.push_back(cTemp);
        d.push_back(dTemp);
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
        matrixSolver.add_one_hot_constraint(oneHot);
    }
    /*
    for (int i = 0; i < y.size(); ++i) {
      vector<Lit> allLits;
      vector<Lit> lits;
      for (int j = 0; j < x.size() + 1; ++j) { // include the zero/one column
        allLits.push_back(Lit(a[i][j].matrixVar));
        allLits.push_back(Lit(b[i][j].matrixVar));
        lits.clear();
        lits.push_back(~Lit(a[i][j].matrixVar));
        lits.push_back(~Lit(b[i][j].matrixVar));
        matrixSolver.addCNF(lits);
        for (int k = j + 1; k < x.size() + 1; ++k) {
          lits.clear();
          lits.push_back(~Lit(a[i][j].matrixVar));
          lits.push_back(~Lit(a[i][k].matrixVar));
          matrixSolver.addCNF(lits);

          lits.clear();
          lits.push_back(~Lit(a[i][j].matrixVar));
          lits.push_back(~Lit(b[i][k].matrixVar));
          matrixSolver.addCNF(lits);

          lits.clear();
          lits.push_back(~Lit(b[i][j].matrixVar));
          lits.push_back(~Lit(a[i][k].matrixVar));
          matrixSolver.addCNF(lits);

          lits.clear();
          lits.push_back(~Lit(b[i][j].matrixVar));
          lits.push_back(~Lit(b[i][k].matrixVar));
          matrixSolver.addCNF(lits);
        }
      }
      matrixSolver.addCNF(allLits);
    }
    */

    // Output constraints
    for (int i = 0; i < fStar.size(); ++i) {
        vector<Lit> lits;
        for (int j = 0; j < f.size(); ++j) {
            lits.clear();
            lits.push_back(~Lit(c[i][j].matrixVar));
            lits.push_back(~Lit(d[i][j].matrixVar));
            matrixSolver.addCNF(lits);
            for (int k = j + 1; k < f.size(); ++k) {
                lits.clear();
                lits.push_back(~Lit(c[i][j].matrixVar));
                lits.push_back(~Lit(c[i][k].matrixVar));
                matrixSolver.addCNF(lits);

                lits.clear();
                lits.push_back(~Lit(c[i][j].matrixVar));
                lits.push_back(~Lit(d[i][k].matrixVar));
                matrixSolver.addCNF(lits);

                lits.clear();
                lits.push_back(~Lit(d[i][j].matrixVar));
                lits.push_back(~Lit(c[i][k].matrixVar));
                matrixSolver.addCNF(lits);

                lits.clear();
                lits.push_back(~Lit(d[i][j].matrixVar));
                lits.push_back(~Lit(d[i][k].matrixVar));
                matrixSolver.addCNF(lits);
            }
        }
    }

    // update score helper Var
    ansHelper.reserve(f.size());
    vector<Lit> aggressiveLits;
    for (int j = 0; j < f.size(); ++j) {
        ansHelper.push_back(matrixSolver.newVar());
        // v <-> (all c in column) + (all d in column)
        // => (¬p ∨ v) ∧ (¬q ∨ v) ∧ (¬r ∨ v) ∧ (¬s ∨ v) ∧ (¬v ∨ p ∨ q ∨ r ∨ s)
        vector<Lit> lits;
        lits.push_back(~Lit(ansHelper[j]));
        for (int i = 0; i < g.size(); ++i) {
            lits.push_back(Lit(c[i][j].matrixVar));
            lits.push_back(Lit(d[i][j].matrixVar));

            vector<Lit> lits2;
            lits2.push_back(Lit(ansHelper[j]));
            lits2.push_back(~Lit(c[i][j].matrixVar)); // (~c + v)
            matrixSolver.addCNF(lits2);

            lits2[1] = ~Lit(d[i][j].matrixVar); // (~d + v)
            matrixSolver.addCNF(lits2);
        }
        matrixSolver.addCNF(lits);
        aggressiveLits.push_back(Lit(ansHelper[j]));
    }
    matrixSolver.addCNF(aggressiveLits);
}

void
genMiterConstraint() {
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

void
solve() {
    bestScore      = 0;
    int iterations = 0;
    int prevTime   = 0;
    while (1) {
        iterations++;
        int execTime = (clock() - START) / CLOCKS_PER_SEC;
        if (execTime - prevTime > 10) {
            cout << "Iteration " << iterations << ", time: " << execTime
                 << " seconds" << endl;
            prevTime = execTime;
        }
        if (execTime >= 3600) {
            cout << "3600 seconds: " << bestScore << endl;
            return;
        }

        if (bestScore == g.size() + f.size()) {
            cout << "This must be the OPT with (#output_port(Circuit I) + "
                    "#output_port(Circuit II)) = "
                 << bestScore << endl;
            return;
        }
        bool matrixResult = matrixSolver.solve();
        if (!matrixResult) {
            cout << "No matching found!" << endl;
            return;
        }
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
                if (matrixVarValue != -1) // -1 means unknown
                    miterSolver.assumeProperty(c[i][j].miterVar,
                                               matrixVarValue);
                matrixVarValue = matrixSolver.getValue(d[i][j].matrixVar);
                if (matrixVarValue != -1) // -1 means unknown
                    miterSolver.assumeProperty(d[i][j].miterVar,
                                               matrixVarValue);
            }
        }

        // Solve miter
        bool miterResult = miterSolver.assumpSolve();
        if (!miterResult) {
            // UNSAT => find a valid mapping
            // update answer and block this answer from matrixSlover

            // Block answer
            vector<Lit> lits;
            for (int i = 0; i < y.size(); ++i) {
                for (int j = 0; j < x.size(); ++j) {
                    int value = matrixSolver.getValue(a[i][j].matrixVar);
                    assert(value != -1);
                    if (value != -1) {
                        lits.push_back(value ? ~Lit(a[i][j].matrixVar)
                                             : Lit(a[i][j].matrixVar));
                    }
                    value = matrixSolver.getValue(b[i][j].matrixVar);
                    assert(value != -1);
                    if (value != -1) {
                        lits.push_back(value ? ~Lit(b[i][j].matrixVar)
                                             : Lit(b[i][j].matrixVar));
                    }
                }
            }
            for (int i = 0; i < fStar.size(); ++i) {
                for (int j = 0; j < f.size(); ++j) {
                    int value = matrixSolver.getValue(c[i][j].matrixVar);
                    assert(value != -1);
                    if (value != -1) {
                        lits.push_back(value ? ~Lit(c[i][j].matrixVar)
                                             : Lit(c[i][j].matrixVar));
                    }
                    value = matrixSolver.getValue(d[i][j].matrixVar);
                    if (value != -1) {
                        lits.push_back(value ? ~Lit(d[i][j].matrixVar)
                                             : Lit(d[i][j].matrixVar));
                    }
                    assert(value != -1);
                }
            }
            matrixSolver.addCNF(lits);

            cout << "Find a valid mapping!" << endl;
            int score = getScore();
            if (score > bestScore) {
                cout << "Better mapping!" << endl;
                bestScore = score;
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
                for (int i = 0; i < fStar.size(); ++i) {
                    for (int j = 0; j < f.size(); ++j) {
                        cout << matrixSolver.getValue(c[i][j].matrixVar) << " ";
                        cout << matrixSolver.getValue(d[i][j].matrixVar) << " ";
                        ans_c[i][j] = matrixSolver.getValue(c[i][j].matrixVar);
                        ans_d[i][j] = matrixSolver.getValue(d[i][j].matrixVar);
                    }
                    cout << endl;
                }
                cout << "Best Score: " << bestScore << endl;
            }
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
                    for (int k = 0; k < y.size(); ++k) {
                        for (int l = 0; l < x.size(); ++l) { // +1 or not
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
    }
}

int
main(int argc, char** argv) {
    START = clock();
    if (argc != 5) {
        cerr << "Usage: ./satTest <PortMapping> <AAG1> <AAG2> <OutputFile>"
             << endl;
        return 0;
    }
    ifstream portMapping(argv[1]);
    ifstream aag1(argv[2]);
    ifstream aag2(argv[3]);
    ofstream out(argv[4]);
    if (!portMapping) {
        cerr << "Error: Cannot open PortMapping " << argv[1] << endl;
        return 0;
    }
    if (!aag1) {
        cerr << "Error: Cannot open AAG " << argv[2] << endl;
        return 0;
    }
    if (!aag2) {
        cerr << "Error: Cannot open AAG " << argv[3] << endl;
        return 0;
    }
    if (!out) {
        cerr << "Error: Cannot open OutputFile " << argv[4] << endl;
        return 0;
    }

    matrixSolver.initialize();
    matrixSolver.assumeRelease();
    miterSolver.initialize();
    miterSolver.assumeRelease();

    genCircuitModel(portMapping, aag1, aag2);
    buildMatrix();
    genMiterConstraint();
    cout << "Start solving..." << endl;
    solve();
    cout <<"argv[2]" << argv[2] << endl;
    // output ans
    outputAns(out);
}
