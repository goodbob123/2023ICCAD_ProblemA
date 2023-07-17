#include <time.h>

#include <algorithm>
#include <fstream>
#include <iostream>
#include <set>
#include <unordered_map>

#include "./SAT/test/sat.h"
#include "./cir/cirGate.h"
#include "./cir/cirMgr.h"

using namespace std;

class Port {
    friend struct PortHashKey;

   public:
    Port(const string& _name, const Var& _var) {
        name = _name;
        var = _var;
    }
    ~Port() {}
    string getName() const { return name; }
    Var getVar() const { return var; }

    void addSupport(int index) { supports.insert(index); }
    size_t nofSupport() const { return supports.size(); }
    bool isSupport(int index) const { return supports.find(index) != supports.end(); }

   private:
    string name;
    Var var;
    set<int> supports;  // output support for input port, input support for output port
};

struct PortHashKey {
    PortHashKey(const vector<Port>& portList, const Port& p) {
        set<int>::const_iterator it;
        for (it = p.supports.begin(); it != p.supports.end(); ++it) {
            nof_support_of_support.push_back(portList[*it].nofSupport());
        }
        sort(nof_support_of_support.begin(), nof_support_of_support.end());
    }
    bool operator==(const PortHashKey& pk) const {
        if (nof_support_of_support.size() != pk.nof_support_of_support.size())
            return false;
        for (int i = 0; i < nof_support_of_support.size(); ++i) {
            if (nof_support_of_support[i] != pk.nof_support_of_support[i])
                return false;
        }
        return true;
    }
    vector<int> nof_support_of_support;
};

struct PortHashFunc {
    size_t operator()(const PortHashKey& pk) const {
        return pk.nof_support_of_support.size();
    }
};
struct mtx2Mit {
    Var matrixVar;
    Var miterVar;
};

class BMatchSolver {
   public:
    BMatchSolver(){};
    ~BMatchSolver(){};
    void init(ifstream& portMapping, ifstream& aag1, ifstream& aag2, ostream& out);
    void genFuncSupport(ifstream& in);
    void inputPreprocess();
    void outputPreprocess(ifstream& in1, ifstream& in2);
    void run(ostream& out);
    void outputAns(ostream& out);

   protected:
    void genCircuitModel(ifstream& portMapping, ifstream& aag1, ifstream& aag2);
    void readPortMapping(ifstream& in);
    void readAAG(ifstream& in, bool circuitOne);
    void buildMatrix();
    void genMiterConstraint();
    bool outputSolve(vector<Var>& outputPairs);
    bool isValidMo(const set<Var>& currentResult);
    bool miterSolve();

    Var AAG2Var(int AAGVar, bool circuitOne);
    int getScore();
    void scoreGte(int x);

    void addEqualConstraint(ifstream& in1, ifstream& in2);
    void createEqualRelationByGroup(const vector<pair<CirGate*, bool>>& group_f,
                                    const vector<pair<CirGate*, bool>>& group_g);
    void createEqualRelationByOneOutput(const int index_f,
                const vector<pair<CirGate*, bool>>& group_g);


    // SAT Solver
    SatSolver matrixSolver, miterSolver;
    SatSolver outputSolver;

    // Circuit 1
    vector<Port> x;
    vector<Port> f;

    // Circuit 2
    vector<Port> y;
    vector<Port> g;
    vector<Var> fStar;

    // I/O Matrix
    vector<vector<mtx2Mit>> a, b, c, d;
    vector<vector<Var>> outputC, outputD;

    // Answer
    int bestScore;
    vector<vector<bool>> ans_a, ans_b, ans_c, ans_d;
    vector<Var> ansHelper;

    // time
    double START;
    unordered_map<int, Var> AAG2VarHashmap;

    // vector<set<int>> fSupport;
    // vector<set<int>> gSupport;
};