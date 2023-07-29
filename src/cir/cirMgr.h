/****************************************************************************
  FileName     [ cirMgr.h ]
  PackageName  [ cir ]
  Synopsis     [ Define circuit manager ]
  Author       [ Chung-Yang (Ric) Huang ]
  Copyright    [ Copyleft(c) 2008-present LaDs(III), GIEE, NTU, Taiwan ]
****************************************************************************/

#ifndef CIR_MGR_H
#define CIR_MGR_H
#include <fstream>
#include <iostream>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;

// TODO: Feel free to define your own classes, variables, or functions.
#include <sys/types.h>

#include "cirDef.h"
#include "cirGate.h"

extern CirMgr *cirMgr;

class CirMgr {
   public:
    CirMgr() {}
    ~CirMgr() {}

    // Access functions
    // return '0' if "gid" corresponds to an undefined gate.
    CirGate *getGate(unsigned gid) const { return all[gid]; }
    string getFilename() const { return fileName; }
    int getIOsize() const { return PIs.size() + POs.size(); }
    int getAllsize() const { return all.size(); }

    // Member functions about circuit construction
    bool readCircuit(const string &);
    bool readCircuit(ifstream &);

    // Member functions about circuit optimization
    void sweep();
    void optimize();

    // Member functions about simulation
    void randomSim();
    void fileSim(ifstream &);
    void setSimLog(ofstream *logFile) { _simLog = logFile; }
    bool findPattern(CirGate *, vector<bool> &isUpdate);
    void simulate64times();
    // void writeLog(vector<uint32_t> &);
    void writeLog();
    bool isNoPattern = true;
    vector<int> inputId2Pattern;

    // Member functions about fraig
    void strash();
    void printFEC() const;
    void fraig();
    void genProofModel(SatSolver &s);
    bool ifFEC(SatSolver &solver, pair<CirGate *, bool> a, pair<CirGate *, bool> b);

    // Member functions about CAD
    vector<vector<pair<CirGate *, bool>>> fraigForGroup();

    // Member functions about circuit reporting
    void printSummary() const;
    void printNetlist();
    void printPIs() const;
    void printPOs() const;
    void printFloatGates() const;
    void printFECPairs() const;
    void writeAag(ostream &);
    void writeGate(ostream &, CirGate *);
    void DFS(CirGate *);
    string getIOName(const CirGate *) const;

    //  Member function about coverage
    // void showCoverage();
    // void coverage(CirGate *g);
    void coverageHelper(CirGate* g, int& coverage, vector<int>& supports);
    void getSupportCoverageInfo(vector<int> &allCoverage, vector<vector<int>> &allSupports);
    void findNecessary(CirGate *g, set<int> &set);
    vector<set<int>> getNecessary(const vector<int> &, const vector<int> &);
    void showInfo();

    // update Function
    void updateFanout();
    void updateUnusedForPI();
    void updateAIGs();
    void updateTrace();
    void updateFloats();

  //  private:
    ofstream *_simLog;
    GateList all;  // index = gid
    GateList PIs;
    GateList POs;
    GateList AIGs;
    GateList ConstGates;
    GateList FloatGates;
    GateList UnusedGates;
    // store input name,ouput name(output index= inputsize+ 0,1,2.... )
    vector<string> ioname;
    // for DFS list
    vector<int> trace;
    string fileName;
    vector<vector<pair<CirGate *, bool>>> SimGroups;  // true for negation
    // for Sim
    // each index correspond each PI pattern
    vector<uint64_t> inputPattern;
    int currWriteLine;
    int allWriteLine;
    // for SAT
    vector<Var> id2Var;
    vector<int> var2id;
    bool isSimulated = false;
    bool isStrashed = false;

    // for CAD tmp data
    vector<int> all_coverage;
    unordered_map<int, int> id2Idx;  // for input
};

#endif  // CIR_MGR_H
