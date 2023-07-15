/****************************************************************************
  FileName     [ cirMgr.cpp ]
  PackageName  [ cir ]
  Synopsis     [ Define cir manager functions ]
  Author       [ Chung-Yang (Ric) Huang ]
  Copyright    [ Copyleft(c) 2008-present LaDs(III), GIEE, NTU, Taiwan ]
****************************************************************************/

#include "cirMgr.h"

#include <ctype.h>

#include <algorithm>
#include <cassert>
#include <cstdio>
#include <cstring>
#include <iomanip>
#include <iostream>
#include <sstream>

#include "cirGate.h"
// #include "util.h"

using namespace std;

// TODO: Implement memeber functions for class CirMgr

/*******************************/
/*   Global variable and enum  */
/*******************************/
CirMgr* cirMgr = 0;

enum CirParseError {
    EXTRA_SPACE,
    MISSING_SPACE,
    ILLEGAL_WSPACE,
    ILLEGAL_NUM,
    ILLEGAL_IDENTIFIER,
    ILLEGAL_SYMBOL_TYPE,
    ILLEGAL_SYMBOL_NAME,
    MISSING_NUM,
    MISSING_IDENTIFIER,
    MISSING_NEWLINE,
    MISSING_DEF,
    CANNOT_INVERTED,
    MAX_LIT_ID,
    REDEF_GATE,
    REDEF_SYMBOLIC_NAME,
    REDEF_CONST,
    NUM_TOO_SMALL,
    NUM_TOO_BIG,

    DUMMY_END
};

/**************************************/
/*   Static varaibles and functions   */
/**************************************/
static unsigned lineNo = 0;  // in printint, lineNo needs to ++
static unsigned colNo = 0;   // in printing, colNo needs to ++
static char buf[1024];
static string errMsg;
static int errInt;
static CirGate* errGate;

static bool
parseError(CirParseError err) {
    switch (err) {
        case EXTRA_SPACE:
            cerr << "[ERROR] Line " << lineNo + 1 << ", Col " << colNo + 1
                 << ": Extra space character is detected!!" << endl;
            break;
        case MISSING_SPACE:
            cerr << "[ERROR] Line " << lineNo + 1 << ", Col " << colNo + 1
                 << ": Missing space character!!" << endl;
            break;
        case ILLEGAL_WSPACE:  // for non-space white space character
            cerr << "[ERROR] Line " << lineNo + 1 << ", Col " << colNo + 1
                 << ": Illegal white space char(" << errInt << ") is detected!!"
                 << endl;
            break;
        case ILLEGAL_NUM:
            cerr << "[ERROR] Line " << lineNo + 1 << ": Illegal " << errMsg << "!!"
                 << endl;
            break;
        case ILLEGAL_IDENTIFIER:
            cerr << "[ERROR] Line " << lineNo + 1 << ": Illegal identifier \""
                 << errMsg << "\"!!" << endl;
            break;
        case ILLEGAL_SYMBOL_TYPE:
            cerr << "[ERROR] Line " << lineNo + 1 << ", Col " << colNo + 1
                 << ": Illegal symbol type (" << errMsg << ")!!" << endl;
            break;
        case ILLEGAL_SYMBOL_NAME:
            cerr << "[ERROR] Line " << lineNo + 1 << ", Col " << colNo + 1
                 << ": Symbolic name contains un-printable char(" << errInt << ")!!"
                 << endl;
            break;
        case MISSING_NUM:
            cerr << "[ERROR] Line " << lineNo + 1 << ", Col " << colNo + 1
                 << ": Missing " << errMsg << "!!" << endl;
            break;
        case MISSING_IDENTIFIER:
            cerr << "[ERROR] Line " << lineNo + 1 << ": Missing \"" << errMsg
                 << "\"!!" << endl;
            break;
        case MISSING_NEWLINE:
            cerr << "[ERROR] Line " << lineNo + 1 << ", Col " << colNo + 1
                 << ": A new line is expected here!!" << endl;
            break;
        case MISSING_DEF:
            cerr << "[ERROR] Line " << lineNo + 1 << ": Missing " << errMsg
                 << " definition!!" << endl;
            break;
        case CANNOT_INVERTED:
            cerr << "[ERROR] Line " << lineNo + 1 << ", Col " << colNo + 1 << ": "
                 << errMsg << " " << errInt << "(" << errInt / 2
                 << ") cannot be inverted!!" << endl;
            break;
        case MAX_LIT_ID:
            cerr << "[ERROR] Line " << lineNo + 1 << ", Col " << colNo + 1
                 << ": Literal \"" << errInt << "\" exceeds maximum valid ID!!"
                 << endl;
            break;
        case REDEF_GATE:
            cerr << "[ERROR] Line " << lineNo + 1 << ": Literal \"" << errInt
                 << "\" is redefined, previously defined as "
                 << errGate->getTypeStr() << " in line " << errGate->getLineNo()
                 << "!!" << endl;
            break;
        case REDEF_SYMBOLIC_NAME:
            cerr << "[ERROR] Line " << lineNo + 1 << ": Symbolic name for \""
                 << errMsg << errInt << "\" is redefined!!" << endl;
            break;
        case REDEF_CONST:
            cerr << "[ERROR] Line " << lineNo + 1 << ", Col " << colNo + 1
                 << ": Cannot redefine const (" << errInt << ")!!" << endl;
            break;
        case NUM_TOO_SMALL:
            cerr << "[ERROR] Line " << lineNo + 1 << ": " << errMsg
                 << " is too small (" << errInt << ")!!" << endl;
            break;
        case NUM_TOO_BIG:
            cerr << "[ERROR] Line " << lineNo + 1 << ": " << errMsg
                 << " is too big (" << errInt << ")!!" << endl;
            break;
        default:
            break;
    }
    return false;
}

/**************************************************************/
/*   class CirMgr member functions for circuit construction   */
/**************************************************************/
bool CirMgr::readCircuit(const string& name) {
    ifstream fin;
    fin.open(fileName);
    if (!fin) {
        cout << "can not open file" << endl;
        return false;
    }
    return readCircuit(fin);
}

bool CirMgr::readCircuit(ifstream& fin) {
    // ifstream fin;
    // fin.open(fileName);
    if (!fin) {
        cout << "can not open file" << endl;
        return false;
    }
    char buffer[20];
    string agg;
    int inputSize, allid, latchSize, outputSize, AIGsize, content, content1,
        content2;
    // head line
    fin >> agg >> allid >> inputSize >> latchSize >> outputSize >> AIGsize;
    all.clear();
    // const zero id=0
    all.resize(allid + outputSize + 1);
    ioname = vector<string>(inputSize + outputSize);
    // POsIdBias = allid+1;
    // for CONST
    CirGate* c = new CirGate(0, CONST_GATE, -1, -1, false, false);
    all[0] = c;
    ConstGates.push_back(c);

    // for input id
    for (int i = 0; i < inputSize; ++i) {
        fin >> content;
        int id = content / 2;
        CirGate* temp = new CirGate(id, PI_GATE, -1, -1, false, false);
        all[id] = temp;
        PIs.push_back(temp);
    }
    // for output id & fanin gate id
    int outputid = allid + 1;
    for (int i = 0; i < outputSize; ++i) {
        fin >> content;
        int fanin0id = content / 2;
        bool fanin0cp = content % 2 == 1 ? true : false;
        CirGate* temp =
            new CirGate(outputid, PO_GATE, fanin0id, -1, fanin0cp, false);
        all[outputid] = temp;
        POs.push_back(temp);
        ++outputid;
    }

    // 60 AIG node id
    for (int i = 0; i < AIGsize; ++i) {
        fin >> content >> content1 >> content2;
        int id = content / 2;
        int fanin0id = content1 / 2;
        int fanin1id = content2 / 2;
        bool fanin0cp = content1 % 2 == 1 ? true : false;
        bool fanin1cp = content2 % 2 == 1 ? true : false;
        CirGate* temp =
            new CirGate(id, AIG_GATE, fanin0id, fanin1id, fanin0cp, fanin1cp);
        all[id] = temp;
        AIGs.push_back(temp);
    }

    // pick undefind gates (AIG)
    for (size_t i = 0; i < AIGs.size(); ++i) {
        CirGate* g = AIGs[i];
        int id = g->id;
        int fanin0 = g->fanin0id;
        int fanin1 = g->fanin1id;
        // 1. type: defined but not used
        bool isUsed = false;
        // ### search AIG fanin
        for (size_t j = 0; j < AIGs.size(); ++j) {
            if (j == i) continue;
            if (AIGs[j]->fanin0id == id || AIGs[j]->fanin1id == id) {
                isUsed = true;
                break;
            }
        }
        // ### search OUT fanin
        if (!isUsed) {
            for (size_t j = 0; j < POs.size(); ++j) {
                if (POs[j]->fanin0id == id) {
                    isUsed = true;
                    break;
                }
            }
        }
        if (!isUsed) {
            g->type = AIG_GATE;
            UnusedGates.push_back(g);
        }
        // 2. type: a gate with floating fanins
        if ((all[fanin0] == 0 || all[fanin1] == 0)) {
            if (all[fanin0] == 0 && all[fanin1] == 0)
                g->type = UNDEF_GATE;
            else
                g->type = AIG_GATE;
            FloatGates.push_back(g);
        }
    }
    // pick floating or unused gates gates (PI)
    for (size_t i = 0; i < PIs.size(); ++i) {
        CirGate* g = PIs[i];
        int id = g->id;
        // 1. type: defined but not used
        bool isUsed = false;
        // ### search AIG fanin
        for (size_t j = 0; j < AIGs.size(); ++j) {
            if (AIGs[j]->fanin0id == id || AIGs[j]->fanin1id == id) {
                isUsed = true;
                break;
            }
        }
        // ### search OUT fanin
        if (!isUsed) {
            for (size_t j = 0; j < POs.size(); ++j) {
                if (POs[j]->fanin0id == id) {
                    isUsed = true;
                    break;
                }
            }
        }
        if (!isUsed) {
            g->type = UNDEF_GATE;
            UnusedGates.push_back(g);
        }
    }
    // check alls to generate AIGs(PIs)'s fanout
    for (size_t i = 1; i < all.size(); ++i) {
        if (all[i] != 0) {
            if (all[i]->type == PO_GATE) {
                if (all[i]->fanin0id != -1) {
                    CirGate* fanin = getGate(all[i]->fanin0id);
                    if (fanin != 0) {
                        fanin->fanoutid.push_back(
                            make_pair(i, all[i]->fanin0cp));
                    }
                }
            } else {
                if (all[i]->fanin0id != -1) {
                    CirGate* fanin0 = getGate(all[i]->fanin0id);
                    if (fanin0 != 0) {
                        fanin0->fanoutid.push_back(
                            make_pair(i, all[i]->fanin0cp));
                    }
                }
                if (all[i]->fanin1id != -1) {
                    CirGate* fanin1 = getGate(all[i]->fanin1id);
                    if (fanin1 != 0) {
                        fanin1->fanoutid.push_back(
                            make_pair(i, all[i]->fanin1cp));
                    }
                }
            }
        }
    }

    // for PIO named
    string str;
    while (fin >> str) {
        if (str == "c") break;
        if (str[0] == 'i') {
            str.erase(str.begin());
            int index = stoi(str);
            fin >> str;
            if (fin.bad()) {
                return false;
            }
            ioname[index] = str;
        } else if (str[0] == 'o') {
            str.erase(str.begin());
            int index = stoi(str);
            fin >> str;
            if (fin.bad()) {
                return false;
            }
            ioname[index + inputSize] = str;
        } else {
            return false;
        }
    }
    fin.close();
    this->fileName = fileName;
    // cout << "readCircuit success!";
    // all[0]->cirMgr = this;

    // build DFS trace
    trace.clear();
    for (size_t i = 0; i < POs.size(); ++i) {
        CirGate* curr = POs[i];
        DFS(curr);
    }

    return true;
}

/**********************************************************/
/*   class CirMgr member functions for circuit printing   */
/**********************************************************/
/*********************
Circuit Statistics
==================
  PI          20
  PO          12
  AIG        130
------------------
  Total      162
*********************/
void CirMgr::printSummary() const {
    cout << endl;
    cout << "Circuit Statistics" << endl;
    cout << "==================" << endl;
    cout << "  " << left << setw(10) << "PI" << right << setw(4) << PIs.size()
         << endl;
    cout << "  " << left << setw(10) << "PO" << right << setw(4) << POs.size()
         << endl;
    cout << "  " << left << setw(10) << "AIG" << right << setw(4) << AIGs.size()
         << endl;
    cout << "------------------" << endl;
    cout << "  " << left << setw(10) << "Total" << right << setw(4)
         << PIs.size() + POs.size() + AIGs.size() << endl;
}

void CirMgr::printNetlist() {
    /*
       cout << endl;
       for (unsigned i = 0, n = _dfsList.size(); i < n; ++i) {
          cout << "[" << i << "] ";
          _dfsList[i]->printGate();
       }
    */
    vector<bool>(all.size(), false);
    // int currid;
    cout << endl;
    // for (size_t i = 0; i < POs.size(); ++i) {
    //     CirGate* curr = POs[i];
    //     DFS(curr);
    // }
    // check trace
    for (size_t i = 0; i < trace.size(); ++i) {
        CirGate* curr = all[trace[i]];
        cout << "[" << i << "] ";
        curr->printGate();
        if (curr->type == PI_GATE || curr->type == PO_GATE) {
            if (getIOName(curr) != "") {
                cout << " (" << getIOName(curr) << ")";
            }
        }
        cout << endl;
    }
}

void CirMgr::printPIs() const {
    cout << "PIs of the circuit:";
    for (size_t i = 0; i < PIs.size(); ++i) {
        cout << " " << PIs[i]->id;
    }
    cout << endl;
}

void CirMgr::printPOs() const {
    cout << "POs of the circuit:";
    for (size_t i = 0; i < POs.size(); ++i) {
        cout << " " << POs[i]->id;
    }
    cout << endl;
}

void CirMgr::printFloatGates() const {
    if (FloatGates.size() != 0) {
        cout << "Gates with floating fanin(s):";
        for (size_t i = 0; i < FloatGates.size(); ++i) {
            cout << " " << FloatGates[i]->id;
        }
        cout << endl;
    }
    if (UnusedGates.size() != 0) {
        cout << "Gates defined but not used  :";
        for (size_t i = 0; i < UnusedGates.size(); ++i) {
            cout << " " << UnusedGates[i]->id;
        }
        cout << endl;
    }
}

void CirMgr::printFECPairs() const {
    for (size_t i = 0; i < SimGroups.size(); ++i) {
        cout << "[" << i << "]"
             << " ";
        for (size_t j = 0; j < SimGroups[i].size(); ++j) {
            if (SimGroups[i][j].second) cout << "!";
            cout << SimGroups[i][j].first->id << " ";
        }
        cout << endl;
    }
}

void CirMgr::writeAag(ostream& outfile) {
    // get DFS
    // vector<int> trace;
    // for (size_t i = 0; i < POs.size(); ++i) {
    //     CirGate* curr = POs[i];
    //     DFS(curr);
    // }

    // write to monitor
    stringstream ss;
    ss << "aag " << all.size() - POs.size() - 1 << " " << PIs.size() << " 0 "
       << POs.size() << " "
       << trace.size() - PIs.size() - POs.size() - ConstGates.size() + 1
       << "\n";
    for (size_t i = 0; i < PIs.size(); ++i) {
        ss << PIs[i]->id * 2 << "\n";
    }
    for (size_t i = 0; i < POs.size(); ++i) {
        ss << (POs[i]->fanin0cp ? POs[i]->fanin0id * 2 + 1
                                : POs[i]->fanin0id * 2)
           << "\n";
    }
    for (size_t i = 0; i < trace.size(); ++i) {
        CirGate* g = getGate(trace[i]);
        GateType temp = g->type;
        if (temp != PO_GATE && temp != PI_GATE && temp != CONST_GATE) {
            ss << g->id * 2 << " "
               << (g->fanin0cp ? g->fanin0id * 2 + 1 : g->fanin0id * 2) << " "
               << (g->fanin1cp ? g->fanin1id * 2 + 1 : g->fanin1id * 2) << "\n";
        }
    }
    for (size_t i = 0; i < PIs.size(); ++i) {
        if (ioname[i] != "") ss << "i" << i << " " << ioname[i] << "\n";
    }
    for (size_t i = 0; i < POs.size(); ++i) {
        if (ioname[i] != "")
            ss << "o" << i << " " << ioname[i + PIs.size()] << "\n";
    }

    // comment
    ss << "c\nHi! 期末順利\n";
    outfile << ss.str();
}

void CirMgr::writeGate(ostream& outfile, CirGate* g) {
    cout << "writeGate" << endl;
}

/**********************************************************/
/*   class CirMgr member functions for other              */
/**********************************************************/

string
CirMgr::getIOName(const CirGate* g) const {
    if (g->type == PO_GATE)
        return ioname[g->id - (all.size() - POs.size()) + PIs.size()];
    if (g->type == PI_GATE) {
        string name;
        for (size_t i = 0; i < PIs.size(); ++i) {
            if (PIs[i]->id == g->id) {
                name = ioname[i];
                break;
            }
        }
        return name;
    }
    return "";
}

void CirMgr::DFS(CirGate* g) {
    if (find(trace.begin(), trace.end(), g->id) == trace.end()) {
        if (g->fanin0id != -1) {
            if (all[g->fanin0id] != 0) DFS(all[g->fanin0id]);
        }
        if (g->fanin1id != -1) {
            if (all[g->fanin1id] != 0) DFS(all[g->fanin1id]);
        }
        trace.push_back(g->id);
    }
}

void CirMgr::updateFanout() {
    // check alls to generate AIGs(PIs)'s fanout
    for (size_t i = 1; i < all.size(); ++i) {
        if (all[i] != 0) {
            all[i]->fanoutid.clear();
        }
    }

    for (size_t i = 1; i < all.size(); ++i) {
        if (all[i] != 0) {
            if (all[i]->type == PO_GATE) {
                if (all[i]->fanin0id != -1) {
                    CirGate* fanin = getGate(all[i]->fanin0id);
                    if (fanin != 0) {
                        fanin->fanoutid.push_back(
                            make_pair(i, all[i]->fanin0cp));
                    }
                }
            } else {
                if (all[i]->fanin0id != -1) {
                    CirGate* fanin0 = getGate(all[i]->fanin0id);
                    if (fanin0 != 0) {
                        fanin0->fanoutid.push_back(
                            make_pair(i, all[i]->fanin0cp));
                    }
                }
                if (all[i]->fanin1id != -1) {
                    CirGate* fanin1 = getGate(all[i]->fanin1id);
                    if (fanin1 != 0) {
                        fanin1->fanoutid.push_back(
                            make_pair(i, all[i]->fanin1cp));
                    }
                }
            }
        }
    }
}

void CirMgr::updateUnusedForPI() {
    UnusedGates.clear();
    // update UnusedList (only PI)
    for (size_t i = 0; i < PIs.size(); ++i) {
        bool isUsed = false;
        for (const auto& fanout : PIs[i]->fanoutid) {
            if (all[fanout.first]) {
                isUsed = true;
            }
        }
        if (!isUsed) UnusedGates.push_back(PIs[i]);
    }
}

void CirMgr::updateAIGs() {
    for (size_t i = 0; i < AIGs.size(); ++i) {
        // cout << "i:" << AIGs[i]->id << endl;
        if (AIGs[i]->id > all.size() || AIGs[i]->fanin0id > all.size() ||
            AIGs[i]->fanin1id > all.size()) {
            // cout << "NULL" << endl;
            AIGs.erase(AIGs.begin() + i);
            --i;
        }
    }
}

void CirMgr::updateTrace() {
    trace.clear();
    for (size_t i = 0; i < POs.size(); ++i) {
        CirGate* curr = POs[i];
        DFS(curr);
    }
}

void CirMgr::updateFloats() {
    FloatGates.clear();
    for (size_t i = 0; i < AIGs.size(); ++i) {
        CirGate* g = AIGs[i];
        int fanin0 = g->fanin0id;
        int fanin1 = g->fanin1id;

        if ((all[fanin0] == 0 || all[fanin1] == 0)) {
            if (all[fanin0] == 0 && all[fanin1] == 0)
                g->type = UNDEF_GATE;
            else
                g->type = AIG_GATE;
            FloatGates.push_back(g);
        }
    }
}
