/****************************************************************************
  FileName     [ cirSim.cpp ]
  PackageName  [ cir ]
  Synopsis     [ Define cir simulation functions ]
  Author       [ Chung-Yang (Ric) Huang ]
  Copyright    [ Copyleft(c) 2008-present LaDs(III), GIEE, NTU, Taiwan ]
****************************************************************************/

#include <stdlib.h>
#include <time.h>

#include <algorithm>
#include <bitset>
#include <cassert>
#include <cmath>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <random>

#include "cirDef.h"
#include "cirGate.h"
#include "cirMgr.h"
// #include "util.h"

using namespace std;

// TODO: Keep "CirMgr::randimSim()" and "CirMgr::fileSim()" for cir cmd.
//       Feel free to define your own variables or functions

/*******************************/
/*   Global variable and enum  */
/*******************************/

/**************************************/
/*   Static varaibles and functions   */
/**************************************/

/************************************************/
/*   Public member functions about Simulation   */
/************************************************/
void CirMgr::randomSim() {
    if (inputId2Pattern.empty()) {
        inputId2Pattern = vector<int>(all.size());
        for (size_t i = 0; i < PIs.size(); ++i) {
            inputId2Pattern[PIs[i]->id] = i;
        }
    }

    // gen tattern
    int patternSize = 0;  // 1 -> 64, 2 -> 128...
    random_device rd;
    mt19937_64 generator(rd());
    uniform_int_distribution<uint64_t> distribution(0, numeric_limits<uint64_t>::max());
    int limits = 8;
    if (PIs.size() > 100) {
        limits = 20;
    }
    if (PIs.size() > 1000) {
        limits = 50;
    }

    while (patternSize <= limits) {
        inputPattern.clear();
        for (size_t i = 0; i < PIs.size(); ++i) {
            inputPattern.push_back(distribution(generator));
        }
        // if (PIs[0]->pattern == 0) {
        //     for (size_t i = 0; i < PIs.size(); ++i) {
        //         PIs[i]->pattern = inputPattern[i];
        //     }
        // }
        simulate64times();
        ++patternSize;
    }

    isSimulated = true;
}

void CirMgr::fileSim(ifstream& patternFile) {
    if (inputId2Pattern.empty()) {
        inputId2Pattern = vector<int>(all.size());
        for (size_t i = 0; i < PIs.size(); ++i) {
            inputId2Pattern[PIs[i]->id] = i;
        }
    }

    if (patternFile.is_open()) {
        string line;
        int all_lineCount = 0;
        int count_64 = 0;
        inputPattern.clear();
        inputPattern = vector<uint64_t>(PIs.size());
        // while (getline(patternFile, line)) {

        while (patternFile >> line) {
            if (line.size() != PIs.size()) {
                cout << "Error: Pattern(" << line << ") length(" << line.size() << ") does not match the number of inputs(" << PIs.size() << ") in a circuit !!" << endl;
                return;
            }
            for (size_t i = 0; i < PIs.size(); ++i) {
                if (line[i] == '0')
                    inputPattern[i] = inputPattern[i] << 1;
                else if (line[i] == '1') {
                    inputPattern[i] = inputPattern[i] << 1;
                    inputPattern[i] += 1;
                } else {
                    cout << "  Error: Pattern(" << line << ") contains a non-0/1 character('" << line[i] << "')." << endl;
                    cout << "0 patterns simulated." << endl;
                    inputPattern.clear();
                    inputPattern = vector<uint64_t>(PIs.size());
                    return;
                }
            }
            ++count_64;
            ++all_lineCount;
            allWriteLine = all_lineCount;
            if (count_64 == 64) {
                count_64 = 0;
                // if (PIs[0]->pattern == 0)
                //     for (size_t i = 0; i < PIs.size(); ++i) {
                //         PIs[i]->pattern = inputPattern[i];
                //     }
                simulate64times();
                inputPattern.clear();
                inputPattern = vector<uint64_t>(PIs.size());
            }
        }
        // cout << "all_lineCount: " << all_lineCount << endl;
        // fill remains with zero
        while (count_64 != 64) {
            for (size_t i = 0; i < PIs.size(); ++i) {
                inputPattern[i] = inputPattern[i] << 1;
            }
            ++count_64;
        }
        simulate64times();
        inputPattern.clear();
        inputPattern = vector<uint64_t>(PIs.size());
        patternFile.close();
        cout << all_lineCount << " patterns simulated." << endl;
        isSimulated = true;
    } else {
        cout << "Failed to open the file." << endl;
    }
}

/*************************************************/
/*   Private member functions about Simulation   */
/*************************************************/

// new true == need to change
bool CirMgr::findPattern(CirGate* g, vector<bool>& isUpdate) {
    // undefined
    if (g == 0) {
        assert(0);
        return false;
    } else if (g->type == PI_GATE) {
        if (isNoPattern) return true;
        return (inputPattern[inputId2Pattern[g->id]] != g->pattern);
    } else if (g->type == CONST_GATE) {
        g->pattern = 0;
        if (isNoPattern) return true;
        return false;
    } else if (g->type == PO_GATE) {
        if (findPattern(all[g->fanin0id], isUpdate)) {
            uint64_t fanin0 = all[g->fanin0id]->type == PI_GATE ? inputPattern[inputId2Pattern[g->fanin0id]] : all[g->fanin0id]->pattern;
            if (g->fanin0cp)
                g->pattern = ~fanin0;
            else
                g->pattern = fanin0;
            return true;
        } else {
            return false;
        }
    } else {
        if (isUpdate[g->id]) {
            return true;
        }
        isUpdate[g->id] = true;
        // cout << g->id << "here: call  " << g->fanin0id << "  " << g->fanin1id << endl;
        bool isFanin0Change = findPattern(all[g->fanin0id], isUpdate);
        bool isFanin1Change = findPattern(all[g->fanin1id], isUpdate);
        if (isFanin0Change || isFanin1Change) {
            uint64_t fanin0 = all[g->fanin0id]->type == PI_GATE ? inputPattern[inputId2Pattern[g->fanin0id]] : all[g->fanin0id]->pattern;
            uint64_t fanin1 = all[g->fanin1id]->type == PI_GATE ? inputPattern[inputId2Pattern[g->fanin1id]] : all[g->fanin1id]->pattern;
            // different situation
            if (g->fanin0cp && g->fanin1cp) {
                g->pattern = ((~fanin0) & (~fanin1));
            } else if (g->fanin0cp & !g->fanin1cp) {
                g->pattern = ((~fanin0) & fanin1);
            } else if (!g->fanin0cp && g->fanin1cp) {
                g->pattern = (fanin0 & (~fanin1));
            } else {
                g->pattern = (fanin0 & fanin1);
            }
            return true;
        } else {
            return false;
        }
    }
}
void CirMgr::simulate64times() {
    vector<uint64_t> outputPattern(POs.size());
    bool result;
    vector<bool> isUpdate(all.size(), false);

    for (size_t i = 0; i < POs.size(); ++i) {
        result = findPattern(POs[i], isUpdate);
    }
    for (size_t i = 0; i < PIs.size(); ++i) {
        PIs[i]->pattern = inputPattern[i];
    }
    isNoPattern = false;
    if (SimGroups.empty()) {
        vector<pair<CirGate*, bool>> temp;
        all[0]->pattern = 0;
        temp.push_back(make_pair(all[0], false));
        for (size_t i = 0; i < POs.size(); ++i) {
            temp.push_back(make_pair(POs[i], false));
        }
        SimGroups.push_back(temp);
    }

    // gen group
    for (size_t i = 0; i < SimGroups.size(); ++i) {
        vector<pair<CirGate*, bool>> temp;
        uint64_t head_bitValue = SimGroups[i][0].first->pattern;
        // cout << " SimGroups: " << i << "  head: " << SimGroups[i][0].first->id << endl;
        if (SimGroups[i][0].second) head_bitValue = (~head_bitValue);

        for (size_t j = 1; j < SimGroups[i].size(); ++j) {
            uint64_t bitValue = SimGroups[i][j].first->pattern;
            if (SimGroups[i][j].second) bitValue = (~bitValue);
            if ((~bitValue) == head_bitValue) {
                SimGroups[i].push_back(make_pair(SimGroups[i][j].first, !SimGroups[i][j].second));
            }
            if (bitValue != head_bitValue) {
                temp.push_back(SimGroups[i][j]);
                SimGroups[i].erase(SimGroups[i].begin() + j);
                --j;
            }
        }
        if (!temp.empty()) {
            // cout << "new group!" << endl;
            SimGroups.push_back(temp);
            temp.clear();
        }
    }
    for (size_t i = 0; i < SimGroups.size(); ++i) {
        if (SimGroups[i].size() == 1) {
            SimGroups.erase(SimGroups.begin() + i);
            --i;
        }
    }
    // cout << "Current simgroupSize: " << SimGroups.size() << endl;
}

void CirMgr::writeLog() {
    // vector<uint32_t>& outputPattern
    for (int times = 0; times < 64; ++times) {
        if (currWriteLine >= allWriteLine) {
            // reset
            currWriteLine = 0;
            allWriteLine = 0;
            break;
        }
        // input pattern
        for (size_t i = 0; i < inputPattern.size(); ++i) {
            *_simLog << (inputPattern[i] >> (63 - times) & 1);
        }
        *_simLog << " ";
        // output pattern
        for (size_t i = 0; i < POs.size(); ++i) {
            *_simLog << (POs[i]->pattern >> (63 - times) & 1);
        }
        *_simLog << "\n";
        ++currWriteLine;
    }
}

void CirMgr::findNecessary(CirGate* g, set<int>& set, int& patternShift) {
    assert(g != 0);
    if (g->type == PI_GATE) {
        set.insert(id2Idx[g->getId()]);
        return;
    }
    if (g->type == PO_GATE) {
        findNecessary(all[g->fanin0id], set, patternShift);
        return;
    }
    if (g->type == CONST_GATE) {
        return;
    }
    // when g = 1 -> care both fanin
    if (((g->pattern >> patternShift) & 1) == 1) {
        findNecessary(all[g->fanin0id], set, patternShift);
        findNecessary(all[g->fanin1id], set, patternShift);
    }
    // g = 0 -> care about zero side
    else {
        bool fanin0Value = ((all[g->fanin0id]->pattern >> patternShift) & 1) == 1 ? true : false;
        if (g->fanin0cp) fanin0Value = !fanin0Value;
        bool fanin1Value = ((all[g->fanin1id]->pattern >> patternShift) & 1) == 1 ? true : false;
        if (g->fanin1cp) fanin1Value = !fanin1Value;

        assert(!(fanin1Value && fanin0Value));

        if ((!fanin0Value) && (!fanin1Value)) {
            random_device rd;
            mt19937 gen(rd());
            uniform_int_distribution<> distrib(0, 1);
            int randomValue = distrib(gen);
            if (randomValue == 0) {
                findNecessary(all[g->fanin0id], set, patternShift);
            } else
                // randomValue == 1
                findNecessary(all[g->fanin1id], set, patternShift);
        }
        else if (fanin0Value == 0) {
            findNecessary(all[g->fanin0id], set, patternShift);
        } else {
            findNecessary(all[g->fanin1id], set, patternShift);
        }
    }
}

vector<set<int>> CirMgr::getNecessary(const vector<int>& assign_Input, const vector<int>& assign_Output) {
    double inputSize = assign_Input.size();
    int outputSize = assign_Output.size();
    assert(inputSize == PIs.size());
    assert(outputSize == POs.size());

    uint64_t zero, one;
    zero = 0;
    for (int i = 0; i < 64; ++i) {
        one = one << 1;
        one += 1;
    }

    inputPattern.clear();
    inputPattern = vector<uint64_t>(PIs.size());

    for (int i = 0; i < inputSize; ++i) {
        if (assign_Input[i] == 0)
            inputPattern[i] = zero;
        else if (assign_Input[i] == 1)
            inputPattern[i] = one;
        else
            assert(0);
    }
    // cout << "Origin Input:";
    // for (int i = 0; i < inputSize; ++i) cout << assign_Input[i] << " ";
    // cout << "Origin Output:";
    // for (int i = 0; i < outputSize; ++i) cout << assign_Output[i] << " ";
    // cout << endl;
    simulate64times();
    vector<set<int>> necessarys;
    set<int> necessry;
    int patternShift = 0;
    for (int i = 0; i < POs.size(); ++i) {
        necessry.clear();
        findNecessary(POs[i], necessry, patternShift);
        necessarys.push_back(necessry);
    }
    // cout << "Necessarys" << endl;
    // for (int i = 0; i < necessarys.size(); ++i) {
    //     cout << i << ": ";
    //     for (set<int>::iterator it = necessarys[i].begin(); it != necessarys[i].end(); it++)
    //         cout << *it << " ";
    //     cout << endl;
    return necessarys;
}


// random simulate and return PI/PO/NecessaryPI
void CirMgr::randomSim2Necessary(vector<vector<int>>& assign_Input, vector<vector<int>>& assign_Output, vector<vector<set<int>>>& necessarys_64bit) {
    random_device rd;
    mt19937_64 generator(rd());
    uniform_int_distribution<uint64_t> distribution(0, numeric_limits<uint64_t>::max());
    inputPattern.clear();
    for (size_t i = 0; i < PIs.size(); ++i) {
        inputPattern.push_back(distribution(generator));
    }
    simulate64times();

    vector<set<int>> necessarys;
    set<int> necessry;
    vector<int> pattern;
    for (int patternShift = 0; patternShift < 64; ++patternShift) {
        necessarys.clear();
        for (int i = 0; i < POs.size(); ++i) {
            necessry.clear();
            findNecessary(POs[i], necessry, patternShift);
            necessarys.push_back(necessry);
        }
        necessarys_64bit.push_back(necessarys);

        // record output assign
        pattern.clear();
        for (int i = 0; i < POs.size(); ++i) {
            pattern.push_back(((POs[i]->pattern >> patternShift) & 1));
        }
        assign_Output.push_back(pattern);

        // record input assign
        pattern.clear();
        for (int i = 0; i < PIs.size(); ++i) {
            pattern.push_back(((inputPattern[i] >> patternShift) & 1));
        }
        assign_Input.push_back(pattern);
    }
}
