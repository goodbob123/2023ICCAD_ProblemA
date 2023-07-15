/****************************************************************************
  FileName     [ cirSim.cpp ]
  PackageName  [ cir ]
  Synopsis     [ Define cir simulation functions ]
  Author       [ Chung-Yang (Ric) Huang ]
  Copyright    [ Copyleft(c) 2008-present LaDs(III), GIEE, NTU, Taiwan ]
****************************************************************************/

#include <algorithm>
#include <bitset>
#include <cassert>
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
    // uint32_t randomNum1 = distribution(generator);
    // uint32_t randomNum2 = distribution(generator);
    // cout << "Random number: " << bitset<32>(randomNum1) << endl;
    // cout << "Random number: " << bitset<32>(randomNum2) << endl;

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
        limits = 200;
    }
    if (PIs.size() > 1000) {
        limits = 1000;
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
    // cout << "now GroupSize: " << SimGroups.size() << endl;
    // cout << patternSize * 64 << " patterns simulated." << endl;
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
            // cout << line << endl;
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

// old
// uint64_t CirMgr::findPattern(CirGate* g) {
//     // if (g != 0) {
//     //     cout << "nowGate: " << g->id << " " << g->getTypeName()
//     // }
//     // undefined
//     if (g == 0) {
//         return 0;
//     } else if (g->type == PI_GATE) {
//         return inputPattern[g->id - 1];
//     } else if (g->type == CONST_GATE) {
//         g->pattern = 0;
//         return 0;
//     } else if (g->type == PO_GATE) {
//         uint64_t fanin0 = findPattern(all[g->fanin0id]);
//         if (g->fanin0cp) fanin0 = (~fanin0);
//         g->pattern = fanin0;
//         return fanin0;
//     }

//     else {
//         uint64_t fanin0 = findPattern(all[g->fanin0id]);
//         uint64_t fanin1 = findPattern(all[g->fanin1id]);

//         // different situation
//         if (g->fanin0cp && g->fanin1cp) {
//             g->pattern = ((~fanin0) & (~fanin1));
//             return ((~fanin0) & (~fanin1));
//         } else if (g->fanin0cp & !g->fanin1cp) {
//             g->pattern = (~fanin0) & fanin1;
//             return (~fanin0) & fanin1;
//         } else if (!g->fanin0cp && g->fanin1cp) {
//             g->pattern = fanin0 & (~fanin1);
//             return fanin0 & (~fanin1);
//         } else {
//             g->pattern = (fanin0 & fanin1);
//             return (fanin0 & fanin1);
//         }
//     }
// }

// new true == need to change
bool CirMgr::findPattern(CirGate* g, vector<bool>& isUpdate) {
    // if (g != 0) {
    //     cout << "nowGate: " << g->id << " " << g->getTypeName()
    // }
    // undefined
    if (g == 0) {
        return false;
    } else if (g->type == PI_GATE) {
        if (isNoPattern) return true;
        return (inputPattern[inputId2Pattern[g->id]] != g->pattern);
    } else if (g->type == CONST_GATE) {
        g->pattern = 0;
        return false;
    } else if (g->type == PO_GATE) {
        if (findPattern(all[g->fanin0id], isUpdate)) {
            if (g->fanin0cp)
                g->pattern = ~all[g->fanin0id]->pattern;
            else
                g->pattern = all[g->fanin0id]->pattern;
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
            // cout << "  " << g->id << "  here" << endl;
            // bool flag = false;
            // if (g->pattern == 0) {
            //     cout << g->id << ": " << g->pattern << " vs negate: " << ~g->pattern << endl;
            //     flag = true;
            // }
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
            // if (flag)
            //     cout << g->id << ": " << g->pattern << " vs negate: " << ~g->pattern << endl;
            // cout << " ---> fanin0: (" << g->fanin0id << ") " << fanin0 << " fanin1: (" << g->fanin1id << ") " << fanin1 << endl;
            return true;
        } else {
            return false;
        }
    }
}
void CirMgr::simulate64times() {
    // cout << "START SIM..." << endl;
    vector<uint64_t> outputPattern(POs.size());
    bool result;
    vector<bool> isUpdate(all.size(), false);

    for (size_t i = 0; i < POs.size(); ++i) {
        // cout << "START: " << POs[i]->id << endl;
        result = findPattern(POs[i], isUpdate);
        // cout << "-----------------------------------------" << endl;
    }
    for (size_t i = 0; i < PIs.size(); ++i) {
        PIs[i]->pattern = inputPattern[i];
    }
    isNoPattern = false;
    // if (_simLog != 0) {
    //     writeLog();
    // }
    if (SimGroups.empty()) {
        vector<pair<CirGate*, bool>> temp;
        all[0]->pattern = 0;
        temp.push_back(make_pair(all[0], false));
        for (size_t i = 0; i < POs.size(); ++i) {
            temp.push_back(make_pair(POs[i], false));
            // temp.push_back(make_pair(AIGs[i],false));
        }
        SimGroups.push_back(temp);
    }

    // cout << "start gen!" << endl;
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

    // old way
    // size_t OriginGroupNum = SimGroups.size();
    // for (int times = 0; times < 32; ++times) {
    //     for (size_t i = 0; i < OriginGroupNum; ++i) {
    //         GateList temp;
    //         bool head_bitValue = (SimGroups[i][0]->pattern >> times) & 1;
    //         for (size_t j = 1; j < SimGroups[i].size(); ++j) {
    //             bool bitValue = (SimGroups[i][j]->pattern >> times) & 1;
    //             if (bitValue != head_bitValue) {
    //                 temp.push_back(SimGroups[i][j]);
    //                 SimGroups[i].erase(SimGroups[i].begin() + j);
    //             }
    //         }
    //         if (!temp.empty())
    //             SimGroups.push_back(temp);
    //     }
    // }
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