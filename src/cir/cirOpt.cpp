/****************************************************************************
  FileName     [ cirSim.cpp ]
  PackageName  [ cir ]
  Synopsis     [ Define cir optimization functions ]
  Author       [ Chung-Yang (Ric) Huang ]
  Copyright    [ Copyleft(c) 2008-present LaDs(III), GIEE, NTU, Taiwan ]
****************************************************************************/

#include <cassert>

#include "cirGate.h"
#include "cirMgr.h"
#include "util.h"

using namespace std;

// TODO: Please keep "CirMgr::sweep()" and "CirMgr::optimize()" for cir cmd.
//       Feel free to define your own variables or functions

/*******************************/
/*   Global variable and enum  */
/*******************************/

/**************************************/
/*   Static varaibles and functions   */
/**************************************/

/**************************************************/
/*   Public member functions about optimization   */
/**************************************************/
// Remove unused gates
// DFS list should NOT be changed
// UNDEF, float and unused list may be changed
void CirMgr::sweep() {
    vector<bool> existTable(all.size(), false);
    for (size_t i = 0; i < trace.size(); ++i) {
        existTable[trace[i]] = true;
    }
    for (size_t i = PIs.size(); i < all.size(); ++i) {
        if (!all[i]) continue;
        if (all[i]->type == PO_GATE) break;
        if (all[i]->type == UNDEF_GATE) {
            cout << "Sweeping: " << all[i]->getTypeName() << "(" << all[i]->id << ") removed..." << endl;
        }
        if (!existTable[i] && all[i]->type != PI_GATE) {
            cout << "Sweeping: " << all[i]->getTypeName() << "(" << all[i]->id << ") removed..." << endl;
            for (size_t j = 0; j < FloatGates.size(); ++j) {
                if (FloatGates[j]->id == (int)i) {
                    FloatGates.erase(FloatGates.begin() + j);
                    break;
                }
            }
            for (size_t k = 0; k < AIGs.size(); ++k) {
                if (AIGs[k]->id == (int)i) {
                    AIGs.erase(AIGs.begin() + k);
                    break;
                }
            }
            // clean its fanin0/1
            if (all[all[i]->fanin0id]) {
                CirGate* fanin0 = all[all[i]->fanin0id];
                for (size_t j = 0; j < fanin0->fanoutid.size(); ++j) {
                    if (fanin0->fanoutid[j].first == (int)i) {
                        fanin0->fanoutid.erase(fanin0->fanoutid.begin() + j);
                        break;
                    }
                }
            }
            if (all[i]->fanin1id != -1 && all[all[i]->fanin1id]) {
                CirGate* fanin1 = all[all[i]->fanin1id];
                for (size_t j = 0; j < fanin1->fanoutid.size(); ++j) {
                    if (fanin1->fanoutid[j].first == (int)i) {
                        fanin1->fanoutid.erase(fanin1->fanoutid.begin() + j);
                        break;
                    }
                }
            }
            delete all[i];
            all[i] = 0;
        }
    }

    // UnusedGates.clear();
    // // update UnusedList (only PI)
    // for (size_t i = 0; i < PIs.size(); ++i) {
    //     bool isUsed = false;
    //     for (const auto& fanout : PIs[i]->fanoutid) {
    //         if (all[fanout.first]) {
    //             isUsed = true;
    //         }
    //     }
    //     if (!isUsed) UnusedGates.push_back(PIs[i]);
    // }
    updateUnusedForPI();
}
// Recursively simplifying from POs;
// _dfsList needs to be reconstructed afterwards
// UNDEF gates may be delete if its fanout becomes empty...
void CirMgr::optimize() {
    if (isSimulated) {
        cout << "Error: circuit has been simulated!! Do \"CIRFraig\" first !!" << endl;
        return;
    }
    for (size_t i = 0; i < trace.size(); ++i) {
        // cout << "now trace" << trace[i] << endl;
        CirGate* curr = all[trace[i]];
        if (curr->type == PI_GATE || curr->type == CONST_GATE) continue;
        if (curr->type == PO_GATE) continue;

        // (1) if fanin0 = 0 -> all 0
        if ((curr->fanin0id == 0 && curr->fanin0cp == false) || (curr->fanin1id == 0 && curr->fanin1cp == false)) {
            for (size_t j = 0; j < curr->fanoutid.size(); ++j) {
                if (!all[curr->fanoutid[j].first]) continue;

                if (all[curr->fanoutid[j].first]->fanin0id == curr->id) {
                    all[curr->fanoutid[j].first]->fanin0id = 0;

                } else if (all[curr->fanoutid[j].first]->fanin1id == curr->id) {
                    all[curr->fanoutid[j].first]->fanin1id = 0;
                }
            }
            cout << "Simplifying: " << 0 << " merging " << curr->id << "..." << endl;
            all[curr->id] = 0;
            delete curr;
            curr = NULL;
        }
        // (2) if fanin0 = 1 and #$%
        else if (curr->fanin0id == 0 && curr->fanin0cp == true && curr->fanin1id != 0) {
            for (size_t j = 0; j < curr->fanoutid.size(); ++j) {
                if (!all[curr->fanoutid[j].first]) continue;

                if (all[curr->fanoutid[j].first]->fanin0id == curr->id) {
                    all[curr->fanoutid[j].first]->fanin0id = curr->fanin1id;
                    // all[curr->fanoutid[j].first]->fanoutid.push_back(make_pair(curr, all[i]->fanin0cp));
                    if (curr->fanin1cp) all[curr->fanoutid[j].first]->fanin0cp = !all[curr->fanoutid[j].first]->fanin0cp;

                } else if (all[curr->fanoutid[j].first]->fanin1id == curr->id) {
                    all[curr->fanoutid[j].first]->fanin1id = curr->fanin1id;
                    if (curr->fanin1cp) all[curr->fanoutid[j].first]->fanin1cp = !all[curr->fanoutid[j].first]->fanin1cp;
                }
            }
            cout << "Simplifying: " << curr->fanin1id << " merging ";
            if (curr->fanin1cp) {
                cout << "!";
            }
            cout << curr->id << "..." << endl;
            all[curr->id] = 0;
            delete curr;
            curr = 0;
        }

        // (2) if fanin1 = 1 and #$%
        else if (curr->fanin1id == 0 && curr->fanin1cp == true && curr->fanin0id != 0) {
            for (size_t j = 0; j < curr->fanoutid.size(); ++j) {
                if (!all[curr->fanoutid[j].first]) continue;
                if (all[curr->fanoutid[j].first]->fanin0id == curr->id) {
                    all[curr->fanoutid[j].first]->fanin0id = curr->fanin0id;
                    if (curr->fanin0cp) all[curr->fanoutid[j].first]->fanin0cp = !all[curr->fanoutid[j].first]->fanin0cp;
                } else if (all[curr->fanoutid[j].first]->fanin1id == curr->id) {
                    all[curr->fanoutid[j].first]->fanin1id = curr->fanin0id;
                    if (curr->fanin0cp) all[curr->fanoutid[j].first]->fanin1cp = !all[curr->fanoutid[j].first]->fanin1cp;
                }
            }
            cout << "Simplifying: " << curr->fanin0id << " merging ";
            if (curr->fanin0cp) {
                cout << "!";
            }
            cout << curr->id << "..." << endl;
            all[curr->id] = 0;
            delete curr;
            curr = 0;
        }
        // (3) fanin0 = fanin1
        else if (curr->fanin0id == curr->fanin1id && curr->fanin0cp == curr->fanin1cp) {
            for (size_t j = 0; j < curr->fanoutid.size(); ++j) {
                if (!all[curr->fanoutid[j].first]) continue;

                if (all[curr->fanoutid[j].first]->fanin0id == curr->id) {
                    all[curr->fanoutid[j].first]->fanin0id = curr->fanin0id;
                    if (curr->fanin0cp) all[curr->fanoutid[j].first]->fanin0cp = !all[curr->fanoutid[j].first]->fanin0cp;
                } else if (all[curr->fanoutid[j].first]->fanin1id == curr->id) {
                    all[curr->fanoutid[j].first]->fanin1id = curr->fanin0id;
                    if (curr->fanin0cp) all[curr->fanoutid[j].first]->fanin1cp = !all[curr->fanoutid[j].first]->fanin1cp;
                }
            }
            cout << "Simplifying: " << curr->fanin0id << " merging ";
            if (curr->fanin0cp) {
                cout << "!";
            }
            cout << curr->id << "..." << endl;
            all[curr->id] = 0;
            delete curr;
            curr = 0;
        }
        // (4) fanin0 = ~ fanin1
        else if (curr->fanin0id == curr->fanin1id && curr->fanin0cp != curr->fanin1cp) {
            for (size_t j = 0; j < curr->fanoutid.size(); ++j) {
                if (!all[curr->fanoutid[j].first]) continue;

                if (all[curr->fanoutid[j].first]->fanin0id == curr->id) {
                    all[curr->fanoutid[j].first]->fanin0id = 0;

                } else if (all[curr->fanoutid[j].first]->fanin1id == curr->id) {
                    all[curr->fanoutid[j].first]->fanin1id = 0;
                }
            }
            cout << "Simplifying: " << 0 << " merging " << curr->id << "..." << endl;
            all[curr->id] = 0;
            delete curr;
            curr = 0;
        }
    }

    // update AIG
    updateAIGs();

    // updateFanout
    updateFanout();

    // update UnusedList (only PI)
    updateUnusedForPI();

    // update DFS
    updateTrace();
}

/***************************************************/
/*   Private member functions about optimization   */
/***************************************************/
