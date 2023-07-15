#include <time.h>

#include <fstream>
#include <iostream>
#include <unordered_map>
#include <vector>
#include "bmatchSolver.h"
#include "../cir/cirMgr.h"
#include "./test/sat.h"

class Port;
struct mtx2Mit;
extern unordered_map<int, Var> AAG2VarHashmap;
extern SatSolver matrixSolver;
extern vector<Port> f, g;
extern vector<vector<mtx2Mit>> a, b, c, d;

// aka my GateId
Var AAG2Var(int AAGVar, bool circuitOne);
// bool readCircuit(ifstream&);
static unordered_map<int, int> id2i;
static unordered_map<int, int> id2j;
void createEqualRelationByGroup(const vector<pair<CirGate*, bool>>& group_f,
                                const vector<pair<CirGate*, bool>>& group_g) {
    // TODO: create clasue like paper said

    // unordered_map<Var, int> var2i;  // for mapping f's var to matrix pos
    // unordered_map<Var, int> var2j;  // for mapping g's var to matrix pos
    // for (size_t i = 0; i < f.size(); ++i) {
    //     var2i[f[i].getVar()] = i;
    // }
    // for (size_t j = 0; j < g.size(); ++j) {
    //     var2j[g[j].getVar()] = j;
    // }

    vector<Var> mappingVar;
    int index_f, index_g;
    bool isNagative_f, isNagative_g;
    Var v;
    for (size_t i = 0; i < group_g.size(); ++i) {
        index_f = i < group_f.size() ? id2i[group_f[i].first->getId()] : id2i[group_f.back().first->getId()];
        index_g = id2j[group_g[i].first->getId()];
        isNagative_f = i < group_f.size() ? group_f[i].second : group_f.back().second;
        isNagative_g = group_g[i].second;
        v = isNagative_f == isNagative_g ? c[index_g][index_f].matrixVar : d[index_g][index_f].matrixVar;
        mappingVar.push_back(v);
    }
    // ----------
    // A B C
    // D E F G
    // if A=D (c_AD -> c BE , c_AD->c_CF, c_AD->c_CG)
    // =(~c_AD + c_BE)(~c_AD+c_CF)
    for (size_t i = 0; i < mappingVar.size(); ++i) {
        for (size_t j = 0; j < mappingVar.size(); ++j) {
            if (j == i) continue;
            vector<Lit> lits;
            lits.push_back(~Lit(mappingVar[i]));
            lits.push_back(Lit(mappingVar[j]));
            matrixSolver.addCNF(lits);
            lits.clear();
        }
    }
    return;

    // int matchIdx_f = 0, matchIdx_g = 0;
    // int fEnd = group_f.size();
    // int gEnd = group_g.size();
    // As many as possible to mapping
    // g_q = g_j , f_p = f_i
    // int i, j, p, q;
    // f_p = f_i -> false , f_p = ~f_i ->true
    // bool phase_f, phase_g;

    // while (!(matchIdx_g == (gEnd - 1))) {
    //     // choose two in group f
    //     if (matchIdx_f < (fEnd - 1)) {
    //         cout << "f: mapping " << matchIdx_f << " & " << matchIdx_f + 1 << endl;
    //         // i = var2i[AAG2Var(group_f[matchIdx_f].first->getId(), true)];
    //         // p = var2i[AAG2Var(group_f[matchIdx_f + 1].first->getId(), true)];
    //         i = id2i[group_f[matchIdx_f].first->getId()];
    //         p = id2i[group_f[matchIdx_f + 1].first->getId()];
    //         phase_f = group_f[matchIdx_f].second ^ group_f[matchIdx_f + 1].second;
    //     } else {
    //         cout << "f: mapping " << matchIdx_f << endl;
    //         // i = var2i[AAG2Var(group_f[matchIdx_f].first->getId(), true)];
    //         // p = var2i[AAG2Var(group_f[matchIdx_f].first->getId(), true)];
    //         i = id2i[group_f[matchIdx_f].first->getId()];
    //         p = id2i[group_f[matchIdx_f].first->getId()];

    //         phase_f = false;
    //     }
    //     cout << "    (i,p): " << i << " , " << p << endl;
    //     // choose two in group g
    //     cout << "g: mapping " << matchIdx_g << " & " << matchIdx_g + 1 << endl;
    //     // j = var2j[AAG2Var(group_g[matchIdx_g].first->getId(), false)];
    //     // q = var2j[AAG2Var(group_g[matchIdx_g + 1].first->getId(), false)];
    //     j = id2j[group_g[matchIdx_g].first->getId()];
    //     q = id2j[group_g[matchIdx_g + 1].first->getId()];

    //     phase_g = group_g[matchIdx_g].second ^ group_g[matchIdx_g + 1].second;
    //     cout << "    (j,q): " << j << " , " << q << endl;

    //     // Var invCqp = matrixSolver.newVar();
    //     // Var invDji = matrixSolver.newVar();
    //     // matrixSolver.addInvCNF(invDji, d[j][i]);
    //     // matrixSolver.addInvCNF(invCqp, c[q][p]);

    //     // f, g have different phases (01 10)
    //     if (phase_f ^ phase_g) {
    //         matrixSolver.addInvCNF(c[j][i].matrixVar, c[q][p].matrixVar);
    //         matrixSolver.addInvCNF(d[j][i].matrixVar, d[q][p].matrixVar);
    //     }

    //     // the same phases (11 00)
    //     // {(-c_j,i V c_q,p) &  (c_j,i V -c_q,p)} &  {(-d_j,i V d_q,p) &  (d_j,i V -d_q,p)}
    //     else {
    //         Var invCji = matrixSolver.newVar();
    //         Var invDqp = matrixSolver.newVar();
    //         matrixSolver.addInvCNF(invCji, c[j][i].matrixVar);
    //         matrixSolver.addInvCNF(invDqp, d[q][p].matrixVar);
    //         matrixSolver.addInvCNF(invCji, c[q][p].matrixVar);
    //         matrixSolver.addInvCNF(d[j][i].matrixVar, invDqp);
    //     }

    //     if (matchIdx_f != fEnd - 1) ++matchIdx_f;
    //     ++matchIdx_g;
    // }

    // return;
}

void addEqualConstraint(ifstream& in1, ifstream& in2) {
    CirMgr* c1 = new CirMgr;
    CirMgr* c2 = new CirMgr;
    if (!in1) {
        cout << "can not open file 1" << endl;
        return;
    }
    if (!in2) {
        cout << "can not open file 2" << endl;
        return;
    }

    c1->readCircuit(in1);
    c2->readCircuit(in2);
    c1->randomSim();
    c2->randomSim();
    c1->printSummary();
    c2->printSummary();
    vector<vector<pair<CirGate*, bool>>> equalGroup_1, equalGroup_2;
    equalGroup_1 = c1->fraigForGroup();
    equalGroup_2 = c2->fraigForGroup();

    for (int i = 0; i < c1->POs.size(); ++i) {
        id2i[c1->POs[i]->getId()] = i;
    }
    for (int j = 0; j < c2->POs.size(); ++j) {
        id2j[c2->POs[j]->getId()] = j;
    }

    // TODO: modify fraig th return group
    for (size_t index_1 = 0; index_1 < equalGroup_1.size(); ++index_1) {
        for (size_t index_2 = index_1 + 1; index_2 < equalGroup_2.size(); ++index_2) {
            // valid mapping relation should #n of f <= #n of g
            if (equalGroup_1[index_1].size() <= equalGroup_2[index_2].size()) {
                // cout << "start to map group...index: (f,g): " << index_1 << " , " << index_2 << endl;
                // cout << "size of f: " << equalGroup_1[index_1].size() << " size of g: " << equalGroup_2[index_2].size() << endl;
                createEqualRelationByGroup(equalGroup_1[index_1],
                                           equalGroup_2[index_2]);
            }
        }
    }
    delete c1, c2;
    // TODO: lonely output: g's more output to 's 1 output (should transfer aag to var)
}

// void equalRelationHelper()