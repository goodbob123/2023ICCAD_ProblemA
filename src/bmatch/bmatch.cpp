/****************************************************************************
  FileName     [ bmatch.cpp ]
  PackageName  [ bmatch ]
  Synopsis     [ Define sat prove package interface ]
  Author       [ ]
  Copyright    [ Copyleft(c) 2010 LaDs(III), GIEE, NTU, Taiwan ]
 ****************************************************************************/

#include "gvMsg.h"
#include "gvSatMgr.h"
#include "reader.h"
#include <cassert>
#include <iostream>
#include <queue>
#include <vector>

using namespace std;

// #define isGVNetInverted(netId) (netId.cp)

void
SATMgr::booleanMatching() {
    cout << "enter booleanMatching!" << endl;
    SatProofRes  pRes;
    GVSatSolver* gvSatSolver = new GVSatSolver(gvNtkMgr);
    pRes.setSatSolver(gvSatSolver);

    // assume input number= nPI1, nPI2
    // assume onput number= nPO1, nPO2
    int nPI1 = 2;
    int nPI2 = 2;
    int nPO1 = 2;
    int nPO2 = 2;

    // bulid matrix
    // build each output Data
    cout << "init current clause: " << gvSatSolver->getNumClauses() << endl;
    // for (int i = 0; i < gvNtkMgr->getOutputSize(); ++i) {
    //     gvSatSolver->addBoundedVerifyData(gvNtkMgr->getOutput(i), 0);
    // }
    cout << "builded circut relation, current clause: "
         << gvSatSolver->getNumClauses() << endl;

    // (1) input permutation matirx
    vector<vector<Var>> inputMatrix(nPI1 * 2 + 2,vector<Var>(nPI2));    // have little change
    for (int col = 0; col < nPI2; ++col) {
        for (int row = 0; row < nPI1 * 2 + 2; ++row) {
            Var newVar            = gvSatSolver->newVar();
            inputMatrix[row][col] = newVar;
        }
    }
    // add input constraint
    vector<bool> inputCol_b(2 * nPI2, false);
    vector<Var> inputCol_v(2 * nPI2);
    for (unsigned v = 0; v < nPI1; ++v) { //notice 0, 1 row not >= 1
        for (unsigned col = 0; col < nPI2; ++col) {
            inputCol_v[2 * col] = inputMatrix[2 * v][col];
            inputCol_v[2 * col + 1] = inputMatrix[2 * v + 1][col];
        }
        gvSatSolver->addCNF(inputCol_v, inputCol_b);
    }

    vector<Var> inputRow1_v(nPI1 * 2 + 2);
    vector<bool> inputRow1_b(nPI1 * 2 + 2, false);
    for (unsigned col = 0; col < nPI2; ++col) {
        for (unsigned row = 0; row < nPI1 * 2 + 2; ++row) {
            inputRow1_v[row] = inputMatrix[row][col];
        }
        gvSatSolver->addCNF(inputRow1_v, inputRow1_b);
    }

    for (unsigned col = 0; col < nPI2; ++col) {
        for (unsigned row1 = 0; row1 < nPI1 * 2 + 2; ++row1) {
            for (unsigned row2 = row1 + 1; row2 < nPI1 * 2 + 2; ++row2) {
                gvSatSolver->addCNF(inputMatrix[row1][col], true, inputMatrix[row2][col], true);
            }
        }
    }
    // (2) output permutation matirx
    vector<vector<Var>> outputMatrix(nPO1 * 2,vector<Var>(nPO2));
    for (int col = 0; col < nPO2; ++col) {
        for (int row = 0; row < nPO1 * 2; ++row) {
            Var newVar            = gvSatSolver->newVar();
            outputMatrix[row][col] = newVar;
        }
    }
    // add output constraint
    for (unsigned col = 0; col < nPO2; ++col) {
        for (unsigned row1 = 0; row1 < nPO1 * 2; ++row1) {
            for (unsigned row2 = row1 + 1; row2 < nPO1 * 2; ++row2) {
                gvSatSolver->addCNF(outputMatrix[row1][col], true, outputMatrix[row2][col], true);
            }
        }
    }

    cout << "builded matrix, current clause: " << gvSatSolver->getNumClauses()
         << endl;
    if (gvSatSolver->assump_solve()) {
        cout << "input" << endl;
        for (auto invec: inputMatrix) {
            for (auto invar: invec) {
                cout << gvSatSolver->getVarValue(invar) << " ";
            }
            cout << endl;
        }
        cout << "output" << endl;
        for (auto outvec: outputMatrix) {
            for (auto outvar: outvec) {
                cout << gvSatSolver->getVarValue(outvar) << " ";
            }
            cout << endl;
        }
    }
    unsigned mustOut = 0;
    while (1) {
        #ifdef DEBUG
            ++mustOut;
            if (mustOut > 1000) break;
        #endif
    // solve mapping matrix
    // if UNSAT -> return no match
    // if SAT -> keep going

    // (matching SAT)
    // build miter (建亨)
        break;
    // (miter UNSAT)
    // record score & exclude current matching (wish)

    }
}
