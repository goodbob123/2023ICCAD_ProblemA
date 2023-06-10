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

// calculate score based on the mapping results
static int getScore(GVSatSolver* matrixSolver, const vector<vector<Var>>& outputMatrix) {
    // TODO: How about undefined output ?? Is it possible that there is undefined variable in the output matrix ?
    int score = 0;
    for (int row = 0; row < outputMatrix.size() / 2; ++row) {
        bool foundOne = false;
        for (int col = 0; col < outputMatrix[row].size(); ++col) {
            if (matrixSolver->getVarValue(outputMatrix[2 * row][col]) == 1) {
                score ++;
                foundOne = true;
            }
            if (matrixSolver->getVarValue(outputMatrix[2 * row + 1][col]) == 1) {
                score ++;
                foundOne = true;
            }
        }
        if (foundOne) score += 1;
    }
    return score;
}

void
SATMgr::booleanMatching() {
    cout << "enter booleanMatching!" << endl;
    SatProofRes  pRes;
    GVSatSolver* matrixSolver = new GVSatSolver(gvNtkMgr);
    GVSatSolver* miterSolver = new GVSatSolver(gvNtkMgr);
    pRes.setSatSolver(matrixSolver);

    // assume input number= nPI1, nPI2
    // assume onput number= nPO1, nPO2
    int nPI1 = 2;
    int nPI2 = 2;
    int nPO1 = 2;
    int nPO2 = 2;

    // bulid matrix
    // build each output Data
    cout << "init current clause: " << matrixSolver->getNumClauses() << endl;
    // (1) input permutation matirx
    vector<vector<Var>> inputMatrix(nPI1 * 2 + 2,vector<Var>(nPI2));    // have little change
    for (int col = 0; col < nPI2; ++col) {
        for (int row = 0; row < nPI1 * 2 + 2; ++row) {
            Var newVar            = matrixSolver->newVar();
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
        matrixSolver->addCNF(inputCol_v, inputCol_b);
    }

    vector<Var> inputRow1_v(nPI1 * 2 + 2);
    vector<bool> inputRow1_b(nPI1 * 2 + 2, false);
    for (unsigned col = 0; col < nPI2; ++col) {
        for (unsigned row = 0; row < nPI1 * 2 + 2; ++row) {
            inputRow1_v[row] = inputMatrix[row][col];
        }
        matrixSolver->addCNF(inputRow1_v, inputRow1_b);
    }

    for (unsigned col = 0; col < nPI2; ++col) {
        for (unsigned row1 = 0; row1 < nPI1 * 2 + 2; ++row1) {
            for (unsigned row2 = row1 + 1; row2 < nPI1 * 2 + 2; ++row2) {
                matrixSolver->addCNF(inputMatrix[row1][col], true, inputMatrix[row2][col], true);
            }
        }
    }
    // (2) output permutation matirx
    vector<vector<Var>> outputMatrix(nPO1 * 2,vector<Var>(nPO2));
    for (int col = 0; col < nPO2; ++col) {
        for (int row = 0; row < nPO1 * 2; ++row) {
            Var newVar            = matrixSolver->newVar();
            outputMatrix[row][col] = newVar;
        }
    }
    // add output constraint
    for (unsigned col = 0; col < nPO2; ++col) {
        for (unsigned row1 = 0; row1 < nPO1 * 2; ++row1) {
            for (unsigned row2 = row1 + 1; row2 < nPO1 * 2; ++row2) {
                matrixSolver->addCNF(outputMatrix[row1][col], true, outputMatrix[row2][col], true);
            }
        }
    }

    cout << "builded matrix, current clause: " << matrixSolver->getNumClauses()
         << endl;
    // build miter
    cout << "init current clause: " << miterSolver->getNumClauses() << endl;
    for (int i = 0; i < gvNtkMgr->getOutputSize(); ++i) {
        miterSolver->addBoundedVerifyData(gvNtkMgr->getOutput(i), 0);
    }
    unsigned num_ntk = gvNtkMgr->getNetSize();
    cout << "init ntk num: " << num_ntk << endl;
    cout << "builded ckt, current clause: " << miterSolver->getNumClauses()
         << endl;

    vector<vector<GVNetId>> i_Matching(nPI1 * 2,vector<GVNetId>(nPI2));
    // input should be same
    for (int v2 = 0; v2 < nPI2; ++v2) {
        for (int v1 = 0; v1 < nPI1; ++v1) {
            i_Matching[v1 * 2][v2] = miterSolver->add_XNOR_gate(gvNtkMgr->getInput(v1), gvNtkMgr->getInput(nPI1 + v2));
            i_Matching[v1 * 2 + 1][v2] = miterSolver->add_XNOR_gate(~gvNtkMgr->getInput(v1), gvNtkMgr->getInput(nPI1 + v2));
        }
    }
    vector<vector<GVNetId>> o_Matching(nPO1 * 2,vector<GVNetId>(nPO2));
    // output should not be different(because !P, so use XOR)
    for (int v2 = 0; v2 < nPO2; ++v2) {
        for (int v1 = 0; v1 < nPO1; ++v1) {
            o_Matching[v1 * 2][v2] = miterSolver->add_XOR_gate(gvNtkMgr->getOutput(v1), gvNtkMgr->getOutput(nPO1 + v2));
            o_Matching[v1 * 2 + 1][v2] = miterSolver->add_XOR_gate(~gvNtkMgr->getOutput(v1), gvNtkMgr->getOutput(nPO1 + v2));
        }
    }
    cout << "now ntk num: " << gvNtkMgr->getNetSize() << endl;
    cout << "builded mitter, current clause: " << miterSolver->getNumClauses()
         << endl;
    // unsigned mustOut = 0;
    vector<vector<bool>> inputAns(nPI1 * 2 + 2,vector<bool>(nPI2));
    vector<vector<bool>> outputAns(nPO1 * 2,vector<bool>(nPO2));
    int score = -1;
    bool foundOneAns = false; // must find at least one solution
    while (1) {
        // #ifdef DEBUG
        // ++mustOut;
        // if (mustOut > 1000) break;
        // #endif
    // solve mapping matrix
    // if UNSAT -> return no match
    // if SAT -> keep going
        // if (matrixSolver->assump_solve()) {
        if (matrixSolver->solve()) {
            // cout << "matrixSolver SAT" << endl;
            // cout << "input" << endl;
            // for (int col = 0; col < nPI2; ++col) {
            //     for (int row = 0; row < nPI1 * 2 + 2; ++row) {
            //         cout << matrixSolver->getVarValue(inputMatrix[row][col]) << " ";
            //     }
            //     cout << endl;
            // }
            // cout << "output" << endl;
            // for (int col = 0; col < nPO2; ++col) {
            //     for (int row = 0; row < nPO1 * 2; ++row) {
            //         cout << matrixSolver->getVarValue(outputMatrix[row][col]) << " ";
            //     }
            //     cout << endl;
            // }
            
            miterSolver->assumeRelease();
            // input should be same
            for (int v2 = 0; v2 < nPI2; ++v2) {
                for (int v1 = 0; v1 < 2 * nPI1; ++v1) {
                    if (matrixSolver->getVarValue(inputMatrix[v1][v2]) == 1)
                        miterSolver->assumeProperty(i_Matching[v1][v2], false, 0);
                }
                if (matrixSolver->getVarValue(inputMatrix[nPI1 * 2][v2]) == 1)
                    miterSolver->assumeProperty(gvNtkMgr->getInput(v2), false, 0);
                if (matrixSolver->getVarValue(inputMatrix[nPI1 * 2 + 1][v2]) == 1)
                    miterSolver->assumeProperty(~gvNtkMgr->getInput(v2), false, 0);
            }
            // output should not be different
            GVNetId S;
            bool is_S = false;
            for (int v2 = 0; v2 < nPO2; ++v2) {
                for (int v1 = 0; v1 < nPO1 * 2; ++v1) {
                    if (matrixSolver->getVarValue(outputMatrix[v1][v2]) == 1) {
                        // cout << "output "<< v1 << " " << v2 << " should always same" << endl;
                        if (!is_S) {S = o_Matching[v1][v2]; is_S = true;}
                        else S = miterSolver->add_OR_gate(o_Matching[v1][v2], S);
                    }
                }
            }
            if (is_S) miterSolver->assertProperty(S, false, 0);
        } else {
            // matrixSlover UNSAT -> no remaining matching
            cout << "No remaining matching" << endl;
            break;
        }

        if (miterSolver->assump_solve()) { 
            // miterSolver SAT -> exclude this wrong mapping from mappingSolver
            cout << "miterSlover SAT" << endl;
            
        } 
        else {
            // miterSolver UNSAT -> find a matching mapping
            cout << "miterSlover UNSAT -> find a matching mapping" << endl;
            foundOneAns = true;
            int newScore = getScore(matrixSolver, outputMatrix);
            if (newScore > score) {
                cout << "Update mapping with score: " << newScore << ", mapping as follows:" << endl;
                cout << "input" << endl;
                for (int col = 0; col < nPI2; ++col) {
                    for (int row = 0; row < nPI1 * 2 + 2; ++row) {
                        inputAns[row][col] = matrixSolver->getVarValue(inputMatrix[row][col]);
                        cout << inputAns[row][col] << " ";
                    }
                    cout << endl;
                }
                cout << "output" << endl;
                for (int col = 0; col < nPO2; ++col) {
                    for (int row = 0; row < nPO1 * 2; ++row) {
                        outputAns[row][col] = matrixSolver->getVarValue(outputMatrix[row][col]);
                        cout << outputAns[row][col] << " ";
                    }
                    cout << endl;
                }
                score = newScore; //modify
            }
            // block the found mapping
            // modify : take out the loop
        }
        int nofMatrixVar = nPI2 * (nPI1 * 2 + 2) + nPO2 * (nPO1 * 2);
        vector<Var> vs(nofMatrixVar);
        vector<bool> bs(nofMatrixVar); // bs[index] is true -> ~vs[index] in clause
        int index = 0;
        for (int col = 0; col < nPI2; ++col) {
            for (int row = 0; row < nPI1 * 2 + 2; ++row) {
                vs[index] = inputMatrix[row][col];
                bs[index] = (matrixSolver->getVarValue(inputMatrix[row][col]) == 1);
                index ++;
            }
        }
        for (int col = 0; col < nPO2; ++col) {
            for (int row = 0; row < nPO1 * 2; ++row) {
                vs[index] = outputMatrix[row][col];
                bs[index] = (matrixSolver->getVarValue(outputMatrix[row][col]) == 1);
                index ++;
            }
        }
        matrixSolver->addCNF(vs, bs);
    }
    assert(foundOneAns);
    // output optimal solution
    cout << "Optimal score: " << score << ", mapping as follows:" << endl;
    cout << "input" << endl;
    for (int col = 0; col < nPI2; ++col) {
        for (int row = 0; row < nPI1 * 2 + 2; ++row) {
            inputAns[row][col] = matrixSolver->getVarValue(inputMatrix[row][col]);
            cout << inputAns[row][col] << " ";
        }
        cout << endl;
    }
    cout << "output" << endl;
    for (int col = 0; col < nPO2; ++col) {
        for (int row = 0; row < nPO1 * 2; ++row) {
            outputAns[row][col] = matrixSolver->getVarValue(outputMatrix[row][col]);
            cout << outputAns[row][col] << " ";
        }
        cout << endl;
    }
}
