#include "bmatchSolver.h"

#include <iomanip>
#include <map>
#include <set>
#include <string>
#include <unordered_map>

size_t Order::en_count= 0;

void BMatchSolver::init(ifstream& portMapping, ifstream& aag1, ifstream& aag2, char* match) {
    std::ios::sync_with_stdio(false);
    std::cin.tie(0);

    outputSolver.initialize();
    matrixSolver.initialize();
    miterSolver.initialize();

    genCircuitModel(portMapping, aag1, aag2);
    initCircuit(aag1, aag2);
    buildMatrix();
    genMiterConstraint();
    file_match = match;
    bestScore = 0;
}



void BMatchSolver::genFuncSupport(ifstream& in) {
    /*
    cout << "--------------- Circuit 1 -----------------" << endl;
    cout << "Input:" << endl;
    for (int j = 0; j < x.size(); ++j) {
        cout << x[j].getName() << " ";
    }
    cout << endl;
    cout << "Output:" << endl;
    for (int j = 0; j < f.size(); ++j) {
        cout << f[j].getName() << " ";
    }
    cout << endl;

    cout << "--------------- Circuit 2 -----------------" << endl;
    cout << "Input:" << endl;
    for (int i = 0; i < y.size(); ++i) {
        cout << y[i].getName() << " ";
    }
    cout << endl;
    cout << "Output:" << endl;
    for (int i = 0; i < g.size(); ++i) {
        cout << g[i].getName() << " ";
    }
    cout << endl;
    cout << endl;
    */

    for (int j = 0; j < f.size(); ++j) {
        set<Var> supports;
        string funcSuppVec;

        in >> funcSuppVec;
        assert(funcSuppVec.size() == x.size());
        for (int k = 0; k < x.size(); ++k) {
            if (funcSuppVec[k] == '1') {
                supports.insert(k);
                x[k].addSupport(j);
                f[j].addSupport(k);
            }
        }
        // fSupport.push_back(supports);
    }
    for (int i = 0; i < g.size(); ++i) {
        set<Var> supports;
        string funcSuppVec;

        in >> funcSuppVec;
        assert(funcSuppVec.size() == y.size());
        for (int k = 0; k < y.size(); ++k) {
            if (funcSuppVec[k] == '1') {
                supports.insert(k);
                y[k].addSupport(i);
                g[i].addSupport(k);
            }
        }
        // gSupport.push_back(supports);
    }
    return;
}

class Hash {
   public:
    size_t operator()(const pair<int, int>& p) const {
        return p.first ^ p.second;
    }
};

void BMatchSolver::inputPreprocess() {
    cerr << "inputPreprocess start..." << endl;

    // for (int j = 0; j < x.size(); ++j) {
    //     for (int i = 0; i < y.size(); ++i) {
    //         if (x[j].nofSupport() != y[i].nofSupport()) {
    //             matrixSolver.assertProperty(a[i][j].matrixVar, false);
    //             matrixSolver.assertProperty(b[i][j].matrixVar, false);
    //         }
    //     }
    // }
    cerr << "------------ INPUT SUPPORT CHECK ------------" << endl;
    map<int, set<int>> xSupp;
    map<int, set<int>> ySupp;
    for (int j = 0; j < x.size(); ++j)
        xSupp[x[j].nofSupport()].insert(j);
    for (int i = 0; i < y.size(); ++i)
        ySupp[y[i].nofSupport()].insert(i);
    map<int, set<int>>::iterator itx;
    map<int, set<int>>::iterator ity;
    itx = xSupp.begin();
    ity = ySupp.begin();
    while (ity != ySupp.end()) {
        if (itx->first != ity->first) {
            cerr << "WARNING    nof_support:" << setw(3) << ity->first << " , diff:" << setw(2) << ity->second.size() << endl;
            ity++;
            continue;
        }
        if (itx->second.size() != ity->second.size()) { // wierd: why x > y ????
            int diff = ity->second.size() - itx->second.size();
            cerr << "nof_support:" << setw(3) << ity->first << " , diff:" <<  diff << endl;
            // itx ++;
            // ity ++;
            // continue;
        }
        twoWaySupport(itx->second, ity->second);
        itx ++;
        ity ++;
    }
    cerr << "input diff: " << y.size() - x.size() << endl;
    cerr << "------------ END OF INPUT SUPPORT CHECK ------------" << endl;
    cerr << "inputPreprocess end." << endl;
}

static unordered_map<int, int> id2i;
static unordered_map<int, int> id2j;


void BMatchSolver::createEqualRelationByOneOutput(const int index_f,
                                              const vector<pair<CirGate*, bool>>& group_g) {

    // ----------
    // A  <=> D E ~F G  (pos)
    // ~A <=> D E ~F G  (neg)                                
    vector<Var> mappingVar_pos,mappingVar_neg;
    int  index_g;
    bool isNagative_g;
    Var pos,neg;

    for (size_t i = 0; i < group_g.size(); ++i) {
        index_g = id2j[group_g[i].first->getId()];
        isNagative_g = group_g[i].second;

        // if(isNagative_g)
        //     cout<<"mapping: !"<< index_f << "& "<< index_g<<endl;
        // else
        //     cout<<"mapping: " << index_f << "& "<< index_g <<endl;
        pos = isNagative_g ? d[index_g][index_f].matrixVar : c[index_g][index_f].matrixVar;
        neg = isNagative_g ? c[index_g][index_f].matrixVar : d[index_g][index_f].matrixVar;
        mappingVar_pos.push_back(pos);
        mappingVar_neg.push_back(neg);
    }

    // ----------
    // A 
    // D E ~F G
    // if A=D (c_AD -> c_AE, d_AF, c_AG)
    // =(~c_AD + c_AE)(~c_AD+d_AF)
    // if ~A=D (d_AD -> d_AE , d_AD->c_AF, d_AD->d_AG)
    for (size_t i = 0; i < mappingVar_pos.size(); ++i) {
        for (size_t j = 0; j < mappingVar_pos.size(); ++j) {
            if (j == i) continue;
            vector<Lit> lits;
            lits.push_back(~Lit(mappingVar_pos[i]));
            lits.push_back(Lit(mappingVar_pos[j]));
            matrixSolver.addCNF(lits);
            lits.clear();
            lits.push_back(~Lit(mappingVar_neg[i]));
            lits.push_back(Lit(mappingVar_neg[j]));
            matrixSolver.addCNF(lits);
            lits.clear();
        }
    }
    return;

}

void BMatchSolver::createEqualRelationByGroup(const vector<pair<CirGate*, bool>>& group_f,
                                              const vector<pair<CirGate*, bool>>& group_g) {
    vector<Var> mappingVar_pos,mappingVar_neg;
    int index_f, index_g;
    bool isNagative_f, isNagative_g;
    Var pos,neg;
    // ----------
    // A ~B  
    // D E ~F G
    // if A=D (c_AD -> d_BE, c_BF, d_BG)
    // if A=~D (d_AD -> c_BE, d_BF, c_BG)
    for (size_t i = 0; i < group_g.size(); ++i) {
        index_f = i < group_f.size() ? id2i[group_f[i].first->getId()] : id2i[group_f.back().first->getId()];
        index_g = id2j[group_g[i].first->getId()];
        isNagative_f = i < group_f.size() ? group_f[i].second : group_f.back().second;
        isNagative_g = group_g[i].second;
        // if(isNagative_f)
        //     cout<<"mapping: !"<< index_f <<" & "<< index_g<<endl;
        // else if (isNagative_g)
        //     cout<<"mapping: "<< index_f <<" & !"<< index_g<<endl;
        // else
        //     cout<<"mapping: " << index_f << " & "<< index_g <<endl;
        pos = isNagative_f == isNagative_g ? c[index_g][index_f].matrixVar : d[index_g][index_f].matrixVar;
        neg = isNagative_f != isNagative_g ? c[index_g][index_f].matrixVar : d[index_g][index_f].matrixVar;
        mappingVar_pos.push_back(pos);
        mappingVar_neg.push_back(neg);
    }

    // ----------
    // A B C
    // D E F G
    // if A=D (c_AD -> c BE , c_AD->c_CF, c_AD->c_CG)
    // =(~c_AD + c_BE)(~c_AD+c_CF)
    for (size_t i = 0; i < mappingVar_pos.size(); ++i) {
        for (size_t j = 0; j < mappingVar_pos.size(); ++j) {
            if (j == i) continue;
            vector<Lit> lits;
            lits.push_back(~Lit(mappingVar_pos[i]));
            lits.push_back(Lit(mappingVar_pos[j]));
            matrixSolver.addCNF(lits);
            lits.clear();
            lits.push_back(~Lit(mappingVar_neg[i]));
            lits.push_back(Lit(mappingVar_neg[j]));
            matrixSolver.addCNF(lits);
            lits.clear();
        }
    }
    return;
}

void BMatchSolver::initCircuit(ifstream& in1, ifstream& in2) {
    if (!in1) {
        cout << "can not open file 1" << endl;
        return;
    }
    if (!in2) {
        cout << "can not open file 2" << endl;
        return;
    }
    in1.seekg(0, ios_base::beg);
    in2.seekg(0, ios_base::beg);
    c1 = new CirMgr;
    c2 = new CirMgr;
    c1->readCircuit(in1);
    c2->readCircuit(in2);

    cout << "c1:   #PI, #PO= (" << c1->PIs.size() << ", " << c1->POs.size() << ")" << endl;
    vector<int> f_coverage, g_coverage;
    vector<vector<int>> f_support, g_support;
    c1->getSupportCoverageInfo(f_coverage, f_support);
    c1->showInfo();
    cout << "c2:   #PI, #PO= (" << c2->PIs.size() << ", " << c2->POs.size() << ")" << endl;
    c2->getSupportCoverageInfo(g_coverage, g_support);
    c2->showInfo();

    // coverage init
    for (size_t i = 0; i < f.size(); ++i) {
        f[i].coverage = f_coverage[i];
    }
    for (size_t i = 0; i < g.size(); ++i) {
        g[i].coverage = g_coverage[i];
    }
    vector<vector<pair<int, bool>>> group_f, group_g;
    getEqualGroup(group_f, group_g);
}

// int: f[0],f[1]... , bool: the phase to equal
void BMatchSolver::getEqualGroup(vector<vector<pair<int, bool>>>& group_f, vector<vector<pair<int, bool>>>& group_g) {
    // find equal group
    if (!c1 || !c2) {
        cout << "please init circuit first" << endl;
        return;
    }
    c1->randomSim();
    c2->randomSim();
    vector<vector<pair<CirGate*, bool>>> equalGroup_1, equalGroup_2;
    equalGroup_1 = c1->fraigForGroup();
    equalGroup_2 = c2->fraigForGroup();

    if (equalGroup_1.empty() || equalGroup_2.empty()) return;

    for (int i = 0; i < c1->POs.size(); ++i) {
        id2i[c1->POs[i]->getId()] = i;
    }
    for (int j = 0; j < c2->POs.size(); ++j) {
        id2j[c2->POs[j]->getId()] = j;
    }

    vector<vector<pair<int, bool>>> equalGroup_1_n, equalGroup_2_n;

    // translate from aig id to index (f[0],f[1]...)
    vector<pair<int, bool>> temp;
    for (size_t i = 0; i < equalGroup_1.size(); ++i) {
        for (size_t j = 0; j < equalGroup_1[i].size(); ++j) {
            temp.push_back(make_pair(id2i[equalGroup_1[i][j].first->getId()], equalGroup_1[i][j].second));
        }
        equalGroup_1_n.push_back(temp);
        temp.clear();
    }
    for (size_t i = 0; i < equalGroup_2.size(); ++i) {
        for (size_t j = 0; j < equalGroup_2[i].size(); ++j) {
            temp.push_back(make_pair(id2j[equalGroup_2[i][j].first->getId()], equalGroup_2[i][j].second));
        }
        equalGroup_2_n.push_back(temp);
        temp.clear();
    }
    group_f = equalGroup_1_n;
    group_g = equalGroup_2_n;

    cout << " ------------  Circuit 1 Equal Group Size: " << equalGroup_1.size() << " ------------" << endl;
    for (size_t index_1 = 0; index_1 < equalGroup_1.size(); ++index_1) {
        cout << setw(3) << equalGroup_1[index_1].size() << " ";
    }
    cout << endl;
    cout << " ------------  Circuit 2 Equal Group Size: " << equalGroup_2.size() << " ------------" << endl;
    for (size_t index_2 = 0; index_2 < equalGroup_2.size(); ++index_2) {
        cout << setw(3) << equalGroup_2[index_2].size() << " ";
    }
    cout << endl;
}

// do not use the method
void BMatchSolver::addEqualConstraint() {
    cout << "start to add equal constraint ..." << endl;
    c1->randomSim();
    c2->randomSim();
    vector<vector<pair<CirGate*, bool>>> equalGroup_1, equalGroup_2;
    equalGroup_1 = c1->fraigForGroup();
    equalGroup_2 = c2->fraigForGroup();

    for (int i = 0; i < c1->POs.size(); ++i) {
        id2i[c1->POs[i]->getId()] = i;
    }
    for (int j = 0; j < c2->POs.size(); ++j) {
        id2j[c2->POs[j]->getId()] = j;
    }

    // create output's Equal group mapping
    for (size_t index_1 = 0; index_1 < equalGroup_1.size(); ++index_1) {
        for (size_t index_2 = index_1; index_2 < equalGroup_2.size(); ++index_2) {
            // valid mapping relation should #n of f <= #n of g
            if (equalGroup_1[index_1].size() <= equalGroup_2[index_2].size()) {
                // cout << "start to map group...index: (f,g): " << index_1 << " , " << index_2 << endl;
                // cout << "size of f: " << equalGroup_1[index_1].size() << " size of g: " << equalGroup_2[index_2].size() << endl;
                createEqualRelationByGroup(equalGroup_1[index_1],
                                           equalGroup_2[index_2]);
            }
        }
    }

    // create lonely output mapping: g's more output to f's 1 output 
    cout<<"The index of f in equal group : "<<endl;
    for(int i=0;i<equalGroup_1.size(); ++i){
        for(int j=0;j<equalGroup_1[i].size(); ++j){
            if(id2i[equalGroup_1[i][j].first->getId()]!=-1)
                cout <<id2i[equalGroup_1[i][j].first->getId()] <<" ";
            id2i[equalGroup_1[i][j].first->getId()] = -1;
        }   
    }
    cout<<endl;
    // store the f output's index which is not equal to other
    cout<<"The index of f not in equal group : "<<endl;
    vector<int> lonely_f;
    for(auto element :id2i){
        if(element.second!=-1){
            cout<< element.second <<" ";
            lonely_f.push_back(element.second);
        }
    }
    cout<<endl;

    // lonely_f
    for (size_t index_1 = 0; index_1 < lonely_f.size(); ++index_1) {
        for (size_t index_2 = index_1; index_2 < equalGroup_2.size(); ++index_2) {
            createEqualRelationByOneOutput(lonely_f[index_1],
                                           equalGroup_2[index_2]);
        }
    }

    cout<< "end to add equal constraint ..."<<endl;
}

void BMatchSolver::outputPreprocess() {
    cerr << "outputPreprocess start..." << endl;
    for (int j = 0; j < f.size(); ++j) {
        for (int i = 0; i < g.size(); ++i) {
            if (f[j].nofSupport() > g[i].nofSupport()) {
            // if (f[j].nofSupport() != g[i].nofSupport()) {
                // outputSolver.assertProperty(outputC[i][j], false);
                // outputSolver.assertProperty(outputD[i][j], false);
                outputSolver.assertProperty(outputVarMatrix[i][j], false);
                matrixSolver.assertProperty(c[i][j].matrixVar, false); // maybe redundant
                matrixSolver.assertProperty(d[i][j].matrixVar, false); // maybe redundant
                possibleMo[i][j] = false;
            }
        }
    }
    return;
    // map<int, vector<int>> fSupps;
    // map<int, vector<int>> gSupps;
    // for (int j = 0; j < f.size(); ++j)
    //     fSupps[f[j].nofSupport()].push_back(j);
    // for (int i = 0; i < g.size(); ++i)
    //     gSupps[g[i].nofSupport()].push_back(i);

    // map<int, vector<int>>::iterator itf = fSupps.begin();
    // map<int, vector<int>>::iterator itg = gSupps.begin();
    // set<int> coveredX;
    // int nof_fSupp = 0;

    // // Wish TODO
    // for (; itf != fSupps.end(); ++itf) {
    //     nof_fSupp = itf->first;
    //     while (itg != gSupps.end() && itg->first < nof_fSupp) {
    //         for (int j = 0; j < x.size(); ++j) {
    //             if (coveredX.find(j) != coveredX.end())
    //                 continue;
    //             const vector<int>& gIndice = itg->second;
    //             for (int i = 0; i < gIndice.size(); ++i) {
    //                 const set<int>& gSupp = g[gIndice[i]].supports;
    //                 for (set<int>::const_iterator it = gSupp.begin(); it != gSupp.end(); ++it) {
    //                     // matrixSolver.assertProperty(a[*it][j].matrixVar, false);
    //                     // matrixSolver.assertProperty(b[*it][j].matrixVar, false);
    //                     possibleMi[*it][j] = false;
    //                 }   
    //             }
    //         }
    //         itg++;
    //     }

    //     const vector<int>& fIndice = itf->second;
    //     for (int j = 0; j < fIndice.size(); ++j) {
    //         const set<int>& fSupp = f[fIndice[j]].supports;
    //         for (set<int>::const_iterator it = fSupp.begin(); it != fSupp.end(); ++it) {
    //             coveredX.insert(*it);
    //         }
    //     }
    //     if (coveredX.size() == x.size())
    //         break;
    // }

    /*
        unordered_map<PortHashKey, vector<int>, PortHashFunc> portHash;
        int count = 0;
        for (int j = 0; j < f.size(); ++j) {
            portHash[PortHashKey(x, f[j])].push_back(j);
        }

        for (int i = 0; i < g.size(); ++i) {
            set<int> candidate(portHash[PortHashKey(y, g[i])].begin(), portHash[PortHashKey(y, g[i])].end());
            if (candidate.empty()) {
                cerr << "------------------- EMPTY! -------------------------" << endl;
                return;
            }
            for (int j = 0; j < g.size(); ++j) {
                if (candidate.find(j) == candidate.end()) {
                    outputSolver.assertProperty(outputC[i][j], false);
                    outputSolver.assertProperty(outputD[i][j], false);
                }
            }
        }
    //*/
    cerr << "outputPreprocess end" << endl;
}
void BMatchSolver::setOutMgr() {
    if (!outMgr.hadSet()) {
        outMgr.setPorts(f, g);
        outMgr.setBuses(fBus, gBus);
        vector<vector<pair<int, bool> > > eqgrp_f, eqgrp_g;
        cout << "set1" << endl;
        getEqualGroup(eqgrp_f, eqgrp_g);
        for (auto grp: eqgrp_g) {
            for (auto g: grp) cout << g.first << " ";
            cout << endl;
        }
        outMgr.setEqInfo(eqgrp_f, eqgrp_g);
        assert(y.size() >= x.size());
        cout << y.size() << " " << x.size() << endl;
        outMgr.setInputBias(y.size() - x.size());

        outMgr.setAssumption(true, true);
        outMgr.setAtriType(supportSpan::ordNearS, coneSpan::AbsC, remainCnt::addOne);
        outMgr.setStepWay(stepWay::normal);
    } else {
        outMgr.setAssumption(true, true);
        outMgr.setAtriType(supportSpan::ordNearS, coneSpan::AbsC, remainCnt::addOne);
        outMgr.setStepWay(stepWay::normal);
    }
    cout << "set2" << endl;
    if (!outMgr.init()) {
        cerr << "outMgr not correctly set" << endl;
        assert(0);
    }
}
void BMatchSolver::run() {
    bool considerAll = false;
    int prevTime = 0;
    int pre_eval_time = 0;
    cout << "generate output heuristic order" << endl;
    setOutMgr();
    cerr << "start run..." << endl;
    // for heuristic
    bool toStep = true;
    Order* cur = outMgr.getHead();

    outMgr.printBusInfo();
    outMgr.printAssign();
    for (auto assign : outMgr.getAllAssign()) {
        assign->printMapping();
    }
    cout << "__________" << endl;

    // cout << "c_matrix" << endl;
    // for (auto cv: c) {
    //     for (auto v: cv) cout << v.matrixVar << " ";
    //     cout << endl;
    // }
    // cout << "d_matrix" << endl;
    // for (auto cv: d) {
    //     for (auto v: cv) cout << v.matrixVar << " ";
    //     cout << endl;
    // }
    vector<vector<bool>> negation(1, vector<bool>());

    while (1) {
        int execTime = (clock() - START) / CLOCKS_PER_SEC;
        cout << execTime << " " << pre_eval_time << endl;
        if (execTime - prevTime >= 10) {
            if (execTime >= 3600) {
                cout << "time limit reach\n";
                cout << bestScore << endl;
                return;
            }
            cout << "time: " << execTime << " seconds" << endl;
            prevTime = execTime;
        }
        if ((execTime - pre_eval_time >= 100) && !toStep) {
            outMgr.record();
            setOutMgr();
            for (auto assign : outMgr.getAllAssign()) {
                assign->printMapping();
            }
            toStep = true;
            cur = outMgr.getHead();
            negation.clear();
            negation.push_back(vector<bool>());
        }
        pre_eval_time = execTime;
        if (bestScore == g.size() + f.size()) {
            cout << "This must be the OPT with (#output_port(Circuit I) + "
                    "#output_port(Circuit II)) = "
                 << bestScore << endl;
            // find other input match
            // findAllInputCandidate();
            break;
        }

        // origin, found by output SAT
        // vector<Var> outputPairs;
        // if (!outputSolve(outputPairs)) {
        //     cout << "No output pairs found!" << endl;
        //     break;
        // }
        // cout << "r0" << endl;
        vector<Order*> outputPairs;
        if (toStep) {
            cur = outMgr.step();
            if (cur!= 0 && outMgr.isBacktrack()) {
                cur = outMgr.step();
                negation.clear();
                negation.push_back(vector<bool>());
                assert(!outMgr.isBacktrack());
            }
        } 
        else {
            cur = outMgr.backTrack();
            negation.clear();
            negation.push_back(vector<bool>());
            if (cur != 0) {
                cur = outMgr.step();
                assert(!outMgr.isBacktrack());
            }
        }
        if (cur == 0) {
            cout << "No output pairs found!" << endl;
            break;
        }
        
        outputPairs = outMgr.getAllAssign();
        // cout << "assignment: " << endl;
        // outMgr.printAssign();
        // for (auto assign: outputPairs) {
        //     assign->printMapping();
        // }
        outputPairs.back()->printMapping();
        // outMgr.printBusConnection();
        // cout << "__________" << endl;
        // cout << "r1" << endl;
        assert(negation.size() > 0);

        size_t start;
        if (negation.size() == 1 && negation[0].empty()) start = 0;
        else start = outputPairs.size() - 1;
        for (size_t i = start; i < outputPairs.size(); ++i) {
            if (outputPairs[i]->isPos() && outputPairs[i]->isNeg()) {
                size_t num = negation.size();
                // negation.insert(negation.end(), negation.begin(), negation.end());
                for (size_t j = 0; j < num; ++j) negation.push_back(negation[j]);
                for (size_t j = 0; j < num; ++j) negation[j].push_back(false);
                for (size_t j = num; j < negation.size(); ++j) negation[j].push_back(true);
            } else if (outputPairs[i]->isPos())
                for (size_t j = 0; j < negation.size(); ++j) negation[j].push_back(false);
            else if (outputPairs[i]->isNeg())
                for (size_t j = 0; j < negation.size(); ++j) negation[j].push_back(true);
            else
                assert(0);
            if (negation.size() > 50) negation.resize(50);
        }

        size_t validSolNum = 0;
        for (size_t i = 0; i < negation.size(); ++i) {
            set<Var> currentResult;
            assert(outputPairs.size() == negation[i].size());
            for (size_t k = 0; k < outputPairs.size(); ++k) {
                size_t fid = outputPairs[k]->getFid();
                size_t gid = outputPairs[k]->getGid();
                // cout << fid << " " << gid << endl;
                if (negation[i][k] == 1)
                    currentResult.insert(d[gid][fid].matrixVar);
                else
                    currentResult.insert(c[gid][fid].matrixVar);
            }
            // cout << "start solving for: " << endl;
            // for (auto v: currentResult) cout << v << " ";
            // cout << endl;
            if (isValidMo(currentResult)) {
                // cout << "solved!" << endl;
                negation[validSolNum] = negation[i];
                ++validSolNum;
                if (!considerAll) break;
            }
            // cout << "not solve!" << endl;
        }
        // cout << "r3" << endl;
        if (!considerAll) assert(validSolNum < 2);
        negation.resize(validSolNum);
        bool canPos = false;
        bool canNeg = false;
        size_t end = outputPairs.size() - 1;
        for (size_t i = 0; i < negation.size(); ++i) {
            if (negation[i][end] == true) canNeg = true;
            if (negation[i][end] == false) canPos = true;
            if (canPos && canNeg) break;
        }
        assert(canPos || canNeg || negation.size() == 0);
        if (!canPos) outputPairs[end]->failPos();
        if (!canNeg) outputPairs[end]->failNeg();

        toStep = negation.size() != 0;
        
        size_t score;
        if (toStep)  {
            score = outputPairs.size();
        } else {
            score = 0;
        }
        for (size_t i = 0; i < outputPairs.size(); ++i) {
            outputPairs[i]->updateScore(score);
        }
        // cout << "r4" << endl;
    }
    // outMgr.record();
    // setOutMgr();
    // for (auto assign : outMgr.getAllAssign()) {
    //     assign->printMapping();
    // }
}

void BMatchSolver::outputAns() {
    if (bestScore == 0) {
        cout << "No matching found!" << endl;
        return;
    }
    cout << "----------Optimal Matching----------" << endl;
    cout << "Best Score: " << bestScore << endl
         << endl;
    // cout << "Input matrix: " << endl;
    // for (int i = 0; i < ans_a.size(); ++i) {
    //     for (int j = 0; j < ans_a[0].size(); ++j) {
    //         cout << ans_a[i][j] << " ";
    //         cout << ans_b[i][j] << " ";
    //     }
    //     cout << endl;
    // }
    // cout << endl;
    // cout << "Output matrix: " << endl;
    // for (int i = 0; i < ans_c.size(); ++i) {
    //     for (int j = 0; j < ans_c[0].size(); ++j) {
    //         cout << ans_c[i][j] << " ";
    //         cout << ans_d[i][j] << " ";
    //     }
    //     cout << endl;
    // }
    // cout << endl;

    // output to file as required format
    // INGROUP
    ofstream out(file_match);
    for (int j = 0; j < x.size(); ++j) {
        // all input in circuit 1 must be mapped
        out << "INGROUP" << endl;
        out << "1 + <" << x[j].getName() << ">"
            << endl;  // include "<>" or not ????
        for (int i = 0; i < y.size(); ++i) {
            if (ans_a[i][j] != 0) {
                out << "2 + <" << y[i].getName() << ">" << endl;
            }
            if (ans_b[i][j] != 0) {
                out << "2 - <" << y[i].getName() << ">" << endl;
            }
        }
        out << "END" << endl
            << endl;
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
        if (circuit1Mapped) out << "END" << endl
                                << endl;
    }
    // CONSTGROUP
    out << "CONSTGROUP" << endl;
    for (int i = 0; i < y.size(); ++i) {
        if (ans_a[i][x.size()])
            out << "+ <" << y[i].getName() << ">" << endl;  // + to 0
        if (ans_b[i][x.size()])
            out << "- <" << y[i].getName() << ">" << endl;  // - to 1
    }
    out << "END" << endl
        << endl;

    out.close();
}

void BMatchSolver::genCircuitModel(ifstream& portMapping, ifstream& aag1, ifstream& aag2) {
    x.clear();
    f.clear();
    y.clear();
    g.clear();
    fStar.clear();
    // TODO: build circuit 1/2 constrains to miter, and add IO port name, Var to
    // x/y, f/g

    readPortMapping(portMapping);
    readAAG(aag1, true);
    readAAG(aag2, false);

    for (int i = 0; i < g.size(); ++i) {
        fStar.push_back(miterSolver.newVar());
    }
}

void BMatchSolver::readPortMapping(ifstream& in) {
    // <1|2>(int) <"input"|"output">(string) <PortName>(string) <VarInCNF>(int)
    int one_two;
    string IO;
    string name;
    int litInAAG;
    while (in >> one_two >> IO >> name >> litInAAG) {
        vector<Port>& IOPorts =
            (one_two == 1 ? (IO == "input" ? x : f) : (IO == "input" ? y : g));
        Var v = AAG2Var(litInAAG / 2, (one_two == 1));
        if (litInAAG % 2 == 1) {                // inverted output
            Var invVar = miterSolver.newVar();  // invVar = ~v
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

void BMatchSolver::readAAG(ifstream& in, bool circuitOne) {
    int litInAAG;
    string aag;
    int M, I, L, O, A;
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
        Var vf = AAG2Var(lf / 2, circuitOne);
        Var va = AAG2Var(la / 2, circuitOne);
        bool fa = la % 2;
        Var vb = AAG2Var(lb / 2, circuitOne);
        bool fb = lb % 2;
        miterSolver.addAigCNF(vf, va, fa, vb, fb);
    }
}

void BMatchSolver::buildMatrix() {
    // TODO: add matrix constraints based on x, f, y, g
    a.clear();
    a.reserve(y.size());
    b.clear();
    b.reserve(y.size());
    c.clear();
    c.reserve(g.size());
    d.clear();
    d.reserve(g.size());

    outputC.clear();
    outputC.reserve(g.size());
    outputD.clear();
    outputD.reserve(g.size());

    outputVarMatrix.clear();
    outputVarMatrix.reserve(g.size());

    possibleMi.clear();
    possibleMi.reserve(y.size());

    possibleMo.clear();
    possibleMo.reserve(g.size());

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
        possibleMi.push_back(vector<bool>(x.size() + 1, true));
    }

    // Output matrix
    for (int i = 0; i < fStar.size(); ++i) {
        vector<mtx2Mit> cTemp(f.size());
        vector<mtx2Mit> dTemp(f.size());

        vector<Var> outputCTemp(f.size());
        vector<Var> outputDTemp(f.size());

        vector<Var> outputVarTemp(f.size());

        for (int j = 0; j < f.size(); ++j) {
            cTemp[j].matrixVar = matrixSolver.newVar();
            dTemp[j].matrixVar = matrixSolver.newVar();

            outputCTemp[j] = outputSolver.newVar();
            outputDTemp[j] = outputSolver.newVar();

            outputVarTemp[j] = outputSolver.newVar();
        }
        c.push_back(cTemp);
        d.push_back(dTemp);

        outputC.push_back(outputCTemp);
        outputD.push_back(outputDTemp);

        outputVarMatrix.push_back(outputVarTemp);
        possibleMo.push_back(vector<bool>(f.size(), true));
    }

    // Input constrints
    // sum >= 1
    vector<Lit> ls;
    ls.reserve(2 * y.size());
    for (int j = 0; j < x.size(); ++j) {  // exclude the zero/one column
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
        matrixSolver.addOneHot(oneHot);
    }

    // Output constraints on outputSolver
    for (int i = 0; i < fStar.size(); ++i) {
        vector<Lit> lits;
        for (int j = 0; j < f.size(); ++j) {
            lits.clear();
            lits.push_back(~Lit(outputC[i][j]));
            lits.push_back(~Lit(outputD[i][j]));
            outputSolver.addCNF(lits);
            for (int k = j + 1; k < f.size(); ++k) {
                lits.clear();
                lits.push_back(~Lit(outputC[i][j]));
                lits.push_back(~Lit(outputC[i][k]));
                outputSolver.addCNF(lits);

                lits.clear();
                lits.push_back(~Lit(outputC[i][j]));
                lits.push_back(~Lit(outputD[i][k]));
                outputSolver.addCNF(lits);

                lits.clear();
                lits.push_back(~Lit(outputD[i][j]));
                lits.push_back(~Lit(outputC[i][k]));
                outputSolver.addCNF(lits);

                lits.clear();
                lits.push_back(~Lit(outputD[i][j]));
                lits.push_back(~Lit(outputD[i][k]));
                outputSolver.addCNF(lits);
            }
        }
    }

    // Output Var Matrix
    // p <-> (c XOR d) == (~p + c + d) (p + ~c) (p + ~d)
    for (int i = 0; i < fStar.size(); ++i) {
        for (int j = 0; j < f.size(); ++j) {
            outputSolver.addXorCNF(outputVarMatrix[i][j], outputC[i][j], false, outputD[i][j], false);
            continue;
            vector<Lit> lits;
            lits.push_back(~Lit(outputVarMatrix[i][j]));
            lits.push_back(Lit(outputC[i][j]));
            lits.push_back(Lit(outputD[i][j]));
            outputSolver.addCNF(lits);

            lits.clear();
            lits.push_back(Lit(outputVarMatrix[i][j]));
            lits.push_back(~Lit(outputC[i][j]));
            outputSolver.addCNF(lits);

            lits[1] = ~Lit(outputD[i][j]);
            outputSolver.addCNF(lits);
        }
    }

    // update score helper Var
    ansHelper.reserve(f.size());
    // vector<Lit> aggressiveLits;
    for (int j = 0; j < f.size(); ++j) {
        ansHelper.push_back(outputSolver.newVar());
        // v <-> (all c in column) + (all d in column)
        // => (¬p ∨ v) ∧ (¬q ∨ v) ∧ (¬r ∨ v) ∧ (¬s ∨ v) ∧ (¬v ∨ p ∨ q ∨ r ∨ s)
        vector<Lit> lits;
        lits.push_back(~Lit(ansHelper[j]));
        for (int i = 0; i < g.size(); ++i) {
            lits.push_back(Lit(outputC[i][j]));
            lits.push_back(Lit(outputD[i][j]));

            vector<Lit> lits2;
            lits2.push_back(Lit(ansHelper[j]));
            lits2.push_back(~Lit(outputC[i][j]));  // (~c + v)
            outputSolver.addCNF(lits2);

            lits2[1] = ~Lit(outputD[i][j]);  // (~d + v)
            outputSolver.addCNF(lits2);
        }
        outputSolver.addCNF(lits);
        // aggressiveLits.push_back(Lit(ansHelper[j]));
    }
    // outputSolver.addCNF(aggressiveLits);
}

void BMatchSolver::genMiterConstraint() {
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

    // Output constraints
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
        Var care = miterSolver.newVar();
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

        lits.push_back(Lit(q));  // q means real no match
    }
    miterSolver.addCNF(lits);

    // one hot constraints
    // vector<Lit> oneHot;
    // for (int i = 0; i < x.size(); ++i) {
    //     oneHot.push_back(Lit(x[i].getVar()));
    // }
    // miterSolver.addOneHot(oneHot);
}

bool BMatchSolver::outputSolve(vector<Var>& outputPairs) {
    cerr << "in outputSolve" << endl;
    outputPairs.clear();
    bool result = outputSolver.assumpSolve();
    if (!result)
        return false;
    cerr << "in outputSolve finish" << endl;
    for (int i = 0; i < fStar.size(); ++i) {
        for (int j = 0; j < f.size(); ++j) {
            if (outputSolver.getValue(outputC[i][j]) == 1) {
                outputPairs.push_back(c[i][j].matrixVar);
                cout << "c" << i << ", " << j << endl;
            }
            if (outputSolver.getValue(outputD[i][j]) == 1) {
                outputPairs.push_back(d[i][j].matrixVar);
                cout << "d" << i << ", " << j << endl;
            }
        }
    }

    vector<Lit> lits;
    for (int i = 0; i < fStar.size(); ++i) {
        for (int j = 0; j < f.size(); ++j) {
            int value = outputSolver.getValue(outputC[i][j]);
            assert(value != -1);
            if (value != -1) {
                lits.push_back(value ? ~Lit(outputC[i][j])
                                     : Lit(outputC[i][j]));
            }
            value = outputSolver.getValue(outputD[i][j]);
            if (value != -1) {
                lits.push_back(value ? ~Lit(outputD[i][j])
                                     : Lit(outputD[i][j]));
            }
            assert(value != -1);
        }
    }
    outputSolver.addCNF(lits);
    return true;
}

bool BMatchSolver::isValidMo(const set<Var>& currentResult) {
    // get input matrix
    matrixSolver.assumeRelease();
    vector<int> current_f, current_g;
    for (int i = 0; i < fStar.size(); ++i) {
        for (int j = 0; j < f.size(); ++j) {
            bool cValue = currentResult.find(c[i][j].matrixVar) != currentResult.end();
            bool dValue = currentResult.find(d[i][j].matrixVar) != currentResult.end();
            matrixSolver.assumeProperty(c[i][j].matrixVar, cValue);
            matrixSolver.assumeProperty(d[i][j].matrixVar, dValue);
            if (cValue || dValue) {
                current_f.push_back(j);
                current_g.push_back(i);
                assumeInputRedundnatFromOutput(f[j].supports, g[i].supports);
            }
        }
    }
    //*
    // assign redundant input mapping
    // (1) find current assign output pair (above: current_f, current_g)
    // (2) find the needed input
    set<int> supportInput_x, supportInput_y;
    set<Var> supports;
    for (int i = 0; i < current_f.size(); ++i) {
        supports = f[current_f[i]].getSupport();
        for (set<int>::iterator it = supports.begin(); it != supports.end(); it++) supportInput_x.insert(*it);
    }
    for (int i = 0; i < current_g.size(); ++i) {
        supports = g[current_g[i]].getSupport();
        for (set<int>::iterator it = supports.begin(); it != supports.end(); it++) supportInput_y.insert(*it);
    }

    // (3) assign redundant
    vector<int> redundantInput_x, redundantInput_y;
    for (int i = 0; i < x.size(); ++i)
        if (!supportInput_x.count(i)) redundantInput_x.push_back(i);
    for (int i = 0; i < y.size(); ++i)
        if (!supportInput_y.count(i)) redundantInput_y.push_back(i);
    for (int i = 0; i < redundantInput_y.size(); ++i) {
        if (redundantInput_x.size() <= i) {
            matrixSolver.assumeProperty(a[redundantInput_y[i]][x.size()].matrixVar,
                                        true);
        } else {
            matrixSolver.assumeProperty(a[redundantInput_y[i]][redundantInput_x[i]].matrixVar,
                                        true);
        }
    }
    matrixSolverInstance = 0;
    matrixSolverPeriodInstance = 0;
    double startTime = clock();
    previousTime = clock();
    while (1) {
        matrixSolverInstance ++;
        matrixSolverPeriodInstance ++;
        if ((clock() - startTime) / CLOCKS_PER_SEC >= 100) return false; //added
        if ((clock() - previousTime) / CLOCKS_PER_SEC >= 1) {
            cerr << "\rMatrix Solver solve: " << setw(4) << matrixSolverPeriodInstance / ((clock() - previousTime) / CLOCKS_PER_SEC) << " /sec, total solve: " << setw(5) << matrixSolverInstance;
            matrixSolverPeriodInstance = 0;
            previousTime = clock();
        }
        bool inputResult = matrixSolver.assumpSolve();
        if (!inputResult) {
            cout << "cannot find other input mapping" << endl;
            return false;
        }

        // Assume to miterSolver and solve
        // Assume input mapping
        miterSolver.assumeRelease();
        for (int i = 0; i < y.size(); ++i) {
            for (int j = 0; j < x.size() + 1; ++j) {
                int matrixVarValue = matrixSolver.getValue(a[i][j].matrixVar);
                if (matrixVarValue != -1) {  // -1 means unknown
                    miterSolver.assumeProperty(a[i][j].miterVar,
                                               matrixVarValue);
                }
                matrixVarValue = matrixSolver.getValue(b[i][j].matrixVar);
                if (matrixVarValue != -1) {  // -1 means unknown
                    miterSolver.assumeProperty(b[i][j].miterVar,
                                               matrixVarValue);
                }
            }
        }
        // Assume output mapping
        for (int i = 0; i < fStar.size(); ++i) {
            for (int j = 0; j < f.size(); ++j) {
                int matrixVarValue = matrixSolver.getValue(c[i][j].matrixVar);
                if (matrixVarValue != -1) {  // -1 means unknown
                    miterSolver.assumeProperty(c[i][j].miterVar,
                                               matrixVarValue);
                }
                matrixVarValue = matrixSolver.getValue(d[i][j].matrixVar);
                if (matrixVarValue != -1) {  // -1 means unknown
                    miterSolver.assumeProperty(d[i][j].miterVar,
                                               matrixVarValue);
                }
            }
        }
        for (int j = 0; j < redundantInput_x.size(); ++j) {
            miterSolver.assumeProperty(x[redundantInput_x[j]].getVar(), false);
        }
        for (int i = 0; i < redundantInput_y.size(); ++i) {
            miterSolver.assumeProperty(y[redundantInput_y[i]].getVar(), false);
        }
        if (miterSolve()) {  // UNSAT -> find a valid mapping
            // Update current answer and block answer
            return true;
        } else {
            // cout << "QQ" << endl;
        }
    }
}

bool BMatchSolver::miterSolve() {
    // cout << endl;
    // cout << "enter miter..." << endl;
    bool miterResult = miterSolver.assumpSolve();
    if (!miterResult) {
        // UNSAT => find a valid mapping
        // update answer and block this answer from outputSlover
        // Block answer

        cout << "Find a valid mapping!" << endl;
        // cout << "Input matrix:" << endl;
        for (int i = 0; i < y.size(); ++i) {
            for (int j = 0; j < x.size() + 1; ++j) {
                // cout << matrixSolver.getValue(a[i][j].matrixVar) << " ";
                // cout << matrixSolver.getValue(b[i][j].matrixVar) << " ";
                ans_a[i][j] = matrixSolver.getValue(a[i][j].matrixVar);
                ans_b[i][j] = matrixSolver.getValue(b[i][j].matrixVar);
            }
            // cout << endl;
        }
        // cout << "Output matrix:" << endl;
        vector<Lit> lits;
        for (int i = 0; i < fStar.size(); ++i) {
            for (int j = 0; j < f.size(); ++j) {
                // cout << matrixSolver.getValue(c[i][j].matrixVar) << " ";
                // cout << matrixSolver.getValue(d[i][j].matrixVar) << " ";
                ans_c[i][j] = matrixSolver.getValue(c[i][j].matrixVar);
                ans_d[i][j] = matrixSolver.getValue(d[i][j].matrixVar);
                lits.push_back(ans_c[i][j] ? ~Lit(outputC[i][j]) : Lit(outputC[i][j]));
                lits.push_back(ans_d[i][j] ? ~Lit(outputD[i][j]) : Lit(outputD[i][j]));
            }
            // cout << endl;
        }

        // ensure the same mapping pair do not check by miter again
        // vector<Lit> lits;
        // for (int i = 0; i < fStar.size(); ++i) {
        //     for (int j = 0; j < f.size(); ++j) {
        //         if (ans_c[i][j] == 1) lits.push_back(~Lit(c[i][j].miterVar));
        //         if (ans_d[i][j] == 1) lits.push_back(~Lit(d[i][j].miterVar));
        //         for (int k = 0; i < y.size(); ++k) {
        //             if (!g[i].isSupport(k)) continue;
        //             for (int l = 0; l < x.size() + 1; ++l) {
        //                 if (!f[j].isSupport(l)) continue;
        //                 lits.push_back(ans_a[k][l] ? ~Lit(a[k][l].miterVar) : Lit(a[k][l].miterVar));
        //                 lits.push_back(ans_b[k][l] ? ~Lit(b[k][l].miterVar) : Lit(b[k][l].miterVar));
        //             }
        //         }
        //     }
        // }
        outputSolver.addCNF(lits);
        int score = getScore();
        if (score > bestScore) {
            bestScore = score;
            outputAns();
            // finalCheck();
        }
        cout << "Score: " << score << ", Best Score: " << bestScore << endl;
        // cout << "  leave miter..." << endl;
        return true;
    } else {
        // SAT =>
        // AND(l_O + OR(l_I))
        // l_O = (g[i] != f[j]) ? ~c[i][j] : ~d[i][j]
        // l_I = (x[j] != y[i]) ? a[i][j] : b[i][j]
        vector<Lit> lits;

        // partial assignment
        vector<int> assign_x, assign_y, assign_f, assign_g;
        vector<set<int>> necessary_f, necessary_g;
        for (int i = 0; i < x.size(); ++i) assign_x.push_back(miterSolver.getValue(x[i].getVar()));
        for (int i = 0; i < y.size(); ++i) assign_y.push_back(miterSolver.getValue(y[i].getVar()));
        for (int i = 0; i < f.size(); ++i) assign_f.push_back(miterSolver.getValue(f[i].getVar()));
        for (int i = 0; i < g.size(); ++i) assign_g.push_back(miterSolver.getValue(g[i].getVar()));

        necessary_f = c1->getNecessary(assign_x, assign_f);
        necessary_g = c2->getNecessary(assign_y, assign_g);

        for (int i = 0; i < fStar.size(); ++i) {
            for (int j = 0; j < f.size(); ++j) {
                if (f[j].nofSupport() > g[i].nofSupport()) continue;
                if (miterSolver.getValue(g[i].getVar()) !=
                    miterSolver.getValue(f[j].getVar())) {
                    lits.push_back(~Lit(c[i][j].matrixVar));
                } else {
                    lits.push_back(~Lit(d[i][j].matrixVar));
                }
                // TODO: and or or
                for (int k = 0; k < y.size(); ++k) {
                    // if (!g[i].isSupport(k))
                    if (!necessary_g[i].count(k))
                        continue;
                    for (int l = 0; l < x.size(); ++l) {
                        // if (!f[j].isSupport(l))
                        if (!necessary_f[j].count(l))
                            continue;
                        if (miterSolver.getValue(y[k].getVar()) !=
                            miterSolver.getValue(x[l].getVar())) {
                            lits.push_back(Lit(a[k][l].matrixVar));
                        } else {
                            lits.push_back(Lit(b[k][l].matrixVar));
                        }
                    }
                    if (miterSolver.getValue(y[k].getVar()) != 0) {
                        lits.push_back(Lit(a[k][x.size()].matrixVar));
                    } else {
                        lits.push_back(Lit(b[k][x.size()].matrixVar));
                    }
                }
                matrixSolver.addCNF(lits);
                lits.clear();
            }
        }
    }
    // cout << "  leave miter..." << endl;
    return false;
}

Var BMatchSolver::AAG2Var(int AAGVar, bool circuitOne) {
    if (!circuitOne) AAGVar = -AAGVar;
    if (AAG2VarHashmap.find(AAGVar) == AAG2VarHashmap.end())
        AAG2VarHashmap[AAGVar] = miterSolver.newVar();
    return AAG2VarHashmap[AAGVar];
}

int BMatchSolver::getScore() {
    // TODO: calcutate current score from c, d and compare it with bestScore

    int score = 0;
    for (int j = 0; j < f.size(); ++j) {
        bool columnMap = false;
        for (int i = 0; i < fStar.size(); ++i) {
            // Not sure these assertions is correct or not
            assert(matrixSolver.getValue(c[i][j].matrixVar) != -1);
            assert(matrixSolver.getValue(d[i][j].matrixVar) != -1);
            //

            score += matrixSolver.getValue(c[i][j].matrixVar);
            score += matrixSolver.getValue(d[i][j].matrixVar);
            if (matrixSolver.getValue(c[i][j].matrixVar) || matrixSolver.getValue(d[i][j].matrixVar))
                columnMap = true;
        }
        if (columnMap)
            score++;
    }
    cout << "in getScore func: " << score << endl;
    return score;
}

void BMatchSolver::scoreGte(int x) {
    // return;
    vector<Lit> clause;
    for (int j = 0; j < f.size(); ++j) {
        for (int i = 0; i < fStar.size(); ++i) {
            clause.push_back(Lit(outputC[i][j]));
            clause.push_back(Lit(outputD[i][j]));
        }
        clause.push_back(Lit(ansHelper[j]));
    }
    outputSolver.addGte(clause, x);
}

int BMatchSolver::getPortIndex(const vector<Port> &ports, const string &portName) const {
  for (int i = 0; i < ports.size(); ++i) {
    if (ports[i].getName() == portName) {
      return i;
    }
  }
  return -1; // return -1 if not found
}


void BMatchSolver::readBusInfo(ifstream &in, bool isCircuit1) {
  string circuitName;
  int nof_bus;
  in >> circuitName;
  in >> nof_bus;
  for (int i = 0; i < nof_bus; ++i) {
    set<int> bus;
    int width;
    in >> width;
    bool isInput = true;
    for (int j = 0; j < width; ++j) {
      string name;
      in >> name;
      // cerr << "name: " << name << endl;
      vector<Port> &inPorts = isCircuit1 ? x : y;
      vector<Port> &outPorts = isCircuit1 ? f : g;
      int index = getPortIndex(inPorts, name);
      if (index == -1) {
        index = getPortIndex(outPorts, name);
        isInput = false;
      }
      assert(index != -1);
      bus.insert(index);
    }
    Buses &buses = isCircuit1 ? (isInput ? xBus : fBus) : (isInput ? yBus : gBus);
    buses.push_back(bus);
    // for (set<int>::iterator itr = bus.begin(); itr != bus.end(); itr++) {
    //     
    // }
  }
  
}

void BMatchSolver::printInfo() const{
    set<int>::const_iterator it;
    // cerr  << "------------ Bus ------------" << endl;
    // cerr  << "--- Cir 1 ---" << endl;
    // cerr  << "- input -" << endl;
    // printBus(xBus);
    // cerr  << "- output -" << endl;
    // printBus(fBus);
    // cerr  << "--- Cir 2 ---" << endl;
    // cerr  << "- input -" << endl;
    // printBus(yBus);
    // cerr  << "- output -" << endl;
    // printBus(gBus);
    // cerr << endl;

    cerr << "------------ Support ------------" << endl;
    cerr  << "--- Cir 1 ---" << endl;
    // cerr  << "- input -" << endl;
    // printSupport(x, f);
    cerr  << "- output -" << endl;
    printSupport(f, x);
    cerr  << "--- Cir 2 ---" << endl;
    // cerr  << "- input -" << endl;
    // printSupport(y, g);
    cerr  << "- output -" << endl;
    printSupport(g, y);
    cerr << endl;
}

void BMatchSolver::printBus(const Buses& bus) const {
    // cerr << "printBus " << endl;
    set<int>::const_iterator it;
    for (int i = 0; i < bus.size(); ++i) {
        for (it = bus[i].begin(); it != bus[i].end(); ++it) {
            cerr << setw(3) << (*it);
        }
        cerr << endl;
    }
}

void BMatchSolver::printSupport(const vector<Port>& portTarget, const vector<Port>& portInv) const {
    // set<int>::const_iterator it;
    map<int, int> statistics;
    for (int i = 0; i < portTarget.size(); ++i) {
        cerr << setw(3) << i << ":";
        cerr << setw(3) << portTarget[i].nofSupport() << endl;
        statistics[portTarget[i].nofSupport()] ++;
        continue;
        // for (it = portTarget[i].supports.begin(); it != portTarget[i].supports.end(); ++it) {
        //     cerr << setw(3) << *it << "(" << setw(2) <<  portInv[(*it)].nofSupport() << ") ";
        // }
        // cerr << endl;
    }
    cerr << "Statistics" << endl;
    for (map<int, int>::iterator it = statistics.begin(); it != statistics.end(); ++it) {
        cerr << "(" << setw(3) << it->first << ":" << setw(3) << it->second << ") ";
    }
    cerr << endl;
}


void BMatchSolver::twoWaySupport(const set<int>& oneIndice, const set<int>& twoIndice) {
    // return ;
    for (int i = 0; i < y.size(); ++i) {
        if (twoIndice.find(i) == twoIndice.end())
            continue;
        for (int j = 0; j < x.size(); ++j) {
            if (oneIndice.find(j) == oneIndice.end()) {
                // matrixSolver.assertProperty(a[i][j].matrixVar, false);
                // matrixSolver.assertProperty(b[i][j].matrixVar, false);
                possibleMi[i][j] = false;
            }
        }
        if (oneIndice.size() == twoIndice.size()) {
            // matrixSolver.assertProperty(a[i][x.size()].matrixVar, false);
            // matrixSolver.assertProperty(b[i][x.size()].matrixVar, false);
            possibleMi[i][x.size()] = false;
        }
    }
}

void BMatchSolver::assumeMo() {
    outputSolver.assumeRelease();
    cerr << "Assume output port matching (ex: 5 0 3 1 -1 means map (f,g) = (5,0) and (3,1)): " << endl;
    int temp;
    int ff, gg;
    set<pair<int, int>> matchVar;
    while (cin >> temp) {
        if (temp == -1) {
            break;
        }
        ff = temp;
        cin >> gg;
        matchVar.insert(make_pair(ff, gg));
    }
    cerr << "Solving with (f, g):";
    for (int i = 0; i < fStar.size(); ++i) {
        for (int j = 0; j < f.size(); ++j) {
            if (matchVar.find(make_pair(j, i)) != matchVar.end()) {
                outputSolver.assumeProperty(outputVarMatrix[i][j], true);
                cerr << " (" << setw(2) << j << "," << setw(2) << i << ")";
            }
            else {
                outputSolver.assumeProperty(outputVarMatrix[i][j], false);
            }
        }
    }
    cerr << endl;
}

void BMatchSolver::busConstraint() {    
    inputBusMatrix.reserve(yBus.size());
    for (int i = 0; i < yBus.size(); ++i) {
        vector<Var> inputBusTemp(xBus.size());
        for (int j = 0; j < xBus.size(); ++j) {
            inputBusTemp[j] = matrixSolver.newVar();
            connectBus(inputBusTemp[j], xBus[j], yBus[i]);
        }
    }
}

void BMatchSolver::connectBus(Var connectVar, const set<int>& bus1, const set<int>& bus2) {
    if (bus1.size() != bus2.size()) {
        cerr << "EEEEEEEEEEEErrorrrrrr: bus sizes are not equal!" << endl;
        return;
    }
    vector<Lit> lits;
    set<int>::const_iterator it1;
    set<int>::const_iterator it2;
    for (it1 = bus1.begin(); it1 != bus1.end(); ++it1) {
        for (it2 = bus2.begin(); it2 != bus2.end(); ++it2) {
            lits.push_back(Lit(a[*it2][*it1].matrixVar));
            lits.push_back(Lit(b[*it2][*it1].matrixVar));
        }
    }
    matrixSolver.addOR(Lit(connectVar), lits);

    // p -> a1 + a2 + a3 + ...
    for (it2 = bus2.begin(); it2 != bus2.end(); ++it2) {
        lits.clear();
        lits.push_back(~Lit(connectVar));
        for (it1 = bus1.begin(); it1 != bus1.end(); ++it1) {
            lits.push_back(Lit(a[*it2][*it1].matrixVar));
            lits.push_back(Lit(b[*it2][*it1].matrixVar));
        }
        matrixSolver.addCNF(lits);
    }
}

//*
void BMatchSolver::assumeInputRedundnatFromOutput(const set<int>& input1, const set<int>& input2) {
    for (set<int>::const_iterator it = input2.begin(); it != input2.end(); ++it) {
        for (int j = 0; j < x.size(); ++j) { // don't need x.size() + 1 because it might be possible to connect to 0/1 
            if (input1.find(j) != input1.end()) {
                if (possibleMi[*it][j] == 0) {
                    matrixSolver.assumeProperty(a[*it][j].matrixVar, false);
                    matrixSolver.assumeProperty(b[*it][j].matrixVar, false);
                }
                continue;
            }
            // matrixSolver.assumeProperty(inputVarMatrix[*it][j], false);
            matrixSolver.assumeProperty(a[*it][j].matrixVar, false);
            matrixSolver.assumeProperty(b[*it][j].matrixVar, false);
        }
        if (input1.size() == input2.size()) {
            matrixSolver.assumeProperty(a[*it][x.size()].matrixVar, false);
            matrixSolver.assumeProperty(b[*it][x.size()].matrixVar, false);
        }
    }
}

void BMatchSolver::simulate() {
    cout << "start to simulate" << endl;
    vector<vector<int>> assign_Input_x, assign_Output_f;
    vector<vector<int>> assign_Input_y, assign_Output_g;
    vector<vector<set<int>>> necessarys_f, necessarys_g;
    vector<Lit> lits;
    c1->randomSim2Necessary(assign_Input_x, assign_Output_f, necessarys_f);
    c2->randomSim2Necessary(assign_Input_y, assign_Output_g, necessarys_g);

    // total simulate 64 times (0~63)
    for (int times = 0; times < 64; ++times) {
        for (int i = 0; i < fStar.size(); ++i) {
            for (int j = 0; j < f.size(); ++j) {
                if (f[j].nofSupport() > g[i].nofSupport()) continue;
                // A(x_l= y_k) & B -> f!=g
                // f=g -> ~A or ~B
                // ( !(f=g) + ~A(x_l=y_k) + ~B)
                if (assign_Output_g[times][i] !=
                    assign_Output_f[times][j]) {
                    lits.push_back(~Lit(c[i][j].matrixVar));
                } else {
                    lits.push_back(~Lit(d[i][j].matrixVar));
                }
                for (int k = 0; k < y.size(); ++k) {
                    if (!necessarys_g[times][i].count(k))
                        continue;
                    for (int l = 0; l < x.size(); ++l) {  // +1 or not
                        if (!necessarys_f[times][j].count(l))
                            continue;
                        if (assign_Input_y[times][k] !=
                            assign_Input_x[times][l]) {
                            lits.push_back(Lit(a[k][l].matrixVar));
                        } else {
                            lits.push_back(Lit(b[k][l].matrixVar));
                        }
                    }
                    if (assign_Input_y[times][k] != 0) {
                        lits.push_back(Lit(a[k][x.size()].matrixVar));
                    } else {
                        lits.push_back(Lit(b[k][x.size()].matrixVar));
                    }
                }
                matrixSolver.addCNF(lits);
                lits.clear();
            }
        }
    }
}
void BMatchSolver::interactiveSolve() {
    assumeMo();
    while (1) {
        vector<Var> outputPairs;
        bool result = outputSolve(outputPairs);
        if (!result) {
            cerr << "No output matrix found!" << endl;
            assumeMo();
            continue;
        }
        set<Var> currentResult(outputPairs.begin(), outputPairs.end());
        if (isValidMo(currentResult)) {
            cerr << "Find valid input matrix!" << endl;
            assumeMo();
        } else {
            cerr << "No input matrix found!" << endl;
        }
    }
}

void BMatchSolver::printPossibleM(bool mi, bool mo) {
    if (mi) {
        cout << "--------------- Possible Mi ---------------" << endl;
        for (int i = 0; i < y.size(); ++i) {
            for (int j = 0; j < x.size() + 1; ++j) {
                cout << possibleMi[i][j];
            }
            cout << endl;
        }
        cout << "--------------- Possible Mi end -----------" << endl;
        cout << endl;
        cout.flush();
    }
    if (mo) {
        cout << "--------------- Possible Mo ---------------" << endl;
        for (int i = 0; i < g.size(); ++i) {
            for (int j = 0; j < f.size(); ++j) {
                cout << possibleMo[i][j];
            }
            cout << endl;
        }
        cout << "--------------- Possible Mp end -----------" << endl;
        cout << endl;
        cout.flush();
    }
}

void BMatchSolver::possibleMethod() {
    if (x.size() != y.size()) {
        return;
    }
    printPossibleM(true, true);
    bool modify;
    do {
        modify = false;
        modify |= checkPossibleMi();
        modify |= checkPossibleMo();
    }
    while (!modify);
    return;
}

bool BMatchSolver::checkPossibleMi() {
    bool modify = false;
    for (int i = 0; i < y.size(); ++i) {
        if (possibleMi[i][x.size()]) // possilbe to map to const
            continue;
        set<int> SuppX_y; // Supp(X_y) = Union{sup(x)}, x \in X_y
        for (int j = 0; j < x.size(); ++j) {
            if (!possibleMi[i][j])
                continue;
            for (set<int>::const_iterator it = x[j].supports.begin(); it != x[j].supports.end(); ++it) {
                SuppX_y.insert(*it);
            }
        }
        for (set<int>::const_iterator it = y[i].supports.begin(); it != y[i].supports.end(); ++it) {
            for (int j = 0; j < f.size(); ++j) {
                if (SuppX_y.find(j) != SuppX_y.end()) // f[j] \in Supp(X_y) 
                    continue;
                if (possibleMo[*it][j])
                    modify = true;
                possibleMo[*it][j] = false;
            }
        }
    }
    return modify;
}

bool BMatchSolver::checkPossibleMo() {
    bool modify = false;
    for (int i = 0; i < g.size(); ++i) {
        set<int> SuppF_g;
        for (int j = 0; j < f.size(); ++j) {
            if (possibleMo[i][j] == 0)
                continue;
            for (set<int>::const_iterator it = f[j].supports.begin(); it != f[j].supports.end(); ++it) {
                SuppF_g.insert(*it);
            }
        }
        for (set<int>::const_iterator it = g[i].supports.begin(); it != g[i].supports.end(); ++it) {
            for (int j = 0; j < x.size(); ++j) {
                if (SuppF_g.find(j) != SuppF_g.end())
                    continue;
                if (possibleMi[*it][j])
                    modify = true;
                possibleMi[*it][j] = false;
            }
        }
    }
    return modify;
}

bool BMatchSolver::finalCheck() {
    miterSolver.assumeRelease();
    for (int i = 0; i < ans_a.size(); ++i) {
        for (int j = 0; j < ans_a[0].size(); ++j) {
            miterSolver.assumeProperty(a[i][j].miterVar,
                                       ans_a[i][j]);
            miterSolver.assumeProperty(b[i][j].miterVar,
                                       ans_b[i][j]);
        }
    }
    for (int i = 0; i < ans_c.size(); ++i) {
        for (int j = 0; j < ans_c[0].size(); ++j) {
            miterSolver.assumeProperty(c[i][j].miterVar,
                                       ans_c[i][j]);
            miterSolver.assumeProperty(d[i][j].miterVar,
                                       ans_d[i][j]);
        }
    }
    bool miterResult = miterSolver.assumpSolve();
    if (!miterResult) {
        cout << "\033[1;32mCORRECT ANSWER\033[0m" << endl;
        return true;
    } else {
        cout << "\033[1;31mWRONG ANSWER\033[0m" << endl;
        return false;
    }
}
constexpr unsigned int str2int(const char* str, int h = 0) {
    return !str[h] ? 5381 : (str2int(str, h + 1) * 33) ^ str[h];
}

void BMatchSolver::printGateInfoHelper(unordered_map<string, vector<string>>& map, string fanout, vector<int>& gateCount) {
    if (map.find(fanout) != map.end()) {
        // GATE = [0]
        switch (str2int(map[fanout][0].c_str())) {
            case str2int("and"):
                ++gateCount[0];
                break;
            case str2int("or"):
                ++gateCount[1];
                break;

            case str2int("nand"):
                ++gateCount[2];
                break;

            case str2int("nor"):
                ++gateCount[3];
                break;

            case str2int("not"):
                ++gateCount[4];
                break;

            case str2int("xor"):
                ++gateCount[5];
                break;
            case str2int("xnor"):
                ++gateCount[6];
                break;
            case str2int("buf"):
                ++gateCount[7];
                break;
        }
        printGateInfoHelper(map, map[fanout][1], gateCount);
        if (map[fanout].size() == 3) printGateInfoHelper(map, map[fanout][2], gateCount);
    }
}

void BMatchSolver::printGateInfo(unordered_map<string, vector<string>>& map_1, unordered_map<string, vector<string>>& map_2) {
    cout << "--------------- Circuit 1 --------------- " << endl;
    cout << setw(8) << " " << setw(7) << "and" << setw(7) << "or" << setw(7) << "nand" << setw(7) << "nor" << setw(7) << "not" << setw(7) << "xor" << setw(7) << "xnor" << setw(7) << "buf" << endl;
    for (size_t i = 0; i < c1->POs.size(); ++i) {
        vector<int> gateCount(8, 0);
        cout << setw(6) << c1->getIOName(c1->POs[i]) << " : ";
        printGateInfoHelper(map_1, c1->getIOName(c1->POs[i]), gateCount);
        for (size_t j = 0; j < 8; ++j) cout << setw(6) << gateCount[j] << " ";
        cout << endl;
    }
    cout << "--------------- Circuit 2 --------------- " << endl;
    cout << setw(8) << " " << setw(7) << "and" << setw(7) << "or" << setw(7) << "nand" << setw(7) << "nor" << setw(7) << "not" << setw(7) << "xor" << setw(7) << "xnor" << setw(7) << "buf" << endl;
    for (size_t i = 0; i < c2->POs.size(); ++i) {
        vector<int> gateCount(8, 0);
        cout << setw(6) << c2->getIOName(c2->POs[i]) << " : ";
        printGateInfoHelper(map_2, c2->getIOName(c2->POs[i]), gateCount);
        for (size_t j = 0; j < 8; ++j) cout << setw(6) << gateCount[j] << " ";
        cout << endl;
    }
}

// when find best output pair, start to find all candidates of input matching
void BMatchSolver::findAllInputCandidate() {
    // block current Input matrix
    vector<Lit> lits;
    for (int i = 0; i < fStar.size(); ++i) {
        for (int j = 0; j < f.size(); ++j) {
            // cout << matrixSolver.getValue(c[i][j].matrixVar) << " ";
            // cout << matrixSolver.getValue(d[i][j].matrixVar) << " ";
            ans_a[i][j] = matrixSolver.getValue(a[i][j].matrixVar);
            ans_b[i][j] = matrixSolver.getValue(b[i][j].matrixVar);
            lits.push_back(ans_a[i][j] ? ~Lit(a[i][j].matrixVar) : Lit(a[i][j].matrixVar));
            lits.push_back(ans_b[i][j] ? ~Lit(b[i][j].matrixVar) : Lit(b[i][j].matrixVar));
        }
    }
    matrixSolver.addCNF(lits);

    // get input matrix
    matrixSolver.assumeRelease();
    vector<int> current_f, current_g;
    for (int i = 0; i < fStar.size(); ++i) {
        for (int j = 0; j < f.size(); ++j) {
            matrixSolver.assumeProperty(c[i][j].matrixVar, ans_c[i][j]);
            matrixSolver.assumeProperty(d[i][j].matrixVar, ans_d[i][j]);
        }
    }
    int candidateCount = 0;
    while (1) {
        cerr << "while HEAD" << endl;
        bool inputResult = matrixSolver.assumpSolve();
        cerr << "assumpSolve" << endl;
        if (!inputResult) {
            cout << "total input candidate : " << candidateCount << endl;
            cout << "cannot find other input mapping" << endl;
            return;
        }
        cerr << "1";
        // Assume to miterSolver and solve
        // Assume input mapping
        miterSolver.assumeRelease();
        for (int i = 0; i < y.size(); ++i) {
            for (int j = 0; j < x.size() + 1; ++j) {
                int matrixVarValue = matrixSolver.getValue(a[i][j].matrixVar);
                if (matrixVarValue != -1) {  // -1 means unknown
                    miterSolver.assumeProperty(a[i][j].miterVar,
                                               matrixVarValue);
                }
                matrixVarValue = matrixSolver.getValue(b[i][j].matrixVar);
                if (matrixVarValue != -1) {  // -1 means unknown
                    miterSolver.assumeProperty(b[i][j].miterVar,
                                               matrixVarValue);
                }
            }
        }
        cerr << "2";
        // Assume output mapping
        for (int i = 0; i < fStar.size(); ++i) {
            for (int j = 0; j < f.size(); ++j) {
                int matrixVarValue = matrixSolver.getValue(c[i][j].matrixVar);
                if (matrixVarValue != -1) {  // -1 means unknown
                    miterSolver.assumeProperty(c[i][j].miterVar,
                                               matrixVarValue);
                }
                matrixVarValue = matrixSolver.getValue(d[i][j].matrixVar);
                if (matrixVarValue != -1) {  // -1 means unknown
                    miterSolver.assumeProperty(d[i][j].miterVar,
                                               matrixVarValue);
                }
            }
        }
        cerr << "3" << endl;
        cerr << "START miter..." << endl;
        if (miterSolve()) {  // UNSAT -> find a valid mapping
            // Update current answer and block answer
            ++candidateCount;
            cout << "candidateCount : " << candidateCount << endl;
            // block current Input matrix
            vector<Lit> lits;
            for (int i = 0; i < fStar.size(); ++i) {
                for (int j = 0; j < f.size(); ++j) {
                    // cout << matrixSolver.getValue(c[i][j].matrixVar) << " ";
                    // cout << matrixSolver.getValue(d[i][j].matrixVar) << " ";
                    ans_a[i][j] = matrixSolver.getValue(a[i][j].matrixVar);
                    ans_b[i][j] = matrixSolver.getValue(b[i][j].matrixVar);
                    lits.push_back(ans_a[i][j] ? ~Lit(a[i][j].matrixVar) : Lit(a[i][j].matrixVar));
                    lits.push_back(ans_b[i][j] ? ~Lit(b[i][j].matrixVar) : Lit(b[i][j].matrixVar));
                }
            }
            matrixSolver.addCNF(lits);
        } else {
            cout << "not input candidate" << endl;
        }
    }
}