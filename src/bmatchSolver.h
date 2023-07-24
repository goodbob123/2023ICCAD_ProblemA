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
    friend class BMatchSolver;

   public:
    Port(const string& _name, const Var& _var) {
        name = _name;
        var = _var;
    }
    ~Port() {}
    string getName() const { return name; }
    Var getVar() const { return var; }
    set<int> getSupport() const { return supports; }

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

class Order
{   // Order would record the information about the assignment of f->g and the assignment chain
    public:
        Order() {
            is_head = true;
        }
        Order(Port* _gport_ptr, size_t _gport_id, Port* _fport_ptr, size_t _fport_id) {
            is_head = false;
            fport_ptr = _fport_ptr;
            fport_id = _fport_id;
            gport_ptr = _gport_ptr;
            gport_id = _gport_id;
            is_assign = false;
            en = false;   // should only changed in OutPortMgr::genHeuristicOrder
            is_forbid = true;
            forbid_order = vector<Order*> ();
            // forbid_reason = 0;
            order_nxt = 0;  // should only changed in OutPortMgr::genHeuristicOrder
            assign_nxt = 0;
            assign_pre = 0;
        }
        bool isHead() const {
            return is_head;
        }
        bool isForbid() const {
            if (!en) assert(is_forbid);
            return is_forbid;
            // if (!en) return true;
            // else if (forbid_reason == 0) return false;
            // else {
            //     assert(forbid_reason->is_assign);
            //     return true;
            // }
        }
        bool isNeg() const { return is_neg; }
        bool isPos() const { return is_pos; }
        size_t getId() const { return id; }
        size_t getFid() const { return fport_id; }
        size_t getGid() const { return gport_id; }
        Port* getFptr() const { return fport_ptr; }
        Port* getGptr() const { return gport_ptr; }
        Order* getAssignNxt() const { return assign_nxt; }
        
        // void updateForbidReason(Order* new_reason) {
        //     // if new reason found && !isForbid(), update forbid_reason
        //     if (!isForbid()) forbid_reason = new_reason;
        // }
        void updateForbidOrder(Order* _forbid_order) {
            // if _forbid_order was able to be assigned
            // make _forbid_order unable to assign
            // and record in the vector forbid_order
            if (_forbid_order == 0) {
                // _forbid_order == 0 iff we want to unsign *this (i.e. backToPre)
                // we make forbid assignments able to assign again,
                // and clear forbid_order
                assert(is_assign == false);
                for (size_t i = 0; i < forbid_order.size(); ++i) {
                    forbid_order[i]->is_forbid = false;
                }
                forbid_order.clear();
            } else {
                if (!_forbid_order->is_forbid) {
                    _forbid_order->is_forbid = true;
                    forbid_order.push_back(_forbid_order);
                }
            }
        }

        void assign(Order* pre) {
            // neccesary change for assignment
            // pre record the parent in assignment chain
            assert(!is_forbid);
            assign_pre = pre;
            assign_nxt = order_nxt; // new assignment, start from order_nxt
            is_assign = true;
            is_neg = true;
            is_pos = true;
        }
        void failNeg() {
            is_neg = false;
        }
        void failPos() {
            is_pos = false;
        }
        Order* backToPre() {    
            // one step of backtrack
            // return 0 if no Pre
            Order* pre = assign_pre;
            if (pre != 0) {
                assert(assign_pre.en);
                pre->assign_nxt = order_nxt;
            }

            // unassign
            is_assign = false;
            assign_nxt = 0;
            assign_pre = 0;
            is_neg = true;
            is_pos = true;
            updateForbidOrder(0);   // clear forbid_order

            return pre;
        }
        Order* backTrack() {
            // backTrack to get ready for next assignment
            Order* pre = backToPre();
            if (pre == 0) return 0;
            while (pre->assign_nxt == 0 || pre->assign_nxt->isForbid() || pre->assign_nxt->isAssign()) {
                if (pre->assign_nxt == 0) pre = pre->backToPre(); // no new assignment, need further backtrack
                else pre->assign_nxt = pre->assign_nxt->order_nxt; // next Order in chain is not available
                if (pre == 0) return 0; // return 0 if no pre
            }
            return pre;
        }
        Order* step() {
            // get next assignments
            // if backTrack happen, then only do backTrack 
            // and return the node we backTrack to. need to step again to get next assignments
            while (assign_nxt == 0 || assign_nxt->isForbid()) {
                if (assign_nxt == 0) {
                    Order* pre = backTrack();  // pre->assign_nxt != 0, go to else
                    if (pre == 0) return 0;
                    else return pre;
                } else { // i.e. assign_nxt->isForbid(), thus we should go to next Order in chain
                    assert(!assign_nxt->is_assign());
                    assert(assign_nxt->en);
                    assign_nxt = assign_nxt->order_nxt;
                }
            }
            // i.e. assign_nxt is new assignment
            assert(!assign_nxt->is_assign());
            assert(assign_nxt->en);
            assign_nxt->assign(this);
            return assign_nxt;
        }
        void printMapping() { 
            if (isHead()) cout << "Head" << endl;
            else cout << fport_id << " -> " << gport_id 
                        << "(" << id << ")" << endl; 
        }
        void printLink() {
            cout << "assign_nxt : ";
            if (assign_nxt == 0) cout << "0" << endl;
            else assign_nxt->printMapping();
            cout << "assign_pre : ";
            if (assign_pre == 0) cout << "0" << endl;
            else assign_pre->printMapping();
            cout << "order_nxt : ";
            if (order_nxt == 0) cout << "0" << endl;
            else order_nxt->printMapping();
        }
        void enable(Order* _order_nxt) {
            // make the Order able to assign and unsign
            // _order_nxt record next Order in chain
            en = true;
            is_forbid = false;
            id = en_count;
            order_nxt = _order_nxt;
            ++en_count;
        }
        bool isAssign() { return is_assign; }
    private:
        bool is_head;   // head is a pseudo node used as head of the Order chain

        Port* fport_ptr; // correspond Port in f
        size_t fport_id; // correspond index of port in f
        Port* gport_ptr;
        size_t gport_id;
        bool is_assign; // is fport->gport matching assigned
        bool is_pos;    // whether positive match is possible
        bool is_neg;    // whether negation match is possible
        bool is_forbid; // is such assignment possible
        // Order* forbid_reason;
        vector<Order*> forbid_order; // if assign, the assignment disabled by implication 

        bool en;  // is the Order able to assign and unsign
        static size_t en_count; // num of enable Orders
        size_t id; // the index in the Order chain

        Order* order_nxt;  // next Order in possible assignment chain
        Order* assign_nxt; // next Order in assignment chain
        Order* assign_pre; // pre Order in assignment chain

};
// class BusInfo
// {
//     public:
//         BusInfo() {}
//         vector<BusInfo*> connectBus;
//         size_t bus_size;
//         size_t bus_id;
//         size_t remain_bus;
//         bool isConnect() { return !connectBus.empty();}
//         bool isFull() { return (remain_bus == 0); }
// };
// from big to small
class Comparator {  
    // cmp num Support
    // since used in OutPortMgr, Port is stored as second of pair
    public:
        bool operator() (pair<size_t, Port>& a, pair<size_t, Port>& b) {
            return a.second.nofSupport() < b.second.nofSupport();
        }
};

class OutPortMgr
{
    public:
        OutPortMgr() {}
    
        void init(vector<Port>& _fptr, vector<Port>& _gptr) {
            fptr = &_fptr;
            gptr = &_gptr;
            is_one_to_one = (_fptr.size() == _gptr.size());
            order_map = vector<vector<Order> > ();
            assign_head = new Order();
            assign_current = assign_head;
            is_backtrack = false;

            // cout << "Mgr2" << endl;
            for (size_t i = 0; i < _gptr.size(); ++i) {
                vector<Order> buffer;
                for (size_t j = 0; j < _fptr.size(); ++j) {
                    Order ord(&_gptr[i], i, &_fptr[j], j);
                    buffer.push_back(ord);
                }
                order_map.push_back(buffer);
            }
            // cout << "Mgr1" << endl;
            genHeuristicOrder();    // i.e. gen possible order chain
            // cout << "Mgr0" << endl;
            genBusInfo();
        }
        Order* step() {
            size_t pre_id = assign_current->getId();    // id is index in possible assignment chain
            assign_current = assign_current->step();    // get next assignment (if backTrack, only do backTrack)
            // cout << "step1" << endl;
            size_t now_id = assign_current != 0 ? assign_current->getId() : 0; // assign_current == 0 iff no next assignment
            is_backtrack = pre_id > now_id;
            if (!is_backtrack) { // not backtrack means the assign_current is new assignment's end
                // forbid some assignments according to rules
                assert(now_id != 0);
                // cout << "step2" << endl;
                noRemapRule(); 
            }
            return assign_current;
        }
        Order* backTrack() {
            // backtrack
            is_backtrack = true;
            assign_current = assign_current->backTrack();
            return assign_current;
        }
        Order* getHead() { return assign_head; }
        Order* getAssign() { return assign_current; }
        bool isBacktrack() { return is_backtrack; }
        vector<Order*> getAllAssign() const {
            // return Orders in current assignments
            vector<Order*> assignment;
            Order* cur = assign_head;
            while (cur != assign_current) {
                assert(cur != 0);
                cur = cur->getAssignNxt();
                assignment.push_back(cur);
            }
            return assignment;
        }
        void printAssign() {
            cout << "current assign: ";
            assign_current->printMapping();
            for (size_t i = 0; i < order_map.size(); ++i) {
                vector<Order>& vec = order_map[i];
                for (size_t j = 0; j < vec.size(); ++j) {
                    Order& ord = vec[j];
                    if (ord.isAssign()) cout << "O ";
                    else if (ord.isForbid()) cout << "X ";
                    else cout << "* ";
                }
                cout << endl;
            }
        }

    private:
        bool is_one_to_one; // do we assume output is one to one
        vector<Port>* fptr; // copy of f
        vector<Port>* gptr; // copy of g

        // vector<BusInfo> fbus;
        // vector<BusInfo> gbus;

        vector<vector<Order> > order_map; // matrix of Order, same as format of c, d in bmatch
        Order* assign_head; // pseudo head of chain of possible assignment
        Order* assign_current;  // current end of assignment
        bool is_backtrack;  // whether previous step is backtracking

        void genHeuristicOrder() {

            vector<pair<size_t, Port> > f_sort;
            vector<pair<size_t, Port> > g_sort;
            for (size_t i = 0; i < fptr->size(); ++i) {
                f_sort.push_back(pair<size_t, Port> (i, fptr->at(i)));
            }
            for (size_t i = 0; i < gptr->size(); ++i) {
                g_sort.push_back(pair<size_t, Port> (i, gptr->at(i)));
            }
            
            // sort the f, g by support
            sort(f_sort.begin(), f_sort.end(), Comparator());
            sort(g_sort.begin(), g_sort.end(), Comparator());

            // for (auto f: f_sort) {
            //     cout << f.first << "--";
            //     cout << f.second.nofSupport() << endl;
            // }
            // for (auto g: g_sort) {
            //     cout << g.first << "--";
            //     cout << g.second.nofSupport() << endl;
            // }
            // cout << "gen4" << endl;

            vector<vector<Order*> > order_sort; // group of valid assignment
            if (is_one_to_one) {
                assert(f_sort[0].second.nofSupport() < g_sort[0].second.nofSupport());
                size_t cut = 0; // cut is the end of previous group
                for (size_t i = 1; i < f_sort.size(); ++i) {
                    assert(f_sort[i].second.nofSupport() < g_sort[i].second.nofSupport());    // if fail, means not one to one
                    // cout << "gen3 " << i << endl;
                    if (f_sort[i - 1].second.nofSupport() > g_sort[i].second.nofSupport()) {
                        // group found, between [cut, i)
                        for (size_t i_g = cut; i_g < i; ++i_g) {
                            for (size_t i_f = cut; i_f < i; ++i_f) {
                                pair<size_t, Port> fp = f_sort[i_f];
                                pair<size_t, Port> gp = g_sort[i_g];
                                groupMapping(fp, gp, order_sort); // find the group, add in group set
                            }
                        }
                        cut = i; // update cut
                    }
                }
                // cout << "gen2" << endl;
                // cout << cut << endl;
                assert(f_sort[f_sort.size()].second.nofSupport() < g_sort[f_sort.size()].second.nofSupport());

                // final group should added
                for (size_t i_g = cut; i_g < g_sort.size(); ++i_g) {
                    for (size_t i_f = cut; i_f < f_sort.size(); ++i_f) {
                        pair<size_t, Port> fp = f_sort[i_f];
                        pair<size_t, Port> gp = g_sort[i_g];
                        groupMapping(fp, gp, order_sort); // find the group, add in group set
                    }
                }
                // cout << "__grp__" << endl;
                // for (auto grp: order_sort) {
                //     for (auto ord: grp) {
                //         ord->printMapping();
                //     }
                //     cout << "____" << endl;
                // }

            } else {
                cerr << "not done yet" << endl;
                for (size_t i_g = 0; i_g < g_sort.size(); ++i_g) {
                    for (size_t i_f = 0; i_f < f_sort.size(); ++i_f) {
                        pair<size_t, Port> fp = f_sort[i_f];
                        pair<size_t, Port> gp = g_sort[i_g];
                        groupMapping(fp, gp, order_sort);
                    }
                }
            }

            // cout << "gen1" << endl;

            // make the order chain
            Order* pre = 0;
            Order* nxt = assign_head;
            for (size_t i = 0; i < order_sort.size(); ++i) {
                vector<Order*>& group = order_sort[i];
                for (size_t j = 0; j < group.size(); ++j) {
                    Order*& ord_ptr = group[j];
                    // if (assign_head == 0) assign_head = ord_ptr;
                    pre = nxt;
                    nxt = ord_ptr;
                    if (pre != 0) pre->enable(nxt);
                }
            }
            assign_head->assign(0); // pre of head make it 0
            nxt->enable(0); // nxt of tail make it 0

        }
        void groupMapping(pair<size_t, Port>& fp, pair<size_t, Port>& gp, vector<vector<Order*> >& order_sort) {
            // Order* buf_order_ptr = &order_map[fp.first][gp.first];
            Order* buf_order_ptr = &order_map[gp.first][fp.first];
            if (gp.second.nofSupport() < fp.second.nofSupport()) return;    // support should be bigger
            size_t group = gp.second.nofSupport() - fp.second.nofSupport(); // if support is near, make it priority
            // cout << group << endl;
            group *= 2;
            // if (gp.second.getBusSize() != fp.second.getBusSize()) ++group;
            while (order_sort.size() <= group) order_sort.push_back(vector<Order*> ()); // add group size till enough
            order_sort[group].push_back(buf_order_ptr);
        }
        void genBusInfo() {
            // todo
        }
        void noRemapRule() {
            // cout << assign_current << endl;
            // assign_current->printMapping();
            size_t gid = assign_current->getGid();
            size_t fid = assign_current->getFid();

            // g->f1 no g->f2
            for (size_t i = 0; i < fptr->size(); ++i) {
                if (i == fid) continue;
                else {
                    assert(&(order_map[gid][i]) != 0);
                    assign_current->updateForbidOrder(&(order_map[gid][i]));
                    // order_map[gid][i].updateForbidReason(assign_current);
                }
            }
            if (is_one_to_one) {
                // f->g1 no f->g2
                for (size_t i = 0; i < gptr->size(); ++i) {
                    if (i == gid) continue;
                    else {
                        assert(&(order_map[i][fid]) != 0);
                        assign_current->updateForbidOrder(&(order_map[i][fid]));
                        // order_map[i][fid].updateForbidReason(assign_current);
                    }
                }
            }
        }
};

struct mtx2Mit {
    Var matrixVar;
    Var miterVar;
};


typedef vector<set<int>> Buses;

class BMatchSolver {
   public:
    BMatchSolver(){};
    ~BMatchSolver(){};
    void init(ifstream& portMapping, ifstream& aag1, ifstream& aag2);
    void genFuncSupport(ifstream& in);
    void readBusInfo(ifstream &in, bool isCircuit1);
    void inputPreprocess();
    void outputPreprocess(ifstream& in1, ifstream& in2);
    void run(char* match);
    void outputAns(char* match);
    void printInfo() const;
    void printBus(const Buses& bus) const;
    void printSupport(const vector<Port>& portTarget, const vector<Port>& portInv) const;
    void busConstraint();
    void testOutputMgr();

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

    int getPortIndex(const vector<Port> &ports, const string &portName) const;
    void twoWaySupport(const set<int>& oneIndice, const set<int>& twoIndice);
    void assumeMo();
    void connectBus(Var connectVar, const set<int>& bus1, const set<int>& bus2);
    void assumeInputRedundnatFromOutput(const set<int>& input1, const set<int>& input2);

    // SAT Solver
    SatSolver matrixSolver, miterSolver;
    SatSolver outputSolver;
    OutPortMgr outMgr;

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

    // Bus
    Buses xBus;
    Buses fBus;
    Buses yBus;
    Buses gBus;

    // Var matching matrix
    vector<vector<Var>> outputVarMatrix;
    // vector<vector<Var>> inputVarMatrix;

    vector<vector<Var>> inputBusMatrix;

};