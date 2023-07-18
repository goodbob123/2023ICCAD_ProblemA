
#include <stdio.h>
#include "./SAT/test/sat.h"
extern "C"
{
  #include "aiger.h"
}

#include <iostream>
#include <string>
#include <vector>
#include <fstream>
#include <sstream>
#include <cstring>
#include <time.h>
#include <unordered_map>
#include <algorithm>
#include <set>
#include <map>
using namespace std;
////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////




class Port  // find in code by ctrl+F "pushPort"
{
    public:
        Port(const string& _name, const Var& _var) {
            name = _name;
            var  = _var;
            // id = _id;
            // support = 0;
            bus_size = 0;
        }
        ~Port() {}
        string getName() const { return name; }
        Var    getVar() const { return var; }
        size_t getBusId() const { return bus_id; }
        size_t getBusSize() const { return bus_size; }
        // size_t getId() const {return id;}
        
        // can this part be private ? 
        size_t bus_id;  // different bus should give different id
        size_t bus_size; 
        void addSupport(int index) { supports.insert(index); }
        void addSupport(vector<int> index) { for (auto i: index) supports.insert(i); }
        size_t nofSupport() const { return supports.size(); }
        bool isSupport(int index) const {return supports.find(index) != supports.end();}

    private:
        string name;
        Var    var;
        set<int> supports;
        // size_t id;
};
class Order
{
    public:
        Order() {
            is_head = true;
        }
        Order(Port* _fport_ptr, size_t _fport_id, Port* _gport_ptr, size_t _gport_id) {
            is_head = false;
            fport_ptr = _fport_ptr;
            fport_id = _fport_id;
            gport_ptr = _gport_ptr;
            gport_id = _gport_id;
            is_assign = false;
            en = false;   // should only changed in OutPortMgr::genHeuristicOrder
            forbid_reason = 0;
            order_nxt = 0;  // should only changed in OutPortMgr::genHeuristicOrder
            assign_nxt = 0;
            assign_pre = 0;
        }
        bool isHead() const {
            return is_head;
        }
        bool isForbid() const { 
            if (!en) return true;
            else if (forbid_reason == 0) return false;
            else return forbid_reason->is_assign;
        }
        size_t getId() const { return id; }
        size_t getFid() const { return fport_id; }
        size_t getGid() const { return gport_id; }
        Port* getFptr() const { return fport_ptr; }
        Port* getGptr() const { return gport_ptr; }
        Order* getAssignNxt() const { return assign_nxt; }
        void updateForbidReason(Order* new_reason) {
            // if new reason found && !isForbid(), update forbid_reason
            if (!isForbid()) forbid_reason = new_reason;
        }

        void assign(Order* pre) {
            assign_pre = pre;
            assign_nxt = order_nxt;
            is_assign = true;
        }
        Order* backToPre() {    // return 0 if no Pre
            Order* pre = assign_pre;
            if (pre != 0) {
                assert(assign_pre.en);
                pre->assign_nxt = order_nxt;
            }

            is_assign = false;
            assign_nxt = 0;
            assign_pre = 0;

            return pre;
        }
        Order* backTrack() {    // return 0 if no pre
            Order* pre = backToPre();
            if (pre == 0) return 0;
            while (pre->assign_nxt == 0 || pre->assign_nxt->isForbid() || pre->assign_nxt->isAssign()) {
                // pre->assign_nxt = pre->assign_nxt->order_nxt;
                if (pre->assign_nxt == 0) pre = pre->backToPre();
                else pre->assign_nxt = pre->assign_nxt->order_nxt;
                if (pre == 0) return 0;
            }
            return pre;
        }
        Order* step() {
            // Order* nxt = assign_nxt;
            // Order* pre;
            while (assign_nxt == 0 || assign_nxt->isForbid()) {
                if (assign_nxt == 0) {
                    Order* pre = backTrack();  // pre->assign_nxt != 0, go to else
                    if (pre == 0) return 0;
                    else return pre;
                } else { // assign_nxt->isForbid()
                    assert(!assign_nxt->is_assign());
                    assert(assign_nxt->en);
                    assign_nxt = assign_nxt->order_nxt;
                }
            }
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
            en = true;
            id = en_num;
            order_nxt = _order_nxt;
            ++en_num;
        }
        bool isAssign() { return is_assign; }
    private:
        bool is_head;

        Port* fport_ptr;
        size_t fport_id;
        Port* gport_ptr;
        size_t gport_id;
        bool is_assign;
        Order* forbid_reason;

        bool en;  // be const
        static size_t en_num;
        size_t id;

        Order* order_nxt;   // be const
        Order* assign_nxt;
        Order* assign_pre;

};
size_t Order::en_num = 0;
class BusInfo
{
    public:
        BusInfo() {}
        vector<BusInfo*> connectBus;
        size_t bus_size;
        size_t bus_id;
        size_t remain_bus;
        bool isConnect() { return !connectBus.empty();}
        bool isFull() { return (remain_bus == 0); }
};
// from big to small
bool cmpSupport(pair<size_t, Port>& a, pair<size_t, Port>& b) {
    return a.second.nofSupport() > b.second.nofSupport();
}
class OutPortMgr
{
    public:
        OutPortMgr(vector<Port>& _fptr, vector<Port>& _gptr) {
            fptr = &_fptr;
            gptr = &_gptr;
            is_one_to_one = (_fptr.size() == _gptr.size());
            order_map = vector<vector<Order> > ();
            assign_head = new Order();
            assign_current = assign_head;
            is_backtrack = false;

            // cout << "Mgr2" << endl;
            for (size_t i = 0; i < _fptr.size(); ++i) {
                vector<Order> buffer;
                for (size_t j = 0; j < _gptr.size(); ++j) {
                    Order ord(&_fptr[i], i, &_gptr[j], j);
                    buffer.push_back(ord);
                }
                order_map.push_back(buffer);
            }
            // cout << "Mgr1" << endl;
            genHeuristicOrder();
            // cout << "Mgr0" << endl;
            genBusInfo();
        }
    

        Order* step() {
            size_t pre_id = assign_current->getId();
            assign_current = assign_current->step();
            // cout << "!" << endl;
            size_t now_id = assign_current != 0 ? assign_current->getId() : 0;
            is_backtrack = pre_id > now_id;
            if (!is_backtrack) {
                assert(now_id != 0);
                noRemapRule();
            }
            return assign_current;
        }
        Order* backTrack() {
            is_backtrack = true;
            assign_current = assign_current->backTrack();
            return assign_current;
            // todo
        }
        Order* getHead() { return assign_head; }
        Order* getAssign() { return assign_current; }
        bool isBacktrack() { return is_backtrack; }
        vector<Order*> getAllAssign() const {
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
            for (auto& vec: order_map) {
                for (auto& ord: vec) {
                    if (ord.isAssign()) cout << "O ";
                    else if (ord.isForbid()) cout << "X ";
                    else cout << "* ";
                }
                cout << endl;
            }
        }

    private:
        bool is_one_to_one;
        vector<Port>* fptr;
        vector<Port>* gptr;

        vector<BusInfo> fbus;
        vector<BusInfo> gbus;

        vector<vector<Order> > order_map;
        Order* assign_head;
        Order* assign_current;
        bool is_backtrack;

        void genHeuristicOrder() {

            vector<pair<size_t, Port> > f_sort;
            vector<pair<size_t, Port> > g_sort;
            for (size_t i = 0; i < fptr->size(); ++i) {
                f_sort.push_back(pair<size_t, Port> (i, fptr->at(i)));
            }
            for (size_t i = 0; i < gptr->size(); ++i) {
                g_sort.push_back(pair<size_t, Port> (i, gptr->at(i)));
            }
            
            sort(f_sort.begin(), f_sort.end(), cmpSupport);
            sort(g_sort.begin(), g_sort.end(), cmpSupport);

            // for (auto f: f_sort) {
            //     cout << f.first << "--";
            //     cout << f.second.nofSupport() << endl;
            // }
            // for (auto g: g_sort) {
            //     cout << g.first << "--";
            //     cout << g.second.nofSupport() << endl;
            // }
            // cout << "gen4" << endl;
            vector<vector<Order*> > order_sort;
            if (is_one_to_one) {
                assert(f_sort[0].second.nofSupport() < g_sort[0].second.nofSupport());
                size_t cut = 0;
                for (size_t i = 1; i < f_sort.size(); ++i) {
                    assert(f_sort[i].second.nofSupport() < g_sort[i].second.nofSupport());    // if fail, means not one to one
                    // cout << "gen3 " << i << endl;
                    if (f_sort[i - 1].second.nofSupport() > g_sort[i].second.nofSupport()) {
                        for (size_t i_g = cut; i_g < i; ++i_g) {
                            for (size_t i_f = cut; i_f < i; ++i_f) {
                                pair<size_t, Port> fp = f_sort[i_f];
                                pair<size_t, Port> gp = g_sort[i_g];
                                groupMapping(fp, gp, order_sort);
                            }
                        }
                        cut = i;
                    }
                }
                // cout << "gen2" << endl;
                // cout << cut << endl;
                assert(f_sort[f_sort.size()].second.nofSupport() < g_sort[f_sort.size()].second.nofSupport());
                for (size_t i_g = cut; i_g < g_sort.size(); ++i_g) {
                    for (size_t i_f = cut; i_f < f_sort.size(); ++i_f) {
                        pair<size_t, Port> fp = f_sort[i_f];
                        pair<size_t, Port> gp = g_sort[i_g];
                        groupMapping(fp, gp, order_sort);
                    }
                }

                // for (auto grp: order_sort) {
                //     for (auto ord: grp) {
                //         ord->printMapping();
                //     }
                //     cout << "____" << endl;
                // }

            } else {
                cerr << "not done yet" << endl;
                assert(false);
            }
            // cout << "gen1" << endl;

            // assign_head = new Order();
            Order* pre = 0;
            Order* nxt = assign_head;
            for (auto& group: order_sort) {
                for (auto& ord_ptr: group) {
                    // if (assign_head == 0) assign_head = ord_ptr;
                    pre = nxt;
                    nxt = ord_ptr;
                    if (pre != 0) pre->enable(nxt);
                }
            }
            assign_head->assign(0);
            nxt->enable(0); //tail
            // cout << "gen0" << endl;

        }
        void groupMapping(pair<size_t, Port>& fp, pair<size_t, Port>& gp, vector<vector<Order*> >& order_sort) {
            Order* buf_order_ptr = &order_map[fp.first][gp.first];
            if (gp.second.nofSupport() < fp.second.nofSupport()) return;
            size_t group = gp.second.nofSupport() - fp.second.nofSupport();
            // cout << group << endl;
            group *= 2;
            if (gp.second.getBusSize() != fp.second.getBusSize()) ++group;
            while (order_sort.size() <= group) order_sort.push_back(vector<Order*> ());
            order_sort[group].push_back(buf_order_ptr);
        }
        void genBusInfo() {
            // todo
        }
        void noRemapRule() {
            size_t gid = assign_current->getGid();
            size_t fid = assign_current->getFid();

            // g->f1 no g->f2
            for (size_t i = 0; i < fptr->size(); ++i) {
                if (i == fid) continue;
                else {
                    order_map[i][gid].updateForbidReason(assign_current);
                }
            }
            if (is_one_to_one) {
                // f->g1 no f->g2
                for (size_t i = 0; i < gptr->size(); ++i) {
                    if (i == gid) continue;
                    else {
                        order_map[fid][i].updateForbidReason(assign_current);
                    }
                }
            }
        }
};


struct mtx2Mit {
        Var matrixVar;
        Var miterVar;
};

// Global variables

// SAT Solver
SatSolver matrixSolver, miterSolver;

// Circuit 1
vector<Port> x;
vector<Port> f;

// Circuit 2
vector<Port> y;
vector<Port> g;
vector<Var>  fStar;

// I/O Matrix
vector<vector<mtx2Mit> > a, b, c, d;


void testOutputMgr() {  // pushPort
    // cout << "b" << endl;
    for (int i = 0; i < 3; ++i) {
        x.push_back(Port("x" + to_string(i), miterSolver.newVar()));
    }
    for (int i = 0; i < 3; ++i) {
        f.push_back(Port("f" + to_string(i), miterSolver.newVar()));
    }
    for (int i = 0; i < 4; ++i) {
        y.push_back(Port("y" + to_string(i), miterSolver.newVar()));
    }
    for (int i = 0; i < 3; ++i) {
        g.push_back(Port("g" + to_string(i), miterSolver.newVar()));
    }
    // cout << "a" << endl;
    f[0].addSupport(vector<int> {0,1,2});
    f[1].addSupport(vector<int> {0,1});
    f[2].addSupport(vector<int> {0,1,2});
    //f[3].addSupport(vector<int> {1});
    g[0].addSupport(vector<int> {0,2,3});
    g[1].addSupport(vector<int> {0,1,2,3});
    g[2].addSupport(vector<int> {1,3});
    // g[3].addSupport(vector<int> {0,3});

    // cout << "t0" << endl;
    OutPortMgr o_mgr(f, g);
    // cout << "t1" << endl;
    Order* cur = o_mgr.getAssign();
    // cout << "t2" << endl;
    o_mgr.step();
    o_mgr.printAssign();
    o_mgr.step();
    o_mgr.printAssign();
    o_mgr.backTrack();
    o_mgr.printAssign();
    o_mgr.step();
    o_mgr.printAssign();
    o_mgr.step();
    o_mgr.printAssign();
    o_mgr.step();
    o_mgr.printAssign();
    o_mgr.backTrack();
    o_mgr.printAssign();
    o_mgr.step();
    o_mgr.printAssign();
    o_mgr.step();
    o_mgr.printAssign();
    o_mgr.backTrack();
    o_mgr.printAssign();
    o_mgr.step();
    o_mgr.printAssign();
    // cout << cur << endl;
    // o_mgr.printAssign();
    // while (cur != 0) {
    //     // cur->printMapping();
    //     // cout << (o_mgr.isBacktrack() ? "T" : "F") << endl;
    //     vector<Order*> assignment = o_mgr.getAllAssign();
    //     for (auto assign: assignment) {
    //         assign->printMapping();
    //     }
    //     cout << "____" << endl;
    //     o_mgr.printAssign();
    //     cout << "____" << endl;
    //     cur = o_mgr.step();
    //     // cout << "____" << endl;
    //     // cur->printLink();
    // }

}


////////////////////////////////////
//main
////////////////////////////////////

int main(int argc, char* argv[]) {
    
    matrixSolver.initialize();
    matrixSolver.assumeRelease();
    miterSolver.initialize();
    miterSolver.assumeRelease();
    testOutputMgr();
}
