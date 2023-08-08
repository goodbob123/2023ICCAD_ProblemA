#include <time.h>

#include <algorithm>
#include <fstream>
#include <iostream>
#include <unordered_map>

#include "./SAT/test/sat.h"
//#include "./SAT/sat.h"
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
    int getCoverage() const { return coverage; }

    void addSupport(int index) { supports.insert(index); }
    size_t nofSupport() const { return supports.size(); }
    bool isSupport(int index) const { return supports.find(index) != supports.end(); }

   private:
    string name;
    Var var;
    set<int> supports;  // output support for input port, input support for output port
    int coverage;       // only for ontput (f,g)
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


class BusInfo
{
    public:
        BusInfo(size_t _id, set<int>& _bus, bool _glike) {
            bus_id = _id;
            busPort = &_bus;
            glike = _glike;
            remain_bus = _bus.size();
            connectBus = vector<BusInfo*> ();
        }
        size_t getId() {
            return bus_id;
        }
        size_t getBusSize() { return busPort->size(); }
        set<int> getBusPort() { return *busPort; }
        bool isGlike() {return glike; }
        bool isConnect() {
            if (glike) return !connectBus.empty();
            else return (remain_bus != busPort->size());
            // return !connectBus.empty();
        }
        bool isFull() { return (remain_bus == 0); }
        bool isMatched(BusInfo* b) {
            if (!b->isConnect() || !isConnect()) return false;
            for (size_t i = 0; i < connectBus.size(); ++i) {
                if (b == connectBus[i]) return true;
            }
            return false;
        }
        bool canMatch(BusInfo* b) {
            if (b->isConnect() && isConnect()) return false; // already connected -> can connect more
            else if (isConnect()) return remain_bus > b->busPort->size();
            else if (b->isConnect()) return b->remain_bus > busPort->size();
            else return true;
        }
        void connectTo(BusInfo* b) {
            cout << "connectBus" << endl;
            // if (!canMatch(b) && !isMatched(b)) {
            //     cout << "badconnection" << endl;
            //     assert(false);
            // }
            size_t numConnect = std::min(b->getBusSize(), getBusSize());
            // assert(b.remain_bus >= numConnect && remain_bus >= numConnect);
            // b.remain_bus -= numConnect;
            // b.connectBus.push_back(this);
            remain_bus -= numConnect;
            assert(remain_bus >= 0);
            if (!glike && remain_bus == 0) remain_bus = busPort->size(); 
            connectBus.push_back(b);
        }
        BusInfo* disconnectBack() {
            assert(connectBus.size() != 0);
            BusInfo* bptr = connectBus.back();
            // cout << "disconnectBus : " << bptr->bus_id << " " << bus_id << endl;
            // assert(bptr->connectBus.back() == this);
            size_t numConnect = std::min(bptr->getBusSize(), getBusSize());
            // bptr->remain_bus+=numConnect;
            // assert(bptr->remain_bus <= bptr->busPort->size());
            // bptr->connectBus.pop_back();
            if (!glike && remain_bus == busPort->size()) remain_bus = 0;
            remain_bus+=numConnect;
            assert(remain_bus <= busPort->size());
            // cout << "to popback" << endl;
            connectBus.pop_back();
            // cout << "suc popback" << endl;
            return bptr;
        }
    private:
        // size_t bus_size;
        size_t bus_id;  // 0 if not a bus, just a pin
        size_t remain_bus;
        vector<BusInfo*> connectBus;
        // vector<Port*> firstConnectPort;
        set<int>* busPort;
        bool glike;
};
class Order
{   // Order would record the information about the assignment of f->g and the assignment chain
    public:
        Order() {
            is_head = true;
        }
        Order(Port* _gport_ptr, size_t _gport_id, BusInfo* _gBus_ptr, Port* _fport_ptr, size_t _fport_id, BusInfo* _fBus_ptr) {
            is_head = false;
            fBus_ptr = _fBus_ptr;
            fport_ptr = _fport_ptr;
            fport_id = _fport_id;
            gBus_ptr = _gBus_ptr;
            gport_ptr = _gport_ptr;
            gport_id = _gport_id;

            is_assign = false;
            is_connect_bus = false;
            en = false;   // should only changed in OutPortMgr::genHeuristicOrder
            is_forbid = true;
            forbid_order = vector<Order*> ();

            order_nxt = 0;  // should only changed in OutPortMgr::genHeuristicOrder
            assign_nxt = 0;
            assign_pre = 0;

            grp = 0;
            // support_atri = fport_ptr->nofSupport() + gport_ptr->nofSupport();
            support_atri = gport_ptr->nofSupport();
            support_span_atri = gport_ptr->nofSupport() - fport_ptr->nofSupport();
            bus_atri = (fBus_ptr->getBusSize() == gBus_ptr->getBusSize());
            cone_span_atri = gport_ptr->getCoverage() - fport_ptr->getCoverage();
            if (cone_span_atri < 0) cone_span_atri = -cone_span_atri;
        }
        friend class Comparator;
        friend class OutPortMgr;
        bool isHead() const { return is_head; }
        bool isForbid() const {
            if (!en) assert(is_forbid);
            return is_forbid;
        }
        bool isNeg() const { return is_neg; }
        bool isPos() const { return is_pos; }
        size_t getId() const { return id; }
        size_t getFid() const { return fport_id; }
        size_t getGid() const { return gport_id; }
        Port* getFptr() const { return fport_ptr; }
        Port* getGptr() const { return gport_ptr; }
        Order* getAssignNxt() const { return assign_nxt; }
        bool isAssign() const { return is_assign; }
        bool isConnectBus() const { return is_connect_bus; }
        BusInfo* getFBusptr() const { return fBus_ptr; }
        BusInfo* getGBusptr() const { return gBus_ptr; }
        bool isSameGrp(size_t numConstraint) const { return (grp == numConstraint); }

        void sameGrp() { ++grp; }
        void enable(Order* _order_nxt) {
            // make the Order able to assign and unsign
            // _order_nxt record next Order in chain
            en = true;
            is_forbid = false;
            order_nxt = _order_nxt;
            ++en_count;
            id = en_count;
        }
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
            if (!is_head && !fBus_ptr->isMatched(gBus_ptr)) {
                is_connect_bus = true;
                fBus_ptr->connectTo(gBus_ptr);
                gBus_ptr->connectTo(fBus_ptr);
            }
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
                assert(assign_pre->en);
                pre->assign_nxt = order_nxt;
            }

            // unassign
            is_assign = false;
            assign_nxt = 0;
            assign_pre = 0;
            is_neg = true;
            is_pos = true;
            updateForbidOrder(0);   // clear forbid_order
            if (!is_head && is_connect_bus) {
                BusInfo* gBus_buf = fBus_ptr->disconnectBack();
                if (gBus_buf != gBus_ptr) cout << "wrong" << endl;
                BusInfo* fBus_buf = gBus_ptr->disconnectBack();
                if (fBus_buf != fBus_ptr) cout << "wrong" << endl;
                is_connect_bus = false;
            }

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
                    assert(!assign_nxt->is_assign);
                    assert(assign_nxt->en);
                    assign_nxt = assign_nxt->order_nxt;
                }
            }
            // i.e. assign_nxt is new assignment
            assert(!assign_nxt->is_assign);
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
    private:
        bool is_head;   // head is a pseudo node used as head of the Order chain
        Port* fport_ptr; // correspond Port in f
        size_t fport_id; // correspond index of port in f
        Port* gport_ptr;
        size_t gport_id;
        BusInfo* fBus_ptr;
        BusInfo* gBus_ptr;

        bool is_connect_bus;
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

        size_t grp;
        size_t support_atri;
        int support_span_atri;
        int cone_span_atri;
        bool bus_atri;
};

// from big to small
class Comparator {  
    // cmp num Support
    // since used in OutPortMgr, Port is stored as second of pair
    public:
        bool operator() (const Order* a, const Order* b) {
            assert(a->support_span_atri >= 0);
            assert(b->support_span_atri >= 0);
            if (a->support_atri == b->support_atri) {
                if (a->support_span_atri == b->support_span_atri) {
                    if (a->cone_span_atri == b->cone_span_atri) {
                        return a->bus_atri && !b->bus_atri; // Comparator() (a, a) should be false
                    } else return a->cone_span_atri < b->cone_span_atri;
                } else return a->support_span_atri < b->support_span_atri;
            } else return a->support_atri < b->support_atri;
        }
        bool operator() (set<int>& a, set<int>& b) {
            return a.size() < b.size();
        }
};
class ComparatorSupport {
    public:
        bool operator() (pair<size_t, Port>& a, pair<size_t, Port>& b) {
            return a.second.nofSupport() > b.second.nofSupport();
        }
};
class ComparatorBinate {
    public:
        bool operator() (pair<size_t, Port>& a, pair<size_t, Port>& b) {
            return false; // todo
            // return a.second.nofSupport() > b.second.nofSupport();
        }
};

typedef vector<set<int>> Buses;
class OutPortMgr
{
    public:
        OutPortMgr() {}
        friend class BMatchSolver;
        void init(vector<Port>& _f, vector<Port>& _g, Buses& _fBus, Buses& _gBus) {
            fptr = &_f;
            gptr = &_g;
            fBusptr = &_fBus;
            gBusptr = &_gBus;
            is_one_to_one = (_f.size() == _g.size());
            Buses fBusBuf = _fBus;
            Buses gBusBuf = _gBus;
            sort(fBusBuf.begin(), fBusBuf.end(), Comparator());
            sort(gBusBuf.begin(), gBusBuf.end(), Comparator());
            is_bus_one_to_one = fBusBuf.size() == gBusBuf.size();
            if (is_bus_one_to_one) {
                for (size_t i = 0; i < fBusBuf.size(); ++i) {
                    if (fBusBuf[i].size() != gBusBuf[i].size()) {
                        is_bus_one_to_one = false;
                        break;
                    }
                }
            }
            order_map = vector<vector<Order> > ();
            fbus_map = vector<BusInfo* > ();
            gbus_map = vector<BusInfo* > ();
            assign_head = new Order();
            assign_current = assign_head;
            is_backtrack = false;

            // cout << "Mgr2" << endl;
            genMaps();
            // cout << "Mgr1" << endl;
            genHeuristicOrder();    // i.e. gen possible order chain
            cout << "done outPortMgr init" << endl;
        }
        Order* step() {
            if (assign_current->isHead()) cout << "at head" << endl; 
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
                unsplitBusRule();
            }
            return assign_current;
        }
        Order* backTrack() {
            // backtrack
            if (assign_current->isHead()) cout << "at head" << endl;
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
        bool is_bus_one_to_one;
        vector<Port>* fptr; // copy of f
        vector<Port>* gptr; // copy of g
        Buses* fBusptr;
        Buses* gBusptr;

        // vector<BusInfo> fBus;
        // vector<BusInfo> gBus;

        vector<vector<Order> > order_map; // matrix of Order, same as format of c, d in bmatch
        vector<BusInfo* > fbus_map;
        vector<BusInfo* > gbus_map;
        Order* assign_head; // pseudo head of chain of possible assignment
        Order* assign_current;  // current end of assignment
        bool is_backtrack;  // whether previous step is backtracking
        // init
        void genMaps() {
            // todo

            vector<BusInfo*> f_businfo(fptr->size(), 0);
            vector<BusInfo*> g_businfo(gptr->size(), 0);
            // fbus_map.push_back(set<BusInfo*> ());
            // fbus_map.push_back(set<BusInfo*> ());
            // gbus_map.push_back(set<BusInfo*> ());
            // gbus_map.push_back(set<BusInfo*> ());

            for (size_t i = 0; i < fBusptr->size(); ++i) {
                set<int>& bus = fBusptr->at(i);
                BusInfo* bufptr = new BusInfo(i + 1, bus, is_bus_one_to_one);
                fbus_map.push_back(bufptr);
                for (set<int>::iterator itr = bus.begin(); itr != bus.end(); ++itr) {
                    f_businfo[*itr] = bufptr;
                }
            }
            for (size_t i = 0; i < f_businfo.size(); ++i) {
                if (f_businfo[i] == 0) {
                    // cout << "in f " << i << ": "; 
                    set<int>* bufbus = new set<int> ();
                    bufbus->insert(i);
                    BusInfo* bufptr = new BusInfo(0, *bufbus, is_bus_one_to_one);
                    fbus_map.push_back(bufptr);
                    f_businfo[i] = bufptr;
                    // cout << bufptr << endl;
                }
            }

            for (size_t i = 0; i < gBusptr->size(); ++i) {
                set<int>& bus = gBusptr->at(i);
                BusInfo* bufptr = new BusInfo(i + 1, bus, true);
                // while (gbus_map.size() <= bus.size()) gbus_map.push_back(set<BusInfo*> ());
                // gbus_map[bus.size()].insert(bufptr);
                gbus_map.push_back(bufptr);
                for (set<int>::iterator itr = bus.begin(); itr != bus.end(); ++itr) {
                    g_businfo[*itr] = bufptr;
                }
            }
            for (size_t i = 0; i < g_businfo.size(); ++i) {
                if (g_businfo[i] == 0) {
                    set<int>* bufbus = new set<int> ();
                    bufbus->insert(i);
                    BusInfo* bufptr = new BusInfo(0, *bufbus, true);
                    // gbus_map[1].insert(bufptr);
                    gbus_map.push_back(bufptr);
                    g_businfo[i] = bufptr;
                }
            }

            // for (size_t i = 0; i < f_businfo.size(); ++i) {
            //     cout << i << "---" << f_businfo[i] <<  " : ";
            //     for (auto port : f_businfo[i]->getBusPort()) {
            //         cout << port << " ";
            //     }
            //     cout << endl;
            // }
            // for (size_t i = 0; i < g_businfo.size(); ++i) {
            //     cout << i << "---" << g_businfo[i] <<  " : ";
            //     for (auto port : g_businfo[i]->getBusPort()) {
            //         cout << port << " ";
            //     }
            //     cout << endl;
            // }

            for (size_t i = 0; i < gptr->size(); ++i) {
                vector<Order> buffer;
                for (size_t j = 0; j < fptr->size(); ++j) {
                    Order ord(&gptr->at(i), i, g_businfo[i], &fptr->at(j), j, f_businfo[j]);
                    buffer.push_back(ord);
                }
                order_map.push_back(buffer);
            }
            // for (auto s: fbus_map) {
            //     for (auto busptr: s) {
            //         cout << busptr << " ";
            //     }
            //     cout << "--" << endl;
            // }
            // for (auto vec: order_map) {
            //     for (auto ord: vec) {
            //         cout << ord.getFid() << ":" << ord.getFBusptr() << " " <<  ord.getGid() << ":" << ord.getGBusptr() << endl;
            //     }
            // }
        }
        // init
        void genHeuristicOrder() {

            vector<pair<size_t, Port> > f_sort;
            vector<pair<size_t, Port> > g_sort;
            for (size_t i = 0; i < fptr->size(); ++i) {
                f_sort.push_back(pair<size_t, Port> (i, fptr->at(i)));
            }
            for (size_t i = 0; i < gptr->size(); ++i) {
                g_sort.push_back(pair<size_t, Port> (i, gptr->at(i)));
            }
            

            // for (auto f: f_sort) {
            //     cout << f.first << "--";
            //     cout << f.second.nofSupport() << endl;
            // }
            // for (auto g: g_sort) {
            //     cout << g.first << "--";
            //     cout << g.second.nofSupport() << endl;
            // }
            // cout << "gen4" << endl;

            vector<Order*> order_sort; // group of valid assignment
            Order* order_buf;

            if (is_one_to_one) {
                grouping();
            }

            // cout << "gen 0" <<endl;
            for (size_t i_g = 0; i_g < g_sort.size(); ++i_g) {
                for (size_t i_f = 0; i_f < f_sort.size(); ++i_f) {
                    pair<size_t, Port> fp = f_sort[i_f];
                    pair<size_t, Port> gp = g_sort[i_g];
                    order_buf = checkMapping(fp, gp);
                    if (order_buf) order_sort.push_back(order_buf);
                }
            }

            // cout << "gen1" << endl;

            // make the order chain
            sort(order_sort.begin(), order_sort.end(), Comparator());
            for (auto ord: order_sort) {
                ord->printMapping();
            }
            Order* pre = 0;
            Order* nxt = assign_head;
            for (size_t i = 0; i < order_sort.size(); ++i) {
                // cout << i << endl;
                Order*& ord_ptr = order_sort[i];
                pre = nxt;
                nxt = ord_ptr;
                if (pre != 0) pre->enable(nxt);
            }
            assign_head->assign(0); // pre of head make it 0
            nxt->enable(0); // nxt of tail make it 0
        }
        // init-genHeuristicOrder
        void grouping() {
            vector<pair<size_t, Port> > f_sort;
            vector<pair<size_t, Port> > g_sort;
            for (size_t i = 0; i < fptr->size(); ++i) {
                f_sort.push_back(pair<size_t, Port> (i, fptr->at(i)));
            }
            for (size_t i = 0; i < gptr->size(); ++i) {
                g_sort.push_back(pair<size_t, Port> (i, gptr->at(i)));
            }


            sort(f_sort.begin(), f_sort.end(), ComparatorSupport());
            sort(g_sort.begin(), g_sort.end(), ComparatorSupport());
            for (size_t i = 0; i < f_sort.size(); ++i) {
                assert(f_sort[i].second.nofSupport() <= g_sort[i].second.nofSupport()); // if fail, means not one to one
            }

            size_t cut = 0; // cut is the end of previous group
            for (size_t i = 1; i < f_sort.size(); ++i) {
                if (f_sort[i - 1].second.nofSupport() > g_sort[i].second.nofSupport()) {
                    // group found, between [cut, i)
                    for (size_t i_g = cut; i_g < i; ++i_g) {
                        for (size_t i_f = cut; i_f < i; ++i_f) {
                            size_t fid = f_sort[i_f].first;
                            size_t gid = g_sort[i_g].first;
                            order_map[gid][fid].sameGrp();
                        }
                    }
                    cut = i; // update cut
                }
            }
            // final group should added
            for (size_t i_g = cut; i_g < g_sort.size(); ++i_g) {
                for (size_t i_f = cut; i_f < f_sort.size(); ++i_f) {
                    size_t fid = f_sort[i_f].first;
                    size_t gid = g_sort[i_g].first;
                    order_map[gid][fid].sameGrp();
                }
            }
        }
        // init-genHeuristicOrder
        Order* checkMapping(pair<size_t, Port>& fp, pair<size_t, Port>& gp) {
            // Order* buf_order_ptr = &order_map[fp.first][gp.first];
            Order* buf_order_ptr = &order_map[gp.first][fp.first];
            size_t numConstraint = 1;

            // checking the mapping is valid
            if (gp.second.nofSupport() < fp.second.nofSupport()) return 0;    // support should be bigger
            if (is_bus_one_to_one && buf_order_ptr->getFBusptr()->getBusSize() != buf_order_ptr->getGBusptr()->getBusSize()) return 0; // bus should be same
            if (!buf_order_ptr->isSameGrp(numConstraint)) return 0;
            return buf_order_ptr;
        }
        // step
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
        void unsplitBusRule() {
            if (assign_current->isConnectBus()) {
                BusInfo* fbus_ptr = assign_current->getFBusptr();
                BusInfo* gbus_ptr = assign_current->getGBusptr();
                for (size_t i = 0; i < gbus_map.size(); ++i) {
                    if (is_bus_one_to_one) {
                        if (fbus_ptr->getBusSize() != gbus_map[i]->getBusSize()) continue;  // forbid by one to one already
                        if (gbus_map[i] == gbus_ptr) continue;
                        assert(!fbus_ptr->canMatch(gbus_ptr));
                        forbidByBus(fbus_ptr, gbus_map[i]);
                    }
                    else {
                        cout << "not done yet" << endl;
                        assert(false);
                        // todo
                    }
                }
                for (size_t i = 0; i < fbus_map.size(); ++i) {
                    if (is_bus_one_to_one) {
                        if (gbus_ptr->getBusSize() != fbus_map[i]->getBusSize()) continue;  // forbid by one to one already
                        if (fbus_map[i] == fbus_ptr) continue;
                        assert(!gbus_ptr->canMatch(fbus_ptr));
                        forbidByBus(fbus_map[i], gbus_ptr);
                    }
                    else {
                        cout << "not done yet" << endl;
                        assert(false);
                        // todo
                    }
                }
            }
        }
        // unsplitBusRule
        void forbidByBus(BusInfo* fbus, BusInfo* gbus) {
            set<int> fbusport = fbus->getBusPort();
            set<int> gbusport = gbus->getBusPort();
            for (set<int>::iterator fitr = fbusport.begin(); fitr != fbusport.end(); ++fitr) {
                for (set<int>::iterator gitr = gbusport.begin(); gitr != gbusport.end(); ++gitr) {
                    cout << "forbid " << *fitr << " " << *gitr<< endl;
                    assign_current->updateForbidOrder(&order_map[*gitr][*fitr]);
                }
            }
        }
};

struct mtx2Mit {
    Var matrixVar;
    Var miterVar;
};

class BMatchSolver {
   public:
    BMatchSolver(){};
    ~BMatchSolver(){};
    void init(ifstream& portMapping, ifstream& aag1, ifstream& aag2, char* match);
    void genFuncSupport(ifstream& in);
    void readBusInfo(ifstream &in, bool isCircuit1);
    void inputPreprocess();
    void outputPreprocess();
    void run();
    void outputAns();
    void printInfo() const;
    void printBus(const Buses& bus) const;
    void printSupport(const vector<Port>& portTarget, const vector<Port>& portInv) const;
    void busConstraint();
    void testOutputMgr();
    void simulate();
    void interactiveSolve();

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

    void initCircuit(ifstream& in1, ifstream& in2);
    void addEqualConstraint();
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
    CirMgr* c1;

    // Circuit 2
    vector<Port> y;
    vector<Port> g;
    vector<Var> fStar;
    CirMgr* c2;

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

    // file
    char* file_match;

    size_t matrixSolverInstance;
    size_t matrixSolverPeriodInstance;
    double previousTime;
};