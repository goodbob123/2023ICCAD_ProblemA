/****************************************************************************
  FileName     [ cirGate.cpp ]
  PackageName  [ cir ]
  Synopsis     [ Define class CirAigGate member functions ]
  Author       [ Chung-Yang (Ric) Huang ]
  Copyright    [ Copyleft(c) 2008-present LaDs(III), GIEE, NTU, Taiwan ]
****************************************************************************/

#include "cirGate.h"

#include <stdarg.h>

#include <cassert>
#include <iomanip>
#include <iostream>
#include <sstream>

#include "cirMgr.h"
// #include "util.h"

using namespace std;

// extern CirMgr *cirMgr;

// TODO: Implement memeber functions for class(es) in cirGate.h

/**************************************/
/*   class CirGate member functions   */
/**************************************/
// void CirGate::reportGate() const {
//     ifstream fin;
//     fin.open(cirMgr->getFilename());
//     if (!fin) {
//         cout << "can not open file" << endl;
//         return;
//     }
//     char buffer[40];
//     string token;
//     string str = buffer;
//     // useless
//     fin.getline(buffer, sizeof(buffer));
//     int line = 1;
//     // should skip line of IO
//     if (type == AIG_GATE) {
//         for (int i = 0; i < cirMgr->getIOsize(); ++i) {
//             fin.getline(buffer, sizeof(buffer));
//             ++line;
//         }
//     }

//     while (fin.getline(buffer, sizeof(buffer))) {
//         ++line;
//         str = buffer;
//         myStrGetTok(str, token);
//         if (id == stoi(token) / 2) {
//             stringstream ss;
//             if ((type == PI_GATE || type == PO_GATE) && cirMgr->getIOName(this) != "") {
//                 ss << " " << getTypeName() << "(" << id << ")\"" << cirMgr->getIOName(this) << "\", line " << line;
//             } else
//                 ss << " " << getTypeName() << "(" << id << "), line " << line;
//             cout << "==================================================" << endl;
//             cout << "=" << left << setw(48) << ss.str() << "=" << endl;
//             cout << "==================================================" << endl;
//             fin.close();
//             return;
//         }
//     }
//     fin.close();
// }

void CirGate::reportFanin(int level) const {
    assert(level >= 0);
    string space;
    vector<bool> markList(cirMgr->getAllsize(), false);
    doReportFanin(level, space, false, markList);
}

void CirGate::doReportFanin(int level, string space, bool cp, vector<bool>& markList) const {
    if (level >= 0) {
        if (cp)
            cout << space << "!" << getTypeName() << " " << id;
        else
            cout << space << getTypeName() << " " << id;
        if (markList[this->id] && level != 0) {
            cout << " (*)" << endl;
            return;
        }
        cout << endl;
        space = "  " + space;
        if (fanin0id != -1 && !markList[id]) {
            if (cirMgr->getGate(fanin0id) != 0)
                cirMgr->getGate(fanin0id)->doReportFanin(level - 1, space, this->fanin0cp, markList);
            // for UNDEF
            else {
                cout << space;
                if (fanin0cp)
                    cout << "!";
                cout << "UNDEF"
                     << " " << fanin0id << endl;
            }
        }
        if (fanin1id != -1 && !markList[id]) {
            if (level != 0)
                markList[id] = true;
            if (cirMgr->getGate(fanin1id) != 0)
                cirMgr->getGate(fanin1id)->doReportFanin(level - 1, space, this->fanin1cp, markList);
            // for UNDEF
            else {
                cout << space;
                if (fanin0cp)
                    cout << "!";
                cout << "UNDEF"
                     << " " << fanin1id << endl;
            }
        }
    }
}

void CirGate::reportFanout(int level) const {
    assert(level >= 0);
    string space;
    vector<bool> markList(cirMgr->getAllsize(), false);
    doReportFanout(level, space, false, markList);
}

void CirGate::doReportFanout(int level, string space, bool cp, vector<bool>& markList) const {
    if (level >= 0) {
        // print self
        if (cp)
            cout << space << "!" << getTypeName() << " " << id;
        else
            cout << space << getTypeName() << " " << id;
        if (markList[this->id] && level != 0) {
            cout << " (*)" << endl;
            return;
        }
        cout << endl;

        // print all fanout
        space = "  " + space;
        for (size_t i = 0; i < fanoutid.size(); ++i) {
            int id = fanoutid[i].first;
            bool cp = fanoutid[i].second;

            if (id != -1 && !markList[this->id]) {
                if (cirMgr->getGate(id) != 0)
                    cirMgr->getGate(id)->doReportFanout(level - 1, space, cp, markList);
                // for UNDEF
                else {
                    cout << space;
                    if (cp)
                        cout << "!";
                    cout << "UNDEF"
                         << " " << id << endl;
                }
            }
        }
        if (level != 0)
            markList[this->id] = true;
    }
}

void CirGate::printGate() const {
    switch (type) {
        case UNDEF_GATE:
            cout << left << setw(4) << "UNDEF " << id;
            cout << " ";
            if (!cirMgr->getGate(fanin0id)) cout << "*";
            if (fanin0cp == true) cout << "!";
            cout << fanin0id;
            cout << " ";
            if (!cirMgr->getGate(fanin1id) == 0) cout << "*";
            if (fanin1cp == true) cout << "!";
            cout << fanin1id;
            break;
        case PI_GATE:
            cout << left << setw(4) << "PI " << id;
            break;
        case PO_GATE:
            cout << left << setw(4) << "PO " << id;
            cout << " ";
            if (!cirMgr->getGate(fanin0id)) cout << "*";
            if (fanin0cp == true) cout << "!";
            cout << fanin0id;
            break;
        case AIG_GATE:
            cout << left << setw(4) << "AIG " << id;
            cout << " ";
            if (!cirMgr->getGate(fanin0id)) cout << "*";
            if (fanin0cp == true) cout << "!";
            cout << fanin0id;
            cout << " ";
            if (!cirMgr->getGate(fanin1id)) cout << "*";
            if (fanin1cp == true) cout << "!";
            cout << fanin1id;
            break;
        case CONST_GATE:
            cout << left << "CONST0";
            break;
        default:
            break;
    }
}

string CirGate::getTypeName() const {
    switch (type) {
        case UNDEF_GATE:
            return "UNDEF";
            break;
        case PI_GATE:
            return "PI";
            break;
        case PO_GATE:
            return "PO";
            break;
        case AIG_GATE:
            return "AIG";
            break;
        case CONST_GATE:
            return "CONST";
            break;
        default:
            return "NON";
            break;
    }
}