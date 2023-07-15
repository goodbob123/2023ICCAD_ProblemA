#include <time.h>

#include <fstream>
#include <iostream>
#include <vector>

#include "../cir/cirMgr.h"

void addEqualConstraint(ifstream& in1, ifstream& in2);
void createEqualRelationByGroup(const vector<pair<CirGate*, bool>>& group_f,
                                const vector<pair<CirGate*, bool>>& group_g);