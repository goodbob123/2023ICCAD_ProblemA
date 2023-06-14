/****************************************************************************
  FileName     [ sat.h ]
  PackageName  [ sat ]
  Synopsis     [ Define miniSat solver interface functions ]
  Author       [ Chung-Yang (Ric) Huang, Cheng-Yin Wu ]
  Copyright    [ Copyleft(c) 2010-present LaDs(III), GIEE, NTU, Taiwan ]
****************************************************************************/

#ifndef SAT_H
#define SAT_H

#include "Solver.h"
#include <cassert>
#include <iostream>
#include <vector>

using namespace std;

/********** MiniSAT_Solver **********/
class SatSolver {
public:
  SatSolver() : _solver(0) {}
  ~SatSolver() {
    if (_solver)
      delete _solver;
  }

  // Solver initialization and reset
  void initialize() {
    reset();
    if (_curVar == 0) {
      _solver->newVar();
      ++_curVar;
    }
  }
  void reset() {
    if (_solver)
      delete _solver;
    _solver = new Solver();
    _assump.clear();
    _curVar = 0;
  }

  // Constructing proof model
  // Return the Var ID of the new Var
  inline Var newVar() {
    _solver->newVar();
    return _curVar++;
  }
  // fa/fb = true if it is inverted
  void addAigCNF(Var vf, Var va, bool fa, Var vb, bool fb) {
    vec<Lit> lits;
    Lit lf = Lit(vf);
    Lit la = fa ? ~Lit(va) : Lit(va);
    Lit lb = fb ? ~Lit(vb) : Lit(vb);
    lits.push(la);
    lits.push(~lf);
    _solver->addClause(lits);
    lits.clear();
    lits.push(lb);
    lits.push(~lf);
    _solver->addClause(lits);
    lits.clear();
    lits.push(~la);
    lits.push(~lb);
    lits.push(lf);
    _solver->addClause(lits);
    lits.clear();
  }
  // fa/fb = true if it is inverted
  void addXorCNF(Var vf, Var va, bool fa, Var vb, bool fb) {
    vec<Lit> lits;
    Lit lf = Lit(vf);
    Lit la = fa ? ~Lit(va) : Lit(va);
    Lit lb = fb ? ~Lit(vb) : Lit(vb);
    lits.push(~la);
    lits.push(lb);
    lits.push(lf);
    _solver->addClause(lits);
    lits.clear();
    lits.push(la);
    lits.push(~lb);
    lits.push(lf);
    _solver->addClause(lits);
    lits.clear();
    lits.push(la);
    lits.push(lb);
    lits.push(~lf);
    _solver->addClause(lits);
    lits.clear();
    lits.push(~la);
    lits.push(~lb);
    lits.push(~lf);
    _solver->addClause(lits);
    lits.clear();
  }
  void addCNF(vector<Lit> lits) { // Wish
    vec<Lit> _lits(lits.size());
    for (int i = 0; i < lits.size(); ++i) {
      _lits[i] = lits[i];
    }
    _solver->addClause(_lits);
  }

  void addOR(Lit f, vector<Lit> lits) { // Wish
    // f = OR(for lit in lits)
    // A <-> B + C + D + E +...+ => (¬B ∨ A) ∧ (¬C ∨ A) ∧ (¬D ∨ A) ∧ (¬E ∨ A) ∧
    // (¬A ∨ B ∨ C ∨ D ∨ E)
    vector<Lit> outerLits;
    outerLits.push_back(~f);
    for (int i = 0; i < lits.size(); ++i) {
      outerLits.push_back(lits[i]);
      vector<Lit> innerLits;
      innerLits.push_back(f);
      innerLits.push_back(~lits[i]);
      addCNF(innerLits);
    }
    addCNF(outerLits);
  }

  // commander encoding
  // ref:
  // http://www.cs.cmu.edu/~wklieber/papers/2007_efficient-cnf-encoding-for-selecting-1.pdf
  void add_one_hot_constraint(const vector<Lit> &v) {
    vector<Lit> commander_lits = vector<Lit>(v.begin(), v.end());
    vector<Lit> new_commander_lits = vector<Lit>();
    vector<Lit> clause = vector<Lit>();

    while (commander_lits.size() > 1) {
      for (int i = 0; i < commander_lits.size(); i += 3) {
        if (commander_lits.size() - i == 1) {
          new_commander_lits.push_back(commander_lits[i]);
        } else if (commander_lits.size() - i == 2) {
          Var new_commander = newVar();
          Lit new_commander_lit = Lit(new_commander);
          new_commander_lits.push_back(new_commander_lit);

          clause.clear();
          clause.push_back(~commander_lits[i]);
          clause.push_back(~commander_lits[i + 1]);
          addCNF(clause);

          clause.clear();
          clause.push_back(~new_commander_lit);
          clause.push_back(commander_lits[i]);
          clause.push_back(commander_lits[i + 1]);
          addCNF(clause);

          clause.clear();
          clause.push_back(new_commander_lit);
          clause.push_back(~commander_lits[i]);
          addCNF(clause);
          clause.clear();
          clause.push_back(new_commander_lit);
          clause.push_back(~commander_lits[i + 1]);
          addCNF(clause);
        } else {
          Var new_commander = newVar();
          Lit new_commander_lit = Lit(new_commander);
          new_commander_lits.push_back(new_commander_lit);

          clause.clear();
          clause.push_back(~commander_lits[i]);
          clause.push_back(~commander_lits[i + 1]);
          addCNF(clause);
          clause.clear();
          clause.push_back(~commander_lits[i]);
          clause.push_back(~commander_lits[i + 2]);
          addCNF(clause);
          clause.clear();
          clause.push_back(~commander_lits[i + 1]);
          clause.push_back(~commander_lits[i + 2]);
          addCNF(clause);

          clause.clear();
          clause.push_back(~new_commander_lit);
          clause.push_back(commander_lits[i]);
          clause.push_back(commander_lits[i + 1]);
          clause.push_back(commander_lits[i + 2]);
          addCNF(clause);

          clause.clear();
          clause.push_back(new_commander_lit);
          clause.push_back(~commander_lits[i]);
          addCNF(clause);
          clause.at(1) = ~commander_lits[i + 1];
          addCNF(clause);
          clause.at(1) = ~commander_lits[i + 2];
          addCNF(clause);
        }

        addCNF(clause);
      }

      // swap commander_lits and new_commander_lits
      commander_lits.clear();
      commander_lits.swap(new_commander_lits);
    }

    _solver->addUnit(commander_lits[0]);
  }

  // For incremental proof, use "assumeSolve()"
  void assumeRelease() { _assump.clear(); }
  void assumeProperty(Var prop, bool val) {
    _assump.push(val ? Lit(prop) : ~Lit(prop));
  }
  bool assumpSolve() { return _solver->solve(_assump); }

  // For one time proof, use "solve"
  void assertProperty(Var prop, bool val) {
    _solver->addUnit(val ? Lit(prop) : ~Lit(prop));
  }
  bool solve() {
    _solver->solve();
    return _solver->okay();
  }

  // Functions about Reporting
  // Return 1/0/-1; -1 means unknown value
  int getValue(Var v) const {
    return (_solver->modelValue(v) == l_True
                ? 1
                : (_solver->modelValue(v) == l_False ? 0 : -1));
  }
  void printStats() const { const_cast<Solver *>(_solver)->printStats(); }

private:
  Solver *_solver;  // Pointer to a Minisat solver
  Var _curVar;      // Variable currently
  vec<Lit> _assump; // Assumption List for assumption solve
};

#endif // SAT_H
