/****************************************************************************
  FileName     [ sat.h ]
  PackageName  [ sat ]
  Synopsis     [ Define miniSat solver interface functions ]
  Author       [ Chung-Yang (Ric) Huang, Cheng-Yin Wu ]
  Copyright    [ Copyleft(c) 2010-present LaDs(III), GIEE, NTU, Taiwan ]
****************************************************************************/

#ifndef SAT_H
#define SAT_H

#include "VarLit.h"
#include <vector>



// define Lit and utility function

extern "C" {
  #include "application.h"
  #include "cover.h"
  #include "handle.h"
  #include "kissat.h"
  #include "print.h"
  #include "random.h"
  #include "error.h"
  // void kissat_release(kissat*);
  // kissat* kissat_init();
  // void kissat_add(kissat *solver, int elit);

  // int kissat_solve(kissat *solver);
  int kissat_assign_assumption(kissat *solver);
  int kissat_propagate_assumptions(kissat *solver);
  void kissat_reset_assumptions(kissat *solver);
  // void kissat_assume(kissat *solver, int elit);
}

class SatSolver {
public:
  SatSolver() : _solver(0) {}

  ~SatSolver() {
    if (_solver) {
      kissat_release(_solver);
    }
  }

  void initialize() {
    reset();
  }

  void reset() {
    if (_solver)
      kissat_release(_solver);
    _solver = kissat_init();
    // std::cout << "hehehe" << kissat_set_option(_solver, "-verbose", -1) << std::endl;
    _assump.clear();
    _curVar = 0;
  }

  Var newVar() {
    return ++_curVar;
  }

  bool solve() {
    return kissat_solve(_solver) == 10;
  }

  bool assumpSolve() {
    return kissat_solve(_solver) == 10;
    if (_assump.empty())
      return kissat_solve(_solver) == 10;
    // int result = kissat_assign_assumption(_solver);
    int result = kissat_propagate_assumptions(_solver);
    return result == 10;
  }

  int getValue(Var v) const {
    // dump(_solver);
    // assert(v < _solver->vars)
    return kissat_value(_solver, v) > 0;

  }

  void assumeProperty(Var prop, bool val) {
    _assump.push_back(val ? Lit(prop) : ~Lit(prop));
    kissat_assume(_solver, toInt(_assump.back()));
  }
  
  void assumeRelease() { 
    _assump.clear(); 
    kissat_reset_assumptions(_solver);
  }

  void assertProperty(Var prop, bool val) {
    addCNF({val ? Lit(prop) : ~Lit(prop)});
  }

  void addCNF(std::vector<Lit> lits) {
    for (int i = 0; i < lits.size(); ++i) {
      kissat_add(_solver, toInt(lits[i]));
    }
    kissat_add(_solver, 0);
  }

  void addAigCNF(Var vf, Var va, bool fa, Var vb, bool fb) {
    Lit lf = Lit(vf);
    Lit la = fa ? ~Lit(va) : Lit(va);
    Lit lb = fb ? ~Lit(vb) : Lit(vb);
    addCNF({~lf, la});
    addCNF({~lf, lb});
    addCNF({~la, ~lb, lf});
  }

  void addXorCNF(Var vf, Var va, bool fa, Var vb, bool fb) {
    Lit lf = Lit(vf);
    Lit la = fa ? ~Lit(va) : Lit(va);
    Lit lb = fb ? ~Lit(vb) : Lit(vb);
    addCNF({~la, lb, lf});
    addCNF({la, ~lb, lf});
    addCNF({la, lb, ~lf});
    addCNF({~la, ~lb, ~lf});
  }

  void addOR(Lit f, std::vector<Lit> lits) {
    // f = OR(for lit in lits)
    // A <-> B + C + D + E +...+ => (¬B ∨ A) ∧ (¬C ∨ A) ∧ (¬D ∨ A) ∧ (¬E ∨ A) ∧
    // (¬A ∨ B ∨ C ∨ D ∨ E)
    std::vector<Lit> outerLits;
    outerLits.push_back(~f);
    for (int i = 0; i < lits.size(); ++i) {
      outerLits.push_back(lits[i]);
      std::vector<Lit> innerLits;
      innerLits.push_back(f);
      innerLits.push_back(~lits[i]);
      addCNF(innerLits);
    }
    addCNF(outerLits);
  }

  // commander encoding
  // ref:
  // http://www.cs.cmu.edu/~wklieber/papers/2007_efficient-cnf-encoding-for-selecting-1.pdf
  void addOneHot(const std::vector<Lit> &v) {
    std::vector<Lit> commander_lits = std::vector<Lit>(v.begin(), v.end());
    std::vector<Lit> new_commander_lits = std::vector<Lit>();
    std::vector<Lit> clause = std::vector<Lit>();

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
          clause[1] = ~commander_lits[i + 1];
          addCNF(clause);
          clause[1] = ~commander_lits[i + 2];
          addCNF(clause);
        }

        addCNF(clause);
      }

      // swap commander_lits and new_commander_lits
      commander_lits.clear();
      commander_lits.swap(new_commander_lits);
    }
    addCNF({commander_lits[0]});
  }

    // ref: https://people.eng.unimelb.edu.au/pstuckey/mddenc/mddenc.pdf
  void addGte(std::vector<Lit> lits, int n) {
    assert(lits.size() >= n);

    std::vector<std::vector<Var>> BDD = std::vector<std::vector<Var>>(lits.size(), std::vector<Var>(n));

    Var trueNode = newVar();
    Var falseNode = newVar();

    auto inRange = [&](int i, int j) {
      return j >= std::max(i + n - int(lits.size()), 0) &&
             j < std::min(i + 1, n);
    };

    for (int i = 0; i < lits.size(); ++i) {
      for (int j = std::max(i + n - int(lits.size()), 0);
           j < std::min(i + 1, n); ++j) {
        BDD[i][j] = newVar();
      }
    }

    std::vector<Lit> clause;
    for (int i = 0; i < lits.size(); ++i) {
      for (int j = std::max(i + n - int(lits.size()), 0);
           j < std::min(i + 1, n); ++j) {
        Lit x = lits[i];
        Lit t = !inRange(i + 1, j + 1) ? Lit(trueNode) : Lit(BDD[i + 1][j + 1]);
        Lit f = !inRange(i + 1, j) ? Lit(falseNode) : Lit(BDD[i + 1][j]);
        Lit v = Lit(BDD[i][j]);

        clause.clear();
        clause.push_back(~t);
        clause.push_back(~x);
        clause.push_back(v);
        addCNF(clause);

        clause.clear();
        clause.push_back(t);
        clause.push_back(~x);
        clause.push_back(~v);
        addCNF(clause);

        clause.clear();
        clause.push_back(~f);
        clause.push_back(x);
        clause.push_back(v);
        addCNF(clause);

        clause.clear();
        clause.push_back(f);
        clause.push_back(x);
        clause.push_back(~v);
        addCNF(clause);

        clause.clear();
        clause.push_back(~t);
        clause.push_back(~f);
        clause.push_back(v);
        addCNF(clause);

        clause.clear();
        clause.push_back(t);
        clause.push_back(f);
        clause.push_back(~v);
        addCNF(clause);
      }
    }

    addCNF({Lit(trueNode)});
    addCNF({~Lit(falseNode)});
    addCNF({Lit(BDD[0][0])});
  }

private:
  kissat* _solver;
  std::vector<Lit> _assump;
  Var _curVar;
};

#endif // SAT_H
