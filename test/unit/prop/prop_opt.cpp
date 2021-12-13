/******************************************************************************
 * Top contributors (to current version):
 *   Yancheng Ou
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Try to implement an optimization loop on top of propEngine.
 */

#include "base/check.h"
#include "context/context.h"
#include "expr/kind.h"
#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "prop/registrar.h"
#include "prop/sat_solver.h"
#include "prop/theory_proxy.h"
#include "smt/smt_solver.h"
#include "smt/assertions.h"
#include "smt/env.h"
#include "smt/preprocessor.h"
#include "smt/solver_engine.h"
#include "smt/solver_engine_state.h"
#include "smt/solver_engine_stats.h"
#include "test_smt.h"
#include "theory/arith/theory_arith.h"
#include "theory/booleans/theory_bool.h"
#include "theory/builtin/theory_builtin.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "util/rational.h"


namespace cvc5 {

using namespace context;
using namespace prop;
using namespace smt;
using namespace theory;

namespace test {


class TestPropOpt : public TestSmt
{
 protected:
  void SetUp() override 
  {
    TestSmt::SetUp();
    // d_theoryEngine = d_slvEngine->getTheoryEngine();
    // d_satSolver.reset(new FakeSatSolver());
    // d_cnfContext.reset(new context::Context());
    // d_cnfRegistrar.reset(new prop::NullRegistrar);
    // d_cnfStream.reset(
    //     new cvc5::prop::CnfStream(d_satSolver.get(),
    //                               d_cnfRegistrar.get(),
    //                               d_cnfContext.get(),
    //                               &d_slvEngine->getEnv(),
    //                               d_slvEngine->getResourceManager()));
  }

  void TearDown() override
  {
    // d_cnfStream.reset(nullptr);
    // d_cnfRegistrar.reset(nullptr);
    // d_cnfContext.reset(nullptr);
    // d_satSolver.reset(nullptr);
    TestSmt::TearDown();
  }

  // /** The SAT solver proxy */
  // std::unique_ptr<FakeSatSolver> d_satSolver;
  // /** The theory engine */
  // TheoryEngine* d_theoryEngine;
  // /** The CNF converter in use */
  // std::unique_ptr<CnfStream> d_cnfStream;
  // /** The context of the CnfStream. */
  // std::unique_ptr<Context> d_cnfContext;
  // /** The registrar used by the CnfStream. */
  // std::unique_ptr<prop::NullRegistrar> d_cnfRegistrar;

};


TEST_F(TestPropOpt, test1)
{
  d_slvEngine->setOption("produce-models", "true");
  d_slvEngine->setOption("incremental", "true");
  d_slvEngine->setOption("produce-assertions", "true");
  Node a = d_nodeManager->mkVar(d_nodeManager->realType());
  Node b = d_nodeManager->mkVar(d_nodeManager->realType());
  Node c = d_nodeManager->mkVar(d_nodeManager->realType());
  Node d = d_nodeManager->mkNode(kind::PLUS, a, b);
  Node eqv = d_nodeManager->mkVar(d_nodeManager->realType());
  Node eq = d_nodeManager->mkNode(kind::EQUAL, eqv, d);
  Node gt = d_nodeManager->mkNode(kind::GT, c, d);
  // Node lt = d_nodeManager->mkNode(kind::LT, a, c);
  // Node ge = d_nodeManager->mkNode(kind::GEQ, c, d);
  // Node le = d_nodeManager->mkNode(kind::LEQ, a, c);
  Node m1 = d_nodeManager->mkConst<Rational>(kind::CONST_RATIONAL, Rational(-1));
  Node zero = d_nodeManager->mkConst<Rational>(kind::CONST_RATIONAL, Rational(0));
  d_slvEngine->assertFormula(gt);
  // d_slvEngine->assertFormula(lt);
  // d_slvEngine->assertFormula(ge);
  // d_slvEngine->assertFormula(le);
  d_slvEngine->assertFormula(eq);


  PropEngine *prop = d_slvEngine->getPropEngine();
  TheoryEngine *theory = d_slvEngine->getTheoryEngine();
  SmtSolver *solver = d_slvEngine->d_smtSolver.get();
  Assertions *as = d_slvEngine->d_asserts.get();

  CnfStream *cnfs = prop->d_cnfStream;

  CDCLTSatSolverInterface *sats = prop->d_satSolver;

  {
    SolverEngineScope scope(d_slvEngine.get());
    d_slvEngine->finishInit();
    solver->d_state.notifyCheckSat(false);

    as->initializeCheckSat({}, false);
    solver->processAssertions(*as);

    Result r;

    prop->d_inCheckSat = true;

    prop->d_theoryProxy->presolve();

    SatValue result;

    std::vector<SatLiteral> assumptions_vec;

    

    result = sats->solve({});
    std::cout << result << std::endl;

    std::cout << "Nodes begin:" << std::endl;
    for (auto it = cnfs->d_nodeToLiteralMap.begin(); it != cnfs->d_nodeToLiteralMap.end(); ++it) {
      std::cout << it->first << std::endl;
    }
    std::cout << "Nodes end." << std::endl;

    Node pivot = d_nodeManager->mkConst<Rational>(kind::CONST_RATIONAL, Rational(-2));
    // Node piv2 = d_nodeManager->mkNode(kind::PLUS, 
    //   d_nodeManager->mkNode(kind::MULT, m1, c), 
    //   pivot);
    Node inc = d_nodeManager->mkNode(kind::GEQ, 
      d_nodeManager->mkNode(kind::MULT, m1, c), 
      // d_nodeManager->mkNode(kind::MULT, m1, pivot)
      pivot
    );
    std::cout << "inc: " << inc << std::endl;
    // as->assertFormula(inc);
    // as->initializeCheckSat({}, false);
    // prop->d_inCheckSat = false;
    // solver->processAssertions(*as);
    // prop->d_inCheckSat = true;
    cnfs->ensureLiteral(inc);

    std::cout << "Nodes begin:" << std::endl;
    for (auto it = cnfs->d_nodeToLiteralMap.begin(); it != cnfs->d_nodeToLiteralMap.end(); ++it) {
      std::cout << it->first << std::endl;
    }
    std::cout << "Nodes end." << std::endl;

    // ASSERT_TRUE(false);  // quick termination
    prop::SatClause clause = {cnfs->getLiteral(inc)};
    result = sats->solve(clause);
    std::cout << result << std::endl;

    Node pivot2 = d_nodeManager->mkConst<Rational>(kind::CONST_RATIONAL, Rational(-1));
    Node inc2 = d_nodeManager->mkNode(kind::GEQ, 
      d_nodeManager->mkNode(kind::MULT, m1, c), 
      pivot2
    );
    cnfs->ensureLiteral(inc2);
    clause.push_back(cnfs->getLiteral(inc2));
    // sats->addClause(clause, true);  // decisionLevel != 0

    result = sats->solve(clause);
    std::cout << result << std::endl;

    prop->d_inCheckSat = false;


    

    // solver->d_state.notifyCheckSatResult(false, r);
  }

  // std::cout << d_slvEngine->getModel({}, {}) << std::endl;
  // std::cout << d_slvEngine->getValue(a) << std::endl;
  // std::cout << d_slvEngine->getValue(b) << std::endl;
  // std::cout << d_slvEngine->getValue(c) << std::endl;
  // std::cout << d_slvEngine->getValue(d) << std::endl;
}


}
}