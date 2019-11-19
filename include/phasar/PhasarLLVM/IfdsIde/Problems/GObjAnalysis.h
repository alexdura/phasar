/******************************************************************************
 * Copyright (c) 2019 Alexandru Dura
 * All rights reserved. This program and the accompanying materials are made
 * available under the terms of LICENSE.txt.
 *
 * Contributors:
 *    Noric Couderc, Alexandru Dura, Claudio Mandrioli
 *****************************************************************************/

#ifndef PHASAR_PHASARLLVM_IFDSIDE_PROBLEMS_GOBJANALYSIS_H_
#define PHASAR_PHASARLLVM_IFDSIDE_PROBLEMS_GOBJANALYSIS_H_

#include <iosfwd>
#include <map>
#include <memory>
#include <phasar/PhasarLLVM/IfdsIde/LLVMDefaultIDETabulationProblem.h>
#include <phasar/PhasarLLVM/Utils/TaintConfiguration.h>
#include <phasar/PhasarLLVM/IfdsIde/GObjAnalysis/GObjTypeSystem.h>
#include <phasar/PhasarLLVM/IfdsIde/GObjAnalysis/FastBitVector.h>
#include <llvm/ADT/SmallBitVector.h>
#include <set>
#include <string>
#include <vector>

// Forward declaration of types for which we only use its pointer or ref type
namespace llvm {
class Instruction;
class Function;
class Value;
} // namespace llvm

namespace psr {

class LLVMBasedICFG;


/**
 * This analysis tracks data-flows through a program. Data flows from
 * dedicated source functions, which generate tainted values, into
 * dedicated sink functions. A leak is reported once a tainted value
 * reached a sink function.
 * (In this case, source functions are "_get_type()" GObject functions
 * and our sinks are casts from one type to another, the taint
 * for our values is their type)
 *
 * @see TaintConfiguration on how to specify your own
 * taint-sensitive source and sink functions.
 */

using BitVectorT = FastBitVector<2>; //llvm::SmallBitVector;

class GObjAnalysis
    : public LLVMDefaultIDETabulationProblem<const llvm::Value *,
                                             BitVectorT,
                                             LLVMBasedICFG &> {
public:
  typedef const llvm::Value *d_t;
  typedef const llvm::Instruction *n_t;
  typedef const llvm::Function *m_t;
  typedef BitVectorT v_t;
  typedef LLVMBasedICFG &i_t;

private:
  std::vector<std::string> EntryPoints;
  GObjTypeGraph TypeInfo;
  std::function<bool(const llvm::Value*)> PredTrue = [](const llvm::Value*) {return true;};
  std::function<bool(const llvm::Value*)> PredZeroVal = [this](const llvm::Value* v) {
    return v == zerovalue || TypeInfo.isTypeValue(v);
  };

public:
  /// Holds all leaks found during the analysis
  // TODO: Is this really needed?
  std::map<n_t, std::set<d_t>> Leaks;

  /**
   *
   * @param icfg
   * @param TSF
   * @param EntryPoints
   */
  GObjAnalysis(i_t icfg, const LLVMTypeHierarchy &th,
                    const ProjectIRDB &irdb,
                    std::vector<std::string> EntryPoints = {"main"});

  ~GObjAnalysis() override = default;

  std::shared_ptr<FlowFunction<d_t>> getNormalFlowFunction(n_t curr,
                                                           n_t succ) override;

  std::shared_ptr<FlowFunction<d_t>> getCallFlowFunction(n_t callStmt,
                                                         m_t destMthd) override;

  std::shared_ptr<FlowFunction<d_t>> getRetFlowFunction(n_t callSite,
                                                        m_t calleeMthd,
                                                        n_t exitStmt,
                                                        n_t retSite) override;

  std::shared_ptr<FlowFunction<d_t>>
  getCallToRetFlowFunction(n_t callSite, n_t retSite,
                           std::set<m_t> callees) override;

  std::shared_ptr<FlowFunction<d_t>>
  getSummaryFlowFunction(n_t callStmt, m_t destMthd) override;

  std::map<n_t, std::set<d_t>> initialSeeds() override;

  d_t createZeroValue() override;

  bool isZeroValue(d_t d) const override;

  std::shared_ptr<FlowFunction<GObjAnalysis::d_t>>
  provideSpecialSummaries(GObjAnalysis::n_t callStmt,
                               GObjAnalysis::m_t destMthd);

  // IDE part
  std::shared_ptr<EdgeFunction<v_t>>
  getNormalEdgeFunction(n_t curr, d_t currNode, n_t succ,
                        d_t succNode) override;

  std::shared_ptr<EdgeFunction<v_t>> getCallEdgeFunction(n_t callStmt,
                                                         d_t srcNode,
                                                         m_t destinationMethod,
                                                         d_t destNode) override;

  std::shared_ptr<EdgeFunction<v_t>>
  getReturnEdgeFunction(n_t callSite, m_t calleeMethod, n_t exitStmt,
                        d_t exitNode, n_t reSite, d_t retNode) override;

  std::shared_ptr<EdgeFunction<v_t>>
  getCallToRetEdgeFunction(n_t callSite, d_t callNode, n_t retSite,
                           d_t retSiteNode, std::set<m_t> callees) override;

  std::shared_ptr<EdgeFunction<v_t>>
  getSummaryEdgeFunction(n_t callSite, d_t callNode, n_t retSite,
                         d_t retSiteNode) override;

  v_t topElement() override {
    // all zeros
    return v_t(TypeInfo.getNumTypes(), false);
  }

  v_t bottomElement() override {
    // all ones, this can be any type
    return v_t(TypeInfo.getNumTypes(), true);
  }

  v_t join(v_t lhs, v_t rhs) override;

  std::shared_ptr<EdgeFunction<v_t>> allTopFunction() override;

  // Print part
  void printNode(std::ostream &os, n_t n) const override;

  void printDataFlowFact(std::ostream &os, d_t d) const override;

  void printMethod(std::ostream &os, m_t m) const override;

  void printIDEReport(std::ostream &os, SolverResults<n_t, d_t, v_t> &SR) override;

  void printValue(std::ostream &os, v_t v) const override;

  enum class Error {
    NARROWING_CAST, // a cast from an object of type T to an object of type U, where U <: T
    INCOMPATIBLE_CAST // a cast between two types T and U such that (not (U <: T or T <: U)) (i.e. unrelated types).
  };

  using ErrorEntryT = std::tuple<Error, const llvm::Value*, std::string, std::string>;

  // We use this method with two type parameters: LLVMIDESolver and SolverResults.
  // Both types provide the resultsAt method.
  template<typename ResultT>
  std::vector<GObjAnalysis::ErrorEntryT> collectErrors(ResultT &SR) const {
    std::vector<ErrorEntryT> errors;
    for (auto F : icfg.getAllMethods()) {
      if (!TypeInfo.isTypeCastFunction(F))
        continue;
      std::string toType = F->getName().lower();
      for (auto I : icfg.getCallersOf(F)) {
        llvm::ImmutableCallSite Call(I);
        auto results = SR.resultsAt(I, /*strip zeros*/ true);

        if (results.empty())
          continue;

        for (auto res : results) {
          if (res.first != Call.getArgument(0))
            continue;
          auto &typeVector = res.second;
          std::stringstream message;
          for (int i = typeVector.find_first(); i >= 0; i = typeVector.find_next(i)) {
            std::string fromType = TypeInfo.getTypeFromTypeId(i);
            if (TypeInfo.isNarrowingCast(fromType, toType)) {
              errors.push_back(make_tuple(
                                 Error::NARROWING_CAST,
                                 res.first,
                                 fromType,
                                 toType));
            } else if (!TypeInfo.isWideningCast(fromType, toType)) {
              errors.push_back(make_tuple(
                                 Error::INCOMPATIBLE_CAST,
                                 res.first,
                                 fromType,
                                 toType));
            }
          }
        }
      }
    }
    return errors;
  }
};
} // namespace psr

namespace llvm {
bool operator<(const llvm::SmallBitVector& left, const llvm::SmallBitVector& right) {
  for (int i = left.find_first(), j = right.find_first(); ; i = left.find_next(i), j = right.find_next(j)) {
    if (i > j)
      return true;
  }
  return false;
}
}


#endif
