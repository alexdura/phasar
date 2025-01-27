/******************************************************************************
 * Copyright (c) 2017 Philipp Schubert.
 * All rights reserved. This program and the accompanying materials are made
 * available under the terms of LICENSE.txt.
 *
 * Contributors:
 *     Philipp Schubert and others
 *****************************************************************************/

#ifndef PHASAR_PHASARLLVM_IFDSIDE_PROBLEMS_IFDSGOBJANALYSIS_H_
#define PHASAR_PHASARLLVM_IFDSIDE_PROBLEMS_IFDSGOBJANALYSIS_H_

#include <iosfwd>
#include <map>
#include <memory>
#include <phasar/PhasarLLVM/IfdsIde/LLVMDefaultIFDSTabulationProblem.h>
#include <phasar/PhasarLLVM/Utils/TaintConfiguration.h>
#include <phasar/PhasarLLVM/IfdsIde/GObjAnalysis/GObjTypeSystem.h>
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
class IFDSGObjAnalysis
    : public LLVMDefaultIFDSTabulationProblem<const llvm::Value *,
                                              LLVMBasedICFG &> {
public:
  typedef const llvm::Value *d_t;
  typedef const llvm::Instruction *n_t;
  typedef const llvm::Function *m_t;
  typedef LLVMBasedICFG &i_t;

private:
  TaintConfiguration<const llvm::Value *> SourceSinkFunctions;
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
  IFDSGObjAnalysis(i_t icfg, const LLVMTypeHierarchy &th,
                    const ProjectIRDB &irdb,
                    TaintConfiguration<const llvm::Value *> TSF,
                    std::vector<std::string> EntryPoints = {"main"});

  ~IFDSGObjAnalysis() override = default;

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

  void printNode(std::ostream &os, n_t n) const override;

  void printDataFlowFact(std::ostream &os, d_t d) const override;

  void printMethod(std::ostream &os, m_t m) const override;

  void printIFDSReport(std::ostream &os,
                       SolverResults<n_t, d_t, BinaryDomain> &SR) override;

  std::shared_ptr<FlowFunction<IFDSGObjAnalysis::d_t>>
  provideSpecialSummaries(IFDSGObjAnalysis::n_t callStmt,
                               IFDSGObjAnalysis::m_t destMthd);
};
} // namespace psr

#endif
