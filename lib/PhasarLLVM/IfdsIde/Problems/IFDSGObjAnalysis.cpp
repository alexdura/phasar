/******************************************************************************
 * Copyright (c) 2017 Philipp Schubert.
 * All rights reserved. This program and the accompanying materials are made
 * available under the terms of LICENSE.txt.
 *
 * Contributors:
 *     Philipp Schubert and others
 *****************************************************************************/

#include <llvm/IR/CallSite.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Value.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/Debug.h>

#include <phasar/PhasarLLVM/ControlFlow/LLVMBasedICFG.h>
#include <phasar/PhasarLLVM/IfdsIde/FlowFunction.h>
#include <phasar/PhasarLLVM/IfdsIde/FlowFunctions/GenAll.h>
#include <phasar/PhasarLLVM/IfdsIde/FlowFunctions/GenIf.h>
#include <phasar/PhasarLLVM/IfdsIde/FlowFunctions/Identity.h>
#include <phasar/PhasarLLVM/IfdsIde/FlowFunctions/KillAll.h>
#include <phasar/PhasarLLVM/IfdsIde/LLVMFlowFunctions/MapFactsToCallee.h>
#include <phasar/PhasarLLVM/IfdsIde/LLVMFlowFunctions/MapFactsToCaller.h>
#include <phasar/PhasarLLVM/IfdsIde/LLVMZeroValue.h>
#include <phasar/PhasarLLVM/IfdsIde/Problems/IFDSGObjAnalysis.h>
#include <phasar/PhasarLLVM/IfdsIde/SpecialSummaries.h>

#include <phasar/Utils/LLVMIRToSrc.h>
#include <phasar/Utils/LLVMShorthands.h>
#include <phasar/Utils/Logger.h>

using namespace std;
using namespace psr;

namespace psr {

IFDSGObjAnalysis::IFDSGObjAnalysis(
    i_t icfg, const LLVMTypeHierarchy &th, const ProjectIRDB &irdb,
    TaintConfiguration<IFDSGObjAnalysis::d_t> TSF, vector<string> EntryPoints)
    : LLVMDefaultIFDSTabulationProblem(icfg, th, irdb),
      SourceSinkFunctions(TSF), EntryPoints(EntryPoints) {

  for (const llvm::Module *M : irdb.getAllModules()) {
    GObjTypeGraph tg(*M);
    tg.buildTypeGraph();
  }

  exit(0);


  IFDSGObjAnalysis::zerovalue = createZeroValue();
}

shared_ptr<FlowFunction<IFDSGObjAnalysis::d_t>>
IFDSGObjAnalysis::getNormalFlowFunction(IFDSGObjAnalysis::n_t curr,
                                         IFDSGObjAnalysis::n_t succ) {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "IFDSGObjAnalysis::getNormalFlowFunction()");
  // If a tainted value is stored, the store location must be tainted too
  if (auto Store = llvm::dyn_cast<llvm::StoreInst>(curr)) {
    struct TAFF : FlowFunction<IFDSGObjAnalysis::d_t> {
      const llvm::StoreInst *store;
      TAFF(const llvm::StoreInst *s) : store(s){};
      set<IFDSGObjAnalysis::d_t>
      computeTargets(IFDSGObjAnalysis::d_t source) override {
        if (store->getValueOperand() == source) {
          return set<IFDSGObjAnalysis::d_t>{store->getPointerOperand(),
                                             source};
        } else if (store->getValueOperand() != source &&
                   store->getPointerOperand() == source) {
          return {};
        } else {
          return {source};
        }
      }
    };
    return make_shared<TAFF>(Store);
  }
  // If a tainted value is loaded, the loaded value is of course tainted
  if (auto Load = llvm::dyn_cast<llvm::LoadInst>(curr)) {
    return make_shared<GenIf<IFDSGObjAnalysis::d_t>>(
        Load, zeroValue(), [Load](IFDSGObjAnalysis::d_t source) {
          return source == Load->getPointerOperand();
        });
  }
  // Check if an address is computed from a tainted base pointer of an
  // aggregated object
  if (auto GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(curr)) {
    return make_shared<GenIf<IFDSGObjAnalysis::d_t>>(
        GEP, zeroValue(), [GEP](IFDSGObjAnalysis::d_t source) {
          return source == GEP->getPointerOperand();
        });
  }
  // Otherwise we do not care and leave everything as it is
  return Identity<IFDSGObjAnalysis::d_t>::getInstance();
}

shared_ptr<FlowFunction<IFDSGObjAnalysis::d_t>>
IFDSGObjAnalysis::getCallFlowFunction(IFDSGObjAnalysis::n_t callStmt,
                                       IFDSGObjAnalysis::m_t destMthd) {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "IFDSGObjAnalysis::getCallFlowFunction()");
  string FunctionName = cxx_demangle(destMthd->getName().str());
  // Check if a source or sink function is called:
  // We then can kill all data-flow facts not following the called function.
  // The respective taints or leaks are then generated in the corresponding
  // call to return flow function.
  if (SourceSinkFunctions.isSource(FunctionName) ||
      (SourceSinkFunctions.isSink(FunctionName))) {
    return KillAll<IFDSGObjAnalysis::d_t>::getInstance();
  }
  // Map the actual into the formal parameters
  if (llvm::isa<llvm::CallInst>(callStmt) ||
      llvm::isa<llvm::InvokeInst>(callStmt)) {
    return make_shared<MapFactsToCallee>(llvm::ImmutableCallSite(callStmt),
                                         destMthd);
  }
  // Pass everything else as identity
  return Identity<IFDSGObjAnalysis::d_t>::getInstance();
}

shared_ptr<FlowFunction<IFDSGObjAnalysis::d_t>>
IFDSGObjAnalysis::getRetFlowFunction(IFDSGObjAnalysis::n_t callSite,
                                      IFDSGObjAnalysis::m_t calleeMthd,
                                      IFDSGObjAnalysis::n_t exitStmt,
                                      IFDSGObjAnalysis::n_t retSite) {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "IFDSGObjAnalysis::getRetFlowFunction()");
  // We must check if the return value and formal parameter are tainted, if so
  // we must taint all user's of the function call. We are only interested in
  // formal parameters of pointer/reference type.
  return make_shared<MapFactsToCaller>(
      llvm::ImmutableCallSite(callSite), calleeMthd, exitStmt,
      [](IFDSGObjAnalysis::d_t formal) {
        return formal->getType()->isPointerTy();
      });
  // All other stuff is killed at this point
}

shared_ptr<FlowFunction<IFDSGObjAnalysis::d_t>>
IFDSGObjAnalysis::getCallToRetFlowFunction(
    IFDSGObjAnalysis::n_t callSite, IFDSGObjAnalysis::n_t retSite,
    set<IFDSGObjAnalysis::m_t> callees) {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "IFDSGObjAnalysis::getCallToRetFlowFunction()");
  // Process the effects of source or sink functions that are called
  for (auto *Callee : icfg.getCalleesOfCallAt(callSite)) {
    string FunctionName = cxx_demangle(Callee->getName().str());
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG) << "F:" << Callee->getName().str());
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG) << "demangled F:" << FunctionName);
    if (SourceSinkFunctions.isSource(FunctionName)) {
      // process generated taints
      LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG) << "Plugin SOURCE effects");
      auto Source = SourceSinkFunctions.getSource(FunctionName);
      set<IFDSGObjAnalysis::d_t> ToGenerate;
      llvm::ImmutableCallSite CallSite(callSite);
      if (auto pval =
              std::get_if<TaintConfiguration<IFDSGObjAnalysis::d_t>::All>(
                  &Source.TaintedArgs)) {
        for (unsigned i = 0; i < CallSite.getNumArgOperands(); ++i) {
          IFDSGObjAnalysis::d_t V = CallSite.getArgOperand(i);
          // Insert the value V that gets tainted
          ToGenerate.insert(V);
          // We also have to collect all aliases of V and generate them
          auto PTS = icfg.getWholeModulePTG().getPointsToSet(V);
          for (auto Alias : PTS) {
            ToGenerate.insert(Alias);
          }
        }
      } else if (auto pval = std::get_if<
                     TaintConfiguration<IFDSGObjAnalysis::d_t>::None>(
                     &Source.TaintedArgs)) {
        // don't do anything
      } else if (auto pval =
                     std::get_if<std::vector<unsigned>>(&Source.TaintedArgs)) {
        for (auto FormalIndex : *pval) {
          IFDSGObjAnalysis::d_t V = CallSite.getArgOperand(FormalIndex);
          // Insert the value V that gets tainted
          ToGenerate.insert(V);
          // We also have to collect all aliases of V and generate them
          auto PTS = icfg.getWholeModulePTG().getPointsToSet(V);
          for (auto Alias : PTS) {
            ToGenerate.insert(Alias);
          }
        }
      } else {
        throw std::runtime_error("Something went wrong, unexpected type");
      }

      if (Source.TaintsReturn) {
        ToGenerate.insert(callSite);
      }
      return make_shared<GenAll<IFDSGObjAnalysis::d_t>>(ToGenerate,
                                                         zeroValue());
    }
    if (SourceSinkFunctions.isSink(FunctionName)) {
      // process leaks
      LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG) << "Plugin SINK effects");
      struct TAFF : FlowFunction<IFDSGObjAnalysis::d_t> {
        llvm::ImmutableCallSite callSite;
        IFDSGObjAnalysis::m_t calledMthd;
        TaintConfiguration<IFDSGObjAnalysis::d_t>::SinkFunction Sink;
        map<IFDSGObjAnalysis::n_t, set<IFDSGObjAnalysis::d_t>> &Leaks;
        const IFDSGObjAnalysis *taintanalysis;
        TAFF(llvm::ImmutableCallSite cs, IFDSGObjAnalysis::m_t calledMthd,
             TaintConfiguration<IFDSGObjAnalysis::d_t>::SinkFunction s,
             map<IFDSGObjAnalysis::n_t, set<IFDSGObjAnalysis::d_t>> &leaks,
             const IFDSGObjAnalysis *ta)
            : callSite(cs), calledMthd(calledMthd), Sink(s), Leaks(leaks),
              taintanalysis(ta) {}
        set<IFDSGObjAnalysis::d_t>
        computeTargets(IFDSGObjAnalysis::d_t source) override {
          // check if a tainted value flows into a sink
          // if so, add to Leaks and return id
          if (!taintanalysis->isZeroValue(source)) {
            for (unsigned Idx = 0; Idx < callSite.getNumArgOperands(); ++Idx) {
              if (source == callSite.getArgOperand(Idx) &&
                  Sink.isLeakedArg(Idx)) {
                cout << "FOUND LEAK" << endl;
                Leaks[callSite.getInstruction()].insert(source);
              }
            }
          }
          return {source};
        }
      };
      return make_shared<TAFF>(llvm::ImmutableCallSite(callSite), Callee,
                               SourceSinkFunctions.getSink(FunctionName), Leaks,
                               this);
    }
  }
  // Otherwise pass everything as it is
  return Identity<IFDSGObjAnalysis::d_t>::getInstance();
}

shared_ptr<FlowFunction<IFDSGObjAnalysis::d_t>>
IFDSGObjAnalysis::getSummaryFlowFunction(IFDSGObjAnalysis::n_t callStmt,
                                          IFDSGObjAnalysis::m_t destMthd) {
  SpecialSummaries<IFDSGObjAnalysis::d_t> &specialSummaries =
      SpecialSummaries<IFDSGObjAnalysis::d_t>::getInstance();
  string FunctionName = cxx_demangle(destMthd->getName().str());
  // If we have a special summary, which is neither a source function, nor
  // a sink function, then we provide it to the solver.
  if (specialSummaries.containsSpecialSummary(FunctionName) &&
      !SourceSinkFunctions.isSource(FunctionName) &&
      !SourceSinkFunctions.isSink(FunctionName)) {
    return specialSummaries.getSpecialFlowFunctionSummary(FunctionName);
  } else {
    // Otherwise we indicate, that not special summary exists
    // and the solver thus calls the call flow function instead
    return nullptr;
  }
}

map<IFDSGObjAnalysis::n_t, set<IFDSGObjAnalysis::d_t>>
IFDSGObjAnalysis::initialSeeds() {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "IFDSGObjAnalysis::initialSeeds()");
  // If main function is the entry point, commandline arguments have to be
  // tainted. Otherwise we just use the zero value to initialize the analysis.
  map<IFDSGObjAnalysis::n_t, set<IFDSGObjAnalysis::d_t>> SeedMap;
  for (auto &EntryPoint : EntryPoints) {
    if (EntryPoint == "main") {
      set<IFDSGObjAnalysis::d_t> CmdArgs;
      for (auto &Arg : icfg.getMethod(EntryPoint)->args()) {
        CmdArgs.insert(&Arg);
      }
      CmdArgs.insert(zeroValue());
      SeedMap.insert(
          make_pair(&icfg.getMethod(EntryPoint)->front().front(), CmdArgs));
    } else {
      SeedMap.insert(make_pair(&icfg.getMethod(EntryPoint)->front().front(),
                               set<IFDSGObjAnalysis::d_t>({zeroValue()})));
    }
  }
  return SeedMap;
}

IFDSGObjAnalysis::d_t IFDSGObjAnalysis::createZeroValue() {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "IFDSGObjAnalysis::createZeroValue()");
  // create a special value to represent the zero value!
  return LLVMZeroValue::getInstance();
}

bool IFDSGObjAnalysis::isZeroValue(IFDSGObjAnalysis::d_t d) const {
  return LLVMZeroValue::getInstance()->isLLVMZeroValue(d);
}

void IFDSGObjAnalysis::printNode(ostream &os, IFDSGObjAnalysis::n_t n) const {
  os << llvmIRToString(n);
}

void IFDSGObjAnalysis::printDataFlowFact(ostream &os,
                                          IFDSGObjAnalysis::d_t d) const {
  os << llvmIRToString(d);
}

void IFDSGObjAnalysis::printMethod(ostream &os,
                                    IFDSGObjAnalysis::m_t m) const {
  os << m->getName().str();
}

void IFDSGObjAnalysis::printIFDSReport(
    std::ostream &os, SolverResults<n_t, d_t, BinaryDomain> &SR) {
  os << "\n----- Found the following leaks -----\n";
  if (Leaks.empty()) {
    os << "No leaks found!\n";
  } else {
    for (auto Leak : Leaks) {
      os << "At instruction\nIR  : " << llvmIRToString(Leak.first) << '\n';
      os << llvmValueToSrc(Leak.first);
      os << "\n\nLeak(s):\n";
      for (auto LeakedValue : Leak.second) {
        os << "IR  : ";
        // Get the actual leaked alloca instruction if possible
        if (auto Load = llvm::dyn_cast<llvm::LoadInst>(LeakedValue)) {
          os << llvmIRToString(Load->getPointerOperand()) << '\n'
             << llvmValueToSrc(Load->getPointerOperand()) << '\n';

        } else {
          os << llvmIRToString(LeakedValue) << '\n'
             << llvmValueToSrc(LeakedValue) << '\n';
        }
      }
      os << "-------------------\n";
    }
  }
}

void GObjTypeGraph::buildTypeGraph() {
  using namespace llvm;

  for (const Function &F : M.getFunctionList()) {
    StringRef name = F.getName();
    if (!(name.endswith("_get_type_once") || name.endswith("_get_type")))
      continue;

    for (const BasicBlock &B : F) {
      for (const Instruction &I : B) {
        if (!isa<CallInst>(I))
          continue;
        ImmutableCallSite callSite(&I);

        const Function *calledFunc = callSite.getCalledFunction();
        if (!calledFunc) {
          continue;
        }

        StringRef  calleeName = calledFunc->getName();

        if (calleeName.equals("g_type_register_static_simple")) {
          const Value *arg0 = callSite.getArgOperand(0);
          if (const ConstantInt *IC = dyn_cast<ConstantInt>(arg0)) {
            if (IC->getZExtValue() == 80)
              dbgs() << name << "->" << "GObject" << "\n";
            else
              dbgs() << "Unknown type id: " << *IC << "\n";
          } else if (const CallInst *C = dyn_cast<CallInst>(arg0)) {
            ImmutableCallSite parentTypeCallSite(C);
            StringRef parentTypeCalleeName = parentTypeCallSite->getName();
            if (parentTypeCalleeName.endswith("_get_type")) {
              dbgs() << name << "->" << parentTypeCalleeName << "\n";
            } else {
              dbgs() << "Unknown type id: " << *C << "\n";
            }
          }
        }
      }
    }
  }
}

} // namespace psr
