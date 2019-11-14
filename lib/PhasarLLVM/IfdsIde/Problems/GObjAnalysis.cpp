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
#include <phasar/PhasarLLVM/IfdsIde/Problems/GObjAnalysis.h>
#include <phasar/PhasarLLVM/IfdsIde/SpecialSummaries.h>

#include <phasar/Utils/LLVMIRToSrc.h>
#include <phasar/Utils/LLVMShorthands.h>
#include <phasar/Utils/Logger.h>

using namespace std;
using namespace psr;

namespace psr {
GObjAnalysis::GObjAnalysis(
    i_t icfg, const LLVMTypeHierarchy &th, const ProjectIRDB &irdb,
    TaintConfiguration<GObjAnalysis::d_t> TSF, vector<string> EntryPoints)
    : LLVMDefaultIDETabulationProblem(icfg, th, irdb),
      SourceSinkFunctions(TSF), EntryPoints(EntryPoints), TypeInfo(irdb.getAllModules()) {
  GObjAnalysis::zerovalue = createZeroValue();
  llvm::outs() << "----- Type map ----\n";
  TypeInfo.dumpTypeMap();
}

shared_ptr<FlowFunction<GObjAnalysis::d_t>>
GObjAnalysis::getNormalFlowFunction(GObjAnalysis::n_t curr,
                                         GObjAnalysis::n_t succ) {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "GObjAnalysis::getNormalFlowFunction()");
  // TODO:
  // Track type values through load, store and getelementptr.
  // Look at all the values in the Type set instead.

  // If a tainted value is stored, the store location must be tainted too
  if (auto Store = llvm::dyn_cast<llvm::StoreInst>(curr)) {
    // TAFF probably stands for "Taint Analysis Flow Function"
    struct TAFF : FlowFunction<GObjAnalysis::d_t> {
      const llvm::StoreInst *store;
      TAFF(const llvm::StoreInst *s) : store(s){};
      set<GObjAnalysis::d_t>
      computeTargets(GObjAnalysis::d_t source) override {
	// If the variable we are looking at the
	// variable to be stored
        if (store->getValueOperand() == source) {
	  // The source flows into the target pointer.
          return set<GObjAnalysis::d_t>{store->getPointerOperand(),
                                            source};
        } else if (store->getValueOperand() != source &&
                   store->getPointerOperand() == source) {
	  // If we are erasing the value, we cut
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
    return make_shared<GenIf<GObjAnalysis::d_t>>(
        Load, nullptr, [Load](GObjAnalysis::d_t source) {
          return source == Load->getPointerOperand();
        });
  }
  // Check if an address is computed from a tainted base pointer of an
  // aggregated object
  if (auto GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(curr)) {
    return make_shared<GenIf<GObjAnalysis::d_t>>(
        GEP, nullptr, [GEP](GObjAnalysis::d_t source) {
          return source == GEP->getPointerOperand();
        });
  }

  if (auto *BC = llvm::dyn_cast<llvm::BitCastInst>(curr)) {
    struct BitCastTAFF : FlowFunction<d_t> {
      d_t Src, Dst;
      const GObjTypeGraph &TG;
      BitCastTAFF(d_t Src, d_t Dst, const GObjTypeGraph &TG) : Src(Src), Dst(Dst), TG(TG) {}
      std::set<d_t> computeTargets(d_t source) override {
        if (source == Src) {
          llvm::dbgs() << ">>> Bitcast of GObject " << *source << " at " << *Dst << "\n";
          return {Src, Dst};
        } else if (source == Dst) {
          return {};
        } else {
          return {source};
        }
      }
    };
    return make_shared<BitCastTAFF>(BC->getOperand(0), BC, TypeInfo);
  }
  // Otherwise we do not care and leave everything as it is
  return Identity<GObjAnalysis::d_t>::getInstance();
}

shared_ptr<FlowFunction<GObjAnalysis::d_t>>
GObjAnalysis::getCallFlowFunction(GObjAnalysis::n_t callStmt,
                                       GObjAnalysis::m_t destMthd) {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "GObjAnalysis::getCallFlowFunction()");
  string FunctionName = cxx_demangle(destMthd->getName().str());
  // Check if a source or sink function is called:
  // We then can kill all data-flow facts not following the called function.
  // The respective taints or leaks are then generated in the corresponding
  // call to return flow function.

#if 0
  if (SourceSinkFunctions.isSource(FunctionName) ||
      (SourceSinkFunctions.isSink(FunctionName))) {
    return KillAll<GObjAnalysis::d_t>::getInstance();
  }
#endif

  // Map the actual into the formal parameters
  if (llvm::isa<llvm::CallInst>(callStmt) ||
      llvm::isa<llvm::InvokeInst>(callStmt)) {
    return make_shared<MapFactsToCallee>(
      llvm::ImmutableCallSite(callStmt),
      destMthd,
      PredTrue,
      PredZeroVal);
  }

  // Pass everything else as identity
  return Identity<GObjAnalysis::d_t>::getInstance();
}

shared_ptr<FlowFunction<GObjAnalysis::d_t>>
GObjAnalysis::getRetFlowFunction(GObjAnalysis::n_t callSite,
                                      GObjAnalysis::m_t calleeMthd,
                                      GObjAnalysis::n_t exitStmt,
                                      GObjAnalysis::n_t retSite) {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "GObjAnalysis::getRetFlowFunction()");
  // We must check if the return value and formal parameter are tainted, if so
  // we must taint all user's of the function call. We are only interested in
  // formal parameters of pointer/reference type.
  return make_shared<MapFactsToCaller>(
      llvm::ImmutableCallSite(callSite), calleeMthd, exitStmt,
      [](GObjAnalysis::d_t formal) {
        return formal->getType()->isPointerTy();
      }, PredTrue, PredZeroVal);
  // All other stuff is killed at this point
}

shared_ptr<FlowFunction<GObjAnalysis::d_t>>
GObjAnalysis::getCallToRetFlowFunction(
  GObjAnalysis::n_t callSite, GObjAnalysis::n_t retSite,
    set<GObjAnalysis::m_t> callees) {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "GObjAnalysis::getCallToRetFlowFunction()");
  // Otherwise pass everything as it is
  return Identity<GObjAnalysis::d_t>::getInstance();
}

shared_ptr<FlowFunction<GObjAnalysis::d_t>>
GObjAnalysis::getSummaryFlowFunction(GObjAnalysis::n_t callStmt,
                                          GObjAnalysis::m_t destMthd) {
  SpecialSummaries<GObjAnalysis::d_t> &specialSummaries =
      SpecialSummaries<GObjAnalysis::d_t>::getInstance();
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
    return provideSpecialSummaries(callStmt, destMthd);
  }
}

shared_ptr<FlowFunction<GObjAnalysis::d_t>>
GObjAnalysis::provideSpecialSummaries(GObjAnalysis::n_t callStmt,
                                               GObjAnalysis::m_t destMthd) {
  llvm::StringRef FunctionName = cxx_demangle(destMthd->getName().str());

  SpecialSummaries<GObjAnalysis::d_t> &specialSummaries =
      SpecialSummaries<GObjAnalysis::d_t>::getInstance();

  llvm::ImmutableCallSite Call(callStmt);
  if (FunctionName.startswith("g_object_new")) {
    // for g_object_new, transfer the type from the first argument
    // to the return
    struct NewObjTAFF : FlowFunction<GObjAnalysis::d_t> {
      const llvm::Value *Arg0, *Ret;
      const GObjTypeGraph &TI;
      NewObjTAFF(const llvm::Value *arg0, const llvm::Value *ret, const GObjTypeGraph &TI) :
        Arg0(arg0), Ret(ret), TI(TI) {}
      set<GObjAnalysis::d_t>
      computeTargets(GObjAnalysis::d_t source) override {
        if (source  == Arg0) {
          return {Ret, Arg0};
        } else if (source == Ret) {
          return {};
        } else {
          return {source};
        }
      }
    };
    return make_shared<NewObjTAFF>(Call.getArgument(0), callStmt, TypeInfo);
  } else if (Call.getCalledFunction() &&
             GObjTypeGraph::isGetTypeFunction(Call.getCalledFunction())) {
    auto typeValue = TypeInfo.getValueForTypeName(
      GObjTypeGraph::extractTypeName(Call.getCalledFunction()));

    struct GetTypeTF : FlowFunction<GObjAnalysis::d_t> {
      const llvm::Value *TypeValue;
      const llvm::Value *Ret;

      GetTypeTF(d_t TypeValue, d_t Ret) : TypeValue(TypeValue), Ret(Ret) {
      }

      set<d_t> computeTargets(d_t source) override {
        if (source == TypeValue) {
          return {Ret, TypeValue};
        } else if (source == Ret) {
          return {};
        } else {
          return {source};
        }
      }
    };
    return make_shared<GetTypeTF>(typeValue, callStmt);
  }

  return nullptr;
}

map<GObjAnalysis::n_t, set<GObjAnalysis::d_t>>
GObjAnalysis::initialSeeds() {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "GObjAnalysis::initialSeeds()");
  // If main function is the entry point, commandline arguments have to be
  // tainted. Otherwise we just use the zero value to initialize the analysis.
  map<GObjAnalysis::n_t, set<GObjAnalysis::d_t>> SeedMap;

  for (const llvm::Module *M : irdb.getAllModules()) {
    for (const llvm::Function &F : M->getFunctionList()) {
      for (const llvm::BasicBlock &B : F) {
        for (const llvm::Instruction &I : B) {
          if (GObjTypeGraph::isGetTypeCall(&I)) {
            llvm::ImmutableCallSite CallSite(&I);
            llvm::StringRef typeName = GObjTypeGraph::extractTypeName(CallSite.getCalledFunction());
            // the TypeName->Value map is lazily initialized, so for the call to getZeroValues() below
            // to work, we need to initialize it here.
            TypeInfo.getValueForTypeName(typeName);
          }
        }
      }
    }
  }

  for (auto &EntryPoint : EntryPoints) {
    set<const llvm::Value*> initialValues(TypeInfo.getTypeValues().begin(),
                                          TypeInfo.getTypeValues().end());
    initialValues.insert(zerovalue);
    SeedMap.insert(std::make_pair(&icfg.getMethod(EntryPoint)->front().front(),
                                  std::move(initialValues)));
  }

  return SeedMap;
}

GObjAnalysis::d_t GObjAnalysis::createZeroValue() {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "GObjAnalysis::createZeroValue()");
  // create a special value to represent the zero value!
  return LLVMZeroValue::getInstance();
}

bool GObjAnalysis::isZeroValue(GObjAnalysis::d_t d) const {
  return LLVMZeroValue::getInstance()->isLLVMZeroValue(d);
}


shared_ptr<EdgeFunction<GObjAnalysis::v_t>>
GObjAnalysis::getNormalEdgeFunction(GObjAnalysis::n_t curr,
                                        GObjAnalysis::d_t currNode,
                                        GObjAnalysis::n_t succ,
                                        GObjAnalysis::d_t succNode) {
  cout << "GObjAnalysis::getNormalEdgeFunction()\n";
  return EdgeIdentity<GObjAnalysis::v_t>::getInstance();
}

shared_ptr<EdgeFunction<GObjAnalysis::v_t>>
GObjAnalysis::getCallEdgeFunction(GObjAnalysis::n_t callStmt,
                                      GObjAnalysis::d_t srcNode,
                                      GObjAnalysis::m_t destinationMethod,
                                      GObjAnalysis::d_t destNode) {
  cout << "GObjAnalysis::getCallEdgeFunction()\n";
  return EdgeIdentity<GObjAnalysis::v_t>::getInstance();
}

shared_ptr<EdgeFunction<GObjAnalysis::v_t>>
GObjAnalysis::getReturnEdgeFunction(GObjAnalysis::n_t callSite,
                                        GObjAnalysis::m_t calleeMethod,
                                        GObjAnalysis::n_t exitStmt,
                                        GObjAnalysis::d_t exitNode,
                                        GObjAnalysis::n_t reSite,
                                        GObjAnalysis::d_t retNode) {
  cout << "GObjAnalysis::getReturnEdgeFunction()\n";
  return EdgeIdentity<GObjAnalysis::v_t>::getInstance();
}

shared_ptr<EdgeFunction<GObjAnalysis::v_t>>
GObjAnalysis::getCallToRetEdgeFunction(GObjAnalysis::n_t callSite,
                                           GObjAnalysis::d_t callNode,
                                           GObjAnalysis::n_t retSite,
                                           GObjAnalysis::d_t retSiteNode,
                                           set<GObjAnalysis::m_t> callees) {
  cout << "GObjAnalysis::getCallToRetEdgeFunction()\n";
  return EdgeIdentity<GObjAnalysis::v_t>::getInstance();
}

shared_ptr<EdgeFunction<GObjAnalysis::v_t>>
GObjAnalysis::getSummaryEdgeFunction(GObjAnalysis::n_t callSite,
                                         GObjAnalysis::d_t callNode,
                                         GObjAnalysis::n_t retSite,
                                         GObjAnalysis::d_t retSiteNode) {
  cout << "GObjAnalysis::getSummaryEdgeFunction()\n";
  return EdgeIdentity<GObjAnalysis::v_t>::getInstance();
}

GObjAnalysis::v_t GObjAnalysis::join(GObjAnalysis::v_t lhs,
                                             GObjAnalysis::v_t rhs) {
  cout << "GObjAnalysis::join()\n";
  return topElement();
}

shared_ptr<EdgeFunction<GObjAnalysis::v_t>>
GObjAnalysis::allTopFunction() {
  cout << "GObjAnalysis::allTopFunction()\n";
  return make_shared<GObjAnalysisAllTop>(getNumGObjectTypes());
}

GObjAnalysis::v_t GObjAnalysis::GObjAnalysisAllTop::computeTarget(
    GObjAnalysis::v_t source) {
  cout << "GObjAnalysis::GObjAnalysisAllTop::computeTarget()\n";
  return llvm::BitVector(NumGObjectTypes, false);
}

shared_ptr<EdgeFunction<GObjAnalysis::v_t>>
GObjAnalysis::GObjAnalysisAllTop::composeWith(
    shared_ptr<EdgeFunction<GObjAnalysis::v_t>> secondFunction) {
  cout << "GObjAnalysis::GObjAnalysisAllTop::composeWith()\n";
  return EdgeIdentity<GObjAnalysis::v_t>::getInstance();
}

shared_ptr<EdgeFunction<GObjAnalysis::v_t>>
GObjAnalysis::GObjAnalysisAllTop::joinWith(
    shared_ptr<EdgeFunction<GObjAnalysis::v_t>> otherFunction) {
  cout << "GObjAnalysis::GObjAnalysisAllTop::joinWith()\n";
  return EdgeIdentity<GObjAnalysis::v_t>::getInstance();
}

bool GObjAnalysis::GObjAnalysisAllTop::equal_to(
    shared_ptr<EdgeFunction<GObjAnalysis::v_t>> other) const {
  cout << "GObjAnalysis::GObjAnalysisAllTop::equalTo()\n";
  return false;
}

void GObjAnalysis::printNode(ostream &os, GObjAnalysis::n_t n) const {
  os << llvmIRToString(n);
}

void GObjAnalysis::printDataFlowFact(ostream &os,
                                          GObjAnalysis::d_t d) const {
  os << llvmIRToString(d);
}

void GObjAnalysis::printMethod(ostream &os,
                                    GObjAnalysis::m_t m) const {
  os << m->getName().str();
}

void GObjAnalysis::printValue(ostream &os, v_t v) const {
  os << " ";
}


void GObjAnalysis::printIFDSReport(
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

} // namespace psr
