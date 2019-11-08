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
      SourceSinkFunctions(TSF), EntryPoints(EntryPoints), TypeInfo(irdb.getAllModules()) {
  IFDSGObjAnalysis::zerovalue = createZeroValue();
}

shared_ptr<FlowFunction<IFDSGObjAnalysis::d_t>>
IFDSGObjAnalysis::getNormalFlowFunction(IFDSGObjAnalysis::n_t curr,
                                         IFDSGObjAnalysis::n_t succ) {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "IFDSGObjAnalysis::getNormalFlowFunction()");
  // TODO:
  // Track type values through load, store and getelementptr.
  // Look at all the values in the Type set instead.

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

  if (auto *BC = llvm::dyn_cast<llvm::BitCastInst>(curr)) {
    struct BitCastTAFF : FlowFunction<d_t> {
      d_t Src, Dst;
      BitCastTAFF(d_t Src, d_t Dst) : Src(Src), Dst(Dst) {}
      std::set<d_t> computeTargets(d_t source) override {
        if (source == Src) {
          llvm::dbgs() << ">>> Bitcast of GObject " << *source << "\n";
          return {Src, Dst};
        } else if (source == Dst) {
          return {};
        } else {
          return {source};
        }
      }
    };
    return make_shared<BitCastTAFF>(BC, BC->getOperand(0));
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

#if 0
  if (SourceSinkFunctions.isSource(FunctionName) ||
      (SourceSinkFunctions.isSink(FunctionName))) {
    return KillAll<IFDSGObjAnalysis::d_t>::getInstance();
  }
#endif

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
#if 0
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
#endif
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
    return provideSpecialSummaries(callStmt, destMthd);
  }
}

shared_ptr<FlowFunction<IFDSGObjAnalysis::d_t>>
IFDSGObjAnalysis::provideSpecialSummaries(IFDSGObjAnalysis::n_t callStmt,
                                               IFDSGObjAnalysis::m_t destMthd) {
  llvm::StringRef FunctionName = cxx_demangle(destMthd->getName().str());

  SpecialSummaries<IFDSGObjAnalysis::d_t> &specialSummaries =
      SpecialSummaries<IFDSGObjAnalysis::d_t>::getInstance();

  if (FunctionName.startswith("g_object_new")) {
    // for g_object_new, transfer the type from the first argument
    // to the return
    llvm::ImmutableCallSite Call(callStmt);
    struct NewObjTAFF : FlowFunction<IFDSGObjAnalysis::d_t> {
      const llvm::Value *Arg0, *Ret;
      NewObjTAFF(const llvm::Value *arg0, const llvm::Value *ret) :
        Arg0(arg0), Ret(ret) {}
      set<IFDSGObjAnalysis::d_t>
      computeTargets(IFDSGObjAnalysis::d_t source) override {
        if (source == Arg0)
          return {Ret};
        return {};
      }
    };
    return make_shared<NewObjTAFF>(Call.getArgument(0), callStmt);
  }

  return nullptr;
}

map<IFDSGObjAnalysis::n_t, set<IFDSGObjAnalysis::d_t>>
IFDSGObjAnalysis::initialSeeds() {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "IFDSGObjAnalysis::initialSeeds()");
  // If main function is the entry point, commandline arguments have to be
  // tainted. Otherwise we just use the zero value to initialize the analysis.
  map<IFDSGObjAnalysis::n_t, set<IFDSGObjAnalysis::d_t>> SeedMap;

  for (const llvm::Module *M : irdb.getAllModules()) {
    for (const llvm::Function &F : M->getFunctionList()) {
      for (const llvm::BasicBlock &B : F) {
        for (const llvm::Instruction &I : B) {
          if (GObjTypeGraph::isGetTypeCall(&I)) {
            llvm::ImmutableCallSite CallSite(&I);
            llvm::StringRef typeName = GObjTypeGraph::extractTypeName(&F);
            const llvm::Value *typeValue = TypeInfo.getValueForTypeName(typeName);
            SeedMap.insert(make_pair(&I, set<IFDSGObjAnalysis::d_t>({typeValue})));
          }
        }
      }
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

// A function that builds the type hierarchy from LLVM IR:
// That is: a map from the daughter class to its parent class
void GObjTypeGraph::buildTypeGraph() {
  using namespace llvm;

  // To get the type
  for (const Module *M : Modules) {
    for (const Function &F : M->getFunctionList()) {
      StringRef name = F.getName();
      // Any function that does not finish by _get_type_once or _get_type
      // is ignored.
      if (!(name.endswith("_get_type_once") || name.endswith("_get_type")))
        continue;

      // We are interested in functions that have names
      // <class_name>_get_type_once or <class_name>_get_type
      for (const BasicBlock &B : F) {
        for (const Instruction &I : B) {
          if (!isa<CallInst>(I))
            continue;
          ImmutableCallSite callSite(&I);

          const Function *calledFunc = callSite.getCalledFunction();
          if (!calledFunc) {
            continue;
          }

          name.consume_back("_once");
          name.consume_back("_get_type");
          std::string subTypeName = name.str();

          StringRef  calleeName = calledFunc->getName();

          // The functions <class_name>_get_type call
          // automatically some type registration for their parent type,
          // that is why we are interested in them!
          // This type registration requires a type ID.
          if (calleeName.equals("g_type_register_static_simple")
              || calleeName.equals("g_type_register_static")) {
            const Value *arg0 = callSite.getArgOperand(0);
            // Some of these calls only register a type through its ID,
            // That is the case when the class inherits GObject.
            if (const ConstantInt *IC = dyn_cast<ConstantInt>(arg0)) {
              if (IC->getZExtValue() == 80 /* type id of GObject, by convention */) {
                SuperClassMap[subTypeName] = "GObject";
              } else {
                dbgs() << "Unknown type id: " << *IC << "\n";
              }
            } else if (const CallInst *C = dyn_cast<CallInst>(arg0)) {
              // Here, we are in the case where the type ID was set with
              // a function.
              ImmutableCallSite parentTypeCallSite(C);
              StringRef parentTypeCalleeName = parentTypeCallSite.getCalledFunction()->getName();
              // If this function also has a name that ends with get_type,
              // it means it will return the type of the parent.
              if (isGetTypeFunction(parentTypeCallSite.getCalledFunction())) {
                parentTypeCalleeName.consume_back("_get_type");
                SuperClassMap[subTypeName] = extractTypeName(parentTypeCallSite.getCalledFunction());
              } else {
                dbgs() << "Unknown type id: " << *C << "\n";
              }
            }
          }
        }
      }
    }
  }
}

void GObjTypeGraph::dumpTypeMap() const {
  for (auto &p : SuperClassMap) {
    llvm::dbgs() << p.first << " -> " << p.second << "\n";
  }
}

const llvm::Value *GObjTypeGraph::getValueForTypeName(const std::string &name) {
  // lazily create a zero value an return it
  auto it = ZeroValueMap.find(name);
  if (it != ZeroValueMap.end())
    return it->second;
  auto zv = ZeroValueModule.getOrInsertGlobal(name,
                                              llvm::Type::getIntNTy(ZeroValueContext, 2));

  ZeroValueMap[name] = zv;
  ZeroValues.insert(zv);
  return zv;
}

} // namespace psr
