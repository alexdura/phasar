/******************************************************************************
 * Copyright (c) 2017 Philipp Schubert.
 * All rights reserved. This program and the accompanying materials are made
 * available under the terms of LICENSE.txt.
 *
 * Contributors:
 *     Philipp Schubert and others
 *****************************************************************************/

#include <llvm/IR/CallSite.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Value.h>

#include <phasar/PhasarLLVM/IfdsIde/LLVMFlowFunctions/MapFactsToCallee.h>
#include <phasar/PhasarLLVM/IfdsIde/LLVMZeroValue.h>

#include <phasar/Utils/LLVMShorthands.h>

using namespace std;
using namespace psr;

namespace psr {

MapFactsToCallee::MapFactsToCallee(
    const llvm::ImmutableCallSite &callSite,
    const llvm::Function *destMthd,
    function<bool(const llvm::Value *)> predicate,
    function<bool(const llvm::Value *)> zeroValuePredicate)
  : destMthd(destMthd), predicate(predicate), zeroValuePredicate(zeroValuePredicate) {
  // Set up the actual parameters
  for (unsigned idx = 0; idx < callSite.getNumArgOperands(); ++idx) {
    actuals.push_back(callSite.getArgOperand(idx));
  }
  // Set up the formal parameters
  for (unsigned idx = 0; idx < destMthd->arg_size(); ++idx) {
    formals.push_back(getNthFunctionArgument(destMthd, idx));
  }
}

set<const llvm::Value *>
MapFactsToCallee::computeTargets(const llvm::Value *source) {
  if (!zeroValuePredicate(source)) {
    set<const llvm::Value *> res;
    // Handle C-style varargs functions
    if (destMthd->isVarArg()) {
      // Map actual parameter into corresponding formal parameter.
      for (unsigned idx = 0; idx < actuals.size(); ++idx) {
        if (source == actuals[idx] && predicate(actuals[idx])) {
          if (idx >= destMthd->arg_size() && !destMthd->isDeclaration()) {
            // Over-approximate by trying to add the
            //   alloca [1 x %struct.__va_list_tag], align 16
            // to the results
            // find the allocated %struct.__va_list_tag and generate it
            for (auto &BB : *destMthd) {
              for (auto &I : BB) {
                if (auto Alloc = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
                  if (Alloc->getAllocatedType()->isArrayTy() &&
                      Alloc->getAllocatedType()->getArrayNumElements() > 0 &&
                      Alloc->getAllocatedType()
                          ->getArrayElementType()
                          ->isStructTy() &&
                      Alloc->getAllocatedType()
                              ->getArrayElementType()
                              ->getStructName() == "struct.__va_list_tag") {
                    res.insert(Alloc);
                  }
                }
              }
            }
          } else {
            res.insert(formals[idx]); // corresponding formal
          }
        }
      }
      return res;
    } else {
      // Handle ordinary case
      // Map actual parameter into corresponding formal parameter.
      for (unsigned idx = 0; idx < actuals.size(); ++idx) {
        if (source == actuals[idx] && predicate(actuals[idx])) {
          res.insert(formals[idx]); // corresponding formal
        }
      }
      return res;
    }
  } else {
    return {source};
  }
}

} // namespace psr
