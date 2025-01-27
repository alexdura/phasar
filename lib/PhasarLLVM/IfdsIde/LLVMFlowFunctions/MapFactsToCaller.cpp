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
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Value.h>

#include <phasar/PhasarLLVM/IfdsIde/LLVMFlowFunctions/MapFactsToCaller.h>
#include <phasar/PhasarLLVM/IfdsIde/LLVMZeroValue.h>

#include <phasar/Utils/LLVMShorthands.h>

using namespace std;
using namespace psr;

namespace psr {

MapFactsToCaller::MapFactsToCaller(
    llvm::ImmutableCallSite cs, const llvm::Function *calleeMthd,
    const llvm::Instruction *exitstmt,
    function<bool(const llvm::Value *)> paramPredicate,
    function<bool(const llvm::Function *)> returnPredicate,
    function<bool(const llvm::Value *)> zeroValuePredicate)
    : callSite(cs), calleeMthd(calleeMthd),
      exitStmt(llvm::dyn_cast<llvm::ReturnInst>(exitstmt)),
      paramPredicate(paramPredicate), returnPredicate(returnPredicate), zeroValuePredicate(zeroValuePredicate) {
  // Set up the actual parameters
  for (unsigned idx = 0; idx < callSite.getNumArgOperands(); ++idx) {
    actuals.push_back(callSite.getArgOperand(idx));
  }
  // Set up the formal parameters
  for (unsigned idx = 0; idx < calleeMthd->arg_size(); ++idx) {
    formals.push_back(getNthFunctionArgument(calleeMthd, idx));
  }
}

set<const llvm::Value *>
MapFactsToCaller::computeTargets(const llvm::Value *source) {
  if (!zeroValuePredicate(source)) {
    set<const llvm::Value *> res;
    // Handle C-style varargs functions
    if (calleeMthd->isVarArg() && !calleeMthd->isDeclaration()) {
      const llvm::Instruction *AllocVarArg;
      // Find the allocation of %struct.__va_list_tag
      for (auto &BB : *calleeMthd) {
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
              AllocVarArg = Alloc;
              // TODO break out this nested loop earlier (without goto ;-)
            }
          }
        }
      }
      // Generate the varargs things by using an over-approximation
      if (source == AllocVarArg) {
        for (unsigned idx = formals.size(); idx < actuals.size(); ++idx) {
          res.insert(actuals[idx]);
        }
      }
    }
    // Handle ordinary case
    // Map formal parameter into corresponding actual parameter.
    for (unsigned idx = 0; idx < formals.size(); ++idx) {
      if (source == formals[idx] && paramPredicate(formals[idx])) {
        res.insert(actuals[idx]); // corresponding actual
      }
    }
    // Collect return value facts
    if (source == exitStmt->getReturnValue() && returnPredicate(calleeMthd)) {
      res.insert(callSite.getInstruction());
    }
    return res;
  } else {
    return {source};
  }
}

} // namespace psr
