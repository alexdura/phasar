/******************************************************************************
 * Copyright (c) 2017 Philipp Schubert.
 * All rights reserved. This program and the accompanying materials are made
 * available under the terms of LICENSE.txt.
 *
 * Contributors:
 *     Philipp Schubert and others
 *****************************************************************************/

#ifndef PHASAR_PHASARLLVM_IFDSIDE_LLVMFLOWFUNCTIONS_MAPFACTSTOCALLEE_H_
#define PHASAR_PHASARLLVM_IFDSIDE_LLVMFLOWFUNCTIONS_MAPFACTSTOCALLEE_H_

#include <functional>
#include <vector>

#include <phasar/PhasarLLVM/IfdsIde/FlowFunction.h>
#include <phasar/PhasarLLVM/IfdsIde/LLVMZeroValue.h>

namespace llvm {
class Value;
class Function;
class ImmutableCallSite;
} // namespace llvm

namespace psr {

/**
 * A predicate can be used to specifiy additonal requirements for mapping
 * actual parameter into formal parameter.
 * @brief Generates all valid formal parameter in the callee context.
 */
class MapFactsToCallee : public FlowFunction<const llvm::Value *> {
protected:
  const llvm::Function *destMthd;
  std::vector<const llvm::Value *> actuals;
  std::vector<const llvm::Value *> formals;
  std::function<bool(const llvm::Value *)> predicate;
  std::function<bool(const llvm::Value *)> zeroValuePredicate;

public:
  MapFactsToCallee(
      const llvm::ImmutableCallSite &callSite, const llvm::Function *destMthd,
      std::function<bool(const llvm::Value *)> predicate =
      [](const llvm::Value *) { return true; },
      std::function<bool(const llvm::Value *)> zeroValuePredicate =
      [](const llvm::Value *v) { return LLVMZeroValue::getInstance()->isLLVMZeroValue(v); }
    );
  virtual ~MapFactsToCallee() = default;

  std::set<const llvm::Value *>
  computeTargets(const llvm::Value *source) override;
};

} // namespace psr

#endif
