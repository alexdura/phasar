#ifndef PHASAR_GOBJTYPESYSTEM
#define PHASAR_GOBJTYPESYSTEM

#include <set>
#include <unordered_set>
#include <map>

#include <llvm/IR/CallSite.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/Debug.h>

namespace psr {

class GObjTypeGraph {
  const std::set<llvm::Module *> &Modules;

  // A map mapping subclasses to their superclass.
  std::map<std::string, std::string> SuperClassMap;
  // we map type names to LLVM values
  // The Phasar framework also uses LLVM values
  // for its "type" values in the analysis
  // because this is less expensive
  // than having a type for LLVM values
  // and more abstract information (in our case, types).
  std::map<std::string, llvm::Value*> TypeValueMap;
  std::unordered_set<const llvm::Value*> TypeValues;

  llvm::LLVMContext TypeValueContext;
  llvm::Module TypeValueModule;

  void buildTypeGraph();

public:
  GObjTypeGraph(const std::set<llvm::Module*> &Modules) :
    Modules(Modules),
    TypeValueModule("module_gobj_type", TypeValueContext) {
    buildTypeGraph();
  }

  void dumpTypeMap() const {
    for (auto &p : SuperClassMap) {
      llvm::dbgs() << p.first << " -> " << p.second << "\n";
    }
  }

  // Returns an LLVM value or the provided type name.
  // (Probably the last call to <type>_get_type()
  const llvm::Value *getValueForTypeName(const std::string &name) {
    // lazily create a zero value an return it
    auto it = TypeValueMap.find(name);
    if (it != TypeValueMap.end())
      return it->second;
    auto zv = TypeValueModule.getOrInsertGlobal(name,
                                                llvm::Type::getInt64Ty(TypeValueContext));

    TypeValueMap[name] = zv;
    TypeValues.insert(zv);
    return zv;
  }

  bool isTypeValue(const llvm::Value *v) const {
    return TypeValues.count(v);
  }

  const std::unordered_set<const llvm::Value*>& getTypeValues() const {
    return TypeValues;
  }

  static bool isGetTypeFunction(const llvm::Function *F) {
    return F->getName().endswith("_get_type");
  }

  static llvm::StringRef extractTypeName(const llvm::Function *F) {
    llvm::StringRef name = F->getName();
    name.consume_back("_get_type");
    return name;
  }

  static bool isGetTypeCall(const llvm::Instruction *I) {
    llvm::ImmutableCallSite CallSite(I);
    if (!CallSite.isCall())
      return false;
    return CallSite.getCalledFunction() &&
      isGetTypeFunction(CallSite.getCalledFunction());
  }
};

}

#endif
