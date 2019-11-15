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
#include <llvm/ADT/SmallBitVector.h>

namespace psr {

class GObjTypeGraph {
  const std::set<llvm::Module *> &Modules;
  const char* TOP_LEVEL_TYPE = "object";

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

  std::unordered_map<std::string, llvm::SmallBitVector> TypeToBitVectorMap;
  std::unordered_map<unsigned, std::string> TypeIdToTypeMap;

  llvm::LLVMContext TypeValueContext;
  llvm::Module TypeValueModule;

  std::map<std::string, std::set<std::string>> SubTypeMap, SuperTypeMap;

  void buildTypeGraph();

  void initializeMaps() {
    unsigned i = 0;
    for (auto &tp : SuperClassMap) {
      llvm::SmallBitVector bv(getNumTypes(), false);
      bv.set(i);
      TypeToBitVectorMap[tp.first] = bv;
      TypeIdToTypeMap[i] = tp.first;
      i++;
    }
  }

public:
  GObjTypeGraph(const std::set<llvm::Module*> &Modules) :
    Modules(Modules),
    TypeValueModule("module_gobj_type", TypeValueContext) {
    buildTypeGraph();
    initializeMaps();
    SuperTypeMap = computeSuperTypeMap();
    SubTypeMap = computeSubTypeMap();
  }

  void dumpTypeMap() const {
    for (auto &p : SuperClassMap) {
      auto it = TypeToBitVectorMap.find(p.first);
      assert(it != TypeToBitVectorMap.end());
      llvm::dbgs() << "[" << it->second.find_last() << "] "
                   << p.first << " -> " << p.second << "\n";
    }
  }

  unsigned getNumTypes() const {
    return SuperClassMap.size();
  }

  // type name -> BitVector mapping, used by IDE transfer functions
  llvm::SmallBitVector getBitVectorForTypeName(const std::string &name) const {
    auto it = TypeToBitVectorMap.find(name);
    assert(it != TypeToBitVectorMap.end() && "Name missing from the type database");
    return it->second;
  }

  // type name -> Value* mapping, used by IFDS analysis
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

  // helper functions
  static bool isGetTypeFunction(const llvm::Function *F) {
    return F->getName().endswith("_get_type");
  }

  bool isTypeCastFunction(const llvm::Function *F) {
    // for a type name named view_file, the cast functions
    // is called VIEW_FILE.
    llvm::StringRef name = F->getName();
    auto it = TypeToBitVectorMap.find(name.lower());
    return it != TypeToBitVectorMap.end();
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

  std::map<std::string, std::set<std::string>> computeSuperTypeMap() const {
    std::map<std::string, std::set<std::string>> result;
    bool change = true;
    for (auto &SP : SuperClassMap) {
      result[SP.first] = {SP.second};
    }
    while (change) {
      change = false;
      for (auto TypeToTypeSetPair : result) {
        for (auto Type : TypeToTypeSetPair.second) {
          auto it = SuperClassMap.find(Type);
          assert(it != SuperClassMap.end());
          std::pair(std::ignore, change) = result[TypeToTypeSetPair.first].insert(it->second);
        }
      }
    }
    return result;
  }

  std::map<std::string, std::set<std::string>> computeSubTypeMap() const {
    std::map<std::string, std::set<std::string>> result;
    bool change = true;
    for (auto &SP : SuperClassMap) {
      result[SP.second] = {SP.first};
    }
    while (change) {
      change = false;
      for (auto TypePair : SuperClassMap) {
        auto SubTypes = result[TypePair.second];
        auto it = SuperClassMap.find(TypePair.first);
        assert(it != SuperClassMap.end());
        for (auto Type : SubTypes) {
          std::pair(std::ignore, change) = result[TypePair.first].insert(Type);
        }
      }
    }
    return result;
  }

  bool isWideningCast(std::string from, std::string to) const {
    if (from == to)
      return true;
    auto it = SuperTypeMap.find(from);
    assert(it != SuperTypeMap.end() && "Type missing from the map");
    return it->second.count(to);
  }

  bool isNarrowingCast(std::string from, std::string to) const {
    auto it = SuperTypeMap.find(to);
    assert(it != SuperTypeMap.end() && "Type missing from the map");
    return it->second.count(from);
  }

  std::string getTypeFromTypeId(unsigned tid) const {
    auto it = TypeIdToTypeMap.find(tid);
    assert(it != TypeIdToTypeMap.end());
    return it->second;
  }

};

}

#endif
