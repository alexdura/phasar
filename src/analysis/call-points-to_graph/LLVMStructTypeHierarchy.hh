/*
 * ClassHierarchy.hh
 *
 *  Created on: 01.02.2017
 *      Author: pdschbrt
 */

#ifndef ANALYSIS_LLVMSTRUCTTYPEHIERARCHY_HH_
#define ANALYSIS_LLVMSTRUCTTYPEHIERARCHY_HH_

#include <llvm/IR/CallSite.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <algorithm>
#include <boost/graph/depth_first_search.hpp>
#include <boost/graph/graph_utility.hpp>
#include <boost/graph/graphviz.hpp>
#include <boost/graph/transitive_closure.hpp>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <tuple>
#include <vector>
#include "../../db/ProjectIRCompiledDB.hh"
#include "VTable.hh"
using namespace std;

class LLVMStructTypeHierarchy {
 private:
  struct VertexProperties {
    llvm::Type* llvmtype;
    string name;
  };

  struct EdgeProperties {
    string name;
  };

  typedef boost::adjacency_list<boost::setS, boost::vecS, boost::directedS,
                                VertexProperties, EdgeProperties>
      digraph_t;
  typedef boost::graph_traits<digraph_t>::vertex_descriptor vertex_t;
  typedef boost::graph_traits<digraph_t>::edge_descriptor edge_t;

  struct reachability_dfs_visitor : boost::default_dfs_visitor {
    set<vertex_t>& subtypes;
    reachability_dfs_visitor(set<vertex_t>& types) : subtypes(types) {}
    template <class Vertex, class Graph>
    void finish_vertex(Vertex u, const Graph& g) {
      subtypes.insert(u);
    }
  };

  digraph_t g;
  map<string, vertex_t> type_vertex_map;
  map<string, VTable> vtable_map;
  set<string> recognized_struct_types;

  void reconstructVTable(const llvm::Module& M);

 public:
  LLVMStructTypeHierarchy() = default;
  LLVMStructTypeHierarchy(const ProjectIRCompiledDB& IRDB);
  ~LLVMStructTypeHierarchy() = default;
  void analyzeModule(const llvm::Module& M);
  set<string> getTransitivelyReachableTypes(string TypeName);
  vector<const llvm::Function*> constructVTable(const llvm::Type* T,
                                                const llvm::Module* M);
  // const llvm::Function* getFunctionFromVirtualCallSite(
  //     llvm::Module* M, llvm::ImmutableCallSite ICS);
  string getVTableEntry(string TypeName, unsigned idx);
  bool hasSuperType(string TypeName, string SuperTypeName);
  bool hasSubType(string TypeName, string SubTypeName);
  bool containsVTable(string TypeName);
  void printTransitiveClosure();
  void print();
};

#endif /* ANALYSIS_LLVMSTRUCTTYPEHIERARCHY_HH_ */