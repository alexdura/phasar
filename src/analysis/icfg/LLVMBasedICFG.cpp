/*
 * LLVMBasedInterproceduralICFG.cpp
 *
 *  Created on: 09.09.2016
 *      Author: pdschbrt
 */

#include "LLVMBasedICFG.hh"


LLVMBasedICFG::VertexProperties::VertexProperties(const llvm::Function* f) : function(f),
																																						 functionName(f->getName().str()) {

}

LLVMBasedICFG::EdgeProperties::EdgeProperties(const llvm::Instruction* i) : callsite(i),
																																						ir_code(llvmIRToString(i)),
																																						id(stoull(llvm::cast<llvm::MDString>(i->getMetadata(MetaDataKind)->getOperand(0))->getString().str())) {

}

LLVMBasedICFG::LLVMBasedICFG(LLVMStructTypeHierarchy& STH,
														 ProjectIRCompiledDB& IRDB,
														 const vector<string>& EntryPoints)
		: CH(STH), IRDB(IRDB) {
	cout << "calling the walker ...\n";
	cout << "entry points are:\n";
	for (auto& function_name : EntryPoints) {
		cout << function_name << "\n";
	}
  cout << "allocation sites set from WMPTG: ";
  for (auto s: WholeModulePTG.allocating_functions) {
    cout << s << " ";
  }
  cout << "\n\n";
	for (auto& function_name : EntryPoints) {
			llvm::Function* function = IRDB.getFunction(function_name);
			PointsToGraph& ptg = *IRDB.getPointsToGraph(function_name);
			WholeModulePTG.mergeWith(ptg, {}, nullptr);
			resolveIndirectCallWalker(function);
	}
	cout << "constructed whole module ptg and resolved indirect calls ...\n";
//	typename boost::graph_traits<PointsToGraph::graph_t>::edge_iterator ei_start, e_end;
//  cout << '\n' << '\n';
//  static PHSStringConverter converter(IRDB);
//  vector<string> names = WholeModulePTG.getMergeStack();
//  for (const auto& fname : names) {
//    cout << fname << " ";
//  }
//  for (tie(ei_start, e_end) = boost::edges(WholeModulePTG.ptg); ei_start != e_end; ++ei_start) {
//		auto source = boost::source(*ei_start, WholeModulePTG.ptg);
//		auto target = boost::target(*ei_start, WholeModulePTG.ptg);
//    cout << WholeModulePTG.ptg[source].ir_code << " --> " << WholeModulePTG.ptg[target].ir_code << endl;
//		cout << "edge ir_code:" << WholeModulePTG.ptg[*ei_start].ir_code << endl;
//    if(WholeModulePTG.ptg[*ei_start].value) {
//			string hsstringrep = converter.PToHStoreStringRep(WholeModulePTG.ptg[*ei_start].value);
//			cout << "hex name: " << hsstringrep << '\n';
//			cout << "edge id: " << WholeModulePTG.ptg[*ei_start].id << '\n';
//			cout << "Re converted\n";
//    	converter.HStoreStringRepToP(hsstringrep)->dump();
//		}
//    cout << "\n\n";
//		string hs_source_rep = converter.PToHStoreStringRep(PTG.ptg[source].value);
//		string hs_target_rep = converter.PToHStoreStringRep(PTG.ptg[target].value);
//	}
	WholeModulePTG.printAsDot("whole_module_ptg.dot");
	cout << "virtual nodes:\n";
	for (auto& entry : DirectCSTargetMethods) {
		if (entry.second->isDeclaration()) {
			entry.second->dump();
		}
	}
}

/*
 * Using a lambda to just pass this call to the other constructor.
 */
 LLVMBasedICFG::LLVMBasedICFG(LLVMStructTypeHierarchy& STH,
														 ProjectIRCompiledDB& IRDB,
														 const llvm::Module& M)
		: LLVMBasedICFG(STH, IRDB, [](const llvm::Module& M) {
																	vector<string> result;
																	for (auto& F : M) {
																		result.push_back(F.getName().str());
																	}
																	return result;
		}(M)) {}

void LLVMBasedICFG::resolveIndirectCallWalker(const llvm::Function* F) {
	// do not analyze functions more than once (this also acts as recursion detection)
	if (VisitedFunctions.find(F) != VisitedFunctions.end() || F->isDeclaration()) {
		return;
	}
	VisitedFunctions.insert(F);
	// add a node for function F to the call graph (if not present already)
	if (function_vertex_map.find(F->getName().str()) == function_vertex_map.end()) {
  	function_vertex_map[F->getName().str()] = boost::add_vertex(cg);
  	cg[function_vertex_map[F->getName().str()]] = VertexProperties(F);
  }
  for (llvm::const_inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
    const llvm::Instruction& Inst = *I;
    if (llvm::isa<llvm::CallInst>(Inst) || llvm::isa<llvm::InvokeInst>(Inst)) {
      llvm::ImmutableCallSite cs(llvm::dyn_cast<llvm::CallInst>(&Inst));
      // function can be resolved statically
      if (cs.getCalledFunction() != nullptr) {
      	// get the ptg of the function that is called
      	PointsToGraph& callee_ptg = *IRDB.getPointsToGraph(cs.getCalledFunction()->getName().str());
      	callee_ptg.printAsDot(cs.getCalledFunction()->getName().str()+".dot");
      	// map the formals
      	auto escaping_formal_params = callee_ptg.getPointersEscapingThroughParams();
      	vector<pair<const llvm::Value*, const llvm::Value*>> mapping;
      	for (auto& entry : escaping_formal_params) {
      		mapping.push_back(make_pair(cs.getArgOperand(entry.first), entry.second));
      	}
      	// map the possibly multiple return values
      	auto escaping_return_vlaues = callee_ptg.getPointersEscapingThroughReturns();
      	for (auto user : cs->users()) {
      		for (auto escaping_return_value : escaping_return_vlaues) {
      			mapping.push_back(make_pair(user, escaping_return_value));
      		}
      	}
      	// note that aliasing with global variables is handled in the intra-procedural ptg construction
      	cout << "mapping caller to callee pointers\n";
      	printPTGMapping(mapping);
      	DirectCSTargetMethods.insert(make_pair(&Inst, cs.getCalledFunction()));
      	// additionally add a node for the target method to the graph (if not present already)
      	if (function_vertex_map.find(cs.getCalledFunction()->getName().str()) == function_vertex_map.end()) {
      		function_vertex_map[cs.getCalledFunction()->getName().str()] = boost::add_vertex(cg);
      		cg[function_vertex_map[cs.getCalledFunction()->getName().str()]] = VertexProperties(cs.getCalledFunction());
      	}
      	boost::add_edge(function_vertex_map[F->getName().str()], function_vertex_map[cs.getCalledFunction()->getName().str()], EdgeProperties(cs.getInstruction()), cg);
    		// do the merge
      	WholeModulePTG.mergeWith(callee_ptg, mapping, cs.getInstruction());
	      resolveIndirectCallWalker(cs.getCalledFunction());
	    } else {
      // we have to resolve the called function ourselves using the accessible points-to information
        cout << "FOUND INDIRECT CALL-SITE" << endl;
        cs->dump();
        set<string> possible_target_names = resolveIndirectCall(cs);
        set<const llvm::Function*> possible_targets;
        for (auto& possible_target_name : possible_target_names) {
        	possible_targets.insert(IRDB.getFunction(possible_target_name));
        }
        cout << "POSSIBLE TARGES: " << possible_targets.size() << endl;
        IndirectCSTargetMethods.insert(make_pair(cs.getInstruction(), possible_targets));
        // additionally add into boost graph
    		for (auto possible_target : possible_targets) {
    			if (function_vertex_map.find(possible_target->getName().str()) == function_vertex_map.end()) {
    				function_vertex_map[possible_target->getName().str()] = boost::add_vertex(cg);
    				cg[function_vertex_map[possible_target->getName().str()]] = VertexProperties(possible_target);
    			}
    			boost::add_edge(function_vertex_map[F->getName().str()], function_vertex_map[possible_target->getName().str()], EdgeProperties(cs.getInstruction()), cg);
    		}
    		// continue resolving
        for (auto possible_target : possible_targets) {
        	resolveIndirectCallWalker(possible_target);
        }
      }
    }
  }
}

set<string> LLVMBasedICFG::resolveIndirectCall(llvm::ImmutableCallSite CS) {
  cout << "RESOLVING CALL" << endl;
  set<string> possible_call_targets;
  // check if we have a virtual call-site
  if ( CS.getNumArgOperands() > 0) {
    // deal with a virtual member function
  	// retrieve the vtable entry that is called
    const llvm::LoadInst* load = llvm::dyn_cast<llvm::LoadInst>(CS.getCalledValue());
    const llvm::GetElementPtrInst* gep = llvm::dyn_cast<llvm::GetElementPtrInst>(load->getPointerOperand());
    unsigned vtable_index = llvm::dyn_cast<llvm::ConstantInt>(gep->getOperand(1))->getZExtValue();

    cout << "vtable entry: " << vtable_index << endl;

    const llvm::Value* receiver = CS.getArgOperand(0);
    const llvm::Type* receiver_type = receiver->getType();
    auto alloc_sites = WholeModulePTG.getReachableAllocationSites(receiver);
    auto possible_types = WholeModulePTG.computeTypesFromAllocationSites(alloc_sites);
    if (possible_types.empty()) {
    	cout << "could not find any possible types" << endl;
    	// here we take the conservative fall-back solution
    	if (const llvm::StructType* struct_type = llvm::dyn_cast<llvm::StructType>(receiver_type)) {
    		// insert declared type
    		// here we have to call debasify() since the following IR might be generated:
    		//   %struct.A = type <{ i32 (...)**, i32, [4 x i8] }>
    		//   %struct.B = type { %struct.A.base, [4 x i8] }
    		//   %struct.A.base = type <{ i32 (...)**, i32 }>
    		// in such a case %struct.A and %struct.A.base are treated as aliases and the vtable for A is stored
    		// under the name %struct.A whereas in the class hierarchy %struct.A.base is used!
    		// debasify() fixes that circumstance and returns id for all normal cases.
    		possible_call_targets.insert(CH.getVTableEntry(debasify(struct_type->getName().str()), vtable_index));
    		// also insert all possible subtypes
    		auto fallback_type_names = CH.getTransitivelyReachableTypes(struct_type->getName().str());
    		for (auto& fallback_name : fallback_type_names) {
    			possible_call_targets.insert(CH.getVTableEntry(fallback_name, vtable_index));
    		}
    	}
    } else {
    	cout << "found the following possible types" << endl;
    	for (auto type : possible_types) {
    		type->dump();
    		// caution: type might be a pointer type returned by a allocating function
    		const llvm::StructType* struct_type = (!type->isPointerTy()) ?
    																					llvm::dyn_cast<llvm::StructType>(type) :
																							llvm::dyn_cast<llvm::StructType>(type->getPointerElementType());
    		if (struct_type) {
    			// same as above
    			possible_call_targets.insert(CH.getVTableEntry(debasify(struct_type->getName().str()), vtable_index));
    		}
    	}
    }

    cout << "possible targets are:" << endl;
    for (auto entry : possible_call_targets) {
    	cout << entry << endl;
    }


  } else { // else we have to deal with a function pointer
   cout << "function pointer" << endl;
   if (CS.getCalledValue()->getType()->isPointerTy()) {
  	if (const llvm::FunctionType* ftype = llvm::dyn_cast<llvm::FunctionType>(CS.getCalledValue()->getType())) {
  		for (auto entry : IRDB.functions) {
  			const llvm::Function* f = IRDB.modules[entry.second]->getFunction(entry.first);
  			if (matchesSignature(f, ftype)) {
  				possible_call_targets.insert(entry.first);
  			}
  		}
  	}
   }
  }
  return possible_call_targets;
}

void LLVMBasedICFG::printPTGMapping(vector<pair<const llvm::Value*, const llvm::Value*>> mapping) {
	for (auto& entry : mapping) {
		cout << llvmIRToString(entry.first) << " ---> " << llvmIRToString(entry.second) << "\n";
	}
}

const llvm::Function* LLVMBasedICFG::getMethodOf(const llvm::Instruction* stmt) {
	return stmt->getFunction();
}

const llvm::Function* LLVMBasedICFG::getMethod(const string& fun) {
	return IRDB.getFunction(fun);
}

vector<const llvm::Instruction*> LLVMBasedICFG::getPredsOf(const llvm::Instruction* I) {
	vector<const llvm::Instruction *> Preds;
	if (I->getPrevNode()) {
	  Preds.push_back(I->getPrevNode());
	}
	/*
	 * If we do not have a predecessor yet, look for basic blocks which
	 * lead to our instruction in question!
	 */
	if (Preds.empty()) {
	  for (auto &BB : *I->getFunction()) {
	    if (const llvm::TerminatorInst *T =
	            llvm::dyn_cast<llvm::TerminatorInst>(BB.getTerminator())) {
	      for (auto successor : T->successors()) {
	        if (&*successor->begin() == I) {
	          Preds.push_back(T);
	        }
	      }
	    }
	  }
	}
	return Preds;
}

vector<const llvm::Instruction*> LLVMBasedICFG::getSuccsOf(const llvm::Instruction* I) {
	vector<const llvm::Instruction*> Successors;
	if (I->getNextNode())
	  Successors.push_back(I->getNextNode());
	if (const llvm::TerminatorInst* T = llvm::dyn_cast<llvm::TerminatorInst>(I)) {
	  for (auto successor : T->successors()) {
	   Successors.push_back(&*successor->begin());
	  }
	}
	return Successors;
}

vector<pair<const llvm::Instruction*,const llvm::Instruction*>> LLVMBasedICFG::getAllControlFlowEdges(const llvm::Function* fun) {
	vector<pair<const llvm::Instruction*,const llvm::Instruction*>> Edges;
	for (auto& BB : *fun) {
		for (auto& I : BB) {
			auto Successors = getSuccsOf(&I);
			for (auto Successor : Successors) {
				Edges.push_back(make_pair(&I, Successor));
			}
		}
	}
	return Edges;
}

vector<const llvm::Instruction*> LLVMBasedICFG::getAllInstructionsOf(const llvm::Function* fun) {
	vector<const llvm::Instruction*> Instructions;
		for (auto& BB : *fun) {
			for (auto& I : BB) {
				Instructions.push_back(&I);
			}
		}
		return Instructions;
}

bool LLVMBasedICFG::isExitStmt(const llvm::Instruction* stmt) {
	return llvm::isa<llvm::ReturnInst>(stmt);
}

bool LLVMBasedICFG::isStartPoint(const llvm::Instruction* stmt) {
	return (stmt == &stmt->getFunction()->front().front());
}

bool LLVMBasedICFG::isFallThroughSuccessor(const llvm::Instruction* stmt, const llvm::Instruction* succ) {
	if (const llvm::BranchInst* B = llvm::dyn_cast<llvm::BranchInst>(succ)) {
    if (B->isConditional()) {
       return &B->getSuccessor(1)->front() == succ;
     } else {
       return &B->getSuccessor(0)->front() == succ;
     }
	}
	return false;
}

bool LLVMBasedICFG::isBranchTarget(const llvm::Instruction* stmt, const llvm::Instruction* succ) {
	if (const llvm::TerminatorInst* T = llvm::dyn_cast<llvm::TerminatorInst>(stmt)) {
		for (auto successor : T->successors()) {
			if (&*successor->begin() == succ) {
				return true;
			}
		}
	}
	return false;
}

string LLVMBasedICFG::getMethodName(const llvm::Function* fun) {
	return fun->getName().str();
}

/**
 * Returns all callee methods for a given call that might be called.
 */
set<const llvm::Function*> LLVMBasedICFG::getCalleesOfCallAt(
    const llvm::Instruction* n) {
  if (llvm::isa<llvm::CallInst>(n) || llvm::isa<llvm::InvokeInst>(n)) {
  	llvm::ImmutableCallSite CS(n);
  	// handle direct call
  	if (CS.getCalledFunction()) {
  		return { CS.getCalledFunction() };
  	} else { // handle indirect call
  		return IndirectCSTargetMethods[n];
  	}
  } else {
    // neither call nor invoke - error!
    llvm::errs() << "ERROR: found instruction that is neither CallInst nor "
                    "InvokeInst\n";
    HEREANDNOW;
    DIE_HARD;
    return {};
  }
}

/**
 * Returns all caller statements/nodes of a given method.
 */
set<const llvm::Instruction*> LLVMBasedICFG::getCallersOf(
    const llvm::Function* m) {
  set<const llvm::Instruction*> CallersOf;
  for (auto& entry : DirectCSTargetMethods) {
  	if (entry.second == m) {
  		CallersOf.insert(entry.first);
  	}
  }
  for (auto& entry : IndirectCSTargetMethods) {
  	for (auto function : entry.second) {
  		if (function == m) {
  			CallersOf.insert(entry.first);
  		}
  	}
  }
  return CallersOf;
}

/**
 * Returns all call sites within a given method.
 */
set<const llvm::Instruction*> LLVMBasedICFG::getCallsFromWithin(
    const llvm::Function* f) {
  set<const llvm::Instruction*> CallSites;
  for (llvm::const_inst_iterator I = llvm::inst_begin(f), E = llvm::inst_end(f); I != E; ++I) {
  	if (llvm::isa<llvm::CallInst>(*I) || llvm::isa<llvm::InvokeInst>(*I)) {
  		CallSites.insert(&(*I));
  	}
  }
  return CallSites;
}

/**
 * Returns all start points of a given method. There may be
 * more than one start point in case of a backward analysis.
 */
set<const llvm::Instruction*> LLVMBasedICFG::getStartPointsOf(
    const llvm::Function* m) {
  return { &m->front().front() };
}

set<const llvm::Instruction*> LLVMBasedICFG::getExitPointsOf(
		const llvm::Function* fun) {
	return { &fun->back().back() };
}

/**
 * Returns all statements to which a call could return.
 * In the RHS paper, for every call there is just one return site.
 * We, however, use as return site the successor statements, of which
 * there can be many in case of exceptional flow.
 */
set<const llvm::Instruction*>
LLVMBasedICFG::getReturnSitesOfCallAt(
    const llvm::Instruction* n) {
  // at the moment we just ignore exceptional control flow
  set<const llvm::Instruction*> ReturnSites;
  if (llvm::isa<llvm::CallInst>(n) || llvm::isa<llvm::InvokeInst>(n)) {
    //ReturnSites.insert(n);
  	llvm::ImmutableCallSite CS(n);
  	for (auto user : CS->users()) {
  		if (const llvm::Instruction* inst = llvm::dyn_cast<llvm::Instruction>(user)) {
  			ReturnSites.insert(inst);
  		}
  	}
  	if (ReturnSites.empty()) {
  		ReturnSites.insert(n->getNextNode());
  	}
  }
  return ReturnSites;
}

CallType LLVMBasedICFG::isCallStmt(const llvm::Instruction* stmt) {
	if (llvm::isa<llvm::CallInst>(stmt) || llvm::isa<llvm::InvokeInst>(stmt)) {
		set<const llvm::Function*> Callees = getCalleesOfCallAt(stmt);
		for (auto Callee : Callees) {
			if (Callee->isDeclaration()) {
				return CallType::unavailable;
			}
		}
		return CallType::call;
	} else {
		return CallType::none;
	}
}

/**
 * Returns the set of all nodes that are neither call nor start nodes.
 */
set<const llvm::Instruction*>
LLVMBasedICFG::allNonCallStartNodes() {
  set<const llvm::Instruction*> NonCallStartNodes;
	for (auto M : IRDB.getAllModules()) {
  	for (auto& F : *M) {
  		for (auto& BB : F) {
  			for (auto& I : BB) {
  				if ((!llvm::isa<llvm::CallInst>(&I)) && (!llvm::isa<llvm::InvokeInst>(&I)) && (!isStartPoint(&I))) {
  					NonCallStartNodes.insert(&I);
  				}
  			}
  		}
  	}
	}
  return NonCallStartNodes;
}

vector<const llvm::Instruction*>
LLVMBasedICFG::getAllInstructionsOfFunction(const string& name) {
  return getAllInstructionsOf(IRDB.getFunction(name));
}

const llvm::Instruction* LLVMBasedICFG::getLastInstructionOf(
    const string& name) {
  const llvm::Function& f = *IRDB.getFunction(name);
  auto last = llvm::inst_end(f);
  last--;
  return &(*last);
}

void LLVMBasedICFG::mergeWith(const LLVMBasedICFG& other) {
	// merge the boost graphs
	vector<pair<LLVMBasedICFG::vertex_t, LLVMBasedICFG::vertex_t>> v_in_g1_u_in_g2;
	for (auto& entry : DirectCSTargetMethods) {
		if (entry.second->isDeclaration()) {
			
		}
	}
	for (auto& entry : IndirectCSTargetMethods) {
		for (auto& f : entry.second) {
			if (f->isDeclaration()) {

			}
		}
	}
	// also merge the call-site to function(s) maps
	DirectCSTargetMethods.insert(other.DirectCSTargetMethods.begin(), other.DirectCSTargetMethods.end());
	IndirectCSTargetMethods.insert(other.IndirectCSTargetMethods.begin(), other.IndirectCSTargetMethods.end());
	// merge visited functions
	VisitedFunctions.insert(other.VisitedFunctions.begin(), other.VisitedFunctions.end());
}

bool LLVMBasedICFG::isPrimitiveFunction(const string& name) {
	for (auto& BB : *IRDB.getFunction(name)) {
		for (auto& I : BB) {
			if (llvm::isa<llvm::CallInst>(&I) || llvm::isa<llvm::InvokeInst>(&I)) {
				return false;
			}
		}
	}
	return true;
}

void LLVMBasedICFG::print() {
	cout << "CallGraph:\n";
	boost::print_graph(cg, boost::get(&LLVMBasedICFG::VertexProperties::functionName, cg));
}

void LLVMBasedICFG::printAsDot(const string& filename) {
	ofstream ofs(filename);
	boost::write_graphviz(ofs, cg,
			boost::make_label_writer(boost::get(&LLVMBasedICFG::VertexProperties::functionName, cg)),
			boost::make_label_writer(boost::get(&LLVMBasedICFG::EdgeProperties::ir_code, cg)));
}

void LLVMBasedICFG::exportPATBCJSON() {
	cout << "LLVMBasedICFG::exportPATBCJSON()\n";
}
