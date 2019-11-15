#include <gtest/gtest.h>
#include <phasar/DB/ProjectIRDB.h>
#include <phasar/PhasarLLVM/ControlFlow/LLVMBasedICFG.h>
#include <phasar/PhasarLLVM/IfdsIde/Problems/GObjAnalysis.h>
#include <phasar/PhasarLLVM/IfdsIde/Solver/LLVMIDESolver.h>
#include <phasar/PhasarLLVM/Passes/ValueAnnotationPass.h>
#include <phasar/PhasarLLVM/Pointer/LLVMTypeHierarchy.h>

using namespace psr;

using SolverT = LLVMIDESolver<const llvm::Value *, GObjAnalysis::v_t, LLVMBasedICFG &>;

/* ============== TEST FIXTURE ============== */
class IDEGObjAnalysisTest : public ::testing::Test {
protected:
  const std::string pathToLLFiles =
      PhasarConfig::getPhasarConfig().PhasarDirectory() +
      "build/test/llvm_test_code/linear_constant/";
  const std::vector<std::string> EntryPoints = {"main"};

  ProjectIRDB *IRDB;
  LLVMTypeHierarchy *TH;
  LLVMBasedICFG *ICFG;
  GObjAnalysis *Problem;

  IDEGObjAnalysisTest() = default;
  virtual ~IDEGObjAnalysisTest() = default;

  void Initialize(const std::vector<std::string> &IRFiles) {
    IRDB = new ProjectIRDB(IRFiles);
    IRDB->preprocessIR();
    TH = new LLVMTypeHierarchy(*IRDB);
    ICFG =
        new LLVMBasedICFG(*TH, *IRDB, CallGraphAnalysisType::OTF, EntryPoints);
    Problem = new GObjAnalysis(*ICFG, *TH, *IRDB, EntryPoints);
  }

  void SetUp() override {
    bl::core::get()->set_logging_enabled(false);
    ValueAnnotationPass::resetValueID();
  }

  void TearDown() override {
    delete IRDB;
    delete TH;
    delete ICFG;
    delete Problem;
  }

  /**
   * We map instruction id to value for the ground truth. ID has to be
   * a string since Argument ID's are not integer type (e.g. main.0 for argc).
   * @param groundTruth results to compare against
   * @param solver provides the results
   */
  // void compareResults(
  //     const std::map<std::string, int64_t> &groundTruth,
  //     SolverT &solver) {
  //   std::map<std::string, int64_t> results;
  //   for (auto M : IRDB->getAllModules()) {
  //     for (auto &F : *M) {
  //       for (auto exit : ICFG->getExitPointsOf(&F)) {
  //         for (auto res : solver.resultsAt(exit, true)) {
  //           results.insert(std::pair<std::string, int64_t>(
  //               getMetaDataID(res.first), res.second));
  //         }
  //       }
  //     }
  //   }
  //   EXPECT_EQ(results, groundTruth);
  // }
}; // Test Fixture

/* ============== BASIC TESTS ============== */
TEST_F(IDEGObjAnalysisTest, HandleBasicTest_01) {
  Initialize({pathToLLFiles + "basic_01_cpp_dbg.ll"});
  SolverT llvmgobjsolver(*Problem, false, true);
  llvmgobjsolver.solve();
  const std::map<std::string, int64_t> gt = {{"0", 0}, {"1", 13}};
  // compareResults(gt, llvmgobjsolver);
}


// main function for the test case
int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
