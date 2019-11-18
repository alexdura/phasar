#include <gtest/gtest.h>
#include <phasar/DB/ProjectIRDB.h>
#include <phasar/PhasarLLVM/ControlFlow/LLVMBasedICFG.h>
#include <phasar/PhasarLLVM/IfdsIde/Problems/GObjAnalysis.h>
#include <phasar/PhasarLLVM/IfdsIde/Solver/LLVMIDESolver.h>
#include <phasar/PhasarLLVM/Passes/ValueAnnotationPass.h>
#include <phasar/PhasarLLVM/Pointer/LLVMTypeHierarchy.h>
#include <phasar/Utils/Logger.h>

using namespace psr;

using SolverT = LLVMIDESolver<const llvm::Value *, GObjAnalysis::v_t, LLVMBasedICFG &>;

using ExpectedErrorT = std::tuple<GObjAnalysis::Error,
                          unsigned /* line */,
                          unsigned /* col */,
                          std::string /* fromType */,
                          std::string /* toType */>;

/* ============== TEST FIXTURE ============== */
class IDEGObjAnalysisTest : public ::testing::Test {
protected:
  const std::string pathToLLFiles =
      PhasarConfig::getPhasarConfig().PhasarDirectory() +
      "build/test/llvm_test_code/gobj/";
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

  void compareResults(
    const std::vector<ExpectedErrorT> &groundTruth,
    const std::vector<GObjAnalysis::ErrorEntryT> &results) {

    EXPECT_EQ(groundTruth.size(), results.size()) << "Different number of errors.";
    if (groundTruth.size() != results.size())
      return;

    for (unsigned i = 0; i < groundTruth.size(); ++i) {
      auto &groundTruthEntry = groundTruth[i];
      auto &resultsEntry = results[i];
      // same class of error
      EXPECT_EQ(get<0>(groundTruthEntry), get<0>(resultsEntry)) << "Different error type.";
      const llvm::Instruction *I = llvm::cast<llvm::Instruction>(get<1>(resultsEntry));
      unsigned line = I->getDebugLoc().getLine();
      unsigned col = I->getDebugLoc().getCol();
      EXPECT_EQ(get<1>(groundTruthEntry), line);
      EXPECT_EQ(get<2>(groundTruthEntry), col);
      EXPECT_EQ(get<3>(groundTruthEntry), get<2>(resultsEntry));
      EXPECT_EQ(get<4>(groundTruthEntry), get<3>(resultsEntry));
    }
  }
}; // Test Fixture

/* ============== BASIC TESTS ============== */
TEST_F(IDEGObjAnalysisTest, NarrowingTestBasic_01) {
  Initialize({pathToLLFiles + "invalid-narrowing-cast_c_m2r_dbg.ll",
        pathToLLFiles + "viewer-file_c_m2r_dbg.ll",
        pathToLLFiles + "viewer-pink_c_m2r_dbg.ll"});
  SolverT llvmgobjsolver(*Problem, false, true);
  llvmgobjsolver.solve();

  auto results = Problem->collectErrors(llvmgobjsolver);

  const std::vector<ExpectedErrorT> expectedErrors = {
    {GObjAnalysis::Error::NARROWING_CAST, 12, 38, "viewer_file", "viewer_pink"}
  };

  compareResults(expectedErrors, results);
}

TEST_F(IDEGObjAnalysisTest, NarrowingTestStruct_01) {
  // initializeLogger(true);
  Initialize({pathToLLFiles + "invalid-narrowing-cast-1_c_m2r_dbg.ll",
        pathToLLFiles + "viewer-file_c_m2r_dbg.ll",
        pathToLLFiles + "viewer-pink_c_m2r_dbg.ll"});
  SolverT llvmgobjsolver(*Problem, true, true);
  llvmgobjsolver.solve();

  auto results = Problem->collectErrors(llvmgobjsolver);

  const std::vector<ExpectedErrorT> expectedErrors = {
    {GObjAnalysis::Error::NARROWING_CAST, 22, 31, "viewer_file", "viewer_pink"}
  };

  compareResults(expectedErrors, results);
}

TEST_F(IDEGObjAnalysisTest, NarrowingTestStruct_02) {
  // initializeLogger(true);
  Initialize({pathToLLFiles + "invalid-narrowing-cast-2_c_m2r_dbg.ll",
        pathToLLFiles + "viewer-file_c_m2r_dbg.ll",
        pathToLLFiles + "viewer-pink_c_m2r_dbg.ll"});
  SolverT llvmgobjsolver(*Problem, true, true);
  llvmgobjsolver.solve();

  auto results = Problem->collectErrors(llvmgobjsolver);

  const std::vector<ExpectedErrorT> expectedErrors = {
    {GObjAnalysis::Error::NARROWING_CAST, 18, 38, "viewer_file", "viewer_pink"},
    {GObjAnalysis::Error::NARROWING_CAST, 20, 34, "viewer_file", "viewer_pink"}

  };

  compareResults(expectedErrors, results);
}


// main function for the test case
int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
