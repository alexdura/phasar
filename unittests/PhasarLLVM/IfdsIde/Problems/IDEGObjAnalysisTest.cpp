#include <gtest/gtest.h>
#include <phasar/DB/ProjectIRDB.h>
#include <phasar/PhasarLLVM/ControlFlow/LLVMBasedICFG.h>
#include <phasar/PhasarLLVM/IfdsIde/Problems/GObjAnalysis.h>
#include <phasar/PhasarLLVM/IfdsIde/GObjAnalysis/FastBitVector.h>
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

TEST(FastBitVector, FastBitVector_01) {
  FastBitVector b, c(true);
  EXPECT_EQ((b | c), c);

  b.set(10);
  b.set(45);
  EXPECT_TRUE(b.get(10));
  EXPECT_TRUE(b.get(45));
  EXPECT_FALSE(b.get(9) || b.get(11));
  EXPECT_FALSE(b.get(46) || b.get(44));
  b.set(10, false);
  EXPECT_FALSE(b.get(10));
  b.set(45, false);
  EXPECT_FALSE(b.get(45));
  EXPECT_EQ(b, FastBitVector());
}

TEST(FastBitVector, FastBitVector_02) {
  FastBitVector b, c;
  b.set(10);
  b.set(0);
  b.set(127);

  c.set(10);
  c.set(0);
  c.set(127);

  EXPECT_EQ(b, c);
  c.set(10, false);
  EXPECT_LT(c,  b);
  b.set(127, false);
  EXPECT_LT(b, c);
}

TEST(FastBitVector, FastBitVector_03) {
  FastBitVector b, c;
  b.set(63);
  b.set(64);
  b.set(65);
  EXPECT_EQ(b.find_first(), 63);
  EXPECT_EQ(b.find_next(63), 64);
  EXPECT_EQ(b.find_next(64), 65);
  EXPECT_EQ(b.find_next(65), -1);
  EXPECT_EQ(c.find_first(), -1);
}


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

TEST_F(IDEGObjAnalysisTest, IncompatibleCast_01) {
  Initialize({pathToLLFiles + "incompatible-cast-1_c_m2r_dbg.ll",
        pathToLLFiles + "viewer-file_c_m2r_dbg.ll",
        pathToLLFiles + "viewer-pink_c_m2r_dbg.ll",
        pathToLLFiles + "viewer-green_c_m2r_dbg.ll"});
  SolverT llvmgobjsolver(*Problem, true, true);
  llvmgobjsolver.solve();

  auto results = Problem->collectErrors(llvmgobjsolver);

  const std::vector<ExpectedErrorT> expectedErrors = {
    {GObjAnalysis::Error::INCOMPATIBLE_CAST, 12, 38, "viewer_green", "viewer_pink"},
  };

  compareResults(expectedErrors, results);
}

TEST_F(IDEGObjAnalysisTest, DISABLED_InvalidBitcast_01) {
  // This test is disabled because it is expected to fail.
  // TODO: enable once we have a mapping from LLVM types to GObj types
  Initialize({pathToLLFiles + "invalid-bitcast-1_c_m2r_dbg.ll",
        pathToLLFiles + "viewer-file_c_m2r_dbg.ll",
        pathToLLFiles + "viewer-pink_c_m2r_dbg.ll"});
  SolverT llvmgobjsolver(*Problem, true, true);
  llvmgobjsolver.solve();

  auto results = Problem->collectErrors(llvmgobjsolver);

  const std::vector<ExpectedErrorT> expectedErrors = {
    {GObjAnalysis::Error::INCOMPATIBLE_CAST, 12, 38, "viewer_green", "viewer_pink"},
  };

  compareResults(expectedErrors, results);
}


// main function for the test case
int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
