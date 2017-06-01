package checkers.inference;

import org.checkerframework.framework.test.TestUtilities;
import org.checkerframework.javacutil.Pair;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import dataflow.solvers.backend.DataflowConstraintSolver;
import dataflow.solvers.classic.DataflowSolver;

import org.junit.runners.Parameterized.Parameters;

import checkers.inference.test.CFInferenceTest;

public class DataflowTest extends CFInferenceTest {

    public DataflowTest(File testFile) {
        super(testFile,  dataflow.DataflowChecker.class, "dataflow",
              "-Anomsgtext", "-d", "tests/build/outputdir");
    }

    @Override
    public String getPathToInferenceScript() {
        return "../checker-framework-inference/scripts/inference";
    }

    @Override
    public Pair<String, List<String>> getSolverNameAndOptions() {
        return Pair.<String, List<String>>of(DataflowConstraintSolver.class.getCanonicalName(), new ArrayList<String>());
    }

    @Override
    public boolean useHacks() {
        return true;
    }

    @Parameters
    public static List<File> getTestFiles(){
        List<File> testfiles = new ArrayList<>();//InferenceTestUtilities.findAllSystemTests();
        testfiles.addAll(TestUtilities.findRelativeNestedJavaFiles("testing", "dataflow"));
        return testfiles;
    }
}
