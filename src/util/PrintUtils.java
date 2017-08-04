package util;

import checkers.inference.InferenceMain;
import checkers.inference.SlotManager;
import checkers.inference.model.Constraint;
import checkers.inference.model.serialization.ToStringSerializer;
import constraintsolver.Lattice;
import org.sat4j.core.VecInt;
import org.sat4j.maxsat.SolverFactory;
import org.sat4j.pb.IPBSolver;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.xplain.DeletionStrategy;
import org.sat4j.tools.xplain.Xplain;
import util.StatisticPrinter.StatisticKey;

import javax.lang.model.element.AnnotationMirror;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class PrintUtils {

    /**
     * print all soft and hard clauses for testing.
     */
    public static void printClauses(final List<VecInt> hardClauses, final List<VecInt> softClauses) {
        System.out.println("Hard clauses: ");
        for (VecInt hardClause : hardClauses) {
            System.out.println(hardClause);
        }
        System.out.println();
        System.out.println("Soft clauses: ");
        for (VecInt softClause : softClauses) {
            System.out.println(softClause);
        }
    }

    /**
     * print result from sat solver for testing.
     *
     * @param result
     */
    public static void printResult(Map<Integer, AnnotationMirror> result) {

        final int maxLength = String.valueOf(InferenceMain.getInstance().getSlotManager().getNumberOfSlots()).length();
        StringBuilder printResult = new StringBuilder();
        System.out.println("/***********************results****************************/");
        for (Integer j : result.keySet()) {
            printResult.append("SlotID: ");
            printResult.append(String.valueOf(j));
            for (int i = 0; i < maxLength + 2 - String.valueOf(j).length(); i++) {
                printResult.append(" ");
            }
            printResult.append("Annotation: ");
            printResult.append(result.get(j).toString());
            printResult.append("\n");
        }
        System.out.println(printResult.toString());
        System.out.flush();
        System.out.println("/**********************************************************/");
    }

    public static void printStatistic(Map<StatisticKey, Long> statistic) {
        System.out.println("/***********************statistic start*************************/");
        for (StatisticKey j : statistic.keySet()) {
            if (statistic.get(j) != (long) 0) {
                System.out.println(j.toString().toLowerCase() + ": " + statistic.get(j));
            }
        }
        System.out.flush();
        System.out.println("/**********************statistic end****************************/");
    }

    public static void writeStatistic(Map<StatisticKey, Long> statistic) {
        String writePath = new File(new File("").getAbsolutePath()).toString() + File.separator + "solver-statistic.txt";
        StringBuilder sb = new StringBuilder();
        for (StatisticKey j : statistic.keySet()) {
            if (statistic.get(j) != (long) 0) {
                sb.append((j.toString().toLowerCase() + "," + statistic.get(j)) + "\n");
            }
        }
        try {
            File f = new File(writePath);
            PrintWriter pw = new PrintWriter(writePath);
            pw.write(sb.toString());
            pw.close();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    public static void writeResult(Map<Integer, AnnotationMirror> result) {
        StringBuilder printResult = new StringBuilder();
        final int maxLength = String.valueOf(InferenceMain.getInstance().getSlotManager().getNumberOfSlots())
                .length();

        for (Integer j : result.keySet()) {
            printResult.append("SlotID: ");
            printResult.append(String.valueOf(j));
            for (int i = 0; i < maxLength + 2 - String.valueOf(j).length(); i++) {
                printResult.append(" ");
            }
            printResult.append("Annotation: ");
            printResult.append(result.get(j).toString());
            printResult.append("\n");
        }

        File CNFData = new File(new File("").getAbsolutePath());
        String writePath = CNFData.getAbsolutePath() + "/result" + ".txt";
        File f = new File(writePath);
        PrintWriter pw;
        try {
            pw = new PrintWriter(f);
            pw.write(printResult.toString());
            pw.close();
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }
        printResult = null;
    }

    public static void printContradictingHardConstraintsAndSlots(final List<VecInt> hardClauses, final List<Constraint> hardConstraints,
                                                                 final SlotManager slotManager, final Lattice lattice) {
        Xplain<IPBSolver> explanationSolver = new Xplain<>(SolverFactory.newDefault());
        configureExplanationSolver(hardClauses, slotManager, lattice, explanationSolver);

        try {
            for (VecInt clause : hardClauses) {
                explanationSolver.addClause(clause);
            }
        } catch (ContradictionException e) {
            throw new RuntimeException("Failed to print contradicting constraints", e);
        }

        try {
            if (explanationSolver.isSatisfiable())
                throw new RuntimeException("Failed to find contradicting constraints");
            printAnalysisResult(hardConstraints, explanationSolver);
        } catch (TimeoutException e) {
            throw new RuntimeException("Failed to print contradicting constraints", e);
        }
    }

    private static void configureExplanationSolver(final List<VecInt> hardClauses, final SlotManager slotManager, final Lattice lattice, final Xplain<IPBSolver> xplainer) {
        int numberOfNewVars = slotManager.getNumberOfSlots() * lattice.numTypes;
        int numberOfClauses = hardClauses.size();
        xplainer.setMinimizationStrategy(new DeletionStrategy());
        xplainer.newVar(numberOfNewVars);
        xplainer.setExpectedNumberOfClauses(numberOfClauses);
    }

    private static void printAnalysisResult(final List<Constraint> hardConstraints, final Xplain<IPBSolver> xplainer) throws TimeoutException {
        int[] indicies = xplainer.minimalExplanation();
        Set<Constraint> contradictingConstrains = new HashSet<>();
        ToStringSerializer toStringSerializer = new ToStringSerializer(false);
        OneLevelSlotsPrinter oneLevelSlotsPrinter = new OneLevelSlotsPrinter(toStringSerializer);

        System.out.println("========== Inference failed because of the following inconsistent constraints ==========");
        for (int clauseIndex : indicies) {
            if (clauseIndex > hardConstraints.size()) continue;
            // Solver gives 1-based index. Decrement by 1 here
            Constraint constraint = hardConstraints.get(clauseIndex - 1);
            if (contradictingConstrains.add(constraint))
                System.out.println("\t" + constraint.serialize(toStringSerializer) + " \n\t    " + constraint.getLocation().toString() + "\n");
        }
        System.out.println("==================================== Related Slots =====================================");
        for (Constraint c : contradictingConstrains) {
            c.serialize(oneLevelSlotsPrinter);
        }
        System.out.println("=================================== Explanation Ends Here ==============================");
    }

}
