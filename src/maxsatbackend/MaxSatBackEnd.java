package maxsatbackend;

import checkers.inference.InferenceMain;
import checkers.inference.SlotManager;
import checkers.inference.model.Constraint;
import checkers.inference.model.PreferenceConstraint;
import checkers.inference.model.Serializer;
import checkers.inference.model.Slot;
import constraintsolver.BackEnd;
import constraintsolver.Lattice;
import org.checkerframework.framework.type.QualifierHierarchy;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.*;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;

import org.sat4j.core.VecInt;
import org.sat4j.maxsat.WeightedMaxSatDecorator;
import org.sat4j.specs.ISolver;

import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.TimeoutException;
import util.MathUtils;
import util.PrintUtils;
import util.StatisticPrinter;
import util.StatisticPrinter.StatisticKey;
import util.VectorUtils;

/**
 * @author jianchu MaxSat back end converts constraints to VecInt, and solves
 *         them by sat4j.
 */
public class MaxSatBackEnd extends BackEnd<VecInt[], VecInt[]> {

    protected final SlotManager slotManager;
    protected final List<VecInt> hardClauses = new LinkedList<>();
    protected final List<Constraint> hardConstraints = new LinkedList<>();
    protected final List<VecInt> softClauses = new LinkedList<>();
    protected final File CNFData = new File(new File("").getAbsolutePath() + "/cnfData");
    protected StringBuilder CNFInput = new StringBuilder();

    // Whether we should compute the minimum unsatisfiable constraints
    // and output a more useful error in the case of an unsolvable set of constraints.
    private boolean explainUnsolvable;

    private long serializationStart;
    private long serializationEnd;
    protected long solvingStart;
    protected long solvingEnd;

    public MaxSatBackEnd(Map<String, String> configuration, Collection<Slot> slots,
            Collection<Constraint> constraints, QualifierHierarchy qualHierarchy,
            ProcessingEnvironment processingEnvironment, Serializer<VecInt[], VecInt[]> realSerializer,
            Lattice lattice) {
        super(configuration, slots, constraints, qualHierarchy, processingEnvironment, realSerializer,
                lattice);
        this.slotManager = InferenceMain.getInstance().getSlotManager();

        if (shouldOutputCNF()) {
            CNFData.mkdir();
        }

        explainUnsolvable = "true".equals(configuration.get("explain"));
    }

    protected boolean shouldOutputCNF() {
        String outputCNF = configuration.get("outputCNF");
        return outputCNF != null && outputCNF.equals("true");
    }

    protected void buildCNF() {
        CNFInput.append("c This is the CNF input\n");

        // TODO: We need to handle softclauses at some point...
        final int totalClauses = hardClauses.size();
        final int totalVars = slotManager.getNumberOfSlots() * lattice.numTypes;

        CNFInput.append("p cnf ");
        CNFInput.append(totalVars);
        CNFInput.append(" ");
        CNFInput.append(totalClauses);
        CNFInput.append("\n");

        for (VecInt clause : hardClauses) {
            int[] literals = clause.toArray();
            for (int i = 0; i < literals.length; i++) {
                CNFInput.append(literals[i]);
                CNFInput.append(" ");
            }
            CNFInput.append("0\n");
        }
    }

    protected void writeCNFInput() {
        writeCNFInput("cnfdata.txt");
    }

    protected void writeCNFInput(String file) {
        String writePath = CNFData.getAbsolutePath() + "/" + file;
        File f = new File(writePath);
        PrintWriter pw;
        try {
            pw = new PrintWriter(f);
            pw.write(CNFInput.toString());
            // saving memory of JVM...
            this.CNFInput = null;
            pw.close();
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }
    }

    /**
     * Convert constraints to list of VecInt.
     */
    @Override
    public void convertAll() {
        for (Constraint constraint : constraints) {
            collectVarSlots(constraint);
            for (VecInt res : constraint.serialize(realSerializer)) {
                if (res != null && res.size() != 0) {
                    if (constraint instanceof PreferenceConstraint) {
                        softClauses.add(res);
                    } else {
                        hardClauses.add(res);
                        hardConstraints.add(constraint);
                    }
                }
            }
        }
    }

    /**
     * generate well form clauses such that there is one and only one beta value
     * can be true.
     *
     * @param clauses
     */
    protected void generateWellForm(List<VecInt> clauses) {
        for (Integer id : this.varSlotIds) {
            int[] leastOneIsTrue = new int[lattice.numTypes];
            for (Integer i : lattice.intToType.keySet()) {
                leastOneIsTrue[i] = MathUtils.mapIdToMatrixEntry(id, i.intValue(), lattice);
            }
            clauses.add(VectorUtils.asVec(leastOneIsTrue));
            List<Integer> varList = new ArrayList<Integer>(lattice.intToType.keySet());
            for (int i = 0; i < varList.size(); i++) {
                for (int j = i + 1; j < varList.size(); j++) {
                    VecInt vecInt = new VecInt(2);
                    vecInt.push(-MathUtils.mapIdToMatrixEntry(id, varList.get(i), lattice));
                    vecInt.push(-MathUtils.mapIdToMatrixEntry(id, varList.get(j), lattice));
                    clauses.add(vecInt);
                }
            }
        }
    }

    protected Map<Integer, AnnotationMirror> decode(int[] solution) {
        Map<Integer, AnnotationMirror> result = new HashMap<>();
        for (Integer var : solution) {
            if (var > 0) {
                var = var - 1;
                int slotId = MathUtils.getSlotId(var, lattice);
                AnnotationMirror type = lattice.intToType.get(MathUtils.getIntRep(var, lattice));
                result.put(slotId, type);
            }
        }
        return result;
    }

    @Override
    public Map<Integer, AnnotationMirror> solve() {
        Map<Integer, AnnotationMirror> result = new HashMap<>();
        final WeightedMaxSatDecorator solver = new WeightedMaxSatDecorator(org.sat4j.pb.SolverFactory.newBoth());
        this.serializationStart = System.currentTimeMillis();
        this.convertAll();
        this.serializationEnd = System.currentTimeMillis();
        StatisticPrinter.record(StatisticKey.SAT_SERIALIZATION_TIME,
                (serializationEnd - serializationStart));
        generateWellForm(hardClauses);
        if (shouldOutputCNF()) {
            buildCNF();
            writeCNFInput();
        }
        // printClauses();
        configureSatSolver(solver);

        try {
            for (VecInt hardClause : hardClauses) {
                solver.addHardClause(hardClause);
            }

            for (VecInt softclause : softClauses) {
                solver.addSoftClause(softclause);
            }

            this.solvingStart = System.currentTimeMillis();
            boolean isSatisfiable = solver.isSatisfiable();
            this.solvingEnd = System.currentTimeMillis();

            boolean graph = configuration.get("useGraph") == null || configuration.get("useGraph").equals("true");
            boolean parallel = configuration.get("solveInParallel") == null ||
                    configuration.get("solveInParallel").equals("true");
            long solvingTime = solvingEnd - solvingStart;
            if (graph) {
                if (parallel) {
                    StatisticPrinter.record(StatisticKey.SAT_SOLVING_GRAPH_PARALLEL_TIME, solvingTime);
                } else {
                    StatisticPrinter.record(StatisticKey.SAT_SOLVING_GRAPH_SEQUENTIAL_TIME, solvingTime);
                }
            } else {
                StatisticPrinter.record(StatisticKey.SAT_SOLVING_WITHOUT_GRAPH_TIME, solvingTime);
            }

            if (isSatisfiable) {
                result = decode(solver.model());
                // PrintUtils.printResult(result);
            } else {
                PrintUtils.printContradictingHardConstraints(hardClauses, hardConstraints, slotManager, lattice);
            }
        } catch (ContradictionException e) {
            PrintUtils.printContradictingHardConstraints(hardClauses, hardConstraints, slotManager, lattice);
        } catch (TimeoutException e) {
            throw new RuntimeException("Failed to solve constrains due to timeout", e);
        } catch (Exception e) {
            throw new RuntimeException("Unknown exception occurred when solving constraints", e);
        } finally {
            // saving memory of JVM...
            this.hardClauses.clear();
            this.softClauses.clear();
            this.constraints = null;
        }

        return result;
    }


    /**
     * sat solver configuration Configure
     *
     * @param solver
     */
    private void configureSatSolver(ISolver solver) {
        final int totalVars = (slotManager.getNumberOfSlots() * lattice.numTypes);
        final int totalClauses = hardClauses.size() + softClauses.size();

        solver.newVar(totalVars);
        solver.setExpectedNumberOfClauses(totalClauses);
        StatisticPrinter.record(StatisticKey.CNF_CLAUSES_SIZE, (long) totalClauses);
        countVariables();
        solver.setTimeoutMs(1000000);
    }

    protected void countVariables() {

        Set<Integer> vars = new HashSet<>();
        for (VecInt vi : hardClauses) {
            for (int i : vi.toArray()) {
                vars.add(i);
            }
        }
        StatisticPrinter.record(StatisticKey.CNF_VARIABLE_SIZE, (long) vars.size());
    }
}
