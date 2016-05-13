package logiqlbackend;

import org.checkerframework.javacutil.AnnotationUtils;

import java.io.File;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.Map;

import javax.lang.model.element.AnnotationMirror;

import constraintsolver.Lattice;

/**
 * LogiqlConstraintGenerator take QualifierHierarchy of current type system as
 * input, and generate the logiql encoding of all constraint, and write the
 * result in a .logic file.
 *
 * @author Jianchu Li
 *
 */
public class LogiQLPredicateGenerator {

    private final String path;
    private final StringBuilder allEncodings = new StringBuilder();

    public LogiQLPredicateGenerator(String path) {
        this.path = path;
    }

    public void GenerateLogiqlEncoding() {
        allEncodings.append(getBasicEncoding());
        allEncodings.append(getEqualityConstraintEncoding());
        allEncodings.append(getInequalityConstraintEncoding());
        allEncodings.append(getSubTypeConstraintEncoding());
        allEncodings.append(getComparableConstraintEncoding());

        // System.out.println(allEncodings.toString());

        writeFile(allEncodings.toString());

    }


    private String getEqualityConstraintEncoding() {
        StringBuilder equalityEncoding = new StringBuilder();
        for (AnnotationMirror annoMirror : Lattice.allTypes) {
            String simpleName = getSimpleName(annoMirror);
            equalityEncoding.append("is" + simpleName + "[v2] = true <- equalityConstraint(v1, v2), is"
                    + simpleName + "[v1] = true.\n");
            equalityEncoding.append("is" + simpleName
                    + "[v2] = true <- equalityConstraintContainsConstant(v1, v2), hasconstantName(v1:\""
                    + simpleName + "\").\n");
        }
        return equalityEncoding.toString();
    }
    
    private String getInequalityConstraintEncoding() {
        StringBuilder inequalityEncoding = new StringBuilder();
        for (AnnotationMirror annoMirror : Lattice.allTypes) {
            String simpleName = getSimpleName(annoMirror);
            inequalityEncoding.append("is" + simpleName + "[v2] = false <- inequalityConstraint(v1, v2), is"
                    + simpleName + "[v1] = true.\n");
            inequalityEncoding.append("is" + simpleName
                    + "[v2] = false <- inequalityConstraintContainsConstant(v1, v2), hasconstantName(v1:\""
                    + simpleName + "\").\n");
        }
        return inequalityEncoding.toString();
    }
    
    private String getSubTypeConstraintEncoding() {
        StringBuilder subtypeEncoding = new StringBuilder();
        String topTypeStr = getSimpleName(Lattice.top);
        String bottomTypeStr = getSimpleName(Lattice.bottom);
        subtypeEncoding.append("is" + topTypeStr + "[v2] = true <- subtypeConstraint(v1, v2), is" + topTypeStr + "[v1] = true.\n");
        subtypeEncoding.append("is" + topTypeStr+ "[v2] = true <- subtypeConstraintLeftConstant(v1, v2), hasconstantName(v1:\"" + topTypeStr + "\").\n");
        subtypeEncoding.append("is" + bottomTypeStr + "[v1] = true <- subtypeConstraint(v1, v2), is" + bottomTypeStr + "[v2] = true.\n");
        subtypeEncoding.append("is" + bottomTypeStr+ "[v1] = true <- subtypeConstraintRightConstant(v1, v2), hasconstantName(v2:\"" + bottomTypeStr + "\").\n\n");
        
        for (Map.Entry<AnnotationMirror, Collection<AnnotationMirror>> entry : Lattice.subType.entrySet()) {
            String superTypeName = getSimpleName(entry.getKey());
            for (AnnotationMirror subType : entry.getValue()) {
                String subTypeName = getSimpleName(subType);
                if (!superTypeName.equals(subTypeName)) {
                    subtypeEncoding.append("is" + subTypeName + "[v2] = false <- subtypeConstraint(v1, v2), is" + superTypeName + "[v1] = true.\n");
                    subtypeEncoding.append("is" + subTypeName + "[v2] = false <- subtypeConstraintLeftConstant(v1, v2), hasconstantName(v1:\"" + superTypeName + "\").\n");
                }
            }
        }
        subtypeEncoding.append("\n");
        // duplicate code for easy understanding
        for (Map.Entry<AnnotationMirror, Collection<AnnotationMirror>> entry : Lattice.superType.entrySet()) {
            String subTypeName = getSimpleName(entry.getKey());
            for (AnnotationMirror superType : entry.getValue()) {
                String superTypeName = getSimpleName(superType);
                if (!superTypeName.equals(subTypeName)) {
                    subtypeEncoding.append("is" + superTypeName + "[v1] = false <- subtypeConstraintRightConstant(v1, v2), hasconstantName(v2:\"" + subTypeName + "\").\n");
                }
            }
        }
        subtypeEncoding.append("\n");
        return subtypeEncoding.toString();
    }
    
    private String getComparableConstraintEncoding() {
        StringBuilder ComparableEncoding = new StringBuilder();
        // duplicate code for easy understanding
        for (Map.Entry<AnnotationMirror, Collection<AnnotationMirror>> entry : Lattice.incomparableType.entrySet()) {
            String incompType1Name = getSimpleName(entry.getKey());
            for (AnnotationMirror incomparableType2 : entry.getValue()) {
                String incompType2Name = getSimpleName(incomparableType2);
                ComparableEncoding.append("is" + incompType2Name + "[v1] = false <- subtypeConstraintRightConstant(v1, v2), hasconstantName(v2:\"" + incompType1Name + "\").\n");
            }
        }
        
        return ComparableEncoding.toString();
    }
    
    private String getBasicEncoding() {
        StringBuilder basicEncoding = new StringBuilder();
        basicEncoding.append("variable(v), hasvariableName(v:i) -> int(i).\n");
        basicEncoding.append("constant(m), hasconstantName(m:i) -> string(i).\n");
        basicEncoding.append("AnnotationOf[v] = a -> variable(v), string(a).\n");
        //predicates for making output in order.
        basicEncoding.append("variableOrder(v) -> int(v).\n");
        basicEncoding.append("variableOrder(i) <- variable(v), hasvariableName(v:i).\n");
        basicEncoding.append("orderVariable[o] = v -> int(o), int(v).\n");
        basicEncoding.append("orderVariable[o] = v <- seq<<o=v>> variableOrder(v).\n");
        basicEncoding.append("orderedAnnotationOf[v] = a -> int(v), string(a).\n");
        basicEncoding.append("orderedAnnotationOf[v] = a <- variable(q), hasvariableName(q:v), AnnotationOf[q]=a, orderVariable[_]=v.\n");
        //predicates for constraints.
        //equality constraint
        basicEncoding.append("equalityConstraint(v1,v2) -> variable(v1), variable(v2).\n");
        basicEncoding.append("equalityConstraintContainsConstant(v1,v2) -> constant(v1), variable(v2).\n");
        //inequality constraint
        basicEncoding.append("inequalityConstraint(v1,v2) -> variable(v1), variable(v2).\n");
        basicEncoding.append("inequalityConstraintContainsConstant(v1,v2) -> constant(v1), variable(v2).\n");
        //subtype constraint
        basicEncoding.append("subtypeConstraint(v1,v2) -> variable(v1), variable(v2).\n");
        basicEncoding.append("subtypeConstraintLeftConstant(v1,v2) -> constant(v1), variable(v2).\n");
        basicEncoding.append("subtypeConstraintRightConstant(v1,v2) -> variable(v1), constant(v2).\n");
        //comparable constraint
        basicEncoding.append("comparableConstraint(v1,v2) -> variable(v1), variable(v2).\n");
        basicEncoding.append("comparableConstraintContainsConstant(v1,v2) -> constant(v1), variable(v2).\n");
        // each type
        for (AnnotationMirror annoMirror : Lattice.allTypes) {
            basicEncoding.append("is" + getSimpleName(annoMirror) + "[v] = i -> variable(v), boolean(i).\n");
        }
        for (AnnotationMirror annoMirror : Lattice.allTypes) {
            String simpleName = getSimpleName(annoMirror);
            basicEncoding.append("AnnotationOf[v] = \"" + simpleName + "\" <- " + "is" + simpleName + "[v] = true.\n");
        }
        for (AnnotationMirror rightAnnoMirror : Lattice.allTypes) {
            for (AnnotationMirror leftAnnoMirror : Lattice.allTypes) {
                String leftAnnoName = getSimpleName(leftAnnoMirror);
                String rightAnnoName = getSimpleName(rightAnnoMirror);
                if (!leftAnnoName.equals(rightAnnoMirror)) {
                    basicEncoding.append("is" + leftAnnoName + "[v] = false <- is" + rightAnnoName + "[v] = true.\n");
                }
                
            }
        }
        return basicEncoding.toString();
    }

    private String getSimpleName(AnnotationMirror annoMirror) {
        return AnnotationUtils.annotationSimpleName(annoMirror).toString();
    }
    
    /**
     * write all encoding generated by this class to file LogiqlEncoding.logic.
     *
     *
     */
    private void writeFile(String output) {
        try {
            String writePath = path + "/logiqlEncoding.logic";
            File f = new File(writePath);
            PrintWriter pw = new PrintWriter(writePath);
            pw.write(output);
            pw.close();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
