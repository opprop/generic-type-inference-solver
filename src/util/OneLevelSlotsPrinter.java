package util;

import checkers.inference.model.CombVariableSlot;
import checkers.inference.model.CombineConstraint;
import checkers.inference.model.ComparableConstraint;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.EqualityConstraint;
import checkers.inference.model.ExistentialConstraint;
import checkers.inference.model.ExistentialVariableSlot;
import checkers.inference.model.InequalityConstraint;
import checkers.inference.model.LubVariableSlot;
import checkers.inference.model.PreferenceConstraint;
import checkers.inference.model.RefinementVariableSlot;
import checkers.inference.model.Serializer;
import checkers.inference.model.Slot;
import checkers.inference.model.SubtypeConstraint;
import checkers.inference.model.VariableSlot;
import checkers.inference.model.serialization.ToStringSerializer;

import java.util.HashSet;
import java.util.Set;

/**
 * Created by mier on 04/08/17.
 * Non-transitively prints all slots in a constraint. Each slot is only printed once.
 */
public final class OneLevelSlotsPrinter implements Serializer<String, Void> {

    /**Delegatee that serializes slots to string representation.*/
    private final ToStringSerializer toStringSerializer;
    private final Set<Slot> printedSlots;


    public OneLevelSlotsPrinter(final ToStringSerializer toStringSerializer) {
        this.toStringSerializer = toStringSerializer;
        printedSlots = new HashSet<>();
    }

    private void printSlotIfNotPrinted(Slot slot) {
        if (!printedSlots.contains(slot) && !(slot instanceof ConstantSlot)) {
            System.out.println("\t" + slot.serialize(this) + " \n\t    " + slot.getLocation().toString() + "\n");
            printedSlots.add(slot);
        }
    }

    @Override
    public Void serialize(SubtypeConstraint constraint) {
        printSlotIfNotPrinted(constraint.getSubtype());
        printSlotIfNotPrinted(constraint.getSupertype());
        return null;// Make compiler happy
    }

    @Override
    public Void serialize(EqualityConstraint constraint) {
        printSlotIfNotPrinted(constraint.getFirst());
        printSlotIfNotPrinted(constraint.getSecond());
        return null;
    }

    @Override
    public Void serialize(ExistentialConstraint constraint) {
        printSlotIfNotPrinted(constraint.getPotentialVariable());
        return null;
    }

    @Override
    public Void serialize(InequalityConstraint constraint) {
        printSlotIfNotPrinted(constraint.getFirst());
        printSlotIfNotPrinted(constraint.getSecond());
        return null;
    }

    @Override
    public Void serialize(ComparableConstraint comparableConstraint) {
        printSlotIfNotPrinted(comparableConstraint.getFirst());
        printSlotIfNotPrinted(comparableConstraint.getSecond());
        return null;
    }

    @Override
    public Void serialize(CombineConstraint combineConstraint) {
        printSlotIfNotPrinted(combineConstraint.getResult());
        printSlotIfNotPrinted(combineConstraint.getTarget());
        printSlotIfNotPrinted(combineConstraint.getDeclared());
        return null;
    }

    @Override
    public Void serialize(PreferenceConstraint preferenceConstraint) {
        printSlotIfNotPrinted(preferenceConstraint.getVariable());
        return null;
    }

    /*Use Decorator pattern to delegate slots serialization to ToStringSerializer*/
    @Override
    public String serialize(VariableSlot slot) {
        return toStringSerializer.serialize(slot);
    }

    @Override
    public String serialize(ConstantSlot slot) {
        return toStringSerializer.serialize(slot);
    }

    @Override
    public String serialize(ExistentialVariableSlot slot) {
        return toStringSerializer.serialize(slot);
    }

    @Override
    public String serialize(RefinementVariableSlot slot) {
        return toStringSerializer.serialize(slot);
    }

    @Override
    public String serialize(CombVariableSlot slot) {
        return toStringSerializer.serialize(slot);
    }

    @Override
    public String serialize(LubVariableSlot slot) {
        return toStringSerializer.serialize(slot);
    }

}
