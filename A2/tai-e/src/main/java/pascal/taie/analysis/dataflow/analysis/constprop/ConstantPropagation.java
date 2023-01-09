/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact boundaryFact = new CPFact();
        for (Stmt stmt : cfg) {
            if (stmt.getDef().isPresent() && stmt.getDef().get() instanceof Var var && canHoldInt(var)) {
                boundaryFact.update(var, Value.getNAC());
            }
            for (RValue use : stmt.getUses()) {
                if (use instanceof Var var && canHoldInt(var)) {
                    boundaryFact.update(var, Value.getNAC());
                } else if (use instanceof BinaryExp binaryExp) {
                    if (canHoldInt(binaryExp.getOperand1())) {
                        boundaryFact.update(binaryExp.getOperand1(), Value.getNAC());
                    }
                    if (canHoldInt(binaryExp.getOperand2())) {
                        boundaryFact.update(binaryExp.getOperand2(), Value.getNAC());
                    }
                }
                // intLiteral or others, no need to add
            }
        }
        return boundaryFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach((var, value) -> {
            assert canHoldInt(var);
            Value tv = target.get(var);
            target.update(var, meetValue(value, tv));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC()) {
            return Value.getNAC();
        } else if (v1.isConstant()) {
            if (v2.isNAC() || v2.isConstant() && v1.getConstant() != v2.getConstant()) {
                // c meet NAC, c1 meet c2
                return Value.getNAC();
            } else {
                // c meet undefined, c meet c
                return v1;
            }
        } else {
            // v1 = undefined
            return v2;
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        boolean change = false;
        if (stmt.getDef().isPresent() && stmt.getDef().get() instanceof Var var && canHoldInt(var)) {
            for (RValue use : stmt.getUses()) {
                change = change || out.update(var, evaluate(use, in));
            }
        }
        return change;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof Var var) {
            return canHoldInt(var) ? in.get(var) : Value.getNAC();
        } else if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        } else if (exp instanceof BinaryExp binaryExp) {
            if (canHoldInt(binaryExp.getOperand1()) && canHoldInt(binaryExp.getOperand2())) {
                Value v1 = in.get(binaryExp.getOperand1());
                Value v2 = in.get(binaryExp.getOperand2());
                if (v1.isConstant() && v2.isConstant()) {
                    if (exp instanceof ArithmeticExp arithmeticExp) {
                        return switch (arithmeticExp.getOperator()) {
                            case ADD -> Value.makeConstant(v1.getConstant() + v2.getConstant());
                            case SUB -> Value.makeConstant(v1.getConstant() - v2.getConstant());
                            case DIV -> Value.makeConstant(v1.getConstant() / v2.getConstant());
                            case MUL -> Value.makeConstant(v1.getConstant() * v2.getConstant());
                            case REM -> Value.makeConstant(v1.getConstant() % v2.getConstant());
                        };
                    } else if (exp instanceof BitwiseExp bitwiseExp) {
                        return switch (bitwiseExp.getOperator()) {
                            case OR -> Value.makeConstant(v1.getConstant() | v2.getConstant());
                            case AND -> Value.makeConstant(v1.getConstant() & v2.getConstant());
                            case XOR -> Value.makeConstant(v1.getConstant() ^ v2.getConstant());
                        };
                    } else if (exp instanceof ConditionExp conditionExp) {
                        return switch (conditionExp.getOperator()) {
                            case EQ -> Value.makeConstant(v1.getConstant() == v2.getConstant() ? 1 : 0);
                            case NE -> Value.makeConstant(v1.getConstant() != v2.getConstant() ? 1 : 0);
                            case LT -> Value.makeConstant(v1.getConstant() < v2.getConstant() ? 1 : 0);
                            case GT -> Value.makeConstant(v1.getConstant() > v2.getConstant() ? 1 : 0);
                            case LE -> Value.makeConstant(v1.getConstant() <= v2.getConstant() ? 1 : 0);
                            case GE -> Value.makeConstant(v1.getConstant() >= v2.getConstant() ? 1 : 0);
                        };
                    } else if (exp instanceof ShiftExp shiftExp) {
                        return switch (shiftExp.getOperator()) {
                            case SHL -> Value.makeConstant(v1.getConstant() << v2.getConstant());
                            case SHR -> Value.makeConstant(v1.getConstant() >> v2.getConstant());
                            case USHR -> Value.makeConstant(v1.getConstant() >>> v2.getConstant());
                        };
                    } else {
                        return Value.getNAC();
                    }
                } else if (v1.isNAC() || v2.isNAC()) {
                    return Value.getNAC();
                } else {
                    return Value.getUndef();
                }
            } else {
                return Value.getNAC();
            }
        } else {
            // other cases
            return Value.getNAC();
        }
    }
}
