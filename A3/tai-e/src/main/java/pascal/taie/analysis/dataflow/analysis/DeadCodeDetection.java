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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // unreachable detect
        Set<Stmt> reachable = new HashSet<>();
        Queue<Stmt> bfsQueue = new LinkedList<>();
        reachable.add(cfg.getEntry());
        bfsQueue.add(cfg.getEntry());
        while (!bfsQueue.isEmpty()) {
            Stmt stmt = bfsQueue.remove();
            CPFact inConstant = constants.getInFact(stmt);
            if (stmt instanceof If ifStmt) {
                Value value = ConstantPropagation.evaluate(ifStmt.getCondition(), inConstant);
                for (Edge<Stmt> edge : cfg.getOutEdgesOf(ifStmt)) {
                    if (reachable.contains(edge.getTarget())
                            || value.isConstant() && value.getConstant() != 0
                            && edge.getKind().equals(Edge.Kind.IF_FALSE)
                            || value.isConstant() && value.getConstant() == 0
                            && edge.getKind().equals(Edge.Kind.IF_TRUE)) {
                        continue;
                    }
                    reachable.add(edge.getTarget());
                    bfsQueue.add(edge.getTarget());
                }
            } else if (stmt instanceof SwitchStmt switchStmt) {
                Value value = ConstantPropagation.evaluate(switchStmt.getVar(), inConstant);
                for (Edge<Stmt> edge : cfg.getOutEdgesOf(switchStmt)) {
                    if (reachable.contains(edge.getTarget())
                            || value.isConstant() && edge.isSwitchCase()
                            && value.getConstant() != edge.getCaseValue()
                            || value.isConstant() && edge.getKind().equals(Edge.Kind.SWITCH_DEFAULT)
                            && switchStmt.getCaseValues().contains(value.getConstant())) {
                        continue;
                    }
                    reachable.add(edge.getTarget());
                    bfsQueue.add(edge.getTarget());
                }
            } else {
                for (Stmt succ : cfg.getSuccsOf(stmt)) {
                    if (!reachable.contains(succ)) {
                        reachable.add(succ);
                        bfsQueue.add(succ);
                    }
                }
            }
        }
        // not live var and dead code
        for (Stmt stmt : cfg) {
            // ? 为什么会删除return这些的语句  TODO bug??
            if (stmt instanceof DefinitionStmt ds && hasNoSideEffect(ds.getRValue())) {
                if (!reachable.contains(stmt) || ds.getLValue() instanceof Var var &&
                        !liveVars.getOutFact(stmt).contains(var)) {
                    deadCode.add(stmt);
                }
            }
        }
        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
