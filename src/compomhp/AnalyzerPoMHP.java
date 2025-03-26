package compomhp;

import java.util.Set;

import soot.jimple.AssignStmt;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.ExitMonitorStmt;
import soot.jimple.InvokeStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.Stmt;

public class AnalyzerPoMHP extends Analyzer {

	@Override
	public void init(Generator gen, FunctionalConstraint callerFc) {
		this.callerFc = callerFc;
		ptConsGen = new GenConsPointsTo();
		ptConsGen.gen = gen;
		ptConsGen.callerFc = callerFc;
		this.gen = gen;
		((GenConsPointsTo)ptConsGen).setFieldMap(MapName.ifieldPts);
		mhpConsGen = new GenConsMHP();
		mhpConsGen.gen = gen;
		mhpConsGen.callerFc = callerFc;
		args = Solver.v().arg;
	}

	
	@Override
	public void genEveryMethod() {
		ptConsGen.genEveryMethod();
		mhpConsGen.genEveryMethod();
		
	}
	@Override
	public void genProcessed() {
		ptConsGen.genProcessed();
		mhpConsGen.genProcessed();
	}
	@Override
	public void genThreadRun(Stmt s1) {
		mhpConsGen.genThreadRun(s1);
		
	}
	@Override
	public void genFieldCons() {
		ptConsGen.genFieldCons();
		
	}
	@Override
	public void setCallerFc(FunctionalConstraint callerFc) {
		this.callerFc = callerFc;
		ptConsGen.callerFc = callerFc;
		mhpConsGen.callerFc = callerFc;
		
	}

	@Override
	public Analyzer getAnalyzer() {
		return new AnalyzerPoMHP();
	}

	
	public void genForAllSt(Stmt s1) {
		 ((GenConsPointsTo)ptConsGen).genVarPCopy(s1);
	 }
}
