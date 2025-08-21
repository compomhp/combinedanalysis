package compomhp;

import java.util.Set;

import soot.jimple.AssignStmt;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.ExitMonitorStmt;
import soot.jimple.InvokeStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.Stmt;

public class AnalyzeriPoMHP extends Analyzer {

	@Override
	public void init(Generator gen, FunctionalConstraint callerFc) {
		this.callerFc = callerFc;
		ptConsGen = new GenConsPointsTo();
		((GenConsPointsTo)ptConsGen).setVarMap(MapName.ivarPts);
		((GenConsPointsTo)ptConsGen).setFieldMap(MapName.ifieldPts);
		ptConsGen.gen = gen;
		ptConsGen.callerFc = callerFc;
		this.gen = gen;
		mhpConsGen = new GenConsMHP();
		mhpConsGen.gen = gen;
		((GenConsMHP)mhpConsGen).setVarMap(MapName.ivarPts);
		((GenConsMHP)mhpConsGen).setFieldMap(MapName.ifieldPts);
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
		ptConsGen.genThreadRun(s1);
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
		return new AnalyzeriPoMHP();
	}

	

}
