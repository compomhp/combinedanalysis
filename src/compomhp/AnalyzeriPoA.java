package compomhp;

import java.util.Set;

import soot.jimple.AssignStmt;
import soot.jimple.InvokeStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.Stmt;

public class AnalyzeriPoA extends Analyzer{

	public void init(Generator gen, FunctionalConstraint callerFc) {
		this.callerFc = callerFc;
		ptConsGen = new GenConsPointsTo();
		((GenConsPointsTo)ptConsGen).setFieldMap(MapName.ifieldPts);
		((GenConsPointsTo)ptConsGen).setVarMap(MapName.ivarPts);
		ptConsGen.gen = gen;
		this.gen = gen;
		ptConsGen.callerFc = callerFc;
		((GenConsPointsTo)ptConsGen).genPointsToOnly = true;
		args = Solver.v().arg;
	}

	@Override
	public void genEveryMethod() {
		ptConsGen.genEveryMethod();
		
	}
	@Override
	public void genProcessed() {
		ptConsGen.genProcessed();
		
	}
	@Override
	public void genThreadRun(Stmt s1) {
		// TODO Auto-generated method stub
		ptConsGen.genThreadRun(s1);
		
	}
	@Override
	public void genFieldCons() {
		ptConsGen.genFieldCons();
		
	}
	@Override
	public void setCallerFc(FunctionalConstraint callerFc) {
		this.callerFc = callerFc;
		ptConsGen.callerFc = callerFc;
		
	}
	@Override
	public Analyzer getAnalyzer() {
		
		return new AnalyzeriPoA();
	}
	

}
