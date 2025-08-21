package compomhp;

import java.util.Set;

import soot.jimple.AssignStmt;
import soot.jimple.InvokeStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.Stmt;

/*
 * Flow sensitive Points-to analysis
 * Because we assume trivial MHP, the field updates are insensitive.
 * 
 */
public class AnalyzerPoA extends Analyzer{
	public void init(Generator gen, FunctionalConstraint callerFc) {
		this.callerFc = callerFc;
		ptConsGen = new GenConsPointsTo();
		ptConsGen.gen = gen;
		ptConsGen.callerFc = callerFc;
		((GenConsPointsTo)ptConsGen).genPointsToOnly = true;
		args = Solver.v().arg;
		if(!args.usePrevMHP)
		((GenConsPointsTo)ptConsGen).setFieldMap(MapName.ifieldPts);
		
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
		
		return new AnalyzerPoA();
	}
	
	public void genForAllSt(Stmt s1) {
		 ((GenConsPointsTo)ptConsGen).genVarPCopy(s1);
	 }

}
