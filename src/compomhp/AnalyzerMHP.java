package compomhp;

import soot.jimple.Stmt;

public class AnalyzerMHP extends Analyzer{

	@Override
	public void init(Generator gen, FunctionalConstraint callerFc) {
		// TODO Auto-generated method stub
		this.callerFc = callerFc;
		ptConsGen = new GenConsPointsTo();
		ptConsGen.gen = gen;
		ptConsGen.callerFc = callerFc;
		this.gen = gen;
		mhpConsGen = new GenConsMHP();
		mhpConsGen.gen = gen;
		((GenConsMHP)mhpConsGen).setVarMap(MapName.varPts);
		mhpConsGen.callerFc = callerFc;
		args = Solver.v().arg;
	}
	
	@Override
	public void genEveryMethod() {
		
		mhpConsGen.genEveryMethod();
		
	}
	@Override
	public void genProcessed() {
		
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
		return new AnalyzerMHP();
	}

	
}
