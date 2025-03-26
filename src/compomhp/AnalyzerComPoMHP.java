package compomhp;

import java.util.Set;

import soot.jimple.AssignStmt;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.ExitMonitorStmt;
import soot.jimple.InvokeStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.Stmt;

/*
 * Flow sensitive Combined MHP and Points-to analysis
 */
public class AnalyzerComPoMHP extends Analyzer {
	
	public void init(Generator gen, FunctionalConstraint callerFc) {
		this.callerFc = callerFc;
		ptConsGen = new GenConsPointsTo();
		ptConsGen.gen = gen;
		this.gen = gen;
		ptConsGen.callerFc = callerFc;
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
		
		return new AnalyzerComPoMHP();
	}
	
//	@Override
//	public void addConsToSolverLists() {
//		Solver solver = Solver.v();
//		addToMap(callerFc.fmem, solver.memConsMap);
//		addToMap(callerFc.fprop, solver.propConsMap);
//		addToMap(callerFc.fcond, solver.condConsMap);
//		addToMap(callerFc.ffunc, solver.funConsMap);
//		addToMap(callerFc.laterCons, solver.processLaterConsMap );
//		solver.memCons.addAll(solver.memConsMap.get(ConstType.pts));
//		solver.memConsMap.get(ConstType.pts).clear();
//		solver.propCons.addAll(solver.propConsMap.get(ConstType.pts));
//		solver.propConsMap.get(ConstType.pts).clear();
//		solver.condCons.addAll(solver.condConsMap.get(ConstType.pts));
//		solver.condConsMap.get(ConstType.pts).clear();
//		solver.funCons.addAll(solver.funConsMap.get(ConstType.pts));
//		solver.funConsMap.get(ConstType.pts).clear();
//		solver.processLaterCons.addAll(solver.processLaterConsMap.get(ConstType.pts));
//		solver.processLaterConsMap.get(ConstType.pts).clear();
//	}
//	 public void addToMap(ArrayList<ConstraintPar> ar, Map<ConstType,ArrayList<ConstraintPar>> mp) {
//	    	for(ConstraintPar c: ar) {
//	    		mp.get(c.constType).add(c);
//	    	}
//	    }
	 public void addForEverySeq(Stmt from,Set<Stmt> toSet) {
//		 ((GenConsPointsTo)ptConsGen).genVarPCopy(from);
		 if(Solver.v().arg.esc) {
			 for(Stmt to : toSet) {
	//			PropagateConstraint invMethStmtsCopy = new PropagateConstraint(from,to, MapName.invMethStmts, MapName.invMethStmts, ConstType.depOnPts);
	//	    	callerFc.addPropagate(invMethStmtsCopy);
		    	
		    		PropagateConstraint escCopy = new PropagateConstraint(from,to, MapName.escapeAt, MapName.escapeAt, ConstType.depOnPts);
		    		callerFc.addPropagate(escCopy);
		    	}
		 }
		 
	}
	 public void genForAllSt(Stmt s1) {
		 ((GenConsPointsTo)ptConsGen).genVarPCopy(s1);
	 }
}
