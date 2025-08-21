package compomhp;

import java.util.Set;

import soot.Body;
import soot.SootClass;
import soot.jimple.AssignStmt;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.ExitMonitorStmt;
import soot.jimple.InvokeStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.Stmt;

public abstract class Analyzer {
	GenConsPointsTo ptConsGen;
	GenConsMHP mhpConsGen;
	FunctionalConstraint callerFc;
	Body b;
	Arg args;
	Generator gen;
	/*
	 * Initialize with appropriate ptConsGen and mhpConsGen
	 */
	public abstract void init(Generator gen, FunctionalConstraint callerFc);
	//public abstract void gen(Stmt s1, Set<Stmt> succs, Set<Stmt> preds, StmtType type);
	public abstract void genEveryMethod();
	public abstract void genProcessed(); 
	public abstract void genThreadRun(Stmt s1);
	public abstract void genFieldCons();
	public abstract void setCallerFc(FunctionalConstraint callerFc);
	public abstract Analyzer getAnalyzer();
	
	public void gen(Stmt s1, Set<Stmt> succs, Set<Stmt> preds, StmtType type) {
		
		if(args.poa && ptConsGen.getVarMap()==MapName.varPts)
			genForAllSt(s1);
		if(args.esc && succs!=null)
			addForEverySeq(s1,succs);
		switch(type) {
		case assign :
			if(args.poa)
			ptConsGen.gen((AssignStmt)s1, preds);
			else {
				if(s1.containsInvokeExpr())
					ptConsGen.gen((AssignStmt)s1, preds);
			}
			if(args.mhp && gen.hasParallelConst)
			mhpConsGen.gen((AssignStmt)s1, succs);

			break;
		case invoke :
		case start :
		case join :
		case notify :
		case wait:
		case submit:
		case execute:
		case invokeAll:
		case invokeAny:
			
			ptConsGen.gen((InvokeStmt)s1, preds);
			if(args.mhp && gen.hasParallelConst)
			mhpConsGen.gen((InvokeStmt)s1, succs);

			break;
		case retVoid :
			if(args.poa)
			ptConsGen.gen((ReturnVoidStmt)s1, preds);
			if(args.mhp && gen.hasParallelConst)
			mhpConsGen.gen((ReturnVoidStmt)s1, succs);

			break;
		case ret :
			if(args.poa)
			ptConsGen.gen((ReturnStmt)s1, preds);
			if(args.mhp && gen.hasParallelConst)
			mhpConsGen.gen((ReturnStmt)s1, succs);

			break;
		case enterMonitor :
			if(args.poa)
			ptConsGen.gen((EnterMonitorStmt)s1,preds);
			if(args.mhp)
			mhpConsGen.gen((EnterMonitorStmt)s1, succs);
			break;
		case exitMonitor :

			if(args.mhp)
			mhpConsGen.gen((ExitMonitorStmt)s1, succs);
			break;
		default :
			/*
			 * uninteresting head
			 */
			if(args.poa)
			ptConsGen.genDefault(s1, preds);
			if(args.mhp && gen.hasParallelConst)
			mhpConsGen.genDefault(s1, succs);
			
			break;
			
		}

	}
	public void addConsToSolverLists() {
		Solver solver = Solver.v();
		solver.memCons.addAll(callerFc.fmem);
		solver.propCons.addAll(callerFc.fprop);
		solver.condCons.addAll(callerFc.fcond);
		solver.funCons.addAll(callerFc.ffunc);

	}
	 public void addForEverySeq(Stmt from,Set<Stmt> toSet) {

		 if(Solver.v().arg.esc) {
			 for(Stmt to : toSet) {
		    		PropagateConstraint escCopy = new PropagateConstraint(from,to, MapName.escapeAt, MapName.escapeAt, ConstType.depOnPts);
		    		callerFc.addPropagate(escCopy);
		    	}
		 }
		 
	}
	 public void genForAllSt(Stmt s1) {
//		 if(solver.arg.fs)
//		 ptConsGen.genVarPCopy(s1);
	 }
	
}
