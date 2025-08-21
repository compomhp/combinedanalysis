package compomhp;

import java.util.Set;

import soot.Local;
import soot.SootClass;
import soot.jimple.AssignStmt;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.ExitMonitorStmt;
import soot.jimple.InvokeStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.Stmt;

public abstract class GenCons {
	Solver solver = Solver.v();
	Generator gen;
	FunctionalConstraint callerFc;
	MapName varMap = MapName.varPts;
	MapName fieldMap = MapName.fieldPts;
	
	abstract public void gen(AssignStmt s1, Set<Stmt> succs);
	abstract public void gen(InvokeStmt s1, Set<Stmt> succs);
	abstract public void gen(ReturnStmt s1,Set<Stmt> succs);
	abstract public void gen(ReturnVoidStmt s1, Set<Stmt> succs);
	abstract public void gen(EnterMonitorStmt s1, Set<Stmt> succs);
	abstract public void gen(ExitMonitorStmt s1, Set<Stmt> succs);
	abstract public void genDefault(Stmt s1, Set<Stmt> succs);
	protected void genEveryMethod() {
		Stmt head = (Stmt)callerFc.b.getUnits().getFirst();
		if(callerFc.threadStart) {
			
			genThreadRun(head);
//			hasParallelConst = true;
			solver.runs.put(callerFc.method,callerFc.method);
		}
		
		else if(callerFc.loadRunCall) {
			genThreadRun(head);
//			hasParallelConst = true;
//			if(callerFc.method.getName().equals("run")) {
//				solver.runs.put(callerFc.method,callerFc.method);
//			}
//			else
				solver.runOrCall.put(callerFc.method,callerFc.method);
			System.out.println("Callable or Runnable loaded:"+callerFc.method.getSignature());
		}
		else if(callerFc.method.getName().equals("run")) {
			SootClass sc = callerFc.method.getDeclaringClass();
			
			if(gen.isThreadClass(sc)) {
//				hasParallelConst = true;
				genThreadRun(head);
				solver.runs.put(callerFc.method,callerFc.method);
//				/solver.numruns++;
				System.out.println("Thread run method"+callerFc.method.getSignature()+" caller: "+callerFc.caller.method.getSignature());
			}
		}
	}
	abstract public void genProcessed();
	abstract public void genThreadRun(Stmt s1);
	abstract public void genFieldCons();
	public abstract void countPtsInfo();
	public abstract void countMonomorphic();
	public abstract void countCallEdges();
	public abstract MapName getVarMap();
	public abstract MapName getFieldMap();
	public Object getKey(Stmt s, Local l) {
		Object key;
		if(varMap == MapName.varPts) {
			key = new StmtLocal(s,l);
		}
		else
			key = l;
		return key;
	}
}
