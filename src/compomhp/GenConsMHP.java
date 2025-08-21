package compomhp;

import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;

import soot.Body;
import soot.IntType;
import soot.Local;
import soot.LongType;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Value;
import soot.VoidType;
import soot.jimple.AssignStmt;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.ExitMonitorStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;

public class GenConsMHP extends GenCons{
	
	public void setVarMap(MapName varMap) {
		this.varMap = varMap; 
	}
	public void setFieldMap(MapName fieldMap) {
		this.fieldMap = fieldMap; 
	}
	@Override
	public void gen(AssignStmt s1, Set<Stmt> succs) {
		if(s1.containsInvokeExpr()) {
			InvokeExpr ie = s1.getInvokeExpr();
			gen(s1,ie,succs);
		}
		else {
			addMHPRelConsSet(s1, succs, false);
		}
		
	}

	@Override
	public void gen(InvokeStmt s1, Set<Stmt> succs) {
		InvokeExpr ie = s1.getInvokeExpr();
		gen(s1,ie,succs);
		
	}

	@Override
	public void gen(ReturnStmt s1, Set<Stmt> succs) {
		addMHPRelConsSet(s1, succs, false);
		if(callerFc.caller!=null && callerFc.callSiteSuccs != null)
			genRetMHPToCaller(s1,callerFc.caller.method, callerFc.callSiteSuccs);
	}

	@Override
	public void gen(ReturnVoidStmt s1, Set<Stmt> succs) {
		addMHPRelConsSet(s1, succs, false);
		if(callerFc.caller!=null && callerFc.callSiteSuccs != null)
			genRetMHPToCaller(s1,callerFc.caller.method, callerFc.callSiteSuccs);
	}
	
	@Override
	public void gen(EnterMonitorStmt s1, Set<Stmt> succs) {
		Value value = s1.getOp();
		
		
	     
	    	
//	        populateMonitorStmts(s1);
//	        if(!solver.mustNodes.containsKey(callerFc.method)) {
//				solver.mustNodes.put(callerFc.method, new HashSet<>());
//			}
	        Object ls = getKey(s1, (Local)value);
	        
	       
	        
	       if(solver.arg.combined) {
	    	
    		for(Stmt s2 : succs) {
        		

	        	PropagateConstraint syncMhpCopy = new PropagateConstraint(s1,s2, MapName.MHP, MapName.MHP, ConstType.mhp);
	        	MemConstraint sinkills1 = new MemConstraint(null, s1, false, MapName.kill, ConstType.depOnPts);

	        	MemConstraint sinMHPs2 = new MemConstraint(null, s2, false, MapName.MHP, ConstType.depOnPts);
	        	ConditionalConstraint mustS = new ConditionalConstraint(null, sinkills1, MapName.must, sinMHPs2, ConstType.depOnPts);
//	        	mustS.name = ConstraintName.INTERFACE_INVOKE;
	        	ConditionalConstraint sinSyncr = new ConditionalConstraint(null, mustS, MapName.syncHA, sinMHPs2, ConstType.depOnPts);
	        	sinSyncr.isExistsCond = true;
	        	sinSyncr.useOuterCondObj = true;
//	        	if(callerFc.method.getSignature().equals("<newtests.examples.T: void run()>")) {
//	        	sinSyncr.name = ConstraintName.A_NEW;
//	        	}
	        	ConditionalConstraint sinMHPs1 = new ConditionalConstraint(s1, sinSyncr, MapName.MHP, null, ConstType.depOnPts);
//	        	sinMHPs1.name=ConstraintName.SPECIAL_INVOKE;
				ConditionalConstraint mustR = new ConditionalConstraint(ls, sinMHPs1, MapName.must, syncMhpCopy, ConstType.depOnPts);
				
	        	ConditionalConstraint syncMHP = new ConditionalConstraint(ls, mustR, varMap,null, ConstType.depOnPts);
	        	
	        	callerFc.addConditional(syncMHP);
//	        	callerFc.addPropagate(syncMhpCopy);

        	}
	       }
	       else {
	    	   addMHPRelConsSet(s1, succs, false);
	       }
        	
		
	}

	@Override
	public void gen(ExitMonitorStmt s1, Set<Stmt> succs) {
		Value value = s1.getOp();
			/*
			 * get monitor entrance
			 */
			EnterMonitorStmt monitorEntrance = null;
			if(gen.monPairs.containsKey(s1)) {
				monitorEntrance = gen.monPairs.get(s1);
			}
			
				for(Stmt s2 : succs) {
					/*
					 * Transfer MHP and invRun maps
					 */
					PropagateConstraint mhpCopy = new PropagateConstraint(s1,s2, MapName.MHP, MapName.MHP, ConstType.mhp);
		  			callerFc.addPropagate(mhpCopy);
		  			if(monitorEntrance != null) {
		  				
		  				/*
		  				 * Add kill set of monitorEntrance to the MHP of s2
		  				 */
		  				PropagateConstraint killMhpCopy = new PropagateConstraint(monitorEntrance,s2, MapName.kill, MapName.MHP,ConstType.mhp);
		  				callerFc.addConsLater(killMhpCopy);
		  				
		  			}
		  			
		  			
				}
			
	
		
	}
	@Override
	public void genDefault(Stmt s1, Set<Stmt> succs) {
		
		addMHPRelConsSet(s1,succs, false);
		
	}
	public void addMHPRelConsSet(Stmt st, Set<Stmt> succSet, boolean genIncl) {

			if(succSet != null) {
				for(Stmt to : succSet) {
					
			    	addMHPRelCons(st,to);
				}
			}
			
//		}
		if(genIncl) {
				/*
				 * If the st is an invoke statement, all the statements in the included methods 
				 * have same MHP if they do not have parallel constructs
				 */
				PropagateConstraint mhpCopy = new PropagateConstraint(st, null, MapName.MHP, MapName.MHP, ConstType.depOnPts);
				ConditionalConstraint methSt = new ConditionalConstraint(null,mhpCopy , MapName.mhpCopyTo, null, ConstType.depOnPts);
//				ConditionalConstraint checkNoPC = new ConditionalConstraint(null, null, MapName.hasPC, methSt, ConstType.depOnPts);
				ConditionalConstraint inclMeths = new ConditionalConstraint(null, methSt, MapName.reachableFuncs, null, ConstType.depOnPts);
	    		ConditionalConstraint callSiteCond = new ConditionalConstraint(st, inclMeths, MapName.funcsAtCallSite, null, ConstType.depOnPts);
	    		callerFc.addConditional(callSiteCond);
			
		}
		
	}
	public void gen(Stmt s1, InvokeExpr ie, Set<Stmt> succs) {
		boolean interested = false;
		if(ie instanceof InterfaceInvokeExpr) {
		SootMethod method = ie.getMethod();
		Local r = (Local)((InterfaceInvokeExpr)ie).getBase();
		Object ls = getKey(s1, r);
		List paras = method.getParameterTypes();
		addMHPRelConsSet(s1,succs, true);

		}
		else if(ie instanceof VirtualInvokeExpr) {
			Value rcvr = ((VirtualInvokeExpr)ie).getBase();
			SootMethod method = ie.getMethod();
			Type retType = method.getReturnType();
			String name = method.getName();
			List paras = method.getParameterTypes();
			
			Object ls = getKey(s1,(Local)rcvr);
			/*start() method*/
			if (method.getName().equals("start") && retType instanceof VoidType && paras.size() == 0) {
		        boolean threadStart = gen.isThreadClass(method.getDeclaringClass());
		        if(!solver.starts.containsKey(callerFc.method)) {
					solver.starts.put(callerFc.method, new HashSet<>());
				}
				solver.starts.get(callerFc.method).add(s1);
		        if(threadStart) {
		        	interested = true;
		        	
		        	/*
		        	 * MHP(s1) flow into MHP(s2)
		        	 */
		        	addMHPRelConsSet(s1,succs, false);
		        	
		        	
					/*
					 * Add functional constraint for run method 
					 */
		        	if(!solver.arg.poa) {
						Local r = (Local)rcvr;
						FunctionalConstraint fc = new FunctionalConstraint(ConstType.depOnPts);
						fc.callSite = s1;
						fc.callSiteSuccs = succs;
						fc.callSiteSuccs = gen.methInterestingStmts.get(s1);
//						fc.fieldIntSuccs = gen.fieldInterestingStmts.get(s1);
						fc.caller = callerFc;
						fc.threadStart = true;
						ConditionalConstraint startCall = new ConditionalConstraint(ls,fc, varMap, null, ConstType.depOnPts);
						callerFc.addConditional(startCall);
						System.out.println("Constraint start method call: "+method.getSignature()+"for all r in varPts("+r.getName()+"), ");
		        	}
	        
		        }
		      }

			else if(method.getName().equals("join") && retType instanceof VoidType && (paras.size() == 0 || (paras.size() == 1 && (Type) paras.get(0) instanceof LongType)
			          || (paras.size() == 2 && (Type) paras.get(0) instanceof LongType && (Type) paras.get(1) instanceof IntType))) {
			
					boolean threadJoin = gen.isThreadClass(method.getDeclaringClass());
			        if(threadJoin) {
			        	
			        	interested = true;
			        	 if(!solver.joins.containsKey(callerFc.method)) {
								solver.joins.put(callerFc.method, new HashSet<>());
							}
							solver.joins.get(callerFc.method).add(s1);
//							 if(!solver.mustNodes.containsKey(callerFc.method)) {
//									solver.mustNodes.put(callerFc.method, new HashSet<>());
//								}
								
			        	/*
			        	 * this checks that varPts is singleton set and nonSummaryRef
			        	 */
//			        	solver.mustNodes.get(callerFc.method).add(new Node(varMap,ls));
			        	
						if(solver.arg.combined) {
				        	for(Stmt s2 : succs) {
				        		
					        	PropagateConstraint joinMhpCopy = new PropagateConstraint(s1,s2, MapName.MHP, MapName.MHP, ConstType.mhp);
					        	MemConstraint sinMHPs2 = new MemConstraint(null, s2, false, MapName.MHP, ConstType.depOnPts);
					        	
					        	ConditionalConstraint mustS = new ConditionalConstraint(null, null, MapName.must, sinMHPs2, ConstType.depOnPts);
					        	ConditionalConstraint sinRunStmts = new ConditionalConstraint(null, mustS, MapName.runStmtsHA, sinMHPs2, ConstType.depOnPts);
								sinRunStmts.isExistsCond = true;
								sinRunStmts.useOuterCondObj = true;
					        	ConditionalConstraint sinMHPs1 = new ConditionalConstraint(s1, sinRunStmts, MapName.MHP, null, ConstType.depOnPts);
//					        	sinMHPs1.name = ConstraintName.CAST_COPY;
								ConditionalConstraint mustR = new ConditionalConstraint(ls, sinMHPs1, MapName.must, joinMhpCopy, ConstType.depOnPts);
					        	ConditionalConstraint joinMHP = new ConditionalConstraint(ls, mustR, varMap,null, ConstType.depOnPts);
					        	callerFc.addConditional(joinMHP);
	//				        	callerFc.addPropagate(joinMhpCopy);
	
				        	}
						}
						else {
							addMHPRelConsSet(s1, succs, false);
						}
			        }
				
			}
			else if (name.equals("wait") && retType instanceof VoidType && (paras.size() == 0 || (paras.size() == 1 && (Type) paras.get(0) instanceof LongType)
			          || (paras.size() == 2 && (Type) paras.get(0) instanceof LongType && (Type) paras.get(1) instanceof IntType))) {
				/*
				 * No need to check if it is thread class as wait, notify, notifyAll methods are of java.lang.Object class and are final and can't be overridden
				 */

			      
				interested = true;
				/*
				 * Add statements that are present only in the current monitor to the kill set
				 * Check if the leaders of s1 is singleton (must info).
				 * If so, add all its monitor statements to kill set
				 */
				if(!solver.waits.containsKey(callerFc.method)) {
					solver.waits.put(callerFc.method, new HashSet<>());
				}

				solver.waits.get(callerFc.method).add(s1);
				/*
				 * As S1 is a wait call and releases lock, it may happen in parallel with other monitor stmts 
				 */
//				if(solver.arg.combined) {
					MemConstraint sinMHPs1 = new MemConstraint(null, s1, false, MapName.MHP, ConstType.mhp);
//					ConditionalConstraint musts = new ConditionalConstraint(null, null, MapName.must, sinMHPs1, ConstType.mhp);
					ConditionalConstraint sinSyncr = new ConditionalConstraint(null, sinMHPs1, MapName.sync, null, ConstType.mhp);
//					sinSyncr.name = ConstraintName.PARAMETER_COPY;
					ConditionalConstraint rinVarpts = new ConditionalConstraint(ls, sinSyncr, varMap, null, ConstType.mhp);
					callerFc.addConditional(rinVarpts);
					
					for(Stmt s2 : succs) {
						/*
						 * since the parallely running notify statement becomes logical predecessor, MHP information flows from it to wait's successor
						 */
						PropagateConstraint pc1 = new PropagateConstraint( null, s2, MapName.MHP, MapName.MHP, ConstType.mhp);
						ConditionalConstraint ccp = new ConditionalConstraint(s1, pc1, MapName.MHP, null, ConstType.mhp );

						ccp.isExistsCond = true;
//						pc1.useOuterCondObj = true;
						ConditionalConstraint ccp2 = new ConditionalConstraint(null, ccp, MapName.notifyStmts, null, ConstType.mhp );
						ConditionalConstraint notifyMhp = new ConditionalConstraint(ls, ccp2, varMap, null, ConstType.mhp);
						callerFc.addConditional(notifyMhp);
						
						PropagateConstraint pc2 = new PropagateConstraint( null, s2, MapName.MHP, MapName.MHP, ConstType.mhp);
						ConditionalConstraint cc1 = new ConditionalConstraint(null, pc2, MapName.notifyStmts, null, ConstType.mhp );
//						pc1.isExistsCond = true;
//						pc2.name = ConstraintName.CC_NEW;
						cc1.isExistsCond = true;
//						cc1.name=ConstraintName.A_NEW;
						cc1.useOuterCondObj = true;
						ConditionalConstraint cc = new ConditionalConstraint(s1, cc1, MapName.MHP, null, ConstType.mhp );
						ConditionalConstraint notifyMhp2 = new ConditionalConstraint(ls, cc, varMap, null, ConstType.mhp);
						callerFc.addConditional(notifyMhp2);
						if(solver.arg.combined) {
							PropagateConstraint waitMhpCopy = new PropagateConstraint(s1,s2, MapName.MHP, MapName.MHP, ConstType.mhp);
				        	MemConstraint sinMHPs2 = new MemConstraint(null, s2, false, MapName.MHP, ConstType.depOnPts);
				        	ConditionalConstraint mustS = new ConditionalConstraint(null, null, MapName.must, sinMHPs2, ConstType.depOnPts);
				        	ConditionalConstraint sinSync = new ConditionalConstraint(null, mustS, MapName.sync, sinMHPs2, ConstType.depOnPts);
				        	sinSync.isExistsCond = true;
				        	sinSync.useOuterCondObj = true;
				        	//sinSyncr.name = ConstraintName.A_NEW;
				        	ConditionalConstraint sinMHP = new ConditionalConstraint(s1, sinSync, MapName.MHP, null, ConstType.depOnPts);
							ConditionalConstraint mustR = new ConditionalConstraint(ls, sinMHP, MapName.must, waitMhpCopy, ConstType.depOnPts);
							
				        	ConditionalConstraint waitMHP = new ConditionalConstraint(ls, mustR, varMap,null, ConstType.depOnPts);
				        	
				        	callerFc.addConditional(waitMHP);
						}
						else {
							PropagateConstraint pc = new PropagateConstraint( s1, s2, MapName.MHP, MapName.MHP, ConstType.mhp);
							callerFc.addPropagate(pc);
						}
						
					}
//				}
//				else {
//					for(Stmt s2 : succs) {
//					/*
//					 * add parallely running notify as predecessor for MHP
//					 */
//					PropagateConstraint pc1 = new PropagateConstraint( null, s2, MapName.MHP, MapName.MHP, ConstType.mhp);
//					ConditionalConstraint ccp = new ConditionalConstraint(s1, pc1, MapName.MHP, null, ConstType.mhp );
//					ccp.isExistsCond = true;
//					ConditionalConstraint ccp2 = new ConditionalConstraint(null, ccp, MapName.notifyStmts, null, ConstType.mhp );
//					ConditionalConstraint notifyMhp = new ConditionalConstraint(ls, ccp2, varMap, null, ConstType.mhp);
//					callerFc.addConsLater(notifyMhp);
//					
//					}
//					/*
//					 * statements in other monitors can MHP with s1
//					 */
//					PropagateConstraint sinSyncr = new PropagateConstraint(null, s1, MapName.sync, MapName.MHP, ConstType.mhp);
//					ConditionalConstraint rinVarpts = new ConditionalConstraint(ls, sinSyncr, varMap, null, ConstType.mhp);
//					callerFc.addConditional(rinVarpts);
//					addMHPRelConsSet(s1, succs, false);
//				}
				
			  }
			else if (method.getName().equals("notify") || method.getName().equals("notifyAll") && retType instanceof VoidType && paras.size() == 0) {
				interested = true;
				/*
				 * Add s1 into notifyStmts  of r
				 */
				if(!solver.notifys.containsKey(callerFc.method)) {
					solver.notifys.put(callerFc.method, new HashSet<>());
				}
				solver.notifys.get(callerFc.method).add(s1);
				MemConstraint mp = new MemConstraint(s1, null, false, MapName.notifyStmts, ConstType.depOnPts);
				ConditionalConstraint notifyMem = new ConditionalConstraint(ls, mp, varMap, null, ConstType.depOnPts);
				callerFc.addConditional(notifyMem);
				addMHPRelConsSet(s1, succs, false);
			}
			
			/*method call*/
			if (!interested){
				Local r = (Local)rcvr;

				
				/*
				 * Pass MHP
				 */
				addMHPRelConsSet(s1, succs, true);
//				addForMethCallStmt(null,s1);
				
				
				
			
			}
		}
		else {
//			SootMethod sm = ie.getMethod();
			addMHPRelConsSet(s1,succs, true);
//			addForMethCallStmt(sm,s1);
		}
	}
	@Override
	public void genEveryMethod() {
		super.genEveryMethod();
		
		if(callerFc.caller!=null && callerFc.callSite != null) {
			SootMethod caller = callerFc.caller.method;
			Stmt from=null,to=null;
			if(solver.noPCMRep.containsKey(caller)) 
				from = solver.noPCMRep.get(caller);
			
			else 
				from = callerFc.callSite;
			
			
			if(solver.noPCMRep.containsKey(callerFc.method)) {
//				to =  solver.noPCMRep.get(callerFc.method);
			}
			else
				to=(Stmt)callerFc.b.getUnits().getFirst();
			if(from!=null && to!=null)	
			addMHPRelCons(from,to);
		}
			

	}
	public void addMHPRelCons(Stmt from, Stmt to) {
		
		PropagateConstraint mhpCopy = new PropagateConstraint(from,to,MapName.MHP,MapName.MHP, ConstType.mhp);
    	callerFc.addPropagate(mhpCopy);
    	

	}

	public void genRetMHPToCaller(Stmt s1, SootMethod caller, Set<Stmt> callSiteSuccs) {
		if(!Solver.xMeths.contains(callerFc.method)){
		if(callSiteSuccs != null) {
			if(solver.noPCMRep.containsKey(caller)) {
				Stmt callerRep = solver.noPCMRep.get(caller);
				if(callerRep!=null) {
					addMHPRelCons(s1,callerRep);
				}
			}
			else {
				addMHPRelConsSet(s1, callSiteSuccs, false);
			}
		}
		}
	}

	@Override
	public void genProcessed() {
		if(!Solver.xMeths.contains(callerFc.method))
		if(callerFc.callSiteSuccs!=null) {
			SootMethod caller = callerFc.caller.method;
			if(solver.noPCMRep.containsKey(callerFc.method)) {
				Stmt rep = solver.noPCMRep.get(callerFc.method);
				genRetMHPToCaller(rep, caller, callerFc.callSiteSuccs);
			}
			else {
				BitSet retStmts = solver.methRet.get(callerFc.method);
				if(retStmts != null) {
					int i = retStmts.nextSetBit(0);
					while(i!=-1) {
						Stmt st = solver.stmtList.get(i);
						
						genRetMHPToCaller(st, caller, callerFc.callSiteSuccs);
						i = retStmts.nextSetBit(i+1);
					}
				}
			}
		}
	}

	@Override
	public void genThreadRun(Stmt s1) {

//		for(Stmt s2 : callerFc.callSiteSuccs) {
		SootClass rcvrType = callerFc.method.getDeclaringClass();
			PropagateConstraint threadRunMhp = new PropagateConstraint(null, rcvrType, MapName.methRep, MapName.runStmts, ConstType.depOnPts);
			ConditionalConstraint inclMeths = new ConditionalConstraint(callerFc.method, threadRunMhp, MapName.reachableFuncs, null, ConstType.depOnPts );
//			threadRunMhp.name = ConstraintName.LOAD;
			callerFc.addConditional(inclMeths);
//		}
			for(Stmt s2 : callerFc.callSiteSuccs) {
	        	PropagateConstraint pc = new PropagateConstraint(rcvrType,s2, MapName.runStmts, MapName.MHP, ConstType.depOnPts);
//	        	pc.name = ConstraintName.START;
	        	callerFc.addPropagate(pc);
        	}
	}

	

	@Override
	public void genFieldCons() {
		// TODO Auto-generated method stub
		
	}
	
	@Override
	public void countPtsInfo() {
		// TODO Auto-generated method stub
		
	}
	
	@Override
	public MapName getVarMap() {
		return varMap;
	}
	@Override
	public MapName getFieldMap() {
		// TODO Auto-generated method stub
		return null;
	}
	@Override
	public void countMonomorphic() {
		// TODO Auto-generated method stub
		
	}
	@Override
	public void countCallEdges() {
		// TODO Auto-generated method stub
		
	}
}
