package compomhp;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;


import soot.ArrayType;
import soot.Body;
import soot.EntryPoints;
import soot.Hierarchy;
import soot.IntType;
import soot.Local;
import soot.LongType;
import soot.PrimType;
import soot.RefLikeType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.VoidType;
import soot.jimple.AssignStmt;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.ExitMonitorStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.NullConstant;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.internal.JArrayRef;
import soot.jimple.internal.JCastExpr;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JInstanceFieldRef;
import soot.toolkits.graph.CompleteUnitGraph;
import soot.toolkits.graph.UnitGraph;



public class Generator {
	//private static Generator instance = new Generator();
	public Generator() {
    	
    	
    	solver = Solver.v();
    	methInterestingStmts = new LinkedHashMap<Stmt,Set<Stmt>>();
    	uninteresting = new HashSet<Stmt>();
    	stmtType = new HashMap<Stmt,StmtType>();
    	expansion = new HashMap<Stmt,Set<Stmt>>();
    	methIntPreds = new HashMap<>();
    	defs = new HashMap<>();
    	uses = new HashMap<>();
    	methFInterestingStmts = new LinkedHashMap<Stmt,Set<Stmt>>();
    	methFIntPreds = new HashMap<>();
    	
    }
    
    
	ArrayList<Stmt> retStmts;
	Solver solver;
	FunctionalConstraint callerFc;
	Analyzer analyzer;
	Local retLocal;
	
	Map<ExitMonitorStmt,EnterMonitorStmt> monPairs = null;
	LinkedHashMap<Stmt,Set<Stmt>> methInterestingStmts;
	HashMap<Stmt,Set<Stmt>> methIntPreds;
	LinkedHashMap<Stmt,Set<Stmt>> methFInterestingStmts;
	HashMap<Stmt,Set<Stmt>> methFIntPreds;
	Map<Stmt,Set<Stmt>> expansion;
	Set<Stmt> uninteresting;
	Map<Stmt,StmtType> stmtType;
	
	Stmt callSite;
	Stmt head;
	Body b;
	StmtLocal throwLs;
	UnitGraph cug;

	Map<Stmt,Set<Local>> defs;
	Map<Stmt,Set<Local>> uses;

	Set<EnterMonitorStmt> synchStmts=null;
	boolean hasParallelConst = false;
	Stmt firstS = null;
	Map<Stmt,Map<Local,Set<Stmt>>> reachDefMap;
	public void clear() {
		
	}
	
	
	public void generate(Body b, FunctionalConstraint callerFc) throws SecurityException, IOException {
		
		
		if(solver.arg.combined && !Solver.intPass && !HelperAnalysis.methFields.containsKey(callerFc.method)) {
			System.out.println("Couldn't find methfields for "+callerFc.method.getSignature());
//			Set s = MyCG.HAedgesInto.get(callerFc.method);
//			if(s==null) {
//				System.out.println("caller: "+callerFc.caller.method.getSignature());
//				s =  MyCG.HAedgesOutof.get(callerFc.caller.method);
//				
//			}
//			Set<SootField> mainFields = HelperAnalysis.methFields.get(solver.main);
//			boolean pr = HelperAnalysis.processedMeths.contains(callerFc.method);
//			boolean find = HelperAnalysis.solver.ignoredMeths.contains(callerFc.method);
//			Set<SootField> f = HelperAnalysis.methFieldsIn.get(callerFc.method);
//			boolean z = HelperAnalysis.zeros.contains(callerFc.method);
//			z = HelperAnalysis.zeros.contains(callerFc.caller.method);
//			z = HelperAnalysis.zeroReach.contains(callerFc.caller.method);
//			z = HelperAnalysis.zeroReach.contains(callerFc.method);
//			boolean intr = CheckInteresting.ignoreMethod(callerFc.method, b);
//			HelperAnalysis.methFields.put(callerFc.method, mainFields);	
		}
//		
		this.callerFc = callerFc;
		retLocal = callerFc.retLocal;
		this.b = b;
		firstS = (Stmt)b.getUnits().getFirst();
		callSite = callerFc.callSite;
		callerFc.methLocals = new HashSet<Local>();
		callerFc.methStmts = new HashSet<Stmt>();
		
//		if(callerFc.method.getSignature().equals("<org.apache.lucene.index.IndexWriter: boolean doFlush(boolean,boolean)>")) {
//			System.out.println("Stop");
//		}
		analyzer.init(this, callerFc);
		
		
		Stmt s1 = null;
		
		Iterator<Unit> stmtIt = b.getUnits().snapshotIterator();

		methInterestingStmts.clear();
		uninteresting.clear();
		stmtType.clear();
		expansion.clear();
		
		head = (Stmt)b.getUnits().getFirst();
		
		/*
		 * Add head as interesting statement
		 */
		if(!isInteresting(head)) {
			callerFc.methStmts.add(head);
			methInterestingStmts.put(head, null);
			stmtType.put(head, StmtType.head);
			
		}
		methIntPreds.put(head, null);
		List<Local> lst = b.getParameterLocals();
		Set<Local> lSet;
		if(!defs.containsKey(head)) {
			lSet = new HashSet<>();
			defs.put(head, lSet);
		}
		lSet = defs.get(head);
		if(!callerFc.method.isStatic()) {
			Local thisL = b.getThisLocal();
			if(thisL!=null) {
				if(SimplifyUtil.isInterestingType(thisL.getType())) {
					lSet.add(thisL);
				}
			}
		}
		for(Local l:lst) {
			if(SimplifyUtil.isInterestingType(l.getType())) {
				lSet.add(l);
			}
		}
			
			

		cug = new CompleteUnitGraph(b);
		Stmt s2 = null;
		retStmts = null;
		
		/*
		 * Find interesting statements and locals
		 */
		while(stmtIt.hasNext()) {
			s1 = (Stmt) stmtIt.next();
			/*
			 * if s1 is interesting, get its cfg successors
			 */
			if(isInteresting(s1)) {
				
				List<Unit> succs = cug.getSuccsOf(s1);
				
				Set<Stmt> sucList = methInterestingStmts.get(s1);
				if(succs.size() > 0) {
						if(sucList == null) {
							sucList = new HashSet<Stmt>();
					}
						
				}
				Iterator<Unit> succsIt = succs.iterator();
		        while (succsIt.hasNext()) {
		        	s2 = (Stmt)succsIt.next();
		        	if(isInteresting(s2)) {
		        		sucList.add(s2);
		        		if(!methIntPreds.containsKey(s2)) {
		        			methIntPreds.put(s2, new HashSet<>());
		        		}
		        		methIntPreds.get(s2).add(s1);
		        	}
		        	else {
		        		/*
		        		 * Expand all s2's successors and add them as s1's successors 
		        		 */
		        		
		        		Set<Stmt> set = expand(s2,cug);
		        		sucList.addAll(set);
		        		for(Stmt s : set) {
		        			if(!methIntPreds.containsKey(s)) {
			        			methIntPreds.put(s, new HashSet<>());
			        		}
		        			
		        			if(methIntPreds.get(s)!=null)
			        		methIntPreds.get(s).add(s1);
		        		}
		        		
		        		
		        	}
		        	
		        }
		       // System.out.println("Successors :"+sucList);
		        methInterestingStmts.put(s1, sucList);
			}
				
			}
		
		if(!isFInteresting(head)) {
			methFInterestingStmts.put(head, null);
		}
		methFIntPreds.put(head, null);
		uninteresting.clear();
		expansion.clear();
		stmtIt = b.getUnits().snapshotIterator();
		while(stmtIt.hasNext()) {
			s1 = (Stmt) stmtIt.next();
			/*
			 * if s1 is interesting, get its cfg successors
			 */
			if(isFInteresting(s1)) {
				
				List<Unit> succs = cug.getSuccsOf(s1);
				
				Set<Stmt> sucList = methFInterestingStmts.get(s1);
				if(succs.size() > 0) {
						if(sucList == null) {
							sucList = new HashSet<Stmt>();
					}
				}
				Iterator<Unit> succsIt = succs.iterator();
		        while (succsIt.hasNext()) {
		        	s2 = (Stmt)succsIt.next();
		        	if(isFInteresting(s2)) {
		        		sucList.add(s2);
		        		if(!methFIntPreds.containsKey(s2)) {
		        			methFIntPreds.put(s2, new HashSet<>());
		        		}
		        		methFIntPreds.get(s2).add(s1);
		        	}
		        	else {
		        		/*
		        		 * Expand all s2's successors and add them as s1's successors 
		        		 */
		        		
		        		Set<Stmt> set = expandF(s2,cug);
		        		sucList.addAll(set);
		        		for(Stmt s : set) {
		        			if(!methFIntPreds.containsKey(s)) {
			        			methFIntPreds.put(s, new HashSet<>());
			        		}
		        			
		        			if(methFIntPreds.get(s)!=null)
			        		methFIntPreds.get(s).add(s1);
		        		}
		        		
		        		
		        	}
		        	
		        }
		       // System.out.println("Successors :"+sucList);
		        methFInterestingStmts.put(s1, sucList);
			}
				
			}
			if(analyzer.ptConsGen != null && analyzer.ptConsGen.varMap == MapName.varPts) {
				reachDefMap = ReachingDefPass.findDefs(this);
			}else {
				reachDefMap = new HashMap<>();
			}
//			calculateVarInteresting();
			boolean genMonStmts = true;
			if(!solver.arg.mhp) {
				genMonStmts = false;
			}
			if(Solver.intPass)
				genMonStmts = true;
			if(genMonStmts) {
				if(synchStmts != null) {
					for(Stmt s : synchStmts) {
						populateMonitorStmts((EnterMonitorStmt)s);
					}
				}
			}
			for(Map.Entry<Stmt, Set<Stmt>> ele : methIntPreds.entrySet()) {
				s1 = ele.getKey();
				
				
				Set<Stmt> preds = ele.getValue();
				Set<Stmt> succs = methInterestingStmts.get(s1);
				
				analyzer.gen(s1,succs, preds, stmtType.get(s1));
				
			}	
			boolean genF = true;
			genF = SimplifyUtil.genFieldCons(callerFc.method);
			if(solver.arg.poa && genF) {
				analyzer.genFieldCons();
			}
			if(solver.arg.mhp && hasParallelConst) {
				if(callerFc.callSite!=null)
				analyzer.mhpConsGen.addMHPRelCons(callerFc.callSite, firstS);
				
			}
			
	}
	
	
	public boolean isThreadClass(SootClass sclass) {
		boolean threadclass = false;
//		synchronized(Scene.v()) {
		Hierarchy h = Scene.v().getActiveHierarchy();
		 
		 if(!(sclass.resolvingLevel() == SootClass.DANGLING) && sclass.isConcrete()) {
			 List<SootClass> superClasses = h.getSuperclassesOfIncluding(sclass);
		        Iterator<SootClass> it = superClasses.iterator();
	
		        while (it.hasNext()) {
		          String className = it.next().getName();
		          if (className.equals("java.lang.Thread")) {
		        	 // System.out.println("It is a thread class");
		        	  threadclass = true;
		            break;
		          }
		        }
		 }
		
		 if(!threadclass) {
			 SootClass runnableClass = Scene.v().getSootClass("java.lang.Runnable");
			 List<SootClass> runnableImplList = h.getDirectImplementersOf(runnableClass);
			 if(runnableImplList.contains(sclass)) {
				 threadclass = true;
			 }
		 }
//	}
	        return threadclass;
	}
	
	

	
	
	
	public void addClinitConstraint(SootClass sc, FunctionalConstraint caller, Stmt s1, Set<Stmt> succs) {
//		try {
		Iterable<SootMethod> mlist = EntryPoints.v().clinitsOf(sc);
		for(SootMethod m : mlist) {
			if(!solver.clinitProcessed.contains(m.getDeclaringClass())) {
				FunctionalConstraint fc2 = new FunctionalConstraint(ConstType.pts);
				
				
				fc2.method = m;
				fc2.invokeExpr = null;
				fc2.callSite = s1;
				fc2.callSiteRDefMap = reachDefMap.get(s1);
				fc2.callSitePreds = methIntPreds.get(s1);
				fc2.fieldIntPreds = methFIntPreds.get(s1);
				fc2.callSiteSuccs = succs;
				fc2.caller = caller;
				if(!hasParallelConst) {
					fc2.callerSkipped = true;
					fc2.callerFirstS = firstS;
				}
				
				//solver.addCons(fc2);
				
					if(caller!=null && !caller.method.getDeclaringClass().isLibraryClass() ) {
//						if(!solver.ignoreMethod(m)) {
						//fc2.genEveryMethod();
	            		caller.ffunc.add(fc2);
//						}
						
						
		    		}
				
			}
			
		}
//		}catch(Exception e) {
//			System.out.println("caught");
//		}
	}
//	
	public boolean isInteresting(Stmt s1) {
		
		boolean interested = false;
		/*
		 * if already check was performed, one of the maps contains s1. This will avoid infinite loop
		 */
//		if(s1.toString().contains("null")) {
//			System.out.println("stop");
//		}
		
		if(methInterestingStmts.containsKey(s1))
			return true;
		else if(uninteresting.contains(s1))
			return false;
		/*
		 * Otherwise, perform the check and if interesting, add in interesting map
		 */
		
		if(s1 instanceof JIdentityStmt) {
			JIdentityStmt ji = (JIdentityStmt)s1;
			Value vl = ji.getLeftOp();
			Value vr = ji.getRightOp();
			if(!(vr instanceof ParameterRef)) {
				if(vl instanceof Local && SimplifyUtil.isInterestingType(vl.getType())) {
					interested = true;
					stmtType.put(s1, StmtType.identity);
					addToDefUse(defs, s1, (Local)vl);
				}
			}
		}
		else if(s1.containsInvokeExpr()) {
//			boolean exploreIE = true;
			if(s1 instanceof AssignStmt) {
				Value vl = ((AssignStmt)s1).getLeftOp();
				Type t = vl.getType();
				if(t instanceof ArrayType) {
					t = ((ArrayType)t).baseType;
				}
				if(SimplifyUtil.isInterestingType(t)) {
					addToDefUse(defs, s1, (Local)vl);
				
				}
//				else {
//					exploreIE = false;
//				}
			}
//			if(exploreIE) {
				InvokeExpr ie = s1.getInvokeExpr();
				if(ie instanceof InstanceInvokeExpr) {
					Local v = (Local)((InstanceInvokeExpr)ie).getBase();
					if(SimplifyUtil.isInterestingType(v.getType())) {
					
						
						StmtType sty =  StmtType.invoke;
						if(ie instanceof VirtualInvokeExpr) {
							/*
							 * finds out if parallel construct related method is there
							 */
							sty =  getMethType((VirtualInvokeExpr)ie);
						}
						else if(ie instanceof InterfaceInvokeExpr) {
							/*
							 * finds out if parallel construct related method is there
							 */
							sty =  getMethType((InterfaceInvokeExpr)ie);
						}
						
						if(!hasParallelConst) {
							if(sty != StmtType.invoke)
								hasParallelConst=true;
						}
							interested = true;
							addToDefUse(uses, s1, v);
							addArgstoUsedLocals(ie,s1);
							if(s1 instanceof AssignStmt) {
								stmtType.put(s1, StmtType.assign);
							}
							else
							stmtType.put(s1, sty);
							
						
					}
				}
				else if(ie instanceof StaticInvokeExpr) {
					SootMethod m = ie.getMethod();
					boolean ign = false;
//					if(solver.arg.combined) {
//						if(HelperAnalysis.ignoredMeths.contains(m))
//							ign = true;
//					}
//					if(solver.ignoredMeths.contains(m)) {
//						ign = true;
//					}
					if(!ign) {
						interested = true;
						addArgstoUsedLocals(ie,s1);
						if(s1 instanceof AssignStmt) {
							stmtType.put(s1, StmtType.assign);
						}
						else
						stmtType.put(s1, StmtType.invoke);
					}
				}
				else {
					interested = true;
					addArgstoUsedLocals(ie,s1);
					if(s1 instanceof AssignStmt) {
						stmtType.put(s1, StmtType.assign);
					}
					else
					stmtType.put(s1, StmtType.invoke);
				}
				
//			}
		}
		else if(s1 instanceof AssignStmt) {
			Value vl = ((AssignStmt)s1).getLeftOp();
			Value vr = ((AssignStmt)s1).getRightOp();
				Type t = vl.getType();

				if(SimplifyUtil.isInterestingType(t)) {
					interested = true;
					stmtType.put(s1, StmtType.assign);
					if(vl instanceof Local) {
						
						addToDefUse(defs, s1, (Local)vl);
						
					
						if(vr instanceof JInstanceFieldRef ) {
							/*
							 * Load x = y.fl;
							 */
							JInstanceFieldRef jfr = (JInstanceFieldRef)vr;
							
							Local l = (Local)jfr.getBase();
							addToDefUse(uses, s1, l);
						}
						else if(vr instanceof JCastExpr) {
							Value v = ((JCastExpr)vr).getOp();
							if(v instanceof Local) {
								addToDefUse(uses, s1, (Local)v);
							}
						}
//						else if(vr instanceof NullConstant) {
//							
//						}
					}
					if(vl instanceof JArrayRef) {
						Local l = (Local)((JArrayRef)vl).getBase();
						addToDefUse(uses, s1, l);
					}
					if(vr instanceof JArrayRef) {
						Local l = (Local)((JArrayRef)vr).getBase();
						addToDefUse(uses, s1, l);
					}
					if(vr instanceof Local) {
						if(SimplifyUtil.isInterestingType(vr.getType())) {
						addToDefUse(uses, s1, (Local)vr);
						
						if(vl instanceof JInstanceFieldRef) {
							/*
							 * Store x.fl = y;
							 * */
							JInstanceFieldRef jfr = (JInstanceFieldRef)vl;
							
							Local l = (Local)jfr.getBase();
							
							addToDefUse(uses, s1, l);
		
						}
					}
					}
				}
				else {
					if(vr instanceof NewExpr && vl instanceof Local) {
						interested = true;
						addToDefUse(defs, s1, (Local)vl);
						stmtType.put(s1, StmtType.assign);
					}
				}
		}
		else if(s1 instanceof EnterMonitorStmt) {
			Value value = ((EnterMonitorStmt)s1).getOp();
			if(value instanceof Local) {
				interested = true;
				hasParallelConst=true;
				stmtType.put(s1, StmtType.enterMonitor);
				addToDefUse(uses, s1, (Local)value);
				if(solver.arg.mhp || Solver.intPass) {
					if(!solver.synchStmts.containsKey(callerFc.method)) {
						solver.synchStmts.put(callerFc.method, new HashSet<>());
					}
					synchStmts = solver.synchStmts.get(callerFc.method);
					synchStmts.add((EnterMonitorStmt)s1);
					
					if(monPairs==null) {
						monPairs=new HashMap<>();
					}
				}
			}
		}
		else if(s1 instanceof ExitMonitorStmt) {
			Value value = ((ExitMonitorStmt)s1).getOp();
			if(value instanceof Local) {
				
				interested = true;
				hasParallelConst=true;
				stmtType.put(s1, StmtType.exitMonitor);
				addToDefUse(uses, s1, (Local)value);
			}
		}
		else if(s1 instanceof ReturnStmt) {
			interested = true;
			stmtType.put(s1, StmtType.ret);
			Value v = ((ReturnStmt)s1).getOp();
			if(v instanceof Local && SimplifyUtil.isInterestingType(v.getType())) {
				addToDefUse(uses, s1, (Local)v);
			}
//			retStmts.add(s1);
		}
		else if(s1 instanceof ReturnVoidStmt) {
			interested = true;
			stmtType.put(s1, StmtType.retVoid);
//			retStmts.add(s1);
		}
		if(interested) {
			callerFc.methStmts.add(s1);
			methInterestingStmts.put(s1, null);
		}
		else
			uninteresting.add(s1);
		
		
		return interested;
	}
public boolean isFInteresting(Stmt s1) {
		
		boolean interested = false;
		/*
		 * if already check was performed, one of the maps contains s1. This will avoid infinite loop
		 */
//		if(s1.toString().equals("$r22 = (org.dacapo.harness.Benchmark) r27")) {
//			System.out.println("stop");
//		}
		if(methFInterestingStmts.containsKey(s1))
			return true;
		else if(uninteresting.contains(s1))
			return false;
		/*
		 * Otherwise, perform the check and if interesting, add in interesting map
		 */
		
		 if(s1.containsInvokeExpr()) {
//			boolean exploreIE = true;
			
				InvokeExpr ie = s1.getInvokeExpr();
				if(ie instanceof InstanceInvokeExpr) {
					Local v = (Local)((InstanceInvokeExpr)ie).getBase();
					if(SimplifyUtil.isInterestingType(v.getType())) {
							interested = true;
					}
				}
				
				else {
					interested = true;
					
				}
				
//			}
		}
		else if(s1 instanceof AssignStmt) {
			Value vl = ((AssignStmt)s1).getLeftOp();
			Value vr = ((AssignStmt)s1).getRightOp();
				
//				interested = true;
				
				if(vl instanceof Local) {
					
					Type t = vl.getType();
					if(SimplifyUtil.isInterestingType(t)) {
					
						if(vr instanceof JInstanceFieldRef ) {
							/*
							 * Load x = y.fl;
							 */
							
							interested = true;
						}
				}
				}
				if(vr instanceof Local) {
					
					Type t = vr.getType();
					if(SimplifyUtil.isInterestingType(t)) {
						if(vl instanceof JInstanceFieldRef) {
							
							interested = true;
						}
				}
			}
		}
		
		else if(s1 instanceof ReturnStmt) {
			interested = true;
			
		}
		else if(s1 instanceof ReturnVoidStmt) {
			interested = true;
		}
		if(interested) {
			
			methFInterestingStmts.put(s1, null);
		}
		else
			uninteresting.add(s1);
		
		
		return interested;
	}
	StmtType getMethType(VirtualInvokeExpr vie){
		StmtType sty = StmtType.invoke;
		SootMethodRef method = vie.getMethodRef();
		Type retType = method.getReturnType();
		List<Type> paras = method.getParameterTypes();
		String  name = method.getName();
		if (name.equals("start") && retType instanceof VoidType && paras.size() == 0) {
			 boolean threadStart = isThreadClass(method.getDeclaringClass());
			 if(threadStart) {
		        	sty= StmtType.start;
			 }
		}
		else if(name.equals("join") && retType instanceof VoidType && (paras.size() == 0 || (paras.size() == 1 && (Type) paras.get(0) instanceof LongType)
		          || (paras.size() == 2 && (Type) paras.get(0) instanceof LongType && (Type) paras.get(1) instanceof IntType))) {
		
				boolean threadJoin = isThreadClass(method.getDeclaringClass());
			    if(threadJoin) {
			    	sty = StmtType.join;
			    }
		}
		else if (name.equals("wait") && retType instanceof VoidType && (paras.size() == 0 || (paras.size() == 1 && (Type) paras.get(0) instanceof LongType)
		          || (paras.size() == 2 && (Type) paras.get(0) instanceof LongType && (Type) paras.get(1) instanceof IntType))) {
			sty = StmtType.wait;
		}
		else if (name.equals("notify") || name.equals("notifyAll") && retType instanceof VoidType && paras.size() == 0) {
			sty = StmtType.notify;
		}
		else if (name.equals("submit") || paras.size() == 1) {
			 String declClass = method.getDeclaringClass().getName();	
			 if(declClass.equals("java.util.concurrent.ForkJoinPool")) {
				 sty = StmtType.submit;
			 }
		}
		else if (name.equals("execute") || paras.size() == 1) {
			 String declClass = method.getDeclaringClass().getName();	
			 if(declClass.equals("java.util.concurrent.ForkJoinPool")) {
				 sty = StmtType.execute;
			 }
		}
		
		return sty;
	}
	StmtType getMethType(InterfaceInvokeExpr vie){
		StmtType sty = StmtType.invoke;
		SootMethodRef method = vie.getMethodRef();
		Type retType = method.getReturnType();
		List<Type> paras = method.getParameterTypes();
		String  name = method.getName();
		if (method.getName().equals("submit") && paras.size() == 1) {
			 String declClass = method.getDeclaringClass().getName();	
			 if(declClass.equals("java.util.concurrent.ExecutorService")) {
				 sty = StmtType.submit;
			 }
		}
		else if (method.getName().equals("execute") && paras.size() == 1) {
			 String declClass = method.getDeclaringClass().getName();	
			 if(declClass.equals("java.util.concurrent.ExecutorService")) {
				 sty = StmtType.execute;
			 }
		}
		else if (name.equals("wait") && retType instanceof VoidType && (paras.size() == 0 || (paras.size() == 1 && (Type) paras.get(0) instanceof LongType)
		          || (paras.size() == 2 && (Type) paras.get(0) instanceof LongType && (Type) paras.get(1) instanceof IntType))) {
			sty = StmtType.wait;
		}
		else if (name.equals("notify") || name.equals("notifyAll") && retType instanceof VoidType && paras.size() == 0) {
			sty = StmtType.notify;
		}
		
		return sty;
	}
	public void addToDefUse(Map<Stmt,Set<Local>> map, Stmt s, Local l) {
		Set<Local> lSet;
		if(!map.containsKey(s)) {
			map.put(s, new HashSet<>());
		}
		lSet = map.get(s);
		lSet.add(l);
		
		callerFc.methLocals.add(l);
	}
	private void addArgstoUsedLocals(InvokeExpr ie, Stmt s1) {
		List<Value> lv = ie.getArgs();
		Set<Local> s;
		if(!uses.containsKey(s1)) {
			s = new HashSet<>();
			uses.put(s1, s);
		}
		else
			s = uses.get(s1);
		for(Value v : lv) {
			if(v instanceof Local && SimplifyUtil.isInterestingType(v.getType())) {
				s.add((Local)v);
			}
		}
	}
	public boolean hasPC(VirtualInvokeExpr ie) {
		SootMethodRef method = ie.getMethodRef();
		List paras = method.getParameterTypes();
		Type retType = method.getReturnType();
		
			if (method.getName().equals("start") && retType instanceof VoidType && paras.size() == 0) {
				 boolean threadStart = isThreadClass(method.getDeclaringClass());	
				 if(threadStart) {
					 return true;
				 }
			}
			else if(method.getName().equals("join") && retType instanceof VoidType && (paras.size() == 0 || (paras.size() == 1 && (Type) paras.get(0) instanceof LongType)
			          || (paras.size() == 2 && (Type) paras.get(0) instanceof LongType && (Type) paras.get(1) instanceof IntType))) { 
				 boolean threadStart = isThreadClass(method.getDeclaringClass());	
				 if(threadStart) {
					 return true;
				 }
			}
			else if (method.getName().equals("wait") && retType instanceof VoidType && (paras.size() == 0 || (paras.size() == 1 && (Type) paras.get(0) instanceof LongType)
			          || (paras.size() == 2 && (Type) paras.get(0) instanceof LongType && (Type) paras.get(1) instanceof IntType))) {
				return true;
			}
			else if (method.getName().equals("notify") || method.getName().equals("notifyAll") && retType instanceof VoidType && paras.size() == 0) {
				return true;
			}
		return false;
	}
	public boolean hasPC(InterfaceInvokeExpr ie) {
		SootMethodRef method = ie.getMethodRef();
		List paras = method.getParameterTypes();
		Type retType = method.getReturnType();
		
			if (method.getName().equals("submit") && paras.size() == 1) {
				 String declClass = method.getDeclaringClass().getName();	
				 if(declClass.equals("java.util.concurrent.ExecutorService")) {
					 return true;
				 }
			}
			
		return false;
	}
	public void populateMonitorStmts(EnterMonitorStmt leader) {
		Queue<Stmt> queue = new LinkedList<>();
		Set<Stmt> succs;
//		if(gen.monPairs==null) {
//			gen.monPairs=new HashMap<>();
//		}
		Set<Stmt> monList = new HashSet<Stmt>();
		Set<Stmt> visited = new HashSet<Stmt>();
		queue.add(leader);
//		System.out.println("Started populating monitor statements");
		while(!queue.isEmpty()) {
			Stmt st = queue.poll();
			if(visited.add(st)) {
			if(!(st instanceof ExitMonitorStmt)) {
				succs = methInterestingStmts.get(st);
				if(succs!=null) {
					//queue.addAll(succs);
					monList.addAll(succs);
					for(Stmt s2:succs) {
						if(!visited.contains(s2)) {
							queue.add(s2);
						}
						MemConstraint addToMonitorStmts = new MemConstraint(s2, leader, false, MapName.monitorStmts, ConstType.depOnPts);
//			    		addToMonitorStmts.name = ConstraintName.INTERFACE_INVOKE;
			    		callerFc.addMember(addToMonitorStmts);
			    		if(s2.containsInvokeExpr()) {
			    			InvokeExpr ie = s2.getInvokeExpr();
			    			if(ie instanceof InstanceInvokeExpr) {
			    				
			    				PropagateConstraint addToMonitor = new PropagateConstraint(null, leader, MapName.methRep, MapName.monitorStmts, ConstType.depOnPts);
			    				ConditionalConstraint inclMeths = new ConditionalConstraint(null, addToMonitor, MapName.reachableFuncs, null, ConstType.depOnPts);
			    	    		ConditionalConstraint callSiteCond = new ConditionalConstraint(s2, inclMeths, MapName.funcsAtCallSite, null, ConstType.depOnPts);
			    	    		callerFc.addConditional(callSiteCond);
			    	    		
			    			}
			    			else {
			    				SootMethod sm = ie.getMethod();
			    				PropagateConstraint addToMonitor = new PropagateConstraint(null, leader, MapName.methRep, MapName.monitorStmts, ConstType.depOnPts);
			    				ConditionalConstraint inclMeths = new ConditionalConstraint(sm, addToMonitor, MapName.reachableFuncs, null, ConstType.depOnPts);
			    	    		callerFc.addConditional(inclMeths);
			    			}
			    		}
					}
				}
			}
			else {
				monPairs.put((ExitMonitorStmt)st,leader);
			}
		}
			
		}
//		System.out.println("Got monitorStmts("+leader+")");
	}

	public Set<Stmt> expand(Stmt s2, UnitGraph cug) {
		if(expansion.containsKey(s2)) {
			return expansion.get(s2);
		}

		/*
		 * add s2 to expansion list to avoid infinite loop
		 * if s2 is reached again, it means all statements in that cycle are not interesting. so we can ignore.
		 * if there is atleast one interesting statement, the recursion will stop there.
		 */
		expansion.put(s2,null);
		Set<Stmt> res = new HashSet<Stmt>();
		List<Unit> succs = cug.getSuccsOf(s2);
		Iterator<Unit> itr = succs.iterator();
		while(itr.hasNext()) {
			Stmt s = (Stmt)itr.next();
			if(isInteresting(s)) {
				res.add(s);
			}
			else {
				Set<Stmt> exp = expand(s,cug);
				if(exp != null)
				res.addAll(exp);
			}
		}
		if(res != null)
			expansion.put(s2,res);
		return res;
	}

	public Set<Stmt> expandF(Stmt s2, UnitGraph cug) {
		if(expansion.containsKey(s2)) {
			return expansion.get(s2);
		}

		/*
		 * add s2 to expansion list to avoid infinite loop
		 * if s2 is reached again, it means all statements in that cycle are not interesting. so we can ignore.
		 * if there is atleast one interesting statement, the recursion will stop there.
		 */
		expansion.put(s2,null);
		Set<Stmt> res = new HashSet<Stmt>();
		List<Unit> succs = cug.getSuccsOf(s2);
		Iterator<Unit> itr = succs.iterator();
		while(itr.hasNext()) {
			Stmt s = (Stmt)itr.next();
			if(isFInteresting(s)) {
				res.add(s);
			}
			else {
				Set<Stmt> exp = expandF(s,cug);
				if(exp != null)
				res.addAll(exp);
			}
		}
		if(res != null)
			expansion.put(s2,res);
		return res;
	}
	
}
