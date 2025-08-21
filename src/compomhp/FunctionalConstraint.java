package compomhp;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import soot.Body;
import soot.Hierarchy;
import soot.Local;
import soot.PrimType;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Value;
import soot.VoidType;
import soot.jimple.AssignStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.NewExpr;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;



public class FunctionalConstraint extends Constraint{

	Stmt callSite;
	
	
	
	/*
	 * Populated values from callSite
	 */
	Local rcvr = null;
	SootMethod method;
	InvokeExpr invokeExpr;
	boolean threadStart = false;
	boolean exSubmit = false;
	boolean loadRunCall = false;
	Map<Local,Set<Stmt>> callSiteRDefMap;
	Set<Stmt> callSitePreds;
	Set<Stmt> callSiteSuccs;
	Stmt callerFirstS;
	boolean callerSkipped = false;
	Set<Stmt> fieldIntPreds;
	Local retLocal = null;
	Set<Stmt> methStmts;
	Set<Local> methLocals;
	Body b = null;
	
	/*
	 * From conditional constraint
	 */
	Object ref;
	
	
	/*
	 * constraints generated for the method. Used in parallelization
	 */
	final ArrayList<Constraint> fmem;
	final ArrayList<Constraint> fprop;
	final ArrayList<Constraint> fcond;
	final ArrayList<Constraint> laterCons;
	final ArrayList<Constraint> 	ffunc;
	
	/*
	 * utility
	 */
	Generator gen;
	FunctionalConstraint caller = null;
	boolean useCHA = false;
	
	public FunctionalConstraint(FunctionalConstraint fc) {
		/*
		 * from Constraint interface
		 */
		this.name = fc.name;
		
		
		this.callSite = fc.callSite;
		
		this.rcvr = fc.rcvr;
		this.method = fc.method;
		this.invokeExpr = fc.invokeExpr;
		this.threadStart = fc.threadStart;
		this.exSubmit = fc.exSubmit;
		this.loadRunCall = fc.loadRunCall;
		this.callSiteRDefMap = fc.callSiteRDefMap;
		this.callSitePreds = fc.callSitePreds;
		this.callSiteSuccs = fc.callSiteSuccs;
		this.fieldIntPreds = fc.fieldIntPreds;
		this.retLocal = fc.retLocal;
		this.b = fc.b;
		
		this.ref = fc.ref;
		
		this.fcond = new ArrayList<Constraint>(fc.fcond);
		this.fmem =  new ArrayList<Constraint>(fc.fmem);
		this.fprop = new ArrayList<Constraint>(fc.fprop);
		this.laterCons = new ArrayList<Constraint>(fc.laterCons);
		this.ffunc = new ArrayList<Constraint>(fc.ffunc);
		
		this.useCHA = fc.useCHA;
		this.gen = fc.gen;
		this.caller = fc.caller;
		this.constType = fc.constType;
//		this.cardinality = fc.cardinality;
		this.outerCondObj = fc.outerCondObj;
		this.useOuterCondObj = fc.useOuterCondObj;
		this.callerSkipped = fc.callerSkipped;
		this.callerFirstS = fc.callerFirstS;
	}
  public FunctionalConstraint(ConstType ct) {
	  	fmem = new ArrayList<Constraint>();
		fprop = new ArrayList<Constraint>();
		fcond = new ArrayList<Constraint>();
		laterCons = new ArrayList<Constraint>();
		ffunc = new ArrayList<Constraint>();
		this.constType = ct;

  }
  public void populateFromCallSite() {
	  invokeExpr = callSite.getInvokeExpr();
	  method = invokeExpr.getMethod();
	  if(invokeExpr instanceof InstanceInvokeExpr) {
		  rcvr = (Local)((InstanceInvokeExpr)invokeExpr).getBase();
	  }
	  if(callSite instanceof AssignStmt) {
		  AssignStmt as = (AssignStmt)callSite;
			Value vl = as.getLeftOp();
			if(vl instanceof Local && !(vl.getType() instanceof PrimType)) {
				retLocal = (Local)vl;
			}
	  }
//	  if(callSite.toString().equals("$r8 = interfaceinvoke $r7.<java.util.Iterator: java.lang.Object next()>()")) {
//		  if(caller.method.getSignature().equals("<org.apache.batik.dom.events.EventSupport: boolean dispatchEvent(org.apache.batik.dom.events.NodeEventTarget,org.w3c.dom.events.Event)>"))
//		  System.out.println("caught");
//	  }
	  
  }
  
	@Override
	public String printConstraint() {
		// TODO Auto-generated method stub
		String s = null;
		s = "Constraint "+ name+" : "+ method.getSignature();
		return s;
	}

	@Override
	public void insert() {
		if(ref!=Solver.v().nullRef)
		if(invokeExpr instanceof InterfaceInvokeExpr || invokeExpr instanceof VirtualInvokeExpr) {
			
			InstanceInvokeExpr vi = (InstanceInvokeExpr) invokeExpr;
			Local rcvr = (Local)vi.getBase();
			Local r = (Local)rcvr;
			Type t = r.getType();
			SootClass rcvrType = null;
			if(t instanceof RefType) {
				rcvrType = ((RefType)t).getSootClass();
			}
			if(useCHA) {
			
				if(rcvrType != null) {
					if(exSubmit) {
						addConsForExecSubmit();
						return;
					}
					if(loadRunCall) {
						addConsForCallStart(rcvrType, null);
						return;
					}
					ArrayList<FunctionalConstraint> smlist = genFunCon(rcvrType, this);
					/*
					 * this is added to have a uniform behaviour for bot and non-bot
					 */
					if(smlist.isEmpty() && !Solver.v().arg.fs && !SimplifyUtil.opaqueMethod(method, b)) {
						if(retLocal != null && SimplifyUtil.isInterestingType(retLocal.getType())) {
							Solver solver = Solver.v();
							Object sl = solver.analyzer.ptConsGen.getKey(callSite, (Local)retLocal) ;
							MemConstraint addBotRet = new MemConstraint(solver.bottom, sl, false, solver.analyzer.ptConsGen.varMap, ConstType.pts);
							addBotRet.addToList();
//							callerFc.addMember(addBotRet);
						}
//						Solver.v().addToWorkList(this);
					}
					Iterator<FunctionalConstraint> itr = smlist.iterator();
					while(itr.hasNext()) {
						FunctionalConstraint lm = itr.next();
						if(lm.method == null) {
							continue;
						}
					
//						Body b = Solver.getBody(lm.method);
//						if(b != null) {
//							lm.b = b;
							Solver.v().addToWorkList(lm);
//						}
//						else {
//							Solver.v().genConsForBodyNull(lm, true);
//		        		}
					}
				}
			}
		}
	}
	
	
	
	
	
	@Override
	public Constraint getCopy() {
		// TODO Auto-generated method stub
		return new FunctionalConstraint(this);
	}
	@Override
	public Constraint updateCond(Object obj, int cardinality) {
		
		Solver solver = Solver.v();
		
		if(solver.arg.bot && obj==Solver.v().bottom) {
			useCHA = true;
			
			populateFromCallSite();
			if(Solver.intPass && Solver.v().arg.fs) {
				StmtLocal sl = new StmtLocal(callSite, rcvr);
				HelperAnalysis.botLocals.add(sl);
			}
			else if(Solver.v().arg.fs && !Solver.v().arg.combined) {
				StmtLocal sl = new StmtLocal(callSite, rcvr);
				Solver.v().botLocals.add(sl);
			}
			insert();
			return null;
		}
		else if(obj==Solver.v().nullRef)
			return null;
		ref = obj;
		boolean addToList = false;
		populateFromCallSite();
		
		
		FunctionalConstraint fc2 = this;
		AllocNode an = (AllocNode) ref;
		SootClass sc = an.anclass;
		if((sc.resolvingLevel() == SootClass.DANGLING)) {
			return null;
		}
		if( fc2.invokeExpr instanceof VirtualInvokeExpr) {
			SootMethod sm = null;
			
			VirtualInvokeExpr vi = (VirtualInvokeExpr) fc2.invokeExpr;
			Local rcvr = (Local)vi.getBase();
			Local r = (Local)rcvr;
			Type t = r.getType();
			String rcvrType = null;
			if(t instanceof RefType) {
				rcvrType = ((RefType)t).getClassName();
			}

			if(an != null) {
				 sm = fc2.method; 
					
					
					 
					
					if(fc2.threadStart) {
						sm = sc.getMethodUnsafe("run",Collections.<Type>emptyList(),VoidType.v());
						if(sm!=null) {
							System.out.println(sm+ " run method is loaded for start"); 
							
						}
					}
					else if(fc2.exSubmit) {
						addConsForExecSubmit();
						return null;
					}
					else if(fc2.loadRunCall) {
						
							addConsForCallStart(sc,an);
							return null;
					
					}
		    		
					else {
						sm = sc.getMethodUnsafe(vi.getMethod().getName(), vi.getMethod().getParameterTypes(), vi.getMethod().getReturnType());

					}
			
		    		if(sm == null) {
		    			
		    			Hierarchy h = Scene.v().getActiveHierarchy();
		    			
		    			if(h.isVisible(sc, vi.getMethod()))
		    				try {
		    				sm = h.resolveConcreteDispatch(sc,vi.getMethod());
		    				}catch(RuntimeException re) {
		    				}
		    			
//		    			sm = fc2.method;
		    		}
			

	    		if(sm!=null ) {
	    			
//	    			Body b = Solver.getBody(sm);
	    			fc2.method = sm;
//	        		if(b!=null) {
//	        			
//	        			
//	        			
//	            		
//	            		addToList = true;
//	        			
//	            		//solver.funCons.add(fc2);
//	            		
//	            		
//	    
//	            	}
//	        			else {
//	        			solver.genConsForBodyNull(fc2, true);
//	        		}
	    		}
			}
			
		}
		
		else if(fc2.invokeExpr instanceof InterfaceInvokeExpr) {
			SootMethod sm = null;
			
			
			InterfaceInvokeExpr vi = (InterfaceInvokeExpr) fc2.invokeExpr;
			if(an != null) {
				
				
				//SootClass sc = an.anclass;
				
				if(fc2.exSubmit) {
					addConsForExecSubmit();
					return null;
				}
				else if(fc2.loadRunCall) {
					
						addConsForCallStart(sc,an);
						return null;
				
				}
				else {
					sm = sc.getMethodUnsafe(vi.getMethod().getName(), vi.getMethod().getParameterTypes(), vi.getMethod().getReturnType());
				}
	    		if(sm==null) {
	    			Hierarchy h = solver.h;
	    			if(h.isVisible(sc, vi.getMethod()))
	    				try {
	    				sm = h.resolveConcreteDispatch(sc,vi.getMethod());
	    				}catch(RuntimeException re) {
	    				}
	    		}
	    		
	    		//if(sm!=null && !caller.method.isJavaLibraryMethod() && !sm.isPhantom()) {
	    		if(sm!=null) {
//	    			Body b = Solver.getBody(sm);
	    			fc2.method = sm;
//	        		if(b!=null) {
//
//	            		
//	            		addToList = true;
//	            			//solver.funCons.add(fc2);
//	            			
//	            		
////	            		
//	            	}
//	        		else {
//	        			solver.genConsForBodyNull(fc2, true);
//	        		}
	    		}
			}
		}
//		if(addToList)
		return fc2;
//		else
//			return null;
		
	}
	public void addConsForExecSubmit() {
		List<Value> lst = invokeExpr.getArgs();
//		String name = invokeExpr.getMethodRef().getName();
//		if(!name.contains("invoke")) {
			Local l = (Local)lst.get(0);
			Solver solver = Solver.v();
			MapName varMap = solver.analyzer.ptConsGen.getVarMap();
			Object key = solver.analyzer.ptConsGen.getKey(callSite, l);
			FunctionalConstraint fc2 = new FunctionalConstraint(this);
			fc2.loadRunCall = true;
			fc2.exSubmit = false;
			ConditionalConstraint cc = new ConditionalConstraint(key, fc2, varMap, null, ConstType.depOnMhp);
			cc.addToList();
//		}
		
	}
	public void addConsForCallStart(SootClass sc, AllocNode an) {
		FunctionalConstraint fc2 = new FunctionalConstraint(this);
		fc2.loadRunCall = true;
		
		SootMethod sm = null;
		if(sc!=null) {
			if(isRunnableClass(sc))
			sm = sc.getMethodUnsafe("run", Collections.<Type>emptyList(),VoidType.v());
			else if(isCallableClass(sc))
				sm = sc.getMethodUnsafe("call", Collections.<Type>emptyList(), RefType.v("java.lang.Object"));
			else if(isForkJoinTask(sc))
				sm = sc.getMethodUnsafe("compute", Collections.<Type>emptyList(), RefType.v("java.lang.Object"));
		}
		Body b = null;
		if(sm != null) {
			b = Solver.getBody(sm);
			fc2.method = sm;
		}
		if(b != null)
		fc2.addToList();
		
	}
	public void addMember(MemConstraint mc) {
		if(mc==null)
			System.out.println("Adding null member constraint for method "+method.getSignature());
    	fmem.add(mc);
    }
    public void addPropagate(PropagateConstraint pc) {
    	
    		if(pc==null)
    			System.out.println("Adding null propagate constraint for method "+method.getSignature());
    	fprop.add(pc);
    	
    	
    }
    public void addConditional(ConditionalConstraint cc) {
    	if(cc==null)
			System.out.println("Adding null conditional constraint for method "+method.getSignature());
    	fcond.add(cc);
    	
    }
    public void addConsLater(Constraint c) {
    	
    	laterCons.add(c);
    }

	@Override
	public void addToList() {
		// TODO Auto-generated method stub
		Solver.v().funCons.add(this);
	}
public boolean isRunnableClass(SootClass sclass) {
		
		Hierarchy h = Scene.v().getActiveHierarchy();
		 boolean threadclass = false;
		 
		 if(!threadclass) {
			 SootClass runnableClass = Scene.v().getSootClass("java.lang.Runnable");
			 List<SootClass> runnableImplList = h.getDirectImplementersOf(runnableClass);
			 if(runnableImplList.contains(sclass)) {
				 threadclass = true;
			 }
		 }
	        return threadclass;
	}
public boolean isCallableClass(SootClass sclass) {
	
	Hierarchy h = Scene.v().getActiveHierarchy();
	 boolean threadclass = false;
	 
	 if(!threadclass) {
		 SootClass runnableClass = Scene.v().getSootClass("java.util.concurrent.Callable");
		 List<SootClass> runnableImplList = h.getDirectImplementersOf(runnableClass);
		 if(runnableImplList.contains(sclass)) {
			 threadclass = true;
		 }
	 }
        return threadclass;
}
public boolean isForkJoinTask(SootClass sclass) {
	
	Hierarchy h = Scene.v().getActiveHierarchy();
	 boolean threadclass = false;
	 if(!(sclass.resolvingLevel() == SootClass.DANGLING) && sclass.isConcrete()) {
		 List<SootClass> superClasses = h.getSuperclassesOfIncluding(sclass);
	        Iterator<SootClass> it = superClasses.iterator();

	        while (it.hasNext()) {
	          String className = it.next().getName();
	          if (className.equals("java.util.concurrent.ForkJoinTask")) {
	        	 // System.out.println("It is a thread class");
	        	  threadclass = true;
	            break;
	          }
	        }
	 }
	 
        return threadclass;
}

	private ArrayList<FunctionalConstraint> genFunCon(SootClass scl, FunctionalConstraint fc){
		ArrayList<FunctionalConstraint> fcList = new ArrayList<FunctionalConstraint>();
		SootMethod sm = fc.method;
		if(Solver.v().resolveDispatchList.contains(sm)) {
			return fcList;
		}
		//SootClass scl = Scene.v().getSootClass(sclass);
//		if(!scl.isLibraryClass()) {
			Hierarchy h = Scene.v().getActiveHierarchy();
			if(fc.threadStart) {
				sm = new SootMethod("run",Collections.<Type>emptyList(),VoidType.v());
				sm.setDeclared(true);
				sm.setDeclaringClass(scl);
				 
			}
			List<SootMethod>  subc = null;
			try {
				
			 subc = h.resolveAbstractDispatch(scl, sm);
			}catch (Exception e) {
				//System.out.println("Couldn't resolve dispatch for class:"+scl.getName()+" method:"+sm.getSignature());
				Solver.v().resolveDispatchList.add(sm);
			}
			if(subc != null) {
				Iterator<SootMethod> itr = subc.iterator();
				while(itr.hasNext()) {
					SootMethod smeth = itr.next();
					if(smeth != null /*&& !Solver.v().processed.contains(smeth) /*&& !smeth.getDeclaringClass().isLibraryClass() && !smeth.isPhantom()*/ /*&& Solver.getBody(smeth)!=null*/) {
						if(fc.threadStart)
							System.out.println("run method loaded for start later constraint:"+smeth.getSignature());
						FunctionalConstraint dup = new FunctionalConstraint(fc);
						dup.ref = Solver.v().bottom;
						dup.method = smeth;
						fcList.add(dup);
					}
				}
			}
//		}
		
		return fcList;
	}
}
