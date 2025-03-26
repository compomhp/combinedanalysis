package compomhp;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import javafx.util.Pair;
import soot.ArrayType;
import soot.Body;
import soot.Hierarchy;
import soot.Local;
import soot.PrimType;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;

public class SimplifyUtil {
	
	private static boolean ignIfNoUsefulStmts(SootMethod method, Body b) {
		/*
		 * checks if the method has any invoke statement or a field update or a ref type
		 * or an interesting return type
		 * otherwise this can be ignored
		 */
		boolean hasRefType=false;
		boolean hasInvoke=false;
		boolean hasIntrFieldAccess=false;
		Local thisLocal = null;
		boolean ign = false;
		if(b!=null) {
			if(!method.isStatic())
				thisLocal = b.getThisLocal();
	
			for(Local l : b.getLocals()) {
				Type t = l.getType();
				
				
				if(l!=thisLocal && isInterestingType(t)) {
					hasRefType=true;
					break;
				} 
			}
			Iterator<Unit> stmtIt = b.getUnits().snapshotIterator();
			
			while(stmtIt.hasNext()) {
				Stmt st = (Stmt)stmtIt.next();
				if(st.containsInvokeExpr()) {
					
						if(st.getInvokeExpr() instanceof StaticInvokeExpr) {
							SootMethod m = st.getInvokeExpr().getMethod();
							/*
							 * Here we can't do this check for 
							 */
							if( solver.arg.combined && HelperAnalysis.ignoredMeths.contains(m)) {
								
								continue;
							}
							
						}
					
					hasInvoke=true;
						break;
				}
				
				if(st.containsFieldRef()) {
					Type ty = st.getFieldRef().getType();
					if(isInterestingType(ty)) {
						hasIntrFieldAccess = true;
					}
				}
			}
			
			if(!hasRefType && !hasIntrFieldAccess && !hasInvoke) {
				if(!isInterestingType(method.getReturnType())) {
					ign =  true;
				}
			}
			
			
		}
		return ign;
	}
	public static boolean useHACallGraph(SootMethod method, Body b) {
		
					Set<Pair<SootMethod, SootMethod>> s = MyCG.HAedgesOutof.get(method);
					if(s==null || s.isEmpty()) {
						/*
						 * since there are no outgoing edges we need to worry about only 
						 * the field references and return type
						 */
						
							boolean hasIntrFieldAccess = false;
							Iterator<Unit> stmtIt = b.getUnits().snapshotIterator();
							while(stmtIt.hasNext()) {
								Stmt st = (Stmt)stmtIt.next();
								if(st.containsFieldRef()) {
									Type ty = st.getFieldRef().getType();
									if(isInterestingType(ty)) {
										hasIntrFieldAccess = true;
										break;
									}
								}
							}
							
							if(!hasIntrFieldAccess) {
								if(!isInterestingType(method.getReturnType())) {
									
									return true;
								}
								else
									return false;
							}
						
					}
				
    			return false;
//    		}
    	
	}
	public static boolean genFieldCons(SootMethod m) {
		boolean genF = true;
		if(solver.arg.combined) {
			/*
			 * The method has zero reachable fields
			 */
//			if(Solver.xMeths.contains(m)) {
//				genF = false;
//			}
			if(HelperAnalysis.zeroReach.contains(m)) {
				genF = false;
			}
			/*
			 * the method has no outgoing edges and no accessed fields
			 * in it
			 */
			else if(HelperAnalysis.tailNoField.contains(m)) {
				genF = false;
			}
		}
		return genF;
	}
	public static boolean ignoreMethod(SootMethod m, Body b) {
		
		boolean ign = false;
		
		
		if(solver.arg.combined) {

			if(HelperAnalysis.ignoredMeths.contains(m)) {
				ign = true;
				Set<Pair<SootMethod,SootMethod>> s = MyCG.HAedgesOutof.get(m);
    			if(s!=null && !s.isEmpty()) {
    				synchronized(solver) {
	    				for(Pair<SootMethod,SootMethod> p : s) {
	    					solver.recordCall(m, p.getValue());
	    					solver.recordProcessed(p.getValue());
	    				}
    				}
    			}
			}
			if(!ign && b!=null)
				ign = useHACallGraph(m,b);
			}

		/*
		 * If there are no useful statements, ignore
		 */
		if(!ign && b!=null)
			ign = ignIfNoUsefulStmts(m,b);

    	if(!ign) {
    		/*
    		 * Otherwise if it is one from the list of ignorable signatures, ignore it
    		 */
    		String methSig = m.getSignature(); 
			

	    	
	    	if(ignoreSignatures.contains(methSig)) {
	    		
	    		
	    		ign = true;
	    	}
	    	else {
	    		SootClass decl =  m.getDeclaringClass();
	    		
	    		String name = decl.getName();
	    		
	    		if(
				name.startsWith("java.io.")){
	    			if(!isInterestingType(m.getReturnType())) {
	    				ign =true;
	    			}
	    				
				}
	    		else if(name.startsWith("java.lang.System") 
	    				|| name.startsWith("java.lang.reflect")) {

	        		ign = true;
	    			}
	    	 if(m.getSubSignature().equals("java.lang.String toString()")) {
	    			ign =  true;
	    		}

	    		
	        	}
		}

    	
    	if(ign) {
    		synchronized(solver) {
    		
    			solver.ignoredMeths.add(m);
    		}
    		
    	}
		return ign;
	}
	public static boolean isLibRun(FunctionalConstraint callerFc) {
		boolean isLibrun = false;
		boolean threadType = false;
		String name = callerFc.method.getDeclaringClass().getName();
		if(callerFc.threadStart) {
			threadType = true;
		}
		
		else if(callerFc.loadRunCall) {
			threadType = true;
		}
		else if(callerFc.method.getName().equals("run")) {
			SootClass sc = callerFc.method.getDeclaringClass();
			
			if(isThreadClass(sc)) {
				threadType = true;
			}
		}
		if(threadType) {
			if(callerFc.method.getDeclaringClass().isLibraryClass())
				isLibrun = true;
		}
		return isLibrun;
	}
	private static boolean isThreadClass(SootClass sclass) {
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
	public static boolean isInterestingType(Type t) {
		/*
		 * Only reading the shared set some type.
		 * So no synchronization required
		 */
		boolean ret = true;
		
		if(t instanceof ArrayType) {
			t = ((ArrayType)t).baseType;
		}
		String name = t.toString();
		if(name.equals("void")) {
			ret = false;
		}
		else if(t instanceof PrimType)
			ret = false;
		else if(someTypes.contains(name)) {
			ret = false;
		}
		else if(name.contains("java.lang.String")) {
			ret = false;
		}
		return ret;
	}
	
	static ArrayList<String> ignoreSignatures = new ArrayList<>();
	 static ArrayList<String> someTypes = new ArrayList<>();
	static Solver solver;
	static {
		ignoreSignatures.add("<soot.rtlib.tamiflex.ReflectiveCalls: void <clinit>()>");
		ignoreSignatures.add("<java.lang.Object: void <clinit>()>");
		ignoreSignatures.add("<java.util.Objects: boolean equals(java.lang.Object,java.lang.Object)>");
		ignoreSignatures.add("<java.lang.System: void <clinit>()>");
		ignoreSignatures.add("<java.lang.Object: void <init>()>");
		ignoreSignatures.add("<java.lang.Exception: void <init>(java.lang.String)>");
		ignoreSignatures.add("<java.lang.Exception: void <init>()>");

		ignoreSignatures.add("<java.lang.RuntimeException: void <init>(java.lang.Throwable)>");
		ignoreSignatures.add("<java.lang.Error: void <init>(java.lang.String)>");
		ignoreSignatures.add("<java.lang.Throwable: void <init>(java.lang.String)>");
		ignoreSignatures.add("<java.lang.Throwable: void <clinit>()>");

		someTypes.add("java.lang.Integer");
		someTypes.add("java.lang.Boolean");
		someTypes.add("java.lang.Float");
		someTypes.add("java.lang.Double");
		someTypes.add("java.lang.Character");
		someTypes.add("java.lang.Long");
		someTypes.add("java.lang.Byte");
		someTypes.add("java.lang.Short");
		someTypes.add("java.lang.Double");
	}
}
