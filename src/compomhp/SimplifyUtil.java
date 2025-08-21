package compomhp;

import java.util.ArrayList;
import java.util.HashSet;
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
		if(method.getSignature().equals("<net.sourceforge.pmd.ast.JavaParser: boolean jj_2_1(int)>")) {
			System.out.println("stop");
		}
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
//				Set<SootMethod> rt = getReachableTails(method);
//				boolean allign = true;
//				for(SootMethod m : rt) {
//					if(!HelperAnalysis.ignoredMeths.contains(m)) {
//						allign = false;
//						//break;
//					}
//				}
    			return false;
//    		}
    	
	}
	private static Set<SootMethod> getReachableTails(SootMethod m){
		Set<SootMethod> rt = new HashSet<>();
		Set<SootMethod> visited = new HashSet<>();
		visited.add(m);
		ArrayList<SootMethod> wL = new ArrayList<>();
		wL.add(m);
		while(!wL.isEmpty()) {
			SootMethod sm = wL.remove(0);
			Set<Pair<SootMethod, SootMethod>> s = MyCG.HAedgesOutof.get(sm);
			visited.add(sm);
			if(s==null || s.isEmpty()) {
				rt.add(sm);
			}
			else {
			for(Pair<SootMethod,SootMethod> p : s) {
				SootMethod callee = p.getValue();
				Set<Pair<SootMethod, SootMethod>> out = MyCG.HAedgesOutof.get(callee);
				
				if(out==null ||out.isEmpty())
					rt.add(callee);
				else if(!visited.contains(callee))
					wL.add(callee);
					
//			 if(HelperAnalysis.ignoredMeths.contains()
				
			}
			}
		}
		
		return rt;
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
	public static boolean opaqueMethod(SootMethod m, Body b) {
		
		boolean ign = false;
		Type t = m.getDeclaringClass().getType();
		String sub = m.getSubSignature();
		if(!isInterestingType(t)) {
			ign = true;
		}
		if(!ign && solver.arg.combined) {

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
		

    	if(!ign) {
    		/*
    		 * Otherwise if it is one from the list of ignorable signatures, ignore it
    		 */
    		String methSig = m.getSignature(); 
			

	    	
	    	if(opqSignatures.contains(methSig)) {
	    		
	    		
	    		ign = true;
	    	}
//	    	else if(opqSubSignatures.contains(sub)) {
//	    		ign = true;
//	    	}
	    	else {
	    		SootClass decl =  m.getDeclaringClass();
	    		
	    		String name = decl.getName();
	    		
	    		if(
				name.startsWith("java.io.")){
	    			if(!isInterestingType(m.getReturnType())) {
	    				ign =true;
	    			}
	    				
				}
	    		else {
	    			for(String s:opqPackages) {
	    				if(name.startsWith(s)) {
	    					ign = true;
	    					break;
	    				}
	    			}
	    		}
	    	 if(m.getSubSignature().equals("java.lang.String toString()")) {
	    			ign =  true;
	    		}

	    		
	        	}
		}
    	if(!ign && b!=null)
			ign = ignIfNoUsefulStmts(m,b);
    	
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
	public static boolean isLibType(Type t) {
		/*
		 * Only reading the shared set some type.
		 * So no synchronization required
		 */
		boolean ret = false;
		
		if(t instanceof ArrayType) {
			t = ((ArrayType)t).baseType;
		}
		if(t instanceof RefType) {
			SootClass sc = ((RefType)t).getSootClass();
			if(sc.isLibraryClass() || sc.isJavaLibraryClass())
				ret = true;
		}
		return ret;
	}
	
	static ArrayList<String> opqSignatures = new ArrayList<>();
//	static ArrayList<String> opqSubSignatures = new ArrayList<>();
	 static ArrayList<String> someTypes = new ArrayList<>();
	 static ArrayList<String> opqPackages = new ArrayList<>();
	static Solver solver;
	static {
		opqSignatures.add("<soot.rtlib.tamiflex.ReflectiveCalls: void <clinit>()>");
		opqSignatures.add("<java.lang.Object: void <clinit>()>");
		opqSignatures.add("<java.util.Objects: boolean equals(java.lang.Object,java.lang.Object)>");
		opqSignatures.add("<java.lang.System: void <clinit>()>");
		opqSignatures.add("<java.lang.Object: void <init>()>");
		opqSignatures.add("<java.lang.Exception: void <init>(java.lang.String)>");
		opqSignatures.add("<java.lang.Exception: void <init>()>");

		opqSignatures.add("<java.lang.RuntimeException: void <init>(java.lang.Throwable)>");
		opqSignatures.add("<java.lang.Error: void <init>(java.lang.String)>");
		opqSignatures.add("<java.lang.Throwable: void <init>(java.lang.String)>");
		opqSignatures.add("<java.lang.Throwable: void <clinit>()>");
		
//		opqSubSignatures.add("boolean addAll(int,java.util.Collection");
//		opqSubSignatures.add("boolean addAll(java.util.Collection)");
//		opqSubSignatures.add("boolean batchRemove(java.util.Collection,boolean)");
//		opqSubSignatures.add("void clear()");
//		opqSubSignatures.add("java.lang.Object clone()");
//		opqSubSignatures.add("boolean contains(java.lang.Object)");
//		opqSubSignatures.add("boolean containsAll(java.util.Collection)");
//		opqSubSignatures.add("void fastRemove(int)");
//		opqSubSignatures.add("java.lang.Object remove(int)");
//		opqSubSignatures.add("boolean remove(java.lang.Object)");
//		opqSubSignatures.add("boolean removeAll(java.util.Collection)");
//		opqSubSignatures.add("boolean removeIf(java.util.function.Predicate)");
//		opqSubSignatures.add("void removeRange(int,int)");
//
//		opqSubSignatures.add("boolean containsKey(java.lang.Object)");
//		opqSubSignatures.add("boolean containsValue(java.lang.Object)");
//		opqSubSignatures.add("java.lang.Object remove(java.lang.Object)");
//		opqSubSignatures.add("void putAll(java.util.Map)");
//		opqSubSignatures.add("boolean remove(java.lang.Object,java.lang.Object)");
//		opqSubSignatures.add("boolean replace(java.lang.Object,java.lang.Object,java.lang.Object)");
//		opqSubSignatures.add("java.lang.Object replace(java.lang.Object,java.lang.Object)");
//		
		
		//do not contribute meaningful heap allocations
				opqPackages.add("java.lang.System");
				opqPackages.add("java.lang.reflect");
		
		/*
		 * CLI, test, tools packages	Ignore
		 * Logging, events, messages	Ignore
		 * Parsers, renderers, fonts	Stub/summarize
		 * Core logic (DB engine, layout engine)	Analyze or summarize selectively
		 */
//		opqPackages.add("org.apache.fop.cli"); // Command-line front-end
//		opqPackages.add("org.apache.fop.tools"); //Utilities and pre/post-processing
//		opqPackages.add("org.apache.fop.events"); //Logging and event handling
//		opqPackages.add("org.apache.fop.render"); // PDF/RTF/PS renderers; large, mostly output-related
//		opqPackages.add("org.apache.fop.fonts"); // Font management; expensive
//		/* FO tree logic; document semantics not required*/
////		opqPackages.add("org.apache.fop.fo.flow");
//		opqPackages.add("org.apache.fop.fo.pagination");
		
//		opqPackages.add("org.h2.bnf");// Grammar parser for SQL; irrelevant
//		opqPackages.add("org.h2.tools"); // CLI tools and utilities; not core to DB logic
//		opqPackages.add("org.h2.test"); // Tests and benchmarks
//		opqPackages.add("org.h2.index");//Indexing logic; can be skipped
//		//Logging and errors
//		opqPackages.add("org.h2.message"); 
//		opqPackages.add("org.h2.log");
//		
//		opqPackages.add("org.h2.util"); //Utility functions are generally simple
//		opqPackages.add("org.h2.tools");// Tools are peripheral to core database operations and often standalone.
//		opqPackages.add("org.h2.constraint"); //Constraints may be less critical if schema operations are out of scope, but they can reference tables.
//		opqPackages.add("org.h2.schema");// (with caution): Schemas are static metadata, but they’re referenced by other objects.
//		opqPackages.add("org.h2.store"); //(with caution): Storage operations are low-level and may be noise if you’re focused on query logic.
//		opqPackages.add("org.h2.jdbc");// (with caution): JDBC interfaces may be noise if you’re analyzing internal H2 logic, not client interactions.

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
