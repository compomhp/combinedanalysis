package compomhp;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import soot.ArrayType;
import soot.Body;
import soot.IntType;
import soot.Local;
import soot.LongType;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Type;
import soot.Value;
import soot.VoidType;
import soot.jimple.AssignStmt;
import soot.jimple.ClassConstant;
import soot.jimple.Constant;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.ExitMonitorStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.NullConstant;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.internal.JArrayRef;
import soot.jimple.internal.JCastExpr;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JNewArrayExpr;
import soot.jimple.internal.JReturnStmt;
import soot.tagkit.Tag;

public class GenConsPointsTo extends GenCons{
	boolean genPointsToOnly = false;
	
	public void setVarMap(MapName varMap) {
		this.varMap = varMap; 
	}
	public void setFieldMap(MapName fieldMap) {
		this.fieldMap = fieldMap; 
	}
	
	@Override
	public void gen(AssignStmt s1, Set<Stmt> preds) {
		Value vl = s1.getLeftOp();
		Value vr = s1.getRightOp();
		if(s1.containsInvokeExpr()){
			InvokeExpr ie = s1.getInvokeExpr();
			gen(s1,ie,preds);
		}
		else if(vl instanceof Local && vr instanceof Local ) {
			
			Local leftv =  (Local)vl;
			Local rightv =  (Local)vr;
			Object lsl  = getKey(s1, leftv);
			
			Object lsr = getKey(s1,rightv);
			PropagateConstraint copy = new PropagateConstraint(lsr, lsl, varMap, varMap, ConstType.pts);
			callerFc.addPropagate(copy);
			
			
			
		}
		
		else if(vl instanceof Local && vr instanceof JCastExpr ) {
			/*
			 * Cast expression
			 */
			
			
			Value v = ((JCastExpr)vr).getOp();
			
			if(v instanceof Local) {
				Local leftv = (Local)vl;
				Local rightv = (Local)v;
				
				Object lsl  = getKey(s1, leftv);
				
				if(!solver.typeCasts.containsKey(callerFc.method)) {
					solver.typeCasts.put(callerFc.method, new HashSet<>());
				}
				solver.typeCasts.get(callerFc.method).add(s1);
				Object lsr = getKey(s1,rightv);
				PropagateConstraint copy = new PropagateConstraint(lsr, lsl, varMap, varMap, ConstType.pts);
				callerFc.addPropagate(copy);
			}
		}
		
		else if(vl instanceof StaticFieldRef && vr instanceof Local ) {
			/*Static store*/
			
			StaticFieldRef sfr = (StaticFieldRef)vl;
			Local y = (Local)vr;
			SootField fl = sfr.getField();
			SootClass scc = fl.getDeclaringClass();
//			gen.outReachableLocals.add((Local)vr);
			Object s1y = getKey(s1, y);
			PropagateConstraint staticstore = new PropagateConstraint(s1y, fl, varMap, MapName.sfieldPts, ConstType.pts);
			callerFc.addPropagate(staticstore);
			
			
			gen.addClinitConstraint(scc, callerFc, s1, preds);
		}
		else if(vl instanceof Local && vr instanceof StaticFieldRef ) {
			/*
			 * Static load
			 */
			SootField fl = ((StaticFieldRef)vr).getField();
			SootClass scc = fl.getDeclaringClass();
			
//			gen.outReachableLocals.add((Local)vl);
			Object s2x = getKey(s1, (Local)vl);
			PropagateConstraint staticload = new PropagateConstraint(fl, s2x, MapName.sfieldPts, varMap, ConstType.pts);
			callerFc.addPropagate(staticload);
//			if(varMap == MapName.varPts) {
//				for(Stmt s2 : preds) {
//					StmtLocal s2x = new StmtLocal(s2, (Local)vl);
//					PropagateConstraint staticload = new PropagateConstraint(fl, s2x, MapName.sfieldPts, MapName.varPts, ConstType.pts);
//					callerFc.addPropagate(staticload);
//				}
//			}
//			else {
//				PropagateConstraint staticload = new PropagateConstraint(fl, (Local)vl, MapName.sfieldPts, MapName.ivarPts, ConstType.pts);
//				callerFc.addPropagate(staticload);
//			}
			gen.addClinitConstraint(scc, callerFc, s1, preds);
			
		}
		else if(vl instanceof Local && vr instanceof NewExpr) {
			/*
			 * New alloc
			 */
			Type t =((NewExpr)vr).getType();
			String cn = ((NewExpr)vr).getBaseType().getClassName();
			SootClass sclass = Scene.v().getSootClassUnsafe(cn);
			
//			Set<Local> newList = new HashSet<Local>();
//			newList.addAll(callerFc.methLocals);
//			newList.remove(vl);
			
			AllocNode an;
			if(solver.arg.combined) {
				an = HelperAnalysis.stmtAllocNodes.get(s1);
				if(an==null) {
					System.out.println("caught an null in "+callerFc.method.getSignature()+ "for st:"+s1.toString());
				}
				else if(an.isInLoop) {
					solver.allAllocsInLoop.add(an.allocSite);
				}
			}
			else {
				an = new AllocNode();
				an.allocSite = s1;
				an.anclass = sclass;
				
				
				
				an.allocSiteMeth = callerFc.method;
				if(Solver.intPass) {
					HelperAnalysis.stmtAllocNodes.put(s1, an);
				}
			}
				

				Object ls = getKey(s1, (Local)vl);
				MemConstraint objcreation = new MemConstraint(an ,ls,true,varMap, ConstType.pts);
				callerFc.addMember(objcreation);
				/*
				  * Process clinit method whenever there is a static reference
				  */
//				gen.addClinitConstraint(sclass, callerFc, s1);
		}
		else if(vl instanceof Local && vr instanceof NullConstant) {
			Object ls = getKey(s1, (Local)vl);
			MemConstraint objcreation = new MemConstraint(solver.nullRef ,ls,true,varMap, ConstType.pts);
			callerFc.addMember(objcreation);
		}
		
		else if(vl instanceof JInstanceFieldRef && vr instanceof Local ) {
			/*
			 * Store x.fl = y;
			 * */
			
			recordLoadStoreStmts(callerFc.method,s1);

		}
		
		else if(vl instanceof Local && vr instanceof JInstanceFieldRef ) {
			/*
			 * Load x = y.fl;
			 */
//			JInstanceFieldRef jfr = (JInstanceFieldRef)vr;
//			SootField sf = jfr.getField();
			if(fieldMap == MapName.fieldPts) {
				List<Tag> tags = s1.getTags();
				boolean tagFound = false;
				for (Tag tag : tags) {
		             if (tag instanceof MyTag) {
		                 MyTag myTag = (MyTag) tag;
		                 if (myTag.getTagValue().equals(FieldSummary.MY_TAG)) {
		                 	tagFound = true;
		                 	
		                 	break;
		                 }
		             }
		         }
					if(tagFound) {
						genLoadInSens(s1,preds);
					}
					else {
				genLoad(s1, preds);
					}
//				genLoadInSens(s1,succs);
			}
			else
				genLoadInSens(s1,preds);
//			gen.outReachableLocals.add((Local)vl);
			recordLoadStoreStmts(callerFc.method,s1);
//			if(!solver.loadf.containsKey(sf)) {
//				solver.loadf.put(sf, new HashSet<>());
//			}
//			solver.loadf.get(sf).add(s1);
			
		}
		
		else if(vl instanceof Local && vr instanceof JNewArrayExpr) {
			/*
			 * New array
			 */
				
				AllocNode an;
				if(solver.arg.combined) {
					an = HelperAnalysis.stmtAllocNodes.get(s1);
					if(an.isInLoop) {
						solver.allAllocsInLoop.add(an.allocSite);
					}
//					if(an==null) {
//						System.out.println("caught");
//					}
				}
				else {
				an = new AllocNode();
				an.allocSite = s1;
				an.anclass = solver.arrayRepClass;
				//an.count = counter;
				
				an.allocSiteMeth = callerFc.method;
//				an.arrayType = true;
				if(Solver.intPass) {
					HelperAnalysis.stmtAllocNodes.put(s1, an);
				}
				}
				
				//gen.genfieldPCopy(s1, succs, false);
				
//				for(Stmt s2 : preds) {
//					
//					StmtLocal ls = new StmtLocal(s2, (Local)vl);
//					
//					MemConstraint newArr = new MemConstraint(an ,ls,true,MapName.varPts, ConstType.pts);
//					
//					callerFc.addMember(newArr);
//				}
				Object ls = getKey(s1, (Local)vl);
				
				MemConstraint newArr = new MemConstraint(an ,ls,true,varMap, ConstType.pts);
				
				callerFc.addMember(newArr);
		}
		else if(vl instanceof Local && vr instanceof JArrayRef) {
		/*
		 * Array element load
		 */
			
			Value v = ((JArrayRef)vr).getBase();
			
			
			
			
			
			if(v instanceof Local) {
				SootField f = Solver.arrayEleField;
				AllocNodeField anf = new AllocNodeField(null, f);
				Object ls = getKey(s1, (Local)v);
//				for(Stmt s2 : preds) {
//				
//					StmtLocal s2vl = new StmtLocal(s2, (Local)vl);
//					PropagateConstraint pc = new PropagateConstraint(anf,s2vl, MapName.afieldPts, MapName.varPts, ConstType.pts);
//					ConditionalConstraint arrLoad = new ConditionalConstraint(ls, pc, MapName.varPts, null, ConstType.pts);
//					callerFc.addConditional(arrLoad);
//				}
				Object s2vl = getKey(s1, (Local)vl);
				PropagateConstraint pc = new PropagateConstraint(anf,s2vl, MapName.afieldPts, varMap, ConstType.pts);
				ConditionalConstraint arrLoad = new ConditionalConstraint(ls, pc, varMap , null, ConstType.pts);
				callerFc.addConditional(arrLoad);
							
			}
		}
		else if( vl instanceof JArrayRef && vr instanceof Local ) {
			/*
			 * Array element store
			 */
			
			Value v = ((JArrayRef)vl).getBase();

			if(v instanceof Local) {
				SootField f = Solver.arrayEleField;
				AllocNodeField anf = new AllocNodeField(null, f);
				Object s1v = getKey(s1, (Local)v);

				Object s2vr = getKey(s1, (Local)vr);
				PropagateConstraint pc = new PropagateConstraint(s2vr,anf, varMap, MapName.afieldPts, ConstType.pts);
				ConditionalConstraint arrStore = new ConditionalConstraint(s1v, pc, varMap, null, ConstType.pts);
				callerFc.addConditional(arrStore);
				
			}
		}
		
		
	}

	@Override
	public void gen(InvokeStmt s1, Set<Stmt> preds) {
		InvokeExpr ie = s1.getInvokeExpr();
		gen(s1,ie,preds);
		
	}

	@Override
	public void gen(ReturnStmt s1, Set<Stmt> preds) {
		 
		if(callerFc.callSite!=null)
			if(SimplifyUtil.genFieldCons(callerFc.method) && solver.arg.combined)
			genfieldPCopy(s1, callerFc.callSite);
		
		if(gen.retStmts == null) {
			gen.retStmts = new ArrayList<Stmt>();
			
		}
		
		gen.retStmts.add(s1);
			if(gen.retLocal != null ) {
				
				Value v = s1.getOp();
				
				
					if(v instanceof Local && SimplifyUtil.isInterestingType(v.getType())) {
						/*
						 * Add copy constraint for ret variable
						 */
						Object lsr = getKey(gen.callSite, gen.retLocal);
						Object ls = getKey(s1, (Local)v);
						PropagateConstraint retC = new PropagateConstraint(ls, lsr, varMap, varMap, ConstType.pts);
						callerFc.addPropagate(retC);
						
					}
					else if(v instanceof ClassConstant) {
						ClassConstant cc = (ClassConstant)v;
						Type t = cc.toSootType();
						if(t instanceof RefType) {
							String cn = ((RefType)cc.toSootType()).getClassName();
							SootClass sclass = Scene.v().getSootClassUnsafe(cn);
							
							if(!sclass.isLibraryClass()) {
								//int counter = solver.allocNodes.size();
								AllocNode an;
								if(solver.arg.combined) {
									an = HelperAnalysis.stmtAllocNodes.get(s1);
									if(an.isInLoop) {
										solver.allAllocsInLoop.add(an.allocSite);
									}
//									if(an==null) {
//										System.out.println("caught");
//									}
								}
								else {
								 an = new AllocNode();
								an.allocSite = s1;
								an.anclass = sclass;
								an.allocSiteMeth = callerFc.method;
								//an.count = counter;
								
							
								if(Solver.intPass) {
									HelperAnalysis.stmtAllocNodes.put(s1, an);
								}
								}
								//solver.addAlloc(an);
								Object ls = getKey(s1, gen.retLocal);
								MemConstraint ccObjCre = new MemConstraint(an , ls,true, varMap, ConstType.pts);
								callerFc.addMember(ccObjCre);
	
							}
						}
					}
				
			}
		
	}

	@Override
	public void gen(ReturnVoidStmt s1, Set<Stmt> preds) {
		if(gen.retStmts == null) {
			gen.retStmts = new ArrayList<Stmt>();
			
		}
		gen.retStmts.add(s1);
		if(callerFc.callSite!=null && solver.arg.combined)
			if(SimplifyUtil.genFieldCons(callerFc.method))
			genfieldPCopy(s1, callerFc.callSite);
		
	}

	@Override
	public void gen(EnterMonitorStmt s1, Set<Stmt> succs) {
		 /*
         * Add monitorStmts(S1) to sync(r)
         */
//		if(Solver.intPass) {
			Value value = s1.getOp();
	        Object ls = getKey(s1, (Local)value);
	        PropagateConstraint pp = new PropagateConstraint(s1, null, MapName.monitorStmts, MapName.sync, ConstType.depOnPts);
	        pp.name = ConstraintName.ARR_STORE;
			ConditionalConstraint addToSync = new ConditionalConstraint(ls, pp, varMap, null, ConstType.depOnPts);
			addToSync.name = ConstraintName.CC_NEW;
			callerFc.addConditional(addToSync);
			
//		}
		
	}

	@Override
	public void gen(ExitMonitorStmt s1, Set<Stmt> succs) {
		
		
	}
	public void gen(Stmt s1, InvokeExpr ie, Set<Stmt> preds) {
		
//		genVarPCopy(callerFc.methLocals, s1, preds);
		

		if(ie instanceof StaticInvokeExpr) {
			
			
//			if(solver.ignoredMeths.contains(method)) {
				
			
			FunctionalConstraint fc = new FunctionalConstraint(ConstType.pts);
					
					
			fc.callSite = s1;
		
			fc.callSiteRDefMap = gen.reachDefMap.get(s1);
			fc.callSitePreds = preds;
			fc.fieldIntPreds = gen.methFIntPreds.get(s1);
			fc.caller = callerFc;		
			if(!gen.hasParallelConst) {
				fc.callerSkipped = true;
				fc.callerFirstS = gen.firstS;
			}
					
//		    Body b = Solver.getBody(method);
//		    if(b != null) {
			           		/*
			        		 * Add copy constraints and process the method body
			        		 */
		    	fc.populateFromCallSite();
		    	//fc.genEveryMethod();
		        callerFc.ffunc.add(fc);        		
//		    }
					
//			gen.addClinitConstraint(method.getDeclaringClass(), callerFc, s1, succs);

			 
		}
		else if(ie instanceof SpecialInvokeExpr) {
			FunctionalConstraint fc = new FunctionalConstraint(ConstType.pts);

			
			
			fc.callSite = s1;
			fc.callSiteRDefMap = gen.reachDefMap.get(s1);
			fc.callSitePreds = preds;
			fc.fieldIntPreds = gen.methFIntPreds.get(s1);
			fc.caller = callerFc;
			if(!gen.hasParallelConst) {
				fc.callerSkipped = true;
				fc.callerFirstS = gen.firstS;
			}
			
//	    	Body b = Solver.getBody(m);
//
//			if(b != null) {
				fc.populateFromCallSite();
				//fc.genEveryMethod();
				 callerFc.ffunc.add(fc);
						
//	    	}
			
		}
		else if(ie instanceof InterfaceInvokeExpr) {
			
			
			SootMethodRef method = ie.getMethodRef();
			Local r = (Local)((InterfaceInvokeExpr)ie).getBase();
			Object ls = getKey(s1, r);
			List<Type> paras = method.getParameterTypes();
//			Type retType = method.getReturnType();
			boolean interested = false;
			
			if ((method.getName().equals("submit")  
					|| method.getName().equals("execute") 
//					|| method.getName().equals("invokeAll")
//					|| method.getName().equals("invokeAny")
					) && paras.size() == 1) {
				
				 String declClass = method.getDeclaringClass().getName();	
//				 SootClass esClass = Scene.v().getSootClass("java.util.concurrent.ExecutorService");
//				 List<SootClass> runnableImplList = h.getDirectImplementersOf(esClass);
//				 if(runnableImplList.contains(esClass)) {
//					 threadclass = true;
//				 }
				 if(declClass.equals("java.util.concurrent.ExecutorService") 
						 || declClass.equals("java.util.concurrent.ForkJoinPool") 
						 || declClass.equals("java.util.concurrent.ForkJoinTask")) {
					interested = true;
					FunctionalConstraint fc = new FunctionalConstraint(ConstType.pts);
					fc.callSite = s1;
					fc.callSiteRDefMap = gen.reachDefMap.get(s1);
					fc.callSitePreds = preds;
					fc.callSiteSuccs = gen.methInterestingStmts.get(s1);
					fc.fieldIntPreds = gen.methFIntPreds.get(s1);
					fc.caller = callerFc;
					fc.exSubmit = true;
//					if(solver.arg.useCHA) {
//						fc.useCHA = true;
//						callerFc.ffunc.add(fc);
//					}
//					if(solver.arg.combined && solver.arg.bot && !Solver.intPass) {
//						if(InterestingFieldPass.botLocals.contains(ls)) {
//							fc.useCHA = true;
//							fc.populateFromCallSite();
//							fc.addConsForExecSubmit();
//							//callerFc.ffunc.add(fc);
//						}
//					}
					if(!fc.useCHA) {
						ConditionalConstraint cc = new ConditionalConstraint(ls,fc, varMap, null, ConstType.pts);
						callerFc.addConditional(cc);
					}
					
						System.out.println("Constraint executorservice submit call: "+method.getSignature()+"for all r in varPts("+r.getName()+"), ");
					
				 }
			}
			/*
			 * Generate a conditional constraint of function
			 */
			else if(!interested) {
				FunctionalConstraint fc = new FunctionalConstraint(ConstType.pts);
				
				
				fc.callSite = s1;
				fc.callSiteRDefMap = gen.reachDefMap.get(s1);
				fc.callSitePreds = preds;
				fc.callSiteSuccs = gen.methInterestingStmts.get(s1);
				fc.fieldIntPreds = gen.methFIntPreds.get(s1);
				fc.caller = callerFc;
				if(!gen.hasParallelConst) {
					fc.callerSkipped = true;
					fc.callerFirstS = gen.firstS;
				}
				
				if(!solver.arg.interleaved) {
					fc.useCHA = true;
					callerFc.ffunc.add(fc);
				}
//				if(solver.arg.combined && solver.arg.bot && !Solver.intPass) {
//					if(InterestingFieldPass.botLocals.contains(ls)) {
//						fc.useCHA = true;
//						fc.populateFromCallSite();
//						callerFc.ffunc.add(fc);
//					}
//				}
				if(!fc.useCHA) {
					ConditionalConstraint cc = new ConditionalConstraint(ls,fc, varMap, null, ConstType.pts);
					callerFc.addConditional(cc);
				}
			}
		}
		/*
		 * there can be dynamic invoke
		 */
		else if(ie instanceof VirtualInvokeExpr) {
			
			Value rcvr = ((VirtualInvokeExpr)ie).getBase();
			SootMethodRef method = ie.getMethodRef();
			Type retType = method.getReturnType();
			String name = method.getName();
			List<Type> paras = method.getParameterTypes();
			boolean interested = false;
			Object ls = getKey(s1, (Local)rcvr);
			if ((method.getName().equals("submit")  
					|| method.getName().equals("execute") 
					) && paras.size() == 1) {
				
				 String declClass = method.getDeclaringClass().getName();	
				 if(declClass.equals("java.util.concurrent.ForkJoinPool")) {
					interested = true;
					FunctionalConstraint fc = new FunctionalConstraint(ConstType.pts);
					fc.callSite = s1;
					fc.callSiteRDefMap = gen.reachDefMap.get(s1);
					fc.callSitePreds = preds;
					fc.callSiteSuccs = gen.methInterestingStmts.get(s1);
					fc.fieldIntPreds = gen.methFIntPreds.get(s1);
					fc.caller = callerFc;
					fc.exSubmit = true;

					if(!fc.useCHA) {
						ConditionalConstraint cc = new ConditionalConstraint(ls,fc, varMap, null, ConstType.pts);
						callerFc.addConditional(cc);
					}
					
						System.out.println("Constraint executorservice submit call: "+method.getSignature()+"for all r in varPts("+((Local)rcvr).getName()+"), ");
					
				 }
			}
			else if (method.getName().equals("start") && retType instanceof VoidType && paras.size() == 0) {
		        boolean threadStart = gen.isThreadClass(method.getDeclaringClass());
		        if(threadStart) {
		        	interested = true;
//		        	if(genPointsToOnly && !solver.arg.mhp) {
						/*
						 * Add functional constraint for run method 
						 */
						Local r = (Local)rcvr;
						FunctionalConstraint fc = new FunctionalConstraint(ConstType.pts);
						fc.callSite = s1;
						fc.callSiteRDefMap = gen.reachDefMap.get(s1);
						fc.callSitePreds = preds;
						fc.callSiteSuccs = gen.methInterestingStmts.get(s1);
						fc.fieldIntPreds = gen.methFIntPreds.get(s1);
						fc.caller = callerFc;
						fc.threadStart = true;
						if(!solver.arg.interleaved) {
							fc.useCHA = true;
							callerFc.ffunc.add(fc);
						}

						if(!fc.useCHA) {
							ConditionalConstraint cc = new ConditionalConstraint(ls,fc, varMap, null, ConstType.pts);
							callerFc.addConditional(cc);
						}
						
							System.out.println("Constraint start method call: "+method.getSignature()+"for all r in varPts("+r.getName()+"), ");
						
//		        	}
	        
		        }
		      }
			else if(method.getName().equals("join") && retType instanceof VoidType && (paras.size() == 0 || (paras.size() == 1 && (Type) paras.get(0) instanceof LongType)
			          || (paras.size() == 2 && (Type) paras.get(0) instanceof LongType && (Type) paras.get(1) instanceof IntType))) {
			
					boolean threadJoin = gen.isThreadClass(method.getDeclaringClass());
			        if(threadJoin) {
			        	
			        	interested = true;
			        }
				
			}
			else if (name.equals("wait") && retType instanceof VoidType && (paras.size() == 0 || (paras.size() == 1 && (Type) paras.get(0) instanceof LongType)
			          || (paras.size() == 2 && (Type) paras.get(0) instanceof LongType && (Type) paras.get(1) instanceof IntType))) {
				/*
				 * No need to check if it is thread class as wait, notify, notifyAll methods are of java.lang.Object class and are final and can't be overridden
				 */

			      
				interested = true;
				
			      }
			
			/*method call*/
			if (!interested){
				
				
				/*
				 * Generate a conditional constraint of function
				 */
				
				FunctionalConstraint fc = new FunctionalConstraint(ConstType.pts);
				fc.method = null;
				fc.callSite = s1;
//				if(s1.toString().equals("$r9 = virtualinvoke $r7.<java.lang.reflect.Constructor: java.lang.Object newInstance(java.lang.Object[])>($r8)")) {
//					System.out.println("caught");
//				}
				fc.callSitePreds = preds;
				fc.callSiteRDefMap = gen.reachDefMap.get(s1);
				fc.callSiteSuccs = gen.methInterestingStmts.get(s1);
				fc.fieldIntPreds = gen.methFIntPreds.get(s1);
				fc.caller = callerFc;
//				if(s1.toString().equals("$r2 = virtualinvoke r0.<avrora.sim.Simulation: avrora.sim.Simulation$Node newNode(int,avrora.sim.platform.PlatformFactory,avrora.core.LoadableProgram)>(i0, r5, r1)")) {
//					fc.name=ConstraintName.INNER_COND;
//				}
				if(!gen.hasParallelConst) {
					fc.callerSkipped = true;
					fc.callerFirstS = gen.firstS;
				}
				if(!solver.arg.interleaved) {
					fc.useCHA = true;
					callerFc.ffunc.add(fc);
				}
//				else {
//					ConditionalConstraint funCall = new ConditionalConstraint(ls,fc, MapName.varPts, null, ConstType.pts );
//					callerFc.addConditional(funCall);
//				}
//				if(solver.arg.combined && solver.arg.bot && !Solver.intPass) {
//					if(InterestingFieldPass.botLocals.contains(ls)) {
//						fc.useCHA = true;
//						fc.populateFromCallSite();
//						callerFc.ffunc.add(fc);
//					}
//				}
				if(!fc.useCHA) {
					ConditionalConstraint cc = new ConditionalConstraint(ls,fc,varMap, null, ConstType.pts);
					callerFc.addConditional(cc);
				}
				
				
			
			}
		}
	}
	

	@Override
	public void genDefault(Stmt s1, Set<Stmt> succs) {
		
//		genVarPCopy(callerFc.methLocals, s1, succs);
	}

public void genRefFieldCopy() {
	boolean genF = true;
	if(solver.arg.combined) {
		if(HelperAnalysis.zeroReach.contains(callerFc.method)) {
			genF = false;
		}
	
		if(genF && !callerFc.method.getDeclaringClass().isLibraryClass()) {
			
			if(callerFc.caller != null) {
				
				PropagateConstraint reFields = new PropagateConstraint(callerFc.method, callerFc.caller.method, MapName.refFields, MapName.refFields, ConstType.pts);
				callerFc.addPropagate(reFields);

			}
		}
	}
	}
	
	
	@Override
	public void genEveryMethod() {
		Body b = null;

		if(callerFc.method.hasActiveBody())
			b = callerFc.b;

		if(b!=null ) {
		super.genEveryMethod();
			if(callerFc.invokeExpr != null) {
				
						addParameterCopy(b);

					if(fieldMap==MapName.fieldPts /*&& callerFc.ref != solver.bottom*/) {
						if(callerFc.caller!=null ) {
							boolean genCons = true;
							genCons = SimplifyUtil.genFieldCons(callerFc.method);
							
							if(genCons) {

								Stmt firstS = (Stmt) b.getUnits().getFirst();
								if(callerFc.fieldIntPreds!=null) {
									for(Stmt s: callerFc.fieldIntPreds) {
											genfieldPCopy(s, firstS);
									}
								}
								if( solver.arg.combined) {
									/*
									 * From the caller pass only the interesting fields
									 */
									MemConstraint m = new MemConstraint(null, callerFc.method, false, MapName.refFields, ConstType.pts);
									ConditionalConstraint fcond = new ConditionalConstraint(callerFc.method, m, MapName.methFields,null, ConstType.pts);
									ConditionalConstraint refCond = new ConditionalConstraint(callerFc.caller.method, fcond, MapName.refFields, null, ConstType.pts);
									
									callerFc.addConditional(refCond);
									
									
								}

							}

							
						}
					}
				
				

				/*
				 * add method in inclMeths(method)
				 */
				MemConstraint addMeth = new MemConstraint(callerFc.method, callerFc.method,false,  MapName.reachableFuncs, ConstType.pts);
				callerFc.addMember(addMeth);
				/*
				 * Propagate inClMeths to caller
				 */
				if(callerFc.caller != null && callerFc.caller.method != null) {
					PropagateConstraint inclCopy = new PropagateConstraint(callerFc.method, callerFc.caller.method, MapName.reachableFuncs, MapName.reachableFuncs, ConstType.pts);
					callerFc.addPropagate(inclCopy);
				}
				/*
				 * in case of instanceinvokeexpr, add the method in callSiteMeths
				 */
//				if(callerFc.invokeExpr instanceof InstanceInvokeExpr ) {
					MemConstraint callSiteMem = new MemConstraint(callerFc.method , callerFc.callSite,false, MapName.funcsAtCallSite, ConstType.pts);
					callerFc.addMember(callSiteMem);
					MemConstraint cs = new MemConstraint(callerFc.callSite, callerFc.method,false, MapName.callSites, ConstType.pts);
					callerFc.addMember(cs);
//				}
				
//				}
			}
				
			}
	}
	

	private void updateEscape() {
		List<Value> la = callerFc.invokeExpr.getArgs();
		Local rcvr = callerFc.rcvr;
		
		Iterator<Value> itr = la.iterator(); 
		/*
		 * For each parameter local pl
		 *  varPts(callSite, pl) in escapeAt(callSiteSucc),
		 */
		if(callerFc.callSiteSuccs!=null) {
			for(Stmt succ : callerFc.callSiteSuccs) {
				if(rcvr != null) {
					Object lsa = getKey(callerFc.callSite, rcvr);
					PropagateConstraint pc = new PropagateConstraint(lsa, succ, varMap, MapName.escapeAt, ConstType.pts);
					
					//cc.name = ConstraintName.CC_NEW;
					callerFc.addPropagate(pc);
				}
				while(itr.hasNext()) {
					Value vl = itr.next();
					if(vl instanceof Local) {
						Object lsa = getKey(callerFc.callSite, (Local)vl);
						PropagateConstraint pc = new PropagateConstraint(lsa, succ, varMap, MapName.escapeAt, ConstType.pts);
						callerFc.addPropagate(pc);
					}
				}
			}
		}
	}
	public void addParameterCopy(Body b) {
		List<Value> callSiteArgs = callerFc.invokeExpr.getArgs();
		List<Local> paraArgs = b.getParameterLocals();
		Stmt firstS = (Stmt) b.getUnits().getFirst();
		Local thisL = null;
		if(!callerFc.method.isStatic()) {
		 thisL = b.getThisLocal();
		
			if(thisL != null && callerFc.rcvr != null /*&& callerFc.ref != solver.bottom*/) {
				if(varMap==MapName.varPts) {
			Set<Stmt> lPreds = callerFc.callSiteRDefMap.get(callerFc.rcvr);
				if(lPreds != null) {
					for(Stmt st: lPreds) {
						Object lsr = getKey(st, callerFc.rcvr);
						Object lst = getKey(firstS, thisL);
						PropagateConstraint thisCopy = new PropagateConstraint(lsr,lst, varMap, varMap, ConstType.pts);
						callerFc.addPropagate(thisCopy);
					}
				}
			}
				else {
					PropagateConstraint thisCopy = new PropagateConstraint(callerFc.rcvr,thisL, varMap, varMap, ConstType.pts);
					callerFc.addPropagate(thisCopy);
				}
			}
		}
		if(!callerFc.loadRunCall) {
	    	Iterator<Value> itr = callSiteArgs.iterator(); 
			Iterator<Local> itr1 = paraArgs.iterator();
			
		
			
			while(itr.hasNext()) {
				Value vl = itr.next();
				Local vr = itr1.next();
	    		if(vl instanceof Local && SimplifyUtil.isInterestingType(vl.getType())) {
	    			if(varMap == MapName.varPts) {
	    			Set<Stmt> lPreds = callerFc.callSiteRDefMap.get(vl);
	    			if(lPreds != null) {
		    			for(Stmt pred : lPreds) {
			    			Object lsa = getKey(pred, (Local)vl);
			    			Object lsf = getKey(firstS, vr);
			    			PropagateConstraint parVCopy = new PropagateConstraint(lsa, lsf,varMap, varMap, ConstType.pts);
							
							callerFc.addPropagate(parVCopy);
		    			}
	    			}
	    			}
	    			else {
	    				PropagateConstraint parVCopy = new PropagateConstraint((Local)vl, vr,varMap, varMap, ConstType.pts);
						
						callerFc.addPropagate(parVCopy);
	    			}
				}
//	    		else if(vl instanceof ClassConstant) {
//	    		
//						ClassConstant cc = (ClassConstant)vl;
//						
//						Type t = cc.toSootType();
//						if(t instanceof RefType && ((RefType) t).hasSootClass()) {
//							
//							String cn = ((RefType)cc.toSootType()).getClassName();
//							
//							SootClass sclass = Scene.v().getSootClassUnsafe(cn, false);
//							
//							if(sclass!= null && !sclass.isLibraryClass()) {
//								
//								AllocNode an = new AllocNode();
//								an.allocSite = callerFc.callSite;
//								an.anclass = sclass;
//			
//								an.stmtsProcessed = false;
//								an.allocSiteMeth = callerFc.method;
//								
//								Object ls = getKey(firstS, vr);
//								MemConstraint ccObjCre = new MemConstraint(an ,ls,true, varMap, ConstType.pts);
//								
//								callerFc.addMember(ccObjCre);
//								
//							}
//						}
//	    			
//				}
			}
		}
    }

	@Override
	public void genProcessed() {
		BitSet retStmts = solver.methRet.get(callerFc.method);
		genRefFieldCopy();
		if(retStmts != null) {
			int i = retStmts.nextSetBit(0);
			while(i!=-1) {
				Stmt st = solver.stmtList.get(i);
				/*
				 * copy the fields
				 */
				if(fieldMap== MapName.fieldPts)
				if(SimplifyUtil.genFieldCons(callerFc.method))
					genfieldPCopy(st, callerFc.callSite);
				if(callerFc.retLocal != null ) {
				Local rl = callerFc.retLocal;
				if(SimplifyUtil.isInterestingType(rl.getType())) {
					Stmt s = solver.stmtList.get(i);
					if(s instanceof JReturnStmt) {
					JReturnStmt rs = (JReturnStmt)s;
					Value v = rs.getOp();
					if(!(v instanceof Constant))	{
						Object ls1 = getKey(rs, (Local)v);
						if(callerFc.callSite != null) {
//							for(Stmt succ : callerFc.callSiteSuccs) {
								Object ls2 = getKey(callerFc.callSite, callerFc.retLocal);
								PropagateConstraint retC = new PropagateConstraint(ls1,ls2, varMap, varMap, ConstType.pts);
								
								callerFc.addPropagate(retC);
								
								
//							}
						}
					}
					}
				}
				}
				i = retStmts.nextSetBit(i+1);
			}
			
		}
		
	}

	@Override
	public void genThreadRun(Stmt s1) {
		// TODO Auto-generated method stub
		if(Solver.intPass) {
			
			SootClass rcvrType = callerFc.method.getDeclaringClass();
//			PropagateConstraint threadRunMhp = new PropagateConstraint(null, rcvrType, MapName.methStmts, MapName.runStmtsIP, ConstType.depOnPts);
//			ConditionalConstraint inclMeths = new ConditionalConstraint(callerFc.method, threadRunMhp, MapName.reachableFuncs, null, ConstType.depOnPts );
//			threadRunMhp.name = ConstraintName.LOAD;
//			callerFc.addConditional(inclMeths);
			PropagateConstraint threadRunMhp = new PropagateConstraint(null, rcvrType, MapName.methRep, MapName.runStmtsHA, ConstType.depOnPts);
			ConditionalConstraint inclMeths = new ConditionalConstraint(callerFc.method, threadRunMhp, MapName.reachableFuncs, null, ConstType.depOnPts );
			
			callerFc.addConditional(inclMeths);
			
		}
	}

	@Override
	public void genFieldCons() {
		
		if(fieldMap == MapName.fieldPts) {
			Stmt s1;
			for(Map.Entry<Stmt, Set<Stmt>> ele : gen.methFIntPreds.entrySet()) {
				s1 = ele.getKey();
				
				
					Set<Stmt> preds = ele.getValue();
					
					if(s1 instanceof AssignStmt && isStore((AssignStmt)s1)) {
						if(!callerFc.method.getDeclaringClass().isLibraryClass()) {
							List<Tag> tags = s1.getTags();
							boolean tagFound = false;
							for (Tag tag : tags) {
				                if (tag instanceof MyTag) {
				                    MyTag myTag = (MyTag) tag;
				                    if (myTag.getTagValue().equals(FieldSummary.MY_TAG)) {
				                    	tagFound = true;
				                    	
				                    	break;
				                    }
				                }
				            }
							if(tagFound) {
								genStoreInSens(s1);
								genfieldPCopy(s1,preds);
							}
							else
							genStore(s1,preds);
						}
	//					genStoreInSens(s1,succs);
					}
					else
						genfieldPCopy(s1,preds);
				
				
			}
		}
		else {
			Stmt s1;
			for(Map.Entry<Stmt, Set<Stmt>> ele : gen.methIntPreds.entrySet()) {
				s1 = ele.getKey();
//				if(s1.toString().equals("r0.<org.dacapo.harness.TestHarness: org.dacapo.parser.Config config> = $r18")) {
//					System.out.println("-------------Processing : "+ s1+"---------------");
//				}
				
				//Set<Stmt> preds = ele.getValue();
				
				if(s1 instanceof AssignStmt && isStore((AssignStmt)s1)) {
					genStoreInSens(s1);
				}
				
			}
		}
		
	}
	public void genfieldPCopy(Stmt s1, Set<Stmt> preds) {
		
			if(preds != null) {
	
					for(Stmt sp : preds) {
						genfieldPCopy(sp,s1);
					}

			}

	}
	 public void genfieldPCopy(Stmt s1, Stmt s2) {
	    	
		
			
			PropagateConstraint pc1 = new PropagateConstraint(s1, s2, MapName.fieldPts, MapName.fieldPts, ConstType.pts);

				ConditionalConstraint refCond = new ConditionalConstraint(callerFc.method, pc1, MapName.refFields, null, ConstType.pts);
				callerFc.addConditional(refCond);
			
		}
	 public void genStore(Stmt s1, Set<Stmt> preds) {
			/*
			 * Store x.fl = y;
			 * */
			Value vl = ((AssignStmt)s1).getLeftOp();
			Value vr = ((AssignStmt)s1).getRightOp();
			JInstanceFieldRef jfr = (JInstanceFieldRef)vl;
			SootField fl = jfr.getField();
			//gen.methFields.add(fl);
			Value base_x = jfr.getBase(); 
			Local y = (Local)vr;
			
			if(base_x instanceof Local) {
				
				StmtLocal s1x = new StmtLocal(s1, (Local)base_x);
				StmtLocal s1y = new StmtLocal(s1, y);
				StmtAllocNodeField s1rf = new StmtAllocNodeField(s1, null);
				RefFieldKey rfk = new RefFieldKey();
				rfk.an = null;
				rfk.mn = MapName.varPts;
				rfk.key = s1x;
				rfk.sf = fl;
				
				//genVarPCopy(callerFc.methLocals, s1, succs);
				AllocNodeField anf = new AllocNodeField(null,fl);
//				if(preds != null) {
//				for(Stmt s2 : succs) {	
//					
//					
//					
//				
//					
//					
//				}
//				if(gen.fieldInterestingStmts.containsKey(s1)) {
//					succs = gen.fieldInterestingStmts.get(s1);
//					solver.loadStoreSuccs.put(s1, preds);
					MemConstraint addinRefFieldList = new MemConstraint(anf, callerFc.method, false, MapName.refFields, ConstType.pts);
//					addinRefFieldList.name = ConstraintName.ADDTOSYNC_SYNC;
					ConditionalConstraint rinVarpts = new ConditionalConstraint(s1x, addinRefFieldList, MapName.varPts, null, ConstType.pts);
					callerFc.addConditional(rinVarpts);
//					MemConstraint addinRefFieldList1 = new MemConstraint(anf, callerFc.method, false, MapName.refFields, ConstType.pts);
//					addinRefFieldList1.name = ConstraintName.ADDTOSYNC_SYNC;
//					ConditionalConstraint rinVarpts1 = new ConditionalConstraint(s1x, addinRefFieldList1, MapName.varPts, null, ConstType.pts);
//					callerFc.addConditional(rinVarpts1);
//					for(Stmt sp : preds) {
						
						/*
						 *  The varPts(S1,y) will flow into fieldPts(S2,r,fl) for r in varPts(S1,x)
						 */
						
						StmtAllocNodeField s1rfl = new StmtAllocNodeField(s1, anf);
						PropagateConstraint pc3 = new PropagateConstraint(s1y, s1rfl, MapName.varPts, MapName.fieldPts, ConstType.pts);
						ConditionalConstraint storeCopys2 = new ConditionalConstraint(s1x, pc3, MapName.varPts, null, ConstType.pts);
						callerFc.addConditional(storeCopys2);
						
						
						
						/*
						 * The fieldPts of all fields except that of r.fl for r in varPts(S1,x) will flow from Sp to S1 in case of strong update
						 */
						StmtAllocNodeField anfs1 = new StmtAllocNodeField(s1, null);
						preds = gen.methFIntPreds.get(s1);
						for(Stmt sp : preds) {
						StmtAllocNodeField sprf = new StmtAllocNodeField(sp, null);
						PropagateConstraint pc = new PropagateConstraint(sprf, s1rf, MapName.fieldPts, MapName.fieldPts, ConstType.pts);
						ConditionalConstraint dm = new ConditionalConstraint(fl, pc, MapName.exclField, null, ConstType.pts );
						ConditionalConstraint storeCopyRemF = new ConditionalConstraint(callerFc.method, dm, MapName.refFields, null, ConstType.pts);
//						callerFc.addConditional(storeCopyRemF);
						StmtAllocNodeField anfsp = new StmtAllocNodeField(sp, null);
						
						
						PropagateConstraint pc1 = new PropagateConstraint(anfsp, anfs1, MapName.fieldPts, MapName.fieldPts, ConstType.pts);

							ConditionalConstraint refCond = new ConditionalConstraint(callerFc.method, pc1, MapName.refFields, null, ConstType.pts);
//							callerFc.addConditional(refCond);
						/*
						 * in case of weak update, fieldPts(S1,r,fl) will also flow into fieldPts(S2,r,fl)
						 * so copy all fieldPts from Sp to S1 
						 * else 
						 * he fieldPts of all fields except that of r.fl for r in varPts(S1,x) will flow from Sp to S1
						 */
						ConditionalConstraint one = new ConditionalConstraint(s1x, storeCopyRemF, MapName.must, refCond, ConstType.pts);
//						callerFc.addConditional(one);
						/*
						 * For the rebuttal, need to count number of strong heap updates performed
						 * So store the constraints and the else constraints for store operation.
						 * Also store the constraint and corresponding else constraint in a map.
						 * During solving, store all the constraints solved for a store operation.
						 * for each such constraint in the list, if its corresponding else constraint is also solved,
						 * then it is not counted.
						 */
						storeCopyRemF.name = ConstraintName.STORE;
						refCond.name = ConstraintName.STORE;
						ConditionalConstraint.conElseCon.put(storeCopyRemF, refCond);
						
						ConditionalConstraint varCond = new ConditionalConstraint(s1x, one, MapName.varPts, null, ConstType.pts);
						callerFc.addConditional(varCond);
						
						}
						
						/*
						 * In case MHP information is present, use it
						 */
//						if(!solver.arg.combined) {
//							BitSet b = solver.getBitSetFor(MapName.MHP, s1);
//							if(b!=null && b.cardinality() > 0) {
//								int i = b.nextSetBit(0);
//								while(i != -1) {
//									Stmt mhpSt = solver.stmtList.get(i);
//									if(solver.methOfRep.containsKey(mhpSt)) {
//										SootMethod memM = solver.methOfRep.get(mhpSt);
//						        		Set<Stmt> memlsSet = solver.loadStores.get(memM);
//						        		if(memlsSet != null) {
//							    			for(Stmt mem : memlsSet) {
//							    				storeToMHPFields(s1, mem);
//							    			}
//						        		}
//									}
//									else {
//										storeToMHPFields(s1, mhpSt);
//									}
//								    i = b.nextSetBit(i+1);
//								}
//								
//							}
//						}
						
						
						
//					}

//		}
			}
		}
	
	 public void genStoreInSens(Stmt s1) {
			/*
			 * Store x.fl = y;
			 * */
//		 if(s1.toString().equals("r0.<org.dacapo.harness.TestHarness: org.dacapo.parser.Config config> = $r18")) {
//				System.out.println("-------------Processing : "+ s1+"---------------");
//			}
			Value vl = ((AssignStmt)s1).getLeftOp();
			Value vr = ((AssignStmt)s1).getRightOp();
			JInstanceFieldRef jfr = (JInstanceFieldRef)vl;
			SootField fl = jfr.getField();
			//gen.methFields.add(fl);
			Value base_x = jfr.getBase(); 
			Local y = (Local)vr;
			if(base_x instanceof Local) {
				
				/*
				 *  The varPts(S1,y) will flow into ifieldPts(r,fl) for r in varPts(S1,x)
				 */
				Object s1x = getKey(s1, (Local)base_x);
				Object s1y = getKey(s1, y);
				AllocNodeField anf = new AllocNodeField(null,fl);
				PropagateConstraint pc3 = new PropagateConstraint(s1y, anf, varMap, MapName.ifieldPts, ConstType.pts);
				ConditionalConstraint storeCopy = new ConditionalConstraint(s1x, pc3, varMap, null, ConstType.pts);
				callerFc.addConditional(storeCopy);
				//genVarPCopy(callerFc.methLocals, s1, succs);
				
			}
		}
	 public boolean isStore(AssignStmt s) {
			boolean store = false;
			Value vl = s.getLeftOp();
			Value vr = s.getRightOp();
			if(vl instanceof JInstanceFieldRef && vr instanceof Local) {
				
				store = true;
			}
			return store;
		}
	 public void genLoad(Stmt s1, Set<Stmt> preds) {
		
		 Value vl = ((AssignStmt)s1).getLeftOp();
			Value vr = ((AssignStmt)s1).getRightOp();
		 JInstanceFieldRef jfr = (JInstanceFieldRef)vr;
			SootField fl = jfr.getField();
			
			Value base_y = jfr.getBase();
			Local x = (Local)vl;
			if(base_y instanceof Local) {
				
				StmtLocal s1y = new StmtLocal(s1, (Local)base_y);
				AllocNodeField anf = new AllocNodeField(null,fl);
				StmtAllocNodeField s1rfl = new StmtAllocNodeField(s1, anf);
				
				
					
					/*
					 * for r in varPts(S1,y), the fieldPts(S1,r,fl) will flow into varPts(S2,x)
					 */
					StmtLocal s2x = new StmtLocal(s1, x);
					PropagateConstraint pc = new PropagateConstraint(s1rfl, s2x, MapName.fieldPts, MapName.varPts, ConstType.pts);
					
					ConditionalConstraint loadCopys2 = new ConditionalConstraint(s1y, pc, MapName.varPts, null, ConstType.pts);
					callerFc.addConditional(loadCopys2);
					MemConstraint addinRefFieldList = new MemConstraint(anf, callerFc.method, false, MapName.refFields, ConstType.pts);
					
					ConditionalConstraint rinVarpts = new ConditionalConstraint(s2x, addinRefFieldList, MapName.varPts, null, ConstType.pts);
					callerFc.addConditional(rinVarpts);
//					MemConstraint addinRefFieldListIn = new MemConstraint(anf, callerFc.method, false, MapName.refFields, ConstType.pts);
//					
//					ConditionalConstraint rinVarptsIn = new ConditionalConstraint(s2x, addinRefFieldListIn, MapName.varPts, null, ConstType.pts);
//					callerFc.addConditional(rinVarptsIn);
				
				
//				}
			}
	 }
	 public void genLoadInSens(Stmt s1, Set<Stmt> preds) {
		 Value vl = ((AssignStmt)s1).getLeftOp();
			Value vr = ((AssignStmt)s1).getRightOp();
		 JInstanceFieldRef jfr = (JInstanceFieldRef)vr;
			SootField fl = jfr.getField();
			
			Value base_y = jfr.getBase();
			Local x = (Local)vl;
			if(base_y instanceof Local) {
				
				Object s1y = getKey(s1, (Local)base_y);
				AllocNodeField anf = new AllocNodeField(null,fl);
				
					
					/*
					 * for r in varPts(S1,y), the fieldPts(S1,r,fl) will flow into varPts(S2,x)
					 */
					Object s2x = getKey(s1, x);
					PropagateConstraint pc = new PropagateConstraint(anf, s2x, MapName.ifieldPts, varMap, ConstType.pts);
					ConditionalConstraint loadCopy = new ConditionalConstraint(s1y, pc, varMap, null, ConstType.pts);
					callerFc.addConditional(loadCopy);
				
//				}
			}
	 }
	 
	 public void genVarPCopy(Stmt s1) {
	/*
	 * For each used local in the statement s1, copy the varPts from the reaching def statements
	 * to s1.
	 */
//		 if(s1.toString().equals("$r22 = (org.dacapo.harness.Benchmark) r27")) {
//			 System.out.println("caught");
//		 }
		 Set<Local> uses = gen.uses.get(s1);
		 if(uses!=null) {
			 for(Local l : uses) {
				 Map<Local,Set<Stmt>> reachingDefs = gen.reachDefMap.get(s1);
				 if(reachingDefs==null) {
					 System.out.println("null");
				 }
				 if(reachingDefs.containsKey(l)) {
					 Set<Stmt> stSet = reachingDefs.get(l);
					 for(Stmt st: stSet) {
						 StmtLocal left = new StmtLocal(st, l);
						 StmtLocal right = new StmtLocal(s1, l);
						 PropagateConstraint varPCopy = new PropagateConstraint(left, right, MapName.varPts, MapName.varPts, ConstType.pts);
						 callerFc.addPropagate(varPCopy);
						 
					 }
				 }
			 }
		 }
			

		}

	@Override
	public void countPtsInfo() {
		getPointToCount();
	}
	public void findPtDiff(Solver poaSolver, Solver ipoaSolver ) {
		Set<SootMethod> localcountdiff = new HashSet<>();
		Set<SootMethod> poaMore = new HashSet<>();
		for(SootMethod m:solver.methLocals.keySet()) {
			int pltotal = poaSolver.methLocals.get(m).size();
			Set<Local> pl = poaSolver.methLocals.get(m);
			int pC = 0;
			int ipC = 0;
			if(!ipoaSolver.methLocals.containsKey(m)) {
				poaMore.add(m);
				continue;
			}
			int ipltotal = ipoaSolver.methLocals.get(m).size();
			
			Set<Local> ipl = ipoaSolver.methLocals.get(m);
			BitSet b = new BitSet();
			if(poaSolver.methRet.containsKey(m)) {
			BitSet retStmts = poaSolver.methRet.get(m);
			
			for(Local l: pl) {
				if(SimplifyUtil.isInterestingType(l.getType()) && !SimplifyUtil.isLibType(l.getType())) {
					b.clear();
					int length = 0;
					int i = retStmts.nextSetBit(0);
					while(i != -1) {
						Stmt rs = poaSolver.stmtList.get(i);
	//					
						BitSet br = poaSolver.getVarPts(l, rs);
	//					
						/*
						 * some locals may reach only a particular return
						 * so the null check
						 */
						if(br!=null) {
							b.or(br);
						}
	
						
						i = retStmts.nextSetBit(i+1);
					}
					if(b!=null) {
						length = b.cardinality();
						if(b.get(0)) {
							length = 0;
						}
					}
				}
			}
		}
		for(Local l: ipl) {
			int length = 0;
			if(SimplifyUtil.isInterestingType(l.getType()) && !SimplifyUtil.isLibType(l.getType())) {
			b = ipoaSolver.ivarPts.get(l);
			if(b!=null) {
				length = b.cardinality();
				if(b.get(0)) {
					length=0;
				}
				
				ipC+=length;

			}
			else {
				Type t = l.getType();
				if(t instanceof ArrayType) {
					t = ((ArrayType)t).baseType;
				}
		
			}
		}
		}
		if(pC > ipC) {
			poaMore.add(m);
		}
		if(pltotal != ipltotal) {
			localcountdiff.add(m);
		}
		}
		System.out.println("Poa more meths:"+poaMore.size()+" local count diff:"+localcountdiff.size());
	}
	private void getPointToCount() {
		Solver solver = Solver.v();
		System.out.println("Started points-to count");
//		File f = new File(solver.path+"/tmp/ptCount"+solver.aString+".txt");
//		FileWriter fileWriter;
//		try {
//			fileWriter = new FileWriter(f);
//		
//    	BufferedWriter brd = new BufferedWriter(fileWriter);
//		PrintWriter printWriter = new PrintWriter(brd);
		BitSet b = new BitSet();
		System.out.println("Total meths: "+solver.methLocals.entrySet().size());
		for(Map.Entry<SootMethod,Set<Local>> ele : solver.methLocals.entrySet()) {
			
			int methCount =0;
			SootMethod m = ele.getKey();
			boolean print = false;
//			if(m.getSignature().equals("<org.sunflow.RenderObjectMap$RenderObjectHandle: org.sunflow.core.Geometry access$400(org.sunflow.RenderObjectMap$RenderObjectHandle)>")) {
//				print = true;
//			}
			Set<Local> lSet = ele.getValue();
			/*
			 * get the points-to count of variables
			 */
			if(varMap==MapName.varPts) {
				BitSet retStmts = solver.methRet.get(m);
				if(retStmts != null) {
					for(Local l: lSet) {
						if(SimplifyUtil.isInterestingType(l.getType()) && !SimplifyUtil.isLibType(l.getType())) {
						b.clear();
						int length = 0;
						int i = retStmts.nextSetBit(0);
						int tot = 0;
						int size = retStmts.cardinality();
						while(i != -1) {
							Stmt rs = solver.stmtList.get(i);
//							StmtLocal sl = new StmtLocal(rs, l);
//							BitSet br = solver.varPts.get(sl);
							BitSet br = solver.getVarPts(l, rs);
//							BitSet bri = InterestingFieldPass.solver.getVarPts(l, rs);
							/*
							 * some locals may reach only a particular return
							 * so the null check
							 */
//							if(br!=null) {
//								b.or(br);
//							}
//							else {
//								Type t = l.getType();
//										if(t instanceof ArrayType) {
//											t = ((ArrayType)t).baseType;
//										}
//								RefType r = (RefType)t;
//								if(!r.getSootClass().isLibraryClass()) {
//								System.out.println("null points-to set in meth "+m.getSignature()+" ignored="+solver.ignoredMeths.contains(m)+" type of local"+r.getClassName());
//								solver.getVarPts(l, rs);
//								}
//							}
							if(br!=null)
							tot += br.cardinality();
							i = retStmts.nextSetBit(i+1);
						}
						if(b!=null) {
						length = tot/size;
//						if(b.get(0)) {
//							length = 0;
//						}
						methCount+=length;
						
						solver.pointCount+=length;
						}
					}
					}
//					printWriter.println(m.getSignature()+": "+methCount);
				}
			}
			else {
				for(Local l: lSet) {
					int length = 0;
					if(SimplifyUtil.isInterestingType(l.getType()) && !SimplifyUtil.isLibType(l.getType())) {
					b = solver.ivarPts.get(l);
					if(b!=null) {
						length = b.cardinality();
//						if(b.get(0)) {
//							length=0;
//						}
						
						solver.pointCount+=length;
//						if(print)
//							System.out.println(l.getName()+":"+length);
						methCount+=length;
					}
					else {
						Type t = l.getType();
						if(t instanceof ArrayType) {
							t = ((ArrayType)t).baseType;
						}
				RefType r = (RefType)t;
				if(!r.getSootClass().isLibraryClass() && r.getSootClass().isJavaLibraryClass()) 
						System.out.println("null points-to set in meth "+m.getSignature()+" ignored="+solver.ignoredMeths.contains(m)+" type of local"+r.getClassName());
					}
				}
				}
//				printWriter.println(m.getSignature()+": "+methCount);
			}
			
			}
		/*
		 * get the points-to count of fields
		 */
//		if(fieldMap==MapName.ifieldPts) {
//			for(Map.Entry<AllocNodeField, BitSet> ele : solver.ifieldPts.entrySet()) {
//					BitSet bt = ele.getValue();
//					if(bt!=null) {
//						int length = bt.cardinality();
//
//						solver.pointCount+=length;
//					}
//					
//				}
//			}
//		else {
//			BitSet retStmts = solver.methRet.get(solver.main);
//			Set<Stmt> rets = new HashSet<>();
//			int i = retStmts.nextSetBit(0);
//			
//			while(i != -1) {
//				Stmt rs = solver.stmtList.get(i);
//				rets.add(rs);
//				i = retStmts.nextSetBit(i+1);
//			}
//			for(AllocNodeField anf : solver.fieldList) {
//				b.clear();
//				for(Stmt s : rets) {
//					StmtAllocNodeField sanf = new StmtAllocNodeField(s,anf);
//					BitSet b1 = solver.fieldPts.get(sanf);
//					if(b1!=null)
//					b.or(b1);
//				}
//				if(b!=null) {
//					int length = b.cardinality();
//					if(b.get(0)) {
//						length--;
//					}
//					solver.pointCount+=length;
//				}
//			}
//		}
//		printWriter.close();
//		brd.close();
//		fileWriter.close();
//		} catch (IOException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
		
		System.out.println("Points to count:"+solver.pointCount);
	}
	@Override
	public void countCallEdges() {

		solver.callEdgeCount= 0;
		
//		for(Stmt st: callSites) {
//			InvokeExpr ie = st.getInvokeExpr();
//			if(ie instanceof VirtualInvokeExpr || ie instanceof InterfaceInvokeExpr) {
//				Local l = (Local)((InstanceInvokeExpr)ie).getBase();
//				BitSet bl = null;
//				if(solver.arg.fs) {
//					bl = solver.getVarPts(l, st);
//					
//				}
//				else {
//					bl = solver.ivarPts.get(l);
//				}
//				if(bl != null) {
//					solver.callEdgeCount+=bl.cardinality();
//					
//				}
//			}
//			
//		}
//		Map<SootMethod,Set<SootMethod>> myCG = new HashMap<>(); 
//		for(Map.Entry<Stmt, BitSet> e : solver.callSiteMeths.entrySet()) {
//    		Stmt st = e.getKey();
//    		SootMethod caller = solver.myS.get(st);
////    		System.out.println("++++++"+st+" from "+myS.get(st).getSignature());
//    		BitSet bs = e.getValue();
//    		int i = bs.nextSetBit(0);
//    		while( i!=-1 ) {
//    			SootMethod callee = solver.methList.get(i);
//    			if(!myCG.containsKey(caller)) {
//    				myCG.put(caller, new HashSet<>());
//    			}
//    			myCG.get(caller).add(callee);
//    			i = bs.nextSetBit(i+1);
//    		}
//		}
//		for(Map.Entry<SootMethod,Set<SootMethod>> e:myCG.entrySet()) {
//			solver.callEdgeCount+=e.getValue().size();
//		}
		Map<SootMethod,Map<Stmt,Set<SootMethod>>> mycallSiteCG = new HashMap<>(); 
		for(Map.Entry<Stmt, BitSet> e : solver.callSiteMeths.entrySet()) {
    		Stmt st = e.getKey();
    		SootMethod caller = solver.myS.get(st);
//    		System.out.println("++++++"+st+" from "+myS.get(st).getSignature());
    		BitSet bs = e.getValue();
    		int i = bs.nextSetBit(0);
    		while( i!=-1 ) {
    			SootMethod callee = solver.methList.get(i);
    			if(!mycallSiteCG.containsKey(caller)) {
    				mycallSiteCG.put(caller, new HashMap<>());
    			}
    			if(!mycallSiteCG.get(caller).containsKey(st)) {
    				mycallSiteCG.get(caller).put(st, new HashSet<>());
    			}
    			mycallSiteCG.get(caller).get(st).add(callee);
    			i = bs.nextSetBit(i+1);
    		}
		}
		for(Map.Entry<SootMethod,Map<Stmt,Set<SootMethod>>> e:mycallSiteCG.entrySet()) {
			Map<Stmt,Set<SootMethod>> mp = e.getValue();
			for(Map.Entry<Stmt,Set<SootMethod>> ele: mp.entrySet())
				solver.callEdgeCount+=ele.getValue().size();
		}
		
	
//		int cg = 0;
//		for(Map.Entry<SootMethod, Set<SootMethod>> ele: myCG.entrySet()) {
//			cg+=ele.getValue().size();
//		}
//		solver.callEdgeCount = cg;
		System.out.println("call edges of"+solver.aString+" : "+solver.callEdgeCount);
	}
	@Override
	public void countMonomorphic() {
//		countCallEdges();
//		countByCallSites(callSites);
//		if(solver.arg.combined) {
//			countMonomorphiciPoA();
//			countMonomorphicPoA();
//		}
//		countByMethsAtCallSite(solver);
//		if(solver.arg.combined) {
//			countMonomorphiciPoA();
//			countMonomorphicPoA();
//		}
		
//		int bottoms = 0;
//		int virtualSites = 0;
//		solver.callEdgeCount = 0;
//		for(Map.Entry<Stmt, BitSet> ele: solver.callSiteMeths.entrySet()) {
//			InvokeExpr ie = ele.getKey().getInvokeExpr();
//			
//				BitSet b = ele.getValue();
//				int calledMeths = b.cardinality();
//				//solver.callEdgeCount+=calledMeths;
//				if(ie instanceof VirtualInvokeExpr || ie instanceof InterfaceInvokeExpr) {
//					virtualSites++;
//				if(calledMeths==1)
//					solver.monomorphicCount++;
//				}
//		}
//		Map<SootMethod,Set<SootMethod>> cg = MyCG.callGraph;
//    	
//    	
//    	for(Map.Entry<SootMethod,Set<SootMethod>> ele: cg.entrySet()) {
//    		solver.callEdgeCount+=ele.getValue().size();
//    			
//    	}
////		double callSites = solver.callSiteMeths.entrySet().size();
//		solver.monoPercent = (solver.monomorphicCount / solver.callEdgeCount )*100;
//    	System.out.println("call edges:"+solver.callEdgeCount+" monomorphic"+solver.monoPercent+"bottoms:"+bottoms);
		
	}
	
	private void countByMethsAtCallSite(Solver sol) {
		Map<Stmt, BitSet> callSiteMeths = this.solver.callSiteMeths;
		sol.callEdgeCount= 0;
		sol.monomorphicCount = 0;
		for(Stmt st: callSiteMeths.keySet()) {
			
			BitSet b = sol.callSiteMeths.get(st);
			InvokeExpr ie = st.getInvokeExpr();
			if(b != null) {
				sol.callEdgeCount+=b.cardinality();
				if(ie instanceof VirtualInvokeExpr || ie instanceof InterfaceInvokeExpr) {
					
					
						
						if(b.cardinality()==1 /*&& !b.get(0)*/) {
							sol.monomorphicCount++;
						}
				}
			}
			
		}
		sol.monoPercent = (sol.monomorphicCount/sol.callEdgeCount)*100 ;
		System.out.println("call edges of"+sol.aString+" : "+sol.callEdgeCount+" monomorphic"+sol.monomorphicCount+"mono percent"+sol.monoPercent);
		
	}
	
	

	private void recordLoadStoreStmts(SootMethod m,Stmt s) {
		if(!solver.loadStores.containsKey(m)) {
			solver.loadStores.put(m, new HashSet<>());
		}
//		if(m==null || s ==null) {
//			System.out.println("stop");
//		}
		solver.loadStores.get(m).add(s);
		
	}
	
	@Override
	public MapName getVarMap() {
		return varMap;
	}
	@Override
	public MapName getFieldMap() {
		return fieldMap;
	}
	
	
}
