package compomhp;

import java.nio.file.FileSystems;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import soot.Local;
import soot.Scene;
import soot.SootMethod;
import soot.Value;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.Stmt;
import soot.jimple.internal.JNopStmt;



public class SolverUtil {
	Solver solver;
	MemConstraint addBotF, addBotA;
	
	static String path = FileSystems.getDefault()
	        .getPath("")
	        .toAbsolutePath()
	        .toString();
	public static void initSolverInstance(Solver sl, Arg arg) {
		sl.path = path;
		sl.arg = arg;
		FunctionalConstraint fc = new FunctionalConstraint(ConstType.pts);
		SootMethod mainMethod = Scene.v().getMainMethod();
		fc.method = mainMethod;
		sl.workList.add(fc);
		sl.main = mainMethod;
		sl.callerStmts.put(mainMethod,new HashSet<>());
		sl.callerStmts.get(mainMethod).add(new JNopStmt());
		sl.sUtil.solver = sl;
		SimplifyUtil.solver = sl;
	}
	
	public void propInverseMaps(Node n, int bitPos) {
//		Stmt keySt = (Stmt)n.key;
//		if(solver.methOfRep.containsKey(keySt)) {
//			
//		}
		int stPos = solver.stmtList.indexOf(n.key);
		Stmt memSt = solver.stmtList.get(bitPos);
			
			BitSet b = solver.getBitSetFor(MapName.MHP, memSt);
			
			if(b==null || !b.get(stPos)) {
				Node n1 = new Node(MapName.MHP, memSt);
				if(solver.Edges.containsKey(n1) || solver.depCN.containsKey(n1)) {
					MemConstraint mc = new MemConstraint(n.key, memSt, false, MapName.MHP, ConstType.mhp);
					mc.addToList();
				}
				else {
					b.set(stPos);
				}
				if(solver.arg.combined)
					solver.propagateToMHPFields(n,memSt);
				
			}
	}
	 public void propagateIter(PropagateTask t) {
	    	
	    	Queue<PropagateTask> pQueue = new LinkedList<PropagateTask>();
	    	pQueue.add(t);
	    	while(!pQueue.isEmpty()) {
	    		PropagateTask pt = pQueue.poll();
	    		
	    		BitSet bv = null;
//	    		if(pt.sn.mapName==MapName.varPts) {
//	    			System.out.println("varpts");
//	    		}
	    		bv = (BitSet) solver.mapForName.get(pt.sn.mapName).get(pt.sn.key);
	    		if(bv==null) {
	        		bv = solver.insertIntoMap(pt.sn.mapName,pt.sn.key);
	        	}
	    		
	    		if( !bv.get(pt.bitPos)) {

	    			/*
	    			 * For points-to information set the bit, only if the type is compatible with type of Local or field
	    			 */
	    				
	    				
	    				boolean isCompatible = solver.isCompatible(pt.sn,pt.bitPos);

	    				
	    				if(/*!solver.arg.combined && solver.arg.bot &&*/ !isCompatible) {
//	    					if(solver.mapBitSetType.get(pt.sn.mapName)==1) {
//	    						if(bv.get(0)) {
//	    							return;
//	    						}
//	    						else
//	    							pt.bitPos = 0;
//	    					}
//	    					else
	    					return;
	    				}
	    					bv.set( pt.bitPos);
//	    					solver.setBit(pt.sn.mapName, bv, pt.bitPos, pt.sn.key);
	    				
	    				if(solver.arg.esc && pt.sn.mapName == MapName.escapeAt)
	    					solver.propEsctoReachables(pt.sn, pt.bitPos);
	    				if(solver.arg.esc && pt.sn.mapName == MapName.sfieldPts)
	    					solver.addStaticFieldToEscape(pt.sn, pt.bitPos);
	    				if(pt.sn.mapName==MapName.MHP /*|| pt.sn.mapName==MapName.funcsAtCallSite*/) {
	    					
	    					propInverseMaps(pt.sn, pt.bitPos);
	    				}
	    				
	    				if(solver.arg.iterative) {
	    					solver.iterChanges++;
	    				}
	    				
	    				solver.solveDeps(pt.sn, pt.bitPos, bv, /*isBot*/false);
	    				
//	    				ArrayList<Node> edges = solver.getEdges(pt.sn, pt.bitPos);
	    				ArrayList<Node> edges = solver.Edges.get(pt.sn);
	    				if(edges != null /*&& !isBot*/) {
//	    					ArrayList<Node> edgeCopy = new ArrayList<>(edges);
	    					for(Node succ : edges) {
//	    						boolean propagate = true;
//	    						if(succ.diffSource) {
//	    							BitSet rbs = solver.getBitSetFor(succ.rightDiffMap,succ.rightDiffVar);
//	    							if(rbs.get(pt.bitPos)) {
//	    								propagate = false;
//	    							}
//	    						}
//	    						if(propagate) {
	    							BitSet b = solver.getBitSetFor(succ.mapName, succ.key);
	    							if(b==null || !b.get(pt.bitPos)) {
	    								
	    								PropagateTask pt1 = new PropagateTask(succ, pt.bitPos);
	    								if(!pQueue.contains(pt1))
	    									pQueue.add(pt1);
	    							}
//	    						}
	    					}
	    					
	    				}
	    				
	    				
	    			 }
	    	}
		}
	 public boolean isBot(MapName mapName, int bitPos) {
		 if(!solver.arg.bot)
			 return false;
		 boolean isBot =false;
		 if(solver.mapBitSetType.get(mapName)==1) {
 			if(solver.arg.bot && bitPos == 0) {
 				isBot = true;
 			}
 		}
		 return isBot;
	 }
	 public void propElemIter(Node sn, int bitPos) {
		 PropagateTask pt = new PropagateTask(sn,bitPos);
		 propagateIter(pt);
	 }
	 public void addBotToParamReachAndReturn(FunctionalConstraint callerFc) {
		List<Value> la = callerFc.invokeExpr.getArgs();
		Local rcvr = callerFc.rcvr;
		MapName varMap = solver.analyzer.ptConsGen.varMap;
		
		/*
		 * Check if the method has some interesting return type or parameters
		 */
		boolean addBot = false;
		if(SimplifyUtil.isInterestingType(callerFc.method.getReturnType())) {
			addBot = true;
		}
		if(!addBot) {
			Iterator<Value> itr = la.iterator();  
			while(itr.hasNext()) {
				Value vl = itr.next();
				if(vl instanceof Local && SimplifyUtil.isInterestingType(vl.getType())) {
					addBot = true;
					break;
				}
		}
		}
		if(addBot) {
			/*
			 * If the call is of type x = lib(), add bottom to varPts(x)
			 */
			solver.natNotNull.add(callerFc.method);
			if(callerFc.retLocal != null && SimplifyUtil.isInterestingType(callerFc.retLocal.getType())) {
				Object sl = solver.analyzer.ptConsGen.getKey(callerFc.callSite, (Local)callerFc.retLocal) ;
				MemConstraint addBotRet = new MemConstraint(solver.bottom, sl, false, varMap, ConstType.pts);
				addBotRet.addToList();
//				callerFc.addMember(addBotRet);
			}
			
				/*
				 * add Bot in reachable heap of receiver
				 */
				
				if(rcvr != null && SimplifyUtil.isInterestingType(rcvr.getType())) {
					if(SimplifyUtil.isInterestingType(rcvr.getType())) {
						Object base = solver.analyzer.ptConsGen.getKey(callerFc.callSite, rcvr);
						propBotToReachableFields(base, callerFc.callSite);
					}
				}
				Iterator<Value> itr = la.iterator();  
				while(itr.hasNext()) {
					Value vl = itr.next();
					if(vl instanceof Local && SimplifyUtil.isInterestingType(vl.getType())) {
						Object base = solver.analyzer.ptConsGen.getKey(callerFc.callSite, (Local)vl);
						propBotToReachableFields(base, callerFc.callSite);
					}
				}
	 }
//		else {
//			System.out.println("debug ignored");
//		}
	 }
	 public void propBotToReachableFields(Object base, Stmt at) {
		 GenCons ptConsGen = solver.analyzer.ptConsGen;
		 MapName fieldMap = ptConsGen.fieldMap;
		 MapName varMap = ptConsGen.varMap;
//		 Object lsa = ptConsGen.getKey(at, base);
			ConditionalConstraint ccf, cca;
			if(fieldMap== MapName.fieldPts) {
				MemConstraint addB = new MemConstraint(addBotF);
				addB.X = at;
				ccf = new ConditionalConstraint(base, addB, varMap, null, ConstType.pts);
				cca = new ConditionalConstraint(base, addBotA, varMap, null, ConstType.pts);
			}
			else {
				ConditionalConstraint c1 = new ConditionalConstraint(null, addBotF, MapName.fieldsOf, null, ConstType.pts);
				addBotF.name = ConstraintName.SYNC_END;
				ccf = new ConditionalConstraint(base, c1, varMap, null, ConstType.pts);
				/*
				 * Array has only one field, so no need to fieldsOf
				 */
				cca = new ConditionalConstraint(base, addBotA, varMap, null, ConstType.pts);
			}
				
			ccf.addToList();
			cca.addToList();
	 }
	 
//	 public void propBotToReachableFields(Object base, Stmt at) {
//		 GenCons ptConsGen = solver.analyzer.ptConsGen;
//		 MapName fieldMap = ptConsGen.fieldMap;
//		 MapName varMap = ptConsGen.varMap;
////		 Object lsa = ptConsGen.getKey(at, base);
//			ConditionalConstraint ccf, cca;
////			if(fieldMap== MapName.fieldPts) {
////				MemConstraint addB = new MemConstraint(addBotF);
////				addB.X = at;
////				ccf = new ConditionalConstraint(base, addB, varMap, null, ConstType.pts);
////				cca = new ConditionalConstraint(base, addBotA, varMap, null, ConstType.pts);
////			}
////			else {
//			
//			Constraint cB=null;
//			if(fieldMap== MapName.fieldPts) {
//				if(at!=null) {
//				MemConstraint addB = new MemConstraint(addBotF);
//				addB.X = at;
//				SootMethod m = solver.myS.get(at);
//				if(m!=null) {
//				ConditionalConstraint cc = new ConditionalConstraint(m, addB, MapName.methFields, null, ConstType.pts);
//				cB = cc;
//				}
//				}
//			}
//			else {
//				cB = addBotF;
//			}
//			if(cB!=null) {
//				ConditionalConstraint c1 = new ConditionalConstraint(null, cB, MapName.fieldsOf, null, ConstType.pts);
//				addBotF.name = ConstraintName.SYNC_END;
//				ccf = new ConditionalConstraint(base, c1, varMap, null, ConstType.pts);
//				ccf.addToList();
//			}
//				/*
//				 * Array has only one field, so no need to fieldsOf
//				 */
//				cca = new ConditionalConstraint(base, addBotA, varMap, null, ConstType.pts);
////			}
//				
//			
//			cca.addToList();
//	 }
	
	   
}
