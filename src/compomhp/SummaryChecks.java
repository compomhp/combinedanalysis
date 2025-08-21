package compomhp;

import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javafx.util.Pair;
import soot.Body;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.Stmt;
import soot.jimple.toolkits.annotation.logic.Loop;
import soot.jimple.toolkits.annotation.logic.LoopFinder;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.DominatorsFinder;
import soot.toolkits.graph.LoopNestTree;
import soot.toolkits.graph.MHGDominatorsFinder;
import soot.toolkits.graph.UnitGraph;

public class SummaryChecks {
    Set<Stmt> allocsInLoop = new HashSet<>();
    Set<Stmt> summaryStmtsFromHA = new HashSet<>();
    Set<Stmt> nonSummaryStmtsFromHA = new HashSet<>();
    
    public boolean isSummaryStNew(Stmt s, boolean isAllocSite, Stmt st) {
    	boolean isSumry= false;
    	
    /*	
     * isSummarySt(s) checks if a statement s may be executed multiple times.
     * if isSummarySt(s) is true,
   	 * - In case, s is an allocation site, even if s is a summary statement, we can assume non-summary node at
   	 * a statement st, if s dominates st, because it will receive the recent version of allocated object instead of
   	 * summary version
   	 * Recency abstraction:
	 * Even if an allocsite is executed multiple times, some statements in the same method as allocsite
	 * which are dominated by the allocsite receive only the recent copy of the object and need not be a
	 * summary object for those statements
   	 */ 
    	isSumry = isSummarySt(s, isAllocSite);
    	Solver HASolver = HelperAnalysis.solver;
    	if(isSumry && isAllocSite) {
    		SootMethod sm = HASolver.myS.get(s);
    		
    		SootMethod smSt = HASolver.myS.get(st);
    		boolean sumryAtSt = true;
    			
    			Stmt allocMulti = s;
    			SootMethod m = sm;
    			
    			while(m != null) {
    				if(isInLoop(m,allocMulti))
    					break;
    				else {
    					Set<Stmt> callSites = HASolver.callerStmts.get(m);
    					if(callSites==null || callSites.isEmpty()) {
    						break;
    					}
    					if(callSites.size()>1) {
    						return true;
    					}
    					else {
    						allocMulti = callSites.iterator().next();
    						m = HASolver.myS.get(allocMulti);
    					}
    				}
    			}
    			Set<Stmt> stmtsOfInterest = new HashSet<>();
    			if(m==smSt) {
    				stmtsOfInterest.add(st);
    			}else {
    				
    		    	BitSet mReach = HASolver.reachableFuncs.get(m);
    		    	int smStBit = HASolver.methList.indexOf(smSt);
    		    	
    		    	if(mReach.get(smStBit)) {
    					/*
    					 * check if smSt is reachable without m. If so, 
    					 * summary = true
    					 */
    					Map<SootMethod,Set<SootMethod>> cgCopy = new HashMap<>(MyCG.callGraphHA);
    					cgCopy.remove(m);
    					if(m != smSt && isReachable(HASolver.main, smSt, cgCopy)) {
    						return true;
    					}
    					else {
    						Set<Pair<SootMethod,SootMethod>> directCallees = MyCG.HAedgesOutof.get(m);
    						for(Pair<SootMethod,SootMethod> p: directCallees) {
    							SootMethod mc = p.getValue();
    							BitSet bm = HASolver.reachableFuncs.get(mc);
//    							if(bm==null) {
//    								System.out.println("null");
//    							}
    							if(bm!=null && bm.get(smStBit)) {
    								/*
    								 * since smSt is reachable get the callsite
    								 * of m in sm
    								 */
    								Set<Stmt> cst = HASolver.callerStmts.get(mc);
    								for(Stmt cs: cst) {
    									SootMethod cm = HASolver.myS.get(cs);
    									if(cm==m) {
    										stmtsOfInterest.add(cs);
    									}
    								}
    							}
    							
    						}
    						
    					}
    				}
    			}
    			
    			if(!stmtsOfInterest.isEmpty()) {
    				boolean allStmtsDom = true;
	    				for(Stmt cs:stmtsOfInterest) {
//	    					try {
	    					 if (!isSameLoopAndDominance(cs, allocMulti, m)) {
	    						 allStmtsDom = false;
	    	    		        	break;
	    	    		        }
//	    					}catch(Exception e){
//	    						System.out.println("error");
//	    					}
	    				}
	    				if(allStmtsDom)
	    					sumryAtSt = false;
					}
    			isSumry = sumryAtSt;    	
    	}
    	return isSumry;
    }
   
    public boolean isReachable(SootMethod main, SootMethod target, Map<SootMethod,Set<SootMethod>> cg) {
        Set<SootMethod> visited = new HashSet<>();
        return dfs(main, target, visited, cg);
    }

    private boolean dfs(SootMethod current, SootMethod target, Set<SootMethod> visited, Map<SootMethod,Set<SootMethod>> cg) {
        // Base case: if current node is the target, return true
        if (current == target) {
            return true;
        }
        // Mark current node as visited
        visited.add(current);
        // Explore neighbors
        Set<SootMethod> adj = cg.get(current);
        if(adj != null) {
        for (SootMethod neighbor : adj) {
            if (!visited.contains(neighbor)) {
                if (dfs(neighbor, target, visited, cg)) {
                    return true;
                }
            }
        }
        }
        return false;
    }
    private boolean isSameLoopAndDominance(Stmt st, Stmt s, SootMethod m) {
    	boolean isDom = false;
    	Body body = Solver.getBody(m);
		UnitGraph cfg = new BriefUnitGraph(body);
		LoopFinder loopFinder = new LoopFinder();
        loopFinder.transform(body);
        LoopNestTree loopNestTree = new LoopNestTree(body);
        Loop imLoop = findImmediatelyEnclosingLoop(s,loopNestTree);
       
        /*
         * if st is present in the immediately enclosing loop of s (allocsite),
         * check if st is dominated by s
         */
        if(imLoop != null) {
        	 List<Stmt> imLoopStmts = imLoop.getLoopStatements();
	        if(imLoopStmts.contains(st)) {
	        	
	        	 // Create a DominatorFinder for the CFG
	        	DominatorsFinder<Unit> dominatorFinder = new MHGDominatorsFinder<>(cfg);
	        	
	        	/*
	        	 * True if "arg1" is dominated by "arg2" in the graph.
	      	   	 */
	        	if(dominatorFinder.isDominatedBy(st, s)) {
	        		isDom = true;
	        	}
	        }
        }else {
        	 // Create a DominatorFinder for the CFG
        	DominatorsFinder<Unit> dominatorFinder = new MHGDominatorsFinder<>(cfg);
        	
        	/*
        	 * True if "arg1" is dominated by "arg2" in the graph.
      	   	 */
        	if(dominatorFinder.isDominatedBy(st, s)) {
        		isDom = true;
        	}
        }

       
       
    	return isDom;
    }
    private Loop findImmediatelyEnclosingLoop(Unit targetStmt, LoopNestTree loopNestTree) {
        Loop immediateLoop = null;
        int minLoopSize = Integer.MAX_VALUE;

        // Iterate through all loops in the LoopNestTree
        for (Loop loop : loopNestTree) {
            // Check if the target statement is in this loop
            if (loop.getLoopStatements().contains(targetStmt)) {
                // Get the number of statements in the loop to determine the innermost loop
                int loopSize = loop.getLoopStatements().size();
                if (loopSize < minLoopSize) {
                    minLoopSize = loopSize;
                    immediateLoop = loop;
                }
            }
        }

        return immediateLoop;
    }
    public boolean isSummarySt(Stmt s, boolean isAllocSite) {
    	/*
    	 * Given the call graph of the program (here, we use call graph from HA) and CFG of each method.
    	 *  A statement s in a method m can be statically checked for 
    	 * the possibility of getting executed multiple times at run time in the following way:
    	 * s can be declared as multi-run,i.e; isSummarySt(s) is true if
    	 * - s is inside a loop in m
    	 * - m can be executed multiple times. To find it out, check if
    	 *   - m is called from multiple call sites or
    	 *   - m is called from a single call site c, but the c is multi-run. So, if isSummarySt(c) is true.
    	 * 
    	 */
    	if(summaryStmtsFromHA.contains(s)) {
    		return true;
    	}
    	else if(nonSummaryStmtsFromHA.contains(s)) {
    		return false;
    	}
    	Solver HASolver = HelperAnalysis.solver;
    	SootMethod sm = HASolver.myS.get(s);
    	
    	boolean isSumry = false;
    	if(isInLoop(sm,s)) {
    		if(isAllocSite)
    			allocsInLoop.add(s);
    		summaryStmtsFromHA.add(s);
    		return true;
    	}
        		
    		Set<Pair<SootMethod,SootMethod>> callers = MyCG.HAedgesInto.get(sm);
    		if(callers==null) {
    			nonSummaryStmtsFromHA.add(s);
    			return false;
    		}
    		else if(callers.size() > 1) {
    			/*
    			 * callers are more than 1
    			 */
    			summaryStmtsFromHA.add(s);
    			return true;
    		}
    		else if(callers.size() == 1){
    			/*
    			 * if there is only one caller, check if the caller has only one caller
    			 * and the call-site is not inside loop
    			 * 
    			 */
    			Set<Stmt> callSites = MyCG.callerStmtsHA.get(sm);
    			if(callSites.size()>1) {
    				summaryStmtsFromHA.add(s);
    				return true;
    			}
    			else {
    				Stmt cs = callSites.iterator().next();
    				return isSummarySt(cs, false);
    			}
    			
    		}
			
    	if(isSumry) {
    		summaryStmtsFromHA.add(s);
    	}
    	else {
    		nonSummaryStmtsFromHA.add(s);
    	}
    	
    	return isSumry;
    }
    public boolean isInLoop(SootMethod sm, Stmt s) {
    	boolean inLoop = false;
    	
    	if(sm!=null) {
	    	Body b = sm.getActiveBody();
	    	if(b!=null) {
	    		LoopNestTree loopNestTree = new LoopNestTree(b);
				for(Loop loop : loopNestTree) {
					List<Stmt> stL = loop.getLoopStatements();
					if(stL.contains(s)) {
						inLoop = true;
						break;
					}
				}
	    	}
    	}
    	return inLoop;
    }
}
