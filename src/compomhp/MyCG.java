package compomhp;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import javafx.util.Pair;
import soot.SootMethod;
import soot.jimple.Stmt;

public class MyCG {
	static Map<SootMethod,Set<Pair<SootMethod,SootMethod>>> HAedgesOutof = new HashMap<>();
    static Map<SootMethod,Set<Pair<SootMethod,SootMethod>>> HAedgesInto = new HashMap<>();
    static Set<Pair<SootMethod,SootMethod>> edgesHA = new HashSet<>();
    static Map<SootMethod,Set<Stmt>> callerStmtsHA;
    static Map<SootMethod,Set<SootMethod>> callGraph = new HashMap<>();
    static Map<SootMethod,Set<SootMethod>> inverseCallGraph = new HashMap<>();
    static void addEdge(SootMethod src, SootMethod dest) {
    	Pair<SootMethod,SootMethod> e = new Pair<SootMethod,SootMethod>(src,dest);
    	//Pair<SootMethod,SootMethod> from = new Pair<SootMethod,SootMethod>(dest,src);
    	edgesHA.add(e);
    	if(!HAedgesOutof.containsKey(src)) {
    		HAedgesOutof.put(src, new HashSet<>());
    	}
    	if(!HAedgesInto.containsKey(dest)) {
    		HAedgesInto.put(dest, new HashSet<>());
    	}
    	
    	HAedgesOutof.get(src).add(e);
    	HAedgesInto.get(dest).add(e);
    	
    }
    static void addToCallGraph(SootMethod src, SootMethod dest) {
    	if(!callGraph.containsKey(src)) {
    		callGraph.put(src, new HashSet<>());
    	}
    	callGraph.get(src).add(dest);
    	if(!inverseCallGraph.containsKey(dest)) {
    		inverseCallGraph.put(dest, new HashSet<>());
    	}
    	inverseCallGraph.get(dest).add(src);
    }
}
