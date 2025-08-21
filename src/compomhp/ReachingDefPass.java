package compomhp;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import soot.Local;
import soot.jimple.Stmt;

public class ReachingDefPass {
 static Map<Stmt,Map<Local,Set<Stmt>>> findDefs( Generator g) {
	 /*
	  * Find which definitions of variables reach which statements
	  */
	 Map<Stmt,Map<Local,Set<Stmt>>> reachDefMap = new HashMap<>();
	 Map<Stmt,Map<Local,Set<Stmt>>> outMap = new HashMap<>();
	 Map<Stmt,Set<Local>> defs = g.defs;

	 Queue<Stmt> wL = new LinkedList<>();
	 
	 Stmt s = g.head;
	 Map<Stmt,Set<Stmt>> intPreds = g.methIntPreds;
	 Map<Stmt,Set<Stmt>> intSuccs = g.methInterestingStmts;
	 wL.add(s);
	 Set<Stmt> succs;
	 Set<Stmt> preds;
	 Set<Local> gen;
	 do {
		 /*
		  * remove an element from worklist
		  */
		 s = wL.remove();
		 

		 succs = intSuccs.get(s);
		 preds = intPreds.get(s);
		 Map<Local,Set<Stmt>> outOld = outMap.get(s);

		 Map<Local,Set<Stmt>> in = new HashMap<>();
		 /*
		  * compute in from predecessors
		  */
		 if(preds != null) {
			 for(Stmt pr : preds) {
				 Map<Local,Set<Stmt>> outPr = outMap.get(pr);
				 if(outPr != null) {
					for(Map.Entry<Local,Set<Stmt>> ele : outPr.entrySet()) {
						Local key = ele.getKey();
						Set<Stmt> value = ele.getValue();
						if(in.containsKey(key)) {
							Set<Stmt> sts = in.get(key);

							sts.addAll(ele.getValue());

						}
						else {
							
							in.put(key, new HashSet<>(value));
						}
					}
				 }
			 }
		 }
		 /*
		  * gen is the set of objects defined by s
		  * Add s in the maps corresponding to the objects in gen and 
		  * kill the corresponding maps in out
		  */
		 
		 gen = defs.get(s);
		 /*
		  * OUT(s) = GEN(s) U (IN(S) - KILL(S))
		  */
		 Map<Local,Set<Stmt>> out = new HashMap<>(in);
		 Set<Stmt> st = new HashSet<>();
		 st.add(s);
		 if(gen != null) {
			 for(Local l:gen) {
				 if(in.containsKey(l)) {
					 Set<Stmt> set = in.get(l);
					 if(set!=null && set.equals(st)) {
						 out.put(l, set);
					 }
					 else {
						 out.put(l, st);
					 }
					 
				 }
				 else {
					 out.put(l, st);
				 }
			 }
		 }

		boolean changed = hasChanged(outOld,out);
		if(changed) {
			if(succs!=null)
			wL.addAll(succs);
			
			
		}
		outMap.put(s, out);
		reachDefMap.put(s,in); 
	 }while(!(wL.isEmpty()));
	 
	 return reachDefMap;
 }
 private static boolean hasChanged(Map<Local,Set<Stmt>> outOld, Map<Local,Set<Stmt>> out) {
	 boolean changed = false;
	 if(outOld==null && out!=null) {
		 changed = true;
	 }
	 else if(outOld.entrySet().size() != out.entrySet().size()) {
		 changed = true;
	 }
	 else {
		 for(Map.Entry<Local, Set<Stmt>> ele : out.entrySet()) {
			 Local l = ele.getKey();
			 if(!outOld.containsKey(l)) {
				 changed = true;
				 break;
			 }
			 else {
				 Set<Stmt> sOld = outOld.get(l);
				 Set<Stmt> sNew = ele.getValue();
				 if(!sNew.equals(sOld)) {
					 changed = true;
					 break;
				 }
				 
			 }
		 }
	 }
	 return changed;
	 
 }
}
