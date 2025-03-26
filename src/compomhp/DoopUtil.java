package compomhp;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.StringTokenizer;

import soot.Scene;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Type;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.internal.JCastExpr;

public class DoopUtil {
	Solver solver;
	int mineBetter = 0;
	int doopBetter = 0;
	int same = 0;
	int notFoundinDoop=0;
	int methNotFound=0;
	int mineMonoBetter=0;
	int doopMonoBetter=0;
	int Monosame=0;
	int doopTotFailed = 0;
	int doopcallEdges=0;
	int mycallEdges=0;
	int myMono=0;
	int doopMono=0;
	
	int myCGE=0;
	int doopCGE=0;
	int myExtraE=0;
	int doopExtraE=0;
	int commFC=0;
	String cs;
	public DoopUtil() {
		solver = Solver.v();
		findCsVariant(solver.arg.doopcode);
	}
	void compCallEdges() throws IOException{
		/*
		 * Populates call graphs of both ComPoMHP and Doop and compares
		 */
		String name;
    	name = "doopfiles/"+solver.arg.bench+cs+"CG.txt";
    	
		Map<SootMethod,Set<SootMethod>> doopCG = loadDoopCG(name);
		Map<SootMethod,Set<SootMethod>> myCG = new HashMap<>(); 
		for(Map.Entry<Stmt, BitSet> e : solver.callSiteMeths.entrySet()) {
    		Stmt st = e.getKey();
    		SootMethod caller = solver.myS.get(st);
//    		System.out.println("++++++"+st+" from "+myS.get(st).getSignature());
    		BitSet bs = e.getValue();
    		int i = bs.nextSetBit(0);
    		while( i!=-1 ) {
    			SootMethod callee = solver.methList.get(i);
    			if(!myCG.containsKey(caller)) {
    				myCG.put(caller, new HashSet<>());
    			}
    			myCG.get(caller).add(callee);
    			i = bs.nextSetBit(i+1);
    		}
		}
		Set<SootMethod> temp = new HashSet<>();
		for(Map.Entry<SootMethod, Set<SootMethod>> cg: myCG.entrySet()) {
			Set<SootMethod> my = cg.getValue();
			myCGE+=my.size();
			if(doopCG.containsKey(cg.getKey())) {
				Set<SootMethod> doop = doopCG.get(cg.getKey());
				/*
				 * get my-doop
				 */
				temp.clear();
				temp.addAll(my);
				temp.removeAll(doop);
				myExtraE+=temp.size();
				
			}
			else {
				myExtraE+=my.size();
			}
		}
		for(Map.Entry<SootMethod, Set<SootMethod>> cg: doopCG.entrySet()) {
			Set<SootMethod> doop = cg.getValue();
			doopCGE+=doop.size();
			if(myCG.containsKey(cg.getKey())) {
				Set<SootMethod> my = myCG.get(cg.getKey());
				/*
				 * get my-doop
				 */
				temp.clear();
				temp.addAll(doop);
				temp.removeAll(my);
				doopExtraE+=temp.size();
				
			}
			else {
				doopExtraE+=doop.size();
			}
		}
		System.out.println("my edges: "+myCGE+",Doop edges: "+doopCGE+",my extra: "+myExtraE+",doop extra: "+doopExtraE);
		
	}
	Map<SootMethod,Set<SootMethod>> loadDoopCG(String name) throws IOException {
		/*
		 * File content format:
		 * [Callercontext] Caller/callsite [Calleecontext] callee changed to
		 * [Callercontext];Caller/callsite;[Calleecontext];callee
		 * using cat <file> | sed 's/]\s\+/;/g' | sed 's/\s\+\[/;/g'
		 */
		FileReader fr = new FileReader(name);
		BufferedReader br = new BufferedReader(fr);
		String line = br.readLine();
		Map<SootMethod,Set<SootMethod>> doopCG = new HashMap<>();
		Set<String> notFound = new HashSet<>();
		Set<SootMethod> libs = new HashSet<>();
		while(line != null) {
			StringTokenizer st = new StringTokenizer(line,";");
			/*
			 * get 2nd and 4th token
			 */
			String t1 = st.nextToken();
			
			String callerSig = st.nextToken();
			StringTokenizer st2 = new StringTokenizer(callerSig,"/");
			int tokens = st2.countTokens();
			st.nextToken();
			String calleeSig = st.nextToken();
			if(tokens==3) {
				callerSig = st2.nextToken();
				if(callerSig.startsWith("<") && callerSig.endsWith(">")){
				
				if(Scene.v().containsMethod(callerSig)) {
					SootMethod caller = Scene.v().getMethod(callerSig);
					if(!caller.getDeclaringClass().isLibraryClass() && !caller.getDeclaringClass().isPhantom() && !solver.ignoredMeths.contains(caller)) {
						if(!doopCG.containsKey(caller)) {
							doopCG.put(caller, new HashSet<>());
						}
						if(calleeSig.startsWith("<") && calleeSig.endsWith(">")) {
							if(Scene.v().containsMethod(calleeSig)) {
								SootMethod callee = Scene.v().getMethod(calleeSig);
								if(!callee.getDeclaringClass().isLibraryClass() && !callee.getDeclaringClass().isPhantom() /*&& !solver.ignoreMethod(callee,null)*/) {
									
									doopCG.get(caller).add(callee);
								}
//								else {
//									libs.add(callee);
//								}
							}
							else {
								notFound.add(calleeSig);
							}
						}
					}
					else {
						libs.add(caller);
					}
				}
				else {
					notFound.add(callerSig);
				}
			}
			}
			line = br.readLine();
		}
		System.out.println("Built Doop CG, not found:"+notFound.size()+", libs: "+libs.size());
		br.close();
		fr.close();
		return doopCG;
		
	}
	 void printInvCount() throws IOException {
		 /*
		  * Populates maps for ComPoMHP and Doop. 
		  * The map gives for each method, for each call site inside it, the number of methods invoked. 
		  */
    	String name;
    	name = "doopfiles/"+solver.arg.bench+cs+"InvCount.txt";
    	Map<SootMethod,Map<String,Integer>> doopmethInvCounts = loadDoopInvCount(name);
    	Map<SootMethod,Map<String,Integer>> myInvCounts = new HashMap<>();
//    	FileWriter fileWriter = new FileWriter(solver.path+"/tmp/"+solver.aString+"invCount_"+solver.arg.bench+".txt");
//		PrintWriter printWriter = new PrintWriter(fileWriter);
		
    	//Set<Stmt> callSites = solver.callSiteMeths.keySet();
    	
    	for(Map.Entry<Stmt, BitSet> e : solver.callSiteMeths.entrySet()) {
    		Stmt st = e.getKey();
    		SootMethod caller = solver.myS.get(st);
//    		System.out.println("++++++"+st+" from "+myS.get(st).getSignature());
    		BitSet bs = e.getValue();
    		int i = bs.nextSetBit(0);
    		while( i!=-1 ) {
//    			System.out.println(methList.get(i).getSignature());
    			i = bs.nextSetBit(i+1);
    		}
    		Map<String,Integer> methMaps;
    		
			if(!myInvCounts.containsKey(caller)){
				myInvCounts.put(caller, new HashMap<>());
//				System.out.println("Adding caller:"+caller.getSignature());
			}
//			else {
//				System.out.println("Existing caller:"+caller.getSignature());
//			}
			methMaps = myInvCounts.get(caller);
			InvokeExpr ivst = st.getInvokeExpr();
			SootMethodRef smr = ivst.getMethodRef();
			String s = smr.getDeclaringClass().getName()+"."+smr.getName();
			int c= bs.cardinality();
			if(!methMaps.containsKey(s)) {
				methMaps.put(s, c);
//				System.out.println("Adding methMaps for "+s+" as "+c);
			}
			else {
				int oldC = methMaps.get(s);
				
				methMaps.put(s,c+oldC);
//				System.out.println("Updating methMaps for "+s+" as "+(c+oldC)+" old c was "+oldC);
			}
    	}
    	
    	
    	for(Map.Entry<SootMethod,Map<String,Integer>> ele: myInvCounts.entrySet()) {
    		SootMethod callerM = ele.getKey();
//			System.out.println("====Method: "+ele.getKey().getSignature());
    		if(!callerM.getDeclaringClass().isLibraryClass() && !callerM.getDeclaringClass().isPhantom()) {
    		Map<String,Integer> mymethCounts = ele.getValue();
    		Map<String,Integer> doopmethCounts = doopmethInvCounts.get(callerM);
			if(doopmethCounts != null) {
				for(Map.Entry<String, Integer> e2 : mymethCounts.entrySet()) {
					String calleeM = e2.getKey();
					int mycallCount = e2.getValue();
					int doopcallCount;
					if(!doopmethCounts.containsKey(calleeM)) {
						notFoundinDoop++;
					}
					else {
						doopcallCount = doopmethCounts.get(calleeM);
						doopcallEdges+=doopcallCount;
						mycallEdges+=mycallCount;
						if(doopcallCount==1) {
							doopMono++;
							if(mycallCount!=1) {
								doopMonoBetter++;
							}
						}
						if(mycallCount==1) {
							myMono++;
							if(doopcallCount!=1) {
								mineMonoBetter++;
							}
							else {
								Monosame++;
							}
						}
						if(mycallCount==doopcallCount) {
							same++;
						}
						else if(mycallCount < doopcallCount) {
							mineBetter++;
						}
						else {
							doopBetter++;
						}
					}
				}
			}
			else {
				methNotFound++;
			}
    	}
		}
    	
//    	printWriter.close();
//    	fileWriter.close();
    	
    	System.out.println("Mine Better: "+mineBetter+" Doop Better: "+doopBetter+" same: "+same+" notFoundinDoop: "+notFoundinDoop+" methNotFound in doop: "+methNotFound);
    	System.out.println("My mono "+myMono+" Doop Mono: "+doopMono+" my call edges: "+mycallEdges+" Doop call edges: "+doopcallEdges+" Doop Mono Better"+doopMonoBetter+" my nono better"+mineMonoBetter+"Mono same"+Monosame);
    	
    }
    private Map<SootMethod,Map<String,Integer>> loadDoopInvCount(String name) throws IOException {
    	
//    	FileReader fr = new FileReader("files/doop"+arg.bench+"InvCount.txt");
    	
    	//1-call-site
    	
    	
    	FileReader fr = new FileReader(name);
		BufferedReader br = new BufferedReader(fr);
		String line = br.readLine();
		Map<SootMethod,Map<String,Integer>> methInvCounts = new HashMap<>();
		int nonVirtualCount = 0;
		int notInScene=0;
		while(line != null) {
//			System.out.println("Reading line: "+line);
			StringTokenizer st = new StringTokenizer(line,"/");
			String callerSig = st.nextToken();
			SootMethod meth;
			String calleeSig = st.nextToken();
			if(st.hasMoreTokens()) {
				String callSiteCount = st.nextToken();
				StringTokenizer st2 = new StringTokenizer(callSiteCount,"\t");
				String callSiteNum = st2.nextToken();
				if(st2.hasMoreTokens()) {
					int callCount = Integer.valueOf(st2.nextToken());
					if(Scene.v().containsMethod(callerSig)) {
						meth = Scene.v().getMethod(callerSig);
						if(!methInvCounts.containsKey(meth)) {
							methInvCounts.put(meth, new HashMap<>());
						}
						if(methInvCounts.get(meth).containsKey(calleeSig)) {
							int oldCount = methInvCounts.get(meth).get(calleeSig);
							callCount+=oldCount;
							
						}
						methInvCounts.get(meth).put(calleeSig, callCount);
					}
					else {
						notInScene++;
					}
				}
			}
			else {
				nonVirtualCount++;
			}
			line = br.readLine();
		}
//		System.out.println("Read the file doopMInvCount");
//		for(Map.Entry<SootMethod,Map<String,Integer>> ele: methInvCounts.entrySet()) {
//			System.out.println("----Method: "+ele.getKey().getSignature());
//			for(Map.Entry<String,Integer> e2: ele.getValue().entrySet()) {
//				System.out.println(e2.getKey()+":"+e2.getValue());
//			}
//		}
		br.close();
		fr.close();
		return methInvCounts;
    }
    void compFailedCast() throws IOException {
    	
    	String name;
    	name = "doopfiles/"+solver.arg.bench+cs+"PotentiallyFailingCast.txt";
    	
    	Map<SootMethod,Map<String,Integer>> doopfailedCastCount = loadDoopFailedCast(name);
    	
    	System.out.println("++++++++Doop failed cast");
    	for(Map.Entry<SootMethod,Map<String,Integer>> e : doopfailedCastCount.entrySet()) {
    		int methC = 0;
    		String types="";
    		for(Map.Entry<String,Integer> e1: e.getValue().entrySet()) {
    			String tp = e1.getKey();
    			if(!tp.startsWith("java") && !tp.startsWith("jdk") && tp.contains("."))
//    					!tp.startsWith("int") && !tp.startsWith("char") && !tp.startsWith("long")
//    					&& !tp.startsWith("float") &&
//    					!tp.startsWith("boolean") &&
//    					!tp.startsWith("double")) 
    					{
    			types=types+","+tp;
    			int c = e1.getValue();
    			methC+=c;
    			doopTotFailed+=c;
    			}
    		}
    		if(methC>0) {
    			if(solver.ignoredMeths.contains(e.getKey())) {
    				System.out.println("ignored");
    			}
    		System.out.println("In method:"+e.getKey().getSignature()+" size: "+methC+"types: "+types);
    		}
    	}
    	/*
    	 * get my failed casts
    	 */
    	Map<SootMethod,Map<String,Integer>> myfailedCastCount = new HashMap<>();
    	for(Map.Entry<SootMethod, Set<AssignStmt>> e: solver.fcast.entrySet()) {
    		SootMethod m = e.getKey();
    		if(!myfailedCastCount.containsKey(m)) {
    			myfailedCastCount.put(m, new HashMap<>());
    		}
    		for(AssignStmt as: e.getValue()) {
    			String castType = ((JCastExpr)as.getRightOp()).getCastType().toString();
    			Map<String,Integer> mi = myfailedCastCount.get(m);
    			if(mi.containsKey(castType)) {
    				mi.put(castType,mi.get(castType)+1);
    			}
    			else {
    				mi.put(castType,1);
    			}
    		}
    	}
    	for(Map.Entry<SootMethod,Map<String,Integer>> me: myfailedCastCount.entrySet()) {
    		SootMethod m = me.getKey();
    		Map<String,Integer> mi = me.getValue();
    		if(doopfailedCastCount.containsKey(m)) {
    			Map<String,Integer> md = doopfailedCastCount.get(m);
    			for(Map.Entry<String, Integer> e: mi.entrySet()) {
    				String type = e.getKey();
    				int c = e.getValue();
    				if(md.containsKey(type)) {
    					int cd = md.get(type);
    					if(cd <= c) {
    						commFC+=cd;
    					}
    					else {
    						commFC+=c;
    					}
    				}
    			}
    		}
    	}
    	System.out.println("++++++++Total doop failed casts methods: "+doopfailedCastCount.size()+" total failed casts: "+doopTotFailed+" common Failed Casts: "+commFC);
    	//System.out.println("+++++++++Doop failed casts:"+failedCasts);+
    	
    }
    public void findCsVariant(int code) {
    	switch(code) {
    	case 1:
    		
    		cs="1capp";
    		break;
    	case 2:
    		
    		cs="1cfull";
    		break;
    	case 3:
    		
    		cs="1oapp";
    		break;
    	case 4:
    		
    		cs="1ofull";
    		break;
    	case 5:
    		
    		cs="adp2objhfull";
    		break;
    	}
    }
private Map<SootMethod,Map<String,Integer>> loadDoopFailedCast(String name) throws IOException {
    	
//    	FileReader fr = new FileReader("files/doop"+arg.bench+"InvCount.txt");
    	
    	//1-call-site
    	
    	
    	FileReader fr = new FileReader(name);
		BufferedReader br = new BufferedReader(fr);
		String line = br.readLine();
		/*
		 * For each method, for a given type, no of failed casts
		 */
		Map<SootMethod,Map<String,Integer>> failedCastCount = new HashMap<>();
		Set<SootMethod> libMeths = new HashSet<>();
		Set<String> notInScene = new HashSet<>();
		while(line != null) {
//			System.out.println("Reading line: "+line);
			StringTokenizer st = new StringTokenizer(line,"\t");
			String type = st.nextToken();
			String t2 = st.nextToken();
			StringTokenizer st2 = new StringTokenizer(t2,"/");
			String methSig = st2.nextToken();
			
			if(Scene.v().containsMethod(methSig)) {
				SootMethod m = Scene.v().getMethod(methSig);
				if(!m.isJavaLibraryMethod()) {
					if(!failedCastCount.containsKey(m)) {
						failedCastCount.put(m,new HashMap<>());
					}
					Map<String, Integer> tm = failedCastCount.get(m);
					if(!tm.containsKey(type)) {
						tm.put(type, 1);
					}
					else {
						int c = tm.get(type);
						tm.put(type, c+1);
					}
				}
				else {
					libMeths.add(m);
				}
			}else {
				notInScene.add(methSig);
			}
			
			
			
			line = br.readLine();
		}

		br.close();
		fr.close();
		return failedCastCount;
    }
public void printDoopRes(long timeS) throws IOException {
	String filename = "doopresult.txt";
	File f = new File(solver.path+"/tmp/"+filename);
	boolean exist = true;
	if(!f.exists())
		exist = false;
	FileWriter fw = new FileWriter(f,true);
	BufferedWriter br = new BufferedWriter(fw);
	PrintWriter pw = new PrintWriter(br);
	if(!exist) {
		pw.println("Bench,cs,mineBetter,doopBetter,same,myMono,doopMono,myMonoBetter,doopMonoBetter,sameMono,myCE,doopCE,myFC,doopFC,commFC,totalCasts,myTime,myCGE,doopCGE,myExtraE,doopExtraE");
	}
	
	
	pw.println(solver.arg.bench+","+cs+","+mineBetter+","+doopBetter+","+same+
			","+myMono+","+doopMono+","+mineMonoBetter+","+doopMonoBetter+","+Monosame+
			","+mycallEdges+","+doopcallEdges+
			","+solver.failedCasts+","+doopTotFailed+","+commFC+","+solver.totalCasts+
			","+timeS+
			","+myCGE+","+doopCGE+","+myExtraE+","+doopExtraE);
	pw.close();
	br.close();
	fw.close();
}
}
