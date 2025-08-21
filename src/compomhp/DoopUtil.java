package compomhp;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
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
import soot.SootClass;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.jimple.AssignStmt;
import soot.jimple.InstanceInvokeExpr;
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
	
	 Map<String,Integer> doop1objTimes = new HashMap<>();
	Map<String,Integer> doopa2objhTimes = new HashMap<>();
	/*
	 * h2 
	 * 1obj - app: 4m 48s (288s); full: 5m 14s (314s)
	 * adp2objh - app: 4m 15s (255s); full: 6m 3s (363s)
	 */
	
	
	public DoopUtil(int code) {
		solver = Solver.v();
//		findCsVariant(solver.arg.doopcode);
		findCsVariant(code);
		doop1objTimes.put("avrora", 1267);
		doop1objTimes.put("sunflow", 1213);
		doop1objTimes.put("luindex", 1672);
		doop1objTimes.put("lusearch", 603);
		doop1objTimes.put("pmd", 1218);
		doop1objTimes.put("xalan", 2617);
		doop1objTimes.put("h2", 288);
		
		doopa2objhTimes.put("avrora", 1185);
		doopa2objhTimes.put("sunflow", 1236);
		doopa2objhTimes.put("luindex", 611);
		doopa2objhTimes.put("lusearch", 596);
		doopa2objhTimes.put("pmd", 1260);
		doopa2objhTimes.put("xalan", 2747);
		doopa2objhTimes.put("h2", 255);
	}
	void compCallEdges() throws IOException{
		/*
		 * Populates call graphs of both ComPoMHP and Doop and compares
		 */
		String name;
    	name = "doopfiles/"+solver.arg.bench+cs+"CG.txt";
    	Map<SootMethod,Map<String,Set<SootMethod>>> doopcallSiteCG = new HashMap<>();
		Map<SootMethod,Set<SootMethod>> doopCG = loadDoopCG(name, doopcallSiteCG);
		Map<SootMethod,Set<SootMethod>> myCG = new HashMap<>(); 
		Map<SootMethod,Map<Stmt,Set<SootMethod>>> mycallSiteCG = new HashMap<>(); 
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
    			if(!mycallSiteCG.containsKey(caller)) {
    				mycallSiteCG.put(caller, new HashMap<>());
    			}
    			if(!mycallSiteCG.get(caller).containsKey(st)) {
    				mycallSiteCG.get(caller).put(st, new HashSet<>());
    			}
    			myCG.get(caller).add(callee);
    			mycallSiteCG.get(caller).get(st).add(callee);
    			i = bs.nextSetBit(i+1);
    		}
		}
		/*
		 * count call graph edges of mine
		 */
		for(Map.Entry<SootMethod,Map<Stmt,Set<SootMethod>>> ele: mycallSiteCG.entrySet()) {
			Map<Stmt,Set<SootMethod>> methMap = ele.getValue();
			for(Map.Entry<Stmt, Set<SootMethod>> e: methMap.entrySet()){
				myCGE+=e.getValue().size();
			}
		}
		/*
		 * count call graph edges of doop
		 */
		for(Map.Entry<SootMethod,Map<String,Set<SootMethod>>> ele: doopcallSiteCG.entrySet()) {
			Map<String,Set<SootMethod>> methMap = ele.getValue();
			for(Map.Entry<String, Set<SootMethod>> e: methMap.entrySet()){
				doopCGE+=e.getValue().size();
			}
		}
		Set<SootMethod> temp = new HashSet<>();
		for(Map.Entry<SootMethod, Set<SootMethod>> cg: myCG.entrySet()) {
			Set<SootMethod> my = cg.getValue();
//			myCGE+=my.size();
			
				Set<SootMethod> doop = doopCG.get(cg.getKey());
				/*
				 * get my-doop
				 */
				temp.clear();
				temp.addAll(my);
				
				if(doopCG.containsKey(cg.getKey())) {
					temp.removeAll(doop);
					myExtraE+=temp.size();
				}
				else {
					myExtraE+=my.size();
				}
		}
		for(Map.Entry<SootMethod, Set<SootMethod>> cg: doopCG.entrySet()) {
			Set<SootMethod> doop = cg.getValue();
//			doopCGE+=doop.size();
		
				Set<SootMethod> my = myCG.get(cg.getKey());
				/*
				 * get my-doop
				 */
				temp.clear();
				temp.addAll(doop);
				
				if(myCG.containsKey(cg.getKey())) {
					temp.removeAll(my);
					doopExtraE+=temp.size();
				}
				else {
					doopExtraE+=doop.size();
				}
		}
		System.out.println("my edges: "+myCGE+",Doop edges: "+doopCGE+",my extra: "+myExtraE+",doop extra: "+doopExtraE);
		
	}
	Map<SootMethod,Set<SootMethod>> loadDoopCG(String name, Map<SootMethod,Map<String,Set<SootMethod>>> doopcallSiteCG) throws IOException {
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
//			if(line.equals("[<<immutable-context>>;<org.dacapo.harness.Sunflow: void <init>(org.dacapo.parser.Config,java.io.File)>/java.lang.Class.getMethod/0;<class org.sunflow.Benchmark>;<java.lang.Class: java.lang.reflect.Method getMethod(java.lang.String,java.lang.Class[])>")) {
//				System.out.println("debug");
//			}
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
				String callSite = st2.nextToken()+"/"+st2.nextToken();
				if(callerSig.startsWith("<") && callerSig.endsWith(">")){
				
				if(Scene.v().containsMethod(callerSig)) {
					SootMethod caller = Scene.v().getMethod(callerSig);
					if(!caller.getDeclaringClass().isLibraryClass() && !caller.getDeclaringClass().isPhantom() && !solver.ignoredMeths.contains(caller)) {
						if(!doopCG.containsKey(caller)) {
							doopCG.put(caller, new HashSet<>());
						}
						if(!doopcallSiteCG.containsKey(caller)) {
							doopcallSiteCG.put(caller, new HashMap<>());
						}
						if(!doopcallSiteCG.get(caller).containsKey(callSite)) {
							doopcallSiteCG.get(caller).put(callSite, new HashSet<>());
						}
						if(calleeSig.startsWith("<") && calleeSig.endsWith(">")) {
							if(Scene.v().containsMethod(calleeSig)) {
								SootMethod callee = Scene.v().getMethod(calleeSig);
								if(!callee.getDeclaringClass().isLibraryClass() && !callee.getDeclaringClass().isPhantom() /*&& !solver.ignoreMethod(callee,null)*/) {
									
									doopCG.get(caller).add(callee);
									doopcallSiteCG.get(caller).get(callSite).add(callee);
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
	void countDoopMono(Map<SootMethod,Map<String,Integer>> doopmethInvCounts) {

    	for(Map.Entry<SootMethod,Map<String,Integer>> ele: doopmethInvCounts.entrySet()) {
    		SootMethod callerM = ele.getKey();
    		if(!callerM.getDeclaringClass().isLibraryClass() && !callerM.getDeclaringClass().isPhantom()) {
    			Map<String,Integer> doopmethCounts = doopmethInvCounts.get(callerM);
    			if(doopmethCounts != null) {
    				for(Map.Entry<String, Integer> e2 : doopmethCounts.entrySet()) {
    					String calleeM = e2.getKey();
    					StringTokenizer tokenizer = new StringTokenizer(calleeM, ".");
    	                String lastToken = "";
    	                while (tokenizer.hasMoreTokens()) {
    	                    lastToken = tokenizer.nextToken(); // Keep updating to get the last token
    	                }

    	                // Get the remaining string
    	                String remainingString = "";
    	                if (!lastToken.isEmpty()) {
    	                    remainingString = calleeM.substring(0, calleeM.lastIndexOf(lastToken)-1);
    	                }
    					SootClass sc = Scene.v().getSootClass(remainingString);
    					String mname = lastToken;
    					SootMethod sm = null;
    					try {
    					 sm = sc.getMethodByName(mname);
    					}catch(RuntimeException e) {
    						continue;
    					}
    					if(sm != null) {
    						if(sm.isStatic())
    							continue;
    					}
    					int doopcallCount = e2.getValue();
    					if(doopcallCount==1) {
    						doopMono++;
    					}
    				}	
    			}
    		}
    	}
	}
	 void printInvCount() throws IOException {
		 /*
		  * Populates maps for ComPoMHP and Doop. 
		  * The map gives for each method, for each calleeSig, the number of methods invoked. 
		  */
    	String name;
    	name = "doopfiles/"+solver.arg.bench+cs+"InvCount.txt";
    	Map<SootMethod,Map<String,Integer>> doopmethInvCounts = loadDoopInvCount(name);
    	countDoopMono(doopmethInvCounts);
    	Map<SootMethod,Map<String,Integer>> myInvCounts = new HashMap<>();

    	for(Map.Entry<Stmt, BitSet> e : solver.callSiteMeths.entrySet()) {
    		Stmt st = e.getKey();
    		InvokeExpr ivst = st.getInvokeExpr();
    		if(ivst instanceof InstanceInvokeExpr) {
	    		SootMethod caller = solver.myS.get(st);
	    		BitSet bs = e.getValue();
	    		int i = bs.nextSetBit(0);
	    		while( i!=-1 ) {
	    			i = bs.nextSetBit(i+1);
	    		}
	    		Map<String,Integer> methMaps;
	    		
				if(!myInvCounts.containsKey(caller)){
					myInvCounts.put(caller, new HashMap<>());
				}
				methMaps = myInvCounts.get(caller);
				
				
				SootMethodRef smr = ivst.getMethodRef();
				String s = smr.getDeclaringClass().getName()+"."+smr.getName();
				int c= bs.cardinality();
				if(!methMaps.containsKey(s)) {
					methMaps.put(s, c);
				}
				else {
					int oldC = methMaps.get(s);
					
					methMaps.put(s,c+oldC);
	
				}
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
//						doopcallEdges+=doopcallCount;
//						mycallEdges+=mycallCount;
						if(doopcallCount==1 && mycallCount==1) {
//							doopMono++;
//							myMono++;
							Monosame++;
						}
						else if(doopcallCount==1 && mycallCount>1) {
//							doopMono++;
							doopMonoBetter++;
							
						}
						else if(mycallCount==1 && doopcallCount > 1) {
//							myMono++;
							mineMonoBetter++;
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
    	
    	/*
    	 * Example doopInvCount text file entries format
    	 * <org.dacapo.parser.Config: int getThreadLimit(java.lang.String)>/org.dacapo.parser.Config.getSize/0	1
    	 * caller/callee/callSiteNumber callCount
    	 */
    	
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
    	commFC= 0;
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
		pw.println("Bench,cs,mineBetter,doopBetter,same,myMono,doopMono,myMonoBetter,doopMonoBetter,sameMono,myCE,doopCE,myFC,doopFC,commFC,totalCasts,myTime,myCGE,doopCGE,myExtraE,doopExtraE,doopTime");
	}
	int time=0;
	if(cs.equals("1ofull")) {
		time = doop1objTimes.get(solver.arg.bench);
	}
	else if(cs.equals("adp2objhfull")) {
		time = doopa2objhTimes.get(solver.arg.bench);
	}
	pw.println(solver.arg.bench+","+cs+","+mineBetter+","+doopBetter+","+same+
			","+solver.monomorphicCount+","+doopMono+","+mineMonoBetter+","+doopMonoBetter+","+Monosame+
			","+mycallEdges+","+doopcallEdges+
			","+solver.failedCasts+","+doopTotFailed+","+commFC+","+solver.totalCasts+
			","+timeS+
			","+myCGE+","+doopCGE+","+myExtraE+","+doopExtraE+","+time);
	pw.close();
	br.close();
	fw.close();
}
}
