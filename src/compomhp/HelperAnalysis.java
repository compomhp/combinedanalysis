package compomhp;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.file.FileSystems;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;

import javafx.util.Pair;
import soot.ArrayType;
import soot.Body;
import soot.Hierarchy;
import soot.IntType;
import soot.Local;
import soot.LongType;
import soot.MethodOrMethodContext;
import soot.PrimType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.VoidType;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JNopStmt;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.tagkit.Tag;

public class HelperAnalysis {
	static Map<SootMethod,Set<SootField>> methFields = new HashMap<SootMethod,Set<SootField>>();
	static Map<SootMethod,Set<SootField>> methAccessedFlds = new HashMap<SootMethod,Set<SootField>>();
	static Set<SootMethod> zeros = new HashSet<>();
	static Set<SootMethod> zeroReach = new HashSet<>();
	static Set<SootMethod> sames = new HashSet<>();
	static Set<SootMethod> tailNoField = new HashSet<>();
	static Set<SootMethod> zeroAccess = new HashSet<>();
	static Set<SootMethod> ignoredMeths = new HashSet<SootMethod>();
	static Set<SootMethod> bodyNullMeths = new HashSet<SootMethod>();
	static Map<Stmt,AllocNode> stmtAllocNodes = new ConcurrentHashMap<>();
	static Map<AllocNode, Set<AllocNodeField>> fieldListIP = new HashMap<>();
	//static Map<SootMethod,Set<SootField>> newmethFields = new HashMap<SootMethod,Set<SootField>>();
	static Set<SootMethod> noMHPmeth = new HashSet<>();
	static Set<SootMethod> processedMeths = new HashSet<>();
	static Set<StmtLocal> botLocals = new HashSet<>();
	static Solver solver;
	public static void populateInterestingFields() {
		System.out.println("-----------Starting to calculate interesting fields------------");
		long startTime = System.nanoTime();
		/*
		 * 1. Get the call graph from Scene
		 * 2. Find tails and add to worklist
		 * 3. For each method m in the worklist, get the incoming edges and for each source method, src,
		 * 	3.1. get the interesting fields of src if not already computed.
		 * 	3.2. get the interesting fields of m, if not already computed.
		 *  3.3. add m's fields into src's fields. If there is a change, add src into worklist
		 */
		
		CallGraph cg = Scene.v().getCallGraph();

		System.out.println("callgraph size: "+cg.size());
//		getUsingTails(cg);
		getUsingAllEdges(cg);

//		System.out.println("Calculated interesting fields for methods:"+methFields.size());
//		System.out.println("Calculated interesting fields for methods all edges:"+newmethFields.size());
		long elapsedTime = System.nanoTime() - startTime;
		System.out.println("--------Done Total time for fields pass:"+elapsedTime/1000000+" msec;"+elapsedTime/1000000000+" sec----------");

	}
	public static void populateIntFieldsUsingPoA(boolean interleaved) {
		System.out.println("-----------Performing Helper Analysis------------");
		long startTime = System.nanoTime();
		String path = FileSystems.getDefault()
		        .getPath("")
		        .toAbsolutePath()
		        .toString();
		File file = new File(path+"/tmp/inFieldLog.txt");
		PrintStream stdout = System.out;
	      //Instantiating the PrintStream class
	      try {
			PrintStream stream = new PrintStream(file);
			System.setOut(stream);
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		genCallGraph(interleaved);
		getUsingAllEdges();
//		System.out.println("Calculated interesting fields for methods:"+methFields.size());
//		System.out.println("Calculated interesting fields for methods all edges:"+newmethFields.size());
		System.out.println("Bot Locals:"+botLocals.size());
		botLocals.clear();
		Set<SootField> acc = new HashSet<>();
		long elapsedTime = System.nanoTime() - startTime;
		System.out.println("--------Done Total time for fields pass:"+elapsedTime/1000000+" msec;"+elapsedTime/1000000000+" sec----------");
		ignoredMeths = solver.ignoredMeths;

		for(Map.Entry<SootMethod, Set<SootField>> ele : methFields.entrySet()) {
			SootMethod m = ele.getKey();
			Set<SootField> s = ele.getValue();

			Set<SootField> a = methAccessedFlds.get(m);
			String className = m.getDeclaringClass().getName();
			if (className.startsWith("org.apache.xerces")) {
				acc.addAll(a);
			}
//			if(m.getSignature().equals("<org.apache.xml.dtm.ref.ExpandedNameTable: void initExtendedTypes()>")) {
//	    		System.out.println("debug stop");
//	    	}
//			 if (className.startsWith("org.apache.xml")) {
//				 if(a.size()>0) {
//		        	   System.out.println("hi");
//		           }
//	        }
//	        else if (className.startsWith("org.apache.xpath")) {
//	        	 if(a.size()>0) {
//		        	   System.out.println("hi");
//		           }
//	        }
//	        if (className.equals("org.w3c.dom.Document")) {
//	           if(a.size()>0) {
//	        	   System.out.println("hi");
//	           }
//	        }
//
//	        // Summarize fields for DOM Element
//	        else if (className.equals("org.w3c.dom.Element")) {
//	        	if(a.size()>0) {
//		        	   System.out.println("hi");
//		           }
//	        }
//
//	        // Summarize fields for SAX InputSource
//	        else if (className.equals("org.xml.sax.InputSource")) {
//	        	if(a.size()>0) {
//		        	   System.out.println("hi");
//		           }
//	        }
//
//	        // Summarize fields for XMLSerializer
//	        else if (className.equals("org.apache.xml.serialize.XMLSerializer")) {
//	        	if(a.size()>0) {
//		        	   System.out.println("hi");
//		           }
//	        }
//
//	        // Summarize fields for Xalan TransformerImpl
//	        else if (className.equals("org.apache.xalan.transformer.TransformerImpl")) {
//	        	if(a.size()>0) {
//		        	   System.out.println("hi");
//		           }
//	        }
//	     // Summarize fields for Batik DOM
//	        else if (className.startsWith("org.apache.batik.dom")) {
//	        	if(a.size()>0) {
//		        	   System.out.println("hi");
//		           }
//	        }
//
//	        // Summarize fields for Batik SVG Elements
//	        else if (className.startsWith("org.apache.batik.svggen")) {
//	        	if(a.size()>0) {
//		        	   System.out.println("hi");
//		           }
//	        }
//	     // Summarize fields for PMD XML Parser
//	        else if (className.startsWith("net.sourceforge.pmd.lang.xml")) {
//	        	if(a.size()>0) {
//		        	   System.out.println("hi");
//		           }
//	        }
//
//	        // Summarize fields for PMD Node
//	        else if (className.startsWith("net.sourceforge.pmd.lang.ast")) {
//	        	if(a.size()>0) {
//		        	   System.out.println("hi");
//		           }
//	        }
			
			if(s.size()==0) {
				Body b = Solver.getBody(m);
				if(b!=null && !SimplifyUtil.opaqueMethod(m, b))
				zeros.add(m);

			}
			else if(a.size()==0) {
				Body b = Solver.getBody(m);
				if(b!=null && !SimplifyUtil.opaqueMethod(m, b))
				zeroAccess.add(m);

			}
//			else if(s.size()== a.size()) {
//				
//
//				sames.add(m);
//
//			}
		}
		System.out.println("zero"+zeros.size()+" same: "+sames.size());
		findTails();
		int zc = 0;
		for(SootMethod zm : zeros) {
			if(MyCG.HAedgesOutof.containsKey(zm)) {
			zc+=MyCG.HAedgesOutof.get(zm).size();
			}
		}
		 Queue<SootMethod> wL = new LinkedList<>(zeros);
		 Set<SootMethod> visited = new HashSet<>();
		 if(!wL.isEmpty()) {
		do {
			SootMethod zm = wL.remove();
			zeroReach.add(zm);
			visited.add(zm);
			Set<Pair<SootMethod,SootMethod>> set = MyCG.HAedgesOutof.get(zm);
			if(set != null) {
				for(Pair<SootMethod,SootMethod> p : set) {
					SootMethod dest = p.getValue();
					if(!visited.contains(dest))
					wL.add(dest);
				}
			}
		}while(!wL.isEmpty());
		 }
		System.out.println(zc);
		for(AllocNodeField anf: solver.ifieldPts.keySet()) {
			if(!fieldListIP.containsKey(anf.an)) {
    			fieldListIP.put(anf.an, new HashSet<>());
    		}
    		fieldListIP.get(anf.an).add(anf);
		}
		MyCG.callerStmtsHA = solver.callerStmts;
		System.setOut(stdout);
		Solver.intPass = false;
	}
	private static void findTails() {
//		Set<SootMethod> tls = new HashSet<>();
		for(Map.Entry<SootMethod, Set<Pair<SootMethod,SootMethod>>> ele : MyCG.HAedgesInto.entrySet()) {
			SootMethod sm = ele.getKey();
			boolean isTail = true;
			if(MyCG.HAedgesOutof.containsKey(sm)) {
				Set s = MyCG.HAedgesOutof.get(sm);
				if(s!=null && !s.isEmpty() ) {
					isTail = false;
				}
			}
			if(isTail) {
				if(methFields.get(sm) == null ||  methFields.get(sm).size()==0) {
					Body b = Solver.getBody(sm);
					if(b!=null && !SimplifyUtil.opaqueMethod(sm, b))
					tailNoField.add(sm);
				}
//				else {
//					boolean allLoads = true;
//					Set st = solver.loadStores.get(sm);
//					if(st!=null)
//					for(Stmt s: solver.loadStores.get(sm)) {
//						if(isStore((AssignStmt)s)) {
//							allLoads = false;
//							break;
//						}
//					}
//					if(allLoads)
//						tailOnlyLoad.add(sm);
//						
//				}
			}
		}
		System.out.println("Tails"+tailNoField.size());
	}
	 public static boolean isStore(AssignStmt s) {
			boolean store = false;
			Value vl = s.getLeftOp();
			Value vr = s.getRightOp();
			if(vl instanceof JInstanceFieldRef && vr instanceof Local) {
				
				store = true;
			}
			return store;
		}
	private static void genCallGraph(boolean interleaved){
		Solver.intPass = true;
		solver = Solver.v();
		Arg arg = new Arg();
		arg.combined = false;

		arg.mhp = false;
		arg.interleaved = interleaved;
		arg.genParallel = false;
		solver.arg = arg;
		SolverUtil.initSolverInstance(solver, arg);
		try {
			solver.solve();
		} catch (InterruptedException | ExecutionException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (SecurityException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
//		finally {
//			solver.pool.shutdown();
//    		
//    		try {
//				solver.pool.awaitTermination(60, TimeUnit.SECONDS);
//			} catch (InterruptedException e) {
//				// TODO Auto-generated catch block
//				e.printStackTrace();
//			}
//		}
		
	}
	 public static Body getBody(SootMethod sm) {
//		 if(sm.getSignature().equals("<org.dacapo.harness.TestHarness: boolean isValidSize(java.lang.String)>")) {
//			 System.out.println("Stop");
//		 }
			Body b = null;
			if(sm.hasActiveBody())
				b = sm.getActiveBody();
			else if(sm.isConcrete()){
				b = sm.retrieveActiveBody();
			}
			return b;
		}
	 public static Set<SootField> getFields(SootMethod m, Body b){
		 
		 processedMeths.add(m);
		 
		 Set<SootField> fields = new HashSet<SootField>();
		 Iterator<Unit> stmtIt = b.getUnits().snapshotIterator();
		 while(stmtIt.hasNext()) {
			 Stmt s = (Stmt)stmtIt.next();
			 if(s.containsFieldRef()) {

				SootField sf = s.getFieldRef().getField();

				Type t = sf.getType();
				
				if(SimplifyUtil.isInterestingType(t) && !sf.isStatic()) {
					List<Tag> tags = s.getTags();
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
						if(!tagFound) {
							fields.add(sf);
						}
				}
			 }	
		 }
		 methAccessedFlds.put(m,new HashSet<SootField>(fields));
		 return fields;
	 }
	
	 public static void getUsingAllEdges(CallGraph cg) {
		 Set<Edge> edges = new HashSet<Edge>(); 
		 Iterator<Edge> iteratorEdges = cg.iterator();
			while (iteratorEdges.hasNext()) {
	            Edge edge = iteratorEdges.next();
	            MethodOrMethodContext node_tgt = edge.getTgt(); 
	            MethodOrMethodContext node_src = edge.getSrc();
	            if(node_tgt instanceof SootMethod && node_src instanceof SootMethod) {
//	            	SootMethod tgt_meth = (SootMethod)node_tgt;
//	            	SootMethod src_meth = (SootMethod)node_src;
	            	
	            	//if(!cg.edgesOutOf(tgt_meth).hasNext())
	            		edges.add(edge);
	            		
	            }
	         }
			
			List<Edge> edgeList = new ArrayList<Edge>(edges);
			while(!edgeList.isEmpty()) {
				Edge edge = edgeList.remove(0);
				MethodOrMethodContext node_src = edge.getSrc();
				MethodOrMethodContext node_tgt = edge.getTgt();
				SootMethod src_meth = (SootMethod)node_src;
				SootMethod tgt_meth = (SootMethod)node_tgt;
				
				boolean tgtChanged = false;
					/*
					 * Calculate the fields of target
					 */
				Set<SootField> tgtfields = methFields.get(tgt_meth);
				if(!methAccessedFlds.containsKey(tgt_meth) || tgtfields == null) {
					Body b = getBody(tgt_meth);
					if( b!= null) {
						
						if(tgtfields !=  null)
							tgtChanged = tgtfields.addAll(getFields(tgt_meth,b));
						else {
							tgtfields = getFields(tgt_meth,b);
							methFields.put(tgt_meth, tgtfields);
							tgtChanged = true;
						}
						
						
					}
				}
				if(tgtChanged) {
					Iterator<Edge> itr = cg.edgesInto(tgt_meth);
					while(itr.hasNext()) {
						Edge e = itr.next();
						if(!edgeList.contains(e)) {
							edgeList.add(e);
						}
					}
				}
					/*
					 * Calculate the fields of source
					 */
				Set<SootField> srcfields = methFields.get(src_meth);
				boolean src_changed = false;
				if(!methAccessedFlds.containsKey(src_meth) || srcfields == null) {
					Body b = getBody(src_meth);
					if( b!= null) {
						if(srcfields !=  null)
							src_changed = srcfields.addAll(getFields(src_meth,b));
						else {
						srcfields = getFields(src_meth, b);
						methFields.put(src_meth, srcfields);
						src_changed = true;
						}
					}
				}
					/*
					 * If there is a change in target fields
					 */
				boolean srcFieldUpdated = false;	
//				if(tgtChanged) {
					if(srcfields!=null && tgtfields != null)
						srcFieldUpdated = srcfields.addAll(tgtfields);
					
//				}
				if(src_changed || srcFieldUpdated) {
					Iterator<Edge> itr = cg.edgesInto(src_meth);
					while(itr.hasNext()) {
						Edge e = itr.next();
						if(!edgeList.contains(e)) {
							edgeList.add(e);
						}
					}
				}
				
				
				
			}
	 }
	 public static void getUsingAllEdges() {
//		 	Set<SootMethod> noField = new HashSet<>();
			List<Pair<SootMethod, SootMethod>> edgeList = new ArrayList<Pair<SootMethod, SootMethod>>(MyCG.edgesHA);
			System.out.println("Total edges:"+MyCG.edgesHA.size());
			while(!edgeList.isEmpty()) {
				Pair<SootMethod, SootMethod> edge = edgeList.remove(0);
				
				SootMethod src_meth = edge.getKey();
				SootMethod tgt_meth = edge.getValue();
				

					/*
					 * Calculate the fields of target
					 */
				Set<SootField> tgtfields = methFields.get(tgt_meth);
				boolean tgtFldsChanged = false;
				/*
				 * Calculate the fields of target
				 */
			
			
				if(!methAccessedFlds.containsKey(tgt_meth) || tgtfields == null) {
					Body b = getBody(tgt_meth);
					if( b!= null) {
						if(tgtfields !=  null)
							tgtFldsChanged = tgtfields.addAll(getFields(tgt_meth,b));
						else {
							tgtfields = getFields(tgt_meth,b);
							methFields.put(tgt_meth, tgtfields);
							tgtFldsChanged = true;
						}
						
					}
				}
				
					/*
					 * Calculate the fields of source
					 */
				Set<SootField> srcfields = methFields.get(src_meth);
				boolean srcFldsChanged = false;
				if(!methAccessedFlds.containsKey(src_meth) || srcfields == null) {
					Body b = getBody(src_meth);
					if( b!= null) {
						if(srcfields !=  null)
							srcFldsChanged = srcfields.addAll(getFields(src_meth,b));
						else {
							srcfields = getFields(src_meth,b);
							methFields.put(src_meth, srcfields);
							srcFldsChanged = true;
						}
					}
				}
					/*
					 * If there is a change in target fields
					 */	
				
				if(srcfields!=null && tgtfields != null)	{
					srcFldsChanged = srcfields.addAll(tgtfields);
				}
				if(srcFldsChanged ) {
					Set<Pair<SootMethod, SootMethod>> edgesInto = MyCG.HAedgesInto.get(src_meth);
					if(edgesInto != null) {
						Iterator<Pair<SootMethod, SootMethod>> itr = edgesInto.iterator();
						while(itr.hasNext()) {
							Pair<SootMethod, SootMethod> e = itr.next();
							if(!edgeList.contains(e)) {
								edgeList.add(e);
							}
						}
					}
				}
				
				if(tgtFldsChanged ) {
					Set<Pair<SootMethod, SootMethod>> edgesInto = MyCG.HAedgesInto.get(tgt_meth);
					if(edgesInto != null) {
						Iterator<Pair<SootMethod, SootMethod>> itr = edgesInto.iterator();
						while(itr.hasNext()) {
							Pair<SootMethod, SootMethod> e = itr.next();
							if(!edgeList.contains(e)) {
								edgeList.add(e);
							}
						}
					}
				}
				
				
				
			}
//			System.out.println("No fields meths: "+noField.size());
//			System.out.println("No mhp meths: "+noMHPmeth.size());
//			Set<SootMethod> intersect = new HashSet<>(noMHPmeth);
//			intersect.retainAll(noField);
//			System.out.println("Both:"+intersect.size());
			System.out.println("Done");
	 }
	 public static boolean isThreadClass(SootClass sclass) {
			
			Hierarchy h = Scene.v().getActiveHierarchy();
			 boolean threadclass = false;
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
		        return threadclass;
		}
}
