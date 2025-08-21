package compomhp;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.EnumMap;
import java.util.Formatter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

import javafx.util.Pair;
import soot.ArrayType;
import soot.Body;
import soot.FastHierarchy;
import soot.Hierarchy;
import soot.Local;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.FieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.internal.JCastExpr;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JNopStmt;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.annotation.logic.Loop;
import soot.jimple.toolkits.annotation.logic.LoopFinder;
import soot.jimple.toolkits.thread.mhp.SynchObliviousMhpAnalysis;
import soot.options.Options;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.DominatorsFinder;
import soot.toolkits.graph.LoopNestTree;
import soot.toolkits.graph.MHGDominatorsFinder;
import soot.toolkits.graph.UnitGraph;
import soot.util.Chain;




public class Solver {
	private static Solver instance[] = new Solver[5];
	private static Solver dummyInst = new Solver();
	static int indSolver = 0;
	static boolean intPass=false;
	static {
		for(int i =0;i<instance.length;i++)
			instance[i] = new Solver();
	}
    private Solver() {
    	initialize();
    	
    	 
    	 /*
     	 * arrays are treated like objects with single virtual field.
     	 *  Assignment to any element of array, assigns to this field
     	 */
    	arrayRepClass = Scene.v().getSootClassUnsafe(ArrayRep.class.getName());
    	if(!arrayRepClass.declaresFieldByName("eleField")) {
     		arrayEleField = new SootField("eleField",RefType.v("java.lang.Object"), Modifier.PUBLIC);
     		arrayRepClass.addField(arrayEleField);
     	}
     	
//     	collectionRepClass.addField(collectionEleField);
     	
     	Local throwVar = new JimpleLocal("throwLocal",RefType.v("java.lang.Object"));
     	/*
    	 * a single local representing all thrown exceptions
    	 */
    	throwLs = new StmtLocal(null, throwVar);
//    	if(!methLocals.containsKey(main)) {
//    		methLocals.put(main, new HashSet<>());
//    	}
    	
    }
    
    public static Solver v() { 
    	if(intPass)
    	return dummyInst;
    	else
    		return instance[indSolver];}
    
    /*
     * Debugging
     */
    int memSkipped = 0;
int propSkipped = 0;
boolean extraPass = false;
Set<SootMethod> resolveDispatchList = new HashSet<>();
boolean print = false;
    SummaryChecks schk = new SummaryChecks();
    
    /*pts and MHP Maps (Result maps)*/
    Map<StmtLocal,BitSet> varPts = new ConcurrentHashMap<StmtLocal,BitSet>();
    Map<StmtAllocNodeField,BitSet> fieldPts = new ConcurrentHashMap<StmtAllocNodeField,BitSet>();
    Map<AllocNodeField,BitSet> ifieldPts = new HashMap<AllocNodeField,BitSet>();
    Map<Local,BitSet> ivarPts = new HashMap<Local,BitSet>();
    Map<SootField,BitSet> sfieldPts = new HashMap<SootField,BitSet>();
    Map<AllocNodeField,BitSet> afieldPts = new HashMap<AllocNodeField,BitSet>();
    Map<Stmt,BitSet> MHP = new HashMap<Stmt,BitSet>();
    Map<Stmt,BitSet> kill = new HashMap<>();
    Map<AllocNode,BitSet> notifyStmts = new HashMap<>();
    Object existCond = new Object();
    
    /*Utility maps*/
    
    /*store labels of statements in run method of ref*/
    Map<SootClass,BitSet> runStmts = new HashMap<SootClass,BitSet>(); 
    
    
    Map<SootClass,BitSet> runStmtsIP = new HashMap<SootClass,BitSet>(); 
    /* store statements in sync blocks which are synchronized on r*/ 
    Map<AllocNode,BitSet> sync = new HashMap<AllocNode,BitSet>(); 
    Map<AllocNode,BitSet> syncIP = new HashMap<AllocNode,BitSet>(); 
    
    
    
    /*returns the set of statements of the monitor block with leader s*/
    Map<Stmt,BitSet> monitorStmts = new HashMap<>();
    
    Map<Stmt,BitSet> invMonitorStmts = new HashMap<>();
    Map<Stmt,BitSet> invMethStmts = new HashMap<>();
    Map<SootMethod,BitSet> reachableFuncs = new HashMap<>();
    Map<SootMethod,Set<Stmt>> methStmts = new HashMap<>();
    Map<SootMethod,BitSet> methRep = new HashMap<>();
    Map<SootMethod,BitSet> mhpCopyTo = new HashMap<>();
    Map<SootMethod,BitSet> methRepHA;
    Map<SootMethod,BitSet> mhpCopyToHA;
    Map<Stmt,SootMethod> methOfRep = new HashMap<>();
    Map<SootMethod,Stmt> noPCMRep = new HashMap<>();
    Map<Stmt,BitSet> callSiteMeths = new HashMap<>();
    Map<SootMethod,BitSet> callSites = new HashMap<>();
    ArrayList<AllocNode> allocNodes = new ArrayList<AllocNode>();
    
    
    ArrayList<AllocNodeField> fieldList = new ArrayList<AllocNodeField>();
    Map<AllocNode,BitSet> fieldsOf = new HashMap<>();
    

    Map<Node,ArrayList<Constraint>> depCN = new HashMap<Node,ArrayList<Constraint>>();
    
    Map<Node,ArrayList<Node>> Edges = new HashMap<Node,ArrayList<Node>>();
    ArrayList<SootMethod> methList = new ArrayList<SootMethod>();
    Set<SootMethod> processed = new HashSet<SootMethod>();
    Set<SootMethod> hasPC = new HashSet<SootMethod>();
    ArrayList<Constraint> workList = new ArrayList<Constraint>();
   // Map<Local,SootMethod> myL = new HashMap<Local,SootMethod>();
    Map<SootMethod,Set<Local>> methLocals = new HashMap<>();
    Map<SootMethod,Map<Stmt,Map<Local,Set<Stmt>>>> methRDef = new HashMap<>();
    ArrayList<Stmt> stmtList = new ArrayList<Stmt>();
    Map<Unit,SootMethod> myS = new HashMap<Unit,SootMethod>();
    ArrayList<MHPMethodPair> pairs = new ArrayList<MHPMethodPair>();
    Map<MapName,Integer> mapBitSetType = new EnumMap<MapName,Integer>(MapName.class);
    Map<Object, Object> must = new HashMap<>();
    Map<Object, Object> cardOne = new HashMap<>();
    Map<Object, Object> exclField = new HashMap<>();
    Map<Object, Object> unionMap = new HashMap<>();
    
    Map<MapName, Map> mapForName = new EnumMap<MapName,Map>(MapName.class);
    ArrayList<Constraint> memCons = new ArrayList<Constraint>();
	ArrayList<Constraint> propCons = new ArrayList<Constraint>();
	ArrayList<Constraint> condCons = new ArrayList<Constraint>();
	ArrayList<Constraint> funCons = new ArrayList<Constraint>();
    ArrayList<Constraint> processLaterCons = new ArrayList<Constraint>();
	ArrayList<Constraint> laterFunc = new ArrayList<Constraint>();
	
	

	/*
	 * Maintain a map to handle fields and references set
	 */
   
    Map<SootMethod,BitSet> refFields = new HashMap<SootMethod,BitSet>();

    Map<Object,BitSet> staticFields = new HashMap<Object, BitSet>();
    Map<SootMethod,BitSet> methRet = new HashMap<SootMethod, BitSet>();
    Hierarchy h = Scene.v().getActiveHierarchy();
    ConcurrentHashMap<SootMethod,Set<EnterMonitorStmt>> synchStmts = new ConcurrentHashMap<>();
    Set<AllocNodeField> botRefFields = new HashSet<>();
    int removed = 0;
    
    
    Object fieldKey = new Object();
   
    static SootClass arrayRepClass;
	static SootField arrayEleField;
    
    StmtLocal throwLs;
   SolverUtil sUtil = new SolverUtil(); 

    /*
     * For bottom and escape support
     */
    AllocNode bottom;
    AllocNode nullRef;
    Map<Stmt,BitSet> escapeAt = new HashMap<>();
    Stmt mainFirstS;
    /*
     * Store the RHS of stores of the form x.f = y, if points-to of x has bottom.
     */
    Set<StmtLocal> bottomBases = new HashSet<>();
    Map<SootMethod,Stmt> skipped = new HashMap<>();
    int reAdded = 0;
    ConcurrentHashMap<SootMethod,Set<AssignStmt>> typeCasts = new ConcurrentHashMap<>();

    int fieldpcopycount = 0;
    int fieldpcopyskipcount = 0;
    long timeMHP=0L;
    long timefielPts=0L;
    int synchCount=0;
    Map<SootMethod,Map<Stmt,Set<Stmt>>> fieldIntStmts = new HashMap<>();
    Map<SootMethod,Map<Stmt,Set<Stmt>>> methMhpPred = new HashMap<>();
    Set<SootMethod> ignoredMeths = new HashSet<>();
    String aString = "";
    Set<StmtLocal> botLocals = new HashSet<>();
    Set<SootClass> clinitProcessed = new HashSet<>();
    long totalInvokes = 0;
    Solver solveriPoMHP;
    public void insert(Constraint c) {
//    	 if(c.name==ConstraintName.SYNC_END) {
//    		 System.out.println("stop");
//    	 }
    	c.insert();
    }
    
       
    public void propagateIt(Node sn, int bitPos) {

    	sUtil.propElemIter(sn, bitPos);

    }
   
    public void propagateToMHPFields(Node n, Stmt memSt) {
    	/*
    	 * memSt is added in MHP(keySt). 
    	 * If keySt is a store statement, its fieldPts should flow into memSt
    	 * if 
    	 */
    	Stmt keySt = (Stmt)n.key;
    	if(methOfRep.containsKey(keySt)) {
    		/*
    		 * This is a representative of a method
    		 */
    		SootMethod keyM = methOfRep.get(keySt);
    		Set<Stmt> keylsSet = loadStores.get(keyM);
    		if(methOfRep.containsKey(memSt)) {
    			SootMethod memM = methOfRep.get(keySt);
        		Set<Stmt> memlsSet = loadStores.get(memM);
        		if(keylsSet != null && memlsSet != null) {
	        		for(Stmt key : keylsSet) {
	        			for(Stmt mem : memlsSet) {
	        				propagateToMHPFields(key, mem, true);
	        			}
	        		}
        		}
    		}
    		else {
    			if(keylsSet != null) {
	    			for(Stmt key : keylsSet) {
	    				propagateToMHPFields(key, memSt, true);
	    			}
    			}
    		}
    	}
    	else {
    		if(methOfRep.containsKey(memSt)) {
    			SootMethod memM = methOfRep.get(memSt);
        		Set<Stmt> memlsSet = loadStores.get(memM);
        		if(memlsSet != null) {
	    			for(Stmt mem : memlsSet) {
	    				propagateToMHPFields(keySt, mem, true);
	    			}
        		}
        		
    		}
    		else {
    		
				propagateToMHPFields(keySt, memSt, true);
    			
    		}
    	}
    	
    	}
   public void propagateToMHPFields(Stmt keySt, Stmt memSt, boolean reflect) {
	   SootMethod keyM = myS.get(keySt);
	   SootMethod memM = myS.get(memSt);
	   MapName fieldMapkey = MapName.fieldPts;
	   MapName fieldMapMem = MapName.fieldPts;
	  
	   if(xMeths.contains(keyM)){
			   fieldMapkey = MapName.ifieldPts;
	   }
	   if(xMeths.contains(memM)){
		   fieldMapMem = MapName.ifieldPts;
   }
//	   if(prop) {
		   if(keySt instanceof AssignStmt && keySt.containsFieldRef() && memSt instanceof AssignStmt && memSt.containsFieldRef()) {
	   		AssignStmt asKey = (AssignStmt)keySt;
	   		AssignStmt asMem = (AssignStmt)memSt;
	   		
	   		SootField sfKey = keySt.getFieldRef().getField();
	   		SootField sfMem = memSt.getFieldRef().getField();
	   		
	   		if(!sfKey.isStatic() && sfKey == sfMem) {
	   			Value vlKey = asKey.getLeftOp();
	   	   		
	   	 
	   	   		Value vlMem = asMem.getLeftOp();
	   	   		
		   	   	if(!(vlKey instanceof JInstanceFieldRef) && !(vlMem instanceof JInstanceFieldRef)) {
		    		/*
		    		 * If both are only reads
		    		 */
		    		return;
		    	}
		   	   	else {
			   	   	Type t = sfKey.getType();
					if(t instanceof ArrayType) {
						t = ((ArrayType)t).baseType;
					}
					if(SimplifyUtil.isInterestingType(t)){
						if(vlKey instanceof JInstanceFieldRef) {
							/*
							 * If keySt is a write, propagate 
							 * fieldPts (either weak update or strong update, it will be present in fieldPts at keySt)
							 * from keySt to memSt
							 */
							if(!xMeths.contains(memM) ) {
							Local baseKey = (Local)((JInstanceFieldRef)vlKey).getBase();
				    		StmtLocal baseKeySt = new StmtLocal(keySt, baseKey);
							AllocNodeField keyAnf = new AllocNodeField(null,sfKey);
							Object keySanf = getFieldKey(keySt, keyAnf, fieldMapkey);
							Object memSanf = getFieldKey(memSt, keyAnf, fieldMapMem);
							PropagateConstraint fCopy = new PropagateConstraint(keySanf, memSanf, fieldMapkey, fieldMapMem, ConstType.depOnMhp);
							ConditionalConstraint cc = new ConditionalConstraint(baseKeySt, fCopy, MapName.varPts, null, ConstType.depOnMhp);
							cc.addToList();
							}
							
						}
						if(vlMem instanceof JInstanceFieldRef) {
							/*
							 * If memSt is a write, propagate fieldPts
							 * from memSt to keySt
							 */
							if(!xMeths.contains(keyM)) {
							Local baseMem = (Local)((JInstanceFieldRef)vlMem).getBase();
				    		StmtLocal baseMemSt = new StmtLocal(memSt, baseMem);
							AllocNodeField memAnf = new AllocNodeField(null,sfMem);
							Object memSanf = getFieldKey(memSt, memAnf, fieldMapMem);
							Object keySanf = getFieldKey(keySt, memAnf, fieldMapkey);
							PropagateConstraint fCopy = new PropagateConstraint(memSanf, keySanf, fieldMapMem, fieldMapkey, ConstType.depOnMhp);
							ConditionalConstraint cc = new ConditionalConstraint(baseMemSt, fCopy, MapName.varPts, null, ConstType.depOnMhp);
							cc.addToList();
							}
							
						}
					}
		   	   	}
	   		}
		   }
//	   }
   		
   		
   		
   		
   		
   }
   public Object getFieldKey(Stmt st, AllocNodeField anf, MapName fMap) {
	   Object key;
	   if(fMap == MapName.fieldPts) {
		   key = new StmtAllocNodeField(st, anf);
	   }
	   else {
		   key = anf;
	   }
	   return key;
   }

    public void propEsctoReachables(Node n, int bitPos) {
    	AllocNode an = allocNodes.get(bitPos);
    	Stmt st = (Stmt)n.key;
    	/*
    	 * add fieldPts(an,f,st) to escapeAt(st)
    	 */
    	SootClass sc = an.anclass;
		if(sc!=null) {
			Chain<SootField> ch = sc.getFields();
			Iterator<SootField> itr = ch.iterator();
			while(itr.hasNext()) {
				SootField sf = itr.next();
				if(!sf.isStatic()) {
					AllocNodeField anf = new AllocNodeField(an,sf);
					StmtAllocNodeField sanf = new StmtAllocNodeField(st,anf);
					PropagateConstraint dup  = new PropagateConstraint(sanf, st, MapName.fieldPts, MapName.escapeAt, ConstType.pts);
//					addField(anf, sanf.st);
					dup.addToList();
				}
			}
		}
    }
    public void addStaticFieldToEscape(Node n, int bitPos) {
    	AllocNode an = allocNodes.get(bitPos);
    	
    	/*
    	 * add the object O to escapeAt(st)
    	 * add fieldPts(an,f,st) to escapeAt(st)
    	 */
    	MemConstraint mc = new MemConstraint(an, mainFirstS, false, MapName.escapeAt, ConstType.pts);
    	mc.addToList();
    	
    	SootClass sc = an.anclass;
		if(sc!=null) {
			Chain<SootField> ch = sc.getFields();
			Iterator<SootField> itr = ch.iterator();
			while(itr.hasNext()) {
				SootField sf = itr.next();
				if(!sf.isStatic()) {
					AllocNodeField anf = new AllocNodeField(an,sf);
					StmtAllocNodeField sanf = new StmtAllocNodeField(mainFirstS,anf);
					PropagateConstraint dup  = new PropagateConstraint(sanf, mainFirstS, MapName.fieldPts, MapName.escapeAt, ConstType.pts);

					dup.addToList();
				}
			}
		}
    }
    
    
    public void solveDeps(Node n, int bitPos, BitSet bArray, boolean isBot) {
    	boolean propagate = true;
//    	if(n.diffSource) {
//			/*
//			 * In case if source node is difference map, 
//			 * propagate only if that bit is not set in the rightDiffMap
//			 */
//			BitSet rbs = getBitSetFor(n.rightDiffMap,n.rightDiffVar);
//			if(rbs.get(bitPos)) {
//				propagate = false;
//			}
//			
//		}
    	if(mapBitSetType.get(n.mapName) == 1) {
			Object obj = allocNodes.get(bitPos);
			if(obj==nullRef)
				propagate = false;
		}
    	ArrayList<Constraint> pl = null;
    	
		if(propagate) {
			if(depCN.containsKey(n)) {
				pl = depCN.get(n);
				
			}
			if( pl!= null) {
				Iterator<Constraint> itr = pl.iterator();
	    		while(itr.hasNext()) {
	    			Constraint ic = itr.next();
	    			ic = getDependentCons(ic, bArray, null);

	    			if(ic != null) {
	    				if(isBot) {
	    					if(ic instanceof FunctionalConstraint)
	    						insertConsForBit(bitPos,ic,n.mapName, getCardinality(n.mapName, bArray));
	    				}
	    				else
	    				insertConsForBit(bitPos,ic,n.mapName, getCardinality(n.mapName, bArray));
	    			}
	
	    		}
	    		
			}
		}
    }
    int getCardinality(MapName m, BitSet bArray){
    	int card = bArray.cardinality();
//    	if(mapBitSetType.get(m) == 1) {
//			if(bArray.get(1)) {
//				AllocNode an = allocNodes.get(1);
//				if(an==nullRef)
//					card= card -1;
//					
//			}
//		}
    	return card;
    }
    public boolean isCompatible(Node n, int bitPos) {
		boolean isCompatible = true;
		if(n.mapName == MapName.varPts || n.mapName == MapName.fieldPts || n.mapName == MapName.sfieldPts) {
			

			if(n.mapName == MapName.varPts) {
				StmtLocal ls = (StmtLocal)n.key;
				Local loc = ls.l;
				Type locType = loc.getType();
				String locC = null;
				if(locType instanceof RefType) {
					locC = ((RefType)locType).getClassName();
				}
				AllocNode ref = allocNodes.get(bitPos);
				if((arg.bot && ref == bottom) || ref == nullRef ) {
					isCompatible = true;
					return true;
				}
				Hierarchy h = Scene.v().getActiveHierarchy();
				if(ref != null && locC != null) {

					SootClass refClass = ref.anclass;
					SootClass locClass = Scene.v().getSootClass(locC);
					if(locClass.isInterface()) {
						List<SootClass> lst = h.getImplementersOf(locClass);
						
						if(!lst.isEmpty() && !lst.contains(refClass)) {
							isCompatible = false;
						}
					}
					else {
					if(refClass.resolvingLevel() != SootClass.DANGLING && refClass.isConcrete())
						isCompatible = h.isClassSubclassOfIncluding(refClass, locClass);

					}

				}
				
			
		}
		else {
			Type locType;
			if(n.mapName == MapName.fieldPts) {
				StmtAllocNodeField anfs = (StmtAllocNodeField)n.key;


				locType = anfs.anf.sf.getType();
			}
			else {
				SootField sf = (SootField)n.key;
				locType = sf.getType();
			}
			String locC = null;
			if(locType instanceof RefType) {
				locC = ((RefType)locType).getClassName();
			}
			AllocNode ref = allocNodes.get(bitPos);
			if((arg.bot && ref == bottom) || ref == nullRef) {
				isCompatible = true;
				return true;
			}
			Hierarchy h = Scene.v().getActiveHierarchy();
			if(ref != null && locC != null) {
				SootClass refClass = ref.anclass;
				SootClass locClass = Scene.v().getSootClass(locC);
				if(locClass.isInterface()) {
					List<SootClass> lst = h.getImplementersOf(locClass);
					if(!lst.contains(refClass)) {
						isCompatible = false;
					}
				}
				else {
					
				if(refClass.resolvingLevel() != SootClass.DANGLING && refClass.isConcrete())
					isCompatible = h.isClassSubclassOfIncluding(refClass, locClass);
					
				}

			}
			
			
		}
			
	}
		else if(n.mapName == MapName.ivarPts || n.mapName == MapName.ifieldPts) {
			if(n.mapName == MapName.ivarPts) {

				Local loc = (Local)n.key;
				Type locType = loc.getType();
				String locC = null;
				if(locType instanceof RefType) {
					locC = ((RefType)locType).getClassName();
				}
				AllocNode ref = allocNodes.get(bitPos);
				if((arg.bot && ref == bottom) || ref == nullRef) {
					isCompatible = true;
					return true;
				}
				Hierarchy h = Scene.v().getActiveHierarchy();
				if(ref != null && locC != null) {
					SootClass refClass = ref.anclass;
					SootClass locClass = Scene.v().getSootClass(locC);
					if(locClass.isInterface()) {
						List<SootClass> lst = h.getImplementersOf(locClass);
						if(!lst.contains(refClass)) {
							isCompatible = false;
						}
					}
					else {
					if(refClass.resolvingLevel() != SootClass.DANGLING && refClass.isConcrete())
						isCompatible = h.isClassSubclassOfIncluding(refClass, locClass);
					}

				}
				
			
				}
			else {
			Type locType;
				
					AllocNodeField anf = (AllocNodeField)n.key;
	
	
					locType = anf.sf.getType();
				
				String locC = null;
				if(locType instanceof RefType) {
					locC = ((RefType)locType).getClassName();
				}
				AllocNode ref = allocNodes.get(bitPos);
				if((arg.bot && ref == bottom) || ref == nullRef) {
					isCompatible = true;
					return true;
				}
				Hierarchy h = Scene.v().getActiveHierarchy();
				if(ref != null && locC != null) {
					SootClass refClass = ref.anclass;
					SootClass locClass = Scene.v().getSootClass(locC);
					if(locClass.isInterface()) {
						List<SootClass> lst = h.getImplementersOf(locClass);
						if(!lst.contains(refClass)) {
							isCompatible = false;
						}
					}
					else {
					if(refClass.resolvingLevel() != SootClass.DANGLING && refClass.isConcrete())
						isCompatible = h.isClassSubclassOfIncluding(refClass, locClass);
					}
				
				}
			}
			
		}
		return isCompatible;
	}
//    public ArrayList<Node> getEdges(Node n, int bitPos){
//    	boolean propagate = true;
//    	ArrayList<Node> edg = null;
//    	if(n.diffSource) {
//			/*
//			 * In case if source node is difference map, 
//			 * propagate only if that bit is not set in the rightDiffMap
//			 */
//			BitSet rbs = getBitSetFor(n.rightDiffMap,n.rightDiffVar);
//			if(rbs.get(bitPos)) {
//				propagate = false;
//			}
//			
//		}
//		if(propagate) {
//			edg = Edges.get(n);
//			
//		}
//		return edg;
//    }
		
    
    public int getBitSetSize(MapName mapName) {
    	
    	
    	int bit = mapBitSetType.get(mapName);
    	if(bit == 1)
    		return allocNodes.size();
    	else if(bit == 0)
    		return stmtList.size();
    	else if(bit == 2)
    		return fieldList.size(); 
    	else
    		return methList.size();
    }
    public BitSet getBitSetFor(MapName mapName, Object x) {
    	BitSet xArray = null;
		
			xArray = (BitSet)mapForName.get(mapName).get(x);
			

		
		/*
		 * Add if not present
		 */
		if(xArray == null)
			xArray = insertIntoMap(mapName,x);
		
		return xArray;
    }
    int solverInd;
    public void doOtherForResults() {
    	Solver.indSolver++;
    	solveriPoMHP = Solver.v(); 
    	solveriPoMHP.solverInd = indSolver;
    	Arg arg1 = new Arg();
    	arg1.combined = false;
		arg1.fs = false;
		arg1.mhp = true;
		SolverUtil.initSolverInstance(solveriPoMHP, arg1);
		solveriPoMHP.arg.genParallel = false;
		doExtraAnalysis(solveriPoMHP, null);
		Solver.indSolver++;
		solverPoMHP = Solver.v(); 
		solverPoMHP.solverInd = Solver.indSolver;
		Arg arg2=new Arg();
		arg2.combined = false;
		arg2.mhp = true;
		SolverUtil.initSolverInstance(solverPoMHP, arg2);
		solverPoMHP.arg.genParallel = false;
		doExtraAnalysis(solverPoMHP, null);
		Solver.indSolver = 0;
    }
    public void doExtraAnalysis( Solver solverNew, Solver prevSolver) {
    	System.out.println("Starting extra analysis: "+solverNew.aString);
		
		
		/*
		 * set arguments
		 */
		
    	solverNew.extraPass = true;
		if(solverNew.arg.usePrevMHP) {
			solverNew.MHP = prevSolver.MHP;
			solverNew.mapForName.put(MapName.MHP, prevSolver.MHP);
		}
		else if(solverNew.arg.usePrevP2) {
			solverNew.varPts = prevSolver.varPts;
			solverNew.mapForName.put(MapName.varPts, prevSolver.varPts);
			solverNew.fieldPts = prevSolver.fieldPts;
			solverNew.mapForName.put(MapName.fieldPts, prevSolver.fieldPts);
			solverNew.allocNodes = prevSolver.allocNodes;
			solverNew.methRepHA = prevSolver.methRep;
			
			solverNew.methOfRep = prevSolver.methOfRep;
			solverNew.bottom = prevSolver.bottom;
			solverNew.nullRef = prevSolver.nullRef;
		}
//		FunctionalConstraint fc = new FunctionalConstraint(ConstType.pts);
//		
//		fc.method = mainMethod;
//		
//		/*start execution from main method by adding its FunctionCallConstraint into worklist*/
//		
//		solverNew.workList.add(fc);
//		solverNew.main = mainMethod;
//		solverNew.callerStmts.put(mainMethod,new HashSet<>());
//		solverNew.callerStmts.get(mainMethod).add(new JNopStmt());
//		solverNew.sUtil.solver = solverNew;
//		CheckInteresting.solver = solverNew;
		File file = new File(path+"/tmp/tempPass"+solverNew.aString+".txt");
		PrintStream stdout = System.out;
	      //Instantiating the PrintStream class
	      try {
			PrintStream stream = new PrintStream(file);
			System.setOut(stream);
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
			try {
				solverNew.solve();
			} catch (InterruptedException | ExecutionException  |SecurityException | IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			finally {
				if(solverNew.pool != null)
				solverNew.pool.shutdown();
	    		
	    		try {
	    			if(solverNew.pool != null)
	    			solverNew.pool.awaitTermination(60, TimeUnit.SECONDS);
				} catch (InterruptedException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
			
			System.setOut(stdout);
			System.out.println("Done extra analysis: "+solverNew.aString);
	}
   private void doPoMHP2(Generator gen) throws SecurityException, IOException, InterruptedException, ExecutionException {
	   /*
	    *  perform PoMHP first
	    */
	   analyzer = new AnalyzerPoMHP();
		analyzer.init(gen, null);
		
		doAnalysis(gen);
		System.out.println("first round of PoMHP2 done");
		
		
		/*
		 * Use those MHP maps and perform PoA
		 * The field updates now should be flow-sensitive using the MHP maps
		 */
		Solver.indSolver++;
		Solver solverPoA = Solver.v();
		Arg newarg = new Arg();
		newarg.combined = false;
//		newarg.HA=true;
		newarg.mhp = false;
		newarg.usePrevMHP = true;
		solverPoA.arg=newarg;
		solverPoA.aString = "PoAPrevMHP";
		
		doExtraAnalysis(solverPoA, this);
		System.out.println("second round of PoMHP2 done");
		
		
		/*
		 * Now perform only mhp analysis using the points-to information
		 */
		Solver.indSolver++;
			Solver solverMHP = Solver.v();
			/*
			 * set arguments
			 */
			newarg = new Arg();
			newarg.combined = false;
			newarg.poa = false;
			newarg.usePrevP2 = true;
			solverMHP.arg=newarg;
			solverMHP.aString = "MHP";
			
			
			doExtraAnalysis(solverMHP,solverPoA);
			System.out.println("third round of PoMHP2 done");
			/*
			 * finally get the results maps
			 */
			MHP = solverMHP.MHP;
			mapForName.put(MapName.MHP, solverMHP.MHP);
			varPts = solverPoA.varPts;
			mapForName.put(MapName.varPts, solverPoA.varPts);
			fieldPts = solverPoA.fieldPts;
			mapForName.put(MapName.fieldPts, solverPoA.fieldPts);
			Solver.indSolver = 0;
			
   }

    private void doIterativeAnalysis(Generator gen) throws SecurityException, IOException, InterruptedException, ExecutionException {
    	/*
    	 * Perform PoMHP and store the constraints for points-to and MHP separately
    	 * so that they can be used to perform iterative Po, MHP analysis
    	 * Note that the maps will be reused
    	 */
    	analyzer = new AnalyzerPoMHP();
		analyzer.init(gen, null);
		//int round = 1;
		/*
		 * store the main functional constraint
		 */
		FunctionalConstraint mainFc = (FunctionalConstraint)workList.get(0); 
		do{
			iterRound++;
			iterChanges = 0;
			System.out.println("Starting round "+iterRound+" with worklist size"+workList.size());
			doAnalysis(gen);
			System.out.println("Changes after round completion"+iterChanges);

			workList.add(mainFc);
			analyzer = new AnalyzerComPoMHP();
			analyzer.init(gen, null);
		
		} while(iterChanges > 0);
		System.out.println("Stabilized after "+iterRound+" rounds");
//		printMethResults(main,false);
		
		
    }
    public void solve() throws SecurityException, IOException, InterruptedException, ExecutionException {
    	
    	
    	Generator gen = new Generator();
    	
    	/*
    	 * set argument for helper analysis
    	 */
    	
    	if(arg.bot) {
	    	
    		if(arg.combined) {
    			/*
    			 * In case if a helper analysis is already performed, we copy
    			 * both and all other refs from HA in the prepass. So no need to create bottom
    			 */
    			
    			performPrePassAndCopy();
    			
    		}
    		else if(!arg.usePrevP2){
	    		bottom = new AllocNode();	
	    		bottom.count = 0;
	    		nullRef = new AllocNode();
	    		nullRef.count = 1;
		    	allocNodes.add(bottom);
		    	allocNodes.add(nullRef);
		    	
				
    		}
    		/* 
	    	 * Add a bottom type allocNode
	    	 */
    		MapName fieldMap = MapName.ifieldPts;
			if(arg.combined)
				fieldMap = MapName.fieldPts;
	    	sUtil.addBotF = new MemConstraint(bottom, null, false,fieldMap, ConstType.pts);
	    	if(arg.combined)
	    		sUtil.addBotF.addBottoFields = true;
			AllocNodeField arrAnf = new AllocNodeField(null,Solver.arrayEleField);
			sUtil.addBotA = new MemConstraint(bottom, arrAnf, false,MapName.afieldPts, ConstType.pts);
			if(arg.combined)
				sUtil.addBotA.addBottoFields = true;
    		
    	}
    	if(arg.esc) {
    		Body b = getBody(main);
    		if(b!=null) {
    			mainFirstS = (Stmt)b.getUnits().getFirst();
    		}
    	}
    	
    	
    	/*
    	 * set the specific analyzer based on the given arguments
    	 * and perform the analysis
    	 */
    	
    	if(arg.iterative) {
    		/*
    		 * PoMHP - PoA followed by MHP
    		 */
    		System.out.println("Starting iterative run - PoA followed by MHP followed by PoA and so on");
    		aString = "iter";
    		doIterativeAnalysis(gen);
    		
    	}
    	else {
    		if(arg.pmhp2) {
        		System.out.println("Starting PoMHP square");
        		aString = "PoMHP2";
        		doPoMHP2(gen);
        	}
    		else if(arg.combined && arg.interleaved) {
	    		/*
	    		 * ComPoMHP
	    		 */
	    		System.out.println("Starting ComPoMHP");
	    		analyzer = new AnalyzerComPoMHP();
	    		aString = "ComPoMHP";
	    		analyzer.init(gen, null);
	    		
	    	}
	    	else if(arg.combined && !arg.interleaved) {
	    		/*
	    		 * niComPoMHP 
	    		 */
	    		System.out.println("Starting ComPoMHP non-interleaved");
	    		analyzer = new AnalyzerComPoMHP();
	    		aString = "niComPoMHP";
	    		analyzer.init(gen, null);
	    	}
	    	else if(arg.usePrevMHP && !arg.combined && arg.fs && arg.poa && !arg.mhp) {
	    		System.out.println("Starting PoA using previously computed MHP");
	    		analyzer = new AnalyzerPoA();
	    		aString = "PoAPrevMHP";
	    		analyzer.init(gen, null);
	    	}
	    	else if(arg.usePrevP2 && !arg.combined && !arg.poa && arg.mhp) {
	    		System.out.println("Starting MHP using previously computed Points-to");
	    		analyzer = new AnalyzerMHP();
	    		aString = "MHPPrevP2";
	    		analyzer.init(gen, null);
	    	}
	    	else if(!arg.interleaved && !arg.combined && arg.fs && arg.poa && !arg.mhp) {
	    		System.out.println("Starting PoA non-interleaved");
	    		analyzer = new AnalyzerPoA();
	    		aString = "niPoA";
	    		analyzer.init(gen, null);
	    	}
	    	else if(!arg.combined && arg.fs && arg.poa && !arg.mhp) {
	    		/*
	    		 * PoA - Only flow-sensitive points-to
	    		 */
	    		System.out.println("Starting PoA - Only flow-sensitive points-to");
	    		aString = "PoA";
	    		analyzer = new AnalyzerPoA();
	    		analyzer.init(gen, null);
	    	}
	    	else if(!arg.combined && !arg.fs && !arg.mhp && arg.poa) {
	    		/*
	    		 * iPoA - Only flow-insensitive points-to
	    		 */
	    		System.out.println("Starting iPoA - Only flow-insensitive points-to");
	    		aString = "iPoA";
	    		analyzer = new AnalyzeriPoA();
	    		analyzer.init(gen, null);
	    	}
	    	else if(!arg.combined && !arg.fs && arg.poa && arg.mhp) {
	    		/*
	    		 * iPoMHP - Flow-insensitive points-to analysis followed by MHP analysis
	    		 */
	    		System.out.println("Starting iPoMHP - Flow-insensitive points-to analysis followed by MHP analysis");
	    		aString = "iPoMHP";
	    		analyzer = new AnalyzeriPoMHP();
	    		analyzer.init(gen, null);
	    		
	    	}
	    	else if(!arg.combined && arg.fs && arg.poa && arg.mhp) {
	    		/*
	    		 * PoMHP - PoA followed by MHP
	    		 */
	    		System.out.println("Starting PoMHP - PoA followed by MHP");
	    		aString = "PoMHP";
	    		analyzer = new AnalyzerPoMHP();
	    		analyzer.init(gen, null);
	    		
	    	}
	    	doAnalysis(gen);

	    	/*
	    	 * print results if required
	    	 */
//	    	System.out.println("Nat:"+nat.size());
//	    	System.out.println("Nullnot nat"+natNotNull.size());
//	    	System.out.println("xml parse:"+xmlparse);
//	    	System.out.println("xml non parse"+xmlother);
	    	if(!intPass && !extraPass) {
//	    		printMethAllResults(null, main);
//	    		printMethAllResults("<examples.RecencyCheck2: void bar()>", null);
//	    		printRefFields(main);
//	    		printRefFields(Scene.v().getMethod("<microb.T: void run()>"));
//	    		printMethAllResults("<org.apache.commons.cli.Parser: org.apache.commons.cli.CommandLine parse(org.apache.commons.cli.Options,java.lang.String[])>", null);
//	    		printMethAllResults("<org.apache.commons.cli.PosixParser: java.lang.String[] flatten(org.apache.commons.cli.Options,java.lang.String[],boolean)>", null);
	    	}
//	    	if(intPass)
//	    	printMethAllResults("<org.apache.lucene.store.ChecksumIndexOutput: void prepareCommit()>",null);
    	}
    	
    }
    int printMethIndex=0;
    void printMethAllResults(String sig, SootMethod m) throws IOException {
    	if(sig!=null) {
		 	if(Scene.v().containsMethod(sig)) {
		 		m = Scene.v().getMethod(sig);
		 	
		 	}
    	}
    	if(m!=null) {
    		if(!arg.combined)
	    		printMethResults(m,true, printMethIndex);
	    		else
	    			printMethResults(m,false, printMethIndex);
    	}
    	printMethIndex++;
    }
    private void performPrePassAndCopy() {
    	HelperAnalysis.populateIntFieldsUsingPoA(arg.interleaved);
//		arg.HA=true;
		SimplifyUtil.solver = Solver.v();
		bottom = HelperAnalysis.solver.bottom;
		nullRef = HelperAnalysis.solver.nullRef;
		allocNodes = HelperAnalysis.solver.allocNodes;
		stmtList = HelperAnalysis.solver.stmtList;
		myS = HelperAnalysis.solver.myS;
		runStmtsIP = HelperAnalysis.solver.runStmtsIP;
		mapForName.put(MapName.runStmtsHA, runStmtsIP);
		syncIP = HelperAnalysis.solver.sync;
		mapForName.put(MapName.syncHA, syncIP);
//		monitorStmts = HelperAnalysis.solver.monitorStmts;
//		mapForName.put(MapName.monitorStmts, monitorStmts);
		methRepHA = HelperAnalysis.solver.methRep;
		mhpCopyToHA = HelperAnalysis.solver.mhpCopyTo;
		methOfRep = HelperAnalysis.solver.methOfRep;
		noPCMRep = HelperAnalysis.solver.noPCMRep;
    }
    public void addToWorkList(FunctionalConstraint fc) {
    	boolean ign = false;
//    	if(fc.caller != null)
//    		ign = ignoreMethod(fc.method, fc.caller.method);
//    	else
//    		ign = ignoreMethod(fc.method, null);
//    	if(!ign) {
    		workList.add(fc);
//    	}
    }
    public void addToWorkList(ArrayList<Constraint> fcList) {
    	for(Constraint c: fcList) {
    		FunctionalConstraint fc = (FunctionalConstraint)c;
//    		if(fc.method.getSignature().equals("<avrora.sim.AtmelInterpreter$IORegBehavior: int write(int,int)>")) {
//				  if(fc.caller.method.getSignature().equals("<avrora.sim.AtmelInterpreter: byte writeVolatile(int,byte)>"))
//				  System.out.println("caught");
//			  }
    		
    		addToWorkList(fc);
    	}
    }
    private Map<ConstType,ArrayList<Constraint>> initMap() {
    	Map<ConstType,ArrayList<Constraint>> map = new HashMap<>();
		map.put(ConstType.pts, new ArrayList<Constraint>());
		map.put(ConstType.depOnMhp, new ArrayList<Constraint>());
		map.put(ConstType.mhp, new ArrayList<Constraint>());
		map.put(ConstType.depOnPts, new ArrayList<Constraint>());
		return map;
    }
//    private void addBots() {
//    	for(StmtLocal sl: HelperAnalysis.botLocals) {
//    		MemConstraint m = new MemConstraint(bottom, sl, false, MapName.varPts, ConstType.pts);
//    		
//    		m.addToList();
//    	}
//    }
    private void doAnalysis(Generator gen) throws IOException, SecurityException, InterruptedException, ExecutionException {
    	cycles = 0;
    	genTime = 0L;
    	solveTime = 0L;
    	FileWriter fileWriter = null;
    	FileWriter fileWriterLib = null;
    	if(arg.callLog) {
    		fileWriter = new FileWriter(path+"/tmp/"+aString+"callLog_"+arg.bench+".txt");
    		fileWriterLib = new FileWriter(path+"/tmp/"+aString+"libCalls_"+arg.bench+".txt");
    		printWriter = new PrintWriter(fileWriter);
    		printWriterLib = new PrintWriter(fileWriterLib);
    	}
    	conscount = 0;
		memConsCount = 0;
		condConsCount = 0;
		propConsCount = 0;
		funConsCount = 0;
    	long startTime = System.nanoTime();
    	while(workList.size() > 0 || hasCons()) {
    		cycles++;
    		
    		
    		long elapsedTime = System.nanoTime() - startTime;
    		System.out.println("Starting cycle "+cycles+" worklist size "+workList.size()+"processed till now"+processed.size()+" lib count"+libCount+"total MHP time: "+timeMHP/1000000+"mSec"+" total field time: : "+timefielPts/1000000+"mSec"
    		+"total elapsed "+elapsedTime/1000000+"mSec");
    		/*
    		 * Generate constraints
    		 * Processes worklist and generates and adds constraints for all the methods
    		 * in the lists memCons,propCons etc...
    		 */
    		long genStart = System.nanoTime();
//    		if(arg.genParallel)
//    			genConstraintsP();
//    		else {
    			gen.analyzer = analyzer;
    			genConstraints(gen);
//    		}
    		long genT = (System.nanoTime() - genStart);
        	genTime+= genT;
        	
        	System.out.println("Generation done:"+genT/1000000+"mSec");
        	/*
    		 * Solve constraints
    		 * Remove constraints from lists memCons,propCons etc... and solve them
    		 * and may in-turn add new elements to worklist
    		 */
    		long solStart = System.nanoTime();
    		
    		if(!arg.interleaved)
    		 solvefunCons();
    		else {
    			solveConstr();  
    		}
    		long solT = (System.nanoTime() - solStart);
    		solveTime+= solT;
    		System.out.println("Solving done:"+solT/1000000+"mSec");
//    		System.out.println( "gen time :"+genT/1000000+" msec "+genT/1000000000+"sol time :"+solT/1000000+" msec "+solT/1000000000 );
//	    	solveLaterCons();

	    	totcons+=conscount;
	    	totmem+=memConsCount;
	    	totprop+=propConsCount;
	    	totcond+=condConsCount;
	    	totfunc+=funConsCount;
	    	
    	}
    	if(!arg.interleaved) {
    		int r = 1;
    		while(condCons.size()>0 || memCons.size()>0 || propCons.size()>0) {
    			if(funCons.size()>0) {
    				System.out.println("Found functional cons");
    			}
    			System.out.println("Round"+r++);
    		solveConstr();
    		}
    	}
    	if(arg.callLog) {
	    	printWriter.close();
	    	fileWriter.close();
	    	printWriterLib.close();
	    	fileWriterLib.close();
    	}
    	System.out.println("No of cycles : "+cycles);
    	System.out.println("Processed total :"+totcons+", member :"+totmem+", prop :"+totprop+", cond: "+totcond+", func: "+totfunc);
    }
    public boolean hasCons() {
    	boolean has = false;
    	if(arg.interleaved) {
	    	if(memCons.size()>0)
	    		has = true;
	    	else if(propCons.size() > 0)
	    		has = true;
	    	else if(condCons.size() > 0)
	    		has = true;
    	}
    	if(funCons.size() > 0)
    		has = true;
    	return has;
    }

    int remSynchs=0;
    Solver solverPoMHP;
    DoopUtil du = null;
    DoopUtil du2 = null;
    public void printResults() throws IOException {
//    	printProcessedSig();
    	if(arg.doopcode != 0) {
    		du = new DoopUtil(4);
    		du.compCallEdges();
	    	du.printInvCount();
//	    	countMonomorphic(callSiteMeths.keySet(), callSiteMeths, false);
	    	moreResults(typeCasts);
	    	du.compFailedCast();
	    	
	    	
	    	du2 = new DoopUtil(5);
    		du2.compCallEdges();
	    	du2.printInvCount();
	    	countMonomorphic(callSiteMeths.keySet(), callSiteMeths, false);
	    	moreResults(typeCasts);
	    	du2.compFailedCast();
	    	
    	}
    	else {
		GenConsMHP mhpConsGen = analyzer.mhpConsGen;
		GenConsPointsTo ptConsGen = analyzer.ptConsGen;
//    	countMHPPairs();
    	getBenchmarkProps();
    	if(ptConsGen!=null) {
	    	ptConsGen.countPtsInfo();
	    	ptConsGen.countCallEdges();
    	}
    	moreResults(typeCasts);
//    	printLds();
    	Set<Stmt> composet = countMonomorphic(callSiteMeths.keySet(), callSiteMeths, false);
    	Set<P> iprace = null;
		Set<P> prace = null ;
    	if(arg.combined && arg.interleaved) {
    		/*
    		 * get solvers for PoA and iPoA 
    		 */
    		printCountStrongStoreUpdate();
    		doOtherForResults();
    		/*
    		 * get monomorphic calls
    		 */
    		
    		indSolver = solverPoMHP.solverInd;
    		Set<Stmt> poSet = solverPoMHP.countMonomorphic(callSiteMeths.keySet(), callSiteMeths, true);
    		for(Stmt st: poSet) {
    			if(!composet.contains(st)) {
    				System.out.println("not found");
    				BitSet b = callSiteMeths.get(st);
    				BitSet b2 = solverPoMHP.callSiteMeths.get(st);
    				int i = b.nextSetBit(0);
    				while(i!=-1) {
    					SootMethod sm = methList.get(i);
    					System.out.println(sm.getSignature());
    					i = b.nextSetBit(i+1);
    				}
    				System.out.println("In b2");
    				i = b2.nextSetBit(0);
    				while(i!=-1) {
    					SootMethod sm = methList.get(i);
    					System.out.println(sm.getSignature());
    					i = b2.nextSetBit(i+1);
    				}
    			}
    		}
    		
    		indSolver = solveriPoMHP.solverInd;
    		Set<Stmt> ipoSet = solveriPoMHP.countMonomorphic(callSiteMeths.keySet(), callSiteMeths, true);

    		/*
    		 * get removable casts
    		 */
    		if(arg.doopcode==0)
    		indSolver = 0;
//    		moreResults(typeCasts);
    		if(arg.bench.equals("h2")||arg.bench.equals("fop")) {
    			indSolver = solverPoMHP.solverInd;
    			solverPoMHP.moreResults(solverPoMHP.typeCasts);
    			
    			indSolver = solveriPoMHP.solverInd;
        		solveriPoMHP.moreResults(solveriPoMHP.typeCasts);
    		}
    		else {
    			indSolver = solverPoMHP.solverInd;
    			solverPoMHP.moreResults(typeCasts);
    			
    			indSolver = solveriPoMHP.solverInd;
    			solveriPoMHP.moreResults(typeCasts);
    		}
    		/*
    		 * get removable synchs
    		 */
    		indSolver = 0;
    		getRemSynchs(synchStmts.keySet());
    		
    		indSolver = solverPoMHP.solverInd;
    		solverPoMHP.getRemSynchs(synchStmts.keySet());
    		
    		indSolver = solveriPoMHP.solverInd;
    		solveriPoMHP.getRemSynchs(synchStmts.keySet());
    		
    		indSolver = solverPoMHP.solverInd;
    		solverPoMHP.countMHPPairs();
//    		
    		indSolver = solverPoMHP.solverInd;
    		solveriPoMHP.countMHPPairs();
    		iprace = solveriPoMHP.raceSet;
    		prace = solverPoMHP.raceSet;
    		indSolver = 0;
    		ptConsGen.findPtDiff(solverPoMHP,solveriPoMHP);
    		
    	}
    	if(!arg.combined)
    	getRemSynchs(synchStmts.keySet());
    	countMHPPairs();

    	
    	}
    	
    	
    	
    	
    	
//    	countStrongUpdates();
    	
    	
//    	
//    	findls();
//    	printIgnored();
//    	writeBotCount();
//    	runTimeCallGs(arg.bench);
//    	printRefFields();
//    	TimeDiv.printCsv();
//    	printProcessed();
		//printMethodMhp();
		//printSynchObliviousMethodMhp();
		//printSynchObliviousMhpAll();
		//printTails();
		//printAllocNodes();
		//printWaitCall();
		//printWaitSucc();
		//printSyncMap();
		//printAddToSync();
//		printStmts();
		//printAllocNodes();
		//printMonitorStmt();
		//printMonitorSet();
//		printPendingC();
//		printFieldPtsHash();
    }
    
    
    
    
    int strongStore = 0;
    int notStrongStore=0;
    void printCountStrongStoreUpdate() throws IOException {
    	Set<Constraint> solvedCons = ConditionalConstraint.storeSolvedCons;
    	Map<Constraint, Constraint> m = ConditionalConstraint.conElseCon;
    	for(Constraint c: solvedCons) {
    		if(m.containsKey(c)) {
    			Constraint elseC = m.get(c);
    			if(!solvedCons.contains(elseC)) {
    				strongStore++;
    			}
    			else {
    				notStrongStore++;
    			}
    		}
    		else {
    			notStrongStore++;
    		}
    	}
    	System.out.println("Strong stores: "+strongStore+"Not Strong stores: "+notStrongStore+" total solved cons: "+solvedCons.size());
    	File f = new File(path+"/tmp/stronStores.txt");
    	boolean exist = true;
    	if(!f.exists())
			exist = false;
    	FileWriter fileWriter = new FileWriter(f,true);
    	BufferedWriter br = new BufferedWriter(fileWriter);
		PrintWriter printWriter = new PrintWriter(br);
		
		if(!exist) {
			
			printWriter.print("Benchmark,TotalStores,strongUpdates,allocsinLoop,cardNotOne,allAllocsInLoop");
			
		}
		printWriter.println();
		printWriter.print(arg.bench+","+(strongStore+notStrongStore)+","+strongStore+","+schk.allocsInLoop.size()+","+ConditionalConstraint.notStrongduetoCardinality.size()+","+allAllocsInLoop.size());
		printWriter.close();
		br.close();
		fileWriter.close();
    }
    
    
    public Set<Stmt> countMonomorphic(Set<Stmt> callSites, Map<Stmt,BitSet> callSiteMeths1, boolean fromCombined) {
    	return countByCallSites(callSites, callSiteMeths1, fromCombined);
    }
    private Set<Stmt> countByCallSites(Set<Stmt> callSites, Map<Stmt,BitSet> callSiteMeths1, boolean fromCombined) {
//		Set<Stmt> callSites = this.solver.callSiteMeths.keySet();
		Set<Stmt> monoCallSites = new HashSet<>();
		monomorphicCount = 0;
		for(Stmt st: callSites) {
//			InvokeExpr ie = st.getInvokeExpr();
//			if(ie instanceof VirtualInvokeExpr || ie instanceof InterfaceInvokeExpr) {
//				Local l = (Local)((InstanceInvokeExpr)ie).getBase();
//				BitSet bl = null;
//				if(arg.fs) {
//					bl = getVarPts(l, st);
//					
//				}
//				else {
//					bl = ivarPts.get(l);
//				}
//				if(bl != null) {
//					
//					if(bl.cardinality()==1 /*&& !bl.get(0)*/) {
//						monomorphicCount++;
//					}
//				}
//			}
			InvokeExpr ie = st.getInvokeExpr();
//			if(ie instanceof InstanceInvokeExpr) {
				BitSet br = callSiteMeths.get(st);
				if(fromCombined) {
					BitSet br2 = callSiteMeths1.get(st);
					if(br2==null || br2.cardinality() == 0) {
						continue;
					}
				}
				
				if(br!=null && br.cardinality()==1) {
					
					int i = br.nextSetBit(0);
					SootMethod sm = methList.get(i);
					if(!sm.isStatic()) {
						monoCallSites.add(st);
						monomorphicCount++;
					}
				}
//			}
			
			
		}
//		sol.monoPercent = (sol.monomorphicCount/sol.callEdgeCount)*100 ;
		System.out.println(" monomorphic of "+aString+": "+monomorphicCount);
		return monoCallSites;
	}
    
    
    private void findDiff() {
    	int ifp = HelperAnalysis.solver.processed.size();
    	int cp = processed.size();
    	System.out.println("int field processed:"+ifp);
    	System.out.println("ComPo processed:"+cp);
    	if(cp > ifp) {
    		Set<SootMethod> diff = new HashSet<>(processed);
    		diff.removeAll(HelperAnalysis.solver.processed);
    		System.out.println("difference count:"+diff.size());
    		System.out.println(diff);
    	}
    }

    
    public void getBenchmarkProps() throws IOException {
    	if(aString.equals("PoMHP")) {
    	File f = new File(path+"/tmp/"+arg.bench+"properties.txt");
    	synchCount = 0;
//    	System.out.println("Started countSyncs with entry set:"+synchCount);
    	int sCount=0;
    	int jCount=0;
    	int wCount=0;
    	int nCount=0;
    	int eCount=0;
    	int upd=0;
    	boolean exist = true;
    	if(!f.exists())
			exist = false;
    	FileWriter fileWriter = new FileWriter(f,true);
    	BufferedWriter br = new BufferedWriter(fileWriter);
		PrintWriter printWriter = new PrintWriter(br);
		if(!exist)
			printWriter.print("Benchmark,synchCount,starts,joins,runs,waits,notifys,exec,runorcall");
		printWriter.println();
//		int count=0;
		for(Map.Entry<SootMethod, Set<EnterMonitorStmt>> ele : synchStmts.entrySet()) {
			synchCount+=ele.getValue().size();
		}
		for(Map.Entry<SootMethod, Set<Stmt>> ele : starts.entrySet()) {
			sCount+=ele.getValue().size();
		}
		for(Map.Entry<SootMethod, Set<Stmt>> ele : joins.entrySet()) {
			jCount+=ele.getValue().size();
		}
		for(Map.Entry<SootMethod, Set<Stmt>> ele : waits.entrySet()) {
			wCount+=ele.getValue().size();
		}
		for(Map.Entry<SootMethod, Set<Stmt>> ele : notifys.entrySet()) {
			nCount+=ele.getValue().size();
		}
		for(Map.Entry<SootMethod, Set<Stmt>> ele : execSubmits.entrySet()) {
			eCount+=ele.getValue().size();
		}
//		for(Map.Entry<Node, Set<Integer>> ele : mustUpdated.entrySet()) {
//			if(ele.getValue().size() > 1)
//				upd++;
//		}
		System.out.println("Benchmark :"+arg.bench+",synchCount: "+synchCount+",starts :"+sCount+",joins :"+jCount+",runs :"+runs.size()+",waits :"+wCount+",notifys :"+nCount+",execs :"+eCount+",runOrCall :"+runOrCall.size());
		printWriter.print(arg.bench+","+synchCount+","+sCount+","+jCount+","+runs.size()+","+wCount+","+nCount+","+eCount+","+runOrCall.size());
		printWriter.close();
    	fileWriter.close();
    	}
    }
   // int remPointsSynch = 0;
    Set<Pair<EnterMonitorStmt,EnterMonitorStmt>> mps = new HashSet<>();
    int synchPar=0;
    public int getRemSynchs(Set<SootMethod> mSet) {
    	/*
    	 * A synch can be removed if it does not run in parallel with any other sync and if they run in parallel,
    	 * if the lock objects points-to sets doesn't overlap
    	 * 
    	 */
    	System.out.println("Started removable synchs count in "+aString);
    	//int totalSynch = 0;
    	Set<EnterMonitorStmt> remSet = new HashSet<>();
    	Set<EnterMonitorStmt> noMHPSet = new HashSet<>();
    	Set<EnterMonitorStmt> noPtsMHPSet = new HashSet<>();
    	

		for(Map.Entry<SootMethod, Set<EnterMonitorStmt>> ele : synchStmts.entrySet()) {
			
			
			if(mSet.contains(ele.getKey())){
				
			Set<EnterMonitorStmt> mSynchs = ele.getValue();

			for(EnterMonitorStmt st : mSynchs) {
				System.out.println("Processing "+st.toString()+" from "+myS.get(st).getSignature());
			Local l = (Local)st.getOp();
			int j = stmtList.indexOf(st);
			BitSet pt;
			pt = getVarPts(l,st);

				if(MHP.containsKey(st)) {
					BitSet b = MHP.get(st);
					int c = b.cardinality();
		    		int i = b.nextSetBit(0);
		    		boolean synchParFound = false;
					while(i!=-1) {
						Stmt s = stmtList.get(i);
//						System.out.println(s);
						if(s instanceof EnterMonitorStmt) {
							EnterMonitorStmt em2 = (EnterMonitorStmt)s;
							Local l2 = (Local)em2.getOp();
							
							BitSet pt2;
							pt2 = getVarPts(l2, em2);
							boolean hasIntr = hasIntr(pt,pt2,l.getType(), l2.getType());
							if(hasIntr) {
								System.out.println("Found par synch "+s.toString()+" from "+myS.get(s).getSignature());
								synchParFound = true;
								break;
							}
							
						}
						i = b.nextSetBit(i+1);
					}
//					System.out.println("}");
					if(!synchParFound) {
						/*
						 * If there is no parallely running sync, it can be removed
						 */
						remSet.add(st);
					}
					
					
				}
				else {
					noMHPSet.add(st);
				}
			}
		}
		}

		remSynchs = remSet.size();
		for(EnterMonitorStmt st: remSet) {
			System.out.println(st.toString()+" from "+myS.get(st).getSignature());
			Local l2 = (Local)st.getOp();
			
			BitSet pt2;
			pt2 = getVarPts(l2, st);
			System.out.println(pt2.toString());
			
		}
		System.out.println(aString+" Rem synchs"+remSynchs);
		return remSynchs;
    }
   private boolean hasIntr(BitSet b1, BitSet b2, Type t1, Type t2){
    	boolean hasIntr = false;
    	if(b1==null || b2==null || b1.isEmpty() || b2.isEmpty()) {
    		return hasIntr;
    	}
    	/*
		 * If the bitsets overlap and
		 * the overlap is only bot, don't consider it as overlap
		 * unless types are compatible
		 */
    	BitSet intr = (BitSet)b1.clone();
		intr.and(b2);
		if(intr.get(0) && intr.cardinality()==1) {
			
			FastHierarchy fh = Scene.v().getFastHierarchy();
			if(t1 instanceof RefType && t2 instanceof RefType) {
				if(fh.canStoreType(t1, t2) || fh.canStoreType(t2, t1)) {
					
					hasIntr = true;
				}
			}
			
		}
		else if(intr.cardinality() > 0) {
			hasIntr = true;
		}
			
    	return hasIntr;
    }
   
    int removableCasts = 0;
	int failedCasts = 0;
	int totalCasts=0;
	Map<SootMethod, Set<AssignStmt>> fcast = new HashMap<>();
    public void moreResults(Map<SootMethod,Set<AssignStmt>> typeCasts) {
    	/*
    	 * A cast can be removed if all the references flowing into casted var
    	 * are of compatible type as that of destination
    	 */
    	/*
    	 * A cast is failed if there is a possibility of a non-compatible ref flowing into 
    	 * the casted var
    	 */
    	failedCasts = 0;
    	h = Scene.v().getActiveHierarchy();
    	for(Map.Entry<SootMethod, Set<AssignStmt>> ele: typeCasts.entrySet()) {
    		totalCasts+=ele.getValue().size();
    		for(AssignStmt cast: ele.getValue()) {
    			JCastExpr ce = (JCastExpr)cast.getRightOp();
    			Type t = ce.getCastType();
    			if(t instanceof ArrayType) {
    				t = ((ArrayType)t).baseType;
    			}
    			RefType rt = (RefType)t;
    			Local l = (Local)ce.getOp();
    			Object sl = analyzer.ptConsGen.getKey(cast,l);
    			Map varM = mapForName.get(analyzer.ptConsGen.varMap);
    			boolean rc = true;
				boolean fc = false;
    			if(varM.containsKey(sl)) {
    				BitSet b = (BitSet)varM.get(sl);
    				if(b.cardinality()>0) {
    				int i = b.nextSetBit(0);
    				
    				while(i!=-1) {
    					AllocNode an = allocNodes.get(i);
    					if(an.anclass != null) {
//    						boolean lrc = true;
    						/*
    						 * if any one of the 
    						 */
	    					if(! an.anclass.getName().equals( rt.getSootClass().getName())) {
	    						rc = false;
	    					}
	    					SootClass refClass = an.anclass;
	    					SootClass castClass = rt.getSootClass();
	    					if(castClass.isInterface()) {
	    						List<SootClass> lst = h.getImplementersOf(castClass);
	    						if(!lst.contains(refClass)) {
	    							fc = true;
	    						}
	    					}
	    					else {
		    					if(refClass.resolvingLevel() != SootClass.DANGLING && refClass.isConcrete()) {
		    						
		    						boolean isSub = h.isClassSubclassOfIncluding(refClass, castClass);
		    						if(!isSub)
		    							fc  = true;
		    					}
	    					}
//	    					if(!lrc) {
//	    						rc = false;
//	    						fc = true;
//	    					}
	    					
    					}
    					i = b.nextSetBit(i+1);
    				}
    				if(rc && !b.get(0)) {
    					boolean nr = false;
    					if(arg.combined) {
    						if(HelperAnalysis.botLocals.contains(sl)) {
    							nr = true;
    						}
    					}
    					if(!nr)
        				removableCasts++;
    				}
    				if(fc)
    				{
    					if(!fcast.containsKey(ele.getKey())) {
    						fcast.put(ele.getKey(), new HashSet<>());
    					}
    					fcast.get(ele.getKey()).add(cast);
    					failedCasts++;
    				}
    				if(rc && fc) {
    					System.out.println("error");
    				}
    				}
    			}
    				
    			}
    			
    			
    		}
    	
    	System.out.println("====Removable casts for "+aString+": "+removableCasts+"failed casts: "+failedCasts+"total casts: "+totalCasts);
//    	for(Map.Entry<SootMethod,Set<AssignStmt>> e: fcast.entrySet()) {
//    		System.out.println("In method:"+e.getKey().getSignature()+" size: "+e.getValue().size());
//    		
//    	}
    }
    
    public void solveConstr() {
    	
    	conscount+=memCons.size();
    	memConsCount+=memCons.size();
//    	if(cycles==30) {
//    		System.out.println("Starting to solve mem size"+memCons.size());
//    	}
    	TimeDiv.reset();
    	while(memCons.size() > 0) {
    		Constraint c = memCons.remove(0);
//    		if(c.name==ConstraintName.METHOD_CALL) {
//    			System.out.println("yes");
//    		}
    		long start = System.nanoTime();
    		insert(c);
    		long end = System.nanoTime() - start;
    		TimeDiv.noteTime(((MemConstraint)c).destMap, end);
    	}
    	TimeDiv.printTime("memCons",cycles);
//    	if(cycles==30) {
//    		System.out.println("Done mems");
//    	}
    	//memCons.clear();
    	//Iterator<PropagateConstraint> pitr = propCons.iterator();
    	conscount+=propCons.size();
    	propConsCount+=propCons.size();
//    	System.out.println("Done mem cons");
//    	int pco = 0;
//    	if(cycles==30) {
//    		System.out.println("Starting to solve prop size"+propCons.size());
//    	}
    	TimeDiv.reset();
    	while(propCons.size() > 0) {
    		
    		Constraint c = propCons.remove(0);
//    		if(cycles==19 && pco == 118780) {
//    			System.out.println("Stop");
//    		}
//    		if(cycles==28) {
//        		System.out.println("Insert"+pco+++" "+((PropagateConstraint)c).leftMap+"("+((PropagateConstraint)c).left+")"+"->"+((PropagateConstraint)c).rightMap+"("+((PropagateConstraint)c).right+")");
//        		if(((PropagateConstraint)c).leftMap==MapName.methStmts && ((PropagateConstraint)c).rightMap==MapName.monitorStmts){
//        			if(((PropagateConstraint)c).left.toString().equals("<org.apache.xml.serializer.ToSAXHandler: void setContentHandler(org.xml.sax.ContentHandler)>") && 
//        					((PropagateConstraint)c).right.toString().equals("entermonitor r0")) {
//        				System.out.println("Caught");
//        			}
//        		}
//    		}
    		long start = System.nanoTime();
//if(arg.callLog && (cycles==35)) {
//	PropagateConstraint p = (PropagateConstraint)c;
//	if(p.leftMap==MapName.varPts){
//		if(((StmtLocal)p.left).st.toString().equals("specialinvoke r0.<avrora.arch.legacy.LegacyInstr: void <init>(avrora.arch.legacy.LegacyInstrProperties)>(r1)") &&
//				((StmtLocal)p.right).st.toString().equals("r0 := @this: avrora.arch.legacy.LegacyInstr")) {
//			rec = 1;
//		}
//		
//	}
//}
    		
    		insert(c);  
//    		if(rec==1) {
//    			rec=0;
//    		}
    		long end = System.nanoTime() - start;
    		
    			
    			
    		TimeDiv.noteTime(((PropagateConstraint)c).leftMap, end);
    		
    		
    	}
    	TimeDiv.printTime("propCons",cycles);
    	//propCons.clear();
    	//Iterator<ConditionalConstraint> citr = condCons.iterator();
//    	if(cycles==30) {
//    		System.out.println("Done props");
//    	}
    	conscount+=condCons.size();
    	condConsCount+=condCons.size();
//    	System.out.println("Done prop cons");
    	TimeDiv.reset();
    	while(condCons.size() > 0) {
    		Constraint c = condCons.remove(0);
//    		if(cycles==30) {
//        		System.out.println("Insert"+pco+++" "+((ConditionalConstraint)c).mapType+"("+((ConditionalConstraint)c).condVariable+")"+"->");
//        		if(((ConditionalConstraint)c).mapType==MapName.refFields && ((ConditionalConstraint)c).condVariable.toString().equals("$r1 = r0.<org.dacapo.harness.TeeOutputStream: java.io.OutputStream log>")) {
//        			System.out.println("Caught");
//        			print = true;
//        		}
//    		}
    		long start = System.nanoTime();
    		insert(c);  
    		long end = System.nanoTime() - start;
    		TimeDiv.noteTime(((ConditionalConstraint)c).mapType, end);
    		
    	}
    	TimeDiv.printTime("condCons",cycles);
    	//condCons.clear();
    	
    	solvefunCons();
    	
//    	System.out.println("Done cond cons");
    	
//    	if(!arg.interleaved) {
//    		ArrayList<Constraint> funConscopy = new ArrayList<Constraint>(funCons);
//    		for(Constraint fc : funConscopy) {
//        		if(((FunctionalConstraint)fc).useCHA) {
//        			funCons.remove(fc);
//        			insert(fc);
//        		}
//        		
//        	}
//    	}
    	
    }
    public void solvefunCons() {
    	if(funCons.size()>0) {
    		conscount+=funCons.size();
    	funConsCount+=funCons.size();
    	addToWorkList(funCons);
    	funCons.clear();
    	}
    }
    public void printMhp() throws IOException {
    	
//    	FileWriter fileWriter = new FileWriter(path+"/tmp/"+"MhpResult.txt");
		PrintWriter printWriter = new PrintWriter(System.out);
    	printWriter.println("Mhp result ");
    	String st = String.format("%1$-60s %2$-60s %3$-80s\n", "Stmt", "Method","MHP result");
    	printWriter.println(st);
    	for(Map.Entry<Stmt,BitSet> ele : MHP.entrySet()) {
    		Stmt v = ele.getKey();
    		BitSet b = ele.getValue();
    		int i = b.nextSetBit(0);
    		StringBuilder sb = new StringBuilder();
			while(i!=-1) {
				Unit s = stmtList.get(i);
				sb.append(s+"\n");
				i = b.nextSetBit(i+1);
			}
			if(!sb.toString().equals("")) {
				
				String st1 = String.format("%1$-60s %2$-60s %3$-80s\n", v, myS.get(v).getSignature(),"{"+sb.toString()+"}");
				printWriter.println(st1);
				
				
			}
    	}
    	printWriter.close();
//    	fileWriter.close();
    }
public void printStrongUpdates() throws IOException {
    	
    	FileWriter fileWriter = new FileWriter(path+"/tmp/"+"/strongUpdates.txt");
		PrintWriter printWriter = new PrintWriter(fileWriter);
		for(Map.Entry<SootMethod,Set<Stmt>> ele : loadStores.entrySet()) {
			SootMethod sm = ele.getKey();
			printWriter.println("Method:"+sm.getSignature());
			Set<Stmt> stmts = ele.getValue();
			for(Stmt st : stmts) {
				boolean strong = true;
				if(MHP.containsKey(st)) {
					BitSet bs = MHP.get(st);
					if(bs.cardinality() >= 1) {
						strong = false;
					}
				}
				if(strong)
					printWriter.println(st);
			}
		}
    	printWriter.close();
    	fileWriter.close();
    }
    public void appendOutput(String benchmarkName,long genTms, long genTs, long solveTms, long solveTs,long timeMs, long timeS, int nonLibMethods) throws IOException {
    	String filename = aString+"result.txt";
    	
    	File f = new File(path+"/tmp/"+filename);
    	boolean exist = true;
    	if(!f.exists())
			exist = false;
    	FileWriter fileWriter = new FileWriter(f,true);
    	BufferedWriter br = new BufferedWriter(fileWriter);
		PrintWriter printWriter = new PrintWriter(br);
		
		if(!exist) {
			if(arg.combined && arg.interleaved ) {
			printWriter.print("Benchmark,GenTime,SolveTime,nonLibMethods,TotalTime,Points-toCount,Monomorphic,MonomorphicPoA,MonomorphiciPoA,CallgraphEdges,MHP Pairs,Rounds,failedCasts,failedCastsPoA,failedCastsiPoA,removableCasts,removableCastsPoA,removableCastsiPoA,"
					+ "TotalCasts,removableSynchs,removableSynchsPoA,removableSynchsiPoA,synchPar,totalCons"+",condCons,memCons,funcCons,propCons,MHPPo,MHPiPo,PR,PRPo,PRiPo"
					
					);
			if(arg.suite.equalsIgnoreCase("extra")) {
	    		printWriter.print(",mainClass");
	    	}
			}
			else {
				printWriter.print("Benchmark,GenTime,SolveTime,nonLibMethods,TotalTime,Points-toCount,Monomorphic,CallgraphEdges,MHP Pairs,Rounds,failedCasts,removableCasts,"
						+ "TotalCasts,removableSynchs,synchPar,totalCons"+",condCons,memCons,funcCons,propCons,MHP Pairs,PR"
						);
				if(arg.suite.equalsIgnoreCase("extra")) {
		    		printWriter.print(",mainClass");
		    	}
			}
		}
		printWriter.println();
		if(arg.combined && arg.interleaved) {
		printWriter.print(benchmarkName+","+genTms+","+solveTms+","+nonLibMethods+","+timeMs+","+pointCount+","+monomorphicCount+","+solverPoMHP.monomorphicCount+","+solveriPoMHP.monomorphicCount+","+
		
				callEdgeCount+","+MHPCount+","+iterRound+","+failedCasts+","+solverPoMHP.failedCasts+","+solveriPoMHP.failedCasts+","+removableCasts+","+solverPoMHP.removableCasts+","+solveriPoMHP.removableCasts+","+
				typeCasts.size()+","+remSynchs+","+solverPoMHP.remSynchs+","+solveriPoMHP.remSynchs+","+
				synchPar+","+conscount+","+condConsCount+","+memConsCount+","+funConsCount+","+propConsCount+","+solverPoMHP.MHPCount+","+solveriPoMHP.MHPCount+","+possibleRaces+","+solverPoMHP.possibleRaces+","+solveriPoMHP.possibleRaces
				);
		if(arg.suite.equalsIgnoreCase("extra")) {
    		printWriter.print(","+arg.mainclass);
    	}
		}
		else {
			printWriter.print(benchmarkName+","+genTms+","+solveTms+","+nonLibMethods+","+timeMs+","+pointCount+","+monomorphicCount+","+
					
				callEdgeCount+","+MHPCount+","+iterRound+","+failedCasts+","+removableCasts+","+
				typeCasts.size()+","+remSynchs+","+
				synchPar+","+conscount+","+condConsCount+","+memConsCount+","+funConsCount+","+propConsCount+","+MHPCount+","+possibleRaces);
			if(arg.suite.equalsIgnoreCase("extra")) {
	    		printWriter.print(","+arg.mainclass);
	    	}
		}
		printWriter.close();
		br.close();
		fileWriter.close();
    }
//    public void performSymmetry() {
//    	Map<Stmt,BitSet> MHPCopy = new HashMap<Stmt,BitSet>(MHP);
////    	System.out.println("Started count pairs with entry set:"+MHP.entrySet().size());
//    	//int expCount =0;
////    	for(Map.Entry<Stmt,BitSet> ele : MHP.entrySet()) {
////    		Stmt keyst = ele.getKey();
////    		BitSet b = ele.getValue();
////    		System.out.println(keyst+" from "+myS.get(keyst)+ " MHP: "+b);
////    	}
//    	for(Map.Entry<Stmt,BitSet> ele : MHPCopy.entrySet()) {
//    		Stmt keyst = ele.getKey();
//    		BitSet b = ele.getValue();
//    		int keystPos = stmtList.indexOf(keyst);
//    		
//    		int memstPos = b.nextSetBit(0);
//			while(memstPos!=-1) {
//				Stmt memSt = stmtList.get(memstPos);
//				if(!MHPCopy.containsKey(memSt)) {
//					//MHPCopy.put(memSt, new BitSet());
//					sUtil.propagateElem(new Node(MapName.MHP,memSt),keystPos);
//				}
//				else {
//				BitSet b1 = MHPCopy.get(memSt);
//					if(!b1.get(keystPos)) {
//						sUtil.propagateElem(new Node(MapName.MHP,memSt),keystPos);
//					}
//				}
//				memstPos = b.nextSetBit(memstPos+1);
//	    	}
//			
//    		
//    	}
//    }
    void printLds() {
    	for(Map.Entry<SootMethod, Set<Stmt>> ele: loadStores.entrySet()) {
    		File f = new File(path+"/tmp/lds"+aString+".txt");
    		FileWriter fileWriter;
    		try {
    			fileWriter = new FileWriter(f);
    		
        	BufferedWriter brd = new BufferedWriter(fileWriter);
    		PrintWriter printWriter = new PrintWriter(brd);
    		SootMethod m = ele.getKey();
    		printWriter.println(m.getSignature()+": "+ele.getValue().size());
    		printWriter.close();
    		brd.close();
    		fileWriter.close();
    		} catch (IOException e) {
    			// TODO Auto-generated catch block
    			e.printStackTrace();
    		}
    	}
    }
//    Set<P> MHPSet = new HashSet<>();
    public void countMHPPairs() {
    	MHPCount = 0;

    	/*
    	 * Not a deep copy. So MHP information may change (removing symmetry to avoid recounting). So, run this function at the end.
    	 * 
    	 */
    	 Map<Stmt,BitSet> MHPCopy = new HashMap<Stmt,BitSet>(MHP);
    	 
    	System.out.println(aString+" Started count pairs with entry set:"+MHP.entrySet().size());
    	int th = Thread.activeCount();
   	 System.out.println("th count:"+th);
   	try {
   	    TimeUnit.SECONDS.sleep(2);
   	} catch (InterruptedException ie) {
   	    Thread.currentThread().interrupt();
   	}
   	
    	for(Map.Entry<Stmt,BitSet> ele : MHPCopy.entrySet()) {
    		Stmt keyst = ele.getKey();
    		int keyStmtCount = 1;
    		Set<Stmt> ldsKey=null;
//    		Set<Stmt> keyStSet=null, memStSet=null;
    		if(methOfRep.containsKey(keyst)) {
    			/*
    			 * It is a rep of some method
    			 */
    			SootMethod m = methOfRep.get(keyst);
    			keyStmtCount = methStmts.get(m).size();
//    			keyStSet = methStmts.get(m);
    			ldsKey=loadStores.get(m);
    		}
    		BitSet b = ele.getValue();
    		int keystPos = stmtList.indexOf(keyst);
    		
    		int memstPos = b.nextSetBit(0);
			while(memstPos!=-1) {
				int memStmtCount = 1;
				Set<Stmt> ldsMem=null;
				Stmt memSt = stmtList.get(memstPos);
				if(methOfRep.containsKey(memSt)) {
	    			/*
	    			 * It is a rep of some method
	    			 */
	    			SootMethod m = methOfRep.get(memSt);
	    			memStmtCount = methStmts.get(m).size();
//	    			memStSet = methStmts.get(m);
	    			ldsMem=loadStores.get(m);
	    		}
//				SootMethod keyM = myS.get(keyst);
//				SootMethod memM = myS.get(memSt);
//				if(keyM != null && memM != null)
//				if(keyM.getDeclaringClass().getName().contains("org.apache.xml")||memM.getDeclaringClass().getName().contains("org.apache.xml")
//					|| memM.getDeclaringClass().getName().contains("org.apache.xpath")
//					|| keyM.getDeclaringClass().getName().contains("org.apache.xpath")
//						
//						) {
//					System.out.println("caught");
//				}
					
				countRaces(ldsKey, ldsMem, keyst, memSt);
				BitSet b1 = MHPCopy.get(memSt);
				//if(b1 != null && keystPos!=-1)
					b1.clear(keystPos);
				MHPCount+=(keyStmtCount*memStmtCount);	
//				if(keyStSet!=null) {
//					for(Stmt skey: keyStSet) {
//						if(memStSet != null) {
//							for(Stmt smem: memStSet) {
//								MHPSet.add(new P(skey,smem));
//							}
//						}
//						else {
//							MHPSet.add(new P(skey,memSt));
//						}
//					}
//				}
//				else if(memStSet!=null) {
//					for(Stmt smem: memStSet) {
//						if(keyStSet != null) {
//							for(Stmt skey: keyStSet) {
//								MHPSet.add(new P(skey,smem));
//							}
//						}
//						else {
//							MHPSet.add(new P(keyst,smem));
//						}
//					}
//				}
//				else {
//					MHPSet.add(new P(keyst,memSt));
//				}
				
				memstPos = b.nextSetBit(memstPos+1);
	    	}
			
    		
    	}
    	
    	//System.out.println("After performing symmetry expCount:"+ expCount+" setCount:"+stpairs.size());
    	System.out.println(aString+" Ended count pairs,"+" No of pairs:"+MHPCount);
//    	System.out.println(aString+" Ended count pairs,"+" No of pairs set:"+MHPSet.size());
    	System.out.println(aString+"Possible races: "+possibleRaces);
    	possibleRaces = raceSet.size();
    	System.out.println(aString+"Possible races set: "+raceSet.size());
    }
    int possibleRaces = 0;
    Set<P> raceSet = new HashSet<>();
    HashMap<Stmt,Set<Stmt>> raceMap = new HashMap<>();
    public void addToRace(Stmt s1, Stmt s2) {
    	if(!raceMap.containsKey(s1)) {
    		if(raceMap.containsKey(s2)) {
    			
    		}
    	}
    }
    public void countRaces(Set<Stmt> ldsKey, Set<Stmt> ldsMem, Stmt key, Stmt mem) {
    	if(ldsKey != null) {
    		for(Stmt s1: ldsKey) {
    			if(ldsMem != null) {
    				for(Stmt s2:ldsMem) {
    					if(s1.getFieldRef().getField()==s2.getFieldRef().getField()) {
    						if(SimplifyUtil.isInterestingType(s1.getFieldRef().getField().getType())) {
	    						if(isRace((AssignStmt)s1,(AssignStmt)s2)) {
	    							raceSet.add(new P(s1,s2));
	    							possibleRaces++;
	    								
	    						}
    						}
    					}
    				}
    			}
    			else {
    				if(mem.containsFieldRef() && mem instanceof AssignStmt) {
    					if(s1.getFieldRef().getField()==mem.getFieldRef().getField()) {
    						if(SimplifyUtil.isInterestingType(s1.getFieldRef().getField().getType())) {
	    						if(isRace((AssignStmt)s1,(AssignStmt)mem)) {
	    								possibleRaces++;
	    								raceSet.add(new P(s1,mem));
	    						}
    						}
    					}
    				}
    			}
    		}
    	}
    	else if(ldsMem != null) { 
    		/*ldsKey is null so came to else part*/
    		for(Stmt s1: ldsMem) {
    			if(key.containsFieldRef() && key instanceof AssignStmt) {
					if(s1.getFieldRef().getField()==key.getFieldRef().getField()) {
						if(SimplifyUtil.isInterestingType(s1.getFieldRef().getField().getType())) {
							if(isRace((AssignStmt)s1,(AssignStmt)key)) {
									possibleRaces++;
									raceSet.add(new P(s1,key));
							}
						}
					}
				}
    		}
    	}
    	else { 
    		/*both ldsKey and ldsMem are null*/
    		if(key.containsFieldRef() && key instanceof AssignStmt && mem.containsFieldRef() && mem instanceof AssignStmt) {
				if(key.getFieldRef().getField()==mem.getFieldRef().getField()) {
					if(SimplifyUtil.isInterestingType(key.getFieldRef().getField().getType())) {
						if(isRace((AssignStmt)key,(AssignStmt)mem)) {
								possibleRaces++;
								raceSet.add(new P(key,mem));
						}
					}
				}
			}
    	}
    }
    static class P{
        final Stmt first;
        final Stmt second;

       public P(Stmt first, Stmt second) {
           this.first = first;
           this.second = second;
       }

       // Override equals to compare pairs based on their values
       @Override
       public boolean equals(Object o) {
           if (this == o) return true;
           if (o == null || getClass() != o.getClass()) return false;
           P pair = (P) o;
           return (Objects.equals(first, pair.first) && Objects.equals(second, pair.second)) ||
                   (Objects.equals(first, pair.second) && Objects.equals(second, pair.first));
       }

       // Override hashCode to be consistent with equals
       @Override
       public int hashCode() {
       	int hash1 = Objects.hashCode(first);
           int hash2 = Objects.hashCode(second);
           return hash1 + hash2;
       }

       // Optional: toString for readable output
       @Override
       public String toString() {
           return "(" + first + ", " + second + ")";
       }
   }
    public boolean isRace(AssignStmt key, AssignStmt mem) {
    	/*
    	 * get points-to sets of both the bases
    	 * and find if they intersect
    	 */
    	boolean israce = false;
    	Value kvl = key.getLeftOp();
    	Value kvr = key.getRightOp();
    	Value mvl = mem.getLeftOp();
    	Value mvr = mem.getRightOp();
    	if(!(kvl instanceof JInstanceFieldRef) && !(mvl instanceof JInstanceFieldRef)) {
    		/*
    		 * If both are only reads
    		 */
    		israce= false;
    	}
    	else {	
    		Local b1,b2;
    		if(kvl instanceof JInstanceFieldRef)
    			b1 = (Local)((JInstanceFieldRef)kvl).getBase();
    		else
    			b1 = (Local)((JInstanceFieldRef)kvr).getBase();
    		if(mvl instanceof JInstanceFieldRef)
    			b2 = (Local)((JInstanceFieldRef)mvl).getBase();
    		else
    			b2 = (Local)((JInstanceFieldRef)mvr).getBase();
    		if(SimplifyUtil.isInterestingType(b1.getType()) && SimplifyUtil.isInterestingType(b2.getType())) {
	    		BitSet bs1,bs2;
	    		bs1 = getVarPts(b1, key);
	    		bs2 = getVarPts(b2, mem);
	    		boolean intr = hasIntr(bs1,bs2,b1.getType(),b2.getType());
	    		if(intr)
	    			israce = true;
    		}
    	}	
    	return israce;
    }
   
public void countStrongUpdates() throws IOException {
    	
    	int strongCount = 0;
		for(Map.Entry<SootMethod,Set<Stmt>> ele : loadStores.entrySet()) {
			Set<Stmt> stmts = ele.getValue();
			for(Stmt st : stmts) {
				FieldRef fr = st.getFieldRef();
				SootField sf = fr.getField();
				
				boolean strong = true;
				
				if(MHP.containsKey(st)) {
					BitSet bs = MHP.get(st);
					if(bs.cardinality() >= 1) {
						int st1Pos  = bs.nextSetBit(0);
						
						while(st1Pos != -1) {
							Stmt st1 = stmtList.get(st1Pos);
							if(st1.containsFieldRef()) {
								FieldRef fr1 = st1.getFieldRef();
								SootField sf1 = fr1.getField();
								if(sf1 == sf) {
									strong = false;
									break;
								}
							}
							st1Pos = bs.nextSetBit(st1Pos+1);
						}
					}
				}
				if(strong)
					strongCount++;
			}
		}
		System.out.println("Strong updates:"+strongCount);
    	
    }
  
   
   
    public void printMethodMhp() throws IOException {
    	addPairs(); 
    	FileWriter fileWriter = new FileWriter(path+"/tmp/MhpMethodResult.txt");
		PrintWriter printWriter = new PrintWriter(fileWriter);
    	printWriter.println("Mhp result ");
    	String s = String.format("%1$-100s %2$-100s %3$-20s\n", "Method1", "Method2", "MHP result");
    	//fmt.format("%-30s %-30s %-20s\n", "Method1", "Method2", "MHP result");
    	printWriter.println(s);
    	Iterator<MHPMethodPair> itr = pairs.iterator();
    	while(itr.hasNext()) {
    		MHPMethodPair mp = itr.next();
    		Iterator<SootMethod> sit = mp.pair.iterator();
    		SootMethod m1 = null;
    		
    		if(sit.hasNext())
    			m1 = sit.next();
    		SootMethod m2 = m1;
    		if(sit.hasNext())
    			m2 = sit.next();
    		String s1 = String.format("%1$-100s %2$-100s %3$-20s\n", m1,m2, "true");
    		printWriter.println(s1);
    	}
    	printWriter.close();
    	fileWriter.close();
    }
    public void printSynchObliviousMethodMhp(SynchObliviousMhpAnalysis mhp) throws IOException {
    	FileWriter fileWriter = new FileWriter(path+"/tmp/SynchObMhpResult.txt");
		PrintWriter printWriter = new PrintWriter(fileWriter);
    	String s = String.format("%1$-100s %2$-100s %3$-20s\n", "Method1", "Method2", "MHP result");
    	//fmt.format("%-30s %-30s %-20s\n", "Method1", "Method2", "MHP result");
    	printWriter.println(s);
    	Options.v().setPhaseOption("cg.spark", "on");
    	
    	
    	Iterator<MHPMethodPair> itr = pairs.iterator();
    	while(itr.hasNext()) {
    		MHPMethodPair mp = itr.next();
    		Iterator<SootMethod> sit = mp.pair.iterator();
    		SootMethod m1 = null;
    		
    		if(sit.hasNext())
    			m1 = sit.next();
    		SootMethod m2 = m1;
    		if(sit.hasNext())
    			m2 = sit.next();
    		boolean b = mhp.mayHappenInParallel(m1,m2);
    		String s1 = String.format("%1$-100s %2$-100s %3$-20s\n", m1,m2, b);
    		//fmt.format("%-30s %-30s %-20s\n", mp.pair," ", "true");
    		printWriter.println(s1);
    	}
    	printWriter.close();
    	fileWriter.close();
    }
    public void printSynchObliviousMhpAll(SynchObliviousMhpAnalysis mhp) throws IOException {
    	Set<SootMethod> methSet = processed;
    	
    	Set<Set<SootMethod>> methPairs = new HashSet<Set<SootMethod>>();
		Set<SootMethod> dup = new HashSet<SootMethod>();
		dup.addAll(methSet);
		Iterator<SootMethod> itr1 = methSet.iterator();
		while(itr1.hasNext()) {
			SootMethod o1 = itr1.next();
			dup.remove(o1);
			Iterator<SootMethod> itr2 = dup.iterator();
			while(itr2.hasNext()) {
				SootMethod o2 = itr2.next();
				Set<SootMethod> pair = new HashSet<SootMethod>();
				pair.add(o1);
				pair.add(o2);
				methPairs.add(pair);
			}
		}
		FileWriter fileWriter = new FileWriter(path+"/tmp/SynchObResult.txt");
		PrintWriter printWriter = new PrintWriter(fileWriter);
		Formatter fmt = new Formatter();
      printWriter.println("SynchOblivious Mhp result ");
      String s = String.format("%1$-100s %2$-100s %3$-20s\n", "Method1", "Method2", "MHP result");
    	//fmt.format("%-30s %-30s %-20s\n", "Method1", "Method2", "MHP result");
    	printWriter.print(s);
    	Options.v().setPhaseOption("cg.spark", "on");
    	//SynchObliviousMhpAnalysis mhp = new SynchObliviousMhpAnalysis();
    	Iterator<Set<SootMethod>> itr = methPairs.iterator();
    	long totalTime = 0L;
    	while(itr.hasNext()) {
    		Set<SootMethod> mp = itr.next();
    		Iterator<SootMethod> sit = mp.iterator();
    		SootMethod m1 = sit.next();
    		SootMethod m2 = sit.next();
    		long startTime = System.nanoTime();
    		boolean b = mhp.mayHappenInParallel(m1,m2);
    		long elapsedTime = System.nanoTime() - startTime;
    		totalTime+=elapsedTime;
    		String s1 = String.format("%1$-100s %2$-100s %3$-20s\n", m1,m2, b);
    		//fmt.format("%-30s %-30s %-20s\n", mp.pair," ", "true");
    		if(b == true)
    		printWriter.print(s1);
    	}
      printWriter.print(fmt.toString());
      printWriter.close();
      fileWriter.close();
      System.out.println("Total elapsed time for synch oblivious all methods in seconds:"+totalTime/1000000000);
      System.out.println("Total elapsed time in milli seconds:"+totalTime/1000000);
    }


    public void addPairs() {
    	
    	//int expCount =0;
    	for(Map.Entry<Stmt,BitSet> ele : MHP.entrySet()) {
    		Stmt st = ele.getKey();
    		BitSet b = ele.getValue();
    		SootMethod m1 = myS.get(st);
    		//boolean addPair = true;
//    		if(m1==null) {
//    			System.out.println("Method name null for statement: "+st);
//    			addPair = false;
//    		}
    		BitSet bs = MHP.get(st);
    		int i = bs.nextSetBit(0);
			while(i!=-1) {
				Stmt st1 = (Stmt)stmtList.get(i);
	    		SootMethod m2 = myS.get(st1);
//	    		if(m2==null) {
//	    			System.out.println("Method name null for statement: "+st1);
//	    			addPair = false;
//	    		}
	    		//if(addPair) {
		    		MHPMethodPair mp = new MHPMethodPair(m1, m2);
//		    		if((m1.getName().equals("main") && m2.getName().equals("main")) /*&& (m1.getName().equals("run") || m2.getName().equals("run"))*/) {
//		    			System.out.println("--------------------------");
//		    			System.out.println("Statement : "+st1+" in "+myS.get(st1).methN);
//		    			System.out.println("Statement : "+st+" in "+myS.get(st).methN);
//		    			Set<Stmt> pSet = new HashSet<Stmt>();
//		    			pSet.add(st);
//		    			pSet.add(st1);
//		    			stpairs.add(pSet);
//		    			expCount++;
//		    		}
		    		if(!pairs.contains(mp)) {
		    			pairs.add(mp);
		    		}
	    		//}
	    		i = bs.nextSetBit(i+1);
	    	}
    		
    		
    	}
    	//System.out.println("After performing symmetry expCount:"+ expCount+" setCount:"+stpairs.size());
    	
    }
//    public void printPts() throws IOException {
//    	FileWriter fileWriter = new FileWriter(path+"/tmp/PointstoResult.txt");
//		PrintWriter printWriter = new PrintWriter(fileWriter);
//    	printWriter.println("Points to result ");
//    	printWriter.println("Method,Stmt,Local,Type,Points-to");
////    	fmt.format("%-15s %-30s %-15s%-25s%-15s\n", "Local Name", "Stmt", "Method","Type","Points-to result");
//    	//fmt.format("%s;%s;%s;%s\n", "Local Name", "Method","Type","Points-to result");
//    	for(Map.Entry<StmtLocal,BitSet> ele : varPts.entrySet()) {
//    		
//    		StmtLocal ls = ele.getKey();
//    		Local v = ls.l;
//    		Stmt st = ls.st;
//    		BitSet b = ele.getValue();
//    		StringBuilder sb = new StringBuilder();
//    		int i = b.nextSetBit(0);
//			while(i!=-1) {
//				if(allocNodes.get(i) instanceof AllocNode) {
//					AllocNode a = (AllocNode)allocNodes.get(i);
//				sb.append("O"+i+" at site "+a.printAllocSite()+" , ");
//				}
//				i = b.nextSetBit(i+1);
//				
//			}
//			//LineNumberTag tag = v.getTag("LineNumberTag");
//			//tag.getLineNumber();
//			if(!(v.getType() instanceof PrimType) ) {
//				printWriter.println(myL.get(v).getSignature()+","+st+","+v.getName()+","+v.getType()+","+"{"+sb.toString()+"}");
////				fmt.format("%-12s %-12s %-35s %-35s%-12s\n", v.getName(), st, myL.get(v).getSignature(),v.getType(),"{"+sb.toString()+"}");
//				
//			}
//    	}
////    	printWriter.println(fmt.toString());
//    	printFields(printWriter);
//    	printWriter.close();
//    	fileWriter.close();
//    	//printStaticFields();
//    	
//    	   	
//    }
//    public void printiPts() throws IOException {
//    	FileWriter fileWriter = new FileWriter(path+"/tmp/iPointstoResult.txt");
//		PrintWriter printWriter = new PrintWriter(fileWriter);
//    	printWriter.println("Points to result ");
//    	Formatter fmt = new Formatter();  
//    	fmt.format("%-15s %-15s%-25s%-15s\n", "Local Name", "Class", "Method","Type","Points-to result");
//    	//fmt.format("%s;%s;%s;%s\n", "Local Name", "Method","Type","Points-to result");
//    	for(Map.Entry<Local,BitSet> ele : ivarPts.entrySet()) {
//    		
//    		Local v = ele.getKey();
//    		BitSet b = ele.getValue();
//    		StringBuilder sb = new StringBuilder();
//    		int i = b.nextSetBit(0);
//			while(i!=-1) {
//				if(allocNodes.get(i) instanceof AllocNode) {
//					AllocNode a = (AllocNode)allocNodes.get(i);
//				sb.append("O"+i+" at site "+a.printAllocSite()+" , ");
//				}
//				i = b.nextSetBit(i+1);
//				
//			}
//			//LineNumberTag tag = v.getTag("LineNumberTag");
//			//tag.getLineNumber();
//			if(!(v.getType() instanceof PrimType) ) {
//				fmt.format("%-12s %-35s %-12s%-35s%-12s\n", v.getName(), myL.get(v).getSignature(),"{"+sb.toString()+"}");
//				
//			}
//    	}
//    	printWriter.println(fmt.toString());
//    	printFields(printWriter);
//    	printWriter.close();
//    	fileWriter.close();
//    	//printStaticFields();
//    	
//    	   	
//    }

    public void printFields(PrintWriter printWriter) {
    	printWriter.println("---------Fields points to------------");
    	for(Map.Entry<StmtAllocNodeField,BitSet> ele : fieldPts.entrySet()) {
    		StmtAllocNodeField v = ele.getKey();
    		Stmt st = v.st;

	    		BitSet b = ele.getValue();
	    		StringBuilder sb = new StringBuilder();
	    		int i = b.nextSetBit(0);
				while(i!=-1) {
					sb.append("O"+i+" ");
					i = b.nextSetBit(i+1);
				}
				printWriter.println("Ref "+((AllocNode)v.anf.an).memString()+"at stmt :"+st+" field "+v.anf.sf.getName()+" points to "+"{"+sb.toString()+"}");
	    		
    	}
    }

   Set<Stmt> allAllocsInLoop = new HashSet<>();
    public synchronized int addAlloc(AllocNode a) {
    	int ind =-1;
    	if(!arg.combined && !allocNodes.contains(a)) {
	    	ind = allocNodes.size();
	    	allocNodes.add(a);
	    	a.count=ind;
	    	
	    	SootMethod sm = myS.get(a.allocSite);
	    	
	    	if(schk.isInLoop(sm,a.allocSite)) {
	    		a.isInLoop = true;
	    		
	    	}
	    	
    	}
    	
    	
    	if(a.count==-1) {
    		System.out.println("ind -1");
    	}

		return a.count;
    	
    }
    public int addAllocNodeField(AllocNodeField anf) {

    	if(!fieldList.contains(anf)) {
    		fieldList.add(anf);
	    	
    	}
    	int ind = fieldList.indexOf(anf);
    	
    	
//    	if(a.allocSite!=null) {
//    		a.isSummaryRef = isSummarySt(a.allocSite);
//    	}
    	
		return ind;
    	
    }

   
private void printRefFields(SootMethod m) {
	System.out.println("++++++++++++++++++++++++++");
	System.out.println("ref fields of method: "+m.getSignature());
	BitSet b = refFields.get(m);
	int i = b.nextSetBit(0);
	while(i !=-1){
		System.out.println(fieldList.get(i));
		i = b.nextSetBit(i+1);
	}
	System.out.println("ref fieldsIn of method: "+m.getSignature());
	BitSet b1 = refFields.get(m);
	i = b1.nextSetBit(0);
	while(i !=-1){
		System.out.println(fieldList.get(i));
		i = b1.nextSetBit(i+1);
	}
	System.out.println("methFields of method: "+m.getSignature());
	Set<SootField> sfs = HelperAnalysis.methFields.get(m);
	System.out.println("methAccessed Fields of method: "+m.getSignature());
	Set<SootField> sfs2 = HelperAnalysis.methAccessedFlds.get(m);
	System.out.println(sfs2);
	System.out.println("++++++++++++++++++++++++++");
}
    public void printCallHierarchy(FunctionalConstraint fc, StringBuilder sb) {
		if(fc.caller!=null) {
			printCallHierarchy(fc.caller, sb);
		}
		sb.append(fc.method.getSignature()+" --> ");
	}

    public void insertConsForBit(int i, Constraint ic, MapName mapname, int cardinality) {
    	Constraint dup = ic;
		Object obj = null;
		
		if(mapBitSetType.get(mapname) == null) {
			System.out.println(mapname + "is null");
		}
		if(mapBitSetType.get(mapname) == 1) {
			obj = allocNodes.get(i);
		}
		else if(mapBitSetType.get(mapname) == 0){
			obj = stmtList.get(i);
		}
		else if(mapBitSetType.get(mapname) == 3){
			obj = methList.get(i);
		}
		else {
			obj = fieldList.get(i);
		}
		if(obj != null && obj!=nullRef) {
			dup = ic.getCopy();
			Constraint cons = dup.updateCond(obj, cardinality);
			
			if(cons != null) {
//				if(cons.name==ConstraintName.CC_NEW) {
//					System.out.println("caught");
//				}
				//insert(cons);
//				if(cons.name==ConstraintName.INNER_COND) {
//					System.out.println("s");
//				}
				cons.addToList();
			}
		}
//		else {
//			System.out.println("obj null for "+mapname);
//		}
    }
    
    public void printSyncMap() {
    	System.out.println("-----------------Sync map information------------");
    	for(Map.Entry<AllocNode, BitSet> ele : sync.entrySet()) {
    		AllocNode an = ele.getKey();
    		BitSet ba = ele.getValue();
    		
    		int i = ba.nextSetBit(0);
    		StringBuilder sb = new StringBuilder();
    		
    		while(i!=-1) {
				Stmt st1 = (Stmt)stmtList.get(i);
				sb.append(st1+"in meth :"+myS.get(st1).getSignature()+" ; ");
				sb.append("\n");
				i = ba.nextSetBit(i+1);
			}
    		
    		if(!sb.toString().equals("")) {
    			System.out.print("Alloc Node"+an.memString()+"has sync");
    			System.out.print("{");
    			System.out.println(sb.toString());
    			System.out.println("}");
    		}
    	}
    }

    void insertCond(Object condVariable, Constraint constraint, MapName mapType, Object member, Constraint elseConstraint) {
    	
    	
		Constraint ic = constraint;
		/*
		 * For all bits in bitset of condLocal;
		 * if bit is set, propagate the constraint, else store it in pending
		 */
    	//System.out.println("Solving conditional constraint" + "for all "+indVar+" in "+mapType+"("+condVariable+")"+ c.printConstraint());
		boolean useElseC = false;
		
		BitSet bArray = null;
		boolean isFun = false;
		boolean addToLater = true;
		
		Object condVar = condVariable;
		
		bArray = getBitSetFor(mapType, condVar);
		//bArray = (BitSet)solver.mapForName.get(mapType).get(condVar);
		if(bArray == null) {
			/*
			 * Add if not present
			 */
			bArray = insertIntoMap(mapType, condVar);
//			bArray = new BitSet();
//			mapForName.get(mapType).put(condVar, bArray);
		}
		int bitSize = 0;
		Node n;
		
		  n = new Node(mapType,condVar);
		ArrayList<Constraint> depList;
		if(!depCN.containsKey(n)) {
			depList = new ArrayList<Constraint>();
			depCN.put(n, depList);
		}
		else {
			depList = depCN.get(n);
		}
		
		if(bArray != null) {
			 ic = getDependentCons(ic, bArray, elseConstraint);
		}
		if(ic != null)
			depList.add(ic);
		
//		else
//		 bitSize = getBitSetSize(mapType);
		
		
		if(bArray != null) {
			/*
			 * check if the condition is a must condition
			 * i.e; varPts is singleton and non-summaryRef
			 */
			
    		if(ic != null) {
//    			if(mustCon && mustInd != -1) {
//    				insertConsForBit(mustInd,ic, mapType);
//    				return;
//    			
//    			}
    			
    			if(ic instanceof FunctionalConstraint) {
    				isFun = true;
    			}
    			int i = bArray.nextSetBit(0);
    			while(i != -1) {
    				/*
    				 * If bit is set, insert the constraint
    				 */
    				
    					addToLater = false;
    					boolean insert = true;
//    					if(ic.isSingleCaller) {
//    						Stmt st = stmtList.get(i);
//    						SootMethod sm = myS.get(st);
////    						if(callerStmts.get(sm) == null || sm ==  null) {
////    							System.out.println("null caught");
////    						}
//    						if(callerStmts.get(sm).size() > 1) {
//    							insert = false;
//    						}
//    					}
    					
    					if(insert)
    						insertConsForBit(i, ic, mapType, getCardinality(mapType, bArray));
    					
    					i = bArray.nextSetBit(i+1);
    				

    			}
    				if(!arg.interleaved && isFun && addToLater) {
	    				FunctionalConstraint fc = new FunctionalConstraint((FunctionalConstraint)ic);
		    			fc.useCHA = true;
		    			fc.populateFromCallSite();
//		    			Set<Stmt> sites = callerStmts.get(fc.method);
//		    			if(sites!=null && sites.contains(fc.callSite)) {
//	    					
//		    				System.out.println("not added");
//	    				}
//	    				else {
	    					funCons.add(fc);
	    					
//	    				}
		    			
	    				//processLaterCons.add(fc);
	    			
	    		}
    		}
    		
	    			
	    			
		}
		
		//solver.freeCond.add(this);
    }
   
   private Constraint getDependentCons(Constraint c, BitSet bArray, Constraint elseC) {
	   
	   Constraint ic = c;
	   if(c == null)
		   ic = elseC;
//	if(ic.cardinality != -1) {
//		if(bArray.cardinality() != c.cardinality)
//			ic = elseC;
//	}
		return ic;
		
   }
    public void insertProp(Object left, Object right,MapName leftMap, MapName rightMap) {
    	Object x = left;
		Object y = right;
		/*Add edge X->Y*/
		
		if(leftMap!=null || x != null) {
			Node n;
//			if(leftMap==MapName.fieldPts && rightMap==MapName.fieldPts) {
//				if(((StmtAllocNodeField)left).anf==null || ((StmtAllocNodeField)left).anf==null) {
//					System.out.println("STop");
//				}
//			}
			  n = new Node(leftMap,x);
			ArrayList<Node> elist = Edges.get(n);
			Node ce = new Node(rightMap, y);
			if(elist == null) {
				Edges.put(n, new ArrayList<Node>());
				elist = Edges.get(n);
			}
							
				
				if(!elist.contains(ce)) {
					boolean add = true;
					/*
					 * If there is already an edge from one of the successors,
					 * no need to add the edge
					 */
					for(Node succ : elist) {
						ArrayList<Node> succEList = Edges.get(succ);
						if(succEList != null && succEList.contains(ce)) {
							add = false;
							break;
						}
					}
					if(add)
						elist.add(ce);
					else {
						removed++;
						return;
					}
					
				}
			
			
		
		BitSet xArray = getBitSetFor(leftMap, x);

		/*for each bit that is set in the bitset, propagate the information*/
		if(xArray != null) {
			BitSet xSet = xArray;
			int i = xSet.nextSetBit(0);
			BitSet b = getBitSetFor(rightMap,y);
//			if(rightMap==MapName.fieldPts) {
//				StmtAllocNodeField anf = (StmtAllocNodeField)y;
//				if(anf.st.toString().equals("specialinvoke r0.<avrora.sim.Simulation$Node: void instantiate()>()") && anf.anf.an.count == 432) {
//					System.out.println("Stop");
//				}
//				
//			}
			
			while(i!=-1) {
//				if(b.get(i)) {
//					elist.remove(ce);
//					removed++;
//				}
				if(b==null || !b.get(i)) {
					Node nr = new Node(rightMap,y);
					if(Edges.containsKey(nr) || depCN.containsKey(nr)) {
//						PropagateTask pt = new PropagateTask(nr,i);
						propagateIt(nr,i);
					}
					else {
						propSkipped++;
//						if(!intPass)
//						b.set(i);
//						else
							setBit(rightMap, b, i, y);
					}
				}
				i = xSet.nextSetBit(i+1);
			}
		}
		}
    }
    public void insertMem(Object i, Object x, boolean isAlloc, MapName destMap) {
    	int pos;
//    	System.out.println("Solving member constraint"+ " DestMap:"+destMap+"("+i+")"+" bitPos: "+bitPos);
		if(isAlloc ) {
			pos = addAlloc((AllocNode)i);
			
		}
		else if(i instanceof AllocNode) {
			pos = allocNodes.indexOf(i);
//			pos = ((AllocNode)i).count;
		}
		else if(i instanceof Stmt){
			pos = stmtList.indexOf(i);
		}
		else if(i instanceof SootMethod){
			pos = methList.indexOf(i);
		}
		else {
			pos = fieldList.indexOf(i);
			if(pos==-1) {
				pos = addAllocNodeField((AllocNodeField)i);
			}
		}
//		if(destMap == MapName.varPts && pos == 71 ) {
//			System.out.println("STop");
//		}
		BitSet b = getBitSetFor(destMap,x);
		if(pos == -1) {
			System.out.println("pos -1 for "+destMap+" "+x);
			
//			if(x instanceof SootMethod) {
//				if(canBeIgnored((SootMethod)i, ((SootMethod)i).getActiveBody())) {
//					System.out.println("Ignored method");
//				}
//			}
		}
		if(pos!=-1 && (b==null || !b.get(pos))) {
			Node n = new Node(destMap, x);
			
			if(Edges.containsKey(n)||depCN.containsKey(n)) {
//				PropagateTask t = new PropagateTask(n,pos);
//				if(!propTasks.contains(t)) {
		
					
						propagateIt(n,pos);
					
					
//				}
			}
			else {
				memSkipped++;
//				if(!intPass)
//				b.set(pos);
//				else
					setBit(destMap, b, pos, x);
			}
		}
    	
    }
   public void setBit(MapName m, BitSet b, int bitPos, Object key) {
	   
//		   if(m==MapName.varPts && bitPos==0) {
//			   InterestingFieldPass.botLocals.add((StmtLocal)key);
//		   }
//	   if(m==MapName.varPts) {
//		   StmtLocal sl = (StmtLocal)key;
//		   if(sl.st.toString().equals("$r3 = (avrora.arch.AbstractArchitecture) $r2") 
//				   && sl.l.getName().equals("$r2")) {
//			   System.out.println("Stop here");
//		   }
//	   }
	   b.set(bitPos);
	   
	   if(m==MapName.MHP/* || m==MapName.funcsAtCallSite*/) {
//		   if(!arg.combined && key instanceof EnterMonitorStmt) {
//			  
//			   Stmt s = stmtList.get(bitPos);
//			   if(s instanceof EnterMonitorStmt) {
//				   System.out.println("Stop");
//			   }
//		   }
		  
		   Node n = new Node(m,key);
		   sUtil.propInverseMaps(n, bitPos);
	   }
	  
   }
    public void printMethPts(SootMethod m) throws IOException {
    	Body body = m.getActiveBody();
    	Chain<Unit> methStmts = body.getUnits();
    	Chain<Local> methLocals = body.getLocals();
    	Iterator<Unit> stIt = methStmts.iterator();
    	
    	StmtLocal ls = new StmtLocal(null,null);
    	AllocNodeField anf = new AllocNodeField(null,null);
    	StmtAllocNodeField anfs = new StmtAllocNodeField(null, anf);
//    	 FileWriter fileWriter = new FileWriter(path+"/tmp/mymethpts.txt");
//			PrintWriter printWriter = new PrintWriter(fileWriter);
    	PrintWriter printWriter = new PrintWriter(System.out);
    	while(stIt.hasNext()) {
    		Stmt st = (Stmt) stIt.next();
    		printWriter.println("+++++++before st : "+st+"++++");
    		printWriter.println("-----------Locals----------");
    		Iterator<Local> lIt = methLocals.iterator();
    		while(lIt.hasNext()) {
    			Local l = lIt.next();
    			ls.l = l;
    			ls.st = st;
    			
    		
	    		if(varPts.containsKey(ls)) {
	    			BitSet b = varPts.get(ls);
	        		StringBuilder sb = new StringBuilder();
	        		int i = b.nextSetBit(0);
	    			while(i!=-1) {
	    				if(allocNodes.get(i) instanceof AllocNode) {
	    					AllocNode a = (AllocNode)allocNodes.get(i);
	    				sb.append("O"+i+" at site "+a.printAllocSite()+" , ");
	    				}
	    				i = b.nextSetBit(i+1);
	    				
	    			}
	    			printWriter.println(l+ ": {"+sb.toString()+"}");
	    		}
    		}
    		
    		printWriter.println("-----------fields----------");
    		Iterator<AllocNodeField> fit = fieldList.iterator();
    		while(fit.hasNext()) {
    			AllocNodeField anf1 = fit.next();
    			boolean skip = true;
    			if(anf1 == null || anf1.an == null) {
    				System.out.println("null");
    			}
//    			if(anf1.an.count == 58 || anf1.an.count == 59/*&& anf1.sf.toString().equals("<org.dacapo.harness.CommandLineArgs: org.dacapo.harness.Callback callback>")*/) {
//    					skip = false;
//				}
//				if(skip)
//					continue;
    			//Iterator<AllocNode> allIt = allocNodes.iterator();
//    			while(allIt.hasNext()) {
//    				AllocNode an = allIt.next();
    				//AllocNodeFieldStmt anfs = new AllocNodeFieldStmt(an,sf,st);
				anfs = new StmtAllocNodeField(st,anf1);
//    				anfs.anf = anf1;
//    				//anfs.anf.sf = sf;
//    				anfs.st = st;
    				
    				if(fieldPts.containsKey(anfs)) {
    					
    	    			BitSet b = fieldPts.get(anfs);
    	        		StringBuilder sb = new StringBuilder();
    	        		int i = b.nextSetBit(0);
    	    			while(i!=-1) {
    	    				if(allocNodes.get(i) instanceof AllocNode) {
    	    					AllocNode a = (AllocNode)allocNodes.get(i);
    	    				sb.append("O"+i+" at site "+a.printAllocSite()+" , ");
    	    				}
    	    				i = b.nextSetBit(i+1);
    	    				
    	    			}
    	    			
    	    				printWriter.println("O"+((AllocNode)anfs.anf.an).count +" field :"+anf1.sf + ": {"+sb.toString()+"}");
    	    			
//    	    			else
//    	    				printWriter.println("Static field "+sf + ": {"+sb.toString()+"}");
    	    		}
    				else if(afieldPts.containsKey(anf)) {
    					BitSet b = afieldPts.get(anf);
    	        		StringBuilder sb = new StringBuilder();
    	        		int i = b.nextSetBit(0);
    	    			while(i!=-1) {
    	    				if(allocNodes.get(i) instanceof AllocNode) {
    	    					AllocNode a = (AllocNode)allocNodes.get(i);
    	    				sb.append("O"+i+" at site "+a.printAllocSite()+" , ");
    	    				}
    	    				i = b.nextSetBit(i+1);
    	    				
    	    			}
    	    			
    	    				printWriter.println("O"+((AllocNode)anf.an).count +" field :"+anf.sf + ": {"+sb.toString()+"}");
    	    			
    				}
    				
    			
    		}
    		printWriter.println("++++++++++");
    	}
    		
    	
    	printWriter.close();
//    	fileWriter.close();
    	
    }
    public void printMethResults(SootMethod m, boolean fieldIns, int count) throws IOException {
    	 FileWriter fileWriter = new FileWriter(path+"/tmp/methresult"+count+".txt");
			PrintWriter printWriter = new PrintWriter(fileWriter);
			printMethResults(m,fieldIns, printWriter);
			printWriter.close();
	    	fileWriter.close();
    }
    public void printMethResults(SootMethod m, boolean fieldIns, PrintWriter printWriter) throws IOException {
    	Body body=null;
    	if(m.hasActiveBody())
    	body = m.getActiveBody();
	else if(m.isConcrete()){
		body = m.retrieveActiveBody();
	}
    	Chain<Unit> mStmts = body.getUnits();
    	Stmt last = (Stmt)mStmts.getLast();
    	Chain<Local> methLocals = body.getLocals();
    	
    	Iterator<Unit> stIt = mStmts.iterator();
    	boolean haspc = true;
    	Stmt rep = null;
    	if(!hasPC.contains(m)) {
    		haspc = false;
    		rep = noPCMRep.get(m);
			
			
    	}
			printWriter.println(body);
    	StmtLocal ls = new StmtLocal(null,null);
    	AllocNodeField anf = new AllocNodeField(null,null);
    	StmtAllocNodeField anfs = new StmtAllocNodeField(null, anf);
    	while(stIt.hasNext()) {
    		Stmt st = (Stmt) stIt.next();
//    		if(!st.containsFieldRef())
//    			continue;
    		printWriter.println("+++++++before st : "+st+"++++");
    		printWriter.println("-----------Locals----------");
    		Iterator<Local> lIt = methLocals.iterator();
    		
    		while(lIt.hasNext()) {
    			Local l = lIt.next();
    			Object key= l;
    			Map map = ivarPts;
    			if(arg.fs) {
	    			
	    			ls.l = l;
	    			ls.st = st;
	    			key = ls;
	    			map = varPts;
    			}
    		
	    		if(map.containsKey(key)) {
	    			BitSet b = (BitSet)map.get(key);
	        		StringBuilder sb = new StringBuilder();
	        		int i = b.nextSetBit(0);
	    			while(i!=-1) {
	    				if(allocNodes.get(i) instanceof AllocNode) {
	    					AllocNode a = (AllocNode)allocNodes.get(i);
	    				sb.append("O"+i+" at site "+a.printAllocSite()+" , ");
	    				}
	    				i = b.nextSetBit(i+1);
	    				
	    			}
	    			printWriter.println(l+ ": {"+sb.toString()+"}");
	    		}
    		}
    		if(!fieldIns)
    		printFieldPts(st, printWriter);
//    		if(st.toString().equals("specialinvoke r0.<avrora.sim.Simulation$Node: void instantiate()>()") || st.toString().equals("$r2 = r0.<avrora.sim.types.SensorSimulation$SensorNode: avrora.sim.platform.Platform platform>") ) {
//    			if(refFields.containsKey(st)) {
//    				BitSet b = refFields.get(st);
//    				int i = b.nextSetBit(0);
//    				printWriter.println("------refFields-------");
//    				while(i!=-1) {
//    				AllocNodeField a = fieldList.get(i);
//    				if(a.an.count==432)
//    					printWriter.println(a.toString());
//    				i = b.nextSetBit(i+1);
//    				}
//    			}
//    		}
    		Stmt chk;
    		if(!haspc) {
    			chk = rep;
    		}
    		else {
    			chk = st;
    		}
    		if(MHP.containsKey(chk)) {
    			printWriter.println("-----------MHP----------");
    			BitSet b = MHP.get(chk);
	//    			int count = b.cardinality();
	//    			printWriter.println("Count:"+count);
	        		int i = b.nextSetBit(0);
	        		StringBuilder sb = new StringBuilder();
	    			while(i!=-1) {
	    				Unit s = stmtList.get(i);
	    				if(methOfRep.containsKey(s)) {
	    					/*
	    					 * It is a representative of a method
	    					 */
	    					sb.append("all "+methStmts.get(methOfRep.get(s)).size()+" statements of method: "+methOfRep.get(s).getSignature()+"\n");
	    				}
	    				else
	    				sb.append(s+" from "+myS.get(s)+"\n");
	    				i = b.nextSetBit(i+1);
	    			}
	    			if(!sb.toString().equals("")) {
	    				printWriter.println(sb.toString());
	    				
	    				
	    			}
    			
    		}
    		if(escapeAt.containsKey(st)) {
    			printWriter.println("-----------escape info----------");
    			BitSet b = escapeAt.get(st);
        		StringBuilder sb = new StringBuilder();
        		int i = b.nextSetBit(0);
    			while(i!=-1) {
    				if(allocNodes.get(i) instanceof AllocNode) {
    					AllocNode a = (AllocNode)allocNodes.get(i);
    				sb.append("O"+i+" at site "+a.printAllocSite()+" , ");
    				}
    				i = b.nextSetBit(i+1);
    				
    			}
    			printWriter.println( "{"+sb.toString()+"}");
    		}
    	}
    	if(fieldIns) {
    		printWriter.println("---Field Pts flow-insensitive Information---");
    		for(Map.Entry<AllocNodeField,BitSet> ele : ifieldPts.entrySet()) {
    			AllocNodeField an = ele.getKey();
//    			if(an.sf.getSignature().equals("<avrora.sim.Simulator: avrora.sim.Interpreter interpreter>")) {
	    			BitSet bs = ele.getValue();
	    			StringBuilder sb = new StringBuilder();
	        		int i = bs.nextSetBit(0);
	    			while(i!=-1) {
	    				if(allocNodes.get(i) instanceof AllocNode) {
	    					AllocNode a = (AllocNode)allocNodes.get(i);
	    				sb.append("O"+i+" at site "+a.printAllocSite()+" , ");
	    				}
	    				i = bs.nextSetBit(i+1);
	    				
	    			}
	    			printWriter.println("O"+((AllocNode)an.an).count +" field :"+an.sf + ": {"+sb.toString()+"}");
//    		}
    		}
    	}
//    	System.out.println("reachable methods");
//    	BitSet b = reachableFuncs.get(m);
//    	int bit = b.nextSetBit(0);
//    	while(bit != -1) {
//    		System.out.println(methList.get(bit).getSignature());
//    		bit = b.nextSetBit(bit+1);
//    	}
//    	System.out.println("meth rep");
//    	b = methRep.get(m);
//    	bit = b.nextSetBit(0);
//    	while(bit != -1) {
//    		System.out.println(stmtList.get(bit));
//    		bit = b.nextSetBit(bit+1);
//    	}
    	
//    	else
//    		{
//    		System.out.println("---Field Pts flow-sensitive Information at last statement---");
//    		Iterator<AllocNodeField> fit = fieldList.iterator();
//    		while(fit.hasNext()) {
//    			AllocNodeField anf1 = fit.next();
//    			if(anf1 == null || anf1.an == null) {
//				System.out.println("null");
//			}
//			anfs = new StmtAllocNodeField(last,anf1);
//			if(fieldPts.containsKey(anfs)) {
//	    		BitSet b = fieldPts.get(anfs);
//	        	StringBuilder sb = new StringBuilder();
//	        	int i = b.nextSetBit(0);
//	    		while(i!=-1) {
//	    			if(allocNodes.get(i) instanceof AllocNode) {
//	    				AllocNode a = (AllocNode)allocNodes.get(i);
//	    				sb.append(a.printAllocSite());
//	    			}
//	    			i = b.nextSetBit(i+1);
//	    				
//	    		}
//	    			
//	    		System.out.println("O"+((AllocNode)anfs.anf.an).count +" field :"+anf1.sf + ": {"+sb.toString()+"}");
//	    			
//	    	}
//			else if(afieldPts.containsKey(anf)) {
//				BitSet b = afieldPts.get(anf);
//	        	StringBuilder sb = new StringBuilder();
//	        	int i = b.nextSetBit(0);
//	    		while(i!=-1) {
//	    			if(allocNodes.get(i) instanceof AllocNode) {
//	    				AllocNode a = (AllocNode)allocNodes.get(i);
//	    				sb.append("O"+i+" at site "+a.printAllocSite()+" , ");
//	    			}
//	    			i = b.nextSetBit(i+1);
//	    				
//	    		}
//	    			
//	    		System.out.println("O"+((AllocNode)anf.an).count +" field :"+anf.sf + ": {"+sb.toString()+"}");
//	    			
//			}
//		}
//    		
//    }
//    	printSyncSets();
    	printWriter.println("-------------------kill sets------------------");
    	for(Map.Entry<SootMethod, Set<EnterMonitorStmt>> ele : synchStmts.entrySet()) {
    		SootMethod sm = ele.getKey();
    		Set<EnterMonitorStmt> stset = ele.getValue();
    		for(Stmt st:stset) {
    			printWriter.println("Statement "+st+" from method "+sm.getSignature());
    			printWriter.println("kill set");
    			if(kill.containsKey(st)) {
    				BitSet bs = kill.get(st);
    				printWriter.println("Count:"+bs.cardinality());
//    				System.out.println("{");
//    				int i = bs.nextSetBit(0);
//    				while(i!=-1) {
//    					Stmt s = stmtList.get(i);
//    					System.out.println(s+" from "+myS.get(s).getSignature());
//    					i = bs.nextSetBit(i+1);
//    				}
//    				System.out.println("}");
    			}
    		}
    	}
    	for(Map.Entry<Stmt, BitSet> ele : kill.entrySet()) {
    		Stmt st = ele.getKey();
    		BitSet bs = ele.getValue();
    		if(st.containsInvokeExpr()) {
    			InvokeExpr ie = st.getInvokeExpr();
    			SootMethod method = ie.getMethod();
    			if(method.getName().equals("join")) {
    				printWriter.println("For join kill count:"+bs.cardinality());
//    				System.out.println("{");
//    				int i = bs.nextSetBit(0);
//    				while(i!=-1) {
//    					Stmt s = stmtList.get(i);
//    					System.out.println(s+" from "+myS.get(s).getSignature());
//    					i = bs.nextSetBit(i+1);
//    				}
//    				System.out.println("}");
    			}
    		}
    	}
    	printWriter.println("-------------------monitorStmts sets------------------");
    	for(Map.Entry<SootMethod, Set<EnterMonitorStmt>> ele : synchStmts.entrySet()) {
    		SootMethod sm = ele.getKey();
    		Set<EnterMonitorStmt> stset = ele.getValue();
    		for(Stmt st:stset) {
    			printWriter.println("Statement "+st+" from method "+sm.getSignature());
    			printWriter.println("monitor stmts");
    			if(monitorStmts.containsKey(st)) {
    				BitSet bs = monitorStmts.get(st);
//    				System.out.println("Count:"+bs.cardinality());
    				printWriter.println("{");
    				int i = bs.nextSetBit(0);
    				while(i!=-1) {
    					Stmt s = stmtList.get(i);
    					if(methOfRep.containsKey(s)) {
    						printWriter.println("all meth statements of"+methOfRep.get(s).getSignature());
    					}
    					else {
    					
    						printWriter.println(s+" from "+myS.get(s).getSignature());
    						
    					}
    					i = bs.nextSetBit(i+1);
    				}
    				printWriter.println("}");
    			}
    		}
    	}
    	printWriter.println("-------------------runIP sets------------------");
    	for(Map.Entry<SootClass, BitSet> e: runStmts.entrySet()) {
    		printWriter.println("For alloc node: O"+e.getKey().getName());
    		BitSet bs = e.getValue();
    		int i = bs.nextSetBit(0);
    		printWriter.println("{");
			while(i!=-1) {
				Stmt st = stmtList.get(i);
				printWriter.println(st);
				i =  bs.nextSetBit(i+1);
			}
			printWriter.println("}");
    	}
    	printWriter.println("-------------------syncIP sets------------------");
    	for(Map.Entry<AllocNode, BitSet> e: syncIP.entrySet()) {
    		printWriter.println("For alloc node: O"+e.getKey().count);
    		BitSet bs = e.getValue();
    		int i = bs.nextSetBit(0);
    		printWriter.println("{");
			while(i!=-1) {
				Stmt st = stmtList.get(i);
				printWriter.println(st);
				i =  bs.nextSetBit(i+1);
			}
			printWriter.println("}");
    	}
    	printWriter.println("-------------------sync sets------------------");
    	for(Map.Entry<AllocNode, BitSet> e: sync.entrySet()) {
    		printWriter.println("For alloc node: O"+e.getKey().count);
    		BitSet bs = e.getValue();
    		int i = bs.nextSetBit(0);
    		printWriter.println("{");
			while(i!=-1) {
				Stmt st = stmtList.get(i);
				printWriter.println(st);
				i =  bs.nextSetBit(i+1);
			}
			printWriter.println("}");
    	}
    	
    }
    public void printSyncSets() {
    	System.out.println("-------------------sync sets------------------");
    	for(Map.Entry<SootMethod, Set<EnterMonitorStmt>> ele : synchStmts.entrySet()) {
    		SootMethod sm = ele.getKey();
    		Set<EnterMonitorStmt> stset = ele.getValue();
    		for(Stmt st:stset) {
    			EnterMonitorStmt ste = (EnterMonitorStmt)st;
    			System.out.println("For statemnt "+st+" from "+myS.get(st).getSignature());
    			Value l = ste.getOp();
    			StmtLocal lsp = new StmtLocal(st,(Local)l);
    			BitSet bs = varPts.get(lsp);
    			if(bs != null) {
    				
    				int i = bs.nextSetBit(0);
    				while(i!=-1) {
    					AllocNode a = allocNodes.get(i);
    					System.out.println("sync set of O"+a.count);
    					BitSet bs1 = sync.get(a);
    					if(bs1==null || bs1.cardinality() == 0) {
    						bs1 = sync.get(bottom);
    						//System.out.println("caught");
    					}
    					System.out.println("Count:"+bs1.cardinality());
//    					System.out.println("{");
//    					if(bs1!=null) {
//	        				int j = bs1.nextSetBit(0);
//	        				while(j!=-1) {
//	        					Stmt s = stmtList.get(j);
//	        					System.out.println(s+" from "+myS.get(s).getSignature());
//	        					j = bs1.nextSetBit(j+1);
//	        				}
//    					}
//        				System.out.println("}");
    					i =  bs.nextSetBit(i+1);
    				}
//    				System.out.println("}");
    			}
    		}
    	}
    }
    public void printFieldPts(Stmt st, PrintWriter printWriter) {
    	printWriter.println("---Field Pts flow-sensitive Information---");
    	Iterator<AllocNodeField> fit = fieldList.iterator();
		while(fit.hasNext()) {
			AllocNodeField anf1 = fit.next();
			if(anf1 == null || anf1.an == null) {
				printWriter.println("null");
			}
//			if(anf1.sf.getSignature().equals("<avrora.sim.Simulator: avrora.sim.Interpreter interpreter>")) {
				StmtAllocNodeField anfs = new StmtAllocNodeField(st,anf1);
				if(fieldPts.containsKey(anfs)) {
		    		BitSet b = fieldPts.get(anfs);
		        	StringBuilder sb = new StringBuilder();
		        	int i = b.nextSetBit(0);
		    		while(i!=-1) {
		    			if(allocNodes.get(i) instanceof AllocNode) {
		    				AllocNode a = (AllocNode)allocNodes.get(i);
		    				sb.append(a.printAllocSite());
		    			}
		    			i = b.nextSetBit(i+1);
		    				
		    		}
		    			
		    		printWriter.println("O"+((AllocNode)anfs.anf.an).count +" field :"+anf1.sf + ": {"+sb.toString()+"}");
		    			
		    	}
//			}
		}
    }
    public BitSet insertIntoMap(MapName mapName, Object l) {
    	BitSet bs = new BitSet();
		bs.clear();
		mapForName.get(mapName).put(l,bs);
		return bs;
    }
    public static Body getBody(SootMethod sm) {
		Body b = null;
		if(!methBodies.containsKey(sm)) {
//		if(!sm.getDeclaringClass().isLibraryClass()) {
			if(sm.hasActiveBody())
				b = sm.getActiveBody();
			else if(sm.isConcrete()){
				b = sm.retrieveActiveBody();
			}
			methBodies.put(sm, b);
//		}
		}else {
			b = methBodies.get(sm);
		}
		return b;
	}
//    public void genConstraints(Generator gen) throws SecurityException, IOException, InterruptedException, ExecutionException{
//    	/*
//    	 * Iterate over the methods in worklist.
//    	 * 1. Generate every method constraints
//    	 * 	a. Points-to : Copy parameter, field points-to
//    	 * 	b. MHP : MHP copy from call site to first stmt
//    	 * 2. Record the call statements
//    	 * 3. If method already processed,generate only return copy constraints for points-to, MHP
//    	 * 4. Else, generate the constraints and store in solver constraints list
//    	 * 5. When worklist becomes empty, solve all the constraints
//    	 */
//    	long genT = 0;
//    	while(workList.size() > 0) {
//    		FunctionalConstraint fc = (FunctionalConstraint)workList.remove(0);
//    		SootMethod method = fc.method;
//    		Body b = null;
//    		if(method.hasActiveBody())
//    			b = method.getActiveBody();
//    		if(b!=null ) {
//    			analyzer.setCallerFc(fc);
//    			analyzer.genEveryMethod();
//    			Stmt firstS = (Stmt)b.getUnits().getFirst();
//    			Stmt callSite = fc.callSite;
//    			if(callSite != null) {
//	    			if(callerStmts.containsKey(fc.method)) {
//	    				Set<Stmt> sites = callerStmts.get(fc.method);
//	    				if(!sites.add(callSite)) {
//	    					//System.out.println("Method already processed for this call site");
//	    					continue;
//	    				}
//	    			}
//	    			else {
//	    				Set<Stmt> sites = new HashSet<Stmt>();
//	    				sites.add(callSite);
//	    				callerStmts.put(method, sites);
//	    			}
//	    			callStmts.add(callSite);
////	    			if(!callerStmts.containsKey(method)) {
////	    				callerStmts.put(method, new HashSet<>());
////	    			}
////	    			callerStmts.get(method).add(callSite);
//    			}
//    		
//    			boolean alreadyProcessed = false;
//    			if(processed.contains(method)) {
//    				alreadyProcessed = true;
//    			}
//    			else {
//    				processed.add(method);
//    				if(!methList.contains(method)) {
//    					methList.add(method);
//    				}
//    			}
//   		
//    		if(method.getDeclaringClass().isLibraryClass()) {
//    			if(!stmtList.contains(firstS))
//	    			stmtList.add(firstS);
//	    		if(!myS.containsKey(firstS))
//	    			myS.put(firstS,method);
//	    		analyzer.addConsToSolverLists();
//    			
//    			if(!alreadyProcessed) {
//	    			if(fc.caller!=null && fc.caller.method != fc.method) {
//	    				if(fc.caller.method.getDeclaringClass().isLibraryClass() && fc.method.getDeclaringClass().isLibraryClass()) {
//	    					bothLib++;
//	    					
//	    				}
//	    				if(fc.method.getDeclaringClass().isLibraryClass())
//	    					libCount++;
//	    				if(arg.callLog)
//	    				printWriter.println(fc.caller.method+"->"+fc.method+";");
//	    			}
//    			}
//    			//solveConstr();
//    			
//    			continue;
//    		}
//    		if(arg.callLog && fc.caller != null)
//    			printWriter.println(fc.caller.method+"->"+fc.method+";");
//    		
//    		if(!alreadyProcessed) {
//    			
//    			if(method.getName().equals("<clinit>")) {
//    				clCount++;
//    			}
//    			long genStart = System.nanoTime();
//    			gen.generate(b, fc);
//    			genT = (System.nanoTime() - genStart);
//    	    	genTime+= genT;
//    			
////    				methLocals.put(fc.method, fc.methLocals);
////    				addStmts(fc.methStmts, fc.method);
//    				//analyzer.callerFc = fc;
//    				analyzer.addConsToSolverLists();
////    	    		if(fc.laterCons != null)
////    	    			processLaterCons.addAll(fc.laterCons);
//    	    		if(gen.retStmts != null) {
//    	    			BitSet retStmts = methRet.get(fc.method);
//    	    			if(retStmts == null) {
//    	    				retStmts = new BitSet();
//    	    				methRet.put(fc.method, retStmts);
//    	    			}
//    	    			Iterator<Stmt> itr = gen.retStmts.iterator();
//    	    			while(itr.hasNext()) {
//    	    				Stmt st = itr.next();
//    	    				int ind = stmtList.indexOf(st);
//    	    				retStmts.set(ind);
//    	    			}
//    	    		}
////    	    		intStmtCount+=gen.methInterestingStmts.size();
////    	    		fieldStmtCount+=gen.fieldInterestingStmts.size();
//    	    	
//    			
//    		}
//    		else {
//    			genProcessed(fc);
//    			
//    		}    		
//    	}
//    		
//    	}
//
//    	
//    }
    
    
    public void printProcessed() throws IOException {
    	String filename = path+"/tmp/"+aString+"allMeths_"+arg.bench+".txt";
    	FileWriter fileWriter = new FileWriter(filename);
		PrintWriter printWriter = new PrintWriter(fileWriter);
		for(SootMethod m:processed) {
			String s = m.getDeclaringClass().getName();
			s = s.replace(".", "/");
			String n = m.getName();
//			if(n.equals("parse")) {
//				System.out.println("Stop");
//			}
			StringBuffer sb = new StringBuffer();sb.append(s);
			sb.append(".");
			sb.append(n);
			printWriter.println(sb.toString());
//			printWriter.println(m.getSignature());
		}
		String runlist = path+"/runtimelist/"+arg.bench+"list.txt";
		callScript(filename,runlist);
		printWriter.close();
		fileWriter.close();
    }
    public void printProcessedSig() throws IOException {
    	String filename = path+"/tmp/"+aString+"proMeths_"+arg.bench+".txt";
    	FileWriter fileWriter = new FileWriter(filename);
		PrintWriter printWriter = new PrintWriter(fileWriter);
		for(SootMethod m:processed) {
			
			printWriter.println(m.getSignature());
//			printWriter.println(m.getSignature());
		}
		
		printWriter.close();
		fileWriter.close();
    }
    public void callScript(String file1, String file2) throws IOException {
//    	String[] command = { "./myscript", "key", "ls -t | tail -n 1" };
    	String command = "comm -23 <(sort -u "+file1+") <(sort -u "+file2+")";
        Process process = Runtime.getRuntime().exec(command);
        BufferedReader reader = new BufferedReader(new InputStreamReader(
            process.getInputStream()));
        String s;
        System.out.println("Script output: ");
        while ((s = reader.readLine()) != null) {
        	System.out.println(s);
        }
    }
    public String getMethodString(SootMethod method) {
    	StringBuffer sb = new StringBuffer();
    	String declClass = method.getDeclaringClass().toString();
    	declClass = declClass.replace(".", "/");
    	sb.append(declClass);
    	sb.append(".");
    	sb.append(method.getName());
    	return sb.toString();
    }
    HashSet<SootMethod> nat = new HashSet<SootMethod>();
    Set<SootMethod> natNotNull = new HashSet<SootMethod>();
//    int xmlparse = 0;
//    int xmlother = 0;
    static Map<SootMethod,Body> methBodies = new HashMap<>();
    static Set<SootMethod> xMeths = new HashSet<>();
    Map<SootMethod,Set<SootMethod>> callG = new HashMap<>();
    public void genConstraints(Generator gen) throws SecurityException, IOException, InterruptedException, ExecutionException{
    	List<Task> tasks = null;
    	if(arg.genParallel)
    		tasks = new ArrayList<Task>();
    	ArrayList<FunctionalConstraint> processedMeth = new ArrayList<FunctionalConstraint>();
    	
    	while(workList.size() > 0) {
    		FunctionalConstraint fc = (FunctionalConstraint)workList.remove(0);
    		totalInvokes++;
    		
    		if(!arg.interleaved && fc.ref == null && fc.useCHA ) {
    			fc.populateFromCallSite();
    			fc.insert();
    			continue;
    		}
    		if(arg.combined && !intPass && fc.useCHA && fc.ref==null) {
    			
    			fc.populateFromCallSite();
    			fc.insert();
    			continue;
    		}
    		SootMethod method = fc.method;

    		Body b = getBody(method);
    		fc.b = b;
    		/*
    		 * Record the call
    		 */
    		
    		boolean alreadyProcessed = recordCall(fc);
			Stmt callSite = fc.callSite;
			if(callSite != null) {
    			if(callerStmts.containsKey(fc.method)) {
    				Set<Stmt> sites = callerStmts.get(fc.method);
    				if(!sites.add(callSite)) {
    					
    					continue;
    				}
    			}
    			else {
    				Set<Stmt> sites = new HashSet<Stmt>();
    				sites.add(callSite);
    				callerStmts.put(method, sites);
    			}
    			callStmts.add(callSite);

			}
			if(fc.method.isNative()) {
				nat.add(fc.method);
				continue;
			}
			boolean ign = false;

				ign = SimplifyUtil.opaqueMethod(fc.method,b);
				if(!ign)
					ign = SimplifyUtil.isLibRun(fc);

    		if(ign) {
    			if(arg.callLog) {
    				printWriter.println("ignored");
    			}
    			continue;
    		}
    	
    		if( b!=null && !method.getDeclaringClass().isLibraryClass()) {
//    			if(method.getSignature().equals("<org.apache.xerces.parsers.DOMParser: void <init>()>")) {
//    				System.out.println("debug stop");
//    			}
    			FieldSummary.summarizeCreation(fc.method,b) ;
				FieldSummary.summaryField(fc.method,b);
    			
    			
    		if(!alreadyProcessed) {
    			if(method.getName().equals("<clinit>")) {
    				
    				clCount++;
    				if(clinitProcessed.contains(method.getDeclaringClass())) {
    					/*
    					 * process clinit only once
    					 */
    						continue;
    				}
    				else {
    					clinitProcessed.add(method.getDeclaringClass());
    				}
    			}
    			if(arg.genParallel) {
	    			Task c1 = new Task(b,fc, this);
	        		tasks.add(c1);
    			}
    			else {
    				generateAndAddCons(new Generator(), fc, b);
    			}
    			
    		}
    		else {
    			processedMeth.add(fc);
    			
    		}    		
    	}
    		else {

    			if(b==null) {
    				
    				if(fc.method.isNative()) {
    					nat.add(fc.method);
    					continue;
    				}
//    				else
//    					natNotNull.add(fc.method);    				
    				
    			}
    			genConsForLibAndBodyNull(fc, false);
    		}
    		
    	}
    	
    	if(arg.genParallel&& tasks.size() > 0) {
    		pool= Executors.newFixedThreadPool(noofthreads);
    		CountDownLatch cdl = new CountDownLatch(tasks.size());

			for(Task task : tasks) {
				task.cdl = cdl;
				pool.execute(task);
			}
			
			cdl.await();
			pool.shutdown();
			int th = Thread.activeCount();
			do {
			pool.awaitTermination(60, TimeUnit.SECONDS);
			th = Thread.activeCount();
			}
			while(th>1);
    	}
    	int th = Thread.activeCount();
    	System.out.println("No of threads: "+th);
    	if(th > 1) {
    		System.out.println("!!!!!!!!!!!!!");
    	}
    	genProcessed(processedMeth);
    	
    }
    

    public boolean recordCall(FunctionalConstraint fc) {
    	

		boolean alreadyProcessed = recordProcessed(fc.method);
		
		if(fc.caller!=null) {
			recordCall(fc.caller.method, fc.method);
			
		}
		if(fc.method.getDeclaringClass().isLibraryClass()) {
			if(!alreadyProcessed) {
				libCount++;
				if(arg.callLog)
				printWriterLib.println(fc.method.getSignature());

			}
		
			
		}
		return alreadyProcessed;
    }
    
    private void printCallPath(FunctionalConstraint fc) throws IOException {
    	File f = new File(path+"/tmp/callM"+aString+".txt");
    	
    	FileWriter fileWriter = new FileWriter(f,true);
    	BufferedWriter br = new BufferedWriter(fileWriter);
		PrintWriter printWriter = new PrintWriter(br);
    	while(fc.method!=main) {
    		printWriter.print("->"+fc.method.getSignature());
    		fc = fc.caller;
    	}
    	printWriter.println();
    	printWriter.println("s----------------------------------------");
    	printWriter.close();
    	br.close();
    	fileWriter.close();
    }
   public boolean recordProcessed(SootMethod method) {
	   boolean alreadyProcessed = false;
   	if(processed.contains(method)) {
			alreadyProcessed = true;
		}
		else {
			processed.add(method);
			if(!methList.contains(method)) {
				methList.add(method);
			}
			
		}
   	return alreadyProcessed;
   }
    public void recordCall(SootMethod caller, SootMethod callee) {
    	/*
    	 * record call edges if callLog is set
    	 * IN case of helperanalysis record it
    	 */
    	if(arg.callLog) {
			printWriter.println(caller+"->"+callee);
			
			MyCG.addToCallGraph(caller, callee);
		}
    	if(!callG.containsKey(caller)) {
    		callG.put(caller, new HashSet<>());
    	}
    	callG.get(caller).add(callee);
		if(intPass) {
			MyCG.addEdge(caller, callee);
			MyCG.addToHACallGraph(caller, callee);
		}
    }

    public void genConsForLibAndBodyNull(FunctionalConstraint fc, boolean record) {

    	if(intPass) {
    		HelperAnalysis.bodyNullMeths.add(fc.method);
    	}

    	SootMethod method = fc.method;

    	if(method.getName().equals("<clinit>")) {
			return;
		}
			if(fc.invokeExpr!=null && arg.bot /*&&!arg.combined*/ && arg.poa){
				sUtil.addBotToParamReachAndReturn(fc);

			}

    }
    private void propBotToReachables(FunctionalConstraint callerFc) {
    	List<Value> la = callerFc.invokeExpr.getArgs();
		Local rcvr = callerFc.rcvr;
			Iterator<Value> itr = la.iterator(); 
			
			MemConstraint addBot = new MemConstraint(bottom, null, false, MapName.fieldPts, ConstType.pts);

			addBot.addBottoFields = true;
			if(rcvr != null && SimplifyUtil.isInterestingType(rcvr.getType())) {
				StmtLocal lsa = new StmtLocal(callerFc.callSite, rcvr);
				ConditionalConstraint cc = new ConditionalConstraint(lsa, addBot, MapName.varPts, null, ConstType.pts);
				callerFc.addConditional(cc);
			}
			while(itr.hasNext()) {
				Value vl = itr.next();
				if(vl instanceof Local && SimplifyUtil.isInterestingType(vl.getType())) {
					StmtLocal lsa = new StmtLocal(callerFc.callSite, (Local)vl);
					ConditionalConstraint cc = new ConditionalConstraint(lsa, addBot, MapName.varPts, null, ConstType.pts);
					callerFc.addConditional(cc);
				}
			}

		/*
		 * If the call is of type x = lib(), add bottom to varPts(x)
		 */
		if(callerFc.retLocal != null && SimplifyUtil.isInterestingType(callerFc.retLocal.getType())) {
			StmtLocal sl = new StmtLocal(callerFc.callSite, (Local)callerFc.retLocal) ;
			MemConstraint addBotRet = new MemConstraint(bottom, sl, false, MapName.varPts, ConstType.pts);
			callerFc.addMember(addBotRet);
		}
    }
    private void propBotToParaReachablesIn(List<Value> la, Local rcvr, FunctionalConstraint callerFc, MapName m) {
    	
			Iterator<Value> itr = la.iterator(); 
			MapName varMap = analyzer.ptConsGen.varMap;
			MemConstraint addBot = new MemConstraint(bottom, null, false, m, ConstType.pts);

			ConditionalConstraint c = new ConditionalConstraint(null, addBot, MapName.fieldsOf, null, ConstType.pts);

			if(rcvr != null && SimplifyUtil.isInterestingType(rcvr.getType())) {
				Object lsa = analyzer.ptConsGen.getKey(callerFc.callSite, rcvr);
				ConditionalConstraint cc = new ConditionalConstraint(lsa, c, varMap, null, ConstType.pts);
				
	//			cc.name = ConstraintName.CC_NEW;
				callerFc.addConditional(cc);
			}
			while(itr.hasNext()) {
				Value vl = itr.next();
				if(vl instanceof Local && SimplifyUtil.isInterestingType(vl.getType())) {
					Object lsa = analyzer.ptConsGen.getKey(callerFc.callSite, (Local)vl);
					ConditionalConstraint cc = new ConditionalConstraint(lsa, c, varMap, null, ConstType.pts);
					callerFc.addConditional(cc);
				}
			}
    	
    	
		/*
		 * If the call is of type x = lib(), add bottom to varPts(x)
		 */
		if(callerFc.retLocal != null && SimplifyUtil.isInterestingType(callerFc.retLocal.getType())) {
			
			Object sl = analyzer.ptConsGen.getKey(callerFc.callSite, (Local)callerFc.retLocal) ;
			MemConstraint addBotRet = new MemConstraint(bottom, sl, false, varMap, ConstType.pts);
			callerFc.addMember(addBotRet);

		}
	}

    public void genProcessed(ArrayList<FunctionalConstraint> fcList) {
    	Iterator<FunctionalConstraint> itr = fcList.iterator();
    	while(itr.hasNext()) {
    		FunctionalConstraint fc = itr.next();
    		genProcessed(fc);
    	}
    	
    }
    public void runTimeCallGs() throws IOException {
    	int missingCount = 0;
    	int notInScene=0;
    	FileReader fr = new FileReader(path+"/runtimelist/callg.txt");
		BufferedReader br = new BufferedReader(fr); 
		String line = br.readLine(); 
		Set<SootMethod> edges=null;
		SootMethod source=null;
		while(line!=null) {
			StringTokenizer st = new StringTokenizer(line,"=");
			
			if(st.countTokens()>1) {
				String type = st.nextToken();
				if(type.equals("source")) {
					String sig = st.nextToken();
					if(Scene.v().containsMethod(sig)) {
						source = Scene.v().getMethod(sig);
						edges = MyCG.callGraph.get(source);
					}
					else {
						System.out.println(sig+" Not found in Scene");
						notInScene++;
					}
				}
				if(type.equals("destination")) {
					String sig = st.nextToken();
					if(edges!=null) {
						if(Scene.v().containsMethod(sig)) {
							SootMethod destination = Scene.v().getMethod(sig);
							if(!destination.getDeclaringClass().isPhantom() && !edges.contains(destination)) {
								String ign = "";
								if(!SimplifyUtil.opaqueMethod(destination,getBody(destination))) {
									System.out.println("Missing edge:"+source.getSignature()+"->"+destination.getSignature());
//									if(ignoreMethod(destination,null))
//										System.out.println("  ignored meth");
//									else
//										System.out.println();
									missingCount++;
								}
								
								
							}
						}
						else {
							System.out.println(sig+" Not found in Scene");
						}
					}
				}
			}
			line = br.readLine(); 
		}
		br.close();
		fr.close();
		System.out.println("Missing edges:"+missingCount);
		System.out.println("Not in scene:"+notInScene);
    }
    public void runTimeCallGs(String benchmark) throws IOException {
    	
    	FileReader fr = new FileReader(path+"/runtimelist/"+benchmark+"list.txt");
    	Set<String> methList = new HashSet<>();
    	Set<String> pMethList = new HashSet<>();
    	
		BufferedReader br = new BufferedReader(fr); 
		String line = br.readLine(); 
		
		while(line!=null) {
			
				methList.add(line);
			
			line = br.readLine(); 
		}
		br.close();
		fr.close();
		for(SootMethod sm: processed) {
			String s = getMethodString(sm);
			pMethList.add(s);
		}
		Set<String> onlyInRun = new HashSet<>(methList);
    	Set<String> onlyInMine = new HashSet<>(pMethList);
    	onlyInRun.removeAll(pMethList);
    	onlyInMine.removeAll(methList);
    	FileWriter fileWriter = new FileWriter(path+"/tmp/missingMeths.txt");
		PrintWriter printWriter = new PrintWriter(fileWriter);
		FileWriter fileWriter2 = new FileWriter(path+"/tmp/extraMeths.txt");
		PrintWriter printWriter2 = new PrintWriter(fileWriter2);
		for(String s: onlyInRun) {
			printWriter.println(s);
		}
		for(String s: onlyInMine) {
			printWriter2.println(s);
		}
		printWriter2.close();
		fileWriter2.close();
		printWriter.close();
		fileWriter.close();
		System.out.println("Missing methods:"+onlyInRun.size());
		System.out.println("Extra methods:"+onlyInMine.size());
    }
    public void findls() {
    	for(Map.Entry<SootField, Set<Stmt>> ele : loadf.entrySet()) {
    		SootField sf = ele.getKey();
    		Set<Stmt> s = ele.getValue();
    		if(s.isEmpty()) {
    			System.out.println(sf.getSignature());
    		}
    		if(!storef.containsKey(sf)) {
    			System.out.println(sf.getSignature());
    		}
    	}
    	System.out.println("load done");
    	for(Map.Entry<SootField, Set<Stmt>> ele : storef.entrySet()) {
    		SootField sf = ele.getKey();
    		Set<Stmt> s = ele.getValue();
    		if(s.isEmpty()) {
    			System.out.println(sf.getSignature());
    		}
    		if(!loadf.containsKey(sf)) {
    			System.out.println(sf.getSignature());
    		}
    	}
    }
    public void genProcessed(FunctionalConstraint fc) {
    	/*
		 * Process only the return copy
		 */
    	
		analyzer.setCallerFc(fc);
		analyzer.genEveryMethod();
		analyzer.genProcessed();
		analyzer.addConsToSolverLists();

    }
    
    private void printRunIncls() {
    	int c = 0;
    	Set<SootMethod> s = new HashSet<>();
    	for(Map.Entry<SootMethod, SootMethod> ele : runs.entrySet()) {
    		BitSet bs = reachableFuncs.get(ele.getKey());
    		int i = bs.nextSetBit(0);
//    		System.out.println("----Body-----");
    		Body b = getBody(ele.getKey());
//    		System.out.println(b);
//    		System.out.println("------Included methods-----");
    		while(i!=-1) {
    			SootMethod sm = methList.get(i);
    			s.add(sm);
    			c+=methStmts.get(sm).size();
//    			System.out.println(sm.getSignature());
    			i = bs.nextSetBit(i+1);
    		}
    	}
//    	c+=methStmts.get(main).cardinality();
    	System.out.println("Stmt count"+c);
    	int co = 0;
    	for(Map.Entry<Stmt, BitSet> ele : MHP.entrySet()) {
    		Stmt keys = ele.getKey();
    		SootMethod sm = myS.get(keys);
    		BitSet bs = ele.getValue();
    		if(bs.cardinality() > 0) {
	    		if(!s.contains(sm)) {
	    			System.out.println(keys+" from "+sm.getSignature());
	    			co++;
	    		}
    		}
    	}
    	System.out.println("Suspected"+co);
    }
    public BitSet getVarPts(Local l, Stmt st) {
    	BitSet b = null;
    	if(!arg.fs)
    		b = ivarPts.get(l);
    	else {
			StmtLocal sl = new StmtLocal(st,l);
			
			if(varPts.containsKey(sl)) {
				b = varPts.get(sl);
			}
			if(b==null){
				SootMethod m = myS.get(st);
				
				Map<Stmt,Map<Local,Set<Stmt>>> rDefMap = methRDef.get(m);
				Map<Local,Set<Stmt>> dSet = rDefMap.get(st);
				Set<Stmt> preds = dSet.get(l);
				if(preds != null) {
					BitSet b1 = new BitSet();
					for(Stmt p : preds) {
						StmtLocal pl = new StmtLocal(p,l);
						BitSet bp = varPts.get(pl);
						if(bp!=null)
							b1.or(bp);
					}
					b = b1;
					
				}
			}
    	}
//    	if(b==null) {
//			System.out.println("null");
//			SootMethod m = myS.get(st);
//			boolean ign = ignoredMeths.contains(m);
//			System.out.println(ign);
//		}
		return b;
	}
    public void addMethRep(SootMethod m, boolean hasPC, Set<Stmt> stmts, Stmt firstS) {
    	if(!arg.combined) {
    		Iterator<Stmt> itr = stmts.iterator();
	    	
	    	if(stmtList==null) {
	    		stmtList = new ArrayList<Stmt>();
	    	}
	    	
		    while(itr.hasNext()) {
		    	Stmt u = itr.next();
		    	if(!stmtList.contains(u))
		    		stmtList.add(u);
		    	if(!myS.containsKey(u))
		    		myS.put(u, m);
		    	
		    }
		    methStmts.put(m, stmts);
	    	if(!hasPC) {
	    		Stmt st = new JNopStmt();
	    		methOfRep.put(st, m);
	    		noPCMRep.put(m, st);
	    		stmtList.add(st);
	    		//myS.put(st, m);
	    		MemConstraint mc = new MemConstraint(st, m, false, MapName.methRep, ConstType.pts);
	    		mc.addToList();
	    		MemConstraint mc1 = new MemConstraint(st, m, false, MapName.mhpCopyTo, ConstType.pts);
	    		mc1.addToList();
	    	}
	    	else {
	    		MemConstraint mc1 = new MemConstraint(firstS, m, false, MapName.mhpCopyTo, ConstType.pts);
	    		mc1.addToList();
	    		itr = stmts.iterator();
	    		while(itr.hasNext()) {
	    			Stmt u = itr.next();
	    			MemConstraint mc = new MemConstraint(u, m, false, MapName.methRep, ConstType.pts);
		    		mc.addToList();
			    	
			    }
	    		
	    	}
    	}
    	else {
    		 methStmts.put(m, stmts);
    			BitSet b = methRepHA.get(m);
    			if(b != null) {
    			int i = b.nextSetBit(0);
    			while(i != -1) {
	    			Stmt st = stmtList.get(i);
	    			MemConstraint mc = new MemConstraint(st, m, false, MapName.methRep, ConstType.pts);
		    		mc.addToList();
		    		i = b.nextSetBit(i+1);
    			}
    			}
    			b = mhpCopyToHA.get(m);
    			if(b != null) {
    			int i = b.nextSetBit(0);
    			while(i != -1) {
	    			Stmt st = stmtList.get(i);
	    			MemConstraint mc = new MemConstraint(st, m, false, MapName.mhpCopyTo, ConstType.pts);
		    		mc.addToList();
		    		i = b.nextSetBit(i+1);
    			}
    			}
    	}
    	
    }
    private void initialize() {
    	/*
    	 * Map to store the BitSet type of each map
    	 */
    	 mapBitSetType.put(MapName.varPts,1);
    	 mapBitSetType.put(MapName.runStmts, 0);
    	 mapBitSetType.put(MapName.runStmtsHA, 0);
    	 mapBitSetType.put(MapName.fieldPts, 1);
    	 mapBitSetType.put(MapName.sfieldPts, 1);
    	 mapBitSetType.put(MapName.afieldPts, 1);
    	 mapBitSetType.put(MapName.MHP, 0);
    	 mapBitSetType.put(MapName.sync, 0);
    	 mapBitSetType.put(MapName.syncHA, 0);
    	 mapBitSetType.put(MapName.monitorStmts, 0);
    	 mapBitSetType.put(MapName.invMonitorStmts, 0);
    	 mapBitSetType.put(MapName.kill, 0);
    	 mapBitSetType.put(MapName.notifyStmts, 0);
    	 mapBitSetType.put(MapName.methStmts, 0);
    	 mapBitSetType.put(MapName.methRep, 0);
    	 mapBitSetType.put(MapName.mhpCopyTo, 0);
    	 mapBitSetType.put(MapName.invMethStmts, 3);
    	 mapBitSetType.put(MapName.funcsAtCallSite, 3);
    	 mapBitSetType.put(MapName.callSites, 0);
    	 mapBitSetType.put(MapName.ifieldPts, 1);
    	 mapBitSetType.put(MapName.ivarPts, 1);
    	 mapBitSetType.put(MapName.refFields, 2);
//    	 mapBitSetType.put(MapName.refFieldsIn, 2);
//    	 mapBitSetType.put(MapName.stRefFields, 2);
    	 mapBitSetType.put(MapName.escapeAt, 1);
    	 mapBitSetType.put(MapName.reachableFuncs, 3);
    	 mapBitSetType.put(MapName.fieldsOf, 2);
    	 
    	 /*
    	  * Get map for a name
    	  */
    	 mapForName.put(MapName.varPts,varPts);
    	 mapForName.put(MapName.ivarPts,ivarPts);
    	 mapForName.put(MapName.runStmts, runStmts);
    	 mapForName.put(MapName.runStmtsHA, runStmtsIP);
    	 mapForName.put(MapName.fieldPts, fieldPts);
    	 mapForName.put(MapName.ifieldPts, ifieldPts);
    	 mapForName.put(MapName.MHP, MHP);
    	 mapForName.put(MapName.sync, sync);
    	 mapForName.put(MapName.monitorStmts, monitorStmts);
    	 mapForName.put(MapName.invMonitorStmts, invMonitorStmts);
    	 mapForName.put(MapName.kill, kill);
    	 mapForName.put(MapName.notifyStmts, notifyStmts);
    	 mapForName.put(MapName.funcsAtCallSite, callSiteMeths);
    	 mapForName.put(MapName.callSites, callSites);
    	 mapForName.put(MapName.methStmts, methStmts);
    	 mapForName.put(MapName.methRep, methRep);
    	 mapForName.put(MapName.mhpCopyTo, mhpCopyTo);
    	 mapForName.put(MapName.invMethStmts, invMethStmts);
    	 mapForName.put(MapName.refFields, refFields);
//    	 mapForName.put(MapName.refFieldsIn, refFieldsIn);
//    	 mapForName.put(MapName.stRefFields, stRefFields);
    	 mapForName.put(MapName.sfieldPts, sfieldPts);
    	 mapForName.put(MapName.afieldPts, afieldPts);
    	 mapForName.put(MapName.reachableFuncs, reachableFuncs);
    	 mapForName.put(MapName.fieldsOf, fieldsOf);
    	 
    	 /*
    	  * special purpose maps
    	  */
//    	 mapForName.put(MapName.diffMap, diffMap);
    	 mapForName.put(MapName.exclField, exclField);
    	 mapForName.put(MapName.escapeAt, escapeAt);
    	 mapForName.put(MapName.must, must);
    	 mapForName.put(MapName.cardOne, cardOne);
    }
    
    public static final String TEXT_RED = "\u001B[31m";
    public static final String TEXT_RESET = "\u001B[0m";
    public static final String TEXT_GREEN = "\u001B[32m";
    public static final String TEXT_BLUE = "\u001B[34m";
   
    int conscount;
    int cycles;
    Node searchSource = new Node(null,null);
    /*stat measure*/
    int memConsCount;
    int propConsCount;
    int funConsCount;
    int condConsCount;
    int totcons = 0;
    int totmem = 0;
    int totprop = 0;
    int totfunc = 0;
    int totcond = 0;
    long genTime = 0L;
    long solveTime = 0L;
    PrintWriter printWriter; 
    PrintWriter printWriterLib; 
    ArrayList<PropagateTask> propTasks = new ArrayList<PropagateTask>();
   // int count = 0;
	int clCount = 0;
	int libCount = 0;
	int bothLib = 0;
	String path;
	Arg arg;
    long MHPCount = 0;
    long pointCount = 0;
    long sparkPointCount = 0;
    long callEdgeCount = 0;
    double monomorphicCount =0;
    double monoPercent = 0;
    Map<SootMethod,Set<Stmt>> callerStmts = new HashMap<SootMethod,Set<Stmt>>();
    Set<Stmt> callStmts = new HashSet<Stmt>();
    int noofthreads = 4;
    ExecutorService pool ;
//    Map<SootMethod,Set<SootField>> methFields = new ConcurrentHashMap<SootMethod,Set<SootField>>();
    ArrayList<SootField> sootFieldList = new ArrayList<SootField>();
    int intStmtCount = 0;
    int fieldStmtCount = 0;
    int MHPStmtCount = 0;
    SootClass collectionRepClass;
    SootField collectionEleField;
    SootMethod main;
    Analyzer analyzer;
    int iterRound = 0;
    int iterChanges = 0;
    Map<SootMethod,Set<Stmt>> loadStores = new ConcurrentHashMap<>();
    Map<SootField,Set<Stmt>> loadf = new ConcurrentHashMap<>();
    Map<SootField,Set<Stmt>> storef = new ConcurrentHashMap<>();
    
    /*
     * For rebuttal
     */
//    ConcurrentHashMap<SootMethod,Set<Node>> mustNodes = new ConcurrentHashMap<>();
    ConcurrentHashMap<SootMethod,Set<Stmt>> starts = new ConcurrentHashMap<>();
    ConcurrentHashMap<SootMethod,Set<Stmt>> joins = new ConcurrentHashMap<>();
    ConcurrentHashMap<SootMethod,SootMethod> runs = new ConcurrentHashMap<>();
    ConcurrentHashMap<SootMethod,Set<Stmt>> execSubmits = new ConcurrentHashMap<>();
    ConcurrentHashMap<SootMethod,SootMethod> runOrCall = new ConcurrentHashMap<>();
    int numruns = 0;
    ConcurrentHashMap<SootMethod,Set<Stmt>> waits = new ConcurrentHashMap<>();
    ConcurrentHashMap<SootMethod,Set<Stmt>> notifys = new ConcurrentHashMap<>();
    int mustRounds = 0;
    Map<Node,Set<Integer>> mustUpdated = new HashMap<>();
   
    LoopFinder lf = new LoopFinder();
    
    public void generateAndAddCons(Generator gen, FunctionalConstraint fc, Body b) throws SecurityException, IOException{
    	gen.analyzer = analyzer.getAnalyzer();
		gen.analyzer.init(gen, fc);
		gen.generate(b, fc);
		/*
		 * synchronized not required for non-parallel gen.
		 * But doesn't make a difference
		 */
		synchronized(this) {
			methLocals.put(fc.method, fc.methLocals);
			
			addMethRep(fc.method, gen.hasParallelConst, fc.methStmts, (Stmt)b.getUnits().getFirst() );
//			addMethRep(fc.method, true, fc.methStmts );
			
			methRDef.put(fc.method, gen.reachDefMap);
    		if(!gen.hasParallelConst)
    			skipped.put(fc.method,gen.firstS);
			
			
				
//				for(SootMethod m : gen.ignoredMeths) {
//					recordProcessed(m);
//					recordCall(fc.method, m);
//				}
			
//			if(!fc.method.getDeclaringClass().isLibraryClass()) {
    		if(gen.retStmts != null) {
    			BitSet retStmts = methRet.get(fc.method);
    			if(retStmts == null) {
    				retStmts = new BitSet();
    				methRet.put(fc.method, retStmts);
    			}
    			Iterator<Stmt> itr = gen.retStmts.iterator();
    			while(itr.hasNext()) {
    				Stmt st = itr.next();
    				int ind = stmtList.indexOf(st);
    				if(ind==-1) {
//    					System.out.println("");	    	
    					continue;
    					}
    				retStmts.set(ind);
    			}
    		}
    		gen.analyzer.ptConsGen.genRefFieldCopy();
    		if(arg.mhp) {
    		if(gen.hasParallelConst) {
    			hasPC.add(fc.method);
    		}
    		else {
    			/*
    			 * Copy MHP to the caller.
    			 * If parallel constructs were present, 
    			 * the return statements would've generated the
    			 * required MHP
    			 */
    			Stmt myRep = noPCMRep.get(fc.method);
    			if(fc.caller!=null && fc.callSiteSuccs!=null)
    				gen.analyzer.mhpConsGen.genRetMHPToCaller(myRep,fc.caller.method,fc.callSiteSuccs);
    		}
    		}

//			}
			gen.analyzer.genEveryMethod();
			gen.analyzer.addConsToSolverLists();
    		
		}
    }
   }
class Task implements Runnable{
	Body b;
	FunctionalConstraint fc;
	boolean alreadyProcessed;
	Solver solver;
	CountDownLatch cdl;

	public Task(Body b, FunctionalConstraint fc, Solver solver) {
		super();
		this.b = b;
		this.fc = fc;
		this.solver = solver;
	}

	@Override
	public void run() {
		// TODO Auto-generated method stub
		try {
			Generator gen = new Generator();
			solver.generateAndAddCons(gen, fc, b);
    		cdl.countDown();
		} catch (SecurityException | IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		//return "success";
	}
	
}




