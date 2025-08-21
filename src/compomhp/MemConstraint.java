package compomhp;

import java.util.Iterator;
import java.util.Set;

import soot.Hierarchy;
import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.jimple.Stmt;
import soot.util.Chain;


public class MemConstraint extends Constraint{

	/*
	 * bitPos in destMap(X)
	 * bitPos = get position of i in stmtList or allocNodes based on its type
	 */
	Object i;
	Object X;
	boolean isAlloc;
	MapName destMap;
	String indVar;
	boolean addBottoFields = false;
	
	public MemConstraint(Object i, Object x, boolean isAlloc, MapName destMap, ConstType ct) {
		super();
		this.i = i;
		X = x;
		this.isAlloc = isAlloc;
		this.destMap = destMap;
		this.indVar = "";
		this.constType = ct;
		
	}

	@Override
	public void insert() {
		// TODO Auto-generated method stub
		Solver solver = Solver.v();
//		if(name==ConstraintName.METHOD_CALL) {
//			System.out.println("stop");
//		}
//		if(name==ConstraintName.METHOD_CALL) {
//			System.out.println("stop");
//		}
		solver.insertMem(i, X, isAlloc, destMap);
		
	}
	@Override
	public String printConstraint() {
		// TODO Auto-generated method stub
		StringBuilder sb = new StringBuilder();
		sb.append("Constraint "+name+": ");
		if(i instanceof Stmt && X==null) {
			sb.append(((Stmt)i)+" in "+destMap+"("+indVar+")");
		}
		else if(isAlloc) {
			/*Alloc Node*/
			//sb.append("O"+bitPos+" in ptsTo("+((Local)X).getName()+")");
		}
		else if(i == null) {
			sb.append(indVar +" in "+destMap+"("+X+")");
		}
		return sb.toString();
	}
	public static String printConstraint(Object i, Object x, int bitPos, MapName destMap) {
		StringBuilder sb = new StringBuilder();
		//sb.append("Constraint "+name+": ");
		if(i instanceof Stmt && x==null) {
			sb.append(((Stmt)i)+" in "+destMap+"(x)");
		}
		else if(bitPos != -1) {
			/*Alloc Node*/
			//sb.append("O"+bitPos+" in ptsTo("+((Local)X).getName()+")");
		}
		else if(i == null) {
			sb.append("x" +" in "+destMap+"("+x+")");
		}
		return sb.toString();
	}

	public MemConstraint(MemConstraint mc) {
		
		this.name = mc.name;
		this.i = mc.i;
		X = mc.X;
		this.isAlloc = mc.isAlloc;
		this.destMap = mc.destMap;
		this.indVar = mc.indVar;
		
		this.constType = mc.constType;
//		this.cardinality = mc.cardinality;
//		this.isExistsCond = mc.isExistsCond;
		this.outerCondObj = mc.outerCondObj;
		this.useOuterCondObj = mc.useOuterCondObj;
		this.addBottoFields = mc.addBottoFields;
		
	}
	public MemConstraint(ConstType ct) {
		this.constType = ct;
	}
	@Override
	public Constraint getCopy() {
		// TODO Auto-generated method stub
		return new MemConstraint(this);
	}

	@Override
	public Constraint updateCond(Object obj, int cardinality) {
		if(addBottoFields) {
			AllocNode an = (AllocNode)obj;
			

			SootClass sc = an.anclass;
			
			if(sc!=null) {
				if(destMap == MapName.fieldPts) {

					AllocNode anode = (AllocNode)obj;
					Set<AllocNodeField> anfs = HelperAnalysis.fieldListIP.get(anode);
					Stmt st = (Stmt)X;
					SootMethod m = Solver.v().myS.get(st);
					if(anfs != null) {
						
					for(AllocNodeField anf : anfs) {
						SootField f = anf.sf;
						Set<SootField> mf = HelperAnalysis.methFields.get(m);
						if(mf!=null && mf.contains(f)) {
							StmtAllocNodeField sanf = new StmtAllocNodeField(st,anf);
							MemConstraint dup = new MemConstraint(this);
							dup.X = sanf;dup.addBottoFields = false;
							dup.addToList();
						}
					}
					}
				}
//				else if(destMap == MapName.ifieldPts) {
//					if((sc.resolvingLevel() == SootClass.DANGLING)) {
//						return null;
//					}
//					Chain<SootField> ch = sc.getFields();
//					Iterator<SootField> itr = ch.iterator();
//					while(itr.hasNext()) {
//						SootField sf = itr.next();
//						if(!sf.isStatic() && CheckInteresting.isInterestingType(sf.getType())) {
//							MemConstraint dup = new MemConstraint(this);
//							AllocNodeField anf = new AllocNodeField(an,sf);
//							dup.X = anf;
//	//						dup.name=ConstraintName.ARR_STORE;
//							dup.addToList();
//						}
//					}
//				}
				else if(destMap == MapName.afieldPts) {
					if((sc.resolvingLevel() == SootClass.DANGLING)) {
						return null;
					}
					if(Solver.v().arg.combined) {
						AllocNode anode = (AllocNode)obj;
						Set<AllocNodeField> anfs = HelperAnalysis.fieldListIP.get(anode);
						if(anfs != null) {
						for(AllocNodeField anf : anfs) {
							SootField sf = anf.sf;
							if(Solver.arrayEleField == sf) {
								MemConstraint dup = new MemConstraint(this);
								dup.X = anf;
								dup.addBottoFields = false;
								dup.addToList();
							}
						}
					}
//					Chain<SootField> ch = sc.getFields();
//					Iterator<SootField> itr = ch.iterator();
//					while(itr.hasNext()) {
//						SootField sf = itr.next();
////						if(!sf.isStatic() && Solver.isInterestingType(sf.getType())) {
//							MemConstraint dup = new MemConstraint(this);
//							AllocNodeField anf = new AllocNodeField(an,sf);
//							dup.X = anf;
//	//						dup.name=ConstraintName.ARR_STORE;
//							dup.addToList();
////						}
//					}
					}
				}
			}
			return null;
		}
		
		else if(destMap==MapName.fieldPts) {
			
			if(obj instanceof AllocNodeField) {
				if(X instanceof Stmt) {
					StmtAllocNodeField sanfC = new StmtAllocNodeField((Stmt)X, (AllocNodeField)obj);
					X = sanfC;
				}
				else {
				StmtAllocNodeField sanf = (StmtAllocNodeField)X;
				StmtAllocNodeField sanfC = new StmtAllocNodeField(sanf.st, (AllocNodeField)obj);
				X = sanfC;
				}
			}
		}
		if(X == null) {
			
			X = obj;
		}
		else if(i ==null) {
			i = obj;
		}
		else if(i instanceof AllocNodeField) {
			AllocNodeField anf = new AllocNodeField((AllocNode)obj, ((AllocNodeField)i).sf);
			i = anf;
		}
		
		return this;
	}
	@Override
	public void addToList() {
		// TODO Auto-generated method stub
		Solver.v().memCons.add(this);
	}
	
	
}
