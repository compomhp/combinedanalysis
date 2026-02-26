package compomhp;


import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import soot.SootField;
import soot.SootMethod;
import soot.jimple.Stmt;





public class ConditionalConstraint extends Constraint{
	/*
	 * r in pts(v1) -> pts(v2) sub pts(r,f)
	 */
	static Map<Constraint,Constraint> conElseCon = new HashMap<>();
	static Set<Constraint> storeSolvedCons = new HashSet<>();
	static Set<Constraint> notStrongduetoCardinality= new HashSet<>();
		Object condVariable; /*v1*/
		Constraint constraint;
		Constraint elseConstraint;
		MapName mapType;
		
		
		/*
		 * if member is solver.existCond; the condition checks if such member exists or not
		 */
		int memberPos = -1;
		boolean isExistsCond = false;
		
		//Object outerCondVar = null;
		//ArrayList<CondVar> conditions;
		String meth;
		
		public ConditionalConstraint(
				Object condVariable, Constraint c, MapName mapType, Constraint elseConstraint, ConstType ct) {
			
			//super();
			this.condVariable = condVariable;
			this.constraint = c;
			
			this.mapType = mapType;
			//this.memberPos = member;
			this.elseConstraint = elseConstraint;
			this.constType = ct;
			
		}
		
		
		
	@Override
	public String printConstraint() {
		StringBuilder sb = new StringBuilder();
		sb.append("Constraint "+name+": ");
		String str ="";

		
		sb.append(constraint.printConstraint());
		return sb.toString();
	}
	
	public void insert() {
		Solver solver = Solver.v();
		
//		constraint.isMustCons = isMustCons;
//		constraint.cardinality = cardinality;
//		constraint.isSingleCaller = isSingleCaller;
//		constraint.isExistsCond = isExistsCond;
		solver.insertCond(condVariable,constraint, mapType, memberPos, elseConstraint);
	}


	public ConditionalConstraint(ConditionalConstraint cc) {
		this.name = cc.name;
		this.condVariable = cc.condVariable;
		this.constraint  = cc.constraint;
		this.elseConstraint = cc.elseConstraint;
		//this.condVarType = cc.condVarType;
		this.mapType = cc.mapType;
		this.memberPos = cc.memberPos;
		this.outerCondObj = cc.outerCondObj;
		this.useOuterCondObj = cc.useOuterCondObj;
		this.constType = cc.constType;
//		this.cardinality = cc.cardinality;
		this.isExistsCond = cc.isExistsCond;
		
		//this.condIndVar = cc.condIndVar;
		//this.indVarType = cc.indVarType;
	}



	@Override
	public Constraint getCopy() {
		// TODO Auto-generated method stub
		return new ConditionalConstraint(this);
	}



	@Override
	public Constraint updateCond(Object obj, int cardinality) {
//		if(useOuterCondObj)
//			obj = outerCondObj;
		
		if(condVariable == null) {
			if(useOuterCondObj)
				condVariable = outerCondObj;
			else
			condVariable = obj;
		}
		 if(constraint instanceof ConditionalConstraint) {
			 ConditionalConstraint cc = (ConditionalConstraint)constraint;
			// if(cc.useOuterCondObj)
			 cc.outerCondObj = obj;
		 }
		Constraint dup = null;
		if(isExistsCond) {
			/*
			 * In case of existence condition, just check if the member exists and solve the dependent constraint
			 */
			
			Solver solver = Solver.v();
			int i = Solver.v().mapBitSetType.get(mapType);
			if(i==1) {
				memberPos = solver.allocNodes.indexOf(obj);
			}
			else if(i == 0) {
//				System.out.println("Checking existence of "+obj+" in "+mapType);
				memberPos = solver.stmtList.indexOf(obj);
			}
//			if(memberPos == -1) {
//				System.out.println("caught");
//			}
//			try {
			BitSet bArray;
			if(mapType==MapName.runStmtsHA) {
				AllocNode a = (AllocNode)condVariable;
				bArray = solver.getBitSetFor(mapType, a.anclass);
			}
			else
			bArray = solver.getBitSetFor(mapType, condVariable);
//			if(bArray == null || bArray.cardinality()==0) {
//				if(condVariable instanceof AllocNode) {
//					bArray = solver.getBitSetFor(mapType, solver.bottom);
//				}
//			}
			if(bArray.get(memberPos)) {
//				System.out.println("Found for "+mapType+" "+condVariable);
				if(constraint != null) {
					dup = constraint.getCopy(); 
					dup = dup.updateCond(obj, cardinality);
				}
//				else if(elseConstraint!=null) {
//					elseConstraint.updateCond(obj);
//					return elseConstraint;
//				}
				return dup;
			}
			else {
//				System.out.println("Not Found for "+mapType+" "+condVariable);
				if(elseConstraint!=null) {
					dup = elseConstraint.getCopy(); 
					dup = dup.updateCond(obj, cardinality);
//					if(name==ConstraintName.INNER_COND) {
//						elseConstraint.name=ConstraintName.CAST_COPY;
//					}
				}
				return dup;
			}
//			}catch(Exception e) {
//				System.out.println("line conditional constraint 159"+e);
//			}
			//memberPos = obj;
		}
		if(mapType == MapName.cardOne) {
			Constraint use = null;
			if(cardinality==1) {
				use = constraint;
			}
			else {
				use = elseConstraint;
			}
			
			if(use != null) {
				dup = use.getCopy();
				dup = dup.updateCond(obj, cardinality);
				return dup;
			}
				return null;
			
		}
		if(mapType == MapName.must) {
			if(obj instanceof Stmt) {
				Stmt st = (Stmt)obj;
//				if(st != null) {
					Constraint use = null;
					Solver solver = Solver.v();
					SootMethod m;
					if(solver.methOfRep.containsKey(st)) {
						m = solver.methOfRep.get(st);
					}
					else
						m = solver.myS.get(st);
					Set set = solver.callerStmts.get(m);
					if(set==null) {
						use = constraint;
					}
					else if(set.size()==1) { //checks for call sites==1
						Stmt callSite = (Stmt)set.iterator().next();
						boolean isSummary = Solver.v().schk.isSummaryStNew(callSite, false, null);
						
						if(!isSummary) {
							use = constraint;
							/*
							 * If s is not inserted, in future the call sites of func(s) may change
							 * which requires a conditionalconstraint to track it 
							 */
							if(elseConstraint!=null) {
							MemConstraint c = (MemConstraint)elseConstraint.getCopy();
							c.i = st;
							ConditionalConstraint one = new ConditionalConstraint(m, null, MapName.cardOne, c, ConstType.mhp );
							ConditionalConstraint cc = new ConditionalConstraint(m, one, MapName.callSites,null, ConstType.mhp);
							cc.addToList();
							}
							
						}
						else {
							use = elseConstraint;
						}
					}
					else {
						use = elseConstraint;
						
					}
					if(use != null) {
						dup = use.getCopy();
						dup = dup.updateCond(obj, cardinality);
						return dup;
					}
						return null;
//				}
			}
			else if(obj instanceof AllocNode) {
				AllocNode an = (AllocNode)obj;
//				if(an.allocSite != null) {
				Constraint use = null;
				
				if(cardinality==1) {
					boolean isSummary = false;
					if(an.allocSite!=null) {
						StmtLocal sl = (StmtLocal)condVariable;
						Stmt st = sl.st;
						isSummary = Solver.v().schk.isSummaryStNew(an.allocSite, true, st);
					}
					
					if(!isSummary) {
						use = constraint;
						if(use.name == ConstraintName.STORE)
							storeSolvedCons.add(constraint);
					}
					else {
						use = elseConstraint;
						if(use.name == ConstraintName.STORE)
							storeSolvedCons.add(elseConstraint);
					}
				}
					else {
						use = elseConstraint;
						if(use.name == ConstraintName.STORE) {
							storeSolvedCons.add(elseConstraint);
							notStrongduetoCardinality.add(elseConstraint);
						}
					}
					if(use != null) {
						dup = use.getCopy();
						dup = dup.updateCond(obj, cardinality);
						return dup;
					}
						return null;
//				}
			}
		}
		else if(mapType == MapName.methFields) {
			AllocNodeField anf = (AllocNodeField)obj;
			SootField sf = anf.sf;
			SootMethod sm = (SootMethod)condVariable;
			Set<SootField> fields = HelperAnalysis.methFields.get(sm);
			if((fields != null && fields.contains(sf)) /*|| anf.an.botReach*/) {
				dup = constraint.getCopy();
				dup = dup.updateCond(obj, cardinality);
				return dup;
			}
			return null;
		}

		else if(mapType == MapName.methFieldsIn) {
			AllocNodeField anf = (AllocNodeField)obj;
			SootField sf = anf.sf;
			SootMethod sm = (SootMethod)condVariable;
			Set<SootField> fields = HelperAnalysis.methAccessedFlds.get(sm);
			if((fields != null && fields.contains(sf)) /*|| anf.an.botReach*/) {
				dup = constraint.getCopy();
				dup = dup.updateCond(obj, cardinality);
				return dup;
			}

			return null;
		}
		 else if(mapType == MapName.exclField) {
				AllocNodeField anf = (AllocNodeField)obj;
				SootField sf = anf.sf;
				SootField exf = (SootField)condVariable;
				if(exf != sf) {
					dup = constraint.getCopy();
					dup = dup.updateCond(obj, cardinality);
					return dup;
				}
				return null;
			}
		
		return this;
	}
	
	
	@Override
	public void addToList() {
		// TODO Auto-generated method stub
		Solver.v().condCons.add(this);
	}
}
