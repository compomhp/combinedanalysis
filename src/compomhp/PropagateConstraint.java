package compomhp;





import soot.Local;
import soot.SootMethod;
import soot.jimple.Stmt;


public class PropagateConstraint extends Constraint {

	/*
	 * X subset Y
	 */
	Object left;
	Object right;
	MapName leftMap;
	MapName rightMap;
	
	
	
	
	public PropagateConstraint(Object left, Object right,MapName leftMap, MapName rightMap, ConstType ct) {
		this.left = left;
		this.right = right;
		this.leftMap = leftMap;
		this.rightMap = rightMap;
		this.constType = ct;
		//this.meth = meth;
	}
	@Override
	public String printConstraint() {
		StringBuilder sb = new StringBuilder();
		sb.append("Constraint "+name+": ");
		if(leftMap.equals(MapName.fieldPts)&&rightMap.equals(MapName.varPts)) {
			Local l = (Local)right;
			sb.append("fieldPts(r"+","+")"+" subseteq "+"varPts("+l.getName()+") ");
		}
		else if(leftMap.equals(MapName.varPts)&&rightMap.equals(MapName.fieldPts)) {
			Local l = (Local)left;
			
			sb.append("varPts("+l.getName()+") "+" subseteq "+"fieldPts(r"+","+")");
		}
		else {
			String ls = "";
			String rs = "";
			if(left == null)
				ls = "";
			else if(left instanceof Local) {
				ls = leftMap+"("+((Local)left).getName()+")";
				
			}
			else if(left instanceof Stmt) {
				ls = leftMap+"("+left.toString()+")";
			}
			else if(left instanceof DifferenceMap)
				ls = left.toString();
			if(right == null)
				rs = "";
			if(right instanceof Local) {
				rs = rightMap+"("+((Local)right).getName()+")";
			}
			else if(right instanceof Stmt) {
				rs = rightMap+"("+right.toString()+")";
			}
			else if(right instanceof DifferenceMap)
				rs = right.toString();
			sb.append(ls+" subseteq "+rs);
		}
		return sb.toString();
	}

	@Override
	public void insert() {
		Solver solver = Solver.v();
//		if(right==null) {
//			Stmt l = (Stmt)left;
//			SootMethod m = solver.myS.get(l);
//			System.out.println(m.getSignature());
//		}
			
		solver.insertProp(left, right, leftMap, rightMap);
		
		
		
	}
	public static String printConstraint(Object left, Object right,MapName leftMap, MapName rightMap) {
		StringBuilder sb = new StringBuilder();
		//sb.append("Constraint "+name+": ");
		if(leftMap.equals(MapName.fieldPts)&&rightMap.equals(MapName.varPts)) {
			Local l = (Local)right;
			sb.append("fieldPts(r"+","+")"+" subseteq "+"varPts("+l.getName()+") ");
		}
		else if(leftMap.equals(MapName.varPts)&&rightMap.equals(MapName.fieldPts)) {
			Local l = (Local)left;
			
			sb.append("varPts("+l.getName()+") "+" subseteq "+"fieldPts(r"+","+")");
		}
		else {
			String ls = "";
			String rs = "";
			if(left == null)
				ls = "";
			else if(left instanceof Local) {
				ls = leftMap+"("+((Local)left).getName()+")";
				
			}
			else if(left instanceof Stmt) {
				ls = leftMap+"("+left.toString()+")";
			}
			else if(left instanceof DifferenceMap)
				ls = left.toString();
			if(right == null)
				rs = "";
			if(right instanceof Local) {
				rs = rightMap+"("+((Local)right).getName()+")";
			}
			else if(right instanceof Stmt) {
				rs = rightMap+"("+right.toString()+")";
			}
			else if(right instanceof DifferenceMap)
				rs = right.toString();
			sb.append(ls+" subseteq "+rs);
		}
		return sb.toString();
	}
		
	public PropagateConstraint(PropagateConstraint pc) {
		this.name = pc.name;
		this.left = pc.left;
		this.right = pc.right;
		this.leftMap = pc.leftMap;
		this.rightMap = pc.rightMap;
		
		this.constType = pc.constType;
		
//		this.cardinality = pc.cardinality;
		this.outerCondObj = pc.outerCondObj;
		this.useOuterCondObj = pc.useOuterCondObj;
		//this.f = pc.f;
	}
	public PropagateConstraint(ConstType ct) {
		this.constType = ct;
	}
	@Override
	public Constraint getCopy() {
		// TODO Auto-generated method stub
		return new PropagateConstraint(this);
	}
	@Override
	public Constraint updateCond(Object obj, int cardinality) {
		if(useOuterCondObj) {
			obj = outerCondObj;
		}
		// TODO Auto-generated method stub
		Solver solver = Solver.v();
		if(left == null) {
			left = obj;
		}
		
		else if(leftMap == MapName.fieldPts){
			
			if(solver.arg.bot && obj instanceof AllocNode && obj == solver.bottom) {
				/*
				 * load instr
				 * add bottom to LHS and its reachables
				 */
				MemConstraint mc = new MemConstraint(solver.bottom, right, false, rightMap, ConstType.pts);
				mc.addToList();
			}

			left = updateAnfs(left,obj);
			
			if(left==null)
				return null;
//			AllocNodeField anf = new AllocNodeField((AllocNode)obj, ((StmtAllocNodeField)left).anf.sf);
//			left = anf;
//			AllocNodeField anf = ((StmtAllocNodeField)left).anf;
//				MemConstraint m  = new MemConstraint(anf, anf.an, false, MapName.fieldsOf, ConstType.pts);
//				m.addToList();

		}

		else if(leftMap == MapName.afieldPts || leftMap == MapName.ifieldPts){

				if(solver.arg.bot && obj instanceof AllocNode && obj == solver.bottom) {
					/*
					 * load instr
					 * add bottom to LHS and its reachables
					 */
					MemConstraint mc = new MemConstraint(solver.bottom, right, false, rightMap, ConstType.pts);
					mc.addToList();
					
				}
			
			AllocNodeField anf = new AllocNodeField((AllocNode)obj, ((AllocNodeField)left).sf);
			left = anf;
			if(anf.an != solver.bottom) {
				MemConstraint m  = new MemConstraint(anf, anf.an, false, MapName.fieldsOf, ConstType.pts);
				m.addToList();
			}
		}
		
		if(right == null) {
			right = obj;
		}
		
		else if(rightMap == MapName.fieldPts){
			
			if(solver.arg.bot && obj instanceof AllocNode && obj == solver.bottom) {
				/*
				 * store instr, add bottom to everything reacahble from RHS
				 */
				if(left!=null && left instanceof StmtLocal) {
//					propBotToReachables((StmtLocal)left);
					
					solver.sUtil.propBotToReachableFields(left, ((StmtLocal)left).st);
					
				}
			}
			right = updateAnfs(right,obj);
			if(right==null)
				return null;
//			AllocNodeField anf = ((StmtAllocNodeField)right).anf;
//			MemConstraint m  = new MemConstraint(anf, anf.an, false, MapName.fieldsOf, ConstType.pts);
//			m.addToList();

		}

		else if(rightMap == MapName.afieldPts || rightMap == MapName.ifieldPts){

				if(solver.arg.bot && obj instanceof AllocNode && obj == solver.bottom) {
					/*
					 * store instr, add bottom to everything reacahble from RHS
					 */
					if(left!=null /*&& left instanceof Local*/) {
						
						solver.sUtil.propBotToReachableFields(left, null); 
//						propBotToReachablesInSens(left,leftMap, rightMap);
						
					}
	
				}
				
			AllocNodeField anf = new AllocNodeField((AllocNode)obj, ((AllocNodeField)right).sf);
			right = anf;
			if(anf.an != solver.bottom) {
				MemConstraint m  = new MemConstraint(anf, anf.an, false, MapName.fieldsOf, ConstType.pts);
				m.addToList();
			}
			
		
		}
		
		return this;
	}

	public StmtAllocNodeField updateAnfs(Object lr, Object obj) {
	
		AllocNodeField anf;
		StmtAllocNodeField ret = null;
		if(lr instanceof Stmt) {
			anf = (AllocNodeField)obj;
			ret = new StmtAllocNodeField((Stmt)lr, anf);
		}
		if(lr instanceof StmtAllocNodeField) {
			StmtAllocNodeField anfs = (StmtAllocNodeField)lr;
			if(obj instanceof AllocNode) {
				
				anf = new AllocNodeField((AllocNode)obj, anfs.anf.sf);

				ret = new StmtAllocNodeField(anfs.st, anf);
			}
			else if(obj instanceof Stmt) {
				ret = new StmtAllocNodeField((Stmt)obj, anfs.anf);

			}
			else {
			 anf = (AllocNodeField)obj;
			ret = new StmtAllocNodeField(anfs.st, anf);

			}
			
		}
		
		return ret;
	}
	
	@Override
	public void addToList() {
		// TODO Auto-generated method stub
		Solver.v().propCons.add(this);
	}
//	private void propBotToReachables(StmtLocal rhs) {
//		Solver solver = Solver.v();
//		MemConstraint addBot = new MemConstraint(solver.bottom, rhs.st, false, MapName.fieldPts, ConstType.pts);
//		addBot.addBottoFields = true;
//		ConditionalConstraint cc = new ConditionalConstraint(rhs, addBot, MapName.varPts, null, ConstType.pts);
//		cc.addToList();
//		
//	}
//	
//	private void propBotToReachablesInSens(Object key, MapName m, MapName destMap) {
//		Solver solver = Solver.v();
//		MemConstraint addBot = new MemConstraint(solver.bottom, null, false, m, ConstType.pts);
//		ConditionalConstraint c = new ConditionalConstraint(null, addBot, MapName.fieldsOf, null, ConstType.pts);
//		ConditionalConstraint cc = new ConditionalConstraint(key, c,m, null, ConstType.pts);
//		cc.addToList();
//		
//	}
	
}
