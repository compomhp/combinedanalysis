package compomhp;

public abstract class Constraint {
	
	public ConstraintName name = ConstraintName.GENERAL;
	
	Object outerCondObj = null;
	boolean useOuterCondObj = false;
	
	abstract public String printConstraint(); 
	abstract public void insert();
	abstract public Constraint getCopy();
	abstract public Constraint updateCond(Object obj, int cardinality);
	abstract public void addToList();
	ConstType constType;
}
