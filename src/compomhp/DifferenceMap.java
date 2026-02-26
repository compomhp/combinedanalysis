package compomhp;

import soot.Local;
import soot.jimple.Stmt;

public class DifferenceMap {
	static final Object globalDummy = new Object();
	public MapName leftDiffMap;
	public MapName rightDiffMap;
	public Object leftDiffVar;
	public Object rightDiffVar;
	//public Object cond
	public Object condObj;
	public DifferenceMap(MapName leftDiffMap, MapName rightDiffMap, Object leftDiffVar, Object rightDiffVar) {
		super();
		this.leftDiffMap = leftDiffMap;
		this.rightDiffMap = rightDiffMap;
		this.leftDiffVar = leftDiffVar;
		this.rightDiffVar = rightDiffVar;
		//condObj = null;
	}
	public String toString() {
		StringBuilder  sb = new StringBuilder();
		String left="",right="";
		if(leftDiffVar instanceof Local) {
			left = leftDiffMap+"("+((Local)leftDiffVar).getName()+")";
			
		}
		else if(leftDiffVar instanceof Stmt) {
			left = leftDiffMap+"("+Integer.toString(leftDiffVar.hashCode())+")";
		}
		else
			left = leftDiffMap+"("+leftDiffVar+")";
		if(rightDiffVar instanceof Local) {
			right = rightDiffMap+"("+((Local)rightDiffVar).getName()+")";
			
		}
		else if(rightDiffVar instanceof Stmt) {
			right = rightDiffMap+"("+Integer.toString(rightDiffVar.hashCode())+")";
		}
		else
			right = rightDiffMap+"("+rightDiffVar+")";
		sb.append(left+" - "+right);
		return sb.toString();
		
	}
	public void setCond(Object cond) {
		if(leftDiffVar == globalDummy) {
			leftDiffVar = cond;
		}
		else if(rightDiffVar == globalDummy) {
			rightDiffVar = cond;
		}
	}
}
