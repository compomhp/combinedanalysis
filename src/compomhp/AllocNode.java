package compomhp;

import java.util.Objects;

import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.Stmt;
import soot.util.Chain;

public class AllocNode {
  public Stmt allocSite;
  public SootClass anclass;
  public int count;
  
  boolean isInLoop=false;
  

  
 // public boolean arrayType = false;
  public SootMethod allocSiteMeth;
  public String memString() {
	  String s = "O"+count;
	 
		
		return s;
	}
  public String printAllocSite() {
	  String s = null;
	  if(this==Solver.v().bottom) {
		  s = "bottom";
		  return s;
	  }
	  else if(this==Solver.v().nullRef)
	  {
		  s = "null";
		  return s;
	  }
//	  if(allocSiteMeth==null) {
//		  System.out.println("stop");
//	  }
		  s = memString()+" at "+allocSite+" in method "+allocSiteMeth.getSignature();
		  return s;
  }
  public AllocNode() {
	  
  }
//@Override
//public int hashCode() {
//	return Objects.hash(allocSite, allocSiteMeth);
//}
//@Override
//public boolean equals(Object obj) {
//	if (this == obj)
//		return true;
//	if (obj == null)
//		return false;
//	if (getClass() != obj.getClass())
//		return false;
//	AllocNode other = (AllocNode) obj;
//	return Objects.equals(allocSite, other.allocSite) && Objects.equals(allocSiteMeth, other.allocSiteMeth);
//}
  
}
