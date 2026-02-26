package compomhp;

import java.util.Objects;

import soot.jimple.Stmt;

public class StmtAllocNode {
	Stmt st;
	AllocNode an;
	public StmtAllocNode(Stmt st, AllocNode an) {
		super();
		this.st = st;
		this.an = an;
	}
	@Override
	public int hashCode() {
		return Objects.hash(an, st);
	}
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		StmtAllocNode other = (StmtAllocNode) obj;
		return Objects.equals(an, other.an) && Objects.equals(st, other.st);
	}
	
	
}
