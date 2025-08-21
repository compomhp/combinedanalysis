package compomhp;

import java.util.Objects;

import soot.SootField;
import soot.jimple.Stmt;

public class StmtAllocNodeField {
	AllocNodeField anf;
	public Stmt st;
	public StmtAllocNodeField(Stmt st, AllocNodeField anf) {
		super();
		this.anf = anf;
		this.st = st;
	}
	@Override
	public int hashCode() {
		return Objects.hash(anf, st);
	}
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		StmtAllocNodeField other = (StmtAllocNodeField) obj;
		return Objects.equals(anf, other.anf) && Objects.equals(st, other.st);
	}
	
	
}
