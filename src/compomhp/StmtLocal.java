package compomhp;

import java.util.Objects;

import soot.Local;
import soot.jimple.Stmt;

public class StmtLocal {
	Local l;
	Stmt st;
	
	public StmtLocal(Stmt st, Local l) {
		super();
		this.l = l;
		this.st = st;
	}
	@Override
	public int hashCode() {
		return Objects.hash(l, st);
	}
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		StmtLocal other = (StmtLocal) obj;
		return Objects.equals(l, other.l) && Objects.equals(st, other.st);
	}
	public String toString() {
		String s = st.toString()+", "+l.getName();
		return s;
	}
}
