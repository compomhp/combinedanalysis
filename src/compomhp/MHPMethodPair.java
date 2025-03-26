package compomhp;

import java.util.HashSet;
import java.util.Objects;
import java.util.Set;

import soot.SootMethod;

public class MHPMethodPair {
	public Set<SootMethod> pair;
	public MHPMethodPair(SootMethod m1, SootMethod m2) {
		super();
		pair = new HashSet<SootMethod>();
		pair.add(m1);
		pair.add(m2);
	}
	@Override
	public int hashCode() {
		return Objects.hash(pair);
	}
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		MHPMethodPair other = (MHPMethodPair) obj;
		return Objects.equals(pair, other.pair);
	}
	

	
}
