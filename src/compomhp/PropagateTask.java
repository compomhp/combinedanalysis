package compomhp;

import java.util.BitSet;
import java.util.Objects;

public class PropagateTask {
	Node sn;
	int bitPos;
	String name="prop task";
	BitSet bs;
	public PropagateTask(Node sn, int bitPos) {
		super();
		this.sn = sn;
		this.bitPos = bitPos;
	}
	@Override
	public int hashCode() {
		return Objects.hash(bitPos, sn);
	}
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		PropagateTask other = (PropagateTask) obj;
		return bitPos == other.bitPos && Objects.equals(sn, other.sn);
	}
	@Override
	public String toString() {
		return "PropagateTask :" + sn + ", bitPos=" + bitPos ;
	}
	
}
