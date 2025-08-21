package compomhp;

import java.util.Objects;

import soot.SootField;

public class AllocNodeField {
	public AllocNode an;
	public SootField sf;
	public AllocNodeField(AllocNode an, SootField sf) {
		super();
		this.an = an;
		this.sf = sf;
	}
	@Override
	public int hashCode() {
		return Objects.hash(an, sf);
	}
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		AllocNodeField other = (AllocNodeField) obj;
		return Objects.equals(an, other.an) && Objects.equals(sf, other.sf);
	}
	public String toString() {
		StringBuilder sb = new StringBuilder();
		if(an instanceof AllocNode) {
			sb.append(((AllocNode)an).memString()+" ");
		}
		else
			sb.append(an.toString());
		sb.append(" field: "+sf);
		return sb.toString();
		
	}
	
	
}
