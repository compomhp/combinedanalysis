package compomhp;


import java.util.Objects;

public class NodeNi {
	MapName mapName;
	Object key;
	Object mem;
//	Set<Node> succs;
//	public boolean diffSource = false;
	
	
	
	
	public NodeNi(MapName mapName, Object key, Object mem) {
		super();
		this.mapName = mapName;
		this.key = key;
		this.mem = mem;
//		succs = new HashSet<Node>();
		//preds = new HashSet<Node>();
		
	}
	
	public String toString() {
		String s = "Source Node: Mapname: "+mapName+" key :"+key+" member: "+mem;
		return s;
	}

	@Override
	public int hashCode() {
		return Objects.hash(key, mapName, mem);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		NodeNi other = (NodeNi) obj;
		return Objects.equals(key, other.key) && mapName == other.mapName && Objects.equals(mem, other.mem);
	}
	
	
}
