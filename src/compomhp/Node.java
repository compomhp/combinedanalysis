package compomhp;


import java.util.Objects;

public class Node {
	MapName mapName;
	Object key;
//	Set<Node> succs;
//	public boolean diffSource = false;
	public MapName rightDiffMap = null;
	public Object rightDiffVar = null;
	
	
	
	public Node(MapName mapName, Object key) {
		super();
		this.mapName = mapName;
		this.key = key;
//		succs = new HashSet<Node>();
		//preds = new HashSet<Node>();
		
	}
	@Override
	public int hashCode() {
		return Objects.hash(key, mapName);
	}
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Node other = (Node) obj;
		return Objects.equals(key, other.key) && Objects.equals(mapName, other.mapName);
	}
	public String toString() {
		String s = "Source Node: Mapname: "+mapName+" key :"+key;
		return s;
	}
//	public void addSucc(Node succ) {
//		if(!succs.contains(succ)) {
//			succs.add(succ);
//		}
//	}
//	public void addPred(Node pre) {
//		if(!preds.contains(pre)) {
//			preds.add(pre);
//		}
//	}
}
