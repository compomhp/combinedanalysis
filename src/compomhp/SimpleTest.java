package compomhp;

import java.util.ArrayList;
import java.util.List;

import soot.RefType;
import soot.SootField;
import soot.jimple.Stmt;
import soot.jimple.internal.JReturnVoidStmt;

public class SimpleTest {
	public static void main(String[] args) {
		AllocNode an = new AllocNode();
		List<AllocNodeField> list = new ArrayList<AllocNodeField>();
		an.count = 0;
		SootField sf = new SootField("field1",RefType.v("java.lang.Object"));
		Stmt s1 = new JReturnVoidStmt();
		AllocNodeField anf = new AllocNodeField(an,sf);
		AllocNodeField anf1 = new AllocNodeField(an,null);
		AllocNodeField sr = new AllocNodeField(null,null);
		list.add(anf);
		list.add(anf1);
		System.out.println(list.indexOf(sr));
		sr.an = an;
		System.out.println(list.indexOf(sr));
		sr.sf = sf;
		System.out.println(list.indexOf(sr));
		
	}
}
