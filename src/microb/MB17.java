package microb;
/*
 * static functions with fields
 * expected: flow-sensitive field update. After foo, f points-to the allocation site in foo as well as main
 */
public class MB17 {
	MB17 f;
	public static void main(String[] args) {
		MB17 m = new MB17();
		m.f = new MB17();
		System.out.println(m.f);
		foo(m);
		System.out.println(m.f);
		
	}
	static void foo(MB17 p) {
		p.f = new MB17();
	}
	
}
