package microb;
/*
 * mix of static non-static fields
 * expected: f1 follows flow-sensitivity but f does not
 */
public class MB19 {
	static MB19 f;
	MB19 f1;
	public static void main(String[] args) {
		MB19 mb = new MB19();
		f = new MB19();
		mb.f1 = new MB19();
		mb.f1.foo();
		System.out.println(f+""+mb.f1);
	}
	void foo() {
		f = new MB19();
	}
}
