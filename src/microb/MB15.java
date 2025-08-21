package microb;
/*
 * Multiple calls to same method. Check context insensitivity
 * expected: The points-to gets merged due to context-insensitivity at foo
 */
public class MB15 {
	public static void main(String[] args) {
		MB15 m = new MB15();
		MB15 o = m.foo();
		System.out.println(o);
		m = new MB15();
		o = m.foo();
		System.out.println(o);
	}
	MB15 foo() {
//		System.out.println(this);
		return this;
	}
}
