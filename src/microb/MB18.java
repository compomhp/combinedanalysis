package microb;
/*
 * static fields (updated flow-insensitively)
 * Everywhere the field points-to same set
 */
public class MB18 {
	static MB18 f;
	public static void main(String[] args) {
		f = new MB18();
		System.out.println(f);
		foo();
		System.out.println(f);
	}
	static void foo() {
		f = new MB18();
	}
}
