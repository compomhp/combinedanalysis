package microb;
/*
 * FS check with method calls and branching
 * expected: inside if follows FS.
 * at the end mb1 points-to main alloc site and MB12_1's alloc site
 */
public class MB12 {
	public static void main(String[] args) {
		MB12 mb = new MB12();
		int i = 3;
		MB12 mb1 = mb;
		if(i > 0) {
			mb1 = mb.foo();
			System.out.println(mb1);
			i--;
			mb1 = mb1.foo();
			System.out.println(mb1);
		}
		System.out.println(mb1);
	}
	MB12 foo() {
		return new MB12_1();
	}
}
class MB12_1 extends MB12{
	MB12 foo() {
		return new MB12();
	}
}

