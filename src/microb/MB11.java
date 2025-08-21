package microb;
/*
 * FS check with method calls loops
 * expected: mb1 at the start to end of loop points-to allocation sites in both foos'
 * and after loop to both  alloc sites as well as the one in main
 */
public class MB11 {
	public static void main(String[] args) {
		MB11 mb = new MB11();
		int i = 3;
		MB11 mb1;
		while(i > 0) {
			mb = mb.foo();
			System.out.println(mb);
			i--;
			mb = mb.foo();
			System.out.println(mb);
		}
		System.out.println(mb);
	}
	MB11 foo() {
		return new MB11_1();
	}
}
class MB11_1 extends MB11{
	MB11 foo() {
		return new MB11();
	}
}
