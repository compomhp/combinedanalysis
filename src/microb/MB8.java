package microb;
/*
 * FS check with one method call
 * expected: the returned value of function is successfully transferred
 */
public class MB8 {
	MB8 f;
	public static void main(String[] args) {
		MB8 mb = new MB8();
		mb.f = new MB8();
		MB8 r =  mb.foo();
		System.out.println(r);
		
	}
	MB8 foo() {
		System.out.println(this.f);
		return this.f;
	}
}
