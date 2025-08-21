package microb;
/*
 * FS check with multiple method calls
 * expected: mb at the end of main should point-to allocation in bar and in main
 */
public class MB10 {
	MB10 f;
	public static void main(String[] args) {
		MB10 mb = new MB10();
		System.out.println(mb);
		mb = foo();
		System.out.println(mb);
	}
	static MB10 foo() {
		MB10 m = new MB10();
		return m.bar();
		
	}
	MB10 bar() {
		
		if(this.f == null)
			return this;
		else
			return new MB10();
	}
}
