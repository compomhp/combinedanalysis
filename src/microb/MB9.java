package microb;
/*
 * FS check with recursive method call
 * expected: field f in main points-to second allocation in foo() in the absence of
 * if condition in foo() else points-to both the allocation sites
 */
public class MB9 {
	MB9 f;
public static void main(String[] args) {
		MB9 mb = new MB9();
		mb.foo();
		System.out.println(mb.f);
	}
	void foo() {
		this.f = new MB9();
		System.out.println(this.f);
		if(this.f == null)
			foo();
		else
		this.f = new MB9();
		System.out.println(this.f);
	}
}
