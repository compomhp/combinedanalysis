package microb;
/*
 * FS check with indirect recursion
 * expected: ret in main points-to main alloc site as well as in foo in the presence of if-else
 */
public class MB13 {
	public static void main(String[] args) {
		MB13 mb = new MB13();
		MB13 ret = mb.foo(args);
		System.out.println(ret);
	}
	MB13 foo(String[] args) {
		MB13 ret;
		
		if(args.length > 0) {
			ret = new MB13();
		}
		else
			ret = bar();
		return ret;
	}
	MB13 bar() {
		return this.meth();
	}
	MB13 meth() {
		System.out.println(this);
		return this;
	}
}
