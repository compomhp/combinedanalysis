package microb;
/*
 * static functions
 * expected: main function gets object of foo
 */
public class MB16 {
	
	public static void main(String[] args) {
		System.out.println(foo());
	}
	static MB16 foo(){
		MB16 m = new MB16();
		return m.bar();
	}
	MB16 bar() {
		return this;
	}
}
