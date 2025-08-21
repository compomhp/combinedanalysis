package microb;
/*
 * simple FS check of fields with loops
 * expected: before loop filed points-to one object. Inside loop the points-to at the end
 * should flow to the start of loop
 */
public class MB7 {
	MB7 f;
	public static void main(String[] args) throws InterruptedException {
		MB7 mb = new MB7();
		mb.f = new MB7();
		System.out.println(mb.f);
		while(args.length!=0) {
			int i = args.length;
			System.out.println(i);
			mb.f = new MB7();
		}
		System.out.println(mb.f);
	}
}
