package microb;
/*
 * simple flow-sensitivity check with loops
 * expected: before loop points-to one object. Inside loop the points-to at the end
 * should flow to the start of loop
 */
public class MB6 {
	public static void main(String[] args) throws InterruptedException {
		MB6 mb = new MB6();
		System.out.println(mb);
		while(args.length!=0) {
			System.out.println(mb);
			int i = args.length;
			System.out.println(i);
			mb = new MB6();
		}
		System.out.println(mb);
	}
}
