package microb;
/*
 * Simple local field flow-sensitive check with branching
 * expected: inside if, else field points-to respective objects and it point-to union
 */
public class MB4 {
	MB4 f;
	public static void main(String[] args) {
		MB4 mb = new MB4();
		mb.f = new MB4();
		if(args.length==0) {
			System.out.println(mb.f);
		}
		else {
			mb.f = new MB4();
		}
		System.out.println(mb.f);
	}
}
