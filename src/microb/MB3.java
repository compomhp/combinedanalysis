package microb;
/*
 * Simple local var flow-sensitive check with branching
 * expected: inside if, else points-to respective objects and it point-to union
 */
public class MB3 {
	MB3 f;
	public static void main(String[] args) {
		MB3 mb = new MB3();
		if(args.length==0) {
			System.out.println(mb);
		}
		else {
			mb = new MB3();
		}
		System.out.println(mb);
		
		
	}

}
