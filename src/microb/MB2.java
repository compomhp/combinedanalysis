package microb;
/*
 * Simple local field flow-sensitive check and strong and weak update
 */
public class MB2 {
	MB2 f,f1;
	public static void main(String[] args) {
		MB2 mb = null;
		MB2 mb2 = new MB2();
		int i = 3;
		while(i>0) {
			mb = new MB2();
		}
		mb.f = new MB2();
		mb2.f1 = new MB2();
		System.out.println(mb+""+mb.f+mb2.f1);
		mb.f = new MB2();
		mb2.f1 = new MB2();
		System.out.println(mb+""+mb.f+mb2.f1);
	}

}
