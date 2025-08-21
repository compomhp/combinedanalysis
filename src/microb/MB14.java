package microb;
/*
 * Multiple classes fields weak update & strong update
 * expected: mb.f1 weak update, mb1.f strong update; good example
 */
public class MB14 {
	F f1;
	public static void main(String[] args) {
		MB14 mb = new MB14();
		MB14_1 mb1 = new MB14_1();
		mb1.f = new F();
		mb.f1 = new F();
//		System.out.println(mb.f1+" "+mb1.f);
		if(args.length==2)
			mb = new MB14();
		mb.f1 = new F();
		mb1.f = new F();
//		System.out.println(mb.f1+" "+mb1.f);
		
	}

}
class MB14_1{
	F f;
}
class F{
	
}
