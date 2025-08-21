package compomhp;


import java.io.IOException;
import java.nio.file.FileSystems;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import soot.PackManager;
import soot.Scene;
import soot.SootClass;
import soot.Transform;
import soot.options.Options;




public class MainAnalysisClass{
	static LinkedList<String> excludeList;
	 
	public static void main(String[] args) throws SecurityException, IOException {
		try {
		Arg arg = readArguments(args);

		PackManager.v().getPack("wjtp").add(new
        		Transform("wjtp.AnalysisTransformer",
        				AnalysisTransformer.v(arg)));
		
		
		
		excludeJDKLibrary();
		/*
		 * Command line arguments
		 *  -cp = classpath 
		 *  -b  = benchmark name
		 *  -su = benchmark suite
		 *  -m  = materialize/out (1/0) - default 1
		 *  -c  = combined (0/1 for no/yes) - default 1
		 *  -fs = flow sensitive (0/1 no/yes) - default 1
		 *  -poa= points-to (0/1 for no/yes) - default 1
		 *  -mhp = MHP (0/1 for no/yes) - default 1
		 *  -i = interleaved execution (0/1 for no/yes) - default 1
		 *  -mc = mainclass - default from Benchmark
		 *  -gp = gen parallel off/on (0/1 for no/yes) - default 1
		 *  -cl = call log off/on (0/1 for no/yes) - default 0
		 *  -wr = write results off/on (0/1 for no/yes) - default 1
		 *  -bot = consider bottom (0/1) - default 1
		 *  -esc = compute library parameters escape info (0/1) - default 1 
		 *  -cha = use cha for call sites (0/1) - default 0
		 *  -doopcode = use to indicate which type of doop context sensitivity to compare with 
		 */
		
		/*
		 * Provide soot options here, as the command line arguments are used 
		 * to enable/disable various aspects of the analysis
		 */
		List<String> argsList = new ArrayList<String>();
		   argsList.addAll(Arrays.asList(new String[]{
				   "-w",
				   "-app",
				   "-p", "cg.cha", "enabled:true,on-fly-cg:true,apponly:true",
//				   "-p", "jb.ls","enabled:false", //Disable Local Splitter
//				   "-p", "jb.a","enabled:false", //Disable Local Aggregator
				   "-p","jb.lp","enabled:true" // enables the local packer
//				   "-src-prec", "J"
				   		
		   }));
		   /*
		    * jb.ls and jb.lp needs to be disabled to get flow-insensitive behaviour
		    */
		   
//		if(!arg.fs) {
//			argsList.addAll(Arrays.asList(new String[]{
//					   "-p","jb.lp","enabled:true"   		
//			   }));
//		}
		Options.v().parse((String[])argsList.toArray(new String[0]));
		String classPath = FileSystems.getDefault().getPath("").toAbsolutePath().toString();
//		Options.v().set_output_format(Options.output_format_jimple);
//		int outputFormat = Options.v().output_format();
//		String formatName;
//		switch (outputFormat) {
//        case Options.output_format_none:
//            formatName = "None";
//            break;
//        case Options.output_format_class:
//            formatName = "Class (bytecode)";
//            break;
//        case Options.output_format_jimple:
//            formatName = "Jimple";
//            break;
//        case Options.output_format_shimple:
//            formatName = "Shimple";
//            break;
//        case Options.output_format_grimp:
//            formatName = "Grimp";
//            break;
//        case Options.output_format_baf:
//            formatName = "Baf";
//            break;
//        case Options.output_format_jasmin:
//            formatName = "Jasmin";
//            break;
//        case Options.output_format_dava:
//            formatName = "Dava";
//            break;
//        case Options.output_format_dex:
//            formatName = "Dex";
//            break;
//        default:
//            formatName = "Unknown";
//            break;
//    }
//		System.out.println("out format:"+formatName);
		String sysPath = System.getProperty("java.class.path");
		Options.v().set_prepend_classpath(true);
		
	   if(arg.cp != null) {
//		   Options.v().set_soot_classpath(sysPath+":"+arg.cp);
		   Options.v().set_soot_classpath(arg.cp);
	   }
	   else if(arg.suite.contains("enaissance")) {
//		   Options.v().set_soot_classpath(sysPath+":"+classPath+"/benchfiles/sc_"+arg.bench);
		   Options.v().set_soot_classpath(classPath+"/benchfiles/sc_"+arg.bench);
	   }
	   else if(arg.suite.contains("newdacapo")) {
//		   Options.v().set_soot_classpath(sysPath+":"+classPath+"/benchfiles/boosted_"+arg.bench);
		   Options.v().set_soot_classpath(classPath+"/benchfiles/boosted_"+arg.bench);
	   }
	   else if(arg.suite.contains("extra")) {
//		   Options.v().set_soot_classpath(sysPath+":"+classPath+"/benchfiles/classes_"+arg.bench);
		   Options.v().set_soot_classpath(classPath+"/benchfiles/classes_"+arg.bench);
	   }
	   else if(!arg.mainclass.equals("Harness")) {
			Options.v().set_soot_classpath("bin");
		}
		else {
//		  Options.v().set_soot_classpath(sysPath+":"+classPath+"/benchfiles/materialized_"+arg.bench);
		  Options.v().set_soot_classpath(classPath+"/benchfiles/materialized_"+arg.bench);
		}
	   
//	   	Options.v().set_include_all(true);
	   System.out.println("class path set to: "+Options.v().soot_classpath());
//	   System.out.println("class path set to: "+System.getProperty("java.class.path"));
	   	
	   	/*
	   	 * add basic classes for renaissance
	   	 */
	    Scene.v().addBasicClass("scala.runtime.java8.JFunction0$mcI$sp",SootClass.HIERARCHY);
		Scene.v().addBasicClass("scala.runtime.java8.JFunction0$mcZ$sp",SootClass.HIERARCHY);
		Scene.v().addBasicClass("scala.runtime.java8.JFunction0$mcJ$sp",SootClass.HIERARCHY);
		Scene.v().addBasicClass("scala.runtime.java8.JFunction0$mcV$sp",SootClass.HIERARCHY);
//		Scene.v().addBasicClass("org.apache.zookeeper.server.ZooKeeperServerMain", SootClass.HIERARCHY);
		Scene.v().addBasicClass("net.sf.saxon.functions.Adjust",SootClass.SIGNATURES);
		Scene.v().addBasicClass("net.sf.saxon.functions.BaseURI",SootClass.SIGNATURES);
		SootClass mainClass;
		if(!arg.mainclass.equals("Harness")) {
			mainClass = Scene.v().loadClassAndSupport(arg.mainclass);
		}
		else if(arg.suite.contains("enaissance"))
	   		mainClass = Scene.v().loadClassAndSupport("org.renaissance.core.Launcher");
	   	else if(arg.suite.equals("th"))
	   		mainClass = Scene.v().loadClassAndSupport("org.dacapo.harness.TestHarness"); 
	   	else
	   		mainClass = Scene.v().loadClassAndSupport("Harness"); 
		
	   	Scene.v().setMainClass(mainClass);
		Scene.v().loadNecessaryClasses();
		PackManager.v().runPacks();
		}catch(Exception e) {
			System.out.println("!!!!Exited with exception!!!");
//			e.printStackTrace();
		}
	}
	private static void excludeJDKLibrary()
	{
		 
	    Options.v().set_exclude(excludeList());
	    Options.v().set_no_bodies_for_excluded(true);
	    Options.v().set_allow_phantom_refs(true);
	}
	private static LinkedList<String> excludeList()
	{
		if(excludeList==null)
		{
			excludeList = new LinkedList<String> ();

//			excludeList.add("java.");
//		    excludeList.add("javax.");
		    excludeList.add("sun.");
		    excludeList.add("sunw.");
		    excludeList.add("com.sun.");
		    excludeList.add("com.ibm.");
		    excludeList.add("com.apple.");
		    excludeList.add("apple.awt.");
		    excludeList.add("scala.collection.");
//		    excludeList.add("jdk.internal.");
		    //excludeList.add("scala.");
		}
		return excludeList;
	}
	private static Arg readArguments(String[] argv) {
		Arg arg = new Arg();
		for(int i=0; i<argv.length - 1; i+=2) {
			String option = argv[i];
			String choice = argv[i+1];
			if(option.equals("-cp")) {
				arg.cp = choice;
			}
			else if(option.equals("-b")) {
				arg.bench = choice;
			}
			else if(option.equals("-su")) {
				arg.suite = choice;
			}
			else if(option.equals("-m")) {
				if(choice.equalsIgnoreCase("false"))
					arg.materialized = false;
			}
			else if(option.equals("-c")) {
				if(choice.equalsIgnoreCase("false"))
					arg.combined = false;			
			}
			else if(option.equals("-fs")) {
				if(choice.equalsIgnoreCase("false"))
					arg.fs = false;
			}
			else if(option.equals("-poa")) {
				if(choice.equalsIgnoreCase("false"))
					arg.poa = false;
			}
			else if(option.equals("-mhp")) {
				if(choice.equalsIgnoreCase("false"))
					arg.mhp = false;
			}
			else if(option.equals("-i")) {
				if(choice.equalsIgnoreCase("false"))
					arg.interleaved = false;
			}
			else if(option.equals("-mc")) {
				arg.mainclass = choice;
			}
			else if(option.equals("-gp")) {
				if(choice.equalsIgnoreCase("false"))
					arg.genParallel = false;
			}
			else if(option.equals("-cl")) {
				if(choice.equalsIgnoreCase("false"))
					arg.callLog = false;
			}
			else if(option.equals("-wr")) {
				if(choice.equalsIgnoreCase("true"))
					arg.writeResults = true;
			}
			else if(option.equals("-it")) {
				if(choice.equalsIgnoreCase("true"))
					arg.iterative = true;
			}
			else if(option.equals("-bot")) {
				if(choice.equalsIgnoreCase("false"))
					arg.bot = false;
			}
			else if(option.equals("-esc")) {
				if(choice.equalsIgnoreCase("true"))
					arg.esc = true;
			}
			else if(option.equals("-cha")) {
				if(choice.equalsIgnoreCase("true"))
					arg.useCHA = true;
			}
			else if(option.equals("-pmhp2")) {
				if(choice.equalsIgnoreCase("true"))
					arg.pmhp2 = true;
			}
			else if(option.equals("-doopcode")) {
				arg.doopcode = Integer.valueOf(choice);
			}
			
		}
		return arg;
	}
	
}
class Arg{
	String cp;
	String bench;
	String suite;
	String mainclass;
	boolean materialized;
	boolean combined;
	boolean fs;
	boolean poa;
	boolean mhp;
	boolean genParallel;
	boolean interleaved; 
//	boolean HA;
	boolean callLog;
	boolean writeResults;
	boolean iterative;
	boolean bot;
	boolean esc;
	boolean useCHA;
	boolean pmhp2;
	boolean usePrevMHP;
	boolean usePrevP2;
	int doopcode;
	
	public Arg() {
		/*
		 * set default options
		 */
		cp = null;
		bench = "avrora";
		suite = "dacapo";
		mainclass = "Harness";
		materialized = true;
		combined = true;
		fs = true;
		poa = true;
		mhp = true;
		useCHA = false;
		genParallel = true;
		interleaved = true;
//		HA= false;
		callLog = true;
		writeResults = false;
		iterative = false;
		bot=true;
		esc=false;
		pmhp2 = false;
		usePrevMHP=false;
		usePrevP2=false;
		doopcode = 0;
		
	}
	public String toString() {
		String s = "benchmark: "+bench+"\n"+
				"suite: "+suite+"\n"+
				"mainclass: "+mainclass+"\n"+
				"materialized: "+materialized+"\n"+
				"combined: "+combined+"\n"+
				"flow-sensitive: "+fs+"\n"+
				"poa: "+poa+"\n"+
				"mhp: "+bench+"\n"+
				"genParallel: "+genParallel+"\n"+
				"interleaved: "+interleaved+"\n"+
				"callLog: "+callLog+"\n"+
//				"intFieldPass: "+HA+"\n"+
				"writeResults: "+writeResults+"\n"+
				"iterative: "+iterative+"\n"+
				"bot: "+bot+"\n"+
				"esc:"+esc+"\n"+
				"useCHA"+useCHA+"\n"+
				"pmhp2"+pmhp2+"\n"+
				"usePrevMHP"+usePrevMHP+"\n"+
				"usePrevP2"+usePrevP2+"\n"+
				"doopcode"+doopcode
				;
				
		
		return s;
	}
}


