package compomhp;

import java.util.Map;
import java.util.concurrent.TimeUnit;

import soot.SceneTransformer;

public class AnalysisTransformer extends SceneTransformer{
Arg arg;
	
	private static AnalysisTransformer instance = new AnalysisTransformer();
    private AnalysisTransformer() {}

    public static AnalysisTransformer v(Arg arg) {
    	instance.arg = arg;
    	return instance; }
   
	@Override
	protected void internalTransform(String phaseName, Map<String, String> options) {
		
		long startTime = System.nanoTime();
		
		
		
		
		Solver solver = Solver.v();
		/*start the analysis from main method by adding its FunctionCallConstraint into worklist and setting the arguments
		 *  and the path
		 * for various result files
		 * */
		SolverUtil.initSolverInstance(solver, arg);
		
		
		try {
//			try {
				solver.solve();
//			} catch (InterruptedException | ExecutionException e) {
//				// TODO Auto-generated catch block
//				e.printStackTrace();
//			}
			
		long elapsedTime = System.nanoTime() - startTime;
		long timeMs = elapsedTime/1000000;
		long timeS = elapsedTime/1000000000;
		long genTms = solver.genTime/1000000;
		long genTs = solver.genTime/1000000000;
		long solveTms = solver.solveTime/1000000;
		long solveTs = solver.solveTime/1000000000;
		System.out.println("Total elapsed time in milli seconds:"+timeMs);
		System.out.println("Total elapsed time in seconds:"+timeS);
		System.out.println("Total gen time :"+genTms+"millisec "+genTs+"sec ,"+" solve time: "+solveTms+"millisec "+solveTs+"sec");
		
		System.out.println("Total methods"+solver.processed.size()+"lib methods"+solver.libCount);
//		SootMethod sm = Scene.v().getMethod("<org.dacapo.harness.CommandLineArgs: void defineCallback()>");
//		solver.printMethPts(mainMethod);
		solver.printResults();
		if(arg.writeResults) {
			solver.appendOutput(arg.bench, genTms, genTs, solveTms, solveTs, timeMs, timeS, solver.processed.size());
			
		}
		if(arg.doopcode!=0) {
			solver.du.printDoopRes(timeS);
			solver.du2.printDoopRes(timeS);
		}
		
		} catch (Exception e1) {
			
			e1.printStackTrace();
		}
		finally {
			if(solver.pool != null)
			solver.pool.shutdown();
    		
    		try {
    			if(solver.pool != null)
				solver.pool.awaitTermination(60, TimeUnit.SECONDS);
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		
		//G.reset();
		//System.gc();
	}

}
