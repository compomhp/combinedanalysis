package compomhp;

import java.lang.management.ManagementFactory;
import java.lang.management.MemoryMXBean;
import java.lang.management.MemoryUsage;
import java.lang.management.ThreadMXBean;
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
		Solver.startTime = startTime;
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
			
		long elapsedTime = System.nanoTime() - Solver.startTime;
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
		
		System.out.println("Total constraints: "+Constraint.getTotalCount());
//		SootMethod sm = Scene.v().getMethod("<org.dacapo.harness.CommandLineArgs: void defineCallback()>");
//		solver.printMethPts(mainMethod);
		solver.printResults();
//		printMemoryMetrics();
		System.gc();       // suggest garbage collection
	    Thread.sleep(100); // give GC some time
	    
	    long usedMemory = Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory();
	    System.out.println("Used Memory: " + usedMemory + " bytes");
	    solver.getStmtCount();
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
	private static double peakHeapUsedMB = 0.0;
	private static double totalEstimatedMB = 0.0;
    public static void printMemoryMetrics() {
        MemoryMXBean memoryBean = ManagementFactory.getMemoryMXBean();
        ThreadMXBean threadBean = ManagementFactory.getThreadMXBean();

        MemoryUsage heapUsage = memoryBean.getHeapMemoryUsage();
        long heapUsed = heapUsage.getUsed();
        long heapCommitted = heapUsage.getCommitted();
        long heapMax = heapUsage.getMax();

        MemoryUsage nonHeapUsage = memoryBean.getNonHeapMemoryUsage();
        long nonHeapUsed = nonHeapUsage.getUsed();
        long nonHeapCommitted = nonHeapUsage.getCommitted();
        long nonHeapMax = nonHeapUsage.getMax();

        int threadCount = threadBean.getThreadCount();
        long stackSizePerThread = 1024 * 1024; // 1MB
        long estimatedStackMemory = threadCount * stackSizePerThread;
        long totalEstimatedMemory = heapUsed + nonHeapUsed + estimatedStackMemory;

        // Convert bytes to MB
        double heapUsedMB = heapUsed / (1024.0 * 1024.0);
        double heapCommittedMB = heapCommitted / (1024.0 * 1024.0);
        double heapMaxMB = heapMax / (1024.0 * 1024.0);

        double nonHeapUsedMB = nonHeapUsed / (1024.0 * 1024.0);
        double nonHeapCommittedMB = nonHeapCommitted / (1024.0 * 1024.0);
        double nonHeapMaxMB = nonHeapMax / (1024.0 * 1024.0);

        double estimatedStackMB = estimatedStackMemory / (1024.0 * 1024.0);
       totalEstimatedMB = totalEstimatedMemory / (1024.0 * 1024.0);

        // Update and print the peak heap used
        if (heapUsedMB > peakHeapUsedMB) {
            peakHeapUsedMB = heapUsedMB;
        }

        System.out.printf("Heap Memory (Used/Committed/Max) MB: %.2f / %.2f / %.2f%n", heapUsedMB, heapCommittedMB, heapMaxMB);
        System.out.printf("Non-Heap Memory (Used/Committed/Max) MB: %.2f / %.2f / %.2f%n", nonHeapUsedMB, nonHeapCommittedMB, nonHeapMaxMB);
        System.out.printf("Estimated Stack Memory (Threads * stack size) MB: %.2f%n", estimatedStackMB);
        System.out.printf("Total Estimated Memory (Heap + Non-Heap + Stack) MB: %.2f%n", totalEstimatedMB);
        System.out.printf("Peak Heap Used MB: %.2f%n", peakHeapUsedMB);
    }


}
