package compomhp;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class TimeDiv {
	static Map<Integer,Map<MapName,Long>> memprintLists = new HashMap<>();
	static Map<Integer,Map<MapName,Long>> condprintLists = new HashMap<>();
	static Map<Integer,Map<MapName,Long>> propprintLists = new HashMap<>();
	static ArrayList<MapName> maps = new ArrayList<>();
	static long timevarPts=0;
	static long timefieldPts=0;
	static long timeMHP=0;
	static long timerefFields=0;
	static long timeinclMeths=0;
	static long timecallSiteMeths=0;
	static long timeinvMethStmts=0;
	static long timemethStmts=0;
	static long otherTime =0;
	static Map<MapName,Time> mapTimes = new HashMap<>();
	static void noteTime(MapName mapn, long t) {
		if(!mapTimes.containsKey(mapn)) {
			mapTimes.put(mapn, new Time());
			if(!maps.contains(mapn))
			 maps.add(mapn);
		}
		Time ti = mapTimes.get(mapn);
		ti.l=ti.l+t;
//		if(mapn==MapName.varPts) {
//			timevarPts+=t;
//		}
//		else if(mapn==MapName.fieldPts) {
//			timefieldPts+=t;
//		}
//		else if(mapn==MapName.MHP) {
//			timeMHP+=t;
//		}
//		else if(mapn==MapName.refFields) {
//			timerefFields+=t;
//		}
//		else if(mapn==MapName.inclMeths) {
//			timeinclMeths+=t;
//		}
//		else if(mapn==MapName.callSiteMeths) {
//			timecallSiteMeths+=t;
//		}
//		else if(mapn==MapName.methStmts) {
//			timemethStmts+=t;
//		}
//		else if(mapn==MapName.invMethStmts) {
//			timeinvMethStmts+=t;
//		}
//		else {
//			otherTime+=t;
//		}
	}
	static void reset() {
		for(Map.Entry<MapName, Time> ele : mapTimes.entrySet()) {
			Time t = ele.getValue();
			t.l = 0;
		}
//		timevarPts=0;
//		timefieldPts=0;
//		timeMHP=0;
//		timerefFields=0;
//		timeinclMeths=0;
//		timecallSiteMeths=0;
//		timeinvMethStmts=0;
//		timemethStmts=0;
//		otherTime =0;
	}
	static void printTime(String s, int cycle) {
		StringBuilder sb = new StringBuilder();
		long sum = 0;
		sb.append(s+":");
		Map<MapName,Long> ml;
		if(s.equals("memCons")) {
			if(!memprintLists.containsKey(cycle)) {
				memprintLists.put(cycle, new HashMap<>());
			}
			ml = memprintLists.get(cycle);
		}
		else if(s.equals("propCons")) {
			if(!propprintLists.containsKey(cycle)) {
				propprintLists.put(cycle, new HashMap<>());
			}
			ml = propprintLists.get(cycle);
		}
		else {
			if(!condprintLists.containsKey(cycle)) {
				condprintLists.put(cycle, new HashMap<>());
			}
			ml = condprintLists.get(cycle);
		}
		for(Map.Entry<MapName, Time> ele : mapTimes.entrySet()) {
			MapName m = ele.getKey();
			Time t = ele.getValue();
			sb.append(m+""+t.getMsTime()+";");
			ml.put(m, t.getMsTime());
			sum = sum + t.l;
		}
		sb.append("sum"+""+sum/1000000+"mS");
		System.out.println(sb.toString());
//		long sum = 	timevarPts+
//		timefieldPts+
//		timeMHP+
//		timerefFields+
//		timeinclMeths+
//		timecallSiteMeths+
//		timeinvMethStmts+
//		timemethStmts+
//		otherTime;
//		System.out.println(s+":"+"varPts="+timevarPts+" ; "+
//				"fieldPts="+timefieldPts+" ; "+
//				"MHP="+timeMHP+" ; "+
//				"refFields="+timerefFields+" ; "+
//				"inclMeths="+timeinclMeths+" ; "+
//				"callSiteMeths="+timecallSiteMeths+" ; "+
//				"invMethStmts="+timeinvMethStmts+" ; "+
//				"methStmts="+timemethStmts+" ; "+
//				"others="+otherTime+" ; "+
//				"total="+sum
//				);
	}
	static void printCsv() {
		File file = new File(Solver.v().path+"/tmp/timediv.txt");
		PrintStream stdout = System.out;
	      //Instantiating the PrintStream class
	      try {
			PrintStream stream = new PrintStream(file);
			System.setOut(stream);
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		printCsv(memprintLists);
		printCsv(propprintLists);
		printCsv(condprintLists);
		System.setOut(stdout);
	}
	static void printCsv(Map<Integer,Map<MapName,Long>> printLists) {
		StringBuilder mapStr = new StringBuilder();
		mapStr.append("Cycle,");
		for(MapName m : maps) {
			mapStr.append(m+",");
		}
		System.out.println(mapStr.toString());
		for(Map.Entry<Integer, Map<MapName,Long>> ele : printLists.entrySet()) {
			int cycle = ele.getKey();
			Map<MapName,Long> times = ele.getValue();
			StringBuilder sb = new StringBuilder();
			sb.append(cycle+",");
			for(MapName m : maps) {
				if(times.containsKey(m)) {
					sb.append(times.get(m)+",");
				}
				else {
					sb.append(0+",");
				}
			}
			System.out.println(sb.toString());
		}
		
	}
}
class Time{
	long l;
	Time(){
		l = 0;
	}
	long getMsTime() {
		return l/1000000;
	}
}
