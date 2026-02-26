package compomhp;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import soot.Body;
import soot.Local;
import soot.PatchingChain;
import soot.RefType;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.jimple.AssignStmt;
import soot.jimple.FieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.NullConstant;
import soot.jimple.Stmt;
import soot.jimple.internal.JNopStmt;

public class FieldSummary {
	
	static final String MY_TAG = "mytag";
	static MyTag mytag = new MyTag(MY_TAG);
	  public static void summaryField(SootMethod method, Body body) {
		 
		  if(Solver.xMeths.contains(method)) {
			  return;
		  }
		  boolean xmlMeth = isXMLTypeMeth(method);
		  if(xmlMeth) {
			  summarizeAllFieldAccess(body, null);
			  Solver.xMeths.add(method);
		  }
	        return;
	    }
	  public static boolean isXMLTypeMeth(SootMethod method) {
		  boolean xmlMeth = false;
		  String className = method.getDeclaringClass().getName();
	    	for(String pre: XML_CLASS_PREFIX) {
		    	if(className.contains(pre)) {
		    		
		    		xmlMeth = true;
		    		break;
		    	}
	    	}
	    	
	        // Summarize fields for Xalan TransformerImpl
	        if (className.equals("org.apache.xalan.transformer.TransformerImpl")) {
	        	
	        	xmlMeth = true;

	        }
	     // Summarize fields for Batik DOM
	       // SVG is an XML-based image format
	        else if (className.startsWith("org.apache.batik")) {
	        	if(className.contains(".dom.")
	        			|| className.contains(".svg.")
	        			|| className.contains("XML")
	        			|| className.contains("DOM")
	        			/*|| className.contains("SVG")*/
	        			){
	        	
	        	xmlMeth = true;
	        	}
	        }
	        else if (className.startsWith("org.apache.fop")) {
	        	if(className.contains(".dom.")
	        			|| className.contains(".svg.")){
	        		xmlMeth = true;
	        	}
	        }
	        	
	       
	        /*
	         * Jaxen is a flexible and powerful XPath library for Java used for querying and traversing XML or DOM trees.
	         */
	        else if(className.contains(".jaxen.")) {
	        	xmlMeth = true;
	        }
	        else if (className.startsWith("net.sourceforge.pmd")) {
	        	if(
	        			className.contains("XML")
	        			|| className.contains("DOM")
	        			|| className.contains("XSLT")
	        			|| className.contains("XPATH")
	        		|| 	className.contains(".RuleSetFactory")
	        			)
	        	
	        	xmlMeth = true;
	        }
	        return xmlMeth;
	  }
	  private static void summarizeAllFieldAccess(Body body, Set<String> essentialFields) {
//	    	SootMethod m = body.getMethod();
//	    	boolean modified = false;
//	    	if(Solver.methUpdatedBodies.containsKey(m)) {
//	    		return modified;
//	    	}

	        PatchingChain<Unit> units = body.getUnits();

	        for (Iterator<Unit> iter = units.snapshotIterator(); iter.hasNext(); ) {
	            Unit u = (Stmt) iter.next();
	            if (u instanceof AssignStmt) {
	                AssignStmt stmt = (AssignStmt) u;
	                if (stmt.containsFieldRef()) {
	                		FieldRef f = stmt.getFieldRef();
	                		SootField sf = f.getField();

	                	if(SimplifyUtil.isInterestingType(sf.getType()) && !sf.isStatic()) {
	                		if (stmt.getRightOp() instanceof FieldRef) {
	                			u.addTag(mytag);
//	                			modified = true;
	                		}	
	                		else if (stmt.getLeftOp() instanceof FieldRef) {
	                			u.addTag(mytag);
//	                			modified = true;
	                        }
	                	}

	                }
	            }

	        }
	        
//	        return modified;

	    }
	  public static boolean summarizeCreation(SootMethod method, Body body) {
//        Body body = method.retrieveActiveBody();
        PatchingChain<Unit> units = body.getUnits();
        boolean modified = false;
        for (Iterator<Unit> iter = units.snapshotIterator(); iter.hasNext(); ) {
            Stmt stmt = (Stmt) iter.next();

            if (stmt.containsInvokeExpr()) {
                InvokeExpr invokeExpr = stmt.getInvokeExpr();
                SootMethod targetMethod = invokeExpr.getMethod();
               
                boolean isCreation = false;

                String retClass = null;
                if(XML_CREATION.contains(targetMethod.getName())) {
                	Type retType = targetMethod.getReturnType();
                	if(retType instanceof RefType) {
                		retClass = ((RefType)retType).getClassName();
                		for(String s: XML_CLASS_PREFIX)
	                		if(retClass.contains(s)) {
	                			isCreation = true;
	                			break;
	                		}
                	}
                }
                if(isCreation) {
                	Solver.v().recordProcessed(targetMethod);
                	Solver.v().recordCall(method, targetMethod);
                	modified = true;
                    replaceWithSummary(stmt, units, XMLDOM_CREATION.get(retClass), targetMethod.getReturnType(), body, false);
                }
               
            }

        }
        return modified;
    }
	  private static void replaceWithSummary(Stmt stmt, PatchingChain<Unit> units, String summaryObjectName, Type returnType, Body body, boolean isWrite) {
	        Jimple jimple = Jimple.v();
	        Stmt newSt;
	        if(isWrite) {
	        	 newSt = new JNopStmt();
	        }
	        else {
	        Local summaryObject = Jimple.v().newLocal(summaryObjectName, returnType);
	        
	        // Insert new local variable to store summary object
	        body.getLocals().add(summaryObject);
	        
	        // Assign a new abstract object
	       newSt = jimple.newAssignStmt(summaryObject, NullConstant.v());
	        }
	        
	        // Replace the old statement
	        units.insertBefore(newSt, stmt);
	        units.remove(stmt);
	    }
	  private static final Map<String, String> XMLDOM_CREATION = new HashMap<>();
	   

	    
	    static {
	    XMLDOM_CREATION.put("org.w3c.dom.Node", "DOM_NODE");
	    XMLDOM_CREATION.put("org.w3c.dom.Document","DOM_DOCUMENT");
	    XMLDOM_CREATION.put("org.w3c.dom.Element", "DOM_ELEMENT");
	    		XMLDOM_CREATION.put("org.w3c.dom.Node", "DOM_NODE");
	        XMLDOM_CREATION.put("org.w3c.dom.NamedNodeMap","DOM_ATTRIBUTE");
	       
	    }
	    static final Set<String> XML_CLASS_PREFIX = new HashSet<>(Arrays.asList(
		        "org.apache.xpath",
		        "org.apache.xml",
		        "javax.xml",
		        "org.w3c.dom",
		        "org.xml",
		        "org.apache.xerces"
		    ));
	    private static final HashSet<String> XML_CREATION = new HashSet<>(Arrays.asList(
	    		 "createDocument",        // Creates a new XML document
	    	        "createElementNS",       // Creates an XML element with namespace
	    	        "createAttributeNS",
	    	        "createAttributes",
	    	        "cloneNode",
	    	        "createElement",
	    	        "importNode"
	        ));
}
