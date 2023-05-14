import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;


import ilog.concert.IloException;
import ilog.concert.IloIntVar;
import ilog.concert.IloLinearNumExpr;
import ilog.concert.IloNumVar;
import ilog.concert.IloRange;
import ilog.cplex.IloCplex;
/**
 * 
 * @author xiaohang
 * it is a description of st
 *
 */
public class MILP {

	//private Cell c15 = new Cell(new int[]{14}, new int[]{14}, 1000,1000);//save zone
	//private Cell c16 = new Cell(new int[]{13}, new int[]{13}, 1000,1000);
	private int Cell_Num;
	private int T_true;
	private int P;
	public double[][] d;//DEMAND
	private double[] c;//cost
	private int Buscapacity;
	private double BigM;
    private int[] Tau; //tau_max
    private double ld;
    private double DirectSolveResult;
	public HashMap<Integer,Cell> allcell;
    public HashMap<Integer,Cell> sourcecell ;
    public HashMap<Integer,Cell> intermediatecell;
    public HashMap<Integer,Cell> sinkcell;
    private double[] dual; 
    private HashMap<Integer,IloRange[]> cs;//constraintset: i,t
    private HashMap<Integer,double[]> ds;//dualset
    private HashMap<Integer,Integer> cl;//current location 
    private IloCplex cplex;
    private Integer Tq;
    private HashMap<Integer,Integer> Tp;
    private HashMap<Integer,Double> beta;
    private int[][][] B;//right hand side of b variables
    private Cell[] C;
    private double[][][] bc;//path for all bus for total time horizon
    private double[][][] be;
    private double[][][] bl;
    private double[][] bs;//shortest path
    private double[][] es;
    private double[][] ls;
    private int iniloc[]; // initial location for each bus
    private double[][] xV;//x value
    private double[][][] yV;//y value
    private double [][][] bV;//b value
    private double [][][] LV;//L value
    private double [][][] EV;//E value
    private double [][] hV;//h value
    private int[] AllCellIndex;
    private int[] scl;//source cell list
	private int[] inl;//inter cell list
	private int[] skl;//sink cell list
	private ArrayList<Integer> eb1;//duplicate for eb
	private double pcb;//number of people carried by buses
	double DTAobj;//objvalue for DTA model 
	public MILP() {
		
	}
	
	public class Model{
 	   private IloLinearNumExpr obj;
 	   private IloLinearNumExpr num_expr;
 	   private IloNumVar x[][];
 	   private IloNumVar y[][][];
 	   private IloIntVar b[][][];
       private IloIntVar E[][][];
       private IloIntVar L[][][];
       private IloNumVar h[][];
       private ArrayList<ArrayList<Integer>> busRt;
       private ArrayList<ArrayList<Double>> busLd;
 	   public Model(){    		        	   
	    	
	    	x = new IloNumVar[Cell_Num][T_true];
	  	     y = new IloNumVar[Cell_Num][Cell_Num][T_true];
	  	     b = new IloIntVar[P][Cell_Num][T_true];
	   		 E = new IloIntVar[P][Cell_Num][T_true];
	   		 L = new IloIntVar[P][Cell_Num][T_true]; 
	   		 h = new IloNumVar[P][T_true];
	    	
 	   }
 	   public void smallnw() {
 		   
 	   }
       public void CreatModel(){
       	 
     	    	 try{
                		cplex = new IloCplex();
                		for(int i:allcell.keySet()){
                			for(int t=0;t<T_true;t++){
                				x[i][t] = cplex.numVar(0, Double.MAX_VALUE );
                				x[i][t].setName("x."+i+"."+t);               				
                			}
                		}
                		for(int i:allcell.keySet()){
                			for(int j:allcell.get(i).getSucessor()){  
                			    for(int t=0;t<T_true;t++){                			    	
                			    	y[i][j][t] = cplex.numVar(0,Double.MAX_VALUE);
                			    	y[i][j][t].setName("y."+i+"."+j+"."+t);  
                				}     				
                			}
                		}
                		
                		System.out.println("all cell"+allcell.keySet());
                		for(int t=0;t<T_true;t++){
             			  for(int i:allcell.keySet()){
             				for(int p=0;p<P;p++){
             					b[p][i][t]= cplex.boolVar();
             					b[p][i][t].setName("b."+p+"."+i+"."+t);       				 
             					E[p][i][t]= cplex.boolVar();
             					E[p][i][t].setName("be."+p+"."+i+"."+t);  
             					L[p][i][t]= cplex.boolVar();
             					L[p][i][t].setName("bl."+p+"."+i+"."+t);  
             				}             				
             			  }
             		    }
                		
                		for(int t=0;t<T_true;t++) {
                			for(int p=0;p<P;p++) {
                				h[p][t]=cplex.numVar(0.0, Buscapacity);
                				h[p][t].setName("h."+p+"."+t);
                			}
                		}

 /**
  * object fouction               		
  */

                		obj = cplex.linearNumExpr();
                		for(int t=0;t<T_true;t++){
                			for(int i:sourcecell.keySet()) {
                				obj.addTerm(1.0, x[i][t]);
                			}
                			for(int i:intermediatecell.keySet()) {
                				obj.addTerm(1.0, x[i][t]);
                			}
                			for(int p=0;p<P;p++) {
                				for(int g=0;g<=t;g++) {
                					for(int i:sourcecell.keySet()) {
                						obj.addTerm(ld, b[p][i][g]);
                					}
                					for(int i:sinkcell.keySet()) {
                						obj.addTerm(-ld, b[p][i][g]);
                					}
                				}
                			}         
                			for(int p=0;p<P;p++) {
                				obj.addTerm(-1.0, h[p][t]);
                			}
                			/*
                			for(int p=0;p<P;p++){
                				obj.addTerm(1.0,h[p][t]);
                				obj.addTerm(-1.0,u[p][t]);
                			}*/
                		}
                		cplex.addMinimize(obj);
 /**
  * constraints               		
  */
                		for(int i:sourcecell.keySet()){
                			for(int t=1;t<T_true;t++){
                				num_expr = cplex.linearNumExpr();
                				num_expr.addTerm(1.0, x[i][t]);
                				num_expr.addTerm(-1.0,x[i][t-1]);
                				for(int j: allcell.get(i).getSucessor()){
                					num_expr.addTerm(1.0, y[i][j][t-1]);
                				}
                				for(int k:allcell.get(i).getPredecessor()){
                					num_expr.addTerm(-1.0,y[k][i][t-1]);
                				}
                				for(int p=0;p<P;p++){
                					num_expr.addTerm(ld,b[p][i][t-1]);
                				}                				
                				cplex.addEq(num_expr, d[i][t-1]);                				                			
                			}
                		}
                		
                		for(int i:intermediatecell.keySet()){
                			for(int t=1;t<T_true;t++){
                				num_expr = cplex.linearNumExpr();
                				num_expr.addTerm(1.0, x[i][t]);
                				num_expr.addTerm(-1.0,x[i][t-1]);
                				for(int j: allcell.get(i).getSucessor()){
                					num_expr.addTerm(1.0, y[i][j][t-1]);
                				}
                				for(int k:allcell.get(i).getPredecessor()){
                					num_expr.addTerm(-1.0,y[k][i][t-1]);
                				}
                				cplex.addEq(num_expr, 0);                				                			
                			}
                		}
                		
                		for(int i:sinkcell.keySet()){
                			for(int t=1;t<T_true;t++){
                				num_expr = cplex.linearNumExpr();
                				num_expr.addTerm(1.0, x[i][t]);
                				num_expr.addTerm(-1.0,x[i][t-1]);
                				for(int j: allcell.get(i).getSucessor()){
                					num_expr.addTerm(1.0, y[i][j][t-1]);
                				}
                				for(int k:allcell.get(i).getPredecessor()){
                					num_expr.addTerm(-1.0,y[k][i][t-1]);
                				}
                				for(int p=0;p<P;p++){
                					num_expr.addTerm(-ld,b[p][i][t-1]);
                				}                				                				
                				cplex.addEq(num_expr, 0);                				                			
                			}
                		}
                		
                		for(int i:allcell.keySet()){
                			for(int t=0;t<T_true;t++){
                				num_expr = cplex.linearNumExpr();
                				for(int j : allcell.get(i).getSucessor()){
                					num_expr.addTerm(1.0,y[i][j][t]);
                				}
                				num_expr.addTerm(-1.0,x[i][t]);
                				cplex.addLe(num_expr, 0);
                			}
                		}
                		
                		for(int i:allcell.keySet()){
                			for(int t=0;t<T_true;t++){
                				num_expr = cplex.linearNumExpr();
                				
                				for(int j : allcell.get(i).getSucessor()){
                					num_expr.addTerm(1.0,y[i][j][t]);
                				}
                				for(int p=0;p<P;p++){
                					num_expr.addTerm(1.0,L[p][i][t]);
                				}
                				cplex.addLe(num_expr, allcell.get(i).getFlow());
                			}
                			
                		}
                		
                		for(int i:allcell.keySet()){
                			for(int t=0;t<T_true;t++){
                				num_expr = cplex.linearNumExpr();
                				
                				for(int k : allcell.get(i).getPredecessor()){
                					num_expr.addTerm(1.0,y[k][i][t]);
                				}
                				for(int p=0;p<P;p++){
                					num_expr.addTerm(1.0,E[p][i][t]);
                				}
                				cplex.addLe(num_expr, allcell.get(i).getFlow());
                			}
                			
                		}
                		
                		for(int i:allcell.keySet()){
                			//System.out.println(i);
                			for(int t=0;t<T_true;t++){
                				num_expr = cplex.linearNumExpr();
                				for(int k : allcell.get(i).getPredecessor()){
                					num_expr.addTerm(1.0,y[k][i][t]);
                				}
                				num_expr.addTerm(1.0, x[i][t]);
                				for(int p=0;p<P;p++){
                					num_expr.addTerm(1.0,E[p][i][t]);
                				}
                				
                				cplex.addLe(num_expr,allcell.get(i).getCapacity());
                			}
                			//System.out.println();
                		}
                		
                		////////////new FIFO constraints////////////////
                		
                		for(int i:intermediatecell.keySet()) {
                			for(int t =1;t<T_true-1;t++) {
                				for(int p=0;p<P;p++) {   
                					for(int o=1;o<T_true-t;o++) {
                					    num_expr = cplex.linearNumExpr();
                					    num_expr.addTerm(1.0, b[p][i][t+o]);
                					    double temp = 0.0;
                					    temp=1/C[i].getCapacity();
                					    num_expr.addTerm(-temp, x[i][t-1]);
                					    for(int dp=0;dp<P;dp++) {
                					    	if(dp != p) {
                					    		num_expr.addTerm(-temp, b[dp][i][t]);
                					    	}
                					    }
                					    for(int j:allcell.get(i).getSucessor()) {
                					    	for(int k=0;k<=o;k++) {
                					    		num_expr.addTerm(temp, y[i][j][t+k]);
                					    	}
                					    }
                					    
                					    for(int dp=0;dp<P;dp++) {
                					    	if(dp != p) {
                					    		for(int k=0;k<=0;k++) {
                					    			num_expr.addTerm(temp, L[dp][i][t+k]);
                					    		}
                					    	}
                					    }
                					    num_expr.addTerm(-BigM, E[p][i][t]);
                					    double temp2 = 0.0;
                					    temp2 = -BigM;
                					    cplex.addGe(num_expr, temp2);
                					    
                					}
                				}
                			}
                		}
                		
                		
                		
                 		for(int t=0;t<T_true;t++){
                 				for(int p=0;p<P;p++){
                 					num_expr = cplex.linearNumExpr();
                 					for(int i:allcell.keySet()){
                 					num_expr.addTerm(1.0, b[p][i][t]);
                 					
                 				
                 				}
                 					cplex.addEq(num_expr, 1);
                 			}
                 		}
                 		
                   		for(int t=1;t<T_true;t++){
                 			for(int i:allcell.keySet()){
                 				for(int p=0;p<P;p++){
                 					num_expr = cplex.linearNumExpr();
                 					num_expr.addTerm(1.0,E[p][i][t-1]);
                 					num_expr.addTerm(-1.0,b[p][i][t]);
                 					num_expr.addTerm(1.0,b[p][i][t-1]);
                 					cplex.addGe(num_expr, 0);        				
                 				}
                 			}
                 		}
                 		
                 		for(int t=1;t<T_true;t++){
                 			for(int i:allcell.keySet()){
                 				for(int p=0;p<P;p++){
                 					num_expr = cplex.linearNumExpr();
                 					num_expr.addTerm(1.0,L[p][i][t-1]);
                 					num_expr.addTerm(-1.0,b[p][i][t-1]);
                 					num_expr.addTerm(1.0,b[p][i][t]);
                 					cplex.addGe(num_expr, 0);
                 				
                 				}
                 			}
                 		}
                 		
                 		for(int t=0;t<T_true;t++) {
                 			for(int p=0;p<P;p++) {
                 				num_expr = cplex.linearNumExpr();           
                 				for(int g=0;g<=t;g++) {
                 					for(int i:sourcecell.keySet()) {
                 						num_expr.addTerm(ld,b[p][i][g]);
                 					}
                 					for(int i:sinkcell.keySet()) {                 				
                 						num_expr.addTerm(-ld, b[p][i][g]);
                 					}
                 				}
                 					cplex.addGe(num_expr, 0);
                 					cplex.addLe(num_expr, Buscapacity);
                 			}
                 		}

                 		
                 		for(int t=1;t<T_true;t++){
                 			for(int i:allcell.keySet()){
                 				for(int p=0;p<P;p++){
                 					num_expr = cplex.linearNumExpr();
                 					for(int j:allcell.get(i).getSucessor()){
                 						num_expr.addTerm(1.0, b[p][j][t]);
                 					}
                 					num_expr.addTerm(-1.0, b[p][i][t-1]);
                 					num_expr.addTerm(1.0, b[p][i][t]);
                 					cplex.addGe(num_expr, 0);
                 				}
                 			}
                 		}
///////////////////////////////////constraints for H variables///////////////////////
                 		
                 		for(int t=1;t<T_true;t++) {
                 			for(int p=0;p<P;p++) {
                 		////////////first constraint///
                 				num_expr = cplex.linearNumExpr();
                 				num_expr.addTerm(1.0, h[p][t]);
                    				for(int g=0;g<=t-1;g++) {
                    					for(int i:sourcecell.keySet()) {
                    						num_expr.addTerm(-1.0*ld, b[p][i][g]);
                    					}
                    					for(int i:sinkcell.keySet()) {
                    						num_expr.addTerm(ld, b[p][i][g]);
                    				    }
                    			    }
                    			cplex.addLe(num_expr, 0.0);
                    	////////////second constraint////
                    			num_expr = cplex.linearNumExpr();
                    			num_expr.addTerm(1.0,h[p][t]);
                    			for(int i:sinkcell.keySet()) {
                    				num_expr.addTerm(-BigM, b[p][i][t]);
                    			}
                    			cplex.addLe(num_expr, 0.0);
                 			}
                 		}
   ///////////////////////////////////test preset variables////////////////////////
                 		
     	    	 }catch (IloException e) {
        				System.err.println("Concert exception caught: " + e);        				
        			}
 	             }
      /**
       * set initial variables for model
       */
          public void iniVar() {
        	  try {
        		//x variable start with 0
           		for(int i:allcell.keySet()) {
           			num_expr=cplex.linearNumExpr();
           			num_expr.addTerm(1.0, x[i][0]);
           			cplex.addEq(num_expr, 0);
           		}
           		
           		for(int p=0;p<P;p++) {
           			num_expr=cplex.linearNumExpr();
           			num_expr.addTerm(1.0, h[p][0]);
           			cplex.addEq(num_expr, 0);
           		}
           		//make bus stay in specific cell
           		//initate location for buses             		      		
           		for(int p=0;p<P;p++) {
           			num_expr=cplex.linearNumExpr();
               		num_expr.addTerm(1.0, b[p][iniloc[p]][0]);
               		cplex.addEq(num_expr, 1.0);
           		}
        	  }catch(IloException e) {
        		  System.err.println("Concert exception caught: " + e); 
        	  }
          }
          public void setbusR(int a, int[] c) {
              try {           	  
        	     for(int t=0;t<c.length;t++) {      
        		     int temp = c[t];
        		     num_expr=cplex.linearNumExpr();
        		     num_expr.addTerm(1.0,b[a][temp][t] );
        		     cplex.addEq(num_expr, 1.0);
        	  }
        	     System.out.println("finish setting bus route");
        	     cplex.exportModel("temp.lp");
              }catch(IloException e) {
            	  System.err.println("Concert exception caught: " + e);  
              }
          }
          public void solve(){
         	 try{
         		    cplex.exportModel("SubProblemD.lp");  
 				    cplex.solve();
 				 }catch(IloException e){
 	        			e.printStackTrace();
 	        			}
          }
          public void testmethod(){
        	  try {
        		  num_expr=cplex.linearNumExpr();
        		  num_expr.addTerm(1.0, x[7][20]);
        		  cplex.addEq(num_expr, 34);
        	  }catch(IloException e) {
        		  e.printStackTrace();
        	  }
          }
          public void recordValue() {
        	 
        	  busRt = new ArrayList<ArrayList<Integer>>();
        	  busLd = new ArrayList<ArrayList<Double>>();
        	  
  	    	for(int p=0;p<P;p++) {
  	    		busRt.add(new ArrayList<Integer>());
  	    	}
        	  try {
        		  DirectSolveResult=cplex.getObjValue();
        		  ///////////////// flow value assignment//////////////////
        		  
        		  for(int t=0;t<T_true;t++) {
        			  for(int i:allcell.keySet()) {
        				  xV[i][t] = cplex.getValue(x[i][t]);
        				  for(int j:allcell.get(i).getSucessor()) {          
        						  yV[i][j][t]=cplex.getValue(y[i][j][t]);
        				  }
        			  }
        		  }
        		  
        		  //////////////// integer value assignment/////////////
        		  for(int p=0;p<P;p++){
					   for(int t=0;t<T_true;t++){
					    	for(int i:allcell.keySet()){ 					    		
					    			double tempb = cplex.getValue(b[p][i][t]); 
					    			if(tempb>0.99&&tempb<1.1){
										bV[p][i][t] = 1.0;
										busRt.get(p).add(i);
									}
					 
					    			double templ = cplex.getValue(L[p][i][t]);
									if(templ>0.99&&templ<1.1){
										LV[p][i][t] = 1.0;
									}
									
									double tempe = cplex.getValue(E[p][i][t]);
									if(tempe>0.99&&tempe<1.1){
										EV[p][i][t] = 1.0;
									}
					    		}
					    	}
					    }
        		  //////////////h value assignment////////////////
        		  for(int t=0;t<T_true;t++) {
        			  for(int p=0;p<P;p++) {
        				  hV[p][t] = cplex.getValue(h[p][t]);
        			  }
        		  }
        		  
        		  ////////////// calculate bus load/////////////////////
        		  				
						for(int p=0;p<P;p++) {
							busLd.add(new ArrayList<Double>());
							double temp=0;
							for(int t=0;t<T_true;t++) {
							    for(int i : sourcecell.keySet()) {
							    	temp = temp + bV[p][i][t];
							    }
							    for(int i : sinkcell.keySet()) {
							    	temp = temp - bV[p][i][t];
							    }
							    busLd.get(p).add(temp);
							}
							
						}
        	  }catch(IloException e) {
        		  e.printStackTrace();
        	  }
          } 
        
          public void output() {
					System.out.println("DirectSolveResult"+DirectSolveResult);
					outputbs();					
					outputbsLd();
					outputh();
					for(int i:allcell.keySet()) {
						outputXflow(i,T_true);
					}
					//outputYflow(3,1,T_true);
					//outputYflow(1,6,T_true);
					/*
					for(int i:sinkcell.keySet()) {
						outputXflow(i,T_true);
					}*/
				
          }													
          public void outputbs() {
        		  for(int p=0;p<P;p++) {
        			  System.out.println("bus  "+p+" :"+busRt.get(p)); 
                   }
          }
          public void outputbsLd() {
        	  for(int p=0;p<P;p++) {    			
    			  System.out.println("Ld  "+p+" :"+busLd.get(p));
               }
          }
         public void outputXflow(int a,int c) {        	         	
        	 System.out.println("flow in cell < "+a+" >");
        	      System.out.println(0+" | "+xV[a][0]); 
					for(int t=1;t<c;t++) {
						if(xV[a][t]>0) {
						System.out.println(t+" | "+xV[a][t]); 				
						}
					}
					

         }
         public void outputh() {
        	 for(int p=0;p<P;p++) {
        		 System.out.println("bus "+p+" h value");
        		 for(int t=0;t<T_true;t++) {
        			 System.out.println(t+" | "+hV[p][t] );
        			 
        		 }
        	 }
         }
         /**
          * 
          * @param a from
          * @param b to
          * @param c time
          */
         public void outputYflow(int a, int b, int c) {
        	 System.out.println("flow from < " +a+" >--< "+b+" >");
        	 double temp=0.0;
        	 for(int t=0;t<c;t++) {
        		 if(yV[a][b][t]>0) {
        			 temp=1.0;
        		 System.out.println(t+" | "+yV[a][b][t]);
        		 }
        	 }
        	 if(temp==0.0) {
        		 System.out.println("N/A");
        	 }
         }
         
         /**
          * out put all Y flow value if >0 until a time step
          * @param a maximum time step
          */
         public void outputYpos(int a) {
        	 for(int i:allcell.keySet()) {
        		 for(int j:allcell.get(i).getSucessor()) {
        			 outputYflow(i,j,a );
        		 }
        	 }
         }
         
         /**
          * update net work by specify cell, number and time 
          * @param cr Cell
          * @param nr Number of demand
          * @param tr Time
          */
         public void updateNW(int cr, int nr, int tr) {   
        	 try {
        	 
        	    d[cr][tr]=nr;
        	    CreatModel();
        	    
        	    for(int t=0;t<=tr;t++) {
        	       for(int i:allcell.keySet()) {
        		       num_expr = cplex.linearNumExpr();
        		       num_expr.addTerm(1.0, x[i][t]);
        		       cplex.addEq(num_expr, xV[i][t]);
        		       
        		       for(int j : C[i].getSucessor()) {
        		    	   num_expr = cplex.linearNumExpr();
        		    	   num_expr.addTerm(1.0, y[i][j][t]);
        		    	   cplex.addEq(num_expr, yV[i][j][t]);
        		       }
        	       }          
        	    }

        	    
        	    for(int t=0;t<=tr;t++) {
        	    	for(int p=0;p<P;p++) {
            		    num_expr = cplex.linearNumExpr();
            		    num_expr.addTerm(1.0, b[p][busRt.get(p).get(t)][t]);
            		    cplex.addEq(num_expr, 1.0);
            	    }
        	    }
        	    /*
        	    for(int p=0;p<P;p++) {
        	    	int tempt = tr+1;
        	    	while(busLd.get(p).get(tempt)>0.0) {
        	    		num_expr = cplex.linearNumExpr();
        	    		num_expr.addTerm(1.0, b[p][busRt.get(p).get(tempt)][tempt]);
        	    		cplex.addEq(num_expr, 1);
        	    		tempt = tempt+1;
        	    	}
        	    }*/
        	    cplex.exportModel("update model.lp");
        	    
        	    
        	    }catch(IloException e) {
        		    System.err.println("Concert exception caught: " + e);  
        	    }
        	 
            }
        }
	      
	
	//DTA model to solve during iteration
	public class DTA {
	 	   private IloLinearNumExpr obj;
	 	   private IloLinearNumExpr num_expr;
	 	   private IloNumVar x[][];
	 	   private IloNumVar y[][][];
	 	   private IloIntVar b[][][];
	       private IloIntVar E[][][];
	       private IloIntVar L[][][];
	       private double[] flow;
		   public DTA(double[][][] a, double[][][] b, double[][][] c) {
	 	         bc=a;
	 	         be=b;
	 	         bl=c;
	 	         flow=new double[T_true];
	 	         //System.out.println(d[2][0]);
	 	         //System.out.println(d[1][0]);
		   }
		   public void getdual() {
			 x = new IloNumVar[Cell_Num][T_true];
	  	     y = new IloNumVar[Cell_Num][Cell_Num][T_true];
	  	     //b = new IloIntVar[P][Cell_Num][T_true];
	   		 //E = new IloIntVar[P][Cell_Num][T_true];
	   		 //L = new IloIntVar[P][Cell_Num][T_true]; 
	         cs = new HashMap<Integer,IloRange[]>();
	         ds = new HashMap<Integer,double[]>();
	     	    	 try{    
	                		cplex = new IloCplex();
	                		for(int i:allcell.keySet()){
	                			for(int t=0;t<T_true;t++){
	                				x[i][t] = cplex.numVar(0, Double.MAX_VALUE );
	                				x[i][t].setName("x."+i+"."+t);               				
	                			}
	                		}
	                		for(int i:allcell.keySet()){
	                			for(int j:allcell.keySet()){
	                				if(i != j) {
	                			    for(int t=0;t<T_true;t++){                			    	
	                			    	y[i][j][t] = cplex.numVar(0,Double.MAX_VALUE);
	                			    	y[i][j][t].setName("y."+i+"."+j+"."+t);  
	                			    }
	                			   }        				
	                			}
	                		}

	 /**
	  * object fouction               		
	  */
	                		obj = cplex.linearNumExpr();
	                		for(int t=0;t<T_true;t++){
	                			for(int i:sourcecell.keySet()) {
	                				obj.addTerm(c[t], x[i][t]);
	                			}
	                			for(int i:intermediatecell.keySet()) {
	                				obj.addTerm(c[t], x[i][t]);
	                			}
	                			               			
	                		}
	                		cplex.addMinimize(obj);
	 /**
	  * constraints               		
	  */
	                		for(int i:sourcecell.keySet()){
	                		    IloRange[] c1 = new IloRange[T_true];
	                			for(int t=1;t<T_true;t++){
	                				num_expr = cplex.linearNumExpr();
	                				num_expr.addTerm(1.0, x[i][t]);
	                				num_expr.addTerm(-1.0,x[i][t-1]);
	                				for(int j: allcell.get(i).getSucessor()){
	                					num_expr.addTerm(1.0, y[i][j][t-1]);
	                				}
	                				for(int k:allcell.get(i).getPredecessor()){
	                					num_expr.addTerm(-1.0,y[k][i][t-1]);
	                				}
                                // delete the demand by bus
	                				double temp =0;
	                				for(int p=0;p<P;p++) {
	                					
	                					temp = temp+bc[p][i][t-1];
	                				}
	                				c1[t]=cplex.addEq(num_expr, d[i][t-1]-ld*temp);                				                			
	                			}
	                			cs.put(i, c1);
	                		}
	                		
	                		for(int i:intermediatecell.keySet()){
	                			//System.out.println(i);
	                			for(int t=1;t<T_true;t++){
	                				num_expr = cplex.linearNumExpr();
	                				num_expr.addTerm(1.0, x[i][t]);
	                				num_expr.addTerm(-1.0,x[i][t-1]);
	                				for(int j: allcell.get(i).getSucessor()){
	                					
	                					
	                					num_expr.addTerm(1.0, y[i][j][t-1]);
	                				}
	                				for(int k:allcell.get(i).getPredecessor()){
	                					num_expr.addTerm(-1.0,y[k][i][t-1]);
	                				}
	                				cplex.addEq(num_expr, 0);                				                			
	                			}
	                		}
	                		
	                		for(int i:sinkcell.keySet()){
	                			for(int t=1;t<T_true;t++){
	                				num_expr = cplex.linearNumExpr();
	                				num_expr.addTerm(1.0, x[i][t]);
	                				num_expr.addTerm(-1.0,x[i][t-1]);
	                				for(int j: allcell.get(i).getSucessor()){
	                					num_expr.addTerm(1.0, y[i][j][t-1]);
	                				}
	                				for(int k:allcell.get(i).getPredecessor()){
	                					num_expr.addTerm(-1.0,y[k][i][t-1]);
	                				}
	                				// increase people in sink cell dropped by buses
	                				double temp=0;
	                				for(int p=0;p<P;p++) {
	                					temp = temp+bc[p][i][t-1];
	                				}               				                				
	                				cplex.addEq(num_expr, ld*temp);                				                			
	                			}
	                		}
	                		
	                		for(int i:allcell.keySet()){
	                			for(int t=0;t<T_true;t++){
	                				num_expr = cplex.linearNumExpr();
	                				for(int j : allcell.get(i).getSucessor()){
	                					num_expr.addTerm(1.0,y[i][j][t]);
	                				}
	                				num_expr.addTerm(-1.0,x[i][t]);
	                				cplex.addLe(num_expr, 0);
	                			}
	                		}
	                		
	                		for(int i:allcell.keySet()){
	                			for(int t=0;t<T_true;t++){
	                				num_expr = cplex.linearNumExpr();
	                				
	                				for(int j : allcell.get(i).getSucessor()){
	                					num_expr.addTerm(1.0,y[i][j][t]);
	                				}
	                				//sum up the leaving variables
	                				double temp=0;
	                				for(int p=0;p<P;p++){
	                					temp=temp+bl[p][i][t];
	                				}
	                				cplex.addLe(num_expr, allcell.get(i).getFlow()-temp);
	                			}
	                			
	                		}
	                		
	                		for(int i:allcell.keySet()){
	                			for(int t=0;t<T_true;t++){
	                				num_expr = cplex.linearNumExpr();
	                				
	                				for(int k : allcell.get(i).getPredecessor()){
	                					num_expr.addTerm(1.0,y[k][i][t]);
	                				}
	                				double temp=0;
	                				for(int p=0;p<P;p++){
	                					temp=temp+be[p][i][t];
	                				}
	                				cplex.addLe(num_expr, allcell.get(i).getFlow()-temp);
	                			}
	                			
	                		}
	                		
	                		for(int i:allcell.keySet()){
	                			for(int t=0;t<T_true;t++){
	                				num_expr = cplex.linearNumExpr();
	                				for(int k : allcell.get(i).getPredecessor()){
	                					num_expr.addTerm(1.0,y[k][i][t]);
	                				}
	                				num_expr.addTerm(1.0, x[i][t]);
	                				double temp=0;
	                				for(int p=0;p<P;p++){
	                					temp=temp+be[p][i][t];
	                				}
	                				
	                				cplex.addLe(num_expr,allcell.get(i).getCapacity()-temp);
	                			}
	                		} 	 	 
	                		
              		//x variable start with 0
              		for(int i:allcell.keySet()) {
              			num_expr=cplex.linearNumExpr();
              			num_expr.addTerm(1.0, x[i][0]);
              			cplex.addEq(num_expr, 0);
              		}                  		
              		//cplex.exportModel("SubProblemD.lp");     
              		cplex.setParam(IloCplex.Param.MIP.Display , 0);
  				    cplex.solve();
  				    for(int i:sourcecell.keySet()) {
  				    	double[] temp = new double[T_true];
  				    	for(int t=1;t<T_true;t++) {
  				    		temp[t]=cplex.getDual(cs.get(i)[t]);
  				    	}
  				    	ds.put(i, temp);
  				    }
  				    
  				    //retrive flow pattern
  				   for(int t=0;t<T_true;t++) {
  					   double temp=0;
  					  for(int i:sourcecell.keySet()) {
  	 					   temp=cplex.getValue(x[i][t])+temp;
  	 					   
  	 				   }
  					 for(int i:intermediatecell.keySet()) {
	 					   temp=cplex.getValue(x[i][t])+temp;
	 					   
	 				   }
  					   flow[t]=temp;
  	 			   }
  				    DTAobj=cplex.getObjValue();
  				    hV = new double[P][T_true];
  				    for(int t=1;t<T_true;t++) {
  				    	for(int p=0;p<P;p++) {
  				    		double temp=0;
  				    		for(int g=1;g<=t;g++) {
  				    			for(int i:sourcecell.keySet()) {
  				    				temp = temp + bc[p][i][g];
  				    			}
  				    			for(int i:sinkcell.keySet()) {
  				    				temp = temp - bc[p][i][g];
  				    			}
  				    		}
  				    		hV[p][t]=temp;
  				    		
  				    	}
  				    }
  				    
  				    for(int i:allcell.keySet()) {
  				    	for(int t=1;t<T_true;t++) {
  				    		xV[i][t]=cplex.getValue(x[i][t]);
  				    	}
  				    }
  				    for(int t=1;t<T_true;t++) {
  				    	for(int p=0;p<P;p++) {
  				    		double temp=0;
  				    		for(int i:sourcecell.keySet()) {
  				    			temp = temp + bc[p][i][t];
  				    		}
  				    		for(int i:intermediatecell.keySet()) {
  				    			temp = temp + bc[p][i][t];
  				    		}
  				    		DTAobj = DTAobj + hV[p][t]*temp;
  				    	}
  				    }
		             }catch (IloException e) {
      				System.err.println("Concert exception caught: " + e);        				
      			}
	          }
		   void outputflowEndTime(){
			  
			  for(int t=1;t<flow.length;t++) {
				  if(flow[t]<1) {
				  System.out.println("==========evacuation end at"+t+"=============");
				  break;
				  }
			  }
		   }
		   void output() {
			   for(int i:sourcecell.keySet()) {
				   double[] temp = ds.get(i);
				  System.out.println("cell "+i);
				   for(int t=0;t<T_true;t++) {
					   System.out.println(temp[t]);
				   }
			   }
		   }
	   }
	   public void initiate(){
		   Cell_Num = 15;
		   T_true = 40;
		   
		   d = new double[Cell_Num][T_true];
		   d[1][0]=30;
		   d[2][20]=30;
		   //d[2][10]=60;
		   //d[1][10]=60;//increased demand
		   c = new double[T_true];
		   C = new Cell[Cell_Num];
		   Tau = new int[Cell_Num];
		   for(int t=0;t<T_true;t++) {
			   //c[t]=T_true-t;
			   c[t]=1;
		   }
		   P=3;
		   ld=1.0;
		   Buscapacity=3;
		   BigM=Buscapacity;
		   iniloc = new int[P];
		   iniloc[0]=9;iniloc[1]=9;iniloc[2]=9;

		   xV = new double[Cell_Num][T_true];
		   yV = new double[Cell_Num][Cell_Num][T_true];
		   bV = new double[P][Cell_Num][T_true];
		   LV = new double[P][Cell_Num][T_true];
		   EV = new double[P][Cell_Num][T_true];
		   hV = new double[P][T_true];
		   
		   cl = new HashMap<Integer,Integer>();
		    C[1] = new Cell(new int[]{3}, new int[]{6}, 1000,1000);
			C[2] = new Cell(new int[]{5}, new int[]{4}, 1000,1000);
			C[3] = new Cell(new int[]{8,9}, new int[]{1}, 4,32);
			C[4] = new Cell(new int[]{2}, new int[]{7,10}, 4,32);
			C[5] = new Cell(new int[]{7,11}, new int[]{2}, 4,32);
			C[6] = new Cell(new int[]{1}, new int[]{8,12}, 4,32);
			C[7] = new Cell(new int[]{4,9}, new int[]{5,12}, 4,32);
			C[8] = new Cell(new int[]{6,11}, new int[]{3,10}, 4,32);
			C[9] = new Cell(new int[]{14}, new int[]{3,7}, 2,32);
			C[10] = new Cell(new int[]{4,8}, new int[]{13}, 2,32);
			C[11] = new Cell(new int[]{13}, new int[]{5,8}, 2,32);
			C[12] = new Cell(new int[]{6,7}, new int[]{14}, 2,32);
			C[13] = new Cell(new int[]{10}, new int[]{11}, 1000,1000);//sink cell
			C[14] = new Cell(new int[]{12}, new int[]{9}, 1000,1000);
			
 		   allcell = new HashMap<Integer, Cell>();
 		   for(int i=1;i<Cell_Num;i++) {
 			   allcell.put(i, C[i]);
 			 
 		   }
 		   
 		   sourcecell = new HashMap<Integer,Cell>();
 		   sourcecell.put(1, C[1]);sourcecell.put(2, C[2]);
 		   
 		   intermediatecell = new HashMap<Integer,Cell>();
 		   for(int i=3;i<=12;i++) {
 			   intermediatecell.put(i, C[i]);
 		   } 		   
 		   sinkcell = new HashMap<Integer,Cell>();
 		   sinkcell.put(13,C[13]);sinkcell.put(14,C[14]);
 		   
 		   for(int i:intermediatecell.keySet()) {
 			  int temp=(int) (intermediatecell.get(i).getCapacity()/intermediatecell.get(i).getFlow());
			  Tau[i]=temp;
 		   }
 		  scl = new int[]{1,2};
			inl = new int[]{3,4,5,6,7,8,9,10,11,12,};
			skl = new int[]{13,14};
			AllCellIndex = new int[] {1,2,3,4,5,6,7,8,9,10,11,12,13,14};
 	   }
	   public void inismallnw() {
		   Cell_Num = 7;
		   T_true = 15;
		   d = new double[Cell_Num][T_true];
		   d[1][0]=30;
		   c = new double[T_true];
		   C = new Cell[Cell_Num];
		   Tau = new int[Cell_Num];
		   for(int t=0;t<T_true;t++) {
			   c[t]=T_true-t;
		   }
		   P=1;
		   ld=1;
		   Buscapacity=3;
		   BigM = Buscapacity;
		   iniloc = new int[P];
		   iniloc[0]=5;
		   xV = new double[Cell_Num][T_true];
		   yV = new double[Cell_Num][Cell_Num][T_true];
		   bV = new double[P][Cell_Num][T_true];
		   LV = new double[P][Cell_Num][T_true];
		   EV = new double[P][Cell_Num][T_true];
		   hV = new double[P][T_true];
		   
		   cl = new HashMap<Integer,Integer>();
		    C[1] = new Cell(new int[]{6}, new int[]{2}, 1000,1000);
			C[2] = new Cell(new int[]{1}, new int[]{3}, 4,30);
			C[3] = new Cell(new int[]{2}, new int[]{4}, 2,30);
			C[4] = new Cell(new int[]{3}, new int[]{5}, 1000,1000);
			C[5] = new Cell(new int[]{4}, new int[]{6}, 2,30);
			C[6] = new Cell(new int[]{5}, new int[]{1}, 4,30);
			
 		   allcell = new HashMap<Integer, Cell>();
 		   for(int i=1;i<Cell_Num;i++) {
 			   allcell.put(i, C[i]);
 			 
 		   }
 		   
 		   sourcecell = new HashMap<Integer,Cell>();
 		   sourcecell.put(1, C[1]);
 		   
 		   intermediatecell = new HashMap<Integer,Cell>();
 		   intermediatecell.put(2, C[2]);intermediatecell.put(3, C[3]);
 		   intermediatecell.put(5, C[5]);intermediatecell.put(6, C[6]);
 		   
 		   sinkcell = new HashMap<Integer,Cell>();
 		   sinkcell.put(4,C[4]);
 		   
 		   
 		  for(int i:intermediatecell.keySet()) {
			   int temp=(int) (intermediatecell.get(i).getCapacity()/intermediatecell.get(i).getFlow());
			  Tau[i]=temp;
		   }
	   }
	   /**
	    * change initial cells setting
	    */
	   public void ciniset() {
		   d = new double[Cell_Num][T_true];
		   d[1][0]=50;
		   d[14][0]=100;
		  
		   cl = new HashMap<Integer,Integer>();
		    C[1] = new Cell(new int[]{3}, new int[]{6}, 1000,1000);
			C[2] = new Cell(new int[]{5}, new int[]{4}, 4,32);
			C[3] = new Cell(new int[]{8,9}, new int[]{1}, 4,32);
			C[4] = new Cell(new int[]{2}, new int[]{7,10}, 4,32);
			C[5] = new Cell(new int[]{7,11}, new int[]{2}, 4,32);
			C[6] = new Cell(new int[]{1}, new int[]{8,12}, 4,32);
			C[7] = new Cell(new int[]{4,9}, new int[]{5,12}, 1000,1000);
			C[8] = new Cell(new int[]{6,11}, new int[]{3,10}, 1000,1000);
			C[9] = new Cell(new int[]{14}, new int[]{3,7}, 4,32);
			C[10] = new Cell(new int[]{4,8}, new int[]{13}, 4,32);
			C[11] = new Cell(new int[]{13}, new int[]{5,8}, 4,32);
			C[12] = new Cell(new int[]{6,7}, new int[]{14}, 4,32);
			C[13] = new Cell(new int[]{10}, new int[]{11}, 4,32);//sink cell
			C[14] = new Cell(new int[]{12}, new int[]{9}, 1000,1000);
			
			allcell = new HashMap<Integer, Cell>();
	 		   for(int i=1;i<Cell_Num;i++) {
	 			   allcell.put(i, C[i]);
	 			 
	 		   }
	 		   
		   sourcecell = new HashMap<Integer,Cell>();
 		   sourcecell.put(1, C[1]);sourcecell.put(14, C[14]);
 		   
 		   intermediatecell = new HashMap<Integer,Cell>();
 		   for(int i=2;i<=6;i++) {
 			   intermediatecell.put(i, C[i]);
 		   }
 		  for(int i=9;i<=13;i++) {
			   intermediatecell.put(i, C[i]);
		   } 
 		   sinkcell = new HashMap<Integer,Cell>();
 		   sinkcell.put(7,C[7]);sinkcell.put(8,C[8]);
	   }
	   public class shortestpath {
		   private int o;
		   private int d;
		   //private int p;//the index of bus
		   private double[][] qe;//entering flow capacity
		   private double[][] ql;//leavin flow capacity
		   private IloLinearNumExpr obj;
		   private IloLinearNumExpr num_expr;
		   private IloNumVar[][] b;
		   private int endT;//ending time for shortest path
		   private int endC;//ending cell
		   private HashMap<Integer,Cell> sourcecell1;
		   private HashMap<Integer,Cell> intermediatecell1;
		   private HashMap<Integer,Cell> sinkcell1;
		   private HashMap<Integer,Cell> allcell1;
		   private int T_s;
		   public shortestpath() {
			   bs = new double[Cell_Num][T_true];
				es = new double[Cell_Num][T_true];
				ls = new double[Cell_Num][T_true];
           		allcell1 = allcell;
           		T_s=T_true;
           		
		   }
		   //initiate od pair
		   public void initial1(int a, int b) {
				sourcecell1 = new HashMap<Integer,Cell>();
				intermediatecell1 = new HashMap<Integer,Cell>();
				sinkcell1 = new HashMap<Integer,Cell>();
				//allcell1 =  new HashMap<Integer,Cell>();
				o=a;
				d=b;
				System.out.println("o "+o+" d "+d);
				for(int i:AllCellIndex) {
					allcell1.put(i, C[i]);
					if(i != o && i != d) {
						intermediatecell1.put(i, C[i]);
					}
				}
				sourcecell1.put(o, C[o]);
				sinkcell1.put(d, C[d]);		
				//System.out.println(sourcecell1.keySet());
				//System.out.println(intermediatecell.keySet());
				
			}
		   //initiate drop off trip
			public void initial2(int a) {
				//allcell1 =  new HashMap<Integer,Cell>();
				sourcecell1 = new HashMap<Integer,Cell>();
				intermediatecell1 = new HashMap<Integer,Cell>();
				sinkcell1 = new HashMap<Integer,Cell>();
				o=a;
				for(int i:AllCellIndex) {
					allcell1.put(i, C[i]);
				}
				sourcecell1.put(o, C[o]);
				for(int i=0;i<scl.length;i++) {
					if(scl[i] != o) {
					intermediatecell1.put(scl[i], C[scl[i]]);
					}
				}
				for(int i=0;i<inl.length;i++) {
					intermediatecell1.put(inl[i], C[inl[i]]);
				}
				for(int i=0;i<skl.length;i++) {
					sinkcell1.put(skl[i], C[skl[i]]);
				}
				
			}
			public void creatmodel() {
				try {
					//bc = new double[Cell_Num][T_s];
					//be = new double[Cell_Num][T_s];
					//bl = new double[Cell_Num][T_s];
			  	     b = new IloIntVar[Cell_Num][T_s];
		             cplex = new IloCplex();
		             //set flow limit
		            
		             //q[10][3]=0;
		             //
		             for(int t=0;t<T_s;t++) {
		            	 for(int i:allcell1.keySet()) {
		            		 b[i][t]=cplex.boolVar();
		            		 b[i][t].setName("b."+i+"."+t);
		            	 }
		             }
		             obj = cplex.linearNumExpr();
		             
		             //minimize cell other than sink cell////////////////////////////////////
		             /*
		             for(int t=0;t<T_s;t++) {
		             for(int i:intermediatecell1.keySet()) {
		            	 obj.addTerm(1.0, b[i][t]);
		             }
		             for(int i:sourcecell1.keySet()) {
		            	 obj.addTerm(1.0, b[i][t]);
		             }
		             }
		             cplex.addMinimize(obj);
		             */
		             //maximize sink cell//////////////////////////////////
		             for(int t=0;t<T_s;t++) {
		            	 for(int i:sinkcell1.keySet()) {
		            		 obj.addTerm(1.0, b[i][t]);
		            	 }
		             }
		             cplex.addMaximize(obj);
		             
		             //constraints///////////////////////////////////////
		             for(int t=0;t<T_s;t++) {
		            	 num_expr = cplex.linearNumExpr();
		            	 for(int i:allcell1.keySet()) {
		            		 num_expr.addTerm(1.0, b[i][t]);
		            	 }
		            	 cplex.addEq(num_expr, 1);
		             }
		             
		             for(int t=1;t<T_s;t++){
		      			for(int i:allcell1.keySet()){
		      					num_expr = cplex.linearNumExpr();
		      					//System.out.println(i);
		      					for(int j:allcell1.get(i).getSucessor()){
		      						
		      						num_expr.addTerm(1.0, b[j][t]);
		      					}
		      					num_expr.addTerm(-1.0, b[i][t-1]);
		      					num_expr.addTerm(1.0, b[i][t]);
		      					cplex.addGe(num_expr, 0);      				
		      			}
		      		}
		             
		             for(int i:allcell1.keySet()) {
		            	 for(int t=1;t<T_s;t++) {
		            		 num_expr = cplex.linearNumExpr();
		            		 num_expr.addTerm(1.0, b[i][t]);
		            		 num_expr.addTerm(-1.0, b[i][t-1]);
		            		 cplex.addLe(num_expr, qe[i][t]);
		            	 }
		             }
		             
		             for(int i:allcell1.keySet()) {
		            	 for(int t=1;t<T_s;t++) {
		            		 num_expr = cplex.linearNumExpr();
		            		 num_expr.addTerm(1.0, b[i][t-1]);
		            		 num_expr.addTerm(-1.0, b[i][t]);
		            		 cplex.addLe(num_expr, ql[i][t]);
		            	 }
		             }
		            
		             //initiate location
		             
		             num_expr = cplex.linearNumExpr();
		             System.out.println("o "+o);
		             //System.out.println("cell num "+Cell_Num+" T_s "+T_s);
		             num_expr.addTerm(1.0, b[o][0]);
		             cplex.addEq(num_expr, 1);
		             //set path
		             //cplex.exportModel("SortestPath.lp"); 
				}catch(IloException e) {
					
				}
			}
			public void solve() {
				try {
					//double[][] tempb = new double[Cell_Num][T_s];
					 bs = new double[Cell_Num][T_s];
						es = new double[Cell_Num][T_s];
						ls = new double[Cell_Num][T_s];
						cplex.setParam(IloCplex.Param.MIP.Display , 0);
					if(cplex.solve()==true) {
						for(int t=0;t<T_s;t++) {
							for(int i:allcell1.keySet()) {
								
								if(cplex.getValue(b[i][t])>0.99 &&cplex.getValue(b[i][t])<1.01) {
									//System.out.println("location: "+i+" time: "+t);
									bs[i][t]=1.0;
									// assign value to bc
								}
							}
						}
						
						System.out.println("sinkcell1 "+sinkcell1.keySet());
						for(int t=0;t<T_s;t++) {
							double temp =0;
							for(int i:sinkcell1.keySet()) {
								temp=bs[i][t]+temp;
							}
							if(temp>=1) {
								endT=t;
								break;
							}
						}
						System.out.println("evacuation end: "+endT);
						for(int i:sinkcell1.keySet()) {
							if(bs[i][endT]==1.0) {
								endC=i;
							}
						}
						System.out.println("System end at cell: "+endC);
						cplex.end();
					}
					
				} catch (IloException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				
				for(int t=1;t<T_s;t++) {
					for(int i:allcell1.keySet()) {
						if(bs[i][t]-bs[i][t-1]>0.5) {
							es[i][t]=1.0;
						}
						if(bs[i][t-1]-bs[i][t]>0.5) {
							ls[i][t]=1.0;
						}
						
					}
				}
			}
			//update flow capacity q for current time, start from t=1;
			public void initiateq(int time,int b) {
		  	     ql = new double[Cell_Num][T_s];
		  	     qe = new double[Cell_Num][T_s];
		  	     for(int t=0;t<T_s;t++) {
	            	 for(int i:allcell1.keySet()) {
	            		 qe[i][t]=1;
	            		 ql[i][t]=1;
	            	 }
	              }
				for(int t=time+1;t<T_s;t++) {
					for(int i:allcell1.keySet()) {
						double tempe=0;
						double templ=0;
						for(int p=0;p<P;p++) {
							if(p != b) {
							if(bc[p][i][t]-bc[p][i][t-1]==1) {
								tempe=tempe+1;
							}
							if(bc[p][i][t-1]-bc[p][i][t]==1) {
								templ=templ+1;
							}
							}
						}
						double flow = allcell1.get(i).getFlow();
						if(tempe == flow) {
							qe[i][t-time]=0;
						}else {
							qe[i][t-time]=1;
						}
						if(templ == flow) {
							ql[i][t-time]=0;
						}else {
							ql[i][t-time]=1;
						}
					}
				}
				
			}
			public void start(int a,int b,int time,int p){
				
				initiateq(time,p);
				initial1(a,b);
				//start(1,13);
				creatmodel();
				solve();			
				
			}
			
			public void end(int a,int time,int p) {
				initiateq(time,p);
				initial2(a);
				creatmodel();
				solve();
				 
			}
			public int outputT() {
				return endT;
			}
			public int outputC() {
				return endC;
			}
			public double[][] outputb(){
				return bs;
			}
			public double[][] outputE(){
				return es;
			}
			public double[][] outputL(){
				return ls;
			}
			
			/**
			 * input entering variable
			 * @param a
			 */
			
			public void updateq(int[][][] a) {
				for(int t=0;t<T_s;t++) {
					for(int i:allcell1.keySet()) {
						int temp=0;
						for(int p=0;p<P;p++) {
							temp=a[p][i][t];
						}
						if(temp>0) {
							qe[i][t]=0.0;
						}else {
							qe[i][t]=1.0;
						}
					}
				}
			}
	   }
	   
	   public void heuristic() {
		   Tq=0;
		   B = new int[P][Cell_Num][T_true];
		   //System.out.println("P "+P+" Cell_Num "+Cell_Num+" T_true "+T_true);
		   //to make bus assignemet variable T_true+greatst possible route length, so that no more outof boundary
		   int te=50;//extra length
		   bc = new double[P][Cell_Num][T_true];
		   be = new double[P][Cell_Num][T_true];
		   bl = new double[P][Cell_Num][T_true];
		   cl = new HashMap<Integer,Integer>();//current location list
		   ArrayList<Integer> eb=new ArrayList<Integer>();//empty bus set
		   Tp = new HashMap<Integer,Integer>();//trip end time for bus p
		   
		   /*
		   for(int p=0;p<P;p++) {
			   eb.add(p);
		   }*/
		   //initiate empty bus list
		   //P=1;
           for(int i=0;i<P;i++) {
        	   eb.add(i);
           }
           //initiate bus current location
           for(int i:eb) {
        	   cl.put(i, iniloc[i]);
           }
		   eb1=eb;

		   
		   for(int p:eb) {
			   Tp.put(p, 0);
		   }
		   
		   double nR=0;//number of vehicle in source cell
		   
		   /*
		   for(int i:sourcecell.keySet()) {
			   System.out.println("x."+i+"."+Tq+" "+flow[i][Tq]);
			   nR = nR+flow[i][Tq];
		   }*/ // flow on 0 timestep is 0
		   
		   nR=1000;//initiate flow in source cell with 1000
		   shortestpath ST= new shortestpath();
		   int ite =0;//iteration number
		   while(eb.isEmpty()==false) {	
			   /*
			   for(int t=0;t<T_true;t++) {
				   for(int i:allcell.keySet()) {
					   for(int p:eb) {
						   if(bc[p][i][t]==1.0) {
							   System.out.println("bc i: "+i+" t: "+t);
						   }
						   if(be[p][i][t]==1.0) {
							   System.out.println("be i: "+i+" t: "+t);
						   }
						   if(bl[p][i][t]==1.0) {
							   System.out.println("bl i: "+i+" t: "+t);
						   }
					   }
				   }
			   }
			   */
			   			   
			   //double[][] flow1 = model1.flow();		
			   System.out.println("=========iteration  "+ite+"=============");
			   System.out.println("eb "+eb);
			   System.out.println("Tp "+Tp);
			   System.out.println("=========prebus assignment=============");
			   
			   for(int p:eb) {
				   DTA model1 = new DTA(bc,be,bl);
				   model1.getdual();
				   System.out.println("====bus "+p+"========");
				   beta = new HashMap<Integer,Double>();
				   ArrayList<Integer> order = new ArrayList<Integer>();
				   int endT=0;
				   int endC=0;
				   /*
				   for(int i:ds.keySet()) {
					   for(int j=0;j<ds.get(i).length;j++) {
						   System.out.println("node "+i+" time "+j +": "+ ds.get(i)[j]);
					   }
				   }*/
				   
				  for(int j:sourcecell.keySet()) {
					  //System.out.println("======eb list ========"+eb);
					 // System.out.println("========from  "+cl.get(p)+" to "+j+"=========");
					  ST.start(cl.get(p), j,Tp.get(p),p);
					  int temp =ST.outputT();
					  double dualsum =0;
					  /*cumulative dual
					  for(int i=0;i<Buscapacity;i++) {
					  dualsum=ds.get(j)[temp+Tp.get(p)+i]+dualsum;//get dual for time Tq+T, cumulative dual		 			  
					  }			
					  */
					  
					  dualsum = ds.get(j)[(int) (temp+Tp.get(p)+(Buscapacity/ld))];
					  beta.put(j, dualsum);
				  }
				  //System.out.println("beta"+beta);
				  
				  order=sort(beta);
				  //System.out.println("=======bus "+p+" =========");
				  //System.out.println(order);
				 
				  int d = order.get(0);
				if(beta.get(d)>0.0) {
				System.out.println("=====assgin to source=====");
				System.out.println(cl.get(p)+" - "+d);
				  ST.start(cl.get(p), d,Tp.get(p),p);
				  endT=ST.outputT();
				  double[][] tempb=ST.outputb();
				  double[][] tempe=ST.outputE();
				  double[][] templ=ST.outputL();
				  
				  System.out.println("Tp: "+Tp.get(p));
				  System.out.println("endT: "+endT);
//================assign the new route to source cell=========================
				  for(int t=0;t<=endT;t++) {
					  for(int i:allcell.keySet()) {
						  bc[p][i][t+Tp.get(p)]=tempb[i][t];
						  be[p][i][t+Tp.get(p)]=tempe[i][t];
						  bl[p][i][t+Tp.get(p)]=templ[i][t];
					  }
				  }
                 int tp = Tp.get(p)+endT;
                 Tp.put(p, tp);
                 //outputp(p);
                 System.out.println("==========");
                 
//================stay in source cell=======================================
                 for(int t=0;t<(Buscapacity/ld);t++) {
                	 bc[p][d][t+Tp.get(p)]=1.0;
                 }
                 tp = Tp.get(p);
                 Tp.put(p, (int) (tp+((Buscapacity/ld)-1)));
                 
//================assign bus to nearest sink cell=======================================
                 System.out.println("=====assgin to sink=====");
                 //System.out.println("Tp "+Tp.get(p) );
                 ST.end(d,Tp.get(p),p);
                 System.out.println("===============");
                 endT=ST.outputT();
				  tempb=ST.outputb();
				  tempe=ST.outputE();
				  templ=ST.outputL();
				  System.out.println("Tp: "+Tp.get(p));
				  System.out.println("endT: "+endT);
				  //assign the new route to source cell
				  for(int t=0;t<=endT;t++) {
					  for(int i:allcell.keySet()) {
						  bc[p][i][t+Tp.get(p)]=tempb[i][t];
						  be[p][i][t+Tp.get(p)]=tempe[i][t];
						  bl[p][i][t+Tp.get(p)]=templ[i][t];
					  }
				  }
                tp = Tp.get(p)+endT;
                Tp.put(p, tp);
                //outputp(p);
                System.out.println("==========");
                
//================dropping people=======================================
                endC = ST.outputC();                 
                 for(int t=0;t<(Buscapacity/ld);t++) {
                	 bc[p][endC][t+Tp.get(p)]=1.0;
                 } 
                 
                 tp = (int) (Tp.get(p)+(Buscapacity/ld)-1);
                 Tp.put(p, tp);   
                 cl.put(p, endC);                 
                 System.out.println("==========bus "+p+"out put ====");
                 outputp(p);
				  }else {
					  System.out.println(" bus "+p+" became idle");
					  for(int t=Tp.get(p);t<T_true;t++) {
						  bc[p][endC][t]=1.0;
					  }
					  Tp.put(p, T_true-1);
				  }
			   }
			   eb = sortp(Tp);
			   System.out.println("Tp"+Tp);
			   //outputall();
			   ite++;
			   //if all bus time equal to T_true, stop
		   }
		   DTA finalDTA = new DTA(bc,be,bl);
		   finalDTA.getdual();
		   outputall();
		   finalDTA.outputflowEndTime();
		   double temppcb=0;
		   for(int t=0;t<T_true;t++) {
			   for(int p=0;p<P;p++) {
				   for(int i:sourcecell.keySet()) {
					   temppcb=temppcb+bc[p][i][t];
				   }
			   }
		   }
		   pcb=temppcb*ld;
		   System.out.println("====== people carried by bus "+pcb+"===========");
	   }
	   //find the earlist ending trip
	   public ArrayList<Integer> sortp(HashMap<Integer,Integer> a) {
		   int temp = T_true;
		   ArrayList<Integer> tempp=new ArrayList<Integer>();
		   for(int i:a.keySet()) {
			   if(a.get(i)< temp) {
				   tempp=new ArrayList<Integer>();
				   tempp.add(i);
				   temp=a.get(i);
			   }else if(a.get(i)==temp) {
				   tempp.add(i);
			   }
		   }
		   if(temp==T_true-1) {
			   return new ArrayList<Integer>();
		   }else {
			   return tempp;
		   }
		   
	   }
	   public void outputp(int p) {
		   for(int t=0;t<=Tp.get(p);t++) {
          	 for(int i:allcell.keySet()) {
          		 if(bc[p][i][t]==1) {
          			 System.out.println("time "+t+" location "+i);
          		 }
          	 }
           }
	   }
	   public void outputall() {
		   System.out.println(" Tp :"+Tp);
		   for(int p:eb1) {
			   System.out.println("======== bus "+p+"=============");
			   for(int t=0;t<=Tp.get(p);t++) {
		          	 for(int i:allcell.keySet()) {
		          		 if(bc[p][i][t]==1) {
		          			 System.out.println("time "+t+" location "+i);
		          		 }
		          	 }
		           }
		   }
		   DTA model = new DTA(bc,be,bl);
		   model.getdual();
		   
		   for(int i:sinkcell.keySet()) {
			   System.out.println("========x flow "+i+"========");
			   for(int t=1;t<T_true;t++) {
				   if(xV[i][t]>0) {
					   System.out.println(t+" "+xV[i][t]);
				   }
			   }
		   }
		   System.out.println("obj value: "+DTAobj);
	   }
	   // input current location, finding the best solution
	   
	   public void st(int a, int p,int t) {
		   for(int j:sinkcell.keySet()) {
			   shortestpath temp = new shortestpath();
			   double[][] tempb = temp.outputb();
			   double[][] tempe = temp.outputE();
			   double[][] templ = temp.outputL();
			   
		   }
	   }
	   
       public ArrayList<Integer> sort(HashMap<Integer,Double> a) {
		   ArrayList<Integer> order = new ArrayList<Integer>();
		   for(int i:a.keySet()) {
			   order.add(i);
		   }
		   for(int j=0;j<order.size()-1;j++) {
		      for(int i=0;i<order.size()-1;i++) {			
		    	  System.out.println(i);
			      if(a.get(order.get(i))<a.get(order.get(i+1))) {
			    	  
				      Collections.swap(order, i, i+1);
			      }
		      }
		   }
		   return order;
       }
	 
	   public void run() {
		   initiate();
		   //ciniset();
		   Model e = new Model();
		   e.CreatModel();
		   e.iniVar();
		   e.solve();
		   e.recordValue();
		   e.output(); 
		   /*
		   int cr =2; int nr=60;int tr=10;
		   e.updateNW(cr, nr, tr);
		   e.solve();
		   e.recordValue();
		   //e.updatebsRec(tr);
		   e.output();*/
	   }
	   public void test() {
		   inismallnw();
		   Model e = new Model();
		   e.CreatModel();
		   e.iniVar();
		   e.solve();
		   e.recordValue();
		   //e.outputbs();
		   e.output();
		   
		   /*
		   int cr =1; int nr=30;int tr=0;
		   e.updateNW(cr, nr, tr);
		   e.solve();
		   e.recordValue();
		   //e.updatebsRec(tr);
		   //e.outputbs();
		   e.output();
		   */
	   }
	   public void test1() {
		   initiate();
		   ciniset();
		   /*
		   Model e = new Model();
		   e.CreatModel();
		   e.testmethod();
		   e.iniVar();
		   e.solve();
		   e.recordValue();
		   e.outputbs();*/
		   System.out.println(allcell.get(7).getCapacity());

	   }
	   public void heuristictest() {
		   initiate();
		   heuristic();
		   outputall();
	   }
	   public static void main(String[] args) {
			// TODO Auto-generated method stub
	          MILP ex = new MILP();
	          
	          //ex.run();
	          //ex.test();
	          //ex.test1();
	          ex.heuristictest();
	          //ex.heuristic();
		}
	   
}
