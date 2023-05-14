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
public class Largenw {

	//private Cell c15 = new Cell(new int[]{14}, new int[]{14}, 1000,1000);//save zone
	//private Cell c16 = new Cell(new int[]{13}, new int[]{13}, 1000,1000);
	private int Cell_Num;
	private int T_true;
	private int P;
	public double[][] d;//DEMAND
	private double[] c;//cost
	private int Buscapacity;
    private int l;
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
    private IloNumVar[][] x;
    private int[][][] B;//right hand side of b variables
    private Cell[] C;
    private double[][][] bc;//path for all bus for total time horizon
    private double[][][] be;
    private double[][][] bl;
    private double[][] bs;//shortest path
    private double[][] es;
    private double[][] ls;
    private int[] scl;//source cell list
	private int[] inl;//inter cell list
	private int[] skl;//sink cell list
	private int[] AllCellIndex;
	private ArrayList<Integer> eb;
	private ArrayList<Integer> eb1;//duplicate for eb
	private double pcb;//number of people carried by buses
	public Largenw() {
		
	}
	
	public class Model{
 	   private IloLinearNumExpr obj;
 	   private IloLinearNumExpr num_expr;
 	   //private IloNumVar x[][];
 	   private IloNumVar y[][][];
 	   private IloIntVar b[][][];
       private IloIntVar E[][][];
       private IloIntVar L[][][];
 	   public Model(){    		        	   
	    	
 	   }
 	   public void smallnw() {
 		   
 	   }
       public void CreatModel(){
       	 x = new IloNumVar[Cell_Num][T_true];
  	     y = new IloNumVar[Cell_Num][Cell_Num][T_true];
  	     b = new IloIntVar[P][Cell_Num][T_true];
   		 E = new IloIntVar[P][Cell_Num][T_true];
   		 L = new IloIntVar[P][Cell_Num][T_true]; 
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
                		//System.out.println("all cell"+allcell.keySet());
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
                			for(int p=0;p<P;p++) {
                				for(int g=0;g<=t;g++) {
                					for(int i:sourcecell.keySet()) {
                						obj.addTerm(c[t], b[p][i][g]);
                					}
                					for(int i:sinkcell.keySet()) {
                						obj.addTerm(-c[t], b[p][i][g]);
                					}
                				}
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
                					num_expr.addTerm(l,b[p][i][t-1]);
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
                					num_expr.addTerm(-1.0,b[p][i][t-1]);
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
                		}
                	/*FIFO CONSTRAINTS	
                	    for(int t=1;t<=T_true-Tau-1;t++){
                   			for(int i:intermediatecellIndex){
                   				for(int p=0;p<P;p++){
                   				   for(int r=0;r<Tau;r++){
                   					 num_expr = cplex.linearNumExpr();
                   					 num_expr.addTerm(-1.0/all_cell.get(i).getCapacity(), x[i][t]);
                   					 for(int o=0;o<=r;o++){
                   						 for(int u:all_cell.get(i).getSucessor()){
                   							 num_expr.addTerm(1.0/all_cell.get(i).getCapacity(), y[i][u][t+o]);
                   						 }
                   					 }
                   					 num_expr.addTerm(1.0,b[p][i][t+r+1]);
                   					 num_expr.addTerm(-BigM,E[p][i][t]);
                   					 
                   					 double temp = -BigM;
                   					 cplex.addGe(num_expr,temp);
                   				   }
                   			   }
                   			}
                   		}
                   		
                   		for(int t=T_true-Tau;t<T_true-1;t++){
                   			for(int i:intermediatecellIndex){
                   				for(int p=0;p<P;p++){
                   				   for(int r=0;r<T_true-1-t;r++){
                   					 num_expr = cplex.linearNumExpr();
                   					 num_expr.addTerm(-1.0/all_cell.get(i).getCapacity(), x[i][t]);
                   					 for(int o=0;o<=r;o++){
                   						 for(int u:all_cell.get(i).getSucessor()){
                   							 num_expr.addTerm(1.0/all_cell.get(i).getCapacity(), y[i][u][t+o]);
                   						 }
                   					 }
                   					 num_expr.addTerm(1.0,b[p][i][t+r+1]);
                   					 num_expr.addTerm(-BigM,E[p][i][t]);
                   					 double temp =-BigM;
                   					 
                   					 cplex.addGe(num_expr,temp);
                   				   }
                   			   }
                   			}
                   		}
                   		*/               		
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
                 						num_expr.addTerm(l,b[p][i][g]);
                 					}
                 					for(int i:sinkcell.keySet()) {                 				
                 						num_expr.addTerm(-l, b[p][i][g]);
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
// constraint 15, makesure every bus pick all people before leave, load all people before leave
                 		/*
                 		for(int i:sourcecell.keySet()) {
                 			for(int t=1;t<T_true-Buscapacity;t++) {
                 				for(int p=0;p<P;p++) {
                 					num_expr = cplex.linearNumExpr();
                 					for(int g=1;g<=Buscapacity;g++) {
                 						num_expr.addTerm(1.0, b[p][i][t+g]);
                 					}
                 					num_expr.addTerm(-Buscapacity, E[p][i][t-1]);
                 					cplex.addGe(num_expr, 0);
                 				}
                 			}
                 		}
                 		
                 		for(int i:sinkcell.keySet()) {
                 			for(int t=1;t<T_true-Buscapacity;t++) {
                 				for(int p=0;p<P;p++) {
                 					num_expr = cplex.linearNumExpr();
                 					for(int g=1;g<=Buscapacity;g++) {
                 						num_expr.addTerm(1.0, b[p][i][t+g]);
                 					}
                 					num_expr.addTerm(-Buscapacity, E[p][i][t-1]);
                 					cplex.addGe(num_expr, 0);
                 				}
                 			}
                 		}
                 		*/
                 		//x variable start with 0
                 		for(int i:allcell.keySet()) {
                 			num_expr=cplex.linearNumExpr();
                 			num_expr.addTerm(1.0, x[i][0]);
                 			cplex.addEq(num_expr, 0);
                 		}
                 		
                 		
                 		//make bus stay in specific cell
                 		//initate location for buses
                 		
                 		num_expr=cplex.linearNumExpr();
                 		num_expr.addTerm(1.0, b[0][9][0]);
                 		cplex.addEq(num_expr, 1.0);
                 		
                 		/*
                 		num_expr=cplex.linearNumExpr();
                 		num_expr.addTerm(1.0, b[1][9][0]);
                 		cplex.addEq(num_expr, 1.0);     
                 		
                 		num_expr=cplex.linearNumExpr();
                 		num_expr.addTerm(1.0, b[2][9][0]);
                 		cplex.addEq(num_expr, 1.0);  
                 		
                 		//specific route
                 		/*
                 		for(int t=1;t<T_true;t++) {
                 			num_expr=cplex.linearNumExpr();
                     		num_expr.addTerm(1.0, b[0][9][t]);
                     		cplex.addEq(num_expr, 1.0);
                     		
                     		num_expr=cplex.linearNumExpr();
                     		num_expr.addTerm(1.0, b[1][11][t]);
                     		cplex.addEq(num_expr, 1.0);
                 		}
                 		*/
                 		
     	    	 }catch (IloException e) {
        				System.err.println("Concert exception caught: " + e);        				
        			}
 	             }
          public void solve(){
         	 try{
         		    cplex.exportModel("SubProblemD.lp");  
 				    cplex.solve();
 				    /*
 				    for(int i:sourcecell.keySet()) {
 				    	double[] temp = new double[T_true];
 				    	for(int t=0;t<T_true;t++) {
 				    		temp[t]=cplex.getDual(cs.get(i)[t]);
 				    	}
 				    	ds.put(i, temp);
 				    }*/
 				 }catch(IloException e){
 	        			e.printStackTrace();
 	        			}
          }
          public void bendersolve() {
        	  try {
        		  cplex.setParam(IloCplex.Param.Benders.Strategy, 3);
        		  cplex.solve();
        	  }catch(IloException e){
       			e.printStackTrace();
       			}
          }
          public void output() {
        	  try{
					DirectSolveResult=cplex.getObjValue();
					System.out.println("DirectSolveResult"+DirectSolveResult);
					for(int p=0;p<P;p++){
					   for(int t=0;t<T_true;t++){
					    	for(int i:allcell.keySet()){ 					    		
					    			double temp = cplex.getValue(b[p][i][t]); 
					    			if(temp>0.99&&temp<1.1){
										System.out.println("b."+p+"."+i+"."+t+"."+":"+cplex.getValue(b[p][i][t]));
									}
					    			
					    		}
					    	}
					    }
					/*
					for(int i:allcell.keySet()) {
						for(int t=0;t<T_true;t++) {
						
							System.out.println("x."+i+"."+t+"  "+cplex.getValue(x[i][t]));
						}
					}
						*/		
					for(int i:sourcecell.keySet()) {
						for(int t=0;t<T_true;t++) {
							System.out.println("x."+i+"."+t+"  "+cplex.getValue(x[i][t]));
						}
					}
					//printout people on bus
					
					for(int t=0;t<T_true;t++) {
						int temp=0;
						for(int g=0;g<=t;g++) {
							for(int i:sourcecell.keySet()) {
							    temp = (int) (temp +(l*cplex.getValue(b[0][i][g])));
							}
							for(int i:sinkcell.keySet()) {
								temp = (int) (temp -(l*cplex.getValue(b[0][i][g])));
							}
						}
						System.out.println("b.0."+t+"  "+temp);
					}
					
					/*
					 for(int t=0;t<T_true;t++){
						 for(int i:allcellIndex){
							 System.out.println("x."+i+"."+t+":"+cplex.getValue(x[i][t]));
						 }
					 }
					 for(int t=0;t<T_true;t++){
						 for(int i:allcellIndex){
							 for(int j:all_cell.get(i).getSucessor()){
								 if(cplex.getValue(y[i][j][t])>0){
									 System.out.println("y."+i+"."+j+"."+t+":"+cplex.getValue(y[i][j][t]));
								 }
							 }
						 }
					 }*/
				 }catch(IloException e){
	        			e.printStackTrace();}
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
 	                				c1[t]=cplex.addEq(num_expr, d[i][t-1]-l*temp);                				                			
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
 	                				cplex.addEq(num_expr, l*temp);                				                			
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
     				    cplex.end();
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
	   public void  initiate(){
		   Cell_Num = 343;
		   T_true = 250;
		   d = new double[Cell_Num][T_true];
		   d[17][0]=60;
			d[89][0]=60;
			d[80][0]=60;
			d[134][0]=400;
			d[22][0]=60;
			d[98][0]=60;
			d[42][0]=60;
			d[47][0]=60;
			d[52][0]=60;
			d[57][0]=500;
			d[27][0]=60;
			d[32][0]=60;
			d[37][0]=400;
			d[269][0]=400;
		   c = new double[T_true];//cost
		   C = new Cell[Cell_Num];
		   for(int t=0;t<T_true;t++) {
			   //c[t]=T_true-t;
			  // c[t]=T_true;
			   c[t]=1;
		   }
		   P=10;
		   l=5;
		   Buscapacity=20;
		   double M=1000;
		   cl = new HashMap<Integer,Integer>();
		    C[1] = new Cell(new int[] {3},new int[] {342,18,2},4,31);
		    C[2]=  new Cell(new int[]{17,321,342,1}, new int[]{4}, 4,31);
		    C[3] = new Cell(new int[]{5,87,4,322}, new int[]{1}, 4,31);
		    C[4] = new Cell(new int[]{2}, new int[]{6,88,322,3}, 4,31);
		    C[5] = new Cell(new int[]{7}, new int[]{3,88,6}, 4,31);
		    C[6] = new Cell(new int[]{4,87,322,5}, new int[]{8}, 4,31);
		    C[7] = new Cell(new int[]{9,8,78,323}, new int[]{5}, 4,31);
		    C[8] = new Cell(new int[]{6}, new int[]{10,79,323,7}, 4,31);
		    C[9] = new Cell(new int[]{11}, new int[]{7,79,10}, 4,31);
		    C[10] = new Cell(new int[]{8,78,323,9}, new int[]{12}, 4,31);
		    C[11] = new Cell(new int[]{13,62,12,324}, new int[]{9}, 4,31);
		    C[12] = new Cell(new int[]{10}, new int[]{14,63,324,11}, 4,31);
		    C[13] = new Cell(new int[]{15}, new int[]{11,63,14}, 4,31);
		    C[14] = new Cell(new int[]{12,62,324,13}, new int[]{16}, 4,31);
		    C[15] = new Cell(new int[]{141,326,16,325}, new int[]{13}, 4,31);
		    C[16] = new Cell(new int[]{14}, new int[]{326,325,142,15},4,31);
		    C[17] = new Cell(new int[]{19},new int[]{321,342,2,18},M,M);
		    C[18] = new Cell(new int[]{1,321,17,342},new int[]{20},4,31);
		    C[19] = new Cell(new int[]{139,22,341,20},new int[]{17},4,31);
		    C[20] = new Cell(new int[]{18},new int[]{19,23,138,341},4,31);
		    C[22] = new Cell(new int[]{24},new int[]{19,138,341,23},M,M);
		    C[23]= new Cell(new int[]{20,139,22,341},new int[]{25},4,31);
		    C[24] = new Cell(new int[]{27,45,340,25},new int[]{22},4,31);
		    C[25] = new Cell(new int[]{23},new int[]{28,44,340,24},4,31);
		    C[27] = new Cell(new int[]{29},new int[]{24,340,44,28},M,M);
		    C[28] = new Cell(new int[]{25,45,27,340},new int[]{30},4,31);
		    C[29] = new Cell(new int[]{32,227,339,30},new int[]{27},4,31);
		    C[30] = new Cell(new int[]{28},new int[]{33,226,339,29},4,31);
		    C[32] = new Cell(new int[]{34},new int[]{29,339,226,33},M,M);
		    C[33] = new Cell(new int[]{30,227,32,339},new int[]{35},4,31);
		    C[34] = new Cell(new int[]{37,72,338,35},new int[]{32},4,31);
		    C[35] = new Cell(new int[]{33},new int[]{38,71,338,34},4,31);
		    C[37] = new Cell(new int[]{39},new int[]{34,338,71,38},M,M);
		    C[38] = new Cell(new int[]{35,72,37,338},new int[]{40},4,31);
		    C[39] = new Cell(new int[]{301,336,337,40},new int[]{37},4,31);
		    C[40] = new Cell(new int[]{38},new int[]{336,337,300,39},4,31);
		    C[42] = new Cell(new int[]{44},new int[]{49,111,178,43},M,M);
		    C[43] = new Cell(new int[]{50,177,112,42},new int[]{45},4,31);
		    C[44] = new Cell(new int[]{25,27,340,45},new int[]{42},4,31);
		    C[45] = new Cell(new int[]{43},new int[]{340,28,24,44},4,31);
		    C[47] = new Cell(new int[]{49},new int[]{54,102,169,48},M,M);
		    C[48] = new Cell(new int[]{55,168,103,47},new int[]{50},4,31);
		    C[49] = new Cell(new int[]{42,112,177,50},new int[]{47},4,31);
		    C[50] = new Cell(new int[]{48},new int[]{43,178,111,49},4,31);
		    C[52] = new Cell(new int[]{54},new int[]{59,64,67,53},M,M);
		    C[53] = new Cell(new int[]{60,66,65,52},new int[]{55},4,31);
		    C[54] = new Cell(new int[]{47,103,168,55},new int[]{52},4,31);
		    C[55] = new Cell(new int[]{53},new int[]{48,102,169,54},4,31);
		    C[57] = new Cell(new int[]{59},new int[]{328,156,232,58},4,M);
		    C[58] = new Cell(new int[]{231,157,328,57},new int[]{60},4,31);
		    C[59] = new Cell(new int[]{52,65,66,60},new int[]{57},4,31);
		    C[60] = new Cell(new int[]{58},new int[]{53,67,64,59},4,31);
		    C[62] = new Cell(new int[]{64},new int[]{324,11,14},11,93);
		    C[63] = new Cell(new int[]{13,12,324},new int[]{65},11,93);
		    C[64] = new Cell(new int[]{66,52,60,65},new int[]{62},11,93);
		    C[65] = new Cell(new int[]{63},new int[]{67,59,53,64},11,93);
		    C[66] = new Cell(new int[]{68},new int[]{64,53,59,67},11,93);
		    C[67] = new Cell(new int[]{65,60,52,66},new int[]{69},11,93);
		    C[68] = new Cell(new int[]{75,69},new int[]{66},11,93);
		    C[69] = new Cell(new int[]{67},new int[]{70,77,76,68},11,93);
		    C[70] = new Cell(new int[]{69,75},new int[]{333},11,93);
		    C[71] = new Cell(new int[]{35,37,338,72},new int[]{73},11,93);
		    C[72] = new Cell(new int[]{74},new int[]{338,38,34,71},11,93);
		    C[73] = new Cell(new int[]{71},new int[]{75},11,93);
		    C[74] = new Cell(new int[]{76},new int[]{72},11,93);
		    C[75] = new Cell(new int[]{73},new int[]{77,68,70,76},11,93);
		    C[76] = new Cell(new int[]{69,75},new int[]{74},11,93);
		    C[77] = new Cell(new int[]{75,69},new int[]{330},11,93);
		    C[78] = new Cell(new int[]{80},new int[]{323,7,10},2,7);
		    C[79] = new Cell(new int[]{9,8,323},new int[]{81},2,7);
		    C[80] = new Cell(new int[]{82},new int[]{78},M,M);
		    C[81] = new Cell(new int[]{79},new int[]{83},2,7);
		    C[82] = new Cell(new int[]{84},new int[]{80},2,7);
		    C[83] = new Cell(new int[]{81},new int[]{85},2,7);
		    C[84] = new Cell(new int[]{96,123,121,85},new int[]{82},2,7);
		    C[85] = new Cell(new int[]{83},new int[]{97,120,124,84},2,7);
		    C[87] = new Cell(new int[]{89},new int[]{322,3,6},2,7);
		    C[88] = new Cell(new int[]{5,4,322},new int[]{90},2,7);
		    C[89] = new Cell(new int[]{91},new int[]{87},M,M);
		    C[90] = new Cell(new int[]{88},new int[]{92},2,7);
		    C[91] = new Cell(new int[]{93},new int[]{89},2,7);
		    C[92] = new Cell(new int[]{90},new int[]{94},2,7);
		    C[93] = new Cell(new int[]{105,132,130,94},new int[]{91},2,7);
		    C[94] = new Cell(new int[]{92},new int[]{106,129,133,93},2,7);
		    C[96] = new Cell(new int[]{98},new int[]{84,120,124,97},2,7);
		    C[97] = new Cell(new int[]{85,121,123,96},new int[]{99},2,7);
		    C[98] = new Cell(new int[]{100},new int[]{96},M,M);
		    C[99] = new Cell(new int[]{97},new int[]{101},2,7);
		    C[100] = new Cell(new int[]{102},new int[]{98},2,7);
		    C[101] = new Cell(new int[]{99},new int[]{103},2,7);
		    C[102] = new Cell(new int[]{168,47,55,103},new int[]{100},2,7);
		    C[103] = new Cell(new int[]{101},new int[]{169,54,48,102},2,7);
		    C[105] = new Cell(new int[]{107},new int[]{93,133,129,106},2,7);
		    C[106] = new Cell(new int[]{94,130,132,105},new int[]{108},2,7);
		    C[107] = new Cell(new int[]{109},new int[]{105},2,7);
		    C[108] = new Cell(new int[]{106},new int[]{110},2,7);
		    C[109] = new Cell(new int[]{111},new int[]{107},2,7);
		    C[110] = new Cell(new int[]{108},new int[]{112},2,7);
		    C[111] = new Cell(new int[]{177,42,50,112},new int[]{109},2,7);
		    C[112] = new Cell(new int[]{110},new int[]{178,49,43,111},2,7);
		    C[114] = new Cell(new int[]{116},new int[]{165},2,7);
		    C[115] = new Cell(new int[]{166},new int[]{117},2,7);
		    C[116] = new Cell(new int[]{118},new int[]{114},2,7);
		    C[117] = new Cell(new int[]{115},new int[]{119},2,7);
		    C[118] = new Cell(new int[]{120},new int[]{116},2,7);
		    C[119] = new Cell(new int[]{117},new int[]{121},2,7);
		    C[120] = new Cell(new int[]{123,85,96,121},new int[]{118},2,7);
		    C[121] = new Cell(new int[]{119},new int[]{124,84,97,120},2,7);
		    C[123] = new Cell(new int[]{125},new int[]{120,84,97,124},2,7);
		    C[124] = new Cell(new int[]{121,85,96,123},new int[]{126},2,7);
		    C[125] = new Cell(new int[]{127},new int[]{123},2,7);
		    C[126] = new Cell(new int[]{124},new int[]{128},2,7);
		    C[127] = new Cell(new int[]{129},new int[]{125},2,7);
		    C[128] = new Cell(new int[]{126},new int[]{130},2,7);
		    C[129] = new Cell(new int[]{132,94,105,130},new int[]{127},2,7);
		    C[130] = new Cell(new int[]{128},new int[]{133,106,93,129},2,7);
		    C[132] = new Cell(new int[]{134},new int[]{129,93,106,133},2,7);
		    C[133] = new Cell(new int[]{130,105,94,132},new int[]{135},2,7);
		    C[134] = new Cell(new int[]{136},new int[]{132},M,M);
		    C[135] = new Cell(new int[]{133},new int[]{137},2,7);
		    C[136] = new Cell(new int[]{138},new int[]{134},2,7);
		    C[137] = new Cell(new int[]{135},new int[]{139},2,7);
		    C[138] = new Cell(new int[]{20,22,341,139},new int[]{136},2,7);
		    C[139] = new Cell(new int[]{137},new int[]{341,23,19,138},2,7);
		    C[141] = new Cell(new int[]{143},new int[]{325,15},2,7);
		    C[142] = new Cell(new int[]{16,325,326},new int[]{144},2,7);
		    C[143] = new Cell(new int[]{145},new int[]{141},2,7);
		    C[144] = new Cell(new int[]{142},new int[]{146},2,7);
		    C[145] = new Cell(new int[]{147},new int[]{143},2,7);
		    C[146] = new Cell(new int[]{144},new int[]{148},2,7);
		    C[147] = new Cell(new int[]{150,159,148,327},new int[]{145},2,7);
		    C[148] = new Cell(new int[]{146},new int[]{151,160,327,147},2,7);
		    C[150] = new Cell(new int[]{152},new int[]{147,160,327,151},2,7);
		    C[151] = new Cell(new int[]{148,159,327,150},new int[]{153},2,7);
		    C[152] = new Cell(new int[]{154},new int[]{150},2,7);
		    C[153] = new Cell(new int[]{151},new int[]{155},2,7);
		    C[154] = new Cell(new int[]{156},new int[]{152},2,7);
		    C[155] = new Cell(new int[]{153},new int[]{157},2,7);
		    C[156] = new Cell(new int[]{231,57,157,328},new int[]{154},2,7);
		    C[157] = new Cell(new int[]{155},new int[]{232,328,58,156},2,7);
		    C[159] = new Cell(new int[]{161},new int[]{327,151,147,160},2,7);
		    C[160] = new Cell(new int[]{150,148,327,159},new int[]{162},2,7);
		    C[161] = new Cell(new int[]{163},new int[]{159},2,7);
		    C[162] = new Cell(new int[]{160},new int[]{164},2,7);
		    C[163] = new Cell(new int[]{165},new int[]{161},2,7);
		    C[164] = new Cell(new int[]{162},new int[]{166},2,7);
		    C[165] = new Cell(new int[]{114},new int[]{163},2,7);
		    C[166] = new Cell(new int[]{164},new int[]{115},2,7);
		    C[168] = new Cell(new int[]{170},new int[]{102,48,54,169},2,7);
		    C[169] = new Cell(new int[]{103,55,47,168},new int[]{171},2,7);
		    C[170] = new Cell(new int[]{172},new int[]{168},2,7);
		    C[171] = new Cell(new int[]{169},new int[]{173},2,7);
		    C[172] = new Cell(new int[]{174},new int[]{170},2,7);
		    C[173] = new Cell(new int[]{171},new int[]{175},2,7);
		    C[174] = new Cell(new int[]{186,212,211,175},new int[]{172},2,7);
		    C[175] = new Cell(new int[]{173},new int[]{187,210,213,174},2,7);
		    C[177] = new Cell(new int[]{179},new int[]{111,43,49,178},2,7);
		    C[178] = new Cell(new int[]{112,50,42,177},new int[]{180},2,7);
		    C[179] = new Cell(new int[]{181},new int[]{177},2,7);
		    C[180] = new Cell(new int[]{178},new int[]{182},2,7);
		    C[181] = new Cell(new int[]{183},new int[]{179},2,7);
		    C[182] = new Cell(new int[]{180},new int[]{184},2,7);
		    C[183] = new Cell(new int[]{195,220,219,184},new int[]{181},2,7);
		    C[184] = new Cell(new int[]{182},new int[]{196,218,221,183},2,7);
		    C[186] = new Cell(new int[]{188},new int[]{174,213,210,187},2,7);
		    C[187] = new Cell(new int[]{175,211,212,186},new int[]{189},2,7);
		    C[188] = new Cell(new int[]{190},new int[]{186},2,7);
		    C[189] = new Cell(new int[]{187},new int[]{191},2,7);
		    C[190] = new Cell(new int[]{192},new int[]{188},2,7);
		    C[191] = new Cell(new int[]{189},new int[]{193},2,7);
		    C[192] = new Cell(new int[]{258},new int[]{190},2,7);
		    C[193] = new Cell(new int[]{191},new int[]{259},2,7);
		    C[195] = new Cell(new int[]{197},new int[]{183,221,218,196},2,7);
		    C[196] = new Cell(new int[]{184,219,220,195},new int[]{198},2,7);
		    C[197] = new Cell(new int[]{199},new int[]{195},2,7);
		    C[198] = new Cell(new int[]{196},new int[]{200},2,7);
		    C[199] = new Cell(new int[]{201},new int[]{197},2,7);
		    C[200] = new Cell(new int[]{198},new int[]{202},2,7);
		    C[201] = new Cell(new int[]{267},new int[]{199},2,7);
		    C[202] = new Cell(new int[]{200},new int[]{268},2,7);
		    C[204] = new Cell(new int[]{206},new int[]{255},2,7);
		    C[205] = new Cell(new int[]{256},new int[]{207},2,7);
		    C[206] = new Cell(new int[]{208},new int[]{204},2,7);
		    C[207] = new Cell(new int[]{205},new int[]{209},2,7);
		    C[208] = new Cell(new int[]{210},new int[]{206},2,7);
		    C[209] = new Cell(new int[]{207},new int[]{211},2,7);
		    C[210] = new Cell(new int[]{212,175,186,211},new int[]{208},2,7);
		    C[211] = new Cell(new int[]{209},new int[]{213,187,174,210},2,7);
		    C[212] = new Cell(new int[]{214},new int[]{210,174,187,213},2,7);
		    C[213] = new Cell(new int[]{211,186,175,212},new int[]{215},2,7);
		    C[214] = new Cell(new int[]{216},new int[]{212},2,7);
		    C[215] = new Cell(new int[]{213},new int[]{217},2,7);
		    C[216] = new Cell(new int[]{218},new int[]{214},2,7);
		    C[217] = new Cell(new int[]{215},new int[]{219},2,7);
		    C[218] = new Cell(new int[]{220,184,195,219},new int[]{216},2,7);
		    C[219] = new Cell(new int[]{217},new int[]{221,196,183,218},2,7);
		    C[220] = new Cell(new int[]{222},new int[]{218,183,196,221},2,7);
		    C[221] = new Cell(new int[]{219,195,184,220},new int[]{223},2,7);
		    C[222] = new Cell(new int[]{224},new int[]{220},2,7);
		    C[223] = new Cell(new int[]{221},new int[]{225},2,7);
		    C[224] = new Cell(new int[]{226},new int[]{222},2,7);
		    C[225] = new Cell(new int[]{223},new int[]{227},2,7);
		    C[226] = new Cell(new int[]{30,32,339,227},new int[]{224},2,7);
		    C[227] = new Cell(new int[]{225},new int[]{339,33,29,226},2,7);
		    C[231] = new Cell(new int[]{233},new int[]{156,58,328,232},2,7);
		    C[232] = new Cell(new int[]{157,57,328,231},new int[]{234},2,7);
		    C[233] = new Cell(new int[]{235},new int[]{231},2,7);
		    C[234] = new Cell(new int[]{232},new int[]{236},2,7);
		    C[235] = new Cell(new int[]{237},new int[]{233},2,7);
		    C[236] = new Cell(new int[]{234},new int[]{238},2,7);
		    C[237] = new Cell(new int[]{240,249,238,329},new int[]{235},2,7);
		    C[238] = new Cell(new int[]{236},new int[]{241,329,250,237},2,7);
		    C[240] = new Cell(new int[]{242},new int[]{237,250,329,241},2,7);
		    C[241] = new Cell(new int[]{238,249,329,240},new int[]{243},2,7);
		    C[242] = new Cell(new int[]{244},new int[]{240},2,7);
		    C[243] = new Cell(new int[]{241},new int[]{245},2,7);
		    C[244] = new Cell(new int[]{246},new int[]{242},2,7);
		    C[245] = new Cell(new int[]{243},new int[]{247},2,7);
		    C[246] = new Cell(new int[]{303},new int[]{244},2,7);
		    C[247] = new Cell(new int[]{245},new int[]{304},2,7);
		    C[249] = new Cell(new int[]{251},new int[]{329,237,241,250},2,7);
		    C[250] = new Cell(new int[]{240,238,329,249},new int[]{252},2,7);
		    C[251] = new Cell(new int[]{253},new int[]{249},2,7);
		    C[252] = new Cell(new int[]{250},new int[]{254},2,7);
		    C[253] = new Cell(new int[]{255},new int[]{251},2,7);
		    C[254] = new Cell(new int[]{252},new int[]{256},2,7);
		    C[255] = new Cell(new int[]{204},new int[]{253},2,7);
		    C[256] = new Cell(new int[]{254},new int[]{205},2,7);
		    C[258] = new Cell(new int[]{260},new int[]{192},2,7);
		    C[259] = new Cell(new int[]{193},new int[]{261},2,7);
		    C[260] = new Cell(new int[]{262},new int[]{258},2,7);
		    C[261] = new Cell(new int[]{259},new int[]{263},2,7);
		    C[262] = new Cell(new int[]{264},new int[]{260},2,7);
		    C[263] = new Cell(new int[]{261},new int[]{265},2,7);
		    C[264] = new Cell(new int[]{285,283,334,265},new int[]{262},2,7);
		    C[265] = new Cell(new int[]{263},new int[]{334,282,286,264},2,7);
		    C[267] = new Cell(new int[]{269},new int[]{201},2,7);
		    C[268] = new Cell(new int[]{202},new int[]{270},2,7);
		    C[269] = new Cell(new int[]{271},new int[]{267},M,M);
		    C[270] = new Cell(new int[]{268},new int[]{272},2,7);
		    C[271] = new Cell(new int[]{273},new int[]{269},2,7);
		    C[272] = new Cell(new int[]{270},new int[]{274},2,7);
		    C[273] = new Cell(new int[]{294,292,335,274},new int[]{271},2,7);
		    C[274] = new Cell(new int[]{272},new int[]{291,335,295,273},2,7);
		    C[276] = new Cell(new int[]{278},new int[]{318},2,7);
		    C[277] = new Cell(new int[]{319},new int[]{279},2,7);
		    C[278] = new Cell(new int[]{280},new int[]{276},2,7);
		    C[279] = new Cell(new int[]{277},new int[]{281},2,7);
		    C[280] = new Cell(new int[]{282},new int[]{278},2,7);
		    C[281] = new Cell(new int[]{279},new int[]{283},2,7);
		    C[282] = new Cell(new int[]{285,265,283,334},new int[]{280},2,7);
		    C[283] = new Cell(new int[]{281},new int[]{286,334,264,282},2,7);
		    C[285] = new Cell(new int[]{287},new int[]{282,264,334,286},2,7);
		    C[286] = new Cell(new int[]{283,265,334,285},new int[]{288},2,7);
		    C[287] = new Cell(new int[]{289},new int[]{285},2,7);
		    C[288] = new Cell(new int[]{286},new int[]{290},2,7);
		    C[289] = new Cell(new int[]{291},new int[]{287},2,7);
		    C[290] = new Cell(new int[]{288},new int[]{292},2,7);
		    C[291] = new Cell(new int[]{294,274,292,335},new int[]{289},2,7);
		    C[292] = new Cell(new int[]{290},new int[]{295,335,273,291},2,7);
		    C[294] = new Cell(new int[]{296},new int[]{291,273,335,295},2,7);
		    C[295] = new Cell(new int[]{292,274,335,294},new int[]{297},2,7);
		    C[296] = new Cell(new int[]{298},new int[]{294},2,7);
		    C[297] = new Cell(new int[]{295},new int[]{299},2,7);
		    C[298] = new Cell(new int[]{300},new int[]{296},2,7);
		    C[299] = new Cell(new int[]{297},new int[]{301},2,7);
		    C[300] = new Cell(new int[]{40,337,301,336},new int[]{298},2,7);
		    C[301] = new Cell(new int[]{299},new int[]{337,336,39,300},2,7);
		    C[303] = new Cell(new int[]{305},new int[]{246},2,7);
		    C[304] = new Cell(new int[]{247},new int[]{306},2,7);
		    C[305] = new Cell(new int[]{307},new int[]{303},2,7);
		    C[306] = new Cell(new int[]{304},new int[]{308},2,7);
		    C[307] = new Cell(new int[]{309},new int[]{305},2,7);
		    C[308] = new Cell(new int[]{306},new int[]{310},2,7);
		    C[309] = new Cell(new int[]{312,332,310,331},new int[]{307},2,7);
		    C[310] = new Cell(new int[]{308},new int[]{332,331,313,309},2,7);
		    C[312] = new Cell(new int[]{314},new int[]{331,332,309,313},2,7);
		    C[313] = new Cell(new int[]{310,331,332,312},new int[]{315},2,7);
		    C[314] = new Cell(new int[]{316},new int[]{312},2,7);
		    C[315] = new Cell(new int[]{313},new int[]{317},2,7);
		    C[316] = new Cell(new int[]{318},new int[]{314},2,7);
		    C[317] = new Cell(new int[]{315},new int[]{319},2,7);
		    C[318] = new Cell(new int[]{276},new int[]{316},2,7);
		    C[319] = new Cell(new int[]{317},new int[]{277},2,7);
		    C[321] = new Cell(new int[]{17,1},new int[]{2,18},M,M);
		    C[322] = new Cell(new int[]{87,5,4},new int[]{6,88,3},M,M);
		    C[323] = new Cell(new int[]{78,9,8},new int[]{10,79,7},M,M);
		    C[324] = new Cell(new int[]{62,12,13},new int[]{14,63,11},M,M);
		    C[325] = new Cell(new int[]{141,16},new int[]{142,15},M,M);
		    C[326] = new Cell(new int[]{16,141},new int[]{142,15},M,M);
		    C[327] = new Cell(new int[]{159,148,150},new int[]{151,160,147},M,M);
		    C[328] = new Cell(new int[]{57,231,157},new int[]{232,58,156},M,M);
		    C[329] = new Cell(new int[]{249,238,240},new int[]{241,250,237},M,M);
		    C[330] = new Cell(new int[]{77},new int[]{},M,M);
		    C[331] = new Cell(new int[]{312,310},new int[]{313,309},M,M);
		    C[332]= new Cell(new int[]{310,312},new int[]{309,313},M,M);
		    C[333] = new Cell(new int[]{70},new int[]{},M,M);
		    C[334] = new Cell(new int[]{265,283,285},new int[]{286,264,282},M,M);
		    C[335] = new Cell(new int[]{274,292,294},new int[]{295,273,291},M,M);
		    C[336] = new Cell(new int[]{40,301},new int[]{39,300},M,M);
		    C[337] = new Cell(new int[]{301,40},new int[]{300,39},M,M);
		    C[338] = new Cell(new int[]{72,37,35},new int[]{71,34,38},M,M);
		    C[339] = new Cell(new int[]{227,32,30},new int[]{226,29,33},M,M);
		    C[340] = new Cell(new int[]{45,27,25},new int[]{44,24,28},M,M);
		    C[341]= new Cell(new int[]{139,22,20},new int[]{138,19,23},M,M);
		    C[342] = new Cell(new int[]{1,17},new int[]{2,18},M,M);
			
		    AllCellIndex = new int[]{1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,22,23,24,25,27,28,29,
		        	30,32,33,34,35,37,38,39,40,42,43,44,45,47,48,49,50,52,53,54,55,57,58,59,60,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77
		        	,78,79,80,81,82,83,84,85,87,88,89,90,91,92,93,94,96,97,98,99,100,101,102,103,105,106,107,108,109,110,111,112,114,115,116,
		        	117,118,119,120,121,123,124,125,126,127,128,129,130,132,133,134,135,136,137,138,139,141,142,143,144,145,146,147,148,150,151
		        	,152,153,154,155,156,157,159,160,161,162,163,164,165,166,168,169,170,171,172,173,174,175,177,178,179,180,181,182,183,184,
		        	186,187,188,189,190,191,192,193,195,196,197,198,199,200,201,202,204,205,206,207,208,209,210,211,212,213,214,215,216,217,
		        	218,219,220,221,222,223,224,225,226,227,231,232,233,234,235,236,237,238,240,241,242,243,244,245,246,247,249,250,251,252,
		        	253,254,255,256,258,259,260,261,262,263,264,265,267,268,269,270,271,272,273,274,276,277,278,279,280,281,282,283,285,286,
		        	287,288,289,290,291,292,294,295,296,297,298,299,300,301,303,304,305,306,307,308,309,310,312,313,314,315,316,317,318,319,
		        	321,322,323,324,325,326,327,328,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342};
		    scl = new int[]{17,89,80,134,22,98,42,47,52,57,27,32,37,269};
		    inl =  new int[]{1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,19,20,23,24,25,28,29,
	    	   		30,33,34,35,38,39,40,43,44,45,48,49,50,53,54,55,58,59,60,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79
	    	   		,81,82,83,84,85,87,88,90,91,92,93,94,96,97,99,100,101,102,103,105,106,107,108,109,100,110,111,112,114,115,116,117,118,119,
	    	   		120,121,123,124,125,126,127,128,129,130,132,133,135,136,137,138,139,141,142,143,144,145,146,147,148,150,151,152,153,154,155,156,
	    	   		157,159,160,161,162,163,164,165,166,168,169,170,171,172,173,174,175,177,178,179,180,181,182,183,184,186,187,188,189,190,191,192,193,
	    	   		195,196,197,198,199,200,201,202,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,231,
	    	   		232,233,234,235,236,237,238,240,241,242,243,244,245,246,247,249,250,251,252,253,254,255,256,258,259,260,261,262,263,264,265,267,268
	    	   		,270,271,272,273,274,276,277,278,279,280,281,282,283,285,286,287,288,289,290,291,292,294,295,296,297,298,299,300,301,303,
	    	   		304,305,306,307,308,309,310,312,313,314,315,316,317,318,319};
		    skl = new int[]{321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342};
 		   allcell = new HashMap<Integer, Cell>();
 		   for(int i:AllCellIndex) {
 			   allcell.put(i, C[i]);
 			 
 		   }
 		   //System.out.println(allcell.keySet());
 		   sourcecell = new HashMap<Integer,Cell>();
 		   for(int i:scl) {
 			   sourcecell.put(i, C[i]);
 		   }
 		   
 		   intermediatecell = new HashMap<Integer,Cell>();
 		   for(int i:inl) {
 			   intermediatecell.put(i, C[i]);
 		   }
 		   
 		   sinkcell = new HashMap<Integer,Cell>();
 		   for(int i:skl) {
 			   sinkcell.put(i, C[i]);
 		   }
 		   //System.out.println(allcell.keySet());
 		   //System.out.println("source "+sourcecell.keySet());
 		   //System.out.println("intermediatecell  "+intermediatecell.keySet());
 		   //System.out.println("sinkcell "+sinkcell.keySet());
 	   }
	   public void  initiate1(){
		   Cell_Num = 15;
		   T_true = 50;
		   d = new double[Cell_Num][T_true];
		   d[1][0]=30;
		   d[2][15]=30;
		   c = new double[T_true];
		   C = new Cell[Cell_Num];
		   for(int t=0;t<T_true;t++) {
			   c[t]=T_true-t;
		   }
		   P=1;
		   l=2;
		   Buscapacity=6;
		   cl = new HashMap<Integer,Integer>();
		    C[1] = new Cell(new int[]{3}, new int[]{6}, 1000,1000);
			C[2] = new Cell(new int[]{5}, new int[]{4}, 1000,1000);
			C[3] = new Cell(new int[]{8,9}, new int[]{1}, 2,32);
			C[4] = new Cell(new int[]{2}, new int[]{7,10}, 2,32);
			C[5] = new Cell(new int[]{7,11}, new int[]{2}, 2,32);
			C[6] = new Cell(new int[]{1}, new int[]{8,12}, 2,32);
			C[7] = new Cell(new int[]{4,9}, new int[]{5,12}, 2,32);
			C[8] = new Cell(new int[]{6,11}, new int[]{3,10}, 2,32);
			C[9] = new Cell(new int[]{14}, new int[]{3,7}, 2,32);
			C[10] = new Cell(new int[]{4,8}, new int[]{13}, 2,32);
			C[11] = new Cell(new int[]{13}, new int[]{5,8}, 2,32);
			C[12] = new Cell(new int[]{6,7}, new int[]{14}, 2,32);
			C[13] = new Cell(new int[]{10}, new int[]{11}, 1000,1000);//sink cell
			C[14] = new Cell(new int[]{12}, new int[]{9}, 1000,1000);
			AllCellIndex = new int[]{1,2,3,4,5,6,7,8,9,10,11,12,13,14};
		    scl = new int[]{1,2};
		    inl =  new int[]{3,4,5,6,7,8,9,10,11,12};
		    skl = new int[]{13,14};
 		   allcell = new HashMap<Integer, Cell>();
 		   for(int i:AllCellIndex) {
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
           		T_s=40;
           		
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
        	   cl.put(i, 321);
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
					  
					  dualsum = ds.get(j)[temp+Tp.get(p)+(Buscapacity/l)];
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
                 for(int t=0;t<(Buscapacity/l);t++) {
                	 bc[p][d][t+Tp.get(p)]=1.0;
                 }
                 tp = Tp.get(p);
                 Tp.put(p, tp+((Buscapacity/l)-1));
                 
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
                 for(int t=0;t<(Buscapacity/l);t++) {
                	 bc[p][endC][t+Tp.get(p)]=1.0;
                 } 
                 
                 tp = Tp.get(p)+(Buscapacity/l)-1;
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
		   pcb=temppcb*l;
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
		    	  //System.out.println(i);
			      if(a.get(order.get(i))<a.get(order.get(i+1))) {
			    	  
				      Collections.swap(order, i, i+1);
			      }
		      }
		   }
		   return order;
       }
	 
	   public void run() {
		   Model e = new Model();
		   e.CreatModel();
		   e.solve();
		   e.output();
	   }
	   public void test() {
		   long startTime = System.currentTimeMillis();
		   //initiate();
		   //Model e = new Model();
		   //e.CreatModel();
		   //e.bendersolve();
		   //e.solve();
		   //e.output();
		   initiate();
		   heuristic();
		   long endTime = System.currentTimeMillis();
		   long timeElasped = endTime-startTime;
		   System.out.println("Execution time in milliseconds: "+ timeElasped);
	   }
	  
	   public void runflow() {
		   double[] flow = new double[T_true];
		   double[][] temp2;
		   initiate();
		   bc = new double[P][Cell_Num][T_true];
		   be = new double[P][Cell_Num][T_true];
		   bl = new double[P][Cell_Num][T_true];
		   DTA temp = new DTA(bc,be,bl);
		   temp.getdual();
		   temp.outputflowEndTime();
	   }
	   public static void main(String[] args) {
			// TODO Auto-generated method stub
	          Largenw ex = new Largenw();                 
	          ex.test();
	          //ex.runflow();
	          //ex.heuristic();
		}
}
