
import java.io.*;
import java.util.*;

import jxl.Workbook;
import jxl.write.*;
import ilog.concert.*;
import ilog.cplex.*;
public class BenderDecomposition {
	    //private List<IloConstraint> constraints;
	    private int IterationCounter;
	    private int IterationH;
	    private Subproblem subproblem;
	    private linearSubproblem lsubproblem;
	    private Greedysubproblem greedysubproblem;
	    //private IloIntVar Z;
        public Map<Integer,cell> all_cell =  new HashMap<Integer,cell>();
        public Map<Integer,cell> source_cell = new HashMap<Integer,cell>();
        public Map<Integer,cell> Intermediate_cell = new HashMap<Integer,cell>();
        public Map<Integer,cell> sink_cell = new HashMap<Integer,cell>();
        private int[] AllCellIndex;
    	private int[] SourceCellIndex;
    	private int[] IntermediateCellIndex;
    	private int[] SinkCellIndex;
        public cell cell_0 = new cell(new int[]{10,11}, new int[]{2,3}, 10000,10000);
        public cell cell_1 = new cell(new int[]{11,12}, new int[]{3,4}, 10000,10000);
        public cell cell_2 = new cell(new int[]{0}, new int[]{5,6}, 94,11);
        public cell cell_3 = new cell(new int[]{0,1}, new int[]{6}, 94,11);
        public cell cell_4 = new cell(new int[]{1}, new int[]{6,7}, 94,11);
        public cell cell_5 = new cell(new int[]{2}, new int[]{8}, 94,11);
        public cell cell_6 = new cell(new int[]{2,3,4}, new int[]{9}, 32,6);
        public cell cell_7 = new cell(new int[]{4}, new int[]{9}, 32,6);
        public cell cell_8 = new cell(new int[]{5}, new int[]{9}, 32,6);
        public cell cell_9 = new cell(new int[]{6,7,8}, new int[]{14,15,16}, 10000,10000);
        public cell cell_10 = new cell(new int[]{13,14}, new int[]{0}, 94,11);
        public cell cell_11 = new cell(new int[]{14}, new int[]{0,1}, 94,11);
        public cell cell_12 = new cell(new int[]{14,15}, new int[]{1}, 94,11);
        public cell cell_13 = new cell(new int[]{16}, new int[]{10}, 32,6);
        public cell cell_14 = new cell(new int[]{9}, new int[]{10,11,12}, 32,6);
        public cell cell_15 = new cell(new int[]{9}, new int[]{12}, 32,6);
        public cell cell_16 = new cell(new int[]{9}, new int[]{13}, 32,6);
        public double objDualValue;
        public double objPrimalValue;
        public double paretoObjValue;
        public double FinalResult;
        public double DirectSolveResult;
    	public int Cell_Num;
    	public int T_true;
    	public int Tau;    	
    	public int P;
    	public double[][] d;
    	public double BigM;
    	public int Buscapacity;
        private double u1Value[][];
        private double u1ValueC[][];
        private double u2Value[][];
        private double u3Value[][];
        private double u4Value[][];
        private double u5Value[][];
        private double u6Value[][][][];
        private double u1Zero[][];
        private double u2Zero[][];
        private double u3Zero[][];
        private double u4Zero[][];
        private double u5Zero[][];
        private double u6Zero[][][][];
        private double u1Set[][][];
        private double u2Set[][][];
        private double u3Set[][][];
        private double u4Set[][][];
        private double u5Set[][][];
        private double u6Set[][][][][];
    	private double bValue[][][];
    	private double bDummy[][];
    	private double EValue[][][];
    	private double LValue[][][];
    	private double hValue[][];
    	private double uValue[][];
    	private double bZero[][][];
        private double EZero[][][];
    	private double LZero[][][];
    	private double hZero[][];
    	private double uZero[][];
    	private int C[][];// travel cost
    	private int time;
    	private int timeP;//current time 
    	private int S;//start of every trip
    	private int Destination;
    	private double LB;
    	private double UB;
    	private int iterationT;
        public BenderDecomposition(){
        	SetData();
        	Initiation();
        	
        }
        
        
       public class Masterproblem{
        	private  IloCplex cplex;
        	private IloLinearNumExpr dual_obj;
        	private IloLinearNumExpr num_expr;
        	private IloNumVar u1[][];
        	private IloNumVar u2[][];
        	private IloNumVar u3[][];
        	private IloNumVar u4[][];
        	private IloNumVar u5[][];
        	private IloNumVar u6[][][][];
        	public Masterproblem(){
          		u1 = new IloNumVar[Cell_Num][T_true];
          		u2 = new IloNumVar[Cell_Num][T_true];
          		u3 = new IloNumVar[Cell_Num][T_true];
          		u4 = new IloNumVar[Cell_Num][T_true];
          		u5 = new IloNumVar[Cell_Num][T_true];
          		u6 = new IloNumVar[P][Cell_Num][T_true][Tau];
        				
        		CreatModel();
        		solve();
        		
        	}
        	public void CreatModel(){
              	try{
              		cplex = new IloCplex();
              		for(int t=0;t<T_true;t++){
              		    for(int i=0;i<Cell_Num;i++){              			              				
              				u1[i][t] = cplex.numVar(-Double.MAX_VALUE, Double.MAX_VALUE );
              				u1[i][t].setName("u1."+i+"."+t);        
              				u2[i][t] = cplex.numVar(0, Double.MAX_VALUE );
              				u2[i][t].setName("u2."+i+"."+t);              				
              				u3[i][t] = cplex.numVar(0, Double.MAX_VALUE );
              				u3[i][t].setName("u3."+i+"."+t);              				
              				u4[i][t] = cplex.numVar(0, Double.MAX_VALUE );
              				u4[i][t].setName("u4."+i+"."+t);              				
              				u5[i][t] = cplex.numVar(0, Double.MAX_VALUE );
              				u5[i][t].setName("u5."+i+"."+t);
              				for(int p=0;p<P;p++){
              					for(int r=0;r<Tau;r++){
                      				u6[p][i][t][r] = cplex.numVar(0, Double.MAX_VALUE );
                      				u6[p][i][t][r].setName("u6."+p+"."+i+"."+t+"."+r);
              					}
              				}
              				
              			}
              		}
              		dual_obj  = cplex.linearNumExpr();
              		for(int t=1;t <T_true;t++){
              			for(int i:SourceCellIndex){
              				double FixedValue = 0;
              				for(int p =0; p<P;p++){
/**
 * Fixed wrong code +bvalue CHANGE TO -bvalue
 */
              					FixedValue = FixedValue - bValue[p][i][t-1];
              				}
              				dual_obj.addTerm(d[i][t-1]+FixedValue, u1[i][t]);
              			}
              			for(int i:SinkCellIndex){
              				double FixedValue =0;
              				for(int p=0;p<P;p++){
              					FixedValue = FixedValue + bValue[p][i][t-1];
              				}
              				dual_obj.addTerm(FixedValue, u1[i][t]);
              			}
              			
              		}
              		for(int t=0;t<T_true-1;t++){
              			for(int i:AllCellIndex){
              				double FixedValue=0;
              				for(int p=0;p<P;p++){
              					FixedValue = FixedValue+LValue[p][i][t+1];
              				}
              				dual_obj.addTerm(FixedValue-all_cell.get(i).getFlow(), u3[i][t]);
              			}
              		}
              		for(int i:AllCellIndex){
              			dual_obj.addTerm(-all_cell.get(i).getFlow(), u3[i][T_true-1]);
              		}
              		for(int t=0;t<T_true-1;t++){
              			for(int i:AllCellIndex){
              				double FixedValue=0;
              				for(int p=0;p<P;p++){
              					FixedValue = FixedValue+EValue[p][i][t+1];
              				}
              				dual_obj.addTerm(FixedValue-all_cell.get(i).getFlow(), u4[i][t]);
              			}
              		}
              		for(int i:AllCellIndex){
              			dual_obj.addTerm(-all_cell.get(i).getFlow(), u4[i][T_true-1]);
              		}
              		for(int t=0;t<T_true-1;t++){
              			for(int i:AllCellIndex){
              				double FixedValue=0;
              				for(int p=0;p<P;p++){
/**
 * change E[t] to E[t+1]
 */
              					FixedValue = FixedValue+EValue[p][i][t+1];
              				}
              				dual_obj.addTerm(FixedValue-all_cell.get(i).getCapacity(), u5[i][t]);
              			}
              			
              		}
              		for(int i:AllCellIndex){
              			dual_obj.addTerm(-all_cell.get(i).getCapacity(), u5[i][T_true-1]);
              		}
              		for(int t=1;t<=T_true-Tau-1;t++){
              			for(int i:IntermediateCellIndex){
              				for(int p=0;p<P;p++){
              				   for(int r=0;r<Tau;r++){
              					   dual_obj.addTerm(-bValue[p][i][t+r+1]-BigM+BigM*EValue[p][i][t], u6[p][i][t][r]);
              				   }
              			   }
              			}
              		}
              		for(int t=T_true-Tau;t<T_true-1;t++){
              			for(int i:IntermediateCellIndex){
              				for(int p=0;p<P;p++){
              				   for(int r=0;r<T_true-1-t;r++){
              					   dual_obj.addTerm(-bValue[p][i][t+r+1]-BigM+BigM*EValue[p][i][t], u6[p][i][t][r]);
              				   }
              			   }
              			}
              		}
              		cplex.addMaximize(dual_obj);
/**
 * MasterProblem Constraints              		
 */
              		for(int t=0;t<T_true-1;t++){
              			for(int i:SourceCellIndex){
              			    num_expr = cplex.linearNumExpr();
              			    num_expr.addTerm(1.0, u1[i][t]);
              			    num_expr.addTerm(-1.0, u1[i][t+1]);
              			    num_expr.addTerm(1.0, u2[i][t]);
              			    num_expr.addTerm(-1.0, u5[i][t]);
              			    //System.out.println(i+""+t);
              			    cplex.addLe(num_expr, 1);
              			}	
              		}
              		for(int i:SourceCellIndex){
              			
              			num_expr = cplex.linearNumExpr();
              			num_expr.addTerm(1.0, u1[i][T_true-1]);
              			num_expr.addTerm(1.0, u2[i][T_true-1]);
              			num_expr.addTerm(-1.0, u5[i][T_true-1]);
              			
              			cplex.addLe(num_expr, 1);
              		}
              		for(int i:IntermediateCellIndex){
              			num_expr = cplex.linearNumExpr();
              			num_expr.addTerm(1.0,u1[i][0]);
              			num_expr.addTerm(-1.0, u1[i][1]);
              			num_expr.addTerm(1.0, u2[i][0]);
              			num_expr.addTerm(-1.0, u5[i][0]);
              			
              			cplex.addLe(num_expr, 1);
              		}
              		for(int t=1;t<=T_true-Tau-1;t++){
              			for(int i:IntermediateCellIndex){
              				num_expr = cplex.linearNumExpr();
              				num_expr.addTerm(1.0, u1[i][t]);
              				num_expr.addTerm(-1.0, u1[i][t+1]);
              				num_expr.addTerm(1.0, u2[i][t]);
              				num_expr.addTerm(-1.0, u5[i][t]);
              				for(int p=0;p<P;p++){
              					for(int r=0;r<Tau;r++){
              						num_expr.addTerm(-1.0/all_cell.get(i).getCapacity(), u6[p][i][t][r]);
              					}
              				}
              				
              				cplex.addLe(num_expr, 1);
              			}
              		}
              		for(int t=T_true-Tau;t<T_true-1;t++){
              			for(int i:IntermediateCellIndex){
              				num_expr = cplex.linearNumExpr();
              				num_expr.addTerm(1.0, u1[i][t]);
              				num_expr.addTerm(-1.0, u1[i][t+1]);
              				num_expr.addTerm(1.0, u2[i][t]);
              				num_expr.addTerm(-1.0, u5[i][t]);
              				for(int p=0;p<P;p++){
              					for(int r=0;r<T_true-t-1;r++){
              						num_expr.addTerm(-1.0/all_cell.get(i).getCapacity(), u6[p][i][t][r]);
              					}
              				}
              				
              				cplex.addLe(num_expr, 1);
              			}
              		}
              		for(int i:IntermediateCellIndex){
              			num_expr = cplex.linearNumExpr();
              			num_expr.addTerm(1.0,u1[i][T_true-1]);
              			num_expr.addTerm(1.0, u2[i][T_true-1]);
              			num_expr.addTerm(-1.0, u5[i][T_true-1]);
              			
              			
              			cplex.addLe(num_expr,1);
              		}
              		
              		for(int t=0;t<T_true-1;t++){
              			for(int i:SinkCellIndex){
              				num_expr = cplex.linearNumExpr();
              				num_expr.addTerm(1.0, u1[i][t]);
              				num_expr.addTerm(-1.0, u1[i][t+1]);
              				num_expr.addTerm(1.0, u2[i][t]);
              				num_expr.addTerm(-1.0,u5[i][t] );
              				
              				cplex.addLe(num_expr, 0);
              			}
              		}
              		for(int i:SinkCellIndex){
              			num_expr = cplex.linearNumExpr();
              			num_expr.addTerm(1.0, u1[i][T_true-1]);
              			num_expr.addTerm(1.0, u2[i][T_true-1]);
              			num_expr.addTerm(-1.0, u5[i][T_true-1]);
              			cplex.addLe(num_expr, 0);
              		}
/**
 * dual equations for y variables              		
 */
              		for(int t=Tau;t<T_true-1;t++){
              			for(int i:IntermediateCellIndex){
              				for(int j:all_cell.get(i).getSucessor()){
              					num_expr = cplex.linearNumExpr();
                  				num_expr.addTerm(1.0,u1[i][t+1]);
                  				num_expr.addTerm(-1.0, u1[j][t+1]);
                  				num_expr.addTerm(-1.0, u2[i][t]);
                  				num_expr.addTerm(-1.0, u3[i][t]);
                  				num_expr.addTerm(-1.0, u4[j][t]);
                  				num_expr.addTerm(-1.0, u5[j][t]);
                  				//if(contains(IntermediateCellIndex,i)){
                  					for(int p=0;p<P;p++){
                      					for(int r=t-Tau+1;r<=t;r++){
                      					    for(int k=t-r;k<Tau;k++){
                      					    	//if(r+k>=t ){
                      					    		num_expr.addTerm(1.0/all_cell.get(i).getCapacity(), u6[p][i][r][k]);
                      					    		
                      					    	//}
                      					   // }
                      					}   					
                      				}
                  				}
                  				
                  				cplex.addLe(num_expr, 0);
              				}
              			}
              		}
              		for(int t=1;t<Tau;t++){
              			for(int i:IntermediateCellIndex){
              				for(int j:all_cell.get(i).getSucessor()){
              					num_expr = cplex.linearNumExpr();
                  				num_expr.addTerm(1.0,u1[i][t+1]);
                  				num_expr.addTerm(-1.0, u1[j][t+1]);
                  				num_expr.addTerm(-1.0, u2[i][t]);
                  				num_expr.addTerm(-1.0, u3[i][t]);
                  				num_expr.addTerm(-1.0, u4[j][t]);
                  				num_expr.addTerm(-1.0, u5[j][t]);
                  				for(int p=0;p<P;p++){
                  					for(int r=1;r<=t;r++){
                  					    for(int k=t-r;k<Tau;k++){
                  					    	
                  					    		num_expr.addTerm(1.0/all_cell.get(i).getCapacity(), u6[p][i][r][k]);
                  					    		
                  					    	
                  					    }
                  					}
                  				}
                  				cplex.addLe(num_expr, 0);
              				}
              			}
              		}
              		for(int i:IntermediateCellIndex){
          				for(int j:all_cell.get(i).getSucessor()){
          					num_expr = cplex.linearNumExpr();
          					num_expr.addTerm(1.0, u1[i][1]);
          					num_expr.addTerm(-1.0, u1[j][1]);
          					num_expr.addTerm(-1.0, u2[i][0]);
              				num_expr.addTerm(-1.0, u3[i][0]);
              				num_expr.addTerm(-1.0, u4[j][0]);
              				num_expr.addTerm(-1.0, u5[j][0]);
              				cplex.addLe(num_expr, 0);
          				}
          				
          			}
              		for(int i:IntermediateCellIndex){
          				for(int j:all_cell.get(i).getSucessor()){
          					num_expr = cplex.linearNumExpr();
          					num_expr.addTerm(-1.0, u2[i][T_true-1]);
              				num_expr.addTerm(-1.0, u3[i][T_true-1]);
              				num_expr.addTerm(-1.0, u4[j][T_true-1]);
              				num_expr.addTerm(-1.0, u5[j][T_true-1]);
              				
              				cplex.addLe(num_expr, 0);
          				}
              		
              		}
              		
              		for(int t=0;t<T_true-1;t++){
              			for(int i:SourceCellIndex){
              				for(int j:all_cell.get(i).getSucessor()){
              					num_expr = cplex.linearNumExpr();
                  				num_expr.addTerm(1.0,u1[i][t+1]);
                  				num_expr.addTerm(-1.0, u1[j][t+1]);
                  				num_expr.addTerm(-1.0, u2[i][t]);
                  				num_expr.addTerm(-1.0, u3[i][t]);
                  				num_expr.addTerm(-1.0, u4[j][t]);
                  				num_expr.addTerm(-1.0, u5[j][t]);
                  				
                  				cplex.addLe(num_expr, 0);
              				}
              			}
              		}	
              		for(int i:SourceCellIndex){
          				for(int j:all_cell.get(i).getSucessor()){
          					num_expr = cplex.linearNumExpr();              			
              				num_expr.addTerm(-1.0, u2[i][T_true-1]);
              				num_expr.addTerm(-1.0, u3[i][T_true-1]);
              				num_expr.addTerm(-1.0, u4[j][T_true-1]);
              				num_expr.addTerm(-1.0, u5[j][T_true-1]);
              				
              				cplex.addLe(num_expr, 0);
          				}
          			}
              		                            		
              		for(int t=0;t<T_true-1;t++){
              			for(int i:SinkCellIndex ){
              				for(int j:all_cell.get(i).getSucessor()){
              					num_expr = cplex.linearNumExpr();
                				num_expr.addTerm(1.0,u1[i][t+1]);
                				num_expr.addTerm(-1.0, u1[j][t+1]);
                				num_expr.addTerm(-1.0, u2[i][t]);
                				num_expr.addTerm(-1.0, u3[i][t]);
                				num_expr.addTerm(-1.0, u4[j][t]);
                				num_expr.addTerm(-1.0, u5[j][t]);
                				
                				cplex.addLe(num_expr, 0); 
              				}
              				
              			}
              			
              		}
              		for(int i:SinkCellIndex){
          				for(int j:all_cell.get(i).getSucessor()){
          					num_expr = cplex.linearNumExpr();              			
              				num_expr.addTerm(-1.0, u2[i][T_true-1]);
              				num_expr.addTerm(-1.0, u3[i][T_true-1]);
              				num_expr.addTerm(-1.0, u4[j][T_true-1]);
              				num_expr.addTerm(-1.0, u5[j][T_true-1]);
              				
              				cplex.addLe(num_expr, 0);
          				}
          			}
              			   				
              	}catch (IloException e) {
      				System.err.println("Concert exception caught: " + e);
      				
      			}
              	
              }
            public void solve(){
            	try{
            		cplex.exportModel("MasterProblem).lp"); 
				    cplex.solve();
					objDualValue=cplex.getObjValue();
					paretoObjValue = objDualValue;
					/*
					for(int t=0;t<T_true;t++){
						for(int p=0;p<P;p++){
							objDualValue=objDualValue+hValue[p][t];
						}
					}*/
					//System.out.println("ObjDualValue"+objDualValue);
					
				    for(int t=0;t<T_true;t++){
				    	for(int i:AllCellIndex){
				    		u1Value[i][t]=cplex.getValue(this.u1[i][t]);
				    		//System.out.println("u1"+i+""+t+":"+""+u1Value[i][t]);
				    		
				    	}
				    	for(int i:SourceCellIndex){
				    		//System.out.println("u1"+i+""+t+":"+""+u1Value[i][t]);
				    	}
				    }
				    for(int i :SourceCellIndex){
				    	for(int t=0;t<T_true;t++){
				    		//System.out.println("u1"+i+""+t+":"+""+u1Value[i][t]);
				    	}
				    }
				    for(int i:AllCellIndex){
				    	for(int t=0;t<T_true;t++){
				    		u2Value[i][t]=cplex.getValue(this.u2[i][t]);
				    		//System.out.println("u2"+i+""+t+":"+""+u2Value[i][t]);
				    		u3Value[i][t]=cplex.getValue(this.u3[i][t]);
				    		//System.out.println("u3"+i+""+t+":"+""+u3Value[i][t]);
				    		u4Value[i][t]=cplex.getValue(this.u4[i][t]);
				    		//System.out.println("u4"+i+""+t+":"+""+u4Value[i][t]);
				    		u5Value[i][t]=cplex.getValue(this.u5[i][t]);
				    		//System.out.println("u5"+i+""+t+":"+""+u5Value[i][t]);
				    		
				    	}
				    }
				    for(int t=1;t<=T_true-Tau-1;t++){
				    	for(int i:IntermediateCellIndex){
				    		for(int p=0;p<P;p++){
				    			for(int r=0;r<Tau;r++){
				    				u6Value[p][i][t][r]=cplex.getValue(this.u6[p][i][t][r]);
				    				//System.out.println("u6"+p+""+i+""+t+""+r+":"+""+u6Value[p][i][t][r]);
				    			}
				    		}
				    	}
				    }
				    for(int t=T_true-Tau;t<T_true-1;t++){
				    	for(int i:IntermediateCellIndex){
				    		for(int p=0;p<P;p++){
				    			for(int r=0;r<T_true-t-1;r++){
				    				u6Value[p][i][t][r]=cplex.getValue(this.u6[p][i][t][r]);
				    				//System.out.println("u6"+p+""+i+""+t+""+r+":"+""+u6Value[p][i][t][r]);
				    			}
				    		}
				    	}
				    }
            	}catch(IloException e){
        			e.printStackTrace();}
            }
           public void reocrdDecisionVariable(){
        	   
           }
        	
        }
      
       public class Subproblem{
        	private  IloCplex cplex;
        	private IloIntVar Z;
        	private IloIntVar b[][][];
        	private IloIntVar E[][][];
        	private IloIntVar L[][][];
        	private IloIntVar h[][];
        	private IloIntVar u[][];
        	private IloLinearNumExpr primal_obj;
        	private IloLinearNumExpr num_expr;
        	
        	public Subproblem(){
        		b = new IloIntVar[P][Cell_Num][T_true];
        		E = new IloIntVar[P][Cell_Num][T_true];
        		L = new IloIntVar[P][Cell_Num][T_true];
        		h = new IloIntVar[P][T_true];
        		u = new IloIntVar[P][T_true];    		
        		CreatModel();
        	}
        	public void CreatModel(){
        		try{
        			cplex= new IloCplex();
        			for(int t=0;t<T_true;t++){
            			for(int i:AllCellIndex){
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
            		for(int t=0;t<T_true;t++){
            			for(int p=0;p<P;p++){
            				h[p][t]=cplex.intVar(0, Buscapacity);
            				h[p][t].setName("h."+p+"."+t);
            				u[p][t]=cplex.intVar(0, Buscapacity);
            				u[p][t].setName("u."+p+"."+t);
            			}
            		}
            	Z=cplex.intVar(-Integer.MAX_VALUE, Integer.MAX_VALUE);
            	Z.setName("Z");
        		primal_obj = cplex.linearNumExpr();
        		primal_obj.addTerm(1, Z);
        		cplex.addMinimize(primal_obj);
        		for(int t=1;t<T_true;t++){
        			for(int i:AllCellIndex){
        				for(int p=0;p<P;p++){
        					num_expr = cplex.linearNumExpr();
        					num_expr.addTerm(1.0,E[p][i][t]);
        					num_expr.addTerm(-1.0,b[p][i][t]);
        					num_expr.addTerm(1.0,b[p][i][t-1]);
        					cplex.addGe(num_expr, 0);        				
        				}
        			}
        		}
        		
        		for(int t=1;t<T_true;t++){
        			for(int i:AllCellIndex){
        				for(int p=0;p<P;p++){
        					num_expr = cplex.linearNumExpr();
        					num_expr.addTerm(1.0,L[p][i][t]);
        					num_expr.addTerm(-1.0,b[p][i][t-1]);
        					num_expr.addTerm(1.0,b[p][i][t]);
        					cplex.addGe(num_expr, 0);
        				
        				}
        			}
        		}
        		
        		for(int t=0;t<T_true;t++){
        				for(int p=0;p<P;p++){
        					num_expr = cplex.linearNumExpr();
        					for(int i:AllCellIndex){
        					num_expr.addTerm(1.0, b[p][i][t]);
        					
        				
        				}
        					cplex.addEq(num_expr, 1);
        			}
        		}
        	
        		for(int t=1;t<T_true;t++){
        			for(int i:SourceCellIndex){
        				for(int p=0;p<P;p++){
        					num_expr = cplex.linearNumExpr();
        					num_expr.addTerm(1.0,h[p][t-1]);
        					num_expr.addTerm(-1.0, h[p][t]);
        					num_expr.addTerm(BigM, b[p][i][t]);
        					cplex.addLe(num_expr, BigM-1);
        				}
        			}
        		}
        		for(int t=1;t<T_true;t++){
        			for(int i:SourceCellIndex){
        				for(int p=0;p<P;p++){
        					num_expr = cplex.linearNumExpr();
        					num_expr.addTerm(1.0,h[p][t]);
        					num_expr.addTerm(-1.0, h[p][t-1]);
        					num_expr.addTerm(BigM, b[p][i][t]);
        					cplex.addLe(num_expr, BigM+1);
        				}
        			}
        		}
        		for(int t=1;t<T_true;t++){
        			for(int i:IntermediateCellIndex){
        				for(int p=0;p<P;p++){
        					num_expr = cplex.linearNumExpr();
        					num_expr.addTerm(1.0,h[p][t-1]);
        					num_expr.addTerm(-1.0, h[p][t]);
        					num_expr.addTerm(BigM, b[p][i][t]);
        					cplex.addLe(num_expr, BigM);
        				}
        			}
        		}
        		for(int t=1;t<T_true;t++){
        			for(int i:IntermediateCellIndex){
        				for(int p=0;p<P;p++){
        					num_expr = cplex.linearNumExpr();
        					num_expr.addTerm(1.0,h[p][t]);
        					num_expr.addTerm(-1.0, h[p][t-1]);
        					num_expr.addTerm(BigM, b[p][i][t]);
        					cplex.addLe(num_expr, BigM);
        				}
        			}
        		}
        		for(int t=1;t<T_true;t++){
        			for(int i:SinkCellIndex){
        				for(int p=0;p<P;p++){
        					num_expr = cplex.linearNumExpr();
        					num_expr.addTerm(1.0,h[p][t-1]);
        					num_expr.addTerm(-1.0, h[p][t]);
        					num_expr.addTerm(BigM, b[p][i][t]);
        					cplex.addLe(num_expr, BigM+1);
        				}
        			}
        		}
        		
        		for(int t=1;t<T_true;t++){
        			for(int i:SinkCellIndex){
        				for(int p=0;p<P;p++){
        					num_expr = cplex.linearNumExpr();
        					num_expr.addTerm(1.0,h[p][t]);
        					num_expr.addTerm(-1.0, h[p][t-1]);
        					num_expr.addTerm(BigM, b[p][i][t]);
        					cplex.addLe(num_expr, BigM-1);
        				}
        			}
        		}
        		for(int t=1;t<T_true;t++){
        			for(int i:SinkCellIndex){
        				for(int p=0;p<P;p++){
        					num_expr = cplex.linearNumExpr();
        					num_expr.addTerm(1.0,u[p][t-1]);
        					num_expr.addTerm(-1.0, u[p][t]);
        					num_expr.addTerm(BigM, b[p][i][t]);
        					cplex.addLe(num_expr, BigM-1);
        				}
        			}
        		}
        		for(int t=1;t<T_true;t++){
        			for(int i:SinkCellIndex){
        				for(int p=0;p<P;p++){
        					num_expr = cplex.linearNumExpr();
        					num_expr.addTerm(1.0,u[p][t]);
        					num_expr.addTerm(-1.0, u[p][t-1]);
        					num_expr.addTerm(BigM, b[p][i][t]);
        					cplex.addLe(num_expr, BigM+1);
        				}
        			}
        		}
        		for(int t=1;t<T_true;t++){
        			for(int i:SinkCellIndex){
        				for(int p=0;p<P;p++){
        					num_expr = cplex.linearNumExpr();
        					num_expr.addTerm(1.0, u[p][t]);
        					num_expr.addTerm(-BigM, b[p][i][t]);
        					cplex.addLe(num_expr,0);
        				}
        			}
        		}
        		for(int t=1;t<T_true;t++){
        			for(int i:AllCellIndex){
        				for(int p=0;p<P;p++){
        					num_expr = cplex.linearNumExpr();
        					for(int j:all_cell.get(i).getSucessor()){
        						num_expr.addTerm(1.0, b[p][j][t]);
        					}
        					num_expr.addTerm(-1.0, b[p][i][t-1]);
        					num_expr.addTerm(1.0, b[p][i][t]);
        					cplex.addGe(num_expr, 0);
        				}
        			}
        		}
        		for(int t=0;t<T_true;t++){
        			for(int i:SinkCellIndex){
        				for(int p=0;p<P;p++){
        					num_expr = cplex.linearNumExpr();
        					num_expr.addTerm(1.0, h[p][t]);
        					for(int j:all_cell.get(i).getSucessor()){
        						num_expr.addTerm(BigM, b[p][j][t]);
        						//num_expr.addTerm(BigM, L[p][i][t]);
        					}
        					cplex.addLe(num_expr, BigM);
        				}
        			}
        		}
        		for(int p=0;p<P;p++){
        			num_expr = cplex.linearNumExpr();
        			num_expr.addTerm(1.0, b[p][14][0]);
        			
        			cplex.addEq(num_expr, 1);
        		}
        		for(int p=0;p<P;p++){
        			num_expr = cplex.linearNumExpr();
        			num_expr.addTerm(1.0, h[p][0]);
        			
        			cplex.addEq(num_expr, 0);        			        			
        		}
        		for(int p=0;p<P;p++){
        			num_expr = cplex.linearNumExpr();
        			num_expr.addTerm(1.0, u[p][0]);
        			
        			cplex.addEq(num_expr, 0);        			        			
        		}
        		
        			
        		}catch(IloException e){
        			e.printStackTrace();
        			
        			
        			

        		}
        	}
        	public void AddBound(){
        		try{
        		/*for(IloConstraint c:constraints){
        			cplex.add(c);
        		}*/
        		double RHS =0;
             	num_expr = cplex.linearNumExpr();
         		num_expr.addTerm(1.0, Z);
         		for(int t=0;t<T_true;t++){
         			for(int p=0;p<P;p++){
         				num_expr.addTerm(-1.0, h[p][t]);
         				num_expr.addTerm(1, u[p][t]);
         			}
         		}
         		for(int t=1;t<T_true;t++){
         			for(int i:SourceCellIndex){
         				for(int p=0;p<P;p++){
         					
         					num_expr.addTerm(u1Zero[i][t], b[p][i][t-1]);
         				}
         			}
         			for(int i:SinkCellIndex){
         				for(int p=0;p<P;p++){
         					
         					num_expr.addTerm(-u1Zero[i][t], b[p][i][t-1]);
         				}
         			}
         		}
         		
         		for(int t=0;t<T_true-1;t++){
         			for(int i:AllCellIndex ){
         				for(int p=0;p<P;p++){
         					
         					num_expr.addTerm(-u3Zero[i][t], L[p][i][t+1]);
         				}
         			}
         		}
         		for(int t=0;t<T_true-1;t++){
         			for(int i:AllCellIndex){
         				for(int p=0;p<P;p++){
         				   
         				   num_expr.addTerm(-u4Zero[i][t], E[p][i][t+1]);
         				}
         			}
         		}
         		for(int t=0;t<T_true-1;t++){
         			for(int i:AllCellIndex){
         				for(int p=0;p<P;p++){
         					
         					num_expr.addTerm(-u5Zero[i][t], E[p][i][t+1]);
         				}
         			}
         			        			
         		}
         		for(int t=1;t<=T_true-Tau-1;t++){
         			for(int i:IntermediateCellIndex){
         				
             				for(int p=0;p<P;p++){
             					for(int r=0;r<Tau;r++){
             						num_expr.addTerm(+u6Zero[p][i][t][r], b[p][i][t+r+1]);
             						num_expr.addTerm(-BigM*u6Zero[p][i][t][r],E[p][i][t] );
             					}
             				}
             			 
         			}
         		}
         		
         		for(int t=T_true-Tau;t<T_true-1;t++){
         			for(int i:IntermediateCellIndex){
         				
             				for(int p=0;p<P;p++){
             					for(int r=0;r<T_true-1-t;r++){
             						num_expr.addTerm(+u6Zero[p][i][t][r], b[p][i][t+r+1]);
             						num_expr.addTerm(-BigM*u6Zero[p][i][t][r],E[p][i][t] );
             					}
             				}
             			 
         			}
         		}
         		         		
         		for(int t=1;t<T_true;t++){
         			for(int i:SourceCellIndex){
         				RHS = RHS +u1Zero[i][t]*d[i][t-1];
         			}
         		}	
         		for(int t=0;t<T_true;t++){
         			for(int i:AllCellIndex){
         				RHS = RHS - u3Zero[i][t]*all_cell.get(i).getFlow();
         				RHS = RHS - u4Zero[i][t]*all_cell.get(i).getFlow();
         				//RHS = RHS + u5Value[i][t]*all_cell.get(i).getCapacity();         			
         			}
         		}
         		for(int t=0;t<T_true;t++){
         			for(int i:AllCellIndex){         				        			
         			RHS = RHS - u5Zero[i][t]*all_cell.get(i).getCapacity();
         		    }
         		}	
         		for(int t=1;t<=T_true-Tau-1;t++){
         		    for(int i:IntermediateCellIndex){
         				for(int p=0;p<P;p++){
         					for(int r=0;r<Tau;r++){
         						RHS = RHS +u6Zero[p][i][t][r]*BigM;
         					}
         				}
         			}         		         			
         		}
         		for(int t=T_true-Tau;t<T_true-1;t++){
         		    for(int i:IntermediateCellIndex){
         				for(int p=0;p<P;p++){
         					for(int r=0;r<T_true-t-1;r++){
         						RHS = RHS +u6Zero[p][i][t][r]*BigM;
         					}
         				}
         			}         		         			
         		}
         		//IloConstraint[] constraints = new IloConstraint();
				//constraints.add(cplex.addGe(num_expr, RHS));
         		cplex.addGe(num_expr, RHS);
              }
        	catch(IloException e){
    			e.printStackTrace();}
        
        }
            public void solve(){
            	try{
            		//cplex.exportModel("SubProblem.lp");   
            		cplex.exportModel("SubProblem1.lp"); 
            		if(cplex.solve()==true){
            			System.out.println("sub problem solved");
            		}else{
            			System.out.println("sub problem failed");
            		}
				    cplex.solve();
				    objPrimalValue=cplex.getObjValue();
				    System.out.println("ObjPrimalValue"+objPrimalValue);
/**
 * Check b variables every time, to make sure they are different
 */
				   /* int decisionDifCounter=0;
				    for(int t=0;t<T_true;t++){
				    	for(int i:AllCellIndex){
				    		for(int p=0;p<P;P++){
				    			if(bValue[p][i][t]!=cplex.getValue(b[p][i][t])){
				    				decisionDifCounter=decisionDifCounter+1;
				    			}
				    		}
				    	}
				    }
				    System.out.println("Different decision variable number : "+decisionDifCounter);*/
				    
				    for(int t=0;t<T_true;t++){
				    	for(int i:AllCellIndex){
				    		for(int p=0;p<P;p++){
				    			bValue[p][i][t]=cplex.getValue(b[p][i][t]);	
/**
 * for each iteration print b variables "bValue"
 */
				    			/*if(bValue[p][i][t]>0.99&&bValue[p][i][t]<1.1){
									System.out.println("b."+p+"."+i+"."+t+"."+":"+bValue[p][i][t]);
								}*/
				    			
				    		}
				    	}
				    }
				    for(int t=1;t<T_true;t++){
				    	for(int i:AllCellIndex){
				    		for(int p=0;p<P;p++){
				    			
				    			EValue[p][i][t]=cplex.getValue(E[p][i][t]);
				    			//System.out.println("E."+p+"."+i+"."+t+":"+""+EValue[p][i][t]);
				    			LValue[p][i][t]=cplex.getValue(L[p][i][t]);
				    			//System.out.println("L."+p+"."+i+"."+t+":"+""+LValue[p][i][t]);
				    		}
				    	}
				    }
				    for(int t=0;t<T_true;t++){
				    	for(int p=0;p<P;p++){
				    		hValue[p][t]=cplex.getValue(h[p][t]);
				    		//System.out.println("h."+p+"."+t+":"+""+hValue[p][t]);
				    		uValue[p][t]=cplex.getValue(u[p][t]);
				    		//System.out.println("u."+p+"."+t+":"+""+uValue[p][t]);
				    	}
				    }
            	}catch(IloException e){
        			e.printStackTrace();}
            }
            public void runBender(){
            	AddBound();
            	solve();
            }
        
        
        
        }
       public class linearSubproblem{                                                                      
       	private  IloCplex cplex;
       	private IloNumVar Z;
       	private IloIntVar b[][][];
       	private IloIntVar E[][][];
       	private IloIntVar L[][][];
       	private IloIntVar h[][];
       	private IloIntVar u[][];
       	private IloLinearNumExpr primal_obj;
       	private IloLinearNumExpr num_expr;
       	
       	public linearSubproblem(){
       		b = new IloIntVar[P][Cell_Num][T_true];
       		E = new IloIntVar[P][Cell_Num][T_true];
       		L = new IloIntVar[P][Cell_Num][T_true];
       		h = new IloIntVar[P][T_true];
       		u = new IloIntVar[P][T_true];    		
       		CreatModel();
       	}
       	public void CreatModel(){
       		try{
       			cplex= new IloCplex();
       			for(int t=0;t<T_true;t++){
           			for(int i:AllCellIndex){
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
           		for(int t=0;t<T_true;t++){
           			for(int p=0;p<P;p++){
           				h[p][t]=cplex.intVar(0, Buscapacity);
           				h[p][t].setName("h."+p+"."+t);
           				u[p][t]=cplex.intVar(0, Buscapacity);
           				u[p][t].setName("u."+p+"."+t);
        }
}
           	Z=cplex.numVar(-Double.MAX_VALUE,Double.MAX_VALUE);
           	Z.setName("Z");
       		primal_obj = cplex.linearNumExpr();
       		primal_obj.addTerm(1, Z);
       		cplex.addMinimize(primal_obj);
       		for(int t=1;t<T_true;t++){
       			for(int i:AllCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,E[p][i][t]);
       					num_expr.addTerm(-1.0,b[p][i][t]);
       					num_expr.addTerm(1.0,b[p][i][t-1]);
       					cplex.addGe(num_expr, 0);        				
       				}
       			}
       		}
       		
       		for(int t=1;t<T_true;t++){
       			for(int i:AllCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,L[p][i][t]);
       					num_expr.addTerm(-1.0,b[p][i][t-1]);
       					num_expr.addTerm(1.0,b[p][i][t]);
       					cplex.addGe(num_expr, 0);
       				
       				}
       			}
       		}
       		
       		for(int t=0;t<T_true;t++){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					for(int i:AllCellIndex){
       					num_expr.addTerm(1.0, b[p][i][t]);
       					
       				
       				}
       					cplex.addEq(num_expr, 1);
       			}
       		}
       		for(int t=0;t<T_true-Buscapacity;t++) {
       			for(int i:SourceCellIndex) {
       				for(int p=0;p<P;p++) {
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,L[p][i][t+Buscapacity]);
       					num_expr.addTerm(-1.0,L[p][i][t]);
       					cplex.addGe(num_expr, 0);
       				}
       			}
       		}
/*      	
       		for(int t=1;t<T_true;t++){
       			for(int i:SourceCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,h[p][t-1]);
       					num_expr.addTerm(-1.0, h[p][t]);
       					num_expr.addTerm(BigM, b[p][i][t]);
       					cplex.addLe(num_expr, BigM-1);
       				}
       			}
       		}
       		for(int t=1;t<T_true;t++){
       			for(int i:SourceCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,h[p][t]);
       					num_expr.addTerm(-1.0, h[p][t-1]);
       					num_expr.addTerm(BigM, b[p][i][t]);
       					cplex.addLe(num_expr, BigM+1);
       				}
       			}
       		}
       		for(int t=1;t<T_true;t++){
       			for(int i:IntermediateCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,h[p][t-1]);
       					num_expr.addTerm(-1.0, h[p][t]);
       					num_expr.addTerm(BigM, b[p][i][t]);
       					cplex.addLe(num_expr, BigM);
       				}
       			}
       		}
       		for(int t=1;t<T_true;t++){
       			for(int i:IntermediateCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,h[p][t]);
       					num_expr.addTerm(-1.0, h[p][t-1]);
       					num_expr.addTerm(BigM, b[p][i][t]);
       					cplex.addLe(num_expr, BigM);
       				}
       			}
       		}
       		for(int t=1;t<T_true;t++){
       			for(int i:SinkCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,h[p][t-1]);
       					num_expr.addTerm(-1.0, h[p][t]);
       					num_expr.addTerm(BigM, b[p][i][t]);
       					cplex.addLe(num_expr, BigM+1);
       				}
       			}
       		}
       		
       		for(int t=1;t<T_true;t++){
       			for(int i:SinkCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,h[p][t]);
       					num_expr.addTerm(-1.0, h[p][t-1]);
       					num_expr.addTerm(BigM, b[p][i][t]);
       					cplex.addLe(num_expr, BigM-1);
       				}
       			}
       		}
       		for(int t=1;t<T_true;t++){
       			for(int i:SinkCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,u[p][t-1]);
       					num_expr.addTerm(-1.0, u[p][t]);
       					num_expr.addTerm(BigM, b[p][i][t]);
       					cplex.addLe(num_expr, BigM-1);
       				}
       			}
       		}
       		for(int t=1;t<T_true;t++){
       			for(int i:SinkCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,u[p][t]);
       					num_expr.addTerm(-1.0, u[p][t-1]);
       					num_expr.addTerm(BigM, b[p][i][t]);
       					cplex.addLe(num_expr, BigM+1);
       				}
       			}
       		}
       		for(int t=1;t<T_true;t++){
       			for(int i:SinkCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0, u[p][t]);
       					num_expr.addTerm(-BigM, b[p][i][t]);
       					cplex.addLe(num_expr,0);
       				}
       			}
       		}
*/
       		for(int t=1;t<T_true;t++){
       			for(int i:AllCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					for(int j:all_cell.get(i).getSucessor()){
       						num_expr.addTerm(1.0, b[p][j][t]);
       					}
       					num_expr.addTerm(-1.0, b[p][i][t-1]);
       					num_expr.addTerm(1.0, b[p][i][t]);
       					cplex.addGe(num_expr, 0);
       				}
       			}
       		}
/*       		
       		for(int t=0;t<T_true;t++){
       			for(int i:SinkCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0, h[p][t]);
       					for(int j:all_cell.get(i).getSucessor()){
       						num_expr.addTerm(BigM, b[p][j][t]);
       						//num_expr.addTerm(BigM, L[p][i][t]);
       					}
       					cplex.addLe(num_expr, BigM);
       				}
       			}
       		}
*/       		
       		for(int p=0;p<P;p++){
       			num_expr = cplex.linearNumExpr();
       			num_expr.addTerm(1.0, b[p][14][0]);
       			
       			cplex.addEq(num_expr, 1);
       		}
/*       		
       		for(int p=0;p<P;p++){
       			num_expr = cplex.linearNumExpr();
       			num_expr.addTerm(1.0, h[p][0]);
       			
       			cplex.addEq(num_expr, 0);        			        			
       		}
       		for(int p=0;p<P;p++){
       			num_expr = cplex.linearNumExpr();
       			num_expr.addTerm(1.0, u[p][0]);
       			
       			cplex.addEq(num_expr, 0);        			        			
       		}
*/       		
       			
       		}catch(IloException e){
       			e.printStackTrace();
       			
       			
       			

       		}
       	}
       	public void AddBound(){
       		try{
       		/*for(IloConstraint c:constraints){
       			cplex.add(c);
       		}*/
       		double RHS =0;
            	num_expr = cplex.linearNumExpr();
        		num_expr.addTerm(1.0, Z);
/*        		
        		for(int t=0;t<T_true;t++){
        			for(int p=0;p<P;p++){
        				num_expr.addTerm(-1.0, h[p][t]);
        				num_expr.addTerm(1, u[p][t]);
        			}
        		}*/
        		for(int t=1;t<T_true;t++){
        			for(int i:SourceCellIndex){
        				for(int p=0;p<P;p++){
        					
        					num_expr.addTerm(u1Value[i][t], b[p][i][t-1]);
        				}
        			}
        			for(int i:SinkCellIndex){
        				for(int p=0;p<P;p++){
        					
        					num_expr.addTerm(-u1Value[i][t], b[p][i][t-1]);
        				}
        			}
        		}
        		
        		for(int t=0;t<T_true-1;t++){
        			for(int i:AllCellIndex ){
        				for(int p=0;p<P;p++){
        					
        					num_expr.addTerm(-u3Value[i][t], L[p][i][t+1]);
        				}
        			}
        		}
        		for(int t=0;t<T_true-1;t++){
        			for(int i:AllCellIndex){
        				for(int p=0;p<P;p++){
        				   
        				   num_expr.addTerm(-u4Value[i][t], E[p][i][t+1]);
        				}
        			}
        		}
        		for(int t=0;t<T_true-1;t++){
        			for(int i:AllCellIndex){
        				for(int p=0;p<P;p++){
        					
        					num_expr.addTerm(-u5Value[i][t], E[p][i][t+1]);
        				}
        			}
        			        			
        		}
        		for(int t=1;t<=T_true-Tau-1;t++){
        			for(int i:IntermediateCellIndex){
        				
            				for(int p=0;p<P;p++){
            					for(int r=0;r<Tau;r++){
            						num_expr.addTerm(+u6Value[p][i][t][r], b[p][i][t+r+1]);
            						num_expr.addTerm(-BigM*u6Value[p][i][t][r],E[p][i][t] );
            					}
            				}
            			 
        			}
        		}
        		
        		for(int t=T_true-Tau;t<T_true-1;t++){
        			for(int i:IntermediateCellIndex){
        				
            				for(int p=0;p<P;p++){
            					for(int r=0;r<T_true-1-t;r++){
            						num_expr.addTerm(+u6Value[p][i][t][r], b[p][i][t+r+1]);
            						num_expr.addTerm(-BigM*u6Value[p][i][t][r],E[p][i][t] );
            					}
            				}
            			 
        			}
        		}
        		         		
        		for(int t=1;t<T_true;t++){
        			for(int i:SourceCellIndex){
        				RHS = RHS +u1Value[i][t]*d[i][t-1];
        			}
        		}	
        		for(int t=0;t<T_true;t++){
        			for(int i:AllCellIndex){
        				RHS = RHS - u3Value[i][t]*all_cell.get(i).getFlow();
        				RHS = RHS - u4Value[i][t]*all_cell.get(i).getFlow();
        				//RHS = RHS + u5Value[i][t]*all_cell.get(i).getCapacity();         			
        			}
        		}
        		for(int t=0;t<T_true;t++){
        			for(int i:AllCellIndex){         				        			
        			RHS = RHS - u5Value[i][t]*all_cell.get(i).getCapacity();
        		    }
        		}	
        		for(int t=1;t<=T_true-Tau-1;t++){
        		    for(int i:IntermediateCellIndex){
        				for(int p=0;p<P;p++){
        					for(int r=0;r<Tau;r++){
        						RHS = RHS +u6Value[p][i][t][r]*BigM;
        					}
        				}
        			}         		         			
        		}
        		for(int t=T_true-Tau;t<T_true-1;t++){
        		    for(int i:IntermediateCellIndex){
        				for(int p=0;p<P;p++){
        					for(int r=0;r<T_true-t-1;r++){
        						RHS = RHS +u6Value[p][i][t][r]*BigM;
        					}
        				}
        			}         		         			
        		}
        		//IloConstraint[] constraints = new IloConstraint();
				//constraints.add(cplex.addGe(num_expr, RHS));
        		cplex.addGe(num_expr, RHS);
             }
       	catch(IloException e){
   			e.printStackTrace();}
       
       }
           public void solve(){
           	try{
           		//cplex.exportModel("SubProblem.lp");   
           		cplex.exportModel("SubProblem1.lp"); 
           		if(cplex.solve()==true){
           			System.out.println("sub problem solved");
           		}else{
           			System.out.println("sub problem failed");
           		}
				    cplex.solve();
				    objPrimalValue=cplex.getObjValue();
				    System.out.println("ObjPrimalValue"+objPrimalValue);
/**
* Check b variables every time, to make sure they are different
*/
				   /* int decisionDifCounter=0;
				    for(int t=0;t<T_true;t++){
				    	for(int i:AllCellIndex){
				    		for(int p=0;p<P;P++){
				    			if(bValue[p][i][t]!=cplex.getValue(b[p][i][t])){
				    				decisionDifCounter=decisionDifCounter+1;
				    			}
				    		}
				    	}
				    }
				    System.out.println("Different decision variable number : "+decisionDifCounter);*/
				    
				    for(int t=0;t<T_true;t++){
				    	for(int i:AllCellIndex){
				    		for(int p=0;p<P;p++){
				    			bValue[p][i][t]=cplex.getValue(b[p][i][t]);	
/**
* for each iteration print b variables "bValue"
*/
				    			/*if(bValue[p][i][t]>0.99&&bValue[p][i][t]<1.1){
									System.out.println("b."+p+"."+i+"."+t+"."+":"+bValue[p][i][t]);
								}*/
				    			
				    		}
				    	}
				    }
				    for(int t=1;t<T_true;t++){
				    	for(int i:AllCellIndex){
				    		for(int p=0;p<P;p++){
				    			
				    			EValue[p][i][t]=cplex.getValue(E[p][i][t]);
				    			//System.out.println("E."+p+"."+i+"."+t+":"+""+EValue[p][i][t]);
				    			LValue[p][i][t]=cplex.getValue(L[p][i][t]);
				    			//System.out.println("L."+p+"."+i+"."+t+":"+""+LValue[p][i][t]);
				    		}
				    	}
				    }
				    /*
				    for(int t=0;t<T_true;t++){
				    	for(int p=0;p<P;p++){
				    		hValue[p][t]=cplex.getValue(h[p][t]);
				    		//System.out.println("h."+p+"."+t+":"+""+hValue[p][t]);
				    		uValue[p][t]=cplex.getValue(u[p][t]);
				    		//System.out.println("u."+p+"."+t+":"+""+uValue[p][t]);
				    	}
				    }*/
           	}catch(IloException e){
       			e.printStackTrace();}
           }
           public void runBender(){
           	AddBound();
           	solve();
           }
       
       
       
       }
       public class Greedysubproblem{
    	private  IloCplex cplex;       	
       	private IloIntVar b[][][];
       	private IloIntVar E[][][];
       	private IloIntVar L[][][];
       	private IloIntVar h[][];
       	private IloIntVar u[][];
       	private IloLinearNumExpr primal_obj;
       	private IloLinearNumExpr num_expr;
       	
       	public Greedysubproblem( ){
       		b = new IloIntVar[P][Cell_Num][T_true];
       		E = new IloIntVar[P][Cell_Num][T_true];
       		L = new IloIntVar[P][Cell_Num][T_true];
       		h = new IloIntVar[P][T_true];
       		u = new IloIntVar[P][T_true];           		
       		CreatModel();
       		solve();
       	}
       	public void CreatModel(){
       		try{
       			cplex= new IloCplex();
       			for(int t=0;t<T_true;t++){
           			for(int i:AllCellIndex){
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
           		for(int t=0;t<T_true;t++){
           			for(int p=0;p<P;p++){
           				h[p][t]=cplex.intVar(0, Buscapacity);
           				h[p][t].setName("h."+p+"."+t);
           				u[p][t]=cplex.intVar(0, Buscapacity);
           				u[p][t].setName("u."+p+"."+t);
           			}
           		}
           
       		primal_obj = cplex.linearNumExpr();
       		for(int t=0;t<21;t++){       			
       				for(int p=0;p<P;p++){
       				     primal_obj.addTerm(1.0, u[p][t]);
       				
       			}
       		}       		
       		cplex.addMaximize(primal_obj);
       		for(int t=1;t<T_true;t++){
       			for(int i:AllCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,E[p][i][t]);
       					num_expr.addTerm(-1.0,b[p][i][t]);
       					num_expr.addTerm(1.0,b[p][i][t-1]);
       					cplex.addGe(num_expr, 0);        				
       				}
       			}
       		}
       		
       		for(int t=1;t<T_true;t++){
       			for(int i:AllCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,L[p][i][t]);
       					num_expr.addTerm(-1.0,b[p][i][t-1]);
       					num_expr.addTerm(1.0,b[p][i][t]);
       					cplex.addGe(num_expr, 0);
       				
       				}
       			}
       		}
       		
       		for(int t=0;t<T_true;t++){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					for(int i:AllCellIndex){
       					num_expr.addTerm(1.0, b[p][i][t]);
       					
       				
       				}
       					cplex.addEq(num_expr, 1);
       			}
       		}
       	
       		for(int t=1;t<T_true;t++){
       			for(int i:SourceCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,h[p][t-1]);
       					num_expr.addTerm(-1.0, h[p][t]);
       					num_expr.addTerm(BigM, b[p][i][t]);
       					cplex.addLe(num_expr, BigM-1);
       				}
       			}
       		}
       		for(int t=1;t<T_true;t++){
       			for(int i:SourceCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,h[p][t]);
       					num_expr.addTerm(-1.0, h[p][t-1]);
       					num_expr.addTerm(BigM, b[p][i][t]);
       					cplex.addLe(num_expr, BigM+1);
       				}
       			}
       		}
       		for(int t=1;t<T_true;t++){
       			for(int i:IntermediateCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,h[p][t-1]);
       					num_expr.addTerm(-1.0, h[p][t]);
       					num_expr.addTerm(BigM, b[p][i][t]);
       					cplex.addLe(num_expr, BigM);
       				}
       			}
       		}
       		for(int t=1;t<T_true;t++){
       			for(int i:IntermediateCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,h[p][t]);
       					num_expr.addTerm(-1.0, h[p][t-1]);
       					num_expr.addTerm(BigM, b[p][i][t]);
       					cplex.addLe(num_expr, BigM);
       				}
       			}
       		}
       		for(int t=1;t<T_true;t++){
       			for(int i:SinkCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,h[p][t-1]);
       					num_expr.addTerm(-1.0, h[p][t]);
       					num_expr.addTerm(BigM, b[p][i][t]);
       					cplex.addLe(num_expr, BigM+1);
       				}
       			}
       		}
       		
       		for(int t=1;t<T_true;t++){
       			for(int i:SinkCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,h[p][t]);
       					num_expr.addTerm(-1.0, h[p][t-1]);
       					num_expr.addTerm(BigM, b[p][i][t]);
       					cplex.addLe(num_expr, BigM-1);
       				}
       			}
       		}
       		for(int t=1;t<T_true;t++){
       			for(int i:SinkCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,u[p][t-1]);
       					num_expr.addTerm(-1.0, u[p][t]);
       					num_expr.addTerm(BigM, b[p][i][t]);
       					cplex.addLe(num_expr, BigM-1);
       				}
       			}
       		}
       		for(int t=1;t<T_true;t++){
       			for(int i:SinkCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0,u[p][t]);
       					num_expr.addTerm(-1.0, u[p][t-1]);
       					num_expr.addTerm(BigM, b[p][i][t]);
       					cplex.addLe(num_expr, BigM+1);
       				}
       			}
       		}
       		for(int t=1;t<T_true;t++){
       			for(int i:SinkCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0, u[p][t]);
       					num_expr.addTerm(-BigM, b[p][i][t]);
       					cplex.addLe(num_expr,0);
       				}
       			}
       		}
       		for(int t=1;t<T_true;t++){
       			for(int i:AllCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					for(int j:all_cell.get(i).getSucessor()){
       						num_expr.addTerm(1.0, b[p][j][t]);
       					}
       					num_expr.addTerm(-1.0, b[p][i][t-1]);
       					num_expr.addTerm(1.0, b[p][i][t]);
       					cplex.addGe(num_expr, 0);
       				}
       			}
       		}
       		for(int t=0;t<T_true;t++){
       			for(int i:SinkCellIndex){
       				for(int p=0;p<P;p++){
       					num_expr = cplex.linearNumExpr();
       					num_expr.addTerm(1.0, h[p][t]);
       					for(int j:all_cell.get(i).getSucessor()){
       						num_expr.addTerm(BigM, b[p][j][t]);
       						//num_expr.addTerm(BigM, L[p][i][t]);
       					}
       					cplex.addLe(num_expr, BigM);
       				}
       			}
       		}
       		for(int p=0;p<P;p++){
       			num_expr = cplex.linearNumExpr();
       			num_expr.addTerm(1.0, b[p][14][0]);
       			
       			cplex.addEq(num_expr, 1);
       		}
       		for(int p=0;p<P;p++){
       			num_expr = cplex.linearNumExpr();
       			num_expr.addTerm(1.0, h[p][0]);
       			
       			cplex.addEq(num_expr, 0);        			        			
       		}
       		for(int p=0;p<P;p++){
       			num_expr = cplex.linearNumExpr();
       			num_expr.addTerm(1.0, u[p][0]);
       			
       			cplex.addEq(num_expr, 0);        			        			
       		}
       		
       			
       		}catch(IloException e){
       			e.printStackTrace();
       			
       			
       			

       		}      	       		
       
       }
        public void solve(){
           	try{
           		//cplex.exportModel("SubProblem("+IterationCounter+").lp");   
           		    //cplex.exportModel("SubProblem.lp"); 
				    cplex.solve();
				    //objPrimalValue=cplex.getObjValue();
				    //System.out.println("ObjPrimalValue"+objPrimalValue);
				    
				    for(int t=0;t<T_true;t++){
				    	for(int i:AllCellIndex){
				    		for(int p=0;p<P;p++){
				    			bZero[p][i][t]=cplex.getValue(b[p][i][t]);					    							    			
				    		}
				    	}
				    }
				  /*  
				    for(int p=0;p<P;p++){				    
				    	for(int t=0;t<T_true;t++){
				    		for(int i:AllCellIndex){
				    		if(bZero[p][i][t]>0.99&&bZero[p][i][t]<1.1){
								System.out.println("bZero."+p+"."+i+"."+t+"."+":"+bZero[p][i][t]);
							}
				    	}
				    }
				    }
				    */
				    for(int t=1;t<T_true;t++){
				    	for(int i:AllCellIndex){
				    		for(int p=0;p<P;p++){
				    			
				    			EZero[p][i][t]=cplex.getValue(E[p][i][t]);
				    			//System.out.println("E."+p+"."+i+"."+t+":"+""+EValue[p][i][t]);
				    			LZero[p][i][t]=cplex.getValue(L[p][i][t]);
				    			//System.out.println("L."+p+"."+i+"."+t+":"+""+LValue[p][i][t]);
				    		}
				    	}
				    }
				    for(int t=0;t<T_true;t++){
				    	for(int p=0;p<P;p++){
				    		hZero[p][t]=cplex.getValue(h[p][t]);
				    		//System.out.println("h."+p+"."+t+":"+""+hValue[p][t]);
				    		uZero[p][t]=cplex.getValue(u[p][t]);
				    		//System.out.println("u."+p+"."+t+":"+""+uValue[p][t]);
				    	}
				    }
           	}catch(IloException e){
       			e.printStackTrace();}
           }
         
       
       }
       public class ParetoOptimalCut{
    	private  IloCplex cplex;
       	private IloLinearNumExpr paretoOptObj;
       	private IloLinearNumExpr num_expr;
       	private IloNumVar u1[][];
       	private IloNumVar u2[][];
       	private IloNumVar u3[][];
       	private IloNumVar u4[][];
       	private IloNumVar u5[][];
       	private IloNumVar u6[][][][];
    	   public ParetoOptimalCut(){
    		   u1 = new IloNumVar[Cell_Num][T_true];
         		u2 = new IloNumVar[Cell_Num][T_true];
         		u3 = new IloNumVar[Cell_Num][T_true];
         		u4 = new IloNumVar[Cell_Num][T_true];
         		u5 = new IloNumVar[Cell_Num][T_true];
         		u6 = new IloNumVar[P][Cell_Num][T_true][Tau];
         		CreateModel();
         		Solve();
    	   }
    	   public void CreateModel(){
    		   try{
    			cplex = new IloCplex();
         		for(int t=0;t<T_true;t++){
          		    for(int i=0;i<Cell_Num;i++){              			              				
          		    	u1[i][t] = cplex.numVar(-Double.MAX_VALUE, Double.MAX_VALUE );
          				u1[i][t].setName("u1."+i+"."+t);        
          				u2[i][t] = cplex.numVar(0, Double.MAX_VALUE );
          				u2[i][t].setName("u2."+i+"."+t);              				
          				u3[i][t] = cplex.numVar(0, Double.MAX_VALUE );
          				u3[i][t].setName("u3."+i+"."+t);              				
          				u4[i][t] = cplex.numVar(0, Double.MAX_VALUE );
          				u4[i][t].setName("u4."+i+"."+t);              				
          				u5[i][t] = cplex.numVar(0, Double.MAX_VALUE );
          				u5[i][t].setName("u5."+i+"."+t);
          				for(int p=0;p<P;p++){
          					for(int r=0;r<Tau;r++){
                  				u6[p][i][t][r] = cplex.numVar(0, Double.MAX_VALUE );
                  				u6[p][i][t][r].setName("u6."+p+"."+i+"."+t+"."+r);
          					}
          				}
          				
          			}
          		}
          		paretoOptObj  = cplex.linearNumExpr();
          		for(int t=1;t <T_true;t++){
          			for(int i:SourceCellIndex){
          				double FixedValue = 0;
          				for(int p =0; p<P;p++){
/**
* Fixed wrong code +bvalue CHANGE TO -bvalue
*/
          					FixedValue = FixedValue - bZero[p][i][t-1];
          				}
          				paretoOptObj.addTerm(d[i][t-1]+FixedValue, u1[i][t]);
          			}
          			for(int i:SinkCellIndex){
          				double FixedValue =0;
          				for(int p=0;p<P;p++){
          					FixedValue = FixedValue + bZero[p][i][t-1];
          				}
          				paretoOptObj.addTerm(FixedValue, u1[i][t]);
          			}
          			
          		}
          		for(int t=0;t<T_true-1;t++){
          			for(int i:AllCellIndex){
          				double FixedValue=0;
          				for(int p=0;p<P;p++){
          					FixedValue = FixedValue+LZero[p][i][t+1];
          				}
          				paretoOptObj.addTerm(FixedValue-all_cell.get(i).getFlow(), u3[i][t]);
          			}
          		}
          		for(int i:AllCellIndex){
          			paretoOptObj.addTerm(-all_cell.get(i).getFlow(), u3[i][T_true-1]);
          		}
          		for(int t=0;t<T_true-1;t++){
          			for(int i:AllCellIndex){
          				double FixedValue=0;
          				for(int p=0;p<P;p++){
          					FixedValue = FixedValue+EZero[p][i][t+1];
          				}
          				paretoOptObj.addTerm(FixedValue-all_cell.get(i).getFlow(), u4[i][t]);
          			}
          		}
          		for(int i:AllCellIndex){
          			paretoOptObj.addTerm(-all_cell.get(i).getFlow(), u4[i][T_true-1]);
          		}
          		for(int t=0;t<T_true-1;t++){
          			for(int i:AllCellIndex){
          				double FixedValue=0;
          				for(int p=0;p<P;p++){
/**
* change E[t] to E[t+1]
*/
          					FixedValue = FixedValue+EZero[p][i][t+1];
          				}
          				paretoOptObj.addTerm(FixedValue-all_cell.get(i).getCapacity(), u5[i][t]);
          			}
          			
          		}
          		for(int i:AllCellIndex){
          			paretoOptObj.addTerm(-all_cell.get(i).getCapacity(), u5[i][T_true-1]);
          		}
          		for(int t=1;t<=T_true-Tau-1;t++){
          			for(int i:IntermediateCellIndex){
          				for(int p=0;p<P;p++){
          				   for(int r=0;r<Tau;r++){
          					 paretoOptObj.addTerm(-bZero[p][i][t+r+1]-BigM+BigM*EZero[p][i][t], u6[p][i][t][r]);
          				   }
          			   }
          			}
          		}
          		for(int t=T_true-Tau;t<T_true-1;t++){
          			for(int i:IntermediateCellIndex){
          				for(int p=0;p<P;p++){
          				   for(int r=0;r<T_true-1-t;r++){
          					 paretoOptObj.addTerm(-bZero[p][i][t+r+1]-BigM+BigM*EZero[p][i][t], u6[p][i][t][r]);
          				   }
          			   }
          			}
          		}
          		cplex.addMaximize(paretoOptObj);  
          		
/**
* MasterProblem Constraints              		
*/
          		IloLinearNumExpr num_expr1 = cplex.linearNumExpr();
          		for(int t=1;t <T_true;t++){
          			for(int i:SourceCellIndex){
          				double FixedValue = 0;
          				for(int p =0; p<P;p++){
/**
* Fixed wrong code +bvalue CHANGE TO -bvalue
*/
          					FixedValue = FixedValue - bValue[p][i][t-1];
          				}
          				num_expr1.addTerm(d[i][t-1]+FixedValue, u1[i][t]);
          			}
          			for(int i:SinkCellIndex){
          				double FixedValue =0;
          				for(int p=0;p<P;p++){
          					FixedValue = FixedValue + bValue[p][i][t-1];
          				}
          				num_expr1.addTerm(FixedValue, u1[i][t]);
          			}
          			
          		}
          		for(int t=0;t<T_true-1;t++){
          			for(int i:AllCellIndex){
          				double FixedValue=0;
          				for(int p=0;p<P;p++){
          					FixedValue = FixedValue+LValue[p][i][t+1];
          				}
          				num_expr1.addTerm(FixedValue-all_cell.get(i).getFlow(), u3[i][t]);
          			}
          		}
          		for(int i:AllCellIndex){
          			num_expr1.addTerm(-all_cell.get(i).getFlow(), u3[i][T_true-1]);
          		}
          		for(int t=0;t<T_true-1;t++){
          			for(int i:AllCellIndex){
          				double FixedValue=0;
          				for(int p=0;p<P;p++){
          					FixedValue = FixedValue+EValue[p][i][t+1];
          				}
          				num_expr1.addTerm(FixedValue-all_cell.get(i).getFlow(), u4[i][t]);
          			}
          		}
          		for(int i:AllCellIndex){
          			num_expr1.addTerm(-all_cell.get(i).getFlow(), u4[i][T_true-1]);
          		}
          		for(int t=0;t<T_true-1;t++){
          			for(int i:AllCellIndex){
          				double FixedValue=0;
          				for(int p=0;p<P;p++){
/**
* change E[t] to E[t+1]
*/
          					FixedValue = FixedValue+EValue[p][i][t+1];
          				}
          				num_expr1.addTerm(FixedValue-all_cell.get(i).getCapacity(), u5[i][t]);
          			}
          			
          		}
          		for(int i:AllCellIndex){
          			num_expr1.addTerm(-all_cell.get(i).getCapacity(), u5[i][T_true-1]);
          		}
          		for(int t=1;t<=T_true-Tau-1;t++){
          			for(int i:IntermediateCellIndex){
          				for(int p=0;p<P;p++){
          				   for(int r=0;r<Tau;r++){
          					 num_expr1.addTerm(-bValue[p][i][t+r+1]-BigM+BigM*EValue[p][i][t], u6[p][i][t][r]);
          				   }
          			   }
          			}
          		}
          		for(int t=T_true-Tau;t<T_true-1;t++){
          			for(int i:IntermediateCellIndex){
          				for(int p=0;p<P;p++){
          				   for(int r=0;r<T_true-1-t;r++){
          					 num_expr1.addTerm(-bValue[p][i][t+r+1]-BigM+BigM*EValue[p][i][t], u6[p][i][t][r]);
          				   }
          			   }
          			}
          		}
          		
          		
          		cplex.addEq(num_expr1, paretoObjValue);
/**
 * Normal constraints          		
 */
          		for(int t=0;t<T_true-1;t++){
          			for(int i:SourceCellIndex){
          			    num_expr = cplex.linearNumExpr();
          			    num_expr.addTerm(1.0, u1[i][t]);
          			    num_expr.addTerm(-1.0, u1[i][t+1]);
          			    num_expr.addTerm(1.0, u2[i][t]);
          			    num_expr.addTerm(-1.0, u5[i][t]);
          			    //System.out.println(i+""+t);
          			    cplex.addLe(num_expr, 1);
          			}	
          		}
          		for(int i:SourceCellIndex){
          			
          			num_expr = cplex.linearNumExpr();
          			num_expr.addTerm(1.0, u1[i][T_true-1]);
          			num_expr.addTerm(1.0, u2[i][T_true-1]);
          			num_expr.addTerm(-1.0, u5[i][T_true-1]);
          			
          			cplex.addLe(num_expr, 1);
          		}
          		for(int i:IntermediateCellIndex){
          			num_expr = cplex.linearNumExpr();
          			num_expr.addTerm(1.0,u1[i][0]);
          			num_expr.addTerm(-1.0, u1[i][1]);
          			num_expr.addTerm(1.0, u2[i][0]);
          			num_expr.addTerm(-1.0, u5[i][0]);
          			
          			cplex.addLe(num_expr, 1);
          		}
          		for(int t=1;t<=T_true-Tau-1;t++){
          			for(int i:IntermediateCellIndex){
          				num_expr = cplex.linearNumExpr();
          				num_expr.addTerm(1.0, u1[i][t]);
          				num_expr.addTerm(-1.0, u1[i][t+1]);
          				num_expr.addTerm(1.0, u2[i][t]);
          				num_expr.addTerm(-1.0, u5[i][t]);
          				for(int p=0;p<P;p++){
          					for(int r=0;r<Tau;r++){
          						num_expr.addTerm(-1.0/all_cell.get(i).getCapacity(), u6[p][i][t][r]);
          					}
          				}
          				
          				cplex.addLe(num_expr, 1);
          			}
          		}
          		for(int t=T_true-Tau;t<T_true-1;t++){
          			for(int i:IntermediateCellIndex){
          				num_expr = cplex.linearNumExpr();
          				num_expr.addTerm(1.0, u1[i][t]);
          				num_expr.addTerm(-1.0, u1[i][t+1]);
          				num_expr.addTerm(1.0, u2[i][t]);
          				num_expr.addTerm(-1.0, u5[i][t]);
          				for(int p=0;p<P;p++){
          					for(int r=0;r<T_true-t-1;r++){
          						num_expr.addTerm(-1.0/all_cell.get(i).getCapacity(), u6[p][i][t][r]);
          					}
          				}
          				
          				cplex.addLe(num_expr, 1);
          			}
          		}
          		for(int i:IntermediateCellIndex){
          			num_expr = cplex.linearNumExpr();
          			num_expr.addTerm(1.0,u1[i][T_true-1]);
          			num_expr.addTerm(1.0, u2[i][T_true-1]);
          			num_expr.addTerm(-1.0, u5[i][T_true-1]);
          			
          			
          			cplex.addLe(num_expr,1);
          		}
          		
          		for(int t=0;t<T_true-1;t++){
          			for(int i:SinkCellIndex){
          				num_expr = cplex.linearNumExpr();
          				num_expr.addTerm(1.0, u1[i][t]);
          				num_expr.addTerm(-1.0, u1[i][t+1]);
          				num_expr.addTerm(1.0, u2[i][t]);
          				num_expr.addTerm(-1.0,u5[i][t] );
          				
          				cplex.addLe(num_expr, 0);
          			}
          		}
          		for(int i:SinkCellIndex){
          			num_expr = cplex.linearNumExpr();
          			num_expr.addTerm(1.0, u1[i][T_true-1]);
          			num_expr.addTerm(1.0, u2[i][T_true-1]);
          			num_expr.addTerm(-1.0, u5[i][T_true-1]);
          			cplex.addLe(num_expr, 0);
          		}
/**
* dual equations for y variables              		
*/
          		for(int t=Tau;t<T_true-1;t++){
          			for(int i:IntermediateCellIndex){
          				for(int j:all_cell.get(i).getSucessor()){
          					num_expr = cplex.linearNumExpr();
              				num_expr.addTerm(1.0,u1[i][t+1]);
              				num_expr.addTerm(-1.0, u1[j][t+1]);
              				num_expr.addTerm(-1.0, u2[i][t]);
              				num_expr.addTerm(-1.0, u3[i][t]);
              				num_expr.addTerm(-1.0, u4[j][t]);
              				num_expr.addTerm(-1.0, u5[j][t]);
              				//if(contains(IntermediateCellIndex,i)){
              					for(int p=0;p<P;p++){
                  					for(int r=t-Tau+1;r<=t;r++){
                  					    for(int k=t-r;k<Tau;k++){
                  					    	//if(r+k>=t ){
                  					    		num_expr.addTerm(1.0/all_cell.get(i).getCapacity(), u6[p][i][r][k]);
                  					    		
                  					    	//}
                  					   // }
                  					}   					
                  				}
              				}
              				
              				cplex.addLe(num_expr, 0);
          				}
          			}
          		}
          		for(int t=1;t<Tau;t++){
          			for(int i:IntermediateCellIndex){
          				for(int j:all_cell.get(i).getSucessor()){
          					num_expr = cplex.linearNumExpr();
              				num_expr.addTerm(1.0,u1[i][t+1]);
              				num_expr.addTerm(-1.0, u1[j][t+1]);
              				num_expr.addTerm(-1.0, u2[i][t]);
              				num_expr.addTerm(-1.0, u3[i][t]);
              				num_expr.addTerm(-1.0, u4[j][t]);
              				num_expr.addTerm(-1.0, u5[j][t]);
              				for(int p=0;p<P;p++){
              					for(int r=1;r<=t;r++){
              					    for(int k=t-r;k<Tau;k++){
              					    	
              					    		num_expr.addTerm(1.0/all_cell.get(i).getCapacity(), u6[p][i][r][k]);
              					    		
              					    	
              					    }
              					}
              				}
              				cplex.addLe(num_expr, 0);
          				}
          			}
          		}
          		for(int i:IntermediateCellIndex){
      				for(int j:all_cell.get(i).getSucessor()){
      					num_expr = cplex.linearNumExpr();
      					num_expr.addTerm(1.0, u1[i][1]);
      					num_expr.addTerm(-1.0, u1[j][1]);
      					num_expr.addTerm(-1.0, u2[i][0]);
          				num_expr.addTerm(-1.0, u3[i][0]);
          				num_expr.addTerm(-1.0, u4[j][0]);
          				num_expr.addTerm(-1.0, u5[j][0]);
          				cplex.addLe(num_expr, 0);
      				}
      				
      			}
          		for(int i:IntermediateCellIndex){
      				for(int j:all_cell.get(i).getSucessor()){
      					num_expr = cplex.linearNumExpr();
      					num_expr.addTerm(-1.0, u2[i][T_true-1]);
          				num_expr.addTerm(-1.0, u3[i][T_true-1]);
          				num_expr.addTerm(-1.0, u4[j][T_true-1]);
          				num_expr.addTerm(-1.0, u5[j][T_true-1]);
          				
          				cplex.addLe(num_expr, 0);
      				}
          		
          		}
          		
          		for(int t=0;t<T_true-1;t++){
          			for(int i:SourceCellIndex){
          				for(int j:all_cell.get(i).getSucessor()){
          					num_expr = cplex.linearNumExpr();
              				num_expr.addTerm(1.0,u1[i][t+1]);
              				num_expr.addTerm(-1.0, u1[j][t+1]);
              				num_expr.addTerm(-1.0, u2[i][t]);
              				num_expr.addTerm(-1.0, u3[i][t]);
              				num_expr.addTerm(-1.0, u4[j][t]);
              				num_expr.addTerm(-1.0, u5[j][t]);
              				
              				cplex.addLe(num_expr, 0);
          				}
          			}
          		}	
          		for(int i:SourceCellIndex){
      				for(int j:all_cell.get(i).getSucessor()){
      					num_expr = cplex.linearNumExpr();              			
          				num_expr.addTerm(-1.0, u2[i][T_true-1]);
          				num_expr.addTerm(-1.0, u3[i][T_true-1]);
          				num_expr.addTerm(-1.0, u4[j][T_true-1]);
          				num_expr.addTerm(-1.0, u5[j][T_true-1]);
          				
          				cplex.addLe(num_expr, 0);
      				}
      			}
          		                            		
          		for(int t=0;t<T_true-1;t++){
          			for(int i:SinkCellIndex ){
          				for(int j:all_cell.get(i).getSucessor()){
          					num_expr = cplex.linearNumExpr();
            				num_expr.addTerm(1.0,u1[i][t+1]);
            				num_expr.addTerm(-1.0, u1[j][t+1]);
            				num_expr.addTerm(-1.0, u2[i][t]);
            				num_expr.addTerm(-1.0, u3[i][t]);
            				num_expr.addTerm(-1.0, u4[j][t]);
            				num_expr.addTerm(-1.0, u5[j][t]);
            				
            				cplex.addLe(num_expr, 0); 
          				}          				
          			}          			
          		}
          		for(int i:SinkCellIndex){
      				for(int j:all_cell.get(i).getSucessor()){
      					num_expr = cplex.linearNumExpr();              			
          				num_expr.addTerm(-1.0, u2[i][T_true-1]);
          				num_expr.addTerm(-1.0, u3[i][T_true-1]);
          				num_expr.addTerm(-1.0, u4[j][T_true-1]);
          				num_expr.addTerm(-1.0, u5[j][T_true-1]);          				
          				cplex.addLe(num_expr, 0);
      				}
      			}
    		   }catch (IloException e) {
     				System.err.println("Concert exception caught: " + e);      				
     			}
    	   }
           public void Solve(){
        	   try{
        		   if(cplex.solve()== true){
   			    	System.out.println("optimal cut generated");   			    	
   			    }
   			    else{
   			    	System.out.println("optimal cut generate fail");
   			    }
              cplex.exportModel("ParetoOptimal.lp"); 
        	   for(int t=0;t<T_true;t++){
			    	for(int i:AllCellIndex){
			    		u1Value[i][t]=cplex.getValue(this.u1[i][t]);			    		
			    		//System.out.println("u1"+i+""+t+":"+""+u1Value[i][t]);
			    		//double b = cplex.getValue(this.u1[i][t]);			    		
			    		//System.out.println("u1"+i+""+t+":"+""+b);
			    	}
			    }
			    for(int t=0;t<T_true;t++){
			    	for(int i:AllCellIndex){
			    		u2Value[i][t]=cplex.getValue(this.u2[i][t]);
			    		u2Zero[i][t]=u2Value[i][t];
			    		//u2Value[i][t]=u2Zero[i][t];
			    		//System.out.println("u2"+i+""+t+":"+""+u2Value[i][t]);
			    		u3Value[i][t]=cplex.getValue(this.u3[i][t]);
			    		u3Zero[i][t]=u3Value[i][t];
			    		//u3Value[i][t]=u3Zero[i][t];
			    		//System.out.println("u3"+i+""+t+":"+""+u3Value[i][t]);
			    		u4Value[i][t]=cplex.getValue(this.u4[i][t]);
			    		u4Zero[i][t]=u4Value[i][t];
			    		//u4Value[i][t]=u4Zero[i][t];
			    		//System.out.println("u4"+i+""+t+":"+""+u4Value[i][t]);
			    		u5Value[i][t]=cplex.getValue(this.u5[i][t]);
			    		u5Zero[i][t]=u5Value[i][t];
			    		//u5Value[i][t]=u5Zero[i][t];
			    		//System.out.println("u5"+i+""+t+":"+""+u5Value[i][t]);
			    		
			    	}
			    }
			    for(int t=1;t<=T_true-Tau-1;t++){
			    	for(int i:IntermediateCellIndex){
			    		for(int p=0;p<P;p++){
			    			for(int r=0;r<Tau;r++){
			    				u6Value[p][i][t][r]=cplex.getValue(this.u6[p][i][t][r]);
			    				u6Zero[p][i][t][r]=u6Value[p][i][t][r];
			    				//u6Value[p][i][t][r]=u6Zero[p][i][t][r];
			    				//System.out.println("u6"+p+""+i+""+t+""+r+":"+""+u6Value[p][i][t][r]);
			    			}
			    		}
			    	}
			    }
			    for(int t=T_true-Tau;t<T_true-1;t++){
			    	for(int i:IntermediateCellIndex){
			    		for(int p=0;p<P;p++){
			    			for(int r=0;r<T_true-t-1;r++){
			    				u6Value[p][i][t][r]=cplex.getValue(this.u6[p][i][t][r]);
			    				u6Zero[p][i][t][r]=u6Value[p][i][t][r];
			    				//u6Value[p][i][t][r]=u6Zero[p][i][t][r];
			    				//System.out.println("u6"+p+""+i+""+t+""+r+":"+""+u6Value[p][i][t][r]);
			    			}
			    		}
			    	}
			    }
        	   }catch(IloException e){
        		   e.printStackTrace();
        	   }
           }
       }
       public void InitiateY(){
    	   //Greedysubproblem e = new Greedysubproblem();
    	  // System.out.println("Yzero generated");
    		for(int t=0;t<T_true;t++){
        		for(int i:AllCellIndex){
        			for(int p=0;p<P;p++){        				
        				this.EZero[p][i][t]=0;
        				this.LZero[p][i][t]=0;
        			}
        		}
        	}
        	for(int t=0;t<T_true;t++){        		
        			for(int p=0;p<P;p++){
        				this.bZero[p][15][t]=1;
        			}       		
        	}
        	for(int t=0;t<T_true;t++){
        		for(int p=0;p<P;p++){
        			this.hZero[p][t]=0;
        			this.uZero[p][t]=0;
        		}
        	}
       }
       public void SetData(){
        	//this.constraints = new ArrayList<IloConstraint>();
        	all_cell.put(0, cell_0);
        	all_cell.put(1, cell_1);
        	all_cell.put(2, cell_2);
        	all_cell.put(3, cell_3);
        	all_cell.put(4, cell_4);
        	all_cell.put(5, cell_5);
        	all_cell.put(6, cell_6);
        	all_cell.put(7, cell_7);
        	all_cell.put(8, cell_8);
        	all_cell.put(9, cell_9);
        	all_cell.put(10, cell_10);
        	all_cell.put(11, cell_11);
        	all_cell.put(12, cell_12);
        	all_cell.put(13, cell_13);
        	all_cell.put(14, cell_14);
        	all_cell.put(15, cell_15);
        	all_cell.put(16, cell_16);
        	source_cell.put(0, cell_0);
        	source_cell.put(1, cell_1);
        	Intermediate_cell.put(2, cell_2);
        	Intermediate_cell.put(3, cell_3);
        	Intermediate_cell.put(4, cell_4);
        	Intermediate_cell.put(5, cell_5);
        	Intermediate_cell.put(6, cell_6);
        	Intermediate_cell.put(7, cell_7);
        	Intermediate_cell.put(8, cell_8);
        	Intermediate_cell.put(10, cell_11);
        	Intermediate_cell.put(11, cell_11);
        	Intermediate_cell.put(12, cell_12);
        	Intermediate_cell.put(13, cell_13);
        	Intermediate_cell.put(14, cell_14);
        	Intermediate_cell.put(15, cell_15);
        	Intermediate_cell.put(16, cell_16);
        	sink_cell.put(9,cell_9);
        	AllCellIndex = new int[]{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16};
      		SourceCellIndex = new int[]{0,1};
      		IntermediateCellIndex = new int[]{2,3,4,5,6,7,8,10,11,12,13,14,15,16};
      		SinkCellIndex = new int[]{9};
        	Cell_Num = AllCellIndex.length;
      		T_true = 20;
      		Tau=2;
      		P=2;      		
      		Buscapacity=3;
      		BigM=Buscapacity+1;
      		iterationT=5;
      		d = new double[SourceCellIndex.length][T_true];
      		u1Value = new double[AllCellIndex.length][T_true];
      		u1ValueC = new double[AllCellIndex.length][T_true];
      		u2Value = new double[AllCellIndex.length][T_true];
      		u3Value = new double[AllCellIndex.length][T_true];
      		u4Value = new double[AllCellIndex.length][T_true];
      		u5Value = new double[AllCellIndex.length][T_true];
      		u6Value = new double[P][AllCellIndex.length][T_true][Tau];
      		u1Set = new double[AllCellIndex.length][T_true][iterationT];
      		u2Set = new double[AllCellIndex.length][T_true][iterationT];
      		u3Set = new double[AllCellIndex.length][T_true][iterationT];
      		u4Set = new double[AllCellIndex.length][T_true][iterationT];
      		u5Set = new double[AllCellIndex.length][T_true][iterationT];
      		u6Set = new double[P][AllCellIndex.length][T_true][Tau][iterationT];
      		bValue = new double[P][AllCellIndex.length][T_true];
      		bDummy = new double[AllCellIndex.length][T_true+20];
      		LValue = new double[P][AllCellIndex.length][T_true];
      		EValue = new double[P][AllCellIndex.length][T_true];
      		hValue = new double[P][T_true];
      		uValue = new double[P][T_true];
      		bZero = new double[P][AllCellIndex.length][T_true];
      		LZero = new double[P][AllCellIndex.length][T_true];
      		EZero = new double[P][AllCellIndex.length][T_true];
      		hZero = new double[P][T_true];
      		uZero = new double[P][T_true];
      		u1Zero = new double[AllCellIndex.length][T_true];
      		u2Zero = new double[AllCellIndex.length][T_true];
      		u3Zero = new double[AllCellIndex.length][T_true];
      		u4Zero = new double[AllCellIndex.length][T_true];
      		u5Zero = new double[AllCellIndex.length][T_true];
      		u6Zero = new double[P][AllCellIndex.length][T_true][Tau];
      		C = new int[AllCellIndex.length][AllCellIndex.length];
      		C[16][0]=3;
      		C[16][1]=10;
      		C[9][0]=3;
      		C[9][1]=3;
      		S=16;
      		LB=Double.MIN_VALUE;
      		UB=Double.MAX_VALUE;
      		
      		for(int t=0;t<1;t++){
      			for(int i:SourceCellIndex){
      				d[i][t]=150;
      			}
      		}
      		for(int t=1;t<T_true;t++){
      			for(int i:SourceCellIndex){
      				d[i][t]=0;
      			}
      		}
      		
      		
      	
        }

       public void Initiation(){
        	
        	for(int t=0;t<T_true;t++){
        		for(int i:AllCellIndex){
        			for(int p=0;p<P;p++){        				
        				this.EValue[p][i][t]=0;
        				this.LValue[p][i][t]=0;
        			}
        		}
        	}
        	for(int t=0;t<T_true;t++){
        		for(int p=0;p<P;p++){
        			for(int i:AllCellIndex){
        				this.bValue[p][i][t]=0;
        			}
        		}
        	}
        	for(int t=0;t<T_true;t++){        		
        			for(int p=0;p<P;p++){
        				this.bValue[p][16][t]=1;
        			}       		
        	}
        	for(int t=0;t<T_true;t++){
        		for(int p=0;p<P;p++){
        			this.hValue[p][t]=0;
        			this.uValue[p][t]=0;
        		}
        	}
        	for(int t=0;t<T_true;t++){
      		    for(int i=0;i<Cell_Num;i++){              			              				
      				u1Zero[i][t] = 0;      				      
      				u2Zero[i][t] =0;             				
      				u3Zero[i][t] = 0;            				
      				u4Zero[i][t] =0;           				
      				u5Zero[i][t] = 0;
      				for(int p=0;p<P;p++){
      					for(int r=0;r<Tau;r++){
              				u6Zero[p][i][t][r] = 0;             				
      					}
      				}
      				
      			}
      		}
      
        }

       public void runBenderDecomposition(){
    	 	Masterproblem masterproblem = new Masterproblem();
        	subproblem = new Subproblem();
        	do{
        		IterationCounter++;
        		System.out.println("Start Iteration:"+IterationCounter);
        	    subproblem.runBender();
        		Masterproblem masterproblem1 = new Masterproblem();
        		
        		
        	}while((objDualValue-objPrimalValue)/objPrimalValue>0.01 );
            primalSolve primalsolve = new primalSolve();
            
        	for(int i=0;i<P;i++){
				for(int j=0;j<T_true;j++){
					for(int r:AllCellIndex){
						if(bValue[i][r][j]>0.99&&bValue[i][r][j]<1.1){
							System.out.println("b."+i+"."+r+"."+j+"."+":"+bValue[i][r][j]);
						}
					}
				}
			}	
          System.out.println("FinalResult"+FinalResult);
        	
        
       }
       public void runparetoOptimalAlgorithm(){      
    	   InitiateY();
    	   Masterproblem masterproblem = new Masterproblem();
    	   ParetoOptimalCut paretocut = new ParetoOptimalCut();
       	   lsubproblem = new linearSubproblem();
       	do{
    		IterationCounter++;
    		System.out.println("Start Iteration:"+IterationCounter);
    	    lsubproblem.runBender();
    		Masterproblem masterproblem1 = new Masterproblem();
    		ParetoOptimalCut paretocut1 = new ParetoOptimalCut();
    		System.out.println("Iteration"+IterationCounter+":"+(objDualValue-objPrimalValue));
    		
    	}while(IterationCounter<20 );
       	
        
    	for(int i=0;i<P;i++){
			for(int j=0;j<T_true;j++){
				for(int r:AllCellIndex){
					if(bValue[i][r][j]>0.01&&bValue[i][r][j]<1.1){
						System.out.println("b."+i+"."+r+"."+j+"."+":"+bValue[i][r][j]);
					}
				}
			}
		}	
    	//primalSolve primalsolve = new primalSolve();
      System.out.println("FinalResult"+FinalResult);
       }
       public void runGreedyAlgorithm(){
    	   greedysubproblem = new Greedysubproblem();
    	   Masterproblem masterproblem = new Masterproblem();
    	   subproblem = new Subproblem();
       	   do{
       		   IterationCounter++;
       		   System.out.println("Start Iteration:"+IterationCounter);
       		   subproblem.runBender();
       		   Masterproblem masterproblem1 = new Masterproblem();
       	   }while(objDualValue>objPrimalValue );
       	primalSolve primalsolve = new primalSolve();
       	for(int i=0;i<P;i++){
				for(int j=0;j<T_true;j++){
					for(int r:AllCellIndex){
						if(bValue[i][r][j]>0.99&&bValue[i][r][j]<1.1){
							System.out.println("b."+i+"."+r+"."+j+"."+":"+bValue[i][r][j]);
						}
					}
				}
			}	
       
        System.out.println("FinalResult"+FinalResult);
       }
       public void test(){
    	   Greedysubproblem e = new Greedysubproblem();
       }
       public class cell {
    		
    	    private int[] predecessor;
    	    private int[] sucessor;
    	    private double capacity;
    	    private double flow;
    	    public cell(int[] predecessor ,int[] sucessor, double capacity,double flow){
    	    	this.predecessor = predecessor;
    	    	this.sucessor = sucessor;
    	    	this.capacity = capacity;
    	    	this.flow = flow;
    	    	
    	    }
    	    
    	    public int[] getPredecessor(){
    	    	return predecessor;
    	    }
    	    public int[] getSucessor(){
    	    	return sucessor;
    	    }
    	    public double getCapacity(){
    	    	return capacity;
    	    }
    	    public double getFlow(){
    	    	return flow;
    	    }
    	}
       public double[][][] getRoute(){
    	   double temp[][][] = new double[P][Cell_Num][T_true];
    	   for(int i=0;i<P;i++){
				for(int j=0;j<T_true;j++){
					for(int r:AllCellIndex){
					    temp[i][r][j] = bValue[i][r][j];
						
					}
				}
			}
    	   return temp;
       }
       
       public class primalSolve{
    	   private  IloCplex cplex;
    	   private IloLinearNumExpr obj;
    	   private IloLinearNumExpr num_expr;
    	   private IloNumVar x[][];
    	   private IloNumVar y[][][];  
    	     public primalSolve(){
    	    	 x = new IloNumVar[Cell_Num][T_true];
    	    	 y = new IloNumVar[Cell_Num][Cell_Num][T_true];    	    	
    	    	 CreatModel();
    	    	 solve();
    	     }
         public void CreatModel(){

    	    	 try{
               		cplex = new IloCplex();
               		for(int i:AllCellIndex){
               			for(int t=0;t<T_true;t++){
               				x[i][t] = cplex.numVar(0, Double.MAX_VALUE );
               				x[i][t].setName("x."+i+"."+t);               				
               			}
               		}
               		for(int i:AllCellIndex){
               			for(int j:AllCellIndex){
               			    for(int t=0;t<T_true;t++){
               			    	y[i][j][t] = cplex.numVar(0,Double.MAX_VALUE);
               			    	y[i][j][t].setName("y."+i+"."+j+"."+t);               			    }        				
               			}
               		}            
/**
 * object function               		
 */
            		
               		obj = cplex.linearNumExpr();
               		for(int t=0;t<T_true;t++){
               			for(int i:SourceCellIndex){
               				obj.addTerm(1.0, x[i][t]);
               			}
               			for(int i:IntermediateCellIndex){
               				obj.addTerm(1.0, x[i][t]);
               			}
               		}
               		cplex.addMinimize(obj);               		                           		
/**
 * constraints               		
 */
            	
               		for(int i:SourceCellIndex){
               			for(int t=1;t<T_true;t++){
               				num_expr = cplex.linearNumExpr();
               				num_expr.addTerm(1.0, x[i][t]);
               				num_expr.addTerm(-1.0,x[i][t-1]);
               				for(int j: all_cell.get(i).getSucessor()){
               					num_expr.addTerm(1.0, y[i][j][t-1]);
               				}
               				for(int k:all_cell.get(i).getPredecessor()){
               					num_expr.addTerm(-1.0,y[k][i][t-1]);
               				}
               				double temp = d[i][t-1];
               				for(int p=0;p<P;p++){
               					temp = temp - bValue[p][i][t-1];
               				}
               				cplex.addEq(num_expr, temp);
               				
               			
               			}
               		}
               		
               		for(int i:IntermediateCellIndex){
               			for(int t=1;t<T_true;t++){
               				num_expr = cplex.linearNumExpr();
               				num_expr.addTerm(1.0, x[i][t]);
               				num_expr.addTerm(-1.0,x[i][t-1]);
               				for(int j: all_cell.get(i).getSucessor()){
               					num_expr.addTerm(1.0, y[i][j][t-1]);
               				}
               				for(int k:all_cell.get(i).getPredecessor()){
               					num_expr.addTerm(-1.0,y[k][i][t-1]);
               				}
               				cplex.addEq(num_expr, 0);
               				
               			
               			}
               		}
               		
               		for(int i:SinkCellIndex){
               			for(int t=1;t<T_true;t++){
               				num_expr = cplex.linearNumExpr();
               				num_expr.addTerm(1.0, x[i][t]);
               				num_expr.addTerm(-1.0,x[i][t-1]);
               				for(int j: all_cell.get(i).getSucessor()){
               					num_expr.addTerm(1.0, y[i][j][t-1]);
               				}
               				for(int k:all_cell.get(i).getPredecessor()){
               					num_expr.addTerm(-1.0,y[k][i][t-1]);
               				}
               				double temp = 0;
               				for(int p=0;p<P;p++){
               					temp = temp + bValue[p][i][t-1];
               				}
               				cplex.addEq(num_expr, temp);
               				
               			
               			}
               		}
               		
               		for(int i:AllCellIndex){
               			for(int t=0;t<T_true;t++){
               				num_expr = cplex.linearNumExpr();
               				for(int j : all_cell.get(i).getSucessor()){
               					num_expr.addTerm(1.0,y[i][j][t]);
               				}
               				num_expr.addTerm(-1.0,x[i][t]);
               				cplex.addLe(num_expr, 0);
               			}
               		}
               		
               		for(int i:AllCellIndex){
               			for(int t=0;t<T_true-1;t++){
               				num_expr = cplex.linearNumExpr();
               				
               				for(int j : all_cell.get(i).getSucessor()){
               					num_expr.addTerm(1.0,y[i][j][t]);
               				}
               				double temp = all_cell.get(i).getFlow();
               				for(int p=0;p<P;p++){
               					temp = temp - LValue[p][i][t+1];
               				}
               				cplex.addLe(num_expr, temp);
               			}
               			
               		}
               		
               		for(int i:AllCellIndex){
               			num_expr = cplex.linearNumExpr();
               			for(int j : all_cell.get(i).getSucessor()){
           					num_expr.addTerm(1.0,y[i][j][T_true-1]);
           				}
               			double temp = all_cell.get(i).getFlow();
               			cplex.addLe(num_expr, temp);
               		}
               		
               		for(int i:AllCellIndex){
               			for(int t=0;t<T_true-1;t++){
               				num_expr = cplex.linearNumExpr();
               				
               				for(int k : all_cell.get(i).getPredecessor()){
               					num_expr.addTerm(1.0,y[k][i][t]);
               				}
               				double temp = all_cell.get(i).getFlow();
               				for(int p=0;p<P;p++){
               					temp = temp - EValue[p][i][t+1];
               				}
               				cplex.addLe(num_expr, temp);
               			}
               			
               		}
               		
               		for(int i:AllCellIndex){
               			num_expr = cplex.linearNumExpr();
               			for(int k : all_cell.get(i).getPredecessor()){
           					num_expr.addTerm(1.0,y[k][i][T_true-1]);
           				}
               			double temp = all_cell.get(i).getFlow();
               			cplex.addLe(num_expr, temp);
               		}
               		
               		for(int i:AllCellIndex){
               			for(int t=0;t<T_true-1;t++){
               				num_expr = cplex.linearNumExpr();
               				for(int k : all_cell.get(i).getPredecessor()){
               					num_expr.addTerm(1.0,y[k][i][t]);
               				}
               				num_expr.addTerm(1.0, x[i][t]);
               				
               				double temp = all_cell.get(i).getCapacity();
               				for(int p=0;p<P;p++){
               					temp = temp - EValue[p][i][t+1];
               				}
               				
               				cplex.addLe(num_expr,temp);
               			}
               		}
               		
               		for(int i:AllCellIndex){
               			num_expr = cplex.linearNumExpr();
               			for(int k : all_cell.get(i).getPredecessor()){
           					num_expr.addTerm(1.0,y[k][i][T_true-1]);
           				}
               			num_expr.addTerm(1.0, x[i][T_true-1]);
               			
               			double temp = all_cell.get(i).getCapacity();
               			cplex.addLe(num_expr,temp);
               		}
               			for(int t=1;t<=T_true-Tau-1;t++){
                  			for(int i:IntermediateCellIndex){
                  				for(int p=0;p<P;p++){
                  				   for(int r=0;r<Tau;r++){
                  					 num_expr = cplex.linearNumExpr();
                  					 num_expr.addTerm(-1.0/all_cell.get(i).getCapacity(), x[i][t]);
                  					 for(int o=0;o<=r;o++){
                  						 for(int u:all_cell.get(i).getSucessor()){
                  							 num_expr.addTerm(1.0/all_cell.get(i).getCapacity(), y[i][u][t+o]);
                  						 }
                  					 }
                  					 double temp = -bValue[p][i][t+r+1]-BigM+BigM*EValue[p][i][t];
                  					 
                  					 cplex.addGe(num_expr,temp);
                  				   }
                  			   }
                  			}
                  		}
                  		for(int t=T_true-Tau;t<T_true-1;t++){
                  			for(int i:IntermediateCellIndex){
                  				for(int p=0;p<P;p++){
                  				   for(int r=0;r<T_true-1-t;r++){
                  					 num_expr = cplex.linearNumExpr();
                  					 num_expr.addTerm(-1.0/all_cell.get(i).getCapacity(), x[i][t]);
                  					 for(int o=0;o<=r;o++){
                  						 for(int u:all_cell.get(i).getSucessor()){
                  							 num_expr.addTerm(1.0/all_cell.get(i).getCapacity(), y[i][u][t+o]);
                  						 }
                  					 }
                  					 double temp = -bValue[p][i][t+r+1]-BigM+BigM*EValue[p][i][t];
                  					 
                  					 cplex.addGe(num_expr,temp);
                  				   }
                  			   }
                  			}
                  		}
            		
                  		for(int i:AllCellIndex){
                  			num_expr = cplex.linearNumExpr();
                  			num_expr.addTerm(1.0,x[i][0]);
                  			cplex.addEq(num_expr,0);
                  		}
                  		for(int i:AllCellIndex){
                  			for(int j:AllCellIndex){
                  				num_expr = cplex.linearNumExpr();
                  				num_expr.addTerm(1.0,y[i][j][0]);
                  				cplex.addEq(num_expr,0);
                  			}
                  		}
    	    	 }catch (IloException e) {
       				System.err.println("Concert exception caught: " + e);
       				
       			}
    	     }
         public void solve(){
        	 try{
        		 cplex.exportModel("primalProb.lp");  
				    cplex.solve();
					FinalResult=cplex.getObjValue();
					 for(int t=0;t<T_true;t++){
						 for(int i:AllCellIndex){
							 System.out.println("x."+i+"."+t+":"+cplex.getValue(x[i][t]));
						 }
					 }
					 for(int t=0;t<T_true;t++){
						 for(int i:AllCellIndex){
							 for(int j:all_cell.get(i).getSucessor()){
								 if(cplex.getValue(y[i][j][t])>0){
									 System.out.println("y."+i+"."+j+"."+t+":"+cplex.getValue(y[i][j][t]));
								 }
							 }
						 }
					 }
					for(int p=0;p<P;p++){
						for(int t=0;t<T_true;t++){
							FinalResult = FinalResult + hValue[p][t]-uValue[p][t]; 
						}
					}
					}catch(IloException e){
	        			e.printStackTrace();}
         }
       }
       public void runPrimalProb(){
    	  
    	 	Masterproblem masterproblem = new Masterproblem();
        	subproblem = new Subproblem();
        	 for(int i=0;i<3;i++){
        		 subproblem.runBender();
        		 Masterproblem masterproblem1 = new Masterproblem();
        	 }
    	   primalSolve p =  new primalSolve();
       }
       public class DirectSolveModel{
    	   private  IloCplex cplex;
    	   private IloLinearNumExpr obj;
    	   private IloLinearNumExpr num_expr;
    	   private IloNumVar x[][];
    	   private IloNumVar y[][][];
    	   private IloIntVar b[][][];
       	   private IloIntVar E[][][];
           private IloIntVar L[][][];
       	   private IloIntVar h[][];
       	   private IloIntVar u[][];
    	   public DirectSolveModel(){    		        	   
        	 x = new IloNumVar[Cell_Num][T_true];
  	    	 y = new IloNumVar[Cell_Num][Cell_Num][T_true];
  	    	 b = new IloIntVar[P][Cell_Num][T_true];
    		 E = new IloIntVar[P][Cell_Num][T_true];
    		 L = new IloIntVar[P][Cell_Num][T_true];
    		 h = new IloIntVar[P][T_true];
    		 u = new IloIntVar[P][T_true]; 
  	    	 CreatModel();
  	    	 solve();
    	   }
             public void CreatModel(){


        	    	 try{
                   		cplex = new IloCplex();
                   		for(int i:AllCellIndex){
                   			for(int t=0;t<T_true;t++){
                   				x[i][t] = cplex.numVar(0, Double.MAX_VALUE );
                   				x[i][t].setName("x."+i+"."+t);               				
                   			}
                   		}
                   		for(int i:AllCellIndex){
                   			for(int j:AllCellIndex){
                   			    for(int t=0;t<T_true;t++){
                   			    	y[i][j][t] = cplex.numVar(0,Double.MAX_VALUE);
                   			    	y[i][j][t].setName("y."+i+"."+j+"."+t);               			    }        				
                   			}
                   		}
                   		for(int t=0;t<T_true;t++){
                			for(int i:AllCellIndex){
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
                		for(int t=0;t<T_true;t++){
                			for(int p=0;p<P;p++){
                				h[p][t]=cplex.intVar(0, Buscapacity);
                				h[p][t].setName("h."+p+"."+t);
                				u[p][t]=cplex.intVar(0, Buscapacity);
                				u[p][t].setName("u."+p+"."+t);
                			}
                		}
    /**
     * object fouction               		
     */
                   		obj = cplex.linearNumExpr();
                   		for(int t=0;t<T_true;t++){
                   			for(int i:SourceCellIndex){
                   				obj.addTerm(1.0, x[i][t]);
                   			}
                   			for(int i:IntermediateCellIndex){
                   				obj.addTerm(1.0, x[i][t]);
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
                   		for(int i:SourceCellIndex){
                   			for(int t=1;t<T_true;t++){
                   				num_expr = cplex.linearNumExpr();
                   				num_expr.addTerm(1.0, x[i][t]);
                   				num_expr.addTerm(-1.0,x[i][t-1]);
                   				for(int j: all_cell.get(i).getSucessor()){
                   					num_expr.addTerm(1.0, y[i][j][t-1]);
                   				}
                   				for(int k:all_cell.get(i).getPredecessor()){
                   					num_expr.addTerm(-1.0,y[k][i][t-1]);
                   				}
                   				for(int p=0;p<P;p++){
                   					num_expr.addTerm(1.0,b[p][i][t-1]);
                   				}
                   				double temp = d[i][t-1];
                   				
                   				cplex.addEq(num_expr, temp);
                   				
                   			
                   			}
                   		}
                   		
                   		for(int i:IntermediateCellIndex){
                   			for(int t=1;t<T_true;t++){
                   				num_expr = cplex.linearNumExpr();
                   				num_expr.addTerm(1.0, x[i][t]);
                   				num_expr.addTerm(-1.0,x[i][t-1]);
                   				for(int j: all_cell.get(i).getSucessor()){
                   					num_expr.addTerm(1.0, y[i][j][t-1]);
                   				}
                   				for(int k:all_cell.get(i).getPredecessor()){
                   					num_expr.addTerm(-1.0,y[k][i][t-1]);
                   				}
                   				cplex.addEq(num_expr, 0);
                   				
                   			
                   			}
                   		}
                   		
                   		for(int i:SinkCellIndex){
                   			for(int t=1;t<T_true;t++){
                   				num_expr = cplex.linearNumExpr();
                   				num_expr.addTerm(1.0, x[i][t]);
                   				num_expr.addTerm(-1.0,x[i][t-1]);
                   				for(int j: all_cell.get(i).getSucessor()){
                   					num_expr.addTerm(1.0, y[i][j][t-1]);
                   				}
                   				for(int k:all_cell.get(i).getPredecessor()){
                   					num_expr.addTerm(-1.0,y[k][i][t-1]);
                   				}
                   				for(int p=0;p<P;p++){
                   					num_expr.addTerm(-1.0,b[p][i][t-1]);
                   				}
                   				
                   				
                   				cplex.addEq(num_expr, 0);
                   				
                   			
                   			}
                   		}
                   		
                   		for(int i:AllCellIndex){
                   			for(int t=0;t<T_true;t++){
                   				num_expr = cplex.linearNumExpr();
                   				for(int j : all_cell.get(i).getSucessor()){
                   					num_expr.addTerm(1.0,y[i][j][t]);
                   				}
                   				num_expr.addTerm(-1.0,x[i][t]);
                   				cplex.addLe(num_expr, 0);
                   			}
                   		}
                   		
                   		for(int i:AllCellIndex){
                   			for(int t=0;t<T_true-1;t++){
                   				num_expr = cplex.linearNumExpr();
                   				
                   				for(int j : all_cell.get(i).getSucessor()){
                   					num_expr.addTerm(1.0,y[i][j][t]);
                   				}
                   				double temp = all_cell.get(i).getFlow();
                   				for(int p=0;p<P;p++){
                   					num_expr.addTerm(1.0,L[p][i][t+1]);
                   				}
                   				cplex.addLe(num_expr, temp);
                   			}
                   			
                   		}
                   		
                   		for(int i:AllCellIndex){
                   			num_expr = cplex.linearNumExpr();
                   			for(int j : all_cell.get(i).getSucessor()){
               					num_expr.addTerm(1.0,y[i][j][T_true-1]);
               				}
                   			double temp = all_cell.get(i).getFlow();
                   			cplex.addLe(num_expr, temp);
                   		}
                   		
                   		for(int i:AllCellIndex){
                   			for(int t=0;t<T_true-1;t++){
                   				num_expr = cplex.linearNumExpr();
                   				
                   				for(int k : all_cell.get(i).getPredecessor()){
                   					num_expr.addTerm(1.0,y[k][i][t]);
                   				}
                   				double temp = all_cell.get(i).getFlow();
                   				for(int p=0;p<P;p++){
                   					num_expr.addTerm(1.0,E[p][i][t+1]);
                   				}
                   				cplex.addLe(num_expr, temp);
                   			}
                   			
                   		}
                   		
                   		for(int i:AllCellIndex){
                   			num_expr = cplex.linearNumExpr();
                   			for(int k : all_cell.get(i).getPredecessor()){
               					num_expr.addTerm(1.0,y[k][i][T_true-1]);
               				}
                   			double temp = all_cell.get(i).getFlow();
                   			cplex.addLe(num_expr, temp);
                   		}
                   		
                   		for(int i:AllCellIndex){
                   			for(int t=0;t<T_true-1;t++){
                   				num_expr = cplex.linearNumExpr();
                   				for(int k : all_cell.get(i).getPredecessor()){
                   					num_expr.addTerm(1.0,y[k][i][t]);
                   				}
                   				num_expr.addTerm(1.0, x[i][t]);
                   				
                   				double temp = all_cell.get(i).getCapacity();
                   				for(int p=0;p<P;p++){
                   					num_expr.addTerm(1.0,E[p][i][t+1]);
                   				}
                   				
                   				cplex.addLe(num_expr,temp);
                   			}
                   		}
                   		
                   		for(int i:AllCellIndex){
                   			num_expr = cplex.linearNumExpr();
                   			for(int k : all_cell.get(i).getPredecessor()){
               					num_expr.addTerm(1.0,y[k][i][T_true-1]);
               				}
                   			num_expr.addTerm(1.0, x[i][T_true-1]);
                   			
                   			double temp = all_cell.get(i).getCapacity();
                   			cplex.addLe(num_expr,temp);
                   		}
                   			for(int t=1;t<=T_true-Tau-1;t++){
                      			for(int i:IntermediateCellIndex){
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
                      			for(int i:IntermediateCellIndex){
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
                      		
                      		for(int t=1;t<T_true;t++){
                    			for(int i:AllCellIndex){
                    				for(int p=0;p<P;p++){
                    					num_expr = cplex.linearNumExpr();
                    					num_expr.addTerm(1.0,E[p][i][t]);
                    					num_expr.addTerm(-1.0,b[p][i][t]);
                    					num_expr.addTerm(1.0,b[p][i][t-1]);
                    					cplex.addGe(num_expr, 0);        				
                    				}
                    			}
                    		}
                    		
                    		for(int t=1;t<T_true;t++){
                    			for(int i:AllCellIndex){
                    				for(int p=0;p<P;p++){
                    					num_expr = cplex.linearNumExpr();
                    					num_expr.addTerm(1.0,L[p][i][t]);
                    					num_expr.addTerm(-1.0,b[p][i][t-1]);
                    					num_expr.addTerm(1.0,b[p][i][t]);
                    					cplex.addGe(num_expr, 0);
                    				
                    				}
                    			}
                    		}
                    		
                    		for(int t=0;t<T_true;t++){
                    				for(int p=0;p<P;p++){
                    					num_expr = cplex.linearNumExpr();
                    					for(int i:AllCellIndex){
                    					num_expr.addTerm(1.0, b[p][i][t]);
                    					
                    				
                    				}
                    					cplex.addEq(num_expr, 1);
                    			}
                    		}
                    		
                    		
                    		for(int t=1;t<T_true;t++){
                    			for(int i:SourceCellIndex){
                    				for(int p=0;p<P;p++){
                    					num_expr = cplex.linearNumExpr();
                    					num_expr.addTerm(1.0,h[p][t-1]);
                    					num_expr.addTerm(-1.0, h[p][t]);
                    					num_expr.addTerm(BigM, b[p][i][t]);
                    					cplex.addLe(num_expr, BigM-1);
                    				}
                    			}
                    		}
                    		for(int t=1;t<T_true;t++){
                    			for(int i:SourceCellIndex){
                    				for(int p=0;p<P;p++){
                    					num_expr = cplex.linearNumExpr();
                    					num_expr.addTerm(1.0,h[p][t]);
                    					num_expr.addTerm(-1.0, h[p][t-1]);
                    					num_expr.addTerm(BigM, b[p][i][t]);
                    					cplex.addLe(num_expr, BigM+1);
                    				}
                    			}
                    		}
                    		for(int t=1;t<T_true;t++){
                    			for(int i:IntermediateCellIndex){
                    				for(int p=0;p<P;p++){
                    					num_expr = cplex.linearNumExpr();
                    					num_expr.addTerm(1.0,h[p][t-1]);
                    					num_expr.addTerm(-1.0, h[p][t]);
                    					num_expr.addTerm(BigM, b[p][i][t]);
                    					cplex.addLe(num_expr, BigM);
                    				}
                    			}
                    		}
                    		for(int t=1;t<T_true;t++){
                    			for(int i:IntermediateCellIndex){
                    				for(int p=0;p<P;p++){
                    					num_expr = cplex.linearNumExpr();
                    					num_expr.addTerm(1.0,h[p][t]);
                    					num_expr.addTerm(-1.0, h[p][t-1]);
                    					num_expr.addTerm(BigM, b[p][i][t]);
                    					cplex.addLe(num_expr, BigM);
                    				}
                    			}
                    		}
                    		for(int t=1;t<T_true;t++){
                    			for(int i:SinkCellIndex){
                    				for(int p=0;p<P;p++){
                    					num_expr = cplex.linearNumExpr();
                    					num_expr.addTerm(1.0,h[p][t-1]);
                    					num_expr.addTerm(-1.0, h[p][t]);
                    					num_expr.addTerm(BigM, b[p][i][t]);
                    					cplex.addLe(num_expr, BigM+1);
                    				}
                    			}
                    		}
                    		
                    		for(int t=1;t<T_true;t++){
                    			for(int i:SinkCellIndex){
                    				for(int p=0;p<P;p++){
                    					num_expr = cplex.linearNumExpr();
                    					num_expr.addTerm(1.0,h[p][t]);
                    					num_expr.addTerm(-1.0, h[p][t-1]);
                    					num_expr.addTerm(BigM, b[p][i][t]);
                    					cplex.addLe(num_expr, BigM-1);
                    				}
                    			}
                    		}
                    		for(int t=0;t<T_true-Buscapacity;t++) {
                    			for(int p=0;p<P;p++) {
                    				for(int i:SourceCellIndex) {
                    					num_expr = cplex.linearNumExpr();
                    					for(int k=0;k<Buscapacity;k++) {
                    						num_expr.addTerm(1.0, b[p][i][t+k]);
                    					}
                    					num_expr.addTerm(-3.0, E[p][i][t]);
                    					cplex.addGe(num_expr, 0);
                    				}
                    			}
                    		}
                    		/*
                    		for(int t=1;t<T_true;t++){
                    			for(int i:SinkCellIndex){
                    				for(int p=0;p<P;p++){
                    					num_expr = cplex.linearNumExpr();
                    					num_expr.addTerm(1.0,u[p][t-1]);
                    					num_expr.addTerm(-1.0, u[p][t]);
                    					num_expr.addTerm(BigM, b[p][i][t]);
                    					cplex.addLe(num_expr, BigM-1);
                    				}
                    			}
                    		}
                    		for(int t=1;t<T_true;t++){
                    			for(int i:SinkCellIndex){
                    				for(int p=0;p<P;p++){
                    					num_expr = cplex.linearNumExpr();
                    					num_expr.addTerm(1.0,u[p][t]);
                    					num_expr.addTerm(-1.0, u[p][t-1]);
                    					num_expr.addTerm(BigM, b[p][i][t]);
                    					cplex.addLe(num_expr, BigM+1);
                    				}
                    			}
                    		}
                    		for(int t=1;t<T_true;t++){
                    			for(int i:SinkCellIndex){
                    				for(int p=0;p<P;p++){
                    					num_expr = cplex.linearNumExpr();
                    					num_expr.addTerm(1.0, u[p][t]);
                    					num_expr.addTerm(-BigM, b[p][i][t]);
                    					cplex.addLe(num_expr,0);
                    				}
                    			}
                    		}*/
                    		for(int t=1;t<T_true;t++){
                    			for(int i:AllCellIndex){
                    				for(int p=0;p<P;p++){
                    					num_expr = cplex.linearNumExpr();
                    					for(int j:all_cell.get(i).getSucessor()){
                    						num_expr.addTerm(1.0, b[p][j][t]);
                    					}
                    					num_expr.addTerm(-1.0, b[p][i][t-1]);
                    					num_expr.addTerm(1.0, b[p][i][t]);
                    					cplex.addGe(num_expr, 0);
                    				}
                    			}
                    		}
                    		/*
                    		for(int t=0;t<T_true-Buscapacity;t++) {
                       			for(int i:SourceCellIndex) {
                       				for(int p=0;p<P;p++) {
                       					num_expr = cplex.linearNumExpr();
                       					num_expr.addTerm(1.0,L[p][i][t+Buscapacity]);
                       					num_expr.addTerm(-1.0,E[p][i][t]);
                       					cplex.addGe(num_expr, 0);
                       				}
                       			}
                       		}
                    		for(int p=0;p<P;p++) {
                    			num_expr = cplex.linearNumExpr();
                    			for(int i:SourceCellIndex) {
                    				for(int t=0;t<T_true;t++) {
                    					num_expr.addTerm(1.0, b[p][i][t]);
                    				}
                    			}
                    			for(int i:SinkCellIndex) {
                    				for(int t=0;t<T_true;t++) {
                    					num_expr.addTerm(-1.0, b[p][i][t]);
                    				}
                    			}
                    			cplex.addEq(num_expr, 0);
                    	}*/
                    		/*
                    		for(int t=0;t<T_true;t++){
                    			for(int i:SinkCellIndex){
                    				for(int p=0;p<P;p++){
                    					num_expr = cplex.linearNumExpr();
                    					num_expr.addTerm(1.0, h[p][t]);
                    					for(int j:all_cell.get(i).getSucessor()){
                    						num_expr.addTerm(BigM, b[p][j][t]);
                    						//num_expr.addTerm(BigM, L[p][i][t]);
                    					}
                    					cplex.addLe(num_expr, BigM);
                    				}
                    			}
                    		}*/
                    		for(int p=0;p<P;p++){
                    			num_expr = cplex.linearNumExpr();
                    			num_expr.addTerm(1.0, b[p][14][0]);
                    			
                    			cplex.addEq(num_expr, 1);
                    		}
                    		/*
                    		for(int p=0;p<P;p++){
                    			num_expr = cplex.linearNumExpr();
                    			num_expr.addTerm(1.0, h[p][0]);
                    			
                    			cplex.addEq(num_expr, 0);        			        			
                    		}
                    		for(int p=0;p<P;p++){
                    			num_expr = cplex.linearNumExpr();
                    			num_expr.addTerm(1.0, u[p][0]);
                    			
                    			cplex.addEq(num_expr, 0);        			        			
                    		}
                   		*/
                      		for(int i:AllCellIndex){
                      			num_expr = cplex.linearNumExpr();
                      			num_expr.addTerm(1.0,x[i][0]);
                      			cplex.addEq(num_expr,0);
                      		}
                      		for(int i:AllCellIndex){
                      			for(int j:AllCellIndex){
                      				num_expr = cplex.linearNumExpr();
                      				num_expr.addTerm(1.0,y[i][j][0]);
                      				cplex.addEq(num_expr,0);
                      			}
                      		}
        	    	 }catch (IloException e) {
           				System.err.println("Concert exception caught: " + e);
           				
           			}
    	   }
             public void solve(){
            	 try{
            		    cplex.exportModel("SubProblemD.lp");  
    				    cplex.solve();
    					DirectSolveResult=cplex.getObjValue();
    					System.out.println("DirectSolveResult"+DirectSolveResult);
    					for(int p=0;p<P;p++){
    					for(int t=0;t<T_true;t++){
    					    	for(int i:AllCellIndex){
    					    		
    					    			double temp = cplex.getValue(b[p][i][t]); 
    					    			if(temp>0.99&&temp<1.1){
    										System.out.println("b."+p+"."+i+"."+t+"."+":"+cplex.getValue(b[p][i][t]));
    									}
    					    			
    					    		}
    					    	}
    					    }/*
    					 for(int t=0;t<T_true;t++){
    						 for(int i:AllCellIndex){
    							 System.out.println("x."+i+"."+t+":"+cplex.getValue(x[i][t]));
    						 }
    					 }
    					 for(int t=0;t<T_true;t++){
    						 for(int i:AllCellIndex){
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
       public void DirectSolve(){
    	   DirectSolveModel example = new DirectSolveModel();
       }
       public class heuristicModel {         
    	   private  IloCplex cplex;
       	   private IloIntVar Z;
       	   private IloIntVar b[][][];
       	   private IloIntVar E[][][];
       	   private IloIntVar L[][][];
       	   private IloIntVar h[][];
    	   private IloIntVar u[][];
       	   private IloLinearNumExpr num_expr;
       	private IloLinearNumExpr obj;
    	   public heuristicModel(){
    		   b = new IloIntVar[P][Cell_Num][T_true];
       		E = new IloIntVar[P][Cell_Num][T_true];
       		L = new IloIntVar[P][Cell_Num][T_true];     
       		h = new IloIntVar[P][T_true];
    		u = new IloIntVar[P][T_true];    		
    		creatModel();
    		   }
    	   public void creatModel(){
    		   try{
       			cplex= new IloCplex();
       			for(int t=0;t<T_true;t++){
           			for(int i:AllCellIndex){
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
       			for(int t=0;t<T_true;t++){
        			for(int p=0;p<P;p++){
        				h[p][t]=cplex.intVar(0, Buscapacity);
        				h[p][t].setName("h."+p+"."+t);
        				u[p][t]=cplex.intVar(0, Buscapacity);
        				u[p][t].setName("u."+p+"."+t);
        			}
        		}
       			obj = cplex.linearNumExpr();
       			for(int t=0;t<T_true;t++){
       				for(int i: SourceCellIndex){
       					for(int p=0;p<P;p++){
       						obj.addTerm(u1Value[i][t],b[p][i][t]);
       					}
       				}
       				for(int p=0;p<P;p++){
       					obj.addTerm(1.0,u[p][t]);
       				}
       			}
       			
       			
       			cplex.addMaximize(obj);
       			for(int t=0;t<T_true;t++){
    				for(int p=0;p<P;p++){
    					num_expr = cplex.linearNumExpr();
    					for(int i:AllCellIndex){
    					num_expr.addTerm(1.0, b[p][i][t]);
    					
    				
    				}
    					cplex.addEq(num_expr, 1);
    			}
    		}
    	
    		for(int t=1;t<T_true;t++){
    			for(int i:SourceCellIndex){
    				for(int p=0;p<P;p++){
    					num_expr = cplex.linearNumExpr();
    					num_expr.addTerm(1.0,h[p][t-1]);
    					num_expr.addTerm(-1.0, h[p][t]);
    					num_expr.addTerm(BigM, b[p][i][t]);
    					cplex.addLe(num_expr, BigM-1);
    				}
    			}
    		}
    		for(int t=1;t<T_true;t++){
    			for(int i:SourceCellIndex){
    				for(int p=0;p<P;p++){
    					num_expr = cplex.linearNumExpr();
    					num_expr.addTerm(1.0,h[p][t]);
    					num_expr.addTerm(-1.0, h[p][t-1]);
    					num_expr.addTerm(BigM, b[p][i][t]);
    					cplex.addLe(num_expr, BigM+1);
    				}
    			}
    		}
    		for(int t=1;t<T_true;t++){
    			for(int i:IntermediateCellIndex){
    				for(int p=0;p<P;p++){
    					num_expr = cplex.linearNumExpr();
    					num_expr.addTerm(1.0,h[p][t-1]);
    					num_expr.addTerm(-1.0, h[p][t]);
    					num_expr.addTerm(BigM, b[p][i][t]);
    					cplex.addLe(num_expr, BigM);
    				}
    			}
    		}
    		for(int t=1;t<T_true;t++){
    			for(int i:IntermediateCellIndex){
    				for(int p=0;p<P;p++){
    					num_expr = cplex.linearNumExpr();
    					num_expr.addTerm(1.0,h[p][t]);
    					num_expr.addTerm(-1.0, h[p][t-1]);
    					num_expr.addTerm(BigM, b[p][i][t]);
    					cplex.addLe(num_expr, BigM);
    				}
    			}
    		}
    		for(int t=1;t<T_true;t++){
    			for(int i:SinkCellIndex){
    				for(int p=0;p<P;p++){
    					num_expr = cplex.linearNumExpr();
    					num_expr.addTerm(1.0,h[p][t-1]);
    					num_expr.addTerm(-1.0, h[p][t]);
    					num_expr.addTerm(BigM, b[p][i][t]);
    					cplex.addLe(num_expr, BigM+1);
    				}
    			}
    		}
    		
    		for(int t=1;t<T_true;t++){
    			for(int i:SinkCellIndex){
    				for(int p=0;p<P;p++){
    					num_expr = cplex.linearNumExpr();
    					num_expr.addTerm(1.0,h[p][t]);
    					num_expr.addTerm(-1.0, h[p][t-1]);
    					num_expr.addTerm(BigM, b[p][i][t]);
    					cplex.addLe(num_expr, BigM-1);
    				}
    			}
    		}
    		for(int t=1;t<T_true;t++){
    			for(int i:SinkCellIndex){
    				for(int p=0;p<P;p++){
    					num_expr = cplex.linearNumExpr();
    					num_expr.addTerm(1.0,u[p][t-1]);
    					num_expr.addTerm(-1.0, u[p][t]);
    					num_expr.addTerm(BigM, b[p][i][t]);
    					cplex.addLe(num_expr, BigM-1);
    				}
    			}
    		}
    		for(int t=1;t<T_true;t++){
    			for(int i:SinkCellIndex){
    				for(int p=0;p<P;p++){
    					num_expr = cplex.linearNumExpr();
    					num_expr.addTerm(1.0,u[p][t]);
    					num_expr.addTerm(-1.0, u[p][t-1]);
    					num_expr.addTerm(BigM, b[p][i][t]);
    					cplex.addLe(num_expr, BigM+1);
    				}
    			}
    		}
    		for(int t=1;t<T_true;t++){
    			for(int i:SinkCellIndex){
    				for(int p=0;p<P;p++){
    					num_expr = cplex.linearNumExpr();
    					num_expr.addTerm(1.0, u[p][t]);
    					num_expr.addTerm(-BigM, b[p][i][t]);
    					cplex.addLe(num_expr,0);
    				}
    			}
    		}
    		for(int t=1;t<T_true;t++){
    			for(int i:AllCellIndex){
    				for(int p=0;p<P;p++){
    					num_expr = cplex.linearNumExpr();
    					for(int j:all_cell.get(i).getSucessor()){
    						num_expr.addTerm(1.0, b[p][j][t]);
    					}
    					num_expr.addTerm(-1.0, b[p][i][t-1]);
    					num_expr.addTerm(1.0, b[p][i][t]);
    					cplex.addGe(num_expr, 0);
    				}
    			}
    		}
    		for(int t=0;t<T_true;t++){
    			for(int i:SinkCellIndex){
    				for(int p=0;p<P;p++){
    					num_expr = cplex.linearNumExpr();
    					num_expr.addTerm(1.0, h[p][t]);
    					for(int j:all_cell.get(i).getSucessor()){
    						num_expr.addTerm(BigM, b[p][j][t]);
    						//num_expr.addTerm(BigM, L[p][i][t]);
    					}
    					cplex.addLe(num_expr, BigM);
    				}
    			}
    		}
    		for(int p=0;p<P;p++){
    			num_expr = cplex.linearNumExpr();
    			num_expr.addTerm(1.0, b[p][14][0]);
    			
    			cplex.addEq(num_expr, 1);
    		}
    		for(int p=0;p<P;p++){
    			num_expr = cplex.linearNumExpr();
    			num_expr.addTerm(1.0, h[p][0]);
    			
    			cplex.addEq(num_expr, 0);        			        			
    		}
    		   } catch(IloException e){
       			e.printStackTrace();}
          
           }
          
    	   public void solve() {
    		   try{          		   
           		cplex.exportModel("HeuristicProb.lp"); 
           		if(cplex.solve()==true){
           			System.out.println("sub problem solved");
           		}else{
           			System.out.println("sub problem failed");
           		}			   				    
				    for(int p=0;p<P;p++){
				    	for(int i:AllCellIndex){
				    		for(int t=0;t<T_true;t++){
				    			bValue[p][i][t]=cplex.getValue(b[p][i][t]);	
				    			/*if(bValue[p][i][t]>0.99&&bValue[p][i][t]<1.1){
									System.out.println("b."+p+"."+i+"."+t+"."+":"+bValue[p][i][t]);
								}*/
				    			
				    		}
				    	}
				    }
				    for(int t=0;t<T_true;t++){
				    	for(int p=0;p<P;p++){
				    		hValue[p][t]=cplex.getValue(h[p][t]);
				    		//System.out.println("h."+p+"."+t+":"+""+hValue[p][t]);
				    		uValue[p][t]=cplex.getValue(u[p][t]);
				    		//System.out.println("u."+p+"."+t+":"+""+uValue[p][t]);
				    	}
				    }
           	}catch(IloException e){
       			e.printStackTrace();}
    	   }
       }
       public void runHeuristic(){
    	   Masterproblem b = new Masterproblem();
    	   heuristicModel a = new heuristicModel();
    	   a.solve();
    	   for(int p=0;p<P;p++){
		    	for(int t=0;t<T_true;t++){
		    		for(int i:AllCellIndex){		    			
		    			if(bValue[p][i][t]>0.99&&bValue[p][i][t]<1.1){
							System.out.println("b."+p+"."+i+"."+t+"."+":"+bValue[p][i][t]);
						}
		    			
		    		}
		    	}
		    }
       }
       public void testH()throws Exception{
    	   File result = new File("result.xls");
    	   WritableWorkbook myresult = Workbook.createWorkbook(result);    	
    	   WritableSheet mysheet =  myresult.createSheet("result1", 0);
    	   Label l = new Label(1,0," 0");
    	   Label l1 = new Label(2,0,"1");
    	   mysheet.addCell(l);
    	   mysheet.addCell(l1);
    	   
    	   Masterproblem a1= new Masterproblem();
    	   for(int i:SourceCellIndex){
    		   for(int t=0;t<T_true;t++){
    			   Label s = new Label(i+1,t+1,""+u1Value[i][t]);
    			   mysheet.addCell(s);
	               
    		        }
            }
    	   for(int t=0;t<T_true;t++){
    		   Label s = new Label(0,t+1,""+t);
    		   mysheet.addCell(s);
    	   }
    	   myresult.write();
           myresult.close();
       }
       public void RouteGenerate(int p){
    	   time=0;
    	   timeP=0;
    	   S=16;
    	   for(int i:AllCellIndex){
      		  for(int t=0;t<T_true;t++){
      			  bDummy[i][t]=0;
      		  }
      	  }    	  
    	   //Masterproblem a   = new Masterproblem();
    	   for(int i:SourceCellIndex){
        	   for(int t=0;t<T_true;t++){
        		   u1ValueC[i][t]=u1ValueC[i][t]+u1Value[i][t];
        		   //System.out.println("u."+i+"."+t+"is "+u1ValueC[i][t]);
        	      }
        	   }
    	 while(timeP<T_true){
    		 //System.out.println("time is."+time);    	   
    	   Map<Integer,Double> dual = new HashMap<Integer,Double>();
    	   for(int i:SourceCellIndex){
    		   dual.put(i,u1ValueC[i][time+C[S][i]]);
    	   }
    	   double maxdual =Integer.MIN_VALUE;
    	   for(int i:SourceCellIndex){
    		   if(dual.get(i)>maxdual){
    			   maxdual = dual.get(i);
    			   Destination=i;
    		   }
    	   }
    	   //System.out.println("max"+maxdual);
    	   if(maxdual<=3){
    		   //System.out.println("break at time."+time);
    		   timeP=timeP+10;
    		   break;
    	   }	   
    	   setPath(S,Destination,time);
    	   /*for(int t=0;t<=time;t++){
			   for(int i:AllCellIndex){
				   if(bDummy[0][i][t]>0.99 && bDummy[0][i][t]<1.01){
			            System.out.println("b0."+i+"."+t+".is "+bDummy[0][i][t]);
			 
				   }
		        }
		   }*/
    	   //System.out.println("Destination is."+Destination+"time is."+time);
    	  }
    		  for(int t=time;t<T_true;t++){
    			  bDummy[S][t]=1;
    		  }
    	  
    	    	
       }
       public void recordB(double a[][],int k){
    	   for(int i:AllCellIndex){
    		   for(int t=0;t<T_true;t++){
    			   bValue[k][i][t]=a[i][t];
    		   }
    	   }
    	   for(int i:AllCellIndex){
    		   for(int t=0;t<T_true-1;t++){
    			   if(bValue[k][i][t]-bValue[k][i][t+1]==1){
    				   LValue[k][i][t+1]=1;
    			   }else{LValue[k][i][t+1]=0;}
    			   if(bValue[k][i][t+1]-bValue[k][i][t]==1){
    				   EValue[k][i][t+1]=1;
    			   }else{LValue[k][i][t+1]=0;}
    			   
    		   }
    	   }
    	   for(int t=1;t<T_true;t++){
    		   double R=0;
    		   double S=0;
    	       for(int i:SourceCellIndex){
    		      R=R+bValue[k][i][t];
    		       
    	           }
    	       for(int i:SinkCellIndex){
    	    	 S=S+bValue[k][i][t];
    	       }
    	       if(R==1){
    	    	   hValue[k][t]=hValue[k][t-1]+1;    	    	   
    	       }else if(S==1){
    	    	   hValue[k][t]=0;
    	       }else{
    	    	   hValue[k][t]=hValue[k][t-1];
    	       }
    	       //System.out.println("h ."+k+"."+t+"is" + hValue[k][t]);
    	   }
    	   
    	  
       }
       public class primalS{
    	   private  IloCplex cplex;
    	   private IloLinearNumExpr obj;
    	   private IloLinearNumExpr num_expr;
    	   private IloNumVar x[][];
    	   private IloNumVar y[][][];  
    	     public primalS(){
    	    	 x = new IloNumVar[Cell_Num][T_true];
    	    	 y = new IloNumVar[Cell_Num][Cell_Num][T_true];    	    	
    	    	 CreatModel();
    	    	 solve();
    	     }
         public void CreatModel(){

    	    	 try{
               		cplex = new IloCplex();
               		for(int i:AllCellIndex){
               			for(int t=0;t<T_true;t++){
               				x[i][t] = cplex.numVar(0, Double.MAX_VALUE );
               				x[i][t].setName("x."+i+"."+t);               				
               			}
               		}
               		for(int i:AllCellIndex){
               			for(int j:AllCellIndex){
               			    for(int t=0;t<T_true;t++){
               			    	y[i][j][t] = cplex.numVar(0,Double.MAX_VALUE);
               			    	y[i][j][t].setName("y."+i+"."+j+"."+t);               			    }        				
               			}
               		}            
/**
 * object function               		
 */
            		
               		obj = cplex.linearNumExpr();
               		for(int t=0;t<T_true;t++){
               			for(int i:SourceCellIndex){
               				obj.addTerm(1.0, x[i][t]);
               			}
               			for(int i:IntermediateCellIndex){
               				obj.addTerm(1.0, x[i][t]);
               			}
               		}
               		cplex.addMinimize(obj);               		                           		
/**
 * constraints               		
 */
            	
               		for(int i:SourceCellIndex){
               			for(int t=1;t<T_true;t++){
               				num_expr = cplex.linearNumExpr();
               				num_expr.addTerm(1.0, x[i][t]);
               				num_expr.addTerm(-1.0,x[i][t-1]);
               				for(int j: all_cell.get(i).getSucessor()){
               					num_expr.addTerm(1.0, y[i][j][t-1]);
               				}
               				for(int k:all_cell.get(i).getPredecessor()){
               					num_expr.addTerm(-1.0,y[k][i][t-1]);
               				}
               				double temp = d[i][t-1];
               				for(int p=0;p<P;p++){
               					temp = temp - bValue[p][i][t-1];
               				}
               				cplex.addEq(num_expr, temp);
               				
               			
               			}
               		}
               		
               		for(int i:IntermediateCellIndex){
               			for(int t=1;t<T_true;t++){
               				num_expr = cplex.linearNumExpr();
               				num_expr.addTerm(1.0, x[i][t]);
               				num_expr.addTerm(-1.0,x[i][t-1]);
               				for(int j: all_cell.get(i).getSucessor()){
               					num_expr.addTerm(1.0, y[i][j][t-1]);
               				}
               				for(int k:all_cell.get(i).getPredecessor()){
               					num_expr.addTerm(-1.0,y[k][i][t-1]);
               				}
               				cplex.addEq(num_expr, 0);
               				
               			
               			}
               		}
               		
               		for(int i:SinkCellIndex){
               			for(int t=1;t<T_true;t++){
               				num_expr = cplex.linearNumExpr();
               				num_expr.addTerm(1.0, x[i][t]);
               				num_expr.addTerm(-1.0,x[i][t-1]);
               				for(int j: all_cell.get(i).getSucessor()){
               					num_expr.addTerm(1.0, y[i][j][t-1]);
               				}
               				for(int k:all_cell.get(i).getPredecessor()){
               					num_expr.addTerm(-1.0,y[k][i][t-1]);
               				}
               				double temp = 0;
               				for(int p=0;p<P;p++){
               					temp = temp + bValue[p][i][t-1];
               				}
               				cplex.addEq(num_expr, temp);
               				
               			
               			}
               		}
               		
               		for(int i:AllCellIndex){
               			for(int t=0;t<T_true;t++){
               				num_expr = cplex.linearNumExpr();
               				for(int j : all_cell.get(i).getSucessor()){
               					num_expr.addTerm(1.0,y[i][j][t]);
               				}
               				num_expr.addTerm(-1.0,x[i][t]);
               				cplex.addLe(num_expr, 0);
               			}
               		}
               		
               		for(int i:AllCellIndex){
               			for(int t=0;t<T_true-1;t++){
               				num_expr = cplex.linearNumExpr();
               				
               				for(int j : all_cell.get(i).getSucessor()){
               					num_expr.addTerm(1.0,y[i][j][t]);
               				}
               				double temp = all_cell.get(i).getFlow();
               				for(int p=0;p<P;p++){
               					temp = temp - LValue[p][i][t+1];
               				}
               				cplex.addLe(num_expr, temp);
               			}
               			
               		}
               		
               		for(int i:AllCellIndex){
               			num_expr = cplex.linearNumExpr();
               			for(int j : all_cell.get(i).getSucessor()){
           					num_expr.addTerm(1.0,y[i][j][T_true-1]);
           				}
               			double temp = all_cell.get(i).getFlow();
               			cplex.addLe(num_expr, temp);
               		}
               		
               		for(int i:AllCellIndex){
               			for(int t=0;t<T_true-1;t++){
               				num_expr = cplex.linearNumExpr();
               				
               				for(int k : all_cell.get(i).getPredecessor()){
               					num_expr.addTerm(1.0,y[k][i][t]);
               				}
               				double temp = all_cell.get(i).getFlow();
               				for(int p=0;p<P;p++){
               					temp = temp - EValue[p][i][t+1];
               				}
               				cplex.addLe(num_expr, temp);
               			}
               			
               		}
               		
               		for(int i:AllCellIndex){
               			num_expr = cplex.linearNumExpr();
               			for(int k : all_cell.get(i).getPredecessor()){
           					num_expr.addTerm(1.0,y[k][i][T_true-1]);
           				}
               			double temp = all_cell.get(i).getFlow();
               			cplex.addLe(num_expr, temp);
               		}
               		
               		for(int i:AllCellIndex){
               			for(int t=0;t<T_true-1;t++){
               				num_expr = cplex.linearNumExpr();
               				for(int k : all_cell.get(i).getPredecessor()){
               					num_expr.addTerm(1.0,y[k][i][t]);
               				}
               				num_expr.addTerm(1.0, x[i][t]);
               				
               				double temp = all_cell.get(i).getCapacity();
               				for(int p=0;p<P;p++){
               					temp = temp - EValue[p][i][t+1];
               				}
               				
               				cplex.addLe(num_expr,temp);
               			}
               		}
               		
               		for(int i:AllCellIndex){
               			num_expr = cplex.linearNumExpr();
               			for(int k : all_cell.get(i).getPredecessor()){
           					num_expr.addTerm(1.0,y[k][i][T_true-1]);
           				}
               			num_expr.addTerm(1.0, x[i][T_true-1]);
               			
               			double temp = all_cell.get(i).getCapacity();
               			cplex.addLe(num_expr,temp);
               		}
               			for(int t=1;t<=T_true-Tau-1;t++){
                  			for(int i:IntermediateCellIndex){
                  				for(int p=0;p<P;p++){
                  				   for(int r=0;r<Tau;r++){
                  					 num_expr = cplex.linearNumExpr();
                  					 num_expr.addTerm(-1.0/all_cell.get(i).getCapacity(), x[i][t]);
                  					 for(int o=0;o<=r;o++){
                  						 for(int u:all_cell.get(i).getSucessor()){
                  							 num_expr.addTerm(1.0/all_cell.get(i).getCapacity(), y[i][u][t+o]);
                  						 }
                  					 }
                  					 double temp = -bValue[p][i][t+r+1]-BigM+BigM*EValue[p][i][t];
                  					 
                  					 cplex.addGe(num_expr,temp);
                  				   }
                  			   }
                  			}
                  		}
                  		for(int t=T_true-Tau;t<T_true-1;t++){
                  			for(int i:IntermediateCellIndex){
                  				for(int p=0;p<P;p++){
                  				   for(int r=0;r<T_true-1-t;r++){
                  					 num_expr = cplex.linearNumExpr();
                  					 num_expr.addTerm(-1.0/all_cell.get(i).getCapacity(), x[i][t]);
                  					 for(int o=0;o<=r;o++){
                  						 for(int u:all_cell.get(i).getSucessor()){
                  							 num_expr.addTerm(1.0/all_cell.get(i).getCapacity(), y[i][u][t+o]);
                  						 }
                  					 }
                  					 double temp = -bValue[p][i][t+r+1]-BigM+BigM*EValue[p][i][t];
                  					 
                  					 cplex.addGe(num_expr,temp);
                  				   }
                  			   }
                  			}
                  		}
            		
                  		for(int i:AllCellIndex){
                  			num_expr = cplex.linearNumExpr();
                  			num_expr.addTerm(1.0,x[i][0]);
                  			cplex.addEq(num_expr,0);
                  		}
                  		for(int i:AllCellIndex){
                  			for(int j:AllCellIndex){
                  				num_expr = cplex.linearNumExpr();
                  				num_expr.addTerm(1.0,y[i][j][0]);
                  				cplex.addEq(num_expr,0);
                  			}
                  		}
    	    	 }catch (IloException e) {
       				System.err.println("Concert exception caught: " + e);}
       				
       			}
    	 public void solve(){
    	        	 try{
    	        		 cplex.exportModel("primalProb.lp");  
    					    cplex.solve();
    						FinalResult=cplex.getObjValue();
    						/*
    						 for(int t=0;t<T_true;t++){
    							 for(int i:AllCellIndex){
    								 System.out.println("x."+i+"."+t+":"+cplex.getValue(x[i][t]));
    							 }
    						 }
    						 for(int t=0;t<T_true;t++){
    							 for(int i:AllCellIndex){
    								 for(int j:all_cell.get(i).getSucessor()){
    									 if(cplex.getValue(y[i][j][t])>0){
    										 System.out.println("y."+i+"."+j+"."+t+":"+cplex.getValue(y[i][j][t]));
    									 }
    								 }
    							 }
    						 }*/
    						for(int p=0;p<P;p++){
    							for(int t=0;t<T_true;t++){
    								FinalResult = FinalResult + hValue[p][t]; 
    							}
    						}
    						
    						}catch(IloException e){
    		        			e.printStackTrace();}
    	         }
       }
       public class SubProblemH{
    	   private  IloCplex cplex;
           private IloIntVar Z;
           private IloLinearNumExpr primal_obj;
           private IloLinearNumExpr num_expr;
    	   public SubProblemH(){
    		   creatModel();
    		   addBound();
    		   solve();
    	   }
    	   public void creatModel(){
    		   try{    			  
       			cplex= new IloCplex();
       			Z=cplex.intVar(-Integer.MAX_VALUE, Integer.MAX_VALUE);
            	Z.setName("Z");
        		primal_obj = cplex.linearNumExpr();
        		primal_obj.addTerm(1, Z);
        		cplex.addMinimize(primal_obj);
    		   }catch(IloException e){
       			e.printStackTrace();
       		}
    	   }
    	   public void addBound(){
    		   try{           		           		
    			   for(int k=0;k<=IterationH;k++){
    			   num_expr = cplex.linearNumExpr();
            		num_expr.addTerm(1.0, Z);
            		
            		double RHS =0;
            		for(int t=0;t<T_true;t++){
             			for(int p=0;p<P;p++){
             				RHS = RHS+hValue[p][t];
             			}
             		}         		
            		for(int t=1;t<T_true;t++){
            			for(int i:SourceCellIndex){
            				RHS = RHS +u1Set[i][t][k]*d[i][t-1];
            				for(int p=0;p<P;p++){
            					RHS = RHS - u1Set[i][t][k]*bValue[p][i][t-1];
            				}
            			}
            			for(int i:SinkCellIndex){
            				for(int p=0;p<P;p++){
            					RHS = RHS +u1Set[i][t][k]*bValue[p][i][t-1];
            				}
            			}
            		}	
            		for(int t=0;t<T_true;t++){
            			for(int i:AllCellIndex){
            				RHS = RHS - u3Set[i][t][k]*all_cell.get(i).getFlow();
            				RHS = RHS - u4Set[i][t][k]*all_cell.get(i).getFlow();
            				//RHS = RHS + u5Value[i][t]*all_cell.get(i).getCapacity();         			
            			}
            		}
            		for(int t=0;t<T_true-1;t++)
            			for(int i:AllCellIndex){
            				for(int p=0;p<P;p++){
            					RHS = RHS + u3Set[i][t][k]*LValue[p][i][t+1];
            					RHS = RHS + u4Set[i][t][k]*EValue[p][i][t+1];
            				}
            		}
            		for(int t=0;t<T_true;t++){
            			for(int i:AllCellIndex){         				        			
            			RHS = RHS - u5Set[i][t][k]*all_cell.get(i).getCapacity();
            			
            		    }
            		}/*
            		for(int i:AllCellIndex){
            			for(int t=0;t<T_true;t++){
            				System.out.println(i+"."+t+"is"+u5Set[i][t][k]);
            			}
            		}*/
            		for(int t=0;t<T_true-1;t++){
            			for(int i:AllCellIndex){
            				for(int p=0;p<P;p++){
            					RHS = RHS +u5Set[i][t][k]*EValue[p][i][t];
            				}
            			}
            		}
            		for(int t=1;t<=T_true-Tau-1;t++){
            		    for(int i:IntermediateCellIndex){
            				for(int p=0;p<P;p++){
            					for(int r=0;r<Tau;r++){
            						RHS = RHS -u6Set[p][i][t][r][k]*BigM;
            						RHS = RHS -u6Set[p][i][t][r][k]*bValue[p][i][t+r+1];
            						RHS = RHS +u6Set[p][i][t][r][k]*BigM*EValue[p][i][t];
            					}
            				}
            			}         		         			
            		}
            		for(int t=T_true-Tau;t<T_true-1;t++){
            		    for(int i:IntermediateCellIndex){
            				for(int p=0;p<P;p++){
            					for(int r=0;r<T_true-t-1;r++){
            						RHS = RHS -u6Set[p][i][t][r][k]*BigM;
            						RHS = RHS -u6Set[p][i][t][r][k]*bValue[p][i][t+r+1];
            						RHS = RHS +u6Set[p][i][t][r][k]*BigM*EValue[p][i][t];
            					}
            				}
            			}         		         			
            		}            	
            		cplex.addGe(num_expr, RHS);
                 }
    		   }
           	catch(IloException e){
       			e.printStackTrace();}
    	   }
    	   public void solve(){
    		   try{cplex.exportModel("SubProblem1.lp"); 
       		     if(cplex.solve()==true){
    			      System.out.println("sub problem solved");
    		      }else{
    			      System.out.println("sub problem failed");
    		     }		       
		         objPrimalValue=cplex.getObjValue();
		         //System.out.println("ObjPrimalValue"+objPrimalValue);
    			   
    		   }
    		   catch(IloException e){
    			   e.printStackTrace();
    		   }
    	   }
    	   public void runbender(){
    		   addBound();
    		   solve();
    	   }
       }
       public void runHeuristicBD(){
    	   
    	   IterationH=0;
    	   InitiateY();
    	   Masterproblem pre   = new Masterproblem();  
    	   ParetoOptimalCut paretocut = new ParetoOptimalCut();//presolve dual value once then start iteration
    	   	   
    	   while(IterationH<iterationT){
    		   if(IterationH<P){
    		   saveDual(IterationH);
    		   RouteGenerate(IterationH);
    		   recordB(bDummy,IterationH);
    		   SubProblemH pres = new SubProblemH(); 
        	   
        		   UB = objPrimalValue;    		   
        	   
        	   System.out.println("UB IS"+UB);
    	   
           Masterproblem sloving  = new Masterproblem();
           ParetoOptimalCut paretocut1 = new ParetoOptimalCut();
             	
    	   LB=objDualValue;   		      	   
    	   System.out.println("LB IS"+LB);
    	   
    	   IterationH = IterationH +1;
    	   
    	  
    	   }
    	   else if(IterationH >=P){
    		   saveDual(IterationH);
    		   int busK = IterationH % P;
    		   System.out.println("k is."+busK);
    		   RouteGenerate(busK);
    		   recordB(bDummy,busK);
    		   SubProblemH pres = new SubProblemH(); 
        	   
        		   UB = objPrimalValue;    		   
        	   
        	   System.out.println("UB IS"+UB);
    	   
           Masterproblem sloving  = new Masterproblem();
           ParetoOptimalCut paretocut1 = new ParetoOptimalCut(); 
    	   LB=objDualValue;   		      	   
    	   System.out.println("LB IS"+LB);    	 
    	   
    	   IterationH = IterationH +1;
    	  
    	  
    	   }
    	   }
    	   //output
    	   /*
    	   for(int p=0;p<P;p++){
    		   for(int t=0;t<T_true;t++){
    			   for(int i:AllCellIndex){
    				   if(bValue[p][i][t]>0.99 && bValue[p][i][t]<1.01){
    					   System.out.println("b."+p+"."+i+"."+t+"is equal to 1");
    				   }
    			   }
    		   }
    	   }*/
       }
     
       public void setPath(int i,int j,int t){
    	   
    	   if(j==0 && i==16){
    		  bDummy[16][t]=1;
    		  bDummy[13][t+1]=1;
    		  bDummy[10][t+2]=1;
    		  bDummy[0][t+3]=1;
    		  bDummy[0][t+4]=1;
    		  bDummy[0][t+5]=1;
    		  bDummy[3][t+6]=1;
    		  bDummy[6][t+7]=1;
    		  bDummy[9][t+8]=1;
    		  bDummy[9][t+9]=1;
    		  bDummy[9][t+10]=1;
    		  S= 9;
    		  timeP = timeP + 10;
    		  if(timeP<=T_true){
    			  time = time +10;
    		  }
    	   }
    	   else if(j==1 && i==16 ){
    		   bDummy[16][t]=1;
     		  bDummy[13][t+1]=1;
     		  bDummy[10][t+2]=1;
     		  bDummy[0][t+3]=1;     		 
     		  bDummy[3][t+4]=1;
     		  bDummy[6][t+5]=1;
     		  bDummy[9][t+6]=1;
     		  bDummy[14][t+7]=1;
     		  bDummy[11][t+8]=1;
     		  bDummy[1][t+9]=1;
     		  bDummy[1][t+10]=1;
     		  bDummy[1][t+11]=1;
     		  bDummy[4][t+12]=1;
     		  bDummy[7][t+13]=1;
     		  bDummy[9][t+14]=1;
     		  bDummy[9][t+15]=1;
     		  bDummy[9][t+16]=1;
     		  S = 9;
     		  timeP = timeP + 16;
     		  if(timeP<=T_true){
     			  time = time +16;
     		  }
     	   }
    	   else if(j==0 && i == 9){
    		   bDummy[9][t]=1;
    		   bDummy[14][t+1]=1;
    		   bDummy[11][t+2]=1;
    		   bDummy[0][t+3]=1;
    		   bDummy[0][t+4]=1;
    		   bDummy[0][t+5]=1;
    		   bDummy[3][t+6]=1;
    		   bDummy[6][t+7]=1;
    		   bDummy[9][t+8]=1;
    		   bDummy[9][t+9]=1;
      		   bDummy[9][t+10]=1;
      		   S = 9;
      		   timeP = timeP +10;
      		   if(timeP<=T_true){
      			   time=time+10;
      		   }
    	   }
    	   else if(j==1 && i==9){
    		   bDummy[9][t]=1;
    		   bDummy[15][t+1]=1;
    		   bDummy[12][t+2]=1;
    		   bDummy[1][t+3]=1;
    		   bDummy[1][t+4]=1;
    		   bDummy[1][t+5]=1;
    		   bDummy[4][t+6]=1;
    		   bDummy[7][t+7]=1;
    		   bDummy[9][t+8]=1;
    		   bDummy[9][t+9]=1;
      		   bDummy[9][t+10]=1;
      		   S = 9;
      		   timeP = timeP +10;
      		   if(timeP<=T_true){
      			   time = time +10;
      		   }
    	   }
    	   

       }
       public void saveDual(int k){
    	   for(int t=0;t<T_true;t++){
    		   for(int i :AllCellIndex){
    			   u1Set[i][t][k]=u1Value[i][t];
    			   u2Set[i][t][k]=u2Value[i][t];
    			   u3Set[i][t][k]=u3Value[i][t];
    			   u4Set[i][t][k]=u4Value[i][t];
    			   u5Set[i][t][k]=u5Value[i][t];
    			   for(int p=0;p<P;p++){
    				   for(int c=0;c<Tau;c++){
    					   u6Set[p][i][t][c][k]=u6Value[p][i][t][c];
    				   }
    			   }
    		   }
    	   }
       }
       public void testHroute() throws Exception{
    	   RouteGenerate(0);
    	   
      	       for(int t=0;t<T_true;t++){
    			   for(int i:AllCellIndex){
    				   if(bDummy[i][t]>0.99 && bDummy[i][t]<1.01){
    			            System.out.println("b0."+i+"."+t+".is "+bDummy[i][t]);
    			 
    				   }
    		        }
    		   }
         
    	   
       }
       
}