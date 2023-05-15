import cplex
import docplex
from docplex.mp.model import Model
import docplex.mp.conflict_refiner as cr
import numpy as np
import pandas as pd
import collections.abc
from IPython.display import display
N_num = 5
T_num = 40
P_num = 1
Lrate=3
cp = 12 #bus capacity
BM = 200 # BigM
demand_num = 30
demand = [[0]*T_num,0*T_num,[demand_num]+[0]*(T_num-1),[demand_num]+[0]*(T_num-1), [0]*T_num]
#print(demand)
node = [0,1,2,3,4]; nodess = [2,3]; nodesk=[0]; nodeim=[1,4]
qcap= [3,3,6,6,12] #inflow capacity
Incap = 20 #intermediate cell capacity
ncap = [BM, Incap, BM, BM, Incap] #cell capacity
prenode=[[4],[0],[1],[1],[2,3]]
scusnode=[[1],[2,3],[4],[4],[0]]


for i in nodess:
    for j in scusnode[i]:
        print(j)


time = [i for i in range(0,T_num)]
bus = [i for i in range(0,P_num)]
print('Docplex version:', '.'.join(map(str, docplex.mp.__version_info__)))
print('CPLEX version:', cplex.Cplex().get_version())
class evamodel:

    def __init__(self):
        self.mdl = Model()
        self.x = self.mdl.continuous_var_dict([(i,k) for i in node for k in time], name='x')
        self.y = self.mdl.continuous_var_dict([(i,j,k) for i in node for j in node for k in time], name='y')
        self.b = self.mdl.binary_var_dict([(p,i,k) for p in bus for i in node for k in time], name='b')
        self.e = self.mdl.binary_var_dict([(p,i,k) for p in bus for i in node for k in time], name='e')
        self.l = self.mdl.binary_var_dict([(p,i,k) for p in bus for i in node for k in time], name='l')
        self.h = self.mdl.continuous_var_dict([(p,k) for p in bus for k in time], name='h')
        self.xval_list = np.zeros(shape=(N_num,T_num))
        self.yval_list = np.zeros(shape=(N_num,N_num,T_num))
        self.bval_list = np.zeros(shape=(P_num,N_num,T_num))
    def model(self):

        self.mdl.minimize(self.mdl.sum(self.mdl.sum(self.x[i, k] for i in nodess+nodeim)
        + Lrate*(self.mdl.sum(self.b[p, i, t] for i in nodess for p in bus for t in range(0, k)) - self.mdl.sum(self.b[p, i, t] for i in nodesk for p in bus for t in range(0, k)))
        -self.mdl.sum(self.h[p,k] for p in bus) for k in time))
        self.mdl.add_constraints(self.x[i,t]-self.x[i,t-1]+self.mdl.sum(self.y[i,j,t-1] for j in scusnode[i])-self.mdl.sum(self.y[k,i,t-1] for k in prenode[i])-demand[i][t-1]+Lrate*self.mdl.sum(self.b[p,i,t-1] for p in bus) == 0for i in nodess for t in range(1,T_num))
        self.mdl.add_constraints(self.x[i,t]-self.x[i,t-1]+self.mdl.sum(self.y[i,j,t-1] for j in scusnode[i])-self.mdl.sum(self.y[k,i,t-1] for k in prenode[i]) == 0 for i in nodeim for t in range(1,T_num))
        self.mdl.add_constraints(self.x[i,t]-self.x[i,t-1]+self.mdl.sum(self.y[i,j,t-1] for j in scusnode[i])-self.mdl.sum(self.y[k,i,t-1] for k in prenode[i])-Lrate*self.mdl.sum(self.b[p,i,t-1] for p in bus) == 0 for i in nodesk for t in range(1,T_num))
        self.mdl.add_constraints(self.mdl.sum(self.y[i,j,t] for j in scusnode[i])-self.x[i,t] <= 0 for i in node for t in time)
        self.mdl.add_constraints(self.mdl.sum(self.y[i,j,t] for j in scusnode[i]) + self.mdl.sum(self.l[p,i,t+1] for p in bus) - qcap[i] <=0 for i in node for t in range(0,T_num-1))
        self.mdl.add_constraints(self.mdl.sum(self.y[k,i,t] for k in prenode[i]) + self.mdl.sum(self.e[p,i,t+1] for p in bus) - qcap[i] <=0 for i in node for t in range(0,T_num-1))
        self.mdl.add_constraints(self.mdl.sum(self.y[k,i,t] for k in prenode[i]) + self.mdl.sum(self.e[p,i,t+1] for p in bus) - ncap[i]+self.x[i,t] + self.mdl.sum(self.b[p,i,t+1] for p in bus) <=0 for i in node for t in range(0,T_num-1))
        self.mdl.add_constraints(self.mdl.sum(self.b[p,i,t] for i in node) == 1 for p in bus for t in time)
        self.mdl.add_constraints(self.e[p,i,t] - self.b[p,i,t] + self.b[p,i,t-1] >= 0 for p in bus for i in node for t in range(1,T_num))
        self.mdl.add_constraints(self.l[p,i,t] - self.b[p,i,t-1] + self.b[p,i,t] >= 0 for p in bus for i in node for t in range(1,T_num))
        #self.mdl.add_constraints(0 <= Lrate*self.mdl.sum(self.b[p,i,k] for k in range(0,t) for i in nodess) - Lrate*self.mdl.sum(self.b[p,i,k] for k in range(0,t) for i in nodesk) <= cp for p in bus for t in time)
        self.mdl.add_constraints(Lrate*self.mdl.sum(self.b[p,i,k] for k in range(0,t) for i in nodess) - Lrate*self.mdl.sum(self.b[p,i,k] for k in range(0,t) for i in nodesk) >=0 for p in bus for t in range(1,T_num))
        self.mdl.add_constraints(Lrate*self.mdl.sum(self.b[p,i,k] for k in range(0,t) for i in nodess) - Lrate*self.mdl.sum(self.b[p,i,k] for k in range(0,t) for i in nodesk) <= cp for p in bus for t in range(1,T_num))
        self.mdl.add_constraints(self.mdl.sum(self.b[p,j,t] for j in scusnode[i]) - self.b[p,i,t-1] + self.b[p,i,t] >= 0 for p in bus for i in node for t in range(1,T_num))
        for t in range(0, T_num):
            for tau in range(0,3):
                if t+tau <T_num:
                    for i in nodeim:
                        for p in bus :
                            self.mdl.add_constraint(self.b[p,i,t+tau] - (self.x[i,t]-self.mdl.sum(self.y[i,j,t+k] for j in scusnode[i] for k in range(0,tau)))/ncap[i] + 1 - self.e[p,i,t] >=0)
        self.mdl.add_constraints(self.h[p,t] >= 0 for p in bus for t in time)
        self.mdl.add_constraints(self.h[p,t] - Lrate*self.mdl.sum(self.b[p,i,k] for i in nodess for k in range(0,t)) + Lrate*self.mdl.sum(self.b[p,i,k] for i in nodesk for k in range(0,t)) <=0 for p in bus for t in time)
        self.mdl.add_constraints(self.h[p,t] <= BM*self.mdl.sum(self.b[p,i,t] for i in nodesk) for p in bus for t in time)

        self.mdl.add_constraints(self.b[p,1,0] ==1 for p in bus)
        self.mdl.export_as_lp("bus_evacuation_model")
        solution = self.mdl.solve(log_output=True)
        #print(self.mdl.solve_details)
        #print(solution)
        solve_status = self.mdl.get_solve_status()
        if solve_status.name == 'INFEASIBLE_SOLUTION':
            cref = cr.ConflictRefiner()
            conflicts = cref.refine_conflict(self.mdl)
            for c in conflicts:
                print('infeasible info: ', c)

            #conflict = self.mdl.cplex_conflict
        else:
            for t in time:
                for i in node:
                    self.xval_list[i][t] =self.x[i,t].solution_value
                    for j in node:
                        if j in scusnode[i]:
                            self.yval_list[i][j][t] = self.y[i,j,t].solution_value
                    for p in bus:
                        self.bval_list[p][i][t] = self.b[p,i,t].solution_value
        self.mdl.end()
    def visual(self):
        #print(self.yval_list)
        #print(self.yval_list)
        table = pd.DataFrame()

        for i in range(len(self.xval_list)):
            for k in range(len(self.xval_list[i])):
                table.loc[k, f'x{i}'] = self.xval_list[i][k]
        for i in range(len(self.yval_list)):
            for j in range(len(self.yval_list[i])):
                if j in scusnode[i]:
                    for k in range(len(self.yval_list[i][j])):
                        table.loc[k, f'y({i},{j})'] = self.yval_list[i][j][k]
        for p in range(len(self.bval_list)):
            for k in range(len(self.bval_list[p][0])):
                for i in range(len(self.bval_list[p])):
                    if self.bval_list[p][i][k] >=0.99:
                        table.loc[k, f'b{p}'] = i

        table.to_csv('./{demand}demand_{busnum}bus_{time}time.csv'.format(demand='30', busnum=str(P_num), time = T_num))




def main():
    m1 = evamodel()
    m1.model()
    m1.visual()


if __name__ == "__main__":
    print("Hello World")
    main()
