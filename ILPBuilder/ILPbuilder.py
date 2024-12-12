from pulp import CPLEX_CMD, getSolver, LpVariable, LpMinimize, LpProblem, lpSum, lpDot
import re
import sys
import os.path
# print(analysis_start)

def get_computation_cost(block):
    cost =  block.count('*')
    return  cost

def get_analysis_results(filename):
    with open(filename) as f:
        lines = f.readlines()

    cut_cost = []
    computation_cost = []

    cost_analysis_report = []

    analysis_start = lines.index("Analysis started\n")
    for i in range(analysis_start + 1, len(lines)):
        x = re.split(', |:|\t|\n|,|,  |:\n ', lines[i])
        in_pos = 0;
        out_pos = 0;

        for e in x:
            if len(e) == 0:
                x.remove(e)
        # print(x)
        for e in x:
            if e == 'in':
                in_pos = x.index(e)
            if e == 'out':
                out_pos = x.index(e)

        computation_cost.append(get_computation_cost(x[0]))
        cut_cost.append(len(x) - out_pos - 1)

    return computation_cost, cut_cost

def parse_input(input_name):
    comput_costs = []
    cut_costs = []
    noc = 1
    with open(input_name, "r") as f:
        # raw_n = f.readline()
        raw_comput_costs = f.readline().split(' ')
        raw_cut_costs = f.readline().split(' ')
        raw_noc = f.readline()
        # n = int(raw_n)
        comput_costs = [int(raw) for raw in raw_comput_costs]
        cut_costs = [int(raw) for raw in raw_cut_costs]
        noc = int(raw_noc)
    return comput_costs, cut_costs, noc

def find_best_cut(computation_cost_info, cut_cost_info, noc):
    assert (noc > 1)
    prob = LpProblem(name="circuit-cut-problem", sense= LpMinimize)
    nob  = len(computation_cost_info)
    assert (len(cut_cost_info) == nob)
    assert (noc -1 < nob)
    noc += 1

    cut_point = {i: LpVariable(name="cut_point" + str(i) , lowBound=1, cat='Integer') for i in range(1, noc)}
    cut_point_cost = {i: LpVariable(name="cut_point_cost" + str(i), lowBound=0, cat='Integer') for i in range(1, noc)}
    x = {i: {j: LpVariable(name="x" + str(i) + "_" + str(j), lowBound=0, cat='Binary') for j in range(nob)} for i in range(noc)}
    x_diff = {i: {j: LpVariable(name="x_diff" + str(i) + "_" + str(j), lowBound=0, cat='Binary') for j in range(nob)} for i in range(1, noc)}
    y = {i: {j: LpVariable(name="y" + str(i) + "_" + str(j), lowBound=0, cat='Binary') for j in range(nob)} for i in range(noc)}
    x_y_diff = {i: {j: LpVariable(name="x_y_diff" + str(i) + "_" + str(j), lowBound=0, cat='Binary') for j in range(nob)} for i in range(noc)}

    cost_cut = LpVariable(name="cost_cut", lowBound=0, cat='Integer')
    cost_ops = LpVariable(name="cost_ops", lowBound=0, cat='Integer')

    for j in range(0, nob):
        prob += (x[0][j] == 0, "x_0_" + str(j))
        prob += (y[0][j] == 0, "y_0_" + str(j))

    for i in range(0, noc):
        if i > 1:
            prob += (cut_point[i] >= cut_point[i-1] + 1, "increment_cut_" + str(i))
        if i > 0:
            prob += (lpDot([x[i][j] for j in range(nob)], [1 for j in range(nob)] )== cut_point[i], "x_constraint_" + str(i))
            prob += (lpDot([y[i][j] for j in range(nob)], [1 for j in range(nob)]) == cut_point[i] - 1, "y_constraint_" + str(i))
            prob += (lpDot(computation_cost_info, [x_diff[i][j] for j in range(nob)]) <= cost_ops, "ops_cost_define_" + str(i))
            prob += (lpDot(cut_cost_info, [x_y_diff[i][j] for j in range(nob)]) == cut_point_cost[i], "cut_cost_define_" + str(i))
        for j in range(1, nob):
            prob += (x[i][j] <= x[i][j-1], "x_constraint_" + str(i) + str(j))
            prob += (y[i][j] <= y[i][j-1], "y_constraint_" + str(i) + str(j))
        for j in range(nob):
            if i > 0:
                prob += (x_diff[i][j] == (x[i][j] - x[i-1][j]),  "x_diff_" + str(i)+  str(j))
            prob += (x_y_diff[i][j] == (x[i][j] - y[i][j]),  "x_y_diff_" + str(i)+  str(j))


    prob += (lpSum(cut_point_cost) == cost_cut, "cut_cost_define")
    prob += (cut_point[i] == nob, "last_vector_define")
    prob += (cost_cut + cost_ops)

    path = "/opt/ibm/ILOG/CPLEX_Studio221/cplex/bin/x86-64_linux/cplex"
    solver = getSolver("PULP_CBC_CMD")
    if os.path.isfile(path):
        solver = CPLEX_CMD(path=path)
        print("SOLVER: Using CPLEX")

    prob.solve(solver)
    if prob.status == 1:
        print("============optimal cut found ============")
        print(computation_cost_info)
        print(cut_cost_info)
        for i in range(1, noc):
            print(cut_point[i].name, cut_point[i].value())
        result = []
        for i in range(1, noc):
            result.append(int(cut_point[i].value()))

        #for i in range(noc):
        #    for j in range(nob):
        #        print(x[i][j].name, x[i][j].value())
        #for i in range(noc):
        #    for j in range(nob):
        #        print(y[i][j].name, y[i][j].value())
        #for i in range(1, noc):
        #    for j in range(nob):
        #        print(x_diff[i][j].name, x_diff[i][j].value())
        #for i in range(noc):
        #    for j in range(nob):
        #        print(x_y_diff[i][j].name, x_y_diff[i][j].value())
        #
        #print(cost_cut.name, cost_cut.value())
        #print(cost_ops.name, cost_ops.value())

        return result

# computation_cost_info, cut_cost_info = [1,1,1,1], [1,1,1,1]
comput_costs, cut_costs, noc = parse_input("/tmp/ILPinput.txt")
result = find_best_cut(comput_costs, cut_costs, noc)
raw_result = [str(cut) for cut in result]
with open("/tmp/ILPresult.txt", "w") as f:
    f.write(' '.join(raw_result))
    f.write('\n')
