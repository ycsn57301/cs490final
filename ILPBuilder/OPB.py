import re
import subprocess
import os
from datetime import datetime

solver = 'gurobi_cl'
input_name = "/tmp/OPBInput.txt"
log_name = "/tmp/OPBlog.txt"
solution_name = "/tmp/cut.sol"
result_name = "/tmp/OPBResult.txt"
tmp_name = "/tmp/tmp.opb"
# cost of operation length (number of bits)
cop_length = 20

def encoding(i, j):
    return str(i) + "_" + str(j)

def get_analysis_results(filename):
    with open(filename) as f:
        lines = f.readlines()

    num_nodes = 0
    num_parts = 0
    edge_info = []
    node_info = []

    meta_info_line_begin = lines.index("meta info\n")
    node_info_line_begin = lines.index("node info\n")
    edge_info_line_begin = lines.index("edge info\n")
    x = re.split(', |:|\t|\n|,|,  |:\n ', lines[meta_info_line_begin+1])

    for e in x:
        if len(e) == 0:
            x.remove(e)
    assert len(x) == 2
    num_nodes = int(x[0])
    num_parts = int(x[1])

    node_info = [0 for i in range(num_nodes)]


    for i in range(node_info_line_begin+1, edge_info_line_begin):
        x = re.split(', |:|\t|\n|,|,  |:\n ', lines[i])
        for e in x:
            if len(e) == 0:
                x.remove(e)
        assert len(x) == 2
        index = int(x[0])
        cost = int(x[1])
        node_info[index] = cost
    for i in range(edge_info_line_begin + 1, len(lines)):

        x = re.split(', |:|\t|\n|,|,  |:\n ', lines[i])
        for e in x:
            if len(e) == 0:
                x.remove(e)
        assert len(x) == 4
        s = int(x[0])
        d = int(x[1])
        c = int(x[2])
        is_cuttable = int(x[3])
        edge_info.append((s,d, c, is_cuttable))

    return  node_info, edge_info, num_nodes, num_parts

def encodeOPB(filename, outputfile, nop):
    f = open(outputfile, "w")

    node_cost, edge_cost, non, pub = get_analysis_results(filename)
    assert len(node_cost) == non
    assert  nop <= pub


    # print header
    #print objective
    goal = "min: "
    for l in range(cop_length):
        goal += "+" + str(2 ** l) + " cop_" + str(l) + " "
    for (i, j, c, is_cuttable) in edge_cost:
        goal += "+"+ str(c) +" y_"+str(i) + "_" + str(j)+ " "
    f.write(goal + ";\n")
    #
    constraint_0= ""

    #each node should be in only one partition
    for i in range(non):
        constraint = ""
        for t in range(nop):
            index = encoding(i, t)
            constraint = constraint + "+1 x_" + str(index) + " "
        constraint = constraint  + "= 1"

        f.write(constraint + " ;"+ "\n")
    # encode edge condition
    for t in range(nop):
        for (i, j, c, is_cuttable) in edge_cost:
            index_i_t = encoding(i, t)
            index_j_t = encoding( j, t)
            index_i_j = encoding( i, j)

            constraint = "+1 x_"+ str(index_i_t) + " +1 x_"+ str(index_j_t)  +  " +1 y_"+  str(index_i_j) + " <= 2"
            f.write(constraint+ " ;"+ "\n")
            constraint = "+1 x_"+ str(index_i_t) + " -1 x_"+ str(index_j_t)  +  " -1 y_"+ str(index_i_j)  + " <= 0"
            f.write(constraint + " ;"+ "\n")
            constraint = "+1 x_" + str(index_i_t) + " -1 x_" + str(index_j_t) + " +1 y_" + str(index_i_j) + " >= 0"
            f.write(constraint + " ;"+ "\n")
    # encode computation cost

    for t in range(nop):
        constraint = ''
        for l in range(cop_length):
            constraint += "+" + str(2**l) + " cop_"+str(l) + " "
        for i in range(non):
            index_i_t = encoding(i, t)
            constraint += "-" + str(node_cost[i])  + " x_"+str(index_i_t) + " "
        constraint += " >= 0"
        f.write(constraint+ " ;"+ "\n")

    for (i, j, c, is_cuttable) in edge_cost:
        constraint = ""
        index = encoding( i, j)
        constraint += "+1" + " y_" + str(index) + " <= " + str(is_cuttable)  + " ;\n"
        # print(constraint)
        f.write(constraint)
    # f.write("+1 x258 <= 2 ;")
    f.close()
    return (node_cost, edge_cost, non, pub)
    # 3* nop * noe + non + nop

def parse_result(filename, node_cost, edge_cost, nop):
    with open(filename) as f:
        lines = f.readlines()
    block = []
    cut = []
    total_cost = 0
    comp_cost = [0] * nop
    cut_cost = 0
    for e in lines:
        if e.startswith("# Objective value ="):
            optimal = re.split(' |_|\n', e)
            total_cost = float(optimal[4])
            print("cost", total_cost)
            assert total_cost > 0
        if str(e).startswith("x_"):
            node_partition = re.split(' |_|\n', e)
            b = round(float(node_partition[3]))
            if b == 1:
                block.append((int(node_partition[1]), int(node_partition[2])))
                comp_cost[int(node_partition[2])] += node_cost[int(node_partition[1])]
        if str(e).startswith("y_"):
            edge_partition = re.split(' |_|\n', e)
            b = round(float(edge_partition[3]))
            if b == 1:
                cut.append((int(edge_partition[1]), int(edge_partition[2])))
                for (i, j, cost, b) in edge_cost:
                    if (int(edge_partition[1]), int(edge_partition[2]) ) == (i, j):
                        cut_cost += cost

    return (block, cut, total_cost, comp_cost, cut_cost)
    # opt = str(optimal[len(optimal)-2])[9:len(optimal[len(optimal)-2])]
#
#
#     return block, cut, comp_cost, cut_cost, int(opt)
#
#

def output_result(result_name, num_parts, blocks):
    # assemble commands that belong to the same part
    parts = [[] for i in range(0, num_parts)]
    for (cmd_id, part_id) in blocks:
        parts[part_id].append(cmd_id)
    print("parts:")
    with open(result_name, "w") as f:
        for part in parts:
            part.sort()
            print(part)
            f.write(" ".join([str(cmd_id) for cmd_id in part]))
            f.write("\n")


start_time = datetime.now()
(node_cost, edge_cost,num_nodes, partition_upper_bound) = encodeOPB(input_name, tmp_name, 1)

cost_before_parallel = 0
for e in node_cost:
    cost_before_parallel += e
total_cost = cost_before_parallel
cop_length = total_cost.bit_length()
print("cop_length =", cop_length)
assert(total_cost > 0)
(block_opt, cut_opt, total_cost_opt,  comp_cost_opt, cut_cost_opt) = ([], [], cost_before_parallel, cost_before_parallel, 0)
print("partition upper bound =", partition_upper_bound)
nop_opt = 1
for i in range(partition_upper_bound, partition_upper_bound+1):
    os.remove(tmp_name)
    (node_cost, edge_cost, num_nodes, nop) = encodeOPB(input_name, tmp_name, i)
    with open(log_name, "w") as f:
        subprocess.call([solver, 'ResultFile='+solution_name, "MIPGap=0.01", "TimeLimit=600", tmp_name], stdout=f)
    (block, cut, total_cost,  comp_cost, cut_cost) = parse_result(solution_name,  node_cost, edge_cost, i)
    er = ((cost_before_parallel))/total_cost
    print(i, er, total_cost)
    if total_cost < total_cost_opt:
        (block_opt, cut_opt, total_cost_opt, comp_cost_opt, cut_cost_opt, nop_opt) = (block, cut, total_cost,  comp_cost, cut_cost, i)
end_time = datetime.now()
time_cost = end_time - start_time
print("Time cost in seconds:", time_cost.total_seconds())

output_result(result_name, partition_upper_bound, block_opt)

print("block partition:\n", block_opt)
print("cut edge: \n", cut_opt)
print("total cost, computation cost, cut cost: \n", total_cost_opt,  comp_cost_opt, cut_cost_opt)
print("number of partition:",  nop_opt)


# os.remove(tmp_name)
# os.remove(log_name)
# os.remove(solution_name)
