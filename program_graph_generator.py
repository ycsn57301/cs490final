import networkx as nx
import matplotlib.pyplot as plt
import re
import ast
G = nx.Graph()
cut_edge = []
node_cost = {}
with open('/tmp/OPBStat.txt') as f:
    lines = f.readlines()
    index = lines.index("cut edge: \n")
    i = 0
    while i < len(lines[index+1]):
        if lines[index+1][i] == '(':
            s = ''
            d = ''
            while not lines[index+1][i+1] == ',':
                i = i + 1
                s = s + lines[index+1][i]
            i = i + 1
            while not lines[index+1][i+1] == ')':
                i = i + 1
                d = d + lines[index+1][i]
            cut_edge.append((int(s), int(d)))
        i = i + 1

with open('/tmp/OPBInput.txt') as f:
    lines = f.readlines()
    edge_info_line_begin = lines.index("edge info\n")
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
        if c > 1:
            w = 5
        else:
            w = 1
        if is_cuttable == 0:
            continue
        if cut_edge.count((s, d)) > 0:
            print((s, d), "cut")
            G.add_edge(s,d, color='blue',  weight=w)
            continue
        print((s, d), "non cut")
        G.add_edge(s, d, color='black', weight=w)
    node_info_line_begin = lines.index("node info\n")
    for i in range(node_info_line_begin+1, edge_info_line_begin):
        x = re.split(', |:|\t|\n|,|,  |:\n ', lines[i])
        for e in x:
            if len(e) == 0:
                x.remove(e)
        assert len(x) == 2
        index = int(x[0])
        cost = int(x[1])
        if cost > 1:
            node_cost[index] = 'red'
        else:
            node_cost[index] = 'grey'


#

#
# 0, 1, 256, 1
# 2, 3, 256, 1
# 3, 4, 256, 1
# 1, 4, 256, 1
# 4, 5, 256, 1
# 6, 7, 256, 1
# 8, 9, 256, 1
# 7, 10, 256, 1
# 9, 10, 256, 1
# 10, 11, 256, 1
# 5, 12, 256, 1
# 11, 12, 256, 1
# 12, 13, 256, 1

#
#
pos =nx.circular_layout(G, dim=2, center=[100, 0])
edges = G.edges()
colors = [G[u][v]['color'] for u, v in edges]
weights = [G[u][v]['weight'] for u, v in edges]
print(node_cost.keys())

nx.draw(G,
        node_color=[v for v in node_cost.values()], edge_color=colors, width=weights, with_labels=True)

# nx.draw_networkx_edge_labels(
#     G, pos,
#     edge_labels={('A', 'B'): 'AB',
#                  ('A', 'C'): 'AC',
#                  ('D', 'B'): 'DB'},
#     font_color='red'
# )
plt.savefig("3col-4.pdf", format="pdf", bbox_inches="tight")
