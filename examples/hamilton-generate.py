import numpy as np

size = 100
threshold = 0.8

graph = [0]*(size*size)



path = np.random.permutation(size)
# path = [0,1,2,3]
# print(path)

for i in range(size):
    graph[path[i]*size + path[(i+1)%size]] = 1
    graph[path[(i+1)%size]*size + path[i]] = 1

# print(graph)

for i in range(size*size):
    # if (np.random > 0.5):
    if (np.random.rand() > threshold):
        graph[i] = 1

# print(graph)

# print graph

gr_str = "graph = {"

for i in range(size):
    for j in range(size):
        if (graph[i*size + j] == 1):
            gr_str += "true"
        else:
            gr_str += "false"
        if (j < size-1):
            gr_str += ", "
        else:
            gr_str += ""
        
    if (i < size-1):
        gr_str+=",\n"
    else:
        gr_str+="};"

pt_str = "path = {"
for i in range(size):
    pt_str += str(path[i])
    if (i < size-1):
        pt_str += ","
pt_str += "};"

print(gr_str)
print(pt_str)