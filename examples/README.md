This folder contains some examples for benchmark.

# gd
A stochastic gradient descent algorithm. It uses `M` private datasets, the i-th dataset has a training input `x[i]` and a traning out `y[i]`. The goal is to find a function paramerized by `theta` to approximate the dataset. We run `STEPS`  iterations to search this `theta` with a learning `rate`.
If the user does not trust that a public `theta'` is generated from the datasets, she can run this algorithm with the prover, then ask the prover to reveal `theta` and compare it with `theta'`.

# 3colfast
A graph 3-coloring checking algorithm. Given a graph of `size` vertexes where each vertex is privately labeled by 1 color out of 3, the algorithm proves each pair of adjacent vertexes are colored differently without revealing the coloring.
The running time and cutting does not depend on the graph's structure nor the coloring, so we tested a simply graph that connects all vertexes in a circle and color them by `0` or `1` alternatively.

# merkle
A merkle tree hash algorithm. Given `N` blocks of private data, the algorithm computes their hash using a binary merkle tree. Each leaf node is the hash of a data block, and each non-leaf node is the hash of two subtrees' concatenated hashes. We implemented the hash primitive as SHA-256.

# intmv
Multiple a `N * P` matrix with a `P * 1` vector. Both the matrix and the vector are private. The prover firstly locally compute the result, then let the verifier challenge the result using a randomly generated vector. In theory, when the matrix is big enough, the time cost will be 64% of the naive multiplication. Even when `N = P = 1000`, the time cost can still be reduced to 75%.