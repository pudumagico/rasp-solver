#!/usr/bin/env python3
"""Generate random graph coloring instance."""
import sys
import random

n = int(sys.argv[1]) if len(sys.argv) > 1 else 10
k = int(sys.argv[2]) if len(sys.argv) > 2 else 3
edge_prob = float(sys.argv[3]) if len(sys.argv) > 3 else 0.3
seed = int(sys.argv[4]) if len(sys.argv) > 4 else 42

random.seed(seed)
colors = ["r", "g", "b", "y", "w"][:k]

for i in range(1, n + 1):
    print(f"node({i}).")

edges = []
for i in range(1, n + 1):
    for j in range(i + 1, n + 1):
        if random.random() < edge_prob:
            edges.append((i, j))
            print(f"edge({i},{j}).")

for c in colors:
    print(f"color({c}).")

print()
for c in colors:
    print(f"{{assign(N,{c})}} :- node(N).")

print()
# At least one color per node
for ni in range(1, n + 1):
    nots = ", ".join(f"not assign({ni},{c})" for c in colors)
    print(f":- {nots}.")

# At most one color per node
for i, c1 in enumerate(colors):
    for c2 in colors[i + 1:]:
        print(f":- assign(N,{c1}), assign(N,{c2}).")

print()
print(":- edge(X,Y), assign(X,C), assign(Y,C).")
print()
print("#show assign/2.")
