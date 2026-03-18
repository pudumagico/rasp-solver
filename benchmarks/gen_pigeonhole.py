#!/usr/bin/env python3
"""Generate pigeonhole instance: p pigeons, h holes (UNSAT when p > h)."""
import sys

p = int(sys.argv[1]) if len(sys.argv) > 1 else 5
h = int(sys.argv[2]) if len(sys.argv) > 2 else 4

for i in range(1, p + 1):
    print(f"pigeon({i}).")
for i in range(1, h + 1):
    print(f"hole({i}).")

print()
print("{in(P,H)} :- pigeon(P), hole(H).")
print()

# Each pigeon in at least one hole
for pi in range(1, p + 1):
    holes = ", ".join(f"not in({pi},{hi})" for hi in range(1, h + 1))
    print(f":- {holes}.")

print()
print(":- in(P1,H), in(P2,H), P1 != P2.")
print()
print("#show in/2.")
