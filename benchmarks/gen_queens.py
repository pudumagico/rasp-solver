#!/usr/bin/env python3
"""Generate N-queens ASP instance."""
import sys

n = int(sys.argv[1]) if len(sys.argv) > 1 else 8

for i in range(1, n + 1):
    print(f"row({i}). col({i}).")

print()
print("{queen(R,C)} :- row(R), col(C).")
print()

# At least one queen per row (enumerate all columns)
for r in range(1, n + 1):
    cols = ", ".join(f"not queen({r},{c})" for c in range(1, n + 1))
    print(f":- {cols}.")

print()
print(":- queen(R,C1), queen(R,C2), C1 != C2.")
print(":- queen(R1,C), queen(R2,C), R1 != R2.")
print(":- queen(R1,C1), queen(R2,C2), R1 != R2, R1-C1 = R2-C2.")
print(":- queen(R1,C1), queen(R2,C2), R1 != R2, R1+C1 = R2+C2.")
print()
print("#show queen/2.")
