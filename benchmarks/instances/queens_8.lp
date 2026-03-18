% 8-Queens problem
row(1). row(2). row(3). row(4). row(5). row(6). row(7). row(8).
col(1). col(2). col(3). col(4). col(5). col(6). col(7). col(8).

{queen(R,C)} :- row(R), col(C).

:- row(R), not queen(R,1), not queen(R,2), not queen(R,3), not queen(R,4),
   not queen(R,5), not queen(R,6), not queen(R,7), not queen(R,8).

:- queen(R,C1), queen(R,C2), C1 != C2.
:- queen(R1,C), queen(R2,C), R1 != R2.
:- queen(R1,C1), queen(R2,C2), R1 != R2, R1-C1 = R2-C2.
:- queen(R1,C1), queen(R2,C2), R1 != R2, R1+C1 = R2+C2.

#show queen/2.
