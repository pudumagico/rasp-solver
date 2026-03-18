% 4-Queens problem
row(1). row(2). row(3). row(4).
col(1). col(2). col(3). col(4).

% Place one queen per row
{queen(R,C)} :- row(R), col(C).

% Each row has at least one queen
:- row(R), not queen(R,1), not queen(R,2), not queen(R,3), not queen(R,4).

% At most one queen per row
:- queen(R,C1), queen(R,C2), C1 != C2.

% At most one queen per column
:- queen(R1,C), queen(R2,C), R1 != R2.

% No two queens on same diagonal
:- queen(R1,C1), queen(R2,C2), R1 != R2, R1-C1 = R2-C2.
:- queen(R1,C1), queen(R2,C2), R1 != R2, R1+C1 = R2+C2.

#show queen/2.
