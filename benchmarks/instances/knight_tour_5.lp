% Knight's tour on a 5x5 board — find a Hamiltonian path
row(1). row(2). row(3). row(4). row(5).
col(1). col(2). col(3). col(4). col(5).
step(1). step(2). step(3). step(4). step(5). step(6). step(7). step(8). step(9). step(10).
step(11). step(12). step(13). step(14). step(15). step(16). step(17). step(18). step(19). step(20).
step(21). step(22). step(23). step(24). step(25).

% Knight moves
move(R1,C1,R2,C2) :- row(R1), col(C1), row(R2), col(C2), R2-R1=2, C2-C1=1.
move(R1,C1,R2,C2) :- row(R1), col(C1), row(R2), col(C2), R2-R1=2, C1-C2=1.
move(R1,C1,R2,C2) :- row(R1), col(C1), row(R2), col(C2), R1-R2=2, C2-C1=1.
move(R1,C1,R2,C2) :- row(R1), col(C1), row(R2), col(C2), R1-R2=2, C1-C2=1.
move(R1,C1,R2,C2) :- row(R1), col(C1), row(R2), col(C2), R2-R1=1, C2-C1=2.
move(R1,C1,R2,C2) :- row(R1), col(C1), row(R2), col(C2), R2-R1=1, C1-C2=2.
move(R1,C1,R2,C2) :- row(R1), col(C1), row(R2), col(C2), R1-R2=1, C2-C1=2.
move(R1,C1,R2,C2) :- row(R1), col(C1), row(R2), col(C2), R1-R2=1, C1-C2=2.

% Assign position at each step
{at(T,R,C)} :- step(T), row(R), col(C).

% Exactly one position per step
:- step(T), at(T,R1,C1), at(T,R2,C2), R1 != R2.
:- step(T), at(T,R1,C1), at(T,R2,C2), C1 != C2.

% Each cell visited exactly once
:- row(R), col(C), at(T1,R,C), at(T2,R,C), T1 != T2.

% Start at (1,1)
at(1,1,1).

% Consecutive steps must be knight moves
:- step(T), T > 1, at(T,R2,C2), at(T-1,R1,C1), not move(R1,C1,R2,C2).

#show at/3.
