% Latin square of order 4: fill a 4x4 grid with values 1-4
% such that each value appears exactly once per row and column.
pos(1). pos(2). pos(3). pos(4).
val(1). val(2). val(3). val(4).

% Assign a value to each cell
{cell(R,C,V)} :- pos(R), pos(C), val(V).

% Exactly one value per cell
:- pos(R), pos(C), cell(R,C,V1), cell(R,C,V2), V1 != V2.
:- pos(R), pos(C), not cell(R,C,1), not cell(R,C,2), not cell(R,C,3), not cell(R,C,4).

% Each value appears at most once per row
:- pos(R), val(V), cell(R,C1,V), cell(R,C2,V), C1 != C2.

% Each value appears at most once per column
:- pos(C), val(V), cell(R1,C,V), cell(R2,C,V), R1 != R2.

#show cell/3.
