% Schur numbers: partition {1..9} into 4 sets such that
% no set contains x, y, z with x + y = z.
num(1). num(2). num(3). num(4). num(5). num(6). num(7). num(8). num(9).
set(1). set(2). set(3). set(4).

% Assign each number to exactly one set
{assign(N,S)} :- num(N), set(S).
:- num(N), not assign(N,1), not assign(N,2), not assign(N,3), not assign(N,4).
:- assign(N,S1), assign(N,S2), S1 != S2.

% No x + y = z in the same set
:- assign(X,S), assign(Y,S), assign(Z,S), num(X), num(Y), num(Z), X + Y = Z, X <= Y.

#show assign/2.
