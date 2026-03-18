% Pigeonhole: 3 pigeons into 2 holes (UNSAT)
pigeon(1). pigeon(2). pigeon(3).
hole(1). hole(2).

{in(P,H)} :- pigeon(P), hole(H).

% Each pigeon must be in at least one hole
:- pigeon(P), not in(P,1), not in(P,2).

% At most one pigeon per hole
:- in(P1,H), in(P2,H), P1 != P2.

#show in/2.
