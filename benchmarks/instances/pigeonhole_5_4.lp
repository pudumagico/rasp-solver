% Pigeonhole: 5 pigeons into 4 holes (UNSAT)
pigeon(1). pigeon(2). pigeon(3). pigeon(4). pigeon(5).
hole(1). hole(2). hole(3). hole(4).

{in(P,H)} :- pigeon(P), hole(H).

:- pigeon(P), not in(P,1), not in(P,2), not in(P,3), not in(P,4).
:- in(P1,H), in(P2,H), P1 != P2.

#show in/2.
