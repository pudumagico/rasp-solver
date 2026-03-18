pigeon(1).
pigeon(2).
pigeon(3).
pigeon(4).
pigeon(5).
pigeon(6).
pigeon(7).
pigeon(8).
pigeon(9).
hole(1).
hole(2).
hole(3).
hole(4).
hole(5).
hole(6).
hole(7).
hole(8).

{in(P,H)} :- pigeon(P), hole(H).

:- not in(1,1), not in(1,2), not in(1,3), not in(1,4), not in(1,5), not in(1,6), not in(1,7), not in(1,8).
:- not in(2,1), not in(2,2), not in(2,3), not in(2,4), not in(2,5), not in(2,6), not in(2,7), not in(2,8).
:- not in(3,1), not in(3,2), not in(3,3), not in(3,4), not in(3,5), not in(3,6), not in(3,7), not in(3,8).
:- not in(4,1), not in(4,2), not in(4,3), not in(4,4), not in(4,5), not in(4,6), not in(4,7), not in(4,8).
:- not in(5,1), not in(5,2), not in(5,3), not in(5,4), not in(5,5), not in(5,6), not in(5,7), not in(5,8).
:- not in(6,1), not in(6,2), not in(6,3), not in(6,4), not in(6,5), not in(6,6), not in(6,7), not in(6,8).
:- not in(7,1), not in(7,2), not in(7,3), not in(7,4), not in(7,5), not in(7,6), not in(7,7), not in(7,8).
:- not in(8,1), not in(8,2), not in(8,3), not in(8,4), not in(8,5), not in(8,6), not in(8,7), not in(8,8).
:- not in(9,1), not in(9,2), not in(9,3), not in(9,4), not in(9,5), not in(9,6), not in(9,7), not in(9,8).

:- in(P1,H), in(P2,H), P1 != P2.

#show in/2.
