row(1). col(1).
row(2). col(2).
row(3). col(3).
row(4). col(4).
row(5). col(5).
row(6). col(6).
row(7). col(7).
row(8). col(8).
row(9). col(9).
row(10). col(10).
row(11). col(11).
row(12). col(12).

{queen(R,C)} :- row(R), col(C).

:- not queen(1,1), not queen(1,2), not queen(1,3), not queen(1,4), not queen(1,5), not queen(1,6), not queen(1,7), not queen(1,8), not queen(1,9), not queen(1,10), not queen(1,11), not queen(1,12).
:- not queen(2,1), not queen(2,2), not queen(2,3), not queen(2,4), not queen(2,5), not queen(2,6), not queen(2,7), not queen(2,8), not queen(2,9), not queen(2,10), not queen(2,11), not queen(2,12).
:- not queen(3,1), not queen(3,2), not queen(3,3), not queen(3,4), not queen(3,5), not queen(3,6), not queen(3,7), not queen(3,8), not queen(3,9), not queen(3,10), not queen(3,11), not queen(3,12).
:- not queen(4,1), not queen(4,2), not queen(4,3), not queen(4,4), not queen(4,5), not queen(4,6), not queen(4,7), not queen(4,8), not queen(4,9), not queen(4,10), not queen(4,11), not queen(4,12).
:- not queen(5,1), not queen(5,2), not queen(5,3), not queen(5,4), not queen(5,5), not queen(5,6), not queen(5,7), not queen(5,8), not queen(5,9), not queen(5,10), not queen(5,11), not queen(5,12).
:- not queen(6,1), not queen(6,2), not queen(6,3), not queen(6,4), not queen(6,5), not queen(6,6), not queen(6,7), not queen(6,8), not queen(6,9), not queen(6,10), not queen(6,11), not queen(6,12).
:- not queen(7,1), not queen(7,2), not queen(7,3), not queen(7,4), not queen(7,5), not queen(7,6), not queen(7,7), not queen(7,8), not queen(7,9), not queen(7,10), not queen(7,11), not queen(7,12).
:- not queen(8,1), not queen(8,2), not queen(8,3), not queen(8,4), not queen(8,5), not queen(8,6), not queen(8,7), not queen(8,8), not queen(8,9), not queen(8,10), not queen(8,11), not queen(8,12).
:- not queen(9,1), not queen(9,2), not queen(9,3), not queen(9,4), not queen(9,5), not queen(9,6), not queen(9,7), not queen(9,8), not queen(9,9), not queen(9,10), not queen(9,11), not queen(9,12).
:- not queen(10,1), not queen(10,2), not queen(10,3), not queen(10,4), not queen(10,5), not queen(10,6), not queen(10,7), not queen(10,8), not queen(10,9), not queen(10,10), not queen(10,11), not queen(10,12).
:- not queen(11,1), not queen(11,2), not queen(11,3), not queen(11,4), not queen(11,5), not queen(11,6), not queen(11,7), not queen(11,8), not queen(11,9), not queen(11,10), not queen(11,11), not queen(11,12).
:- not queen(12,1), not queen(12,2), not queen(12,3), not queen(12,4), not queen(12,5), not queen(12,6), not queen(12,7), not queen(12,8), not queen(12,9), not queen(12,10), not queen(12,11), not queen(12,12).

:- queen(R,C1), queen(R,C2), C1 != C2.
:- queen(R1,C), queen(R2,C), R1 != R2.
:- queen(R1,C1), queen(R2,C2), R1 != R2, R1-C1 = R2-C2.
:- queen(R1,C1), queen(R2,C2), R1 != R2, R1+C1 = R2+C2.

#show queen/2.
