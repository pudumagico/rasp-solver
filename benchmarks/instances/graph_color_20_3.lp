node(1).
node(2).
node(3).
node(4).
node(5).
node(6).
node(7).
node(8).
node(9).
node(10).
node(11).
node(12).
node(13).
node(14).
node(15).
node(16).
node(17).
node(18).
node(19).
node(20).
edge(1,3).
edge(1,5).
edge(1,9).
edge(1,11).
edge(1,12).
edge(1,14).
edge(1,15).
edge(1,18).
edge(2,3).
edge(2,7).
edge(2,10).
edge(2,11).
edge(3,8).
edge(3,9).
edge(3,11).
edge(3,12).
edge(3,13).
edge(3,18).
edge(4,7).
edge(4,9).
edge(4,17).
edge(4,18).
edge(5,6).
edge(5,15).
edge(6,7).
edge(6,10).
edge(6,11).
edge(6,12).
edge(6,16).
edge(7,9).
edge(7,15).
edge(8,10).
edge(8,16).
edge(9,10).
edge(9,12).
edge(9,17).
edge(9,20).
edge(10,12).
edge(10,15).
edge(11,12).
edge(11,15).
edge(12,13).
edge(12,14).
edge(12,17).
edge(12,18).
edge(12,19).
edge(13,14).
edge(13,17).
edge(13,18).
edge(13,20).
edge(14,15).
edge(15,16).
edge(15,17).
edge(16,20).
edge(18,19).
edge(18,20).
color(r).
color(g).
color(b).

{assign(N,r)} :- node(N).
{assign(N,g)} :- node(N).
{assign(N,b)} :- node(N).

:- not assign(1,r), not assign(1,g), not assign(1,b).
:- not assign(2,r), not assign(2,g), not assign(2,b).
:- not assign(3,r), not assign(3,g), not assign(3,b).
:- not assign(4,r), not assign(4,g), not assign(4,b).
:- not assign(5,r), not assign(5,g), not assign(5,b).
:- not assign(6,r), not assign(6,g), not assign(6,b).
:- not assign(7,r), not assign(7,g), not assign(7,b).
:- not assign(8,r), not assign(8,g), not assign(8,b).
:- not assign(9,r), not assign(9,g), not assign(9,b).
:- not assign(10,r), not assign(10,g), not assign(10,b).
:- not assign(11,r), not assign(11,g), not assign(11,b).
:- not assign(12,r), not assign(12,g), not assign(12,b).
:- not assign(13,r), not assign(13,g), not assign(13,b).
:- not assign(14,r), not assign(14,g), not assign(14,b).
:- not assign(15,r), not assign(15,g), not assign(15,b).
:- not assign(16,r), not assign(16,g), not assign(16,b).
:- not assign(17,r), not assign(17,g), not assign(17,b).
:- not assign(18,r), not assign(18,g), not assign(18,b).
:- not assign(19,r), not assign(19,g), not assign(19,b).
:- not assign(20,r), not assign(20,g), not assign(20,b).
:- assign(N,r), assign(N,g).
:- assign(N,r), assign(N,b).
:- assign(N,g), assign(N,b).

:- edge(X,Y), assign(X,C), assign(Y,C).

#show assign/2.
