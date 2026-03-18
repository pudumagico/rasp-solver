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
edge(1,3).
edge(1,4).
edge(1,5).
edge(1,9).
edge(1,11).
edge(1,12).
edge(1,14).
edge(1,15).
edge(2,5).
edge(2,8).
edge(2,12).
edge(2,15).
edge(3,4).
edge(4,7).
edge(4,8).
edge(4,9).
edge(4,10).
edge(4,11).
edge(4,12).
edge(4,13).
edge(5,7).
edge(5,8).
edge(5,12).
edge(5,14).
edge(6,13).
edge(6,14).
edge(7,8).
edge(7,9).
edge(8,10).
edge(8,11).
edge(8,13).
edge(9,11).
edge(9,14).
edge(9,15).
edge(10,11).
edge(10,15).
edge(12,14).
edge(14,15).
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
:- assign(N,r), assign(N,g).
:- assign(N,r), assign(N,b).
:- assign(N,g), assign(N,b).

:- edge(X,Y), assign(X,C), assign(Y,C).

#show assign/2.
