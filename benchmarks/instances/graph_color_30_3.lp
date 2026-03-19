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
node(21).
node(22).
node(23).
node(24).
node(25).
node(26).
node(27).
node(28).
node(29).
node(30).
edge(1,3).
edge(1,9).
edge(1,11).
edge(1,14).
edge(1,21).
edge(1,28).
edge(1,29).
edge(2,15).
edge(2,18).
edge(2,20).
edge(3,14).
edge(4,9).
edge(4,10).
edge(4,11).
edge(4,15).
edge(4,21).
edge(4,27).
edge(5,20).
edge(5,22).
edge(5,27).
edge(5,30).
edge(6,8).
edge(6,11).
edge(6,26).
edge(7,9).
edge(7,14).
edge(7,18).
edge(7,25).
edge(8,10).
edge(8,24).
edge(9,13).
edge(9,30).
edge(10,16).
edge(10,21).
edge(11,19).
edge(11,23).
edge(12,18).
edge(12,23).
edge(12,24).
edge(12,25).
edge(13,19).
edge(13,22).
edge(13,29).
edge(13,30).
edge(14,20).
edge(14,21).
edge(14,29).
edge(15,25).
edge(16,20).
edge(16,29).
edge(17,27).
edge(18,20).
edge(18,30).
edge(19,26).
edge(20,27).
edge(21,26).
edge(22,30).
edge(24,26).
edge(24,30).
edge(26,29).
edge(27,29).
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
:- not assign(21,r), not assign(21,g), not assign(21,b).
:- not assign(22,r), not assign(22,g), not assign(22,b).
:- not assign(23,r), not assign(23,g), not assign(23,b).
:- not assign(24,r), not assign(24,g), not assign(24,b).
:- not assign(25,r), not assign(25,g), not assign(25,b).
:- not assign(26,r), not assign(26,g), not assign(26,b).
:- not assign(27,r), not assign(27,g), not assign(27,b).
:- not assign(28,r), not assign(28,g), not assign(28,b).
:- not assign(29,r), not assign(29,g), not assign(29,b).
:- not assign(30,r), not assign(30,g), not assign(30,b).
:- assign(N,r), assign(N,g).
:- assign(N,r), assign(N,b).
:- assign(N,g), assign(N,b).

:- edge(X,Y), assign(X,C), assign(Y,C).

#show assign/2.
