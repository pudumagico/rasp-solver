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
node(31).
node(32).
node(33).
node(34).
node(35).
node(36).
node(37).
node(38).
node(39).
node(40).
node(41).
node(42).
node(43).
node(44).
node(45).
node(46).
node(47).
node(48).
node(49).
node(50).
edge(1,3).
edge(1,9).
edge(1,11).
edge(1,14).
edge(1,21).
edge(1,28).
edge(1,29).
edge(1,43).
edge(1,46).
edge(2,21).
edge(2,42).
edge(2,43).
edge(2,48).
edge(3,7).
edge(3,31).
edge(3,33).
edge(3,38).
edge(3,41).
edge(3,43).
edge(4,21).
edge(4,26).
edge(4,37).
edge(4,44).
edge(5,13).
edge(5,23).
edge(5,40).
edge(5,46).
edge(6,24).
edge(6,28).
edge(6,41).
edge(7,16).
edge(7,19).
edge(7,26).
edge(7,27).
edge(8,11).
edge(8,29).
edge(9,14).
edge(9,21).
edge(9,40).
edge(10,12).
edge(10,21).
edge(10,25).
edge(10,33).
edge(10,41).
edge(11,27).
edge(11,36).
edge(11,48).
edge(12,22).
edge(12,30).
edge(12,33).
edge(12,37).
edge(12,46).
edge(12,47).
edge(13,20).
edge(13,35).
edge(13,41).
edge(14,39).
edge(14,45).
edge(15,19).
edge(15,21).
edge(15,29).
edge(16,24).
edge(16,38).
edge(16,43).
edge(16,45).
edge(17,37).
edge(17,38).
edge(18,25).
edge(18,37).
edge(18,38).
edge(18,42).
edge(18,50).
edge(19,28).
edge(20,36).
edge(21,49).
edge(22,30).
edge(23,28).
edge(23,29).
edge(23,35).
edge(23,41).
edge(23,50).
edge(24,33).
edge(25,34).
edge(26,31).
edge(27,35).
edge(27,45).
edge(27,50).
edge(28,37).
edge(28,48).
edge(29,31).
edge(29,36).
edge(29,49).
edge(30,34).
edge(30,42).
edge(30,49).
edge(30,50).
edge(31,36).
edge(31,46).
edge(32,34).
edge(32,40).
edge(32,41).
edge(32,43).
edge(33,35).
edge(33,47).
edge(34,37).
edge(34,39).
edge(34,40).
edge(36,42).
edge(36,50).
edge(37,43).
edge(38,40).
edge(38,41).
edge(39,46).
edge(39,49).
edge(40,45).
edge(41,44).
edge(41,46).
edge(41,47).
edge(42,47).
edge(43,46).
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
:- not assign(31,r), not assign(31,g), not assign(31,b).
:- not assign(32,r), not assign(32,g), not assign(32,b).
:- not assign(33,r), not assign(33,g), not assign(33,b).
:- not assign(34,r), not assign(34,g), not assign(34,b).
:- not assign(35,r), not assign(35,g), not assign(35,b).
:- not assign(36,r), not assign(36,g), not assign(36,b).
:- not assign(37,r), not assign(37,g), not assign(37,b).
:- not assign(38,r), not assign(38,g), not assign(38,b).
:- not assign(39,r), not assign(39,g), not assign(39,b).
:- not assign(40,r), not assign(40,g), not assign(40,b).
:- not assign(41,r), not assign(41,g), not assign(41,b).
:- not assign(42,r), not assign(42,g), not assign(42,b).
:- not assign(43,r), not assign(43,g), not assign(43,b).
:- not assign(44,r), not assign(44,g), not assign(44,b).
:- not assign(45,r), not assign(45,g), not assign(45,b).
:- not assign(46,r), not assign(46,g), not assign(46,b).
:- not assign(47,r), not assign(47,g), not assign(47,b).
:- not assign(48,r), not assign(48,g), not assign(48,b).
:- not assign(49,r), not assign(49,g), not assign(49,b).
:- not assign(50,r), not assign(50,g), not assign(50,b).
:- assign(N,r), assign(N,g).
:- assign(N,r), assign(N,b).
:- assign(N,g), assign(N,b).

:- edge(X,Y), assign(X,C), assign(Y,C).

#show assign/2.
