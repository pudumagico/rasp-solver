% 3-coloring of a small graph (6 nodes, 7 edges)
node(1). node(2). node(3). node(4). node(5). node(6).
edge(1,2). edge(1,3). edge(2,3). edge(2,4). edge(3,5). edge(4,5). edge(5,6).
color(r). color(g). color(b).

% Each node gets one color via choice + constraints
{assign(N,r)} :- node(N).
{assign(N,g)} :- node(N).
{assign(N,b)} :- node(N).

% Each node must have at least one color
:- node(N), not assign(N,r), not assign(N,g), not assign(N,b).

% Each node must have at most one color
:- assign(N,r), assign(N,g).
:- assign(N,r), assign(N,b).
:- assign(N,g), assign(N,b).

% Adjacent nodes must differ
:- edge(X,Y), assign(X,C), assign(Y,C).

#show assign/2.
