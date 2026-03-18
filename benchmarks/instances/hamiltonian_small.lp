% Hamiltonian cycle on a 4-node graph
node(1). node(2). node(3). node(4).
edge(1,2). edge(2,3). edge(3,4). edge(4,1). edge(1,3). edge(2,4).

% Choose which edges to include
{in(X,Y)} :- edge(X,Y).

% At most one outgoing/incoming per node
:- in(X,Y1), in(X,Y2), Y1 != Y2.
:- in(X1,Y), in(X2,Y), X1 != X2.

% At least one outgoing per node (only existing edges)
:- not in(1,2), not in(1,3).
:- not in(2,3), not in(2,4).
:- not in(3,4).
:- not in(4,1).

% At least one incoming per node (only existing edges)
:- not in(4,1).
:- not in(1,2).
:- not in(2,3), not in(1,3).
:- not in(3,4), not in(2,4).

% Reachability from node 1
reach(1).
reach(Y) :- reach(X), in(X,Y).
:- node(X), not reach(X).

#show in/2.
