% Reachability in a 20-node chain graph
node(1). node(2). node(3). node(4). node(5).
node(6). node(7). node(8). node(9). node(10).
node(11). node(12). node(13). node(14). node(15).
node(16). node(17). node(18). node(19). node(20).

edge(1,2). edge(2,3). edge(3,4). edge(4,5). edge(5,6).
edge(6,7). edge(7,8). edge(8,9). edge(9,10). edge(10,11).
edge(11,12). edge(12,13). edge(13,14). edge(14,15). edge(15,16).
edge(16,17). edge(17,18). edge(18,19). edge(19,20).
edge(1,10). edge(5,15). edge(10,20).

reach(X,Y) :- edge(X,Y).
reach(X,Z) :- reach(X,Y), edge(Y,Z).

#show reach/2.
