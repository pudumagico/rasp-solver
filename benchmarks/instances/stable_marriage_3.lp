% Stable marriage: 3 men, 3 women
man(1). man(2). man(3).
woman(1). woman(2). woman(3).

% Preferences (man, woman, rank) — lower is better
mpref(1,1,1). mpref(1,2,2). mpref(1,3,3).
mpref(2,2,1). mpref(2,1,2). mpref(2,3,3).
mpref(3,1,1). mpref(3,3,2). mpref(3,2,3).

wpref(1,2,1). wpref(1,1,2). wpref(1,3,3).
wpref(2,1,1). wpref(2,3,2). wpref(2,2,3).
wpref(3,3,1). wpref(3,1,2). wpref(3,2,3).

% Choose a match
{match(M,W)} :- man(M), woman(W).

% Each man matched to exactly one woman
:- man(M), not match(M,1), not match(M,2), not match(M,3).
:- match(M,W1), match(M,W2), W1 != W2.

% Each woman matched to exactly one man
:- woman(W), not match(1,W), not match(2,W), not match(3,W).
:- match(M1,W), match(M2,W), M1 != M2.

% No blocking pair: if man M prefers woman W' over his partner W,
% then W' must prefer her partner over M
:- match(M,W), mpref(M,W2,R1), mpref(M,W,R2), R1 < R2,
   match(M2,W2), wpref(W2,M,R3), wpref(W2,M2,R4), R3 < R4.

#show match/2.
