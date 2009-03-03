#!/usr/bin/swipl -q -t main -f 
% top down operator precedence parser 

% tokens
number(N) --> digit(D0), digits(D), { number_chars(N, [D0|D]) },!.
digits([D|T]) --> digit(D), digits(T).
digits([]) --> [].
digit(D) --> [D], {code_type(D, digit)}.

identifier(A) -->  csym(C),csyms(N), {string_to_atom([C|N],A)},!. 
csyms([H|T]) --> csym(H), csyms(T).
csyms([]) --> [].
csym(C) --> [C], {code_type(C, csymf)}.

string(A) --> "\"", chars(S), {string_to_atom(S,A)},!.
chars([]) --> "\"".
chars(["\""|T]) --> "\\\"", chars(T).
chars([H|T]) --> [H], chars(T).

ws0 --> [X], {code_type(X, white)}, ws.
ws --> ws0.
ws --> [].

comment --> "#", comment_tail.

comment_tail --> newline,!.
comment_tail --> [_], comment_tail,!.
comment_tail --> [].

newline --> [10], linefeed. 

linefeed --> [13]; [].

item(E) --> number(E),!.
item(E) --> string(E),!.

% containers

% a block is { ... }, can have terminators
block([H|T],N) --> exprn(H,N), ws,!, block(T,N).
block(X,N) --> ";", ws,!, block(X,N).
block(X,N) --> newline, ws,!, block(X,N).
block(X,N) --> comment, ws, !, block(X,N).
block(X,N) -->  ws0, !, block(X,N).
block([],_) --> [].

% a list of expressions (function args)
exprl([H|T],N) --> exprn(H,N), ws,!, exprl(T,N).
exprl(T,N) --> comment, ws, !, exprl(T,N).
exprl(T,N) -->  ws0,!, exprl(T,N).
exprl([],_) --> [].

%helpers
exprl(L) --> ws,exprl(L, 100).
expr(L) --> ws,exprn(L,100).
block(block(L)) --> ws, block(L,100).

%expressions
exprn(O,N1) --> "(" ,!, ws,  exprn(Op, 100), ws, ")" , follow(Op, O ,N1).
exprn(O,N1) --> "[" ,!, ws,  block(Op, 90), ws, "]" , follow(Op, O ,N1).
exprn(O,N1) --> "{" ,!, ws, block(Op, 100), ws, "}" , follow(block(Op), O ,N1).
exprn(O,N1) --> prefix(Op, N),!, { N =< N1 }, ws, exprn(R,N), !, build(Op,R,Z), follow(Z, O, N1).
exprn(O,N1) --> \+ infix(_,_,_), %\+ postfix(_,_),
                identifier(X), !, idfollow(O,X,N1). 
exprn(O,N) --> item(L), !, follow(L,O,N).
 
% follow parts
idfollow(O,X,N1) --> "(" -> {5 < N1} ,!, ws, exprl(Op, 90), ws, ")",!, follow(call(X,Op), O ,N1).
idfollow(O,X,N1) --> {90 < N1},ws,\+infix(_,_,_),exprn(L1,90),!, exprl(L,90), !,follow(call(X,[L1|L]), O, N1). 
idfollow(O,X,N1) --> !,follow(id(X), O, N1). 

% every expression is ast-fragment then a follow. the fragment is passed
% to follow, to check for infix stuff (that contains it)
follow(L,O,N1) --> "[",!, ws, exprl(Op, 100), ws, "]",! , follow(index(L,Op), O ,N1).
follow(L,O,N1) --> "(",!, ws, exprl(Op, 90), ws, ")",!, follow(call(L,Op), O ,N1).
follow(L,O,N1) --> {90 < N1},ws,"$" ,!, ws, exprl(Op, 90), ws,!, follow(call(L,Op), O ,N1).
follow(L,O,N1) --> ws, (infix(Op,As,N) -> {assoc(As,N, N1)}), !,ws, exprn(R,N),!, build(Op,L,R,Z), follow(Z, O, N1).
%follow(L,O,N1) --> ws, (postfix(Op,N) -> {N =< N1}), !,follow(call(Op,[L]), O, N1).
follow(O,O,_) --> !.

assoc(right, A, B) :-  A =< B.
assoc(left, A, B) :- A < B.

build(any,R,p(any,R)) --> !.
build(some,R,p(some,R)) --> !.
build(maybe,R,p(maybe,R)) --> !.
build(zany,R,p(zany,R)) --> !.
build(zsome,R,p(zsome,R)) --> !.
build(zmaybe,R,p(zmaybe,R)) --> !.
build(ahead,R,p(ahead,R)) --> !.
build(isnt,R,p(isnt,R)) --> !.
build(C,R,call(C,R)) --> !.
build(cons,L,R,[L|R]) --> !.
build(pair,L,R,[L,R]) --> !.
build(bind,L,R,p(bind,[L,R])) --> !.
build(choice,L,R,p(choice,[L,R])) --> !.
build(C,L,R,call(C,[L,R])) --> !.

infix(def, right, 99) --> ":-".
infix(ifthen,left,85) --> "->".
infix(le, right,60) --> ">=".
infix(eq, right,60) --> "==".
infix(unf, left,80) --> "=".
infix(ge,right,60) --> "=<".
infix(gt,right,60) --> ">".
infix(lt,right,60) --> "<".
infix(cons,right,55) --> ",".
infix(bind,left,75) --> ":".
infix(where,left,97) --> "where".
infix(add,right,50) --> "+".
infix(sub,right,50) --> "-".
infix(mul,right,45) --> "*".
infix(div,right,45) --> "/".
infix(conj,right,95) --> "&&". 
infix(and,right,95) --> "and".
infix(disj,right,96) --> "||".
infix(choice,right,75) --> "|".
infix(or,right,96) --> "or".
infix(xor,right,96) --> "xor".
infix(in,right,60) --> "in".

prefix(zany,4) --> "*?".
prefix(zsome,4) --> "+?".
prefix(zmaybe,4) --> "??".

prefix(any,4) --> "*",\+"?".
prefix(some,4) --> "+", \+"?".
prefix(maybe,4) --> "?", \+"?".
prefix(isnt,4) --> "!".
prefix(ahead,4) --> "&", \+ "&".
 
prefix(not,94) --> "not".
prefix(once,94) --> "once".
prefix(quote,5) --> "'".
prefix(eval,5) --> "`".

parse(X,S) :- phrase(block(S),X),!. 
