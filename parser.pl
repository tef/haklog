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

newline --> [10], linefeed. 

linefeed --> [13]; [].

item(E) --> number(E),!.
item(E) --> string(E),!.

% containers

% a block is { ... }, can have terminators
block([H|T],N) --> exprn(H,N), ws,!, block(T,N).
block(X,N) --> ";", ws,!, block(X,N).
block(X,N) --> newline, ws,!, block(X,N).
block([],_) --> [].

% a list of expressions (function args)
exprl([H|T],N) --> exprn(H,N), ws,!, exprl(T,N).
exprl([],_) --> [].

%helpers
exprl(L) --> ws,exprl(L, 100).
expr(L) --> ws,exprn(L,100).
block(block(L)) --> ws, block(L,100).

%expressions
exprn(O,N1) --> \+ infix(_,_,_), \+ postfix(_,_), identifier(X), !, idfollow(O,X,N1). 
exprn(O,N1) --> prefix(Op, N),!, { N =< N1 }, ws, exprn(R,N), !, follow(call(Op,[R]), O, N1).
exprn(O,N1) --> "(" ,!, ws,  exprn(Op, 100), ws, ")" , follow(Op, O ,N1).
exprn(O,N1) --> "[" ,!, ws,  block(Op, 90), ws, "]" , follow(Op, O ,N1).
exprn(O,N1) --> "{" ,!, ws, block(Op, 100), ws, "}" , follow(block(Op), O ,N1).
exprn(O,N) --> item(L), !, follow(L,O,N).
 
% follow parts
idfollow(O,X,N1) --> "(", ws, exprl(L,90), ws, ")", !,follow(call(X,L), O, N1). 
idfollow(O,X,N1) --> {90 < N1},ws, exprn(L1,90),!, exprl(L,90), !,follow(call(X,[L1|L]), O, N1). 
idfollow(O,X,N1) --> !,follow(id(X), O, N1). 

% every expression is ast-fragment then a follow. the fragment is passed
% to follow, to check for infix stuff (that contains it)
follow(L,O,N1) --> "[", ws, exprl(Op, 100), ws, "]",! , follow(index(L,Op), O ,N1).
follow(L,O,N1) --> "(", ws, exprl(Op, 90), ws, ")",!, follow(call(L,Op), O ,N1).
follow(L,O,N1) --> ws, (infix(Op,As,N) -> {assoc(As,N, N1)}), !,ws, exprn(R,N),!, build(Op,L,R,Z), follow(Z, O, N1).
follow(L,O,N1) --> ws, (postfix(Op,N) -> {N =< N1}), follow(call(Op,[L]), O, N1).
follow(L,O,N1) --> ws, ":;" , {99 =< N1} , follow(call(def,[L,[]]), O, N1).
follow(O,O,_) --> ws.

assoc(right, A, B) :-  A =< B.
assoc(left, A, B) :- A < B.

build(cons,L,R,[L|R]) --> [],!.
build(pair,L,R,[L,R]) --> [],!.
build(C,L,R,call(C,[L,R])) --> [],!.

infix(def, right, 99) --> ":-".
infix(ifthen,left,85) --> "->".
infix(le, right,60) --> ">=".
infix(eq, right,60) --> "==".
infix(unf, left,80) --> "=".
infix(ge,right,60) --> "=<".
infix(gt,right,60) --> ">".
infix(lt,right,60) --> "<".
infix(cons,right,55) --> ",".
infix(pair,right,55) --> ":".
infix(add,right,50) --> "+".
infix(sub,right,50) --> "-".
infix(mul,right,45) --> "*".
infix(div,right,45) --> "/".
infix(all,right,95) --> "&&". 
infix(and,right,95) --> "and".
infix(any,right,96) --> "||".
infix(or,right,96) --> "or".
infix(in,right,60) --> "in".

prefix(not,94) --> "not".
prefix(once,94) --> "once".
prefix(quote,5) --> "'".
prefix(eval,5) --> "`".
prefix(unpack,5) --> "*".
postfix(post,5) --> "?".

parse(X,S) :- phrase(block(S),X),!. 
