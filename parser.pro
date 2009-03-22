#!/usr/bin/swipl -q -t main -f 
% top down operator precedence parser 

% works by finding an item, and then a follow.
% the follow searches for a right hand side of a given binding power
% and then builds the expression

% tokens
number(N) --> digit(D0), digits(D), { number_codes(N, [D0|D]) },!.
digits([D|T]) --> ("_" -> !; []),digit(D), digits(T).
digits(O) --> ".",digit(D0),!, {append(".",[D0|T],O)}, digits(T).
digits([]) --> [].
digit(D) --> [D], {code_type(D, digit)},!.

identifier(A) -->  csym(C),csyms(N), {string_to_atom([C|N],A)},!. 
csyms([H|T]) --> csym_(H), csyms(T).
csyms([]) --> [].
csym(C) --> [C], {code_type(C, csymf)}.
csym_(C) --> [C], {code_type(C, csym)}.

string(A) --> "\"", chars(S), {string_to_list(A,S)},!.
chars([]) --> "\"".
chars(O) --> "\\",!, escapes(O). 
chars([H|T]) --> [H], chars(T).

escapes(O) --> "\"", {append("\"",T,O)},chars(T).
escapes(O) --> "n", {append("\n",T,O)},chars(T).
escapes(O) --> "t", {append("\t",T,O)},chars(T).
escapes(O) --> newline, chars(O).

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

% a call_block is { ... }, can have terminators
call_block([H|T],N) --> exprn(H,N), ws,!, call_block(T,N).
call_block(X,N) --> ";", ws,!, call_block(X,N).
call_block(X,N) --> newline, ws,!, call_block(X,N).
call_block(X,N) --> comment, ws, !, call_block(X,N).
call_block(X,N) -->  ws0, !, call_block(X,N).
call_block([],_) --> [].

% a list of expressions (function args)
exprl([H|T],N) --> exprn(H,N), ws,!, exprl(T,N).
exprl(T,N) --> comment, ws, !, exprl(T,N).
exprl(T,N) -->  ws0,!, exprl(T,N).
exprl([],_) --> [].

regex(T,N) --> "^",ws,!,rx_list(T,N).
regex([p(zany,id('_'))|T],N) --> ws,rx_list(T,N),!.
regex([],_) --> ws.

rxm_list([H|T],N) --> rx(H,N), ws,!, rx_list(T,N).
rxm_list([],_) -->  ws.

class_list([H|T]) --> rx_class(H), class_list(T).
class_list([]) --> ws.

rx_list([H|T],N) --> rx(H,N), ws,!, rx_list(T,N).
rx_list([],_) -->  ws, "$",!.
rx_list([p(any,_)],_) --> ws.

rx_class(_) --> ("/";")";"]";"$"),!,{fail}.
rx_class(O) --> "(" ,!, ws,  rx(O, 100), ws, ")" .
rx_class(O) --> "\\",!, rxescapes(O).
rx_class(O) --> csym_(A), "-", csym_(B),!, rxbuild(crange,A,B,O).
rx_class(O) --> [L], {string_to_atom([L],O)}.

rxex(R,_) --> identifier(Ri),!,idbuild(Ri,R).
rxex(R,_) --> item(R),!.
rxex(block(Op),_) --> "{" ,!, ws, block(Op, 100), ws, "}",!.

rx(_,_) --> ("/";")";"]";"$"),!,{fail}.
rx(O,N1) --> "(" ,!, ws,  rx(Op, 100), ws, ")" , rxfollow(Op, O ,N1).
rx(O,N1) --> "[^" ,!, ws,  class_list(Op), ws, "]", rxbuild(choice,Op,Z), rxbuild(isnt,Z,Z1),  rxfollow(Z1, O ,N1).
rx(O,N1) --> "[" ,!, ws,  class_list(Op), ws, "]", rxbuild(choice,Op,Z), rxfollow(Z, O ,N1).
rx(O,N1) --> "{" ,!, ws, block(Op, 100), ws, "}" , rxfollow(block(Op), O ,N1).
rx(O,N1) --> prefix(Op, N), regexop(Op), !, { N =< N1 }, ws, rx(R,N), !, rxbuild(Op,R,Z), rxfollow(Z, O, N1).
rx(O,N1) --> ".",!, rxbuild(dot,C),rxfollow(C,O,N1).
rx(O,N1) --> "\\",!, rxescapes(C), rxfollow(C,O,N1).
rx(O,N1) --> [L], {string_to_atom([L],A)}, rxfollow(A, O, N1).

rxescapes(O) --> "n",!,rxbuild(nl,O).
rxescapes(O) --> [X], {member(X,"wWsSdD"), string_to_atom([X],A)},!,rxbuild(class,A,O).
rxescapes(O) --> [X], {member(X,"^$*+.-[](){}\\"), string_to_atom([X],O)},!.

wbreak --> ws0.
wbreak --> \+ item(_);\+ number(_).

lookahead(X),[X] --> [X].


rxfollow(L,O,N1) --> ((postfix(Op,N), regexop(Op)) -> {N =< N1}), !, rxbuild(Op,L,Z), rxfollow(Z, O, N1).
rxfollow(L,O,N1) --> ws, ((infix(bind,As,N)) -> {assoc(As,N, N1)}), !,ws, rxex(R,N),!, rxbuild(bind,L,R,Z), rxfollow(Z, O, N1).
rxfollow(L,O,N1) --> ws, ((infix(take,As,N)) -> {assoc(As,N, N1)}), !,ws, rxex(R,N),!, rxbuild(take,L,R,Z), rxfollow(Z, O, N1).
rxfollow(L,O,N1) --> ws, ((infix(ztake,As,N)) -> {assoc(As,N, N1)}), !,ws, rxex(R,N),!, rxbuild(ztake,L,R,Z), rxfollow(Z, O, N1).
rxfollow(L,O,N1) --> ws, ((infix(Op,As,N),regexop(Op)) -> {assoc(As,N, N1)}), !,ws, rx(R,N),!, rxbuild(Op,L,R,Z), rxfollow(Z, O, N1).
rxfollow(O,O,_) --> !.

%helpers
exprl(L) --> ws,exprl(L, 100).
expr(L) --> ws,exprn(L,100).
block(block(L)) --> ws, block(L,100).

%par_exprn(Z) --> identifier(O), build(O,[],Z).
par_exprn(O) --> exprn(O, 100), ws.

%expressions
exprn(O,N1) --> "(" ,!, ws,  par_exprn(Op),")",!, follow(Op, O ,N1).
exprn(O,N1) --> "[" ,!, ws,  block(Op, 90), ws, "]" , follow(Op, O ,N1).
exprn(O,N1) --> "{" ,!, ws, block(Op, 100), ws, "}" , follow(block(Op), O ,N1).
exprn(O,N1) --> "~/" ,!, regex(R,100), "/" , follow(R, O ,N1).
exprn(O,N1) --> "m/" ,!, rxm_list(R,100), "/" , follow(R, O ,N1).
exprn(O,N1) --> prefix(Op, N),!, { N =< N1 }, exprn(R,N), !, build(Op,R,Z), follow(Z, O, N1).
exprn(O,N1) --> \+ infix(_,_,_), %\+ postfix(_,_),
                identifier(X), !, idfollow(O,X,N1). 
exprn(O,N) --> item(L), !, follow(L,O,N).
 
% follow parts
idfollow(O,X,N1) --> "(" -> {5 < N1} ,!, ws, exprl(Op, 90), ws, ")",!, follow(call(X,Op), O ,N1).
idfollow(O,X,N1) --> ":",ws0,call_block(L,100), ws, "end",!,follow(call(X,L), O, N1). 
idfollow(O,X,N1) --> {90 < N1},ws,\+infix(_,_,_),exprn(L1,90),!, exprl(L,90), !,follow(call(X,[L1|L]), O, N1). 
idfollow(O,X,N1) --> !,idbuild(X,Xo), follow(Xo, O, N1). 

% every expression is ast-fragment then a follow. the fragment is passed
% to follow, to check for infix stuff (that contains it)
follow(L,O,N1) --> "[",!, ws, exprl(Op, 100), ws, "]",! , follow(index(L,Op), O ,N1).
follow(L,O,N1) --> "(",!, ws, exprl(Op, 90), ws, ")",!, follow(call(L,Op), O ,N1).
follow(L,O,N1) --> (postfix(Op,N) -> {N =< N1}), wbreak, !, build(Op,L,Z), follow(Z, O, N1).
follow(L,O,N1) --> {90 < N1},ws,"$" ,!, ws, exprl(Op, 90), ws,!, follow(call(L,Op), O ,N1).
follow(L,O,N1) --> ws, (infix(Op,As,N) -> {assoc(As,N, N1)}), !,ws, exprn(R,N),!, build(Op,L,R,Z), follow(Z, O, N1).
follow(O,O,_) --> !.

assoc(right, A, B) :-  A =< B.
assoc(left, A, B) :- A < B.
idbuild(end,_) --> !, {fail}.
idbuild(X,X) --> {is_reserved(X)},!.
idbuild(A,id(A)) --> !.
rxbuild(dot,id('_')) --> !.
rxbuild(nl,'\n') --> !.
rxbuild(N,p(N,[])) --> !.
rxbuild(choice,X,p(choice,X)) --> !.
rxbuild(class,X,p(class,X)) --> !.
rxbuild(P,R,L) --> build(P,R,L).
rxbuild(bind,L,R,p(bind,[L,R])) --> !.
rxbuild(take,L,R,p(take,[L,R])) --> !.
rxbuild(ztake,L,R,p(ztake,[L,R])) --> !.
rxbuild(crange,L,R,p(crange,[L,R])) --> !.
rxbuild(P,R,L,O) --> build(P,R,L,O).
build(any,R,p(any,R)) --> !.
build(take,R,p(take,R)) --> !.
build(some,R,p(some,R)) --> !.
build(maybe,R,p(maybe,R)) --> !.
build(zany,R,p(zany,R)) --> !.
build(ztake,R,p(ztake,R)) --> !.
build(zsome,R,p(zsome,R)) --> !.
build(zmaybe,R,p(zmaybe,R)) --> !.
build(ahead,R,p(ahead,R)) --> !.
build(isnt,R,p(isnt,R)) --> !.
build(quote,id(R),R) --> !.
build(quote,R,R) --> {atom(R)},!.
build(neg,R,Ro) --> {number(R), Ro is -R},!.
build(C,R,call(C,R)) --> !.
build(concat,L,R,[p(any,L), p(any,R)]) --> !.
build(cons,L,R,[L|R]) --> !. 
build(pair,L,R,[L,R]) --> !.
build(bind,L,R,p(bind,[L,R])) --> !.
build(choice,L,R,p(choice,[L,R])) --> !.
build(matchr,L,R,call(match,[R,L])) --> !.
build(C,L,R,call(C,[L,R])) --> !.

regexop(isnt) -->!.
regexop(ahead) -->!.
regexop(some) -->!.
regexop(zsome) -->!.
regexop(maybe) -->!.
regexop(zmaybe) -->!.
regexop(any) -->!.
regexop(zany) -->!.
regexop(choice) -->!.

infix(def, right, 99) --> ":-".
infix(to,right,62) --> "..".
infix(is, right, 94) --> "is".
infix(match, right, 81) --> "~=".
infix(matchr, left, 82) --> "=~".
infix(ifthen,left,85) --> "->".
infix(le, right,60) --> ">=".
infix(eq, right,60) --> "==".
infix(unf, right,80) --> "=".
infix(ge,right,60) --> "=<".
infix(gt,right,60) --> ">".
infix(lt,right,60) --> "<".
infix(cons,right,55) --> ",".
infix(bind,left,75) --> ":".
infix(where,right,93) --> "where".
infix(concat,right,57) --> "++".
infix(pow,right,44) --> "**".
infix(add,right,50) --> "+".
infix(sub,right,50) --> "-", ws0.
infix(mul,right,45) --> "*".
infix(div,right,45) --> "/".
infix(conj,right,95) --> "&&". 
infix(and,right,95) --> "and".
infix(disj,right,96) --> "||".
infix(choice,right,56) --> "|".
infix(or,right,96) --> "or".
infix(xor,right,96) --> "xor".
infix(in,right,60) --> "in".
infix(ztake,right,3) --> "^?".
infix(take,right,3) --> "^".

postfix(zany,4) --> "*?".
postfix(zsome,4) --> "+?".
postfix(zmaybe,4) --> "??".

postfix(any,4) --> "*",\+"?".
postfix(some,4) --> "+", \+"?".
postfix(maybe,4) --> "?", \+"?".
prefix(isnt,4) --> "!".
prefix(ahead,4) --> "&", \+ "&".
 
prefix(every,94) --> "every" ,ws.
prefix(once,94) --> "once",ws.
prefix(not,94) --> "not",ws.
prefix(quote,5) --> "'".
prefix(neg,5) --> "-".
prefix(eval,5) --> "`".

parse(X,S) :- phrase(block(S),X),!. 
