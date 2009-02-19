number(N) --> digit(D0), digits(D), { number_chars(N, [D0|D]) },!.

digits([D|T]) --> digit(D), digits(T).
digits([]) --> [].

digit(D) --> [D], {code_type(D, digit)}.

alnums([H|T]) --> alnum(H), alnums(T).
alnums([]) --> [].

alnum(A) --> [A], {code_type(A, alnum)}.
csym(C) --> [C], {code_type(C, csymf)}.

identifier(id(A)) --> csym(C), alnums(N), {string_to_atom([C|N],A)},!. 
variable(var(A)) --> "$", alnums(N), {string_to_atom(N,A)},!.

ws0 --> [X], {code_type(X, white)}, ws.
ws --> ws0.
ws --> [].

item(E) --> number(E),!.
item(E) --> identifier(E),!.
item(E) --> variable(E),!.

exprl([H|T],N) --> exprn(H,N), ws,!, exprl(T,N).
exprl([],_) --> ";", ws.
exprl([],_) --> [].

exprl(L) --> ws,exprl(L, 100).
expr(L) --> ws,exprn(L,100).

exprn(O,N1) --> identifier(id(X)) , command(N), { N < N1 }, ws0, exprl(L,N), follow(command(X,L), O, N1). 
exprn(O,N1) --> prefix(R,Op, N), { N =< N1 }, exprn(R,N), !, follow(Op, O, N1).
exprn(O,N1) --> "(" , exprn(Op, 100) , ")" , follow(Op, O ,N1).
exprn(O,N1) --> "[" ,  exprl(Op, 90) , "]" , follow(Op, O ,N1).
exprn(O,N1) --> "{" , exprl(Op, 100) , "}" , follow(Op, O ,N1).
exprn(O,N) --> ws, item(L), follow(L,O,N).

follow(L,O,N1) --> "[" ,  exprl(Op, 90) , "]" , follow(index(L,Op), O ,N1).
follow(L,O,N1) --> ws, infix(L,R,Op,As,N), {assoc(As,N, N1)},ws, exprn(R,N),!, follow(Op, O, N1).
follow(L,O,N1) --> ws, postfix(L,Op,N), {N =< N1}, follow(Op, O, N1).
follow(O,O,_) --> ";",[].
follow(O,O,_) --> [].

assoc(right, A, B) :-  A =< B.
assoc(left, A, B) :- A < B.

command(90) --> [].

infix(A,B,def(A,B), right, 99) --> ":-".
infix(A,B,A=B, left,90) --> "=".
infix(A,B,A=<B,right,60) --> ">=".
infix(A,B,A>=B,right,60) --> "=<".
infix(A,B,A<B,right,60) --> ">".
infix(A,B,A>B,right,60) --> "<".
infix(A,B,(A,B),right,55) --> ",".
infix(A,B,A+B,right,50) --> "+".
infix(A,B,A-B,right,50) --> "-".
infix(A,B,A*B,right,45) --> "*".
infix(A,B,A/B,right,45) --> "/".
infix(A,B,conj(A,B),right,95) --> "&&".
infix(A,B,and(A,B),right,95) --> "and".
infix(A,B,disj(A,B),right,96) --> "||".
infix(A,B,or(A,B),right,96) --> "or".
infix(A,B,in(A,B),right,60) --> "in".

prefix(A,not(A),10) --> "!".
prefix(A,quote(A),10) --> "'".
postfix(A,post(A),5) --> "?".


exec(X,O) :-
    phrase(expr(S),X),!,
    eval(S,O).


eval(X,X) :- number(X); X = [].

eval(quote(X), X).
eval(X+Y,Z) :- Z is X+Y.
eval(X*Y,Z) :- Z is X*Y.
eval(X-Y,Z) :- Z is X-Y.
eval(X/Y,Z) :- Z is X/Y.




