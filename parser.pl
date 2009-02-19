number(N) --> digit(D0), digits(D), { number_chars(N, [D0|D]) }.

digits([]) --> [].
digits([D|T]) --> digit(D), digits(T).

digit(D) --> [D], {code_type(D, digit)}.

alnums([]) --> [].
alnums([H|T]) --> alnum(H), alnums(T).

alnum(A) --> [A], {code_type(A, alnum)}.
csym(C) --> [C], {code_type(C, csymf)}.

identifier(A) --> csym(C), alnums(N), {string_to_atom([C|N],A)}. 
variable(A) --> "$", alnums(N), {string_to_atom(N,A)}. 

ws0 --> [X], {code_type(X, white)}.
ws --> ws0, ws.
ws --> [].

item(E) --> number(E).
item(E) --> identifier(E).
item(E) --> variable(E).

expr(S) --> sexpr(S).
expr(L+R) --> item(L), "+", expr(R).
expr(L*R) --> item(L), "*", expr(R).
expr(I) --> item(I).

exprl([]) --> [].
exprl([H|T]) --> expr(H), ws, exprl(T).

sexpr(S) --> "(", identifier(I), ws, exprl(C), ")", { S =.. [I|C] }.
