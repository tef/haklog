hprint(T) :- hprint_(T),!.
hprint_([]).
hprint_([H|T]) :- write('['),hprint_list([H|T]), write(']').
hprint_(call(X,Y)) :- write('('),hprint_(X),write('('),hprint_list(Y),write('))').
hprint_(block(X)) :- write('{'),hprint_block(X),write('}').
hprint_(lambda(X,Y)) :- write('_ '),hprint_list(X),write(' :- ' ),hprint_list(Y).
hprint_(id(X)) :- hprint_(X).
hprint_(X) :- write(X).

hprint_list([]) :- write('[]').
hprint_list([H|T]) :- hprint_(H), hprint_tail(T).
hprint_tail([]).
hprint_tail([H|T]) :- write(' '), hprint_(H),hprint_tail(T).
hprint_block([H|T]) :- hprint_(H), hprint_btail(T).
hprint_btail([]).
hprint_btail([H|T]) :- write(';'),nl, hprint_(H),hprint_btail(T).
