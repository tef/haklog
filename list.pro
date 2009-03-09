join(A,[],A) :- !.
join(A,B,C) :- string(A), string(B), !, string_concat(A,B,C).
join(A,B,C) :- append(A,B,C),!;append([A],B,C).
to_list(S,L) :- string(S), string_to_list(S,L),!.
expr_to_string(S,S) :- string(S),!.
expr_to_string(V,S) :- \+var(V), V = [], string_to_list(S,[]).
expr_to_string(I,S) :- atom(I), string_to_atom(S,I),!.

iterable_pair([_|_],[_|_]) :-!.
iterable_pair(L,R) :- string(L),!, \+string_length(L,0), notnull(R),!.
iterable_pair(L,R) :- string(R),!, \+string_length(R,0), (var(L);L=[_|_]),!.

iterable_head_tail(S, H,T) :-  string(S),!,\+string_length(S,0), (var(H);string(H)), (var(T);string(T)),sub_string(S,0,1,A,H), sub_string(S,1,A,0,T).

iterable_head_tail(S, H,T) :-  string(H), string(T),!, string_concat(H,T,S).
iterable_head_tail(S, H,T) :-  string(H), \+var(T), T=[],!,S=H.
iterable_head_tail([H|T],H,T) :-!.

iterable_some(I,O,Lo) :- iterable_head_tail(I,H,T), iterable_any(T,To,Lo), iterable_head_tail(O,H,To).
iterable_any(I,O,Lo) :- iterable_head_tail(I,H,T),iterable_any(T,To,Lo), iterable_head_tail(O,H,To).
iterable_any(I,E,I) :- empty(I,E).

iterable_zany(I,E,I) :- empty(I,E).
iterable_zany(I,O,Lo) :- iterable_head_tail(I,H,T),iterable_zany(T,To,Lo), iterable_head_tail(O,H,To).

iterable_zsome(I,O,Lo) :- iterable_head_tail(I,H,T), iterable_zany(T,To,Lo), iterable_head_tail(O,H,To).

list([]). list([_|_]).

empty([],[]) :-!.
empty([_|_],[]) :-!.
empty(S,S0) :- string(S),!,string_to_list(S0,[]).
null(X) :- \+var(X) , (X=[]; (string(X), string_length(X,0))),!.
notnull(X) :- !, (var(X),!; X=[_|_],!; (string(X), \+string_length(X,0))).

concat(A,B,O) :- to_string(A,A1), to_string(B,B1), !, string_concat(A1,B1,O).
concat(A,B,O) :- \+ var(O), (var(A); var(B)), !, string_concat(A,B,O).
concat(p(concat,[A1,A2]),B,O) :- !, string_concat(A,B,O), concat(A1,A2,A).
concat(A,p(concat,[B1,B2]),O) :- !, string_concat(A,B,O), concat(B1,B2,B).

to_string(A,A) :- !,string(A).
to_string(A,S) :- !,atom(A), string_to_atom(A,S).

class_match(X,S) :- string(S), string_to_list(S,L), !, class_match(X,L).
class_match(X,S) :- atom(S), atom_codes(S,L), !, class_match(X,L).
class_match(w,S) :- code_type(S,csymf).
class_match('W',S) :- \+code_type(S,csymf).
class_match(d,S) :- code_type(S,digit).
class_match('D',S) :- \+code_type(S,digit).
class_match(s,S) :- code_type(S,white).
class_match('S',S) :- \+code_type(S,white).
crange_match(X,S) :- string(S), string_to_list(S,L), !, crange_match(X,L).
crange_match(X,S) :- atom(S), atom_codes(S,L), !, crange_match(X,L).
crange_match([L,R],[S]) :- L =< S, S =<R.
