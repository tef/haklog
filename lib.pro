join(A,[],A) :- !.
join(A,B,C) :- string(A), string(B), !, string_concat(A,B,C).
join(A,B,C) :- append(A,B,C),!;append([A],B,C).
to_list(S,L) :- string(S), string_to_list(S,L),!.
expr_to_string(S,S) :- string(S),!.
expr_to_string(V,S) :- \+var(V), V = [], string_to_list(S,[]).
expr_to_string(I,S) :- atom(I), string_to_atom(S,I),!.

expr_to_atom(S,S) :- atom(S),!.
expr_to_atom(I,S) :- string(I), string_to_atom(I,S),!.

cast_to_string(S,O) :- expr_to_string(S,O),!.
cast_to_string(S,O) :- atom_number(S,A), string_to_atom(O,A),!.

cast_to_number(S,S) :- number(S),!.
cast_to_number(S,O) :- expr_to_atom(S,A), atom_number(A,O),!.

reserved([quote,def,fail,and,or,not,ifthen,if,case,conj,disj,eval,every, once,unf,in,
    add,sub,div,mul,eq,le,lt,gt,ge,say,trace,spawn, recv, send
    ]).
make_environment([],[]).
make_environment([W|T],[W-id(W)|To]) :- make_environment(T,To).

spawn(E,C,pid(Id)) :- thread_create(eval(E,[],C,_), Id, []).
send(pid(Id),M) :- ground(M),thread_send_message(Id,[pid(Id)|M]),!.
send(fd(Id),M) :- ground(M),write(Id,M),!.
recv(M) :- thread_get_message(M),!.
read_(fd(I),M) :- ground(I), get_char(I,M).
open_(F,fd(I)) :- open(F, read, I).
close_(fd(F)) :- ground(F),close(F).

empty_string(S) :- string_to_list(S,"").

iterable_pair([_|_],[_|_]) :-!.
iterable_pair(L,R) :- string(L),!, \+string_length(L,0), notnull(R),!.
iterable_pair(L,R) :- string(R),!, \+string_length(R,0), notnull(L),!.
iterable_pair(fd(L),R) :- ground(L),!, (at_end_of_stream(L) -> fail ;notnull(R)),!.
iterable_pair(L,fd(R)) :- ground(R),!, (at_end_of_stream(R) -> fail; notnull(L)),!.

iterable_head_tail(S, H,T) :-  string(S),!,\+string_length(S,0), (var(H);string(H)), (var(T);string(T)),sub_string(S,0,1,A,H), sub_string(S,1,A,0,T).

iterable_head_tail(S, H,T) :-  string(H), string(T),!, string_concat(H,T,S).
iterable_head_tail(S, H,T) :-  string(H), \+var(T), T=[],!,S=H.
iterable_head_tail(fd(I), H,O) :- \+var(I),!,read_(fd(I),H1),!,expr_to_string(H1,H),(at_end_of_stream(I),!,empty_string(O),!; O=fd(I)).
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
notnull(X) :- !, (var(X),!; X=[_|_],!; string(X),!, \+string_length(X,0); X = fd(I), ground(I)).
%notnull(X) :- !, (var(X),!; X=[_|_],!; string(X),!, \+string_length(X,0)).

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
