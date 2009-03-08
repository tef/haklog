% strucural unification
join(A,[],A) :- !.
join(A,B,C) :- string(A), string(B), !, string_concat(A,B,C).
join(A,B,C) :- append(A,B,C),!;append([A],B,C).
to_list(S,L) :- string(S), string_to_list(S,L),!.
expr_to_string(S,S) :- string(S),!.
expr_to_string(V,S) :- \+var(V), V = [], string_to_list(S,[]).
expr_to_string(I,S) :- atom(I), string_to_atom(S,I),!.

%unify(_,_,L,R,_) :- writef("\nunify: (%w) (%w)\n",[L,R]), fail.

unify(E,Eo,L,R,O) :- (var(L) -> (var(R) -> (L=R, E=Eo,!);(!,unify_var(E,Eo,L,R),L=O));var(R), !, unify_var(E,Eo,R,L),R=O).
unify(E,E,[],[],[]) :- !.

unify(_,_,[],[H|_],_) :- var(H) , !, fail.
unify(_,_,[H|_],[],_) :- var(H) , !, fail.

unify(E,Eo,L,R,L) :- iterable_head_tail(R,p(P,A),Rt), var(L), !, unify_var_p_l(P,E,Eo,A,Rt,L).
unify(E,Eo,L,R,R) :- iterable_head_tail(L,p(P,A),Lt),  var(R), !, unify_var_p_l(P,E,Eo,A,Lt,R). 
unify(E,Eo,L,R,O) :- iterable_pair(L,R), iterable_head_tail(L,Lh,Lt), iterable_head_tail(R,Rh,Rt),( (var(Lh),!,unify_var(E,E1,Lh,Rh), unify(E1,Eo,Lt,Rt,Ot), iterable_head_tail(O,Lh,Ot)); (var(Rh),!,unify_var(E,E1,Rh,Lh), unify(E1,Eo,Lt,Rt,Ot), iterable_head_tail(O,Rh,Ot))).

unify(E,Eo,[p(P,A)|Lt],Ro,R) :-  !, unify_var(E,E1,R,Ro), unify_p_l(P,E1,Eo,A,Lt,R,_).
unify(E,Eo,Lo,[p(P,A)|Rt],L) :-  !, unify_var(E,E1,L,Lo), unify_p_l(P,E1,Eo,A,Rt,L,_).
unify(E,Eo,p(P,A),Ro,O) :-  !, unify_var(E,E1,R,Ro), unify_p(P,E1,Eo,A,R,O).
unify(E,Eo,Lo,p(P,A),O) :-  !, unify_var(E,E1,L,Lo), unify_p(P,E1,Eo,A,L,O).

unify(E,Eo,L,R,O) :- iterable_pair(L,R), !, iterable_head_tail(L,Ho,To), iterable_head_tail(R,H,T),!, unify(E,E1,Ho,H,Oh),unify(E1,Eo,To,T,Ot), iterable_head_tail(O,Oh,Ot).
unify(E,Eo,call(Ho,To), call(H,T),call(Oh,Ot)) :-!,unify(E,E1,Ho,H,Oh),unify(E1,Eo,To,T,Ot).
unify(E,Eo,lambda(Ho,To), lambda(H,T),lambda(Oh,Ot)) :-!,unify(E,E1,H,Ho,Oh), unify(E1,Eo,T,To,Ot).
unify(E,Eo,block(X),O,J) :- !, eval_block(E,E1,X,Xo), unify(E1,Eo,Xo,O,J).
unify(E,Eo,O,block(X),J) :- !, eval_block(E,E1,X,Xo), unify(E1,Eo,O,Xo,J).
unify(E,E,X,X,X) :- !.
unify(E,E,S,A,S) :- string(S),!, expr_to_string(A,S1),!, S1=S.
unify(E,E,A,S,S) :- string(S),!, expr_to_string(A,S1),!, S1=S.

unify_var(E,E,X,Y) :- var(Y),!,X=Y.
unify_var(E,Eo,[H|To],[H|T]) :-  var(H),!, unify_var(E,Eo,To,T).
unify_var(E,E,[],[]) :-!.
unify_var(E,Eo,O,p(P,A)) :- !, var(A) *-> unify_var_p(P,E,Eo,A,O); (unify_var_p(P,E,Eo,A,O),!).
unify_var(E,Eo,O,[p(P,A)|T]) :- !, var(A) *-> (unify_var_p_l(P,E,E1,A,[],Ho),  unify_var(E1,Eo,To,T), join(Ho,To,O)); (unify_var_p_l(P,E,E1,A,[],Ho), unify_var(E1,Eo,To,T), join(Ho,To,O),!).

unify_var(E,Eo,[Ho|To],[H|T]) :- !,unify_var(E,E1,Ho,H), unify_var(E1,Eo,To,T).
unify_var(E,E,call(def,T), call(def,T)) :-!.
unify_var(E,Eo,call(Ho,To), call(H,T)) :-!,unify_var(E,E1,Ho,H),unify_var(E1,Eo,To,T).
unify_var(E,E,lambda(H,T), lambda(H,T)) :-!.
unify_var(E,Eo,O,block(X)) :- !, eval_block(E,E1,X,Xo), unify_var(E1,Eo,O,Xo).
unify_var(E,E,X,X) :- !.

%unify_var_p(concat,E,Eo,[L1,L2],R) :-   !, unify_var(E,E1,A,L1), unify_var(E1,Eo,B,L2), concat(A,B,R). 
unify_var_p(maybe,E,Eo,X,R) :- !, unify_var_p_l(maybe,E,Eo,X,[],[R]).
unify_var_p(zmaybe,E,Eo,X,R) :- !, unify_var_p_l(zmaybe,E,Eo,X,[],[R]).
unify_var_p(P,E,Eo,X,R) :- !, unify_var_p_l(P,E,Eo,X,[],R).

unify_var_p_l(P,E,Eo,X,L,[p(P,X)|R]) :- var(X),!, unify_var(E,Eo,R,L).
unify_var_p_l(bind,E,Eo,[L1,L2],Lt,R) :-   !, unify_var(E,E1,R,L1), unify_var(E1,E2,L2,R), unify(E2,Eo,Lt,[],_).
%unify_var_p_l(concat,E,Eo,[L1,L2],Lt,[R|Rt]) :-   !, unify_var(E,E1,A,L1), unify_var(E1,E2,B,L2), concat(A,B,R), unify(E2,Eo,Lt,Rt,_).
unify_var_p_l(choice,E,Eo,[L1,L2],Lt,R) :-   !, ((unify_var(E,E1,R,L1),unify(E1,Eo,Lt,[],_)); (unify_var(E,E1,R,L2), unify(E1,Eo,Lt,[],_))).
unify_var_p_l(ahead,E,Eo,L,Lt,R) :-   !,unify_var(E,E1,R,L), unify_var(E1,Eo,R,Lt).
unify_var_p_l(isnt,E,Eo,L,Lt,R) :-   !,\+ unify_var(E,_,[L],R), unify_var(E,Eo,R,Lt).
unify_var_p_l(any,E,Eo,L,Lt,R) :-   !,((unify_var(E,E1,R,L), unify(E1,Eo,Lt,[],_)); unify_var(E,Eo,R,Lt)).
unify_var_p_l(some,E,Eo,L,Lt,R) :-   !,unify_var(E,E1,R,L), unify(E1,Eo,Lt,[],_).
unify_var_p_l(maybe,E,Eo,L,Lt,[R|Rt]) :-  !,((unify_var(E,E1,R,L), unify(E1,Eo,Lt,Rt,_)); unify(E,Eo,Lt,[R|Rt],_)). 
unify_var_p_l(zany,E,Eo,L,Lt,R) :-   !,( unify_var(E,Eo,R,Lt);(unify_var(E,E1,R,L), unify(E1,Eo,Lt,[],_))).
unify_var_p_l(zsome,E,Eo,L,Lt,R) :-   !,unify_var(E,E1,R,L), unify(E1,Eo,Lt,[],_).
unify_var_p_l(zmaybe,E,Eo,L,Lt,[R|Rt]) :-  !,(unify(E,Eo,Lt,[R|Rt],_); (unify_var(E,E1,R,L), unify(E1,Eo,Lt,Rt,_))). 

unify_p(bind,E,Eo,[L1,L2],R,O) :-  !, unify(E,E1,L1,R,O),unify_var(E1,Eo,L2,O,_).
unify_p(choice,E,Eo,[L1,L2],R,C) :- !, (unify(E,Eo,L1,R,C) ; unify(E,Eo,L2,R,C)).

unify_p_l(bind,E,Eo,[p(P,A),N],Lt,R,C):-  !,unify_p_l(P,E,E1,A,Lt,R,C),unify(E1,Eo,N,C,_).
unify_p_l(bind,E,Eo,[L1,L2],Lt,R,O) :- iterable_head_tail(R,Rh,Rt), !, unify(E,E1,L1,Rh,O),unify(E1,E2,Lt,Rt,_),unify_var(E2,Eo,L2,O,_).

unify_p_l(choice,E,Eo,[L1,L2],Lt,R,O) :- iterable_head_tail(R,Rh,Rt),!, ((unify(E,E1,L1,Rh,O),unify(E1,Eo,Lt,Rt,_)); (unify(E,E1,L2,Rh,O), unify(E1,Eo,Lt,Rt,_))).

unify_p_l(ahead,E,Eo,L,Lt,R,O) :- iterable_head_tail(R,Rh,_),!,unify(E,E1,L,Rh,O), unify(E1,Eo,Lt,R,_).

unify_p_l(isnt,E,Eo,L,Lt,R,Rh) :- iterable_head_tail(R,Rh,_), !,\+ unify(E,_,L,Rh,_),!,unify(E,Eo,Lt,R,_).

unify_p_l(any,E,Eo,A,To,R,C) :- (var(A); iterable_pair(A,R)),!,iterable_any(R,Rh,Rt) , unify(E,E1,A,Rh,C), unify(E1,Eo,To,Rt,_).
unify_p_l(any,E,Eo,A,To,R,C) :- list(A), null(R),!, unify(E,E1,A,R,C), unify(E1,Eo,To,R,_).
unify_p_l(any,E,Eo,_,To,R,R) :- null(R),!, unify(E,Eo,To,R,_).
unify_p_l(any,E,Eo,A,To,R,C) :- (iterable_head_tail(R,Rh,Rt), unify(E,E1,A,Rh,Ch), unify_p_l(any,E1,Eo,A,To,Rt,Ct), iterable_head_tail(C,Ch,Ct)) ; (C = [],unify(E,Eo,To,R,_)).

unify_p_l(zany,E,Eo,A,To,R,C) :- (var(A); iterable_pair(A,R)),!,iterable_zany(R,Rh,Rt) , unify(E,E1,A,Rh,C), unify(E1,Eo,To,Rt,_).
unify_p_l(zany,E,Eo,A,To,R,C) :- (C = [],unify(E,Eo,To,R,_));(iterable_head_tail(R,Rh,Rt), unify(E,E1,A,Rh,Ch), unify_p_l(zany,E1,Eo,A,To,Rt,Ct), iterable_head_tail(C,Ch,Ct)).

unify_p_l(some,E,Eo,A,To,R,C) :- (var(A);iterable_pair(A,R)),!,iterable_some(R,Rh,Rt) , unify(E,E1,A,Rh,C), unify(E1,Eo,To,Rt,_).
unify_p_l(some,E,Eo,A,To,R,C) :- (iterable_head_tail(R,Rh,Rt), unify(E,E1,A,Rh,Ch), unify_p_l(some,E1,Eo,A,To,Rt,Ct), iterable_head_tail(C,Ch,Ct)) ; (C = [],unify(E,Eo,To,R,_)).

unify_p_l(zsome,E,Eo,A,To,R,C) :- (var(A);iterable_pair(A,R)),!,iterable_zsome(R,Rh,Rt) , unify(E,E1,A,Rh,C), unify(E1,Eo,To,Rt,_).
unify_p_l(zsome,E,Eo,A,To,R,C) :- (iterable_head_tail(R,Rh,Rt), unify(E,E1,A,Rh,Ch), unify_p_l(zsome,E1,Eo,A,To,Rt,Ct), iterable_head_tail(C,Ch,Ct)) ; (C = [],unify(E,Eo,To,R,_)).

unify_p_l(maybe,E,Eo,A,T,R,H) :- iterable_head_tail(R,H,To), unify(E,E1,A,H,_), unify(E1,Eo,T,To,_).
unify_p_l(maybe,E,Eo,_,T,To,_):- unify(E,Eo,T,To,_).
unify_p_l(zmaybe,E,Eo,_,T,To,_):- unify(E,Eo,T,To,_).
unify_p_l(zmaybe,E,Eo,A,T,R,H) :- iterable_head_tail(R,H,To), unify(E,E1,A,H,_), unify(E1,Eo,T,To,_).

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


