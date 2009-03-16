% strucural unification

% warning: pattern matching has been already written twice
% and suffers from constant tweaking as I experimentally discover
% the semantics

% Essentially it works from left to right searching for things to match
% variables are passed onto unify_var
% any iterable is matched with another, - and the head is matched then the tail.
% for patterns, ones on the left are used first

% confusing example
% [x* 1 2 3] = [1 2 3 y*]
% this matches x* = [1 2 3 y*] first and then [1 2 3] = []
% then succeeds with x = [1 2 3] and y = [1 2 3]
% another match is also possible
% x* matches [] and y matches []

%unify(+Env,-Env,+Left,+Right,-Capture)
%unify(_,_,L,R,_) :- writef("\nunify: (%w) (%w)\n",[L,R]), fail.

unify(E,Eo,L,R,O) :- (var(L) -> (var(R) -> (L=R, L=O, E=Eo,!);(!,unify_var(E,Eo,L,R),L=O));var(R), !, unify_var(E,Eo,R,L),R=O).
unify(E,E,[],[],[]) :- !.

unify(_,_,[],[H|_],_) :- var(H) , !, fail.
unify(_,_,[H|_],[],_) :- var(H) , !, fail.

unify(E,Eo,L,R,O) :- iterable_pair(L,R), iterable_head_tail(L,Lh,Lt), iterable_head_tail(R,Rh,Rt),( (var(Lh),!,unify_var(E,E1,Lh,Rh), unify(E1,Eo,Lt,Rt,Ot), iterable_head_tail(O,Lh,Ot)); (var(Rh),!,unify_var(E,E1,Rh,Lh), unify(E1,Eo,Lt,Rt,Ot), iterable_head_tail(O,Rh,Ot))).

unify(E,Eo,L,call(unf,A),C) :-!,eval(E,E1,call(unf,A),O),unify(E1,Eo,L,O,C).
unify(E,Eo,call(unf,A),R,C) :-!,eval(E,E1,call(unf,A),O),unify(E1,Eo,O,R,C).

unify(E,Eo,[p(Pl,Al)|Lt],[p(Pr,Ar)|Rt],[p(Po,Ao)|Ot]) :- pattern_combine(Pl,Pr,Po), arguments_combine(Al,Ar,Ao), !, Al=Ar, unify(E,Eo,Lt,Rt,Ot).
unify(E,Eo,[p(P,A)|Lt],Ro,R) :- \+var(A), pattern_eats(P,Ro), !, unify_var(E,E1,R,Ro), unify_p_l(P,E1,Eo,A,Lt,R,_).
unify(E,Eo,Lo,[p(P,A)|Rt],L) :- \+var(A), pattern_eats(P,Lo), !, unify_var(E,E1,L,Lo), unify_p_l(P,E1,Eo,A,Rt,L,_).
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

arguments_combine(X,Y,X) :- var(X), !,var(Y), X=Y,!.
arguments_combine(X,Y,X) :- \+ var(X), \+ var(Y) , X=Y.

pattern_combine(X,X,X).
pattern_combine(X,some,some) :- member(X,[zsome,any,zany]).
pattern_combine(some,X,some) :- member(X,[zsome,any,zany]).
pattern_combine(X,zsome,zsome) :- member(X,[any,zany]).
pattern_combine(zsome,X,zsome) :- member(X,[any,zany]).
pattern_combine(any,zany,any).
pattern_combine(zany,any,any).
pattern_combine(maybe,zmaybe,maybe).
pattern_combine(zmaybe,maybe,maybe).

pattern_eats(bind,_).
pattern_eats(_,[p(bind,_)|_]) :- !, fail.
pattern_eats(any,_).
pattern_eats(_,[p(any,_)|_]) :- !, fail.
pattern_eats(zany,_).
pattern_eats(_,[p(zany,_)|_]) :- !, fail.
pattern_eats(some,_).
pattern_eats(_,[p(some,_)|_]) :- !, fail.
pattern_eats(zsome,_).
pattern_eats(_,[p(zsome,_)|_]) :- !, fail.
pattern_eats(maybe,_).
pattern_eats(_,[p(maybe,_)|_]) :- !, fail.
pattern_eats(zmaybe,_).
pattern_eats(_,[p(zmaybe,_)|_]) :- !, fail.
pattern_eats(isnt,_).
pattern_eats(_,[p(isnt,_)|_]) :- !, fail.
pattern_eats(ahead,_).
pattern_eats(_,[p(ahead,_)|_]).


%unify_var(+Env,-Env,+Var,+Expr)
% unify an expression with a variable

unify_var(E,E,X,Y) :- var(Y),!,X=Y.
unify_var(E,Eo,[H|To],[H|T]) :-  var(H),!, unify_var(E,Eo,To,T).
unify_var(E,E,[],[]) :-!.
unify_var(E,Eo,O,p(P,A)) :- !,  unify_var_p(P,E,Eo,A,O),!.
unify_var(E,Eo,O,[p(P,A)|T]) :- !,(unify_var_p_l(P,E,E1,A,Ho),!,unify_var(E1,Eo,To,T), join(Ho,To,O)); (unify_var_p_l(P,E,E1,A,Ho), unify_var(E1,Eo,To,T), join(Ho,To,O),!).

unify_var(E,Eo,[Ho|To],[H|T]) :- !,unify_var(E,E1,Ho,H), unify_var(E1,Eo,To,T).
unify_var(E,Eo,L,call(unf,A)) :-!,eval(E,E1,call(unf,A),O),unify_var(E1,Eo,L,O).
unify_var(E,E,call(def,T), call(def,T)) :-!.
unify_var(E,Eo,call(Ho,To), call(H,T)) :-!,unify_var(E,E1,Ho,H),unify_var(E1,Eo,To,T).
unify_var(E,E,lambda(H,T), lambda(H,T)) :-!.
unify_var(E,Eo,O,block(X)) :- !, eval_block(E,E1,X,Xo), unify_var(E1,Eo,O,Xo).
unify_var(E,E,X,X) :- !.

% here be dragons 

%unify_var_p(+Pattern,+Env,-Env,+Args,+Right)
%unify a pattern with a right hand side, only ones we expect out of a list context
%are here
unify_var_p(maybe,E,Eo,X,R) :- !, unify_var_p_l(maybe,E,Eo,X,[R]).
unify_var_p(zmaybe,E,Eo,X,R) :- !, unify_var_p_l(zmaybe,E,Eo,X,[R]).
unify_var_p(P,E,Eo,X,R) :- !, unify_var_p_l(P,E,Eo,X,R).

%unify_var_p_l(+Pattern,+Env,-Env,+Args,+Var)
% reminder- things matched to patterns are unified with a var
% so [x*] = [ 1 2 [1 2 3]* ], 1 2 [1 2 3]* is unified with a var first
% and these functions unpack patterns with iterable arguments 
% becomes [x*] = [1 2 1 2 3]

% 
unify_var_p_l(P,E,E,X,[p(P,X)]) :- var(X),!.
unify_var_p_l(bind,E,Eo,[L1,L2],R) :-   !, unify_var(E,E1,R,L1), unify_var(E1,Eo,L2,R).
unify_var_p_l(choice,E,Eo,[L1|L2],R) :-   !, (unify_var(E,Eo,R,L1); unify_var_p_l(choice,E,Eo,L2,R)).
unify_var_p_l(ahead,E,E,X,[p(ahead,X)]) :- !.
unify_var_p_l(isnt,E,E,X,[p(isnt,X)]) :- !.
unify_var_p_l(any,E,Eo,L,R) :-   unify_p_l(any,E,E1,_,[],L,L1),!,unify_var(E1,Eo,R,L1).
unify_var_p_l(zany,E,Eo,L,R) :-   unify_p_l(zany,E,E1,_,[],L,L1),!,unify_var(E1,Eo,R,L1).
unify_var_p_l(some,E,Eo,L,R) :-   unify_p_l(some,E,E1,_,[],L,L1),!,unify_var(E1,Eo,R,L1).
unify_var_p_l(zsome,E,Eo,L,R) :-   unify_p_l(zsome,E,E1,_,[],L,L1),!,unify_var(E1,Eo,R,L1).
unify_var_p_l(maybe,E,Eo,L,R) :-   unify_p_l(maybe,E,E1,_,[],L,L1),!,unify_var(E1,Eo,R,L1).
unify_var_p_l(zmaybe,E,Eo,L,R) :-   unify_p_l(zmaybe,E,E1,_,[],L,L1),!,unify_var(E1,Eo,R,L1).
% matches things like 1* - this general case is possibly a bad thing
unify_var_p_l(P,E,E,X,[p(P,X)]).

%unify_p(+Pattern,+Env,-Env,+Args,+Right,-Capture)
unify_p(bind,E,Eo,[L1,L2],R,O) :-  !, unify(E,E1,L1,R,O),unify_var(E1,Eo,L2,O).
unify_p(choice,E,Eo,[L1|L2],R,C) :- !, (unify(E,Eo,L1,R,C) ; unify_p(choice,E,Eo,L2,R,C)).
unify_p(class,E,E,L,R,R) :- !,class_match(L,R).
unify_p(crange,E,E,L,R,R) :- !,crange_match(L,R).

%unify_p_l(+Pattern,+Env,-Env,+Args,+LeftTail,+Right,-Capture)
unify_p_l(bind,E,Eo,[X,N],Lt,R,C):- \+var(X), X=p(P,A),!,unify_p_l(P,E,E1,A,Lt,R,C),unify(E1,Eo,N,C,_).
unify_p_l(bind,E,Eo,[L1,L2],Lt,R,O) :- iterable_head_tail(R,Rh,Rt), !, unify(E,E1,L1,Rh,O),unify(E1,E2,Lt,Rt,_),unify_var(E2,Eo,L2,O).

unify_p_l(choice,E,Eo,[X|L2],Lt,R,C):- \+var(X), X=p(P,A),!,((unify_p_l(P,E,Eo,A,Lt,R,C)) ; (unify_p_l(choice,E,Eo,L2,Lt,R,C))).
unify_p_l(choice,E,Eo,[L1|L2],Lt,R,O) :- iterable_head_tail(R,Rh,Rt),!, ((unify(E,E1,L1,Rh,O),unify(E1,Eo,Lt,Rt,_)); (unify_p_l(choice,E,Eo,L2,Lt,R,O))).

unify_p_l(class,E,Eo,L,Lt,R,Rh) :- iterable_head_tail(R,Rh,_),!,class_match(L,Rh), unify(E,Eo,Lt,R,_).
unify_p_l(crange,E,Eo,L,Lt,R,Rh) :- iterable_head_tail(R,Rh,_),!,crange_match(L,Rh), unify(E,Eo,Lt,R,_).

unify_p_l(ahead,E,Eo,L,Lt,R,O) :- iterable_head_tail(R,Rh,_),!,unify(E,E1,L,Rh,O), unify(E1,Eo,Lt,R,_).
 
unify_p_l(isnt,E,Eo,L,Lt,R,Rh) :- iterable_head_tail(R,Rh,_), !,\+ unify(E,_,L,Rh,_),!,unify(E,Eo,Lt,R,_).

% here we have one rule for any on a variable or an iterable
unify_p_l(any,E,Eo,A,To,R,C) :- (var(A); iterable_pair(A,R); null(A),null(R)),!,iterable_any(R,Rh,Rt) , unify(E,E1,A,Rh,C), unify(E1,Eo,To,Rt,_).
% and another for matching things like 1*
unify_p_l(any,E,Eo,A,To,R,C) :- iterable_head_tail(R,Rh,Rt),!, unify(E,E1,A,Rh,Ch), unify_p_l(any,E1,Eo,A,To,Rt,Ct), iterable_head_tail(C,Ch,Ct).
unify_p_l(any,E,Eo,_,To,R,C) :- empty(R,C), unify(E,Eo,To,R,_).

unify_p_l(zany,E,Eo,A,To,R,C) :- (var(A); iterable_pair(A,R); null(A), null(R)),!,iterable_zany(R,Rh,Rt) , unify(E,E1,A,Rh,C), unify(E1,Eo,To,Rt,_).

unify_p_l(some,E,Eo,A,To,R,C) :- (var(A);iterable_pair(A,R)),!,iterable_some(R,Rh,Rt) , unify(E,E1,A,Rh,C), unify(E1,Eo,To,Rt,_).

unify_p_l(zsome,E,Eo,A,To,R,C) :- (var(A);iterable_pair(A,R)),!,iterable_zsome(R,Rh,Rt) , unify(E,E1,A,Rh,C), unify(E1,Eo,To,Rt,_).

unify_p_l(maybe,E,Eo,A,T,R,H) :- iterable_head_tail(R,H,To), unify(E,E1,A,H,_), unify(E1,Eo,T,To,_).
unify_p_l(maybe,E,Eo,_,T,To,_):- unify(E,Eo,T,To,_).
unify_p_l(zmaybe,E,Eo,_,T,To,_):- unify(E,Eo,T,To,_).
unify_p_l(zmaybe,E,Eo,A,T,R,H) :- iterable_head_tail(R,H,To), unify(E,E1,A,H,_), unify(E1,Eo,T,To,_).
