evalone(Ei,Eo,X,O) :- eval(Ei,Eo,X,O),!.

eval(E,E,X,X) :- var(X),!.
eval(_,_,call(id(fail),_),_) :- !,fail.
eval(_,_,id(fail),_) :- !,fail.
eval(E,E,[],[]) :-!.
eval(Ei,Eo,block(X),O) :-!, eval_block(Ei,Eo,X,O).
eval(E,E,call(quote,[X]), Xo) :- !, eval_quote(X,Xo).
eval(Ei,Eo,id(X),O) :- variable(Ei,Eo,bind,X,O),!.
eval(E,E,lambda(X,Y),lambda(X,Y)) :-!. % this is here so when X is defined as call(disj...) 
eval(Ei,Eo,call(def,[call(N,A)|Y]),lambda(Ao,Yo)) :- 
    bind_lambda_vars(Ei,A,Ao,[],Av), !, bind_lambda_vars(Ei,Y,Yo,Av,_), !,
    variable(Ei,Eo,def,N,lambda(Ao,Yo)),!.
eval(Ei,Eo,call(def,[id(N)|Y]),lambda([],Yo)) :- 
    bind_lambda_vars(Ei,Y,Yo,[],_), !,
    variable(Ei,Eo,def,N,lambda([],Yo)),!.
eval(E,Eo,call(and,[X,Y]),Z) :-!, evalone(E,E1,X,_),!,eval(E1,Eo,Y,Z).
eval(E,Eo,call(or,[X,Y]),Z) :- !,(evalone(E,Eo,X,Z);!, eval(E,Eo,Y,Z)).
eval(E,Eo,call(xor,[X,Y]),Z) :- !,((eval(E,Eo,X,Z) *-> true);eval(E,Eo,Y,Z)).
eval(E,E,call(not,X),[]) :- \+ eval(E,_,X,_), !.
eval(E,Eo,call(ifthen,[X,Y]),Z) :- !,((evalone(E,E1,X,_) -> (!, eval(E1,Eo,Y,Z))); !,Z =[]).
eval(E,Eo,call(if,X),Z) :- !,eval_if(E,Eo,X,Z). 
eval(E,Eo,call(case,[X|T]),Z) :- !, bind_vars(E,E1,X,X1), eval_case(E1,Eo,X1,T,Z). 
eval(E,Eo,call(conj,X),Z) :- !,eval_conj(E,Eo,X,[],Z).
eval(_,_,call(disj,[]),_) :- !, fail.
eval(E,Eo,call(disj,[H|T]),Z) :- !,(eval(E,E1,H,Z) ; !,eval(E1,Eo,call(disj,T),Z)).
eval(E,Eo,call(eval,X),Z) :- !,bind_vars(E,E1,X,X1),!, eval(E1,Eo,X1,[Z]).
eval(E,Eo,call(every,X),Z) :- !,findall(A,eval_block(E,Eo,X,A),Z),!.
eval(E,Eo,call(once,T),A) :- !,eval_block(E,Eo,T,A),!.
eval(E,Eo,call(unf,[A,B]),B1) :- !,bind_vars(E,E1,A,A1),!, bind_vars(E1,E2,B,B1), !,unify(E2,Eo,A1,B1).
eval(E,Eo,call(in,[A,B]),A1) :- !,bind_vars(E,E1,A,A1), !,eval(E1,Eo,B,A1).
eval(E,Eo,call(lambda(A,C),T),O) :- bind_vars(E,Eo,T,To),eval_fun(E,[lambda(A,C)],To,O).
eval(E,Eo,call(H,T),O) :- 
    atom(H) -> (
        (builtin(H),!, eval(E,Eo,T,To), apply(H,To,O)); 
        (!,defined(E,H,F), \+ F = [],bind_vars(E,Eo,T,To),!,eval_fun(E,F,To,O))
    );
    (H = lambda(_,_), !, bind_vars(E,Eo,T,To),!,eval_fun(E,H,To,O));
    (!,eval(E,E1,H,Ho),  bind_vars(E1,Eo,T,To),!,eval_fun(E,Ho,To,O)).

eval(E,Eo,[H|T],[Ho|To]) :- eval(E,E1,H,Ho), eval(E1,Eo,T,To).
eval(E,E,X,X) :- number(X),!.
eval(E,E,X,X) :- atom(X),!.
eval(E,E,X,X) :- var(X),!.

eval_quote(id(X),X) :- !.
eval_quote([H|T], [Ho|To]) :-!, eval_quote(H,Ho),!, eval_quote(T,To),!.
eval_quote(call(def,T), call(def,T)) :-!.
eval_quote(call(H,T), call(H,To)) :-!, eval_quote(T,To),!.
eval_quote(X,X) :- !.

eval_case(E,E,_,[],[]).
eval_case(Ei,Eo,A,[call(ifthen,[X,Y])|T],O) :- !, ( ( bind_vars(Ei,E1,X,X1), !, unify(E1,E2,A,X1)) *-> eval(E2,Eo,Y,O) ; eval_case(Ei,Eo,A,T,O)).
eval_case(Ei,Eo,A,[E],Ev) :- !, bind_vars(Ei,E1,E,Ev),!, unify(E1,Eo,A,Ev).

eval_if(E,E,[],[]).
eval_if(Ei,Eo,[call(ifthen,[X,Y])|T],O) :- !, (evalone(Ei,E1,X,_) -> (!, eval(E1,Eo,Y,O))); eval_if(Ei,Eo,T,O). 
eval_if(Ei,Eo,[E],O) :- !, eval(Ei,Eo,E,O).

eval_block(E,E,[],[]). 
eval_block(E,Eo,[H],O) :- !, eval(E,Eo,H,O).
eval_block(E,Eo,[H|T],X) :-  eval(E,E1,H,_), !,eval_block(E1,Eo,T,X).

eval_conj(E,E,[],X,X). 
eval_conj(E,Eo,[H|T],_,X) :-  eval(E,E1,H,O), eval_conj(E1,Eo,T,O,X).

% evaluate against a given list of functions
eval_fun(P,call(disj,[A,B]),T,O) :- !, (eval_fun(P,A,T,O); eval_fun(P,B,T,O)).
eval_fun(P,lambda(A,C),T,O) :-!,bind_vars([],E1,A,A1),!, unify(E1,Eo,A1,T), eval_block(['_'-P|Eo],_,C,O).

quote_unf(E,E,id(X),X) :- !.
quote_unf(E,Eo,[H|T], [Ho|To]) :-!, quote_unf(E,E1,H,Ho),!, quote_unf(E1,Eo,T,To),!.
quote_unf(E,E,X,X) :- !.

bind_vars(E,E,X,X) :- var(X),!.
bind_vars(E,Eo,id(X),O) :- !, variable(E,Eo,bind,X ,O),!.
bind_vars(E,Eo,quote(X),Y) :- !, quote_unf(E,Eo,X,Y).
bind_vars(E,E,lambda(H,T), lambda(H,T)) :- !.
bind_vars(E,E,call(def,T), call(def,T)) :- !.
bind_vars(E,Eo,call(H,T), call(Ho,To)) :-!, bind_vars(E,E1,H,Ho),bind_vars(E1,Eo,T,To).
bind_vars(E,Eo,p(P,H),p(P,Ho)) :-!, bind_vars(E,Eo,H,Ho).
bind_vars(E,Eo,block(X),O) :- !, eval_block(E,Eo,X,O).
bind_vars(E,Eo,[H|T], [Ho|To]) :-!, bind_vars(E,E1,H,Ho), bind_vars(E1,Eo,T,To).
bind_vars(E,E,X,X) :- !.


bind_lambda_vars(E,id(X),O,V,V) :- \+ member(X,V), member(X-O,E),!. 
bind_lambda_vars(_,id(X),id(X),V,[X|V]) :-!.
bind_lambda_vars(_,quote(X),X,V,V) :- !.
bind_lambda_vars(_,lambda(X,Y),lambda(X,Y),V,V) :- !.
bind_lambda_vars(_,call(def,Y),call(def,Y),V,V) :- !.
bind_lambda_vars(E,call(X,Y),call(Xo,Yo),Vi,Vo) :- !, bind_lambda_vars(E,X,Xo,Vi,V1),!,bind_lambda_vars(E,Y,Yo,V1,Vo).
bind_lambda_vars(E,block(X),block(Xo),Vi,Vo) :- !, bind_lambda_vars(E,X,Xo,Vi,Vo).
bind_lambda_vars(E,p(P,T),p(P,To),Vi,Vo) :-!, bind_lambda_vars(E,T,To,Vi,Vo).
bind_lambda_vars(_,X,X,V,V) :- !.


% find all function defs, return a list of functions and an environment of defined things
defined(E,K,V) :- member(K-V,E).
defined(E,K,V) :- !, member('_'-P,E), defined(P,K,V).

% state
variable(E,E,_,'_',_):- !.
variable(E,[K-call(disj,[Vi,V])|R],def,K,V) :- select(K-Vi, E, R),!.
variable(E,E,bind,K,V) :- member(K-V,E),!.
variable(E,[K-V|E],_,K,V):- !.


% builtin functions
:- discontiguous builtin/1, apply/3.
builtin(add). apply(add,[X,Y],O) :- O is X+Y,!.
builtin(sub). apply(sub,[X,Y],O) :- O is X-Y,!.
builtin(mul). apply(mul,[X,Y],O) :- O is X*Y,!.
builtin(div). apply(div,[X,Y],O) :- O is X/Y .
builtin(eq). apply(eq,[X,Y],Y) :- X==Y,!.
builtin(lt). apply(lt,[X,Y],Y) :-  X <Y,!.
builtin(le). apply(le,[X,Y],Y) :-  X =<Y,!.
builtin(gt). apply(gt,[X,Y],Y) :-  X >Y,!.
builtin(ge). apply(ge,[X,Y],Y) :-  X >=Y,!.
builtin(say).
apply(say,[],[]):-nl,!.
apply(say,[H|T],[]) :- say(H),!,apply(say,T,[]),!.
builtin(cons). apply(cons,[X,Y],[X|Y]):-!.
builtin(list). apply(list,X,X):-!.
say(X) :- write(X),!.

