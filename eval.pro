

evalone(Ei,Eo,X,O) :- eval(Ei,Eo,X,O),!.

% eval(+Environment,-Environment,+Expression,-Result)

%eval(_,_,call(X,Y),_) :-  writef("Eval: call(%w,%w)\n",[X,Y]), fail.
eval(E,E,X,X) :- var(X),!.
eval(_,_,call(X,_),_) :- var(X),!,fail.
eval(E,E,[],[]) :-!.
eval(_,_,call(id(fail),_),_) :- !,fail.
eval(_,_,fail,_) :- !,fail.
eval(E,E,trace,[]) :- !,trace.
eval(Ei,Eo,block(X),O) :-!, eval_block(Ei,Eo,X,O).
eval(E,E,call(quote,X), X) :- !.
eval(Ei,Eo,id(X),O) :- bind_variable(Ei,Eo,X,O),!.
eval(Ei,Eo,p(P,A),O) :- !,bind_vars(Ei,E1,A,A1),!,unify_var_p(P,E1,Eo,A1,O).
eval(E,E,lambda(X,Y),lambda(X,Y)) :-!. % this is here so when X is defined as call(disj...) 
eval(E,Eo,call(def,[call(N,A)|Y]),lambda(Ao,Yo)) :- 
    bind_lambda_vars(N,[],A,Ao,[],Av), !, bind_lambda_vars(N,E,Y,Yo,Av,_), !,
    def_variable(E,Eo,N,lambda(Ao,Yo)),!.
eval(E,Eo,call(def,[id(N)|Y]),lambda([],Yo)) :- 
    bind_lambda_vars(N,E,Y,Yo,[],_), !,
    def_variable(E,Eo,N,lambda([],Yo)),!.
eval(E,Eo,call(and,[X,Y]),Z) :-!, evalone(E,E1,X,_),!,eval(E1,Eo,Y,Z).
eval(E,Eo,call(or,[X,Y]),Z) :- !,(evalone(E,Eo,X,Z);!, eval(E,Eo,Y,Z)).
eval(E,Eo,call(xor,[X,Y]),Z) :- !,((eval(E,Eo,X,Z) *-> true);eval(E,Eo,Y,Z)).
eval(E,E,call(not,X),[]) :- \+ eval(E,_,X,_), !.
eval(E,Eo,call(ifthen,[X,Y]),Z) :- !,((evalone(E,E1,X,_) -> (!, eval(E1,Eo,Y,Z))); !,Z =[]).
eval(E,Eo,call(if,X),Z) :- !,eval_if(E,Eo,X,Z). 
eval(E,Eo,call(case,[X|T]),Z) :- !, bind_vars(E,E1,X,X1),!, eval_case(E1,Eo,X1,T,Z). 
eval(E,Eo,call(conj,X),Z) :- !,eval_conj(E,Eo,X,[],Z).
eval(_,_,call(disj,[]),_) :- !, fail.
eval(E,Eo,call(disj,[H|T]),Z) :- !,(eval(E,E1,H,Z) ; !,eval(E1,Eo,call(disj,T),Z)).
eval(E,Eo,call(eval,X),Z) :- !,bind_vars(E,E1,X,X1),!, eval(E1,Eo,X1,[Z]).
eval(E,Eo,call(say,X),[]) :- !,bind_vars(E,Eo,X,X1),!, hprint_list(X1), nl.
eval(E,Eo,call(spawn,X),Z) :- !,bind_vars(E,Eo,X,X1),!, spawn(Eo,X1,Z).
eval(E,Eo,call(send,[X,Y]),[]) :- !,eval(E,E1,X,X1),!,bind_vars(E1,Eo,Y,Y1),!, send(X1,Y1).
eval(E,Eo,call(write,[X,Y]),[]) :- !,eval(E,E1,X,X1),!,bind_vars(E1,Eo,Y,Y1),!, send(X1,Y1).
eval(E,Eo,call(recv,T),Z) :- !,recv(X), !,eval_case(E,Eo,X,T,Z). 
eval(E,Eo,call(read,[S]),X) :- !, bind_vars(E,Eo,S,St), !, read_(St,X), !. 
eval(E,Eo,call(read,[S|T]),Z) :- !, bind_vars(E,E1,S,St), !, read_(St,X), !,eval_case(E1,Eo,X,T,Z). 
eval(E,Eo,call(open,[S]),Z) :- !, bind_vars(E,Eo,S,St), !, open_(St,Z).
eval(E,Eo,call(close,[S]),[]) :- !, bind_vars(E,Eo,S,St), !, close_(St).
eval(E,Eo,call(where,[Y,X]),Z) :- !,bind_lambda_vars('_',E,X,Xo,[],_),eval([],E1,Xo,_), bind_lambda_vars('_',E1,Y,Yo,[],_), eval(E,Eo,Yo,Z).
eval(E,Eo,call(every,X),Z) :- !,findall(A,eval(E,Eo,X,A),Z),!.
eval(E,Eo,call('_term',[X|Y]),Z) :-!,bind_vars(E,E1,X,X1), bind_vars(E1,Eo,Y,Y1), Z =.. [X1|Y1].
eval(E,Eo,call('_prolog',[X|Y]),[]) :-!,bind_vars(E,E1,X,X1), bind_vars(E1,Eo,Y,Y1), Z =.. [X1|Y1],  call(Z).
eval(E,Eo,call('_prolog',[X]),[]) :-!,bind_vars(E,Eo,X,X1), call(X1).
eval(E,Eo,call(once,T),A) :- !,eval(E,Eo,T,A),!.
eval(E,Eo,call(to,[A,B]),O) :- !,bind_vars(E,E1,A,A1), bind_vars(E1,Eo,B,B1), between(A1,B1,O).
eval(E,Eo,call(is,[A,B]),O) :- !,bind_vars(E,E1,A,O), eval(E1,Eo,B,O).
eval(E,Eo,call(match,[A,B]),O) :- !,bind_vars(unf,E,E1,A,A1), bind_vars(unf,E1,E2,B,B1), unify(pat,E2,Eo,A1,B1,O).
eval(E,Eo,call(unf,[A,B]),O) :- !,bind_vars(unf,E,E1,A,A1),!, bind_vars(unf,E1,E2,B,B1), !,unify(unf,E2,Eo,A1,B1,O).
eval(E,Eo,call(eq,[A,B]),O) :- !,bind_vars(eq,E,E1,A,A1),!, bind_vars(eq,E1,_,B,B1), !,unify(unf,E,Eo,A1,B1,O).
eval(E,Eo,call(concat,[A,B]),O) :- !,bind_vars(E,E1,A,A1),!, bind_vars(E1,E2,B,B1), !,eval(E2,E3,A1,A2), eval(E3,Eo,B1,B2), concat(A2,B2,O).
eval(E,Eo,call(in,[A,B]),A1) :- !,bind_vars(E,E1,A,A1), !,bind_vars(E1,Eo,B,B1),!,member(A1,B1).
eval(E,Eo,call(H,T),O) :-  \+ var(H), 
    atom(H) -> (
        (aug_builtin(H),!, eval_aug(E,Eo,H,T,O)); 
        (builtin(H),!, eval(E,Eo,T,To), apply(H,To,O)); 
        (!,defined(E,H,F),!,eval(E,Eo,call(F,T),O))
    );
    ((H = lambda(_,_);H = call(disj,_)), !, bind_vars(E,Eo,T,To),!,eval_fun(E,['_rec'-H],H,To,O));
    (H = id(Ho), !, eval(E,Eo,call(Ho,T),O));
    (string(H), !, string_to_atom(H,Ho), !, eval(E,Eo,call(Ho,T),O));
    (!,eval(E,E1,H,Ho),\+H=Ho,eval(E1,Eo,call(Ho,T),O)).

eval(E,Eo,[H|T],[H|To]) :- var(H),!,eval(E,Eo,T,To).
eval(Ei,Eo,[p(P,A)|Lt],O) :- !,bind_vars(Ei,E1,A,A1),!,unify_var_p_l(P,E1,E2,A1,Po),eval(E2,Eo,Lt,T),join(Po,T,O).
eval(E,Eo,[H|T],[Ho|To]) :- eval(E,E1,H,Ho), eval(E1,Eo,T,To).
eval(E,E,X,X) :- atomic(X),!.
eval(E,E,X,X) :- string(X),!.
eval(E,E,X,X) :- var(X),!.

%eval_case(+Env,-Env,+Expression,+CaseList,-Result).
%eval_case(_,_,A,T,_) :- writef("\ncase: [%w] [%w]\n",[A,T]),  fail.
eval_case(E,E,_,[],[]).
eval_case(Ei,Eo,A,[call(ifthen,[X,Y])|T],O) :- !, ( ( bind_vars(Ei,E1,X,X1), !, unify(pat,E1,E2,X1,A,_)) *-> eval(E2,Eo,Y,O) ; eval_case(Ei,Eo,A,T,O)).
eval_case(Ei,Eo,_,[X],O) :- !,bind_vars(Ei,E1,X,X1) ,!,eval(E1,Eo,X1,O).

%eval_if(+Env,-Env,+IfList,-Result).
eval_if(E,E,[],[]).
eval_if(Ei,Eo,[call(ifthen,[X,Y])|T],O) :- !, (evalone(Ei,E1,X,_) -> (!, eval(E1,Eo,Y,O))); eval_if(Ei,Eo,T,O). 
eval_if(Ei,Eo,[E],O) :- !, eval(Ei,Eo,E,O).

%eval_block(+Env,-Env,+Expression,-Result)
% this returns the last result in a block 
% {a;b;c} --> a and b and c

eval_block(E,E,[],[]). 
eval_block(E,Eo,[H],O) :- !, eval(E,Eo,H,O).
eval_block(E,Eo,[H|T],X) :-  eval(E,E1,H,_), !,eval_block(E1,Eo,T,X).

%eval_conj(+Env,-Env, +ConjList, +LastResult, -Result).
eval_conj(E,E,[],X,X). 
eval_conj(E,Eo,[H|T],_,X) :-  eval(E,E1,H,O), eval_conj(E1,Eo,T,O,X).

%eval_fun(+ParentEnv, +StartEnv, +FunctionDef, +FunctionArgs, -Output)
% evaluate against a given list of functions

eval_fun(P,S,lambda(A,C),T,O) :-!,bind_vars(S,E1,A,A1),!, unify(pat, E1,Eo,A1,T,_),eval_block(['_'-P|Eo],_,C,O).
eval_fun(P,S,call(disj,[A,B]),T,O) :- !, (eval_fun(P,S,A,T,O); \+ var(B),eval_fun(P,S,B,T,O)).


bind_vars(E,Eo,A,B) :- bind_vars(eval,E,Eo,A,B).
%bind_vars(+Eval,+Env,-Env,+Expr,-Expr)
% Bind the variables in the expression i.e replace id(X) with an actual variable
bind_vars(_,E,E,X,X) :- var(X),!.
bind_vars(eq,E,Eo,id(X),O) :- !, bind_variable(E,Eo,X ,Ot),!, (var(Ot); Ot=O),!.
bind_vars(_,E,Eo,id(X),O) :- !, bind_variable(E,Eo,X ,O),!.
bind_vars(_,E,E,call(quote,X),call(quote,X)) :-!.
bind_vars(_,E,E,lambda(H,T), lambda(H,T)) :- !.
bind_vars(_,E,E,call(def,T), call(def,T)) :- !.
bind_vars(M,E,Eo,call(H,T), call(Ho,To)) :-!, bind_vars(M,E,E1,H,Ho),bind_vars(M,E1,Eo,T,To).
bind_vars(M,E,Eo,[p(P,H)|T],R) :- bind_vars(M,E,Ei,H,H1),unify_var_p_l(P,Ei,E1,H1,Ho),!,bind_vars(M,E1,Eo,T,To), join(Ho,To,R).
bind_vars(M,E,Eo,p(P,H),R) :- bind_vars(M,E,E1,H,H1), unify_var_p(P,E1,Eo,H1,R),!.
bind_vars(M,E,Eo,p(P,H),p(P,Ho)) :-!, bind_vars(M,E,Eo,H,Ho).
bind_vars(eval,E,Eo,block(X),O) :- !, eval_block(E,Eo,X,O).
bind_vars(M,E,Eo,[H|T], [Ho|To]) :-!, bind_vars(M,E,E1,H,Ho), bind_vars(M,E1,Eo,T,To).
bind_vars(_,E,E,X,X) :- !.

%bind_lambda_vars(+RecursiveName,+Environment,+Expr,-Expr,+BoundAlready,-BoundAlready)
% bind the variables in a lambda expression
bind_lambda_vars(_,_,id('_'),id('_'),V,V) :-!. 
bind_lambda_vars(R,_,id(R),id('_rec'),V,V) :-!. 
%bind_lambda_vars(id(R),_,id(R),id('_rec'),V,V) :-!. 
bind_lambda_vars(_,_,id(X),id(X),V,V) :- member(X,V),!.
bind_lambda_vars(_,E,id(X),O,V,V) :- defined(E,X,O),!. 
bind_lambda_vars(_,_,id(X),id(X),V,[X|V]) :-!.
bind_lambda_vars(R,E,lambda(X,Y),lambda(Xo,Yo),V,V) :- 
    !,bind_lambda_vars(R,E,X,Xo,[],V1), append(V1,V,V2),!,bind_lambda_vars(R,E,Y,Yo,V2,_).
bind_lambda_vars(_,E,call(def,[id(X),Y]),call(def,[id(X),Yo]),Vi,Vo) :- !,bind_lambda_vars(X,E,Y,Yo,Vi,Vo).
bind_lambda_vars(R,E,call(X,Y),call(Xo,Yo),Vi,Vo) :- atom(X),!, 
    bind_lambda_vars(R,E,id(X),X1,Vi,V1), (X1 = id(Xo),!;Xo=X1),!,bind_lambda_vars(R,E,Y,Yo,V1,Vo).
bind_lambda_vars(R,E,call(X,Y),call(Xo,Yo),Vi,Vo) :- !, bind_lambda_vars(R,E,X,Xo,Vi,V1),!,bind_lambda_vars(R,E,Y,Yo,V1,Vo).
bind_lambda_vars(R,E,[X|Y],[Xo|Yo],Vi,Vo) :- !, bind_lambda_vars(R,E,X,Xo,Vi,V1),!,bind_lambda_vars(R,E,Y,Yo,V1,Vo).
bind_lambda_vars(R,E,block(X),block(Xo),Vi,Vo) :- !, bind_lambda_vars(R,E,X,Xo,Vi,Vo).
bind_lambda_vars(R,E,p(P,T),p(P,To),Vi,Vo) :-!, bind_lambda_vars(R,E,T,To,Vi,Vo).
bind_lambda_vars(_,_,X,X,V,V) :- !.

%defined(+Environment,+Key,-Value).
% find all function defs, return a list of functions and an environment of defined things
defined(E,K,V) :- member(K-V,E).
defined(E,K,V) :- !, member('_'-P,E), defined(P,K,V).

%def_variable(+Env,-Env,+Name,-Value)
%define a variable using :-
def_variable(E,E,'_',_):- !.
def_variable(E,[K-call(disj,[Vi,V])|R],K,V) :- select(K-Vi, E, R),!.
def_variable(E,[K-V|E],K,V):- !.

%bind_variable(+Env,-Env,+Name,-Value)
bind_variable(E,E,'_',_):- !.
bind_variable(E,E,'_env',E):- !.
bind_variable(E,E,K,V) :- member(K-V,E),!.
bind_variable(E,[K-V|E],K,V):- !.

%builtin(+Name)
%apply(+Name,+Args,-Output)
% builtin functions
% this is swi specific
eval_aug(E,Eo,N,[A,B],O) :- list(A), list(B),!, eval_aug_l(E,Eo,N,A,B,O).
eval_aug(E,Eo,N,[A,B],O) :- list(A),!, eval_aug_sl(E,Eo,N,B,A,O).
eval_aug(E,Eo,N,[A,B],O) :- list(B),!, eval_aug_sl(E,Eo,N,A,B,O).
eval_aug(E,Eo,N,[A,B],O) :- !, eval(E,E1,A,A1), eval(E1,Eo,B,B1),  apply(N,[A1,B1],O),!.

eval_aug(E,Eo,N,A,O) :- list(A),!, eval_aug_sl(E,Eo,N,A,O).
eval_aug(E,Eo,N,A,O) :- !, eval(E,Eo,A,A1), apply(N,[A1],O),!.


eval_aug_l(E,E,_,[],[],[]).
eval_aug_l(E,Eo,N,[Ha|Ta],[Hb|Tb],[Ho|To]) :- eval_aug(E,E1,N,[Ha,Hb],Ho), eval_aug_l(E1,Eo,N,Ta,Tb,To).

eval_aug_sl(E,E,_,_,[],[]).
eval_aug_sl(E,Eo,N,H,[Hb|Tb],[Ho|To]) :- eval_aug(E,E1,N,[H,Hb],Ho), eval_aug_sl(E1,Eo,N,H,Tb,To).
eval_aug_sl(E,E,_,[],[]).
eval_aug_sl(E,Eo,N,[Hb|Tb],[Ho|To]) :- eval_aug(E,E1,N,Hb,Ho), eval_aug_sl(E1,Eo,N,Tb,To).


:- discontiguous builtin/1, apply/3, aug_builtin/1.

aug_builtin(add). apply(add,[X,Y],O) :-plus(X,Y,O),!.
aug_builtin(sub). apply(sub,[X,Y],O) :- O is X-Y,!.
aug_builtin(neg). apply(neg,[X],O) :- O is 0 - X,!.
aug_builtin(mul). apply(mul,[X,Y],O) :- O is X*Y,!.
aug_builtin(div). apply(div,[X,Y],O) :- O is X/Y .
builtin(lt). apply(lt,[X,Y],Y) :-  X <Y,!.
builtin(le). apply(le,[X,Y],Y) :-  X =<Y,!.
builtin(gt). apply(gt,[X,Y],Y) :-  X >Y,!.
builtin(ge). apply(ge,[X,Y],Y) :-  X >=Y,!.
builtin(number). apply(number,[X],Y) :-  cast_to_number(X,Y),!.
builtin(string). apply(string,[X],Y) :-  cast_to_string(X,Y),!.
