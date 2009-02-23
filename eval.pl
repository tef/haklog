#!/usr/bin/swipl -q -t start -f 

:- consult('parser.pl').

start :-    catch(main,E,(print_message(error,E),fail)),    halt.
start :-    halt.

main :- current_prolog_flag(argv,X),
        clean_arguments(X,[],[_,File|_]),
        \+File = [],
           string_to_atom(File,Name),
           open(Name,read,I),
        execute(I).

clean_arguments([--],H,[H,[],[]]).
clean_arguments([--|T],H,[H|T]).
clean_arguments([H|T],_,O) :- clean_arguments(T,H,O).

execute(I):-
    read_file(I,[],Code),
    exec(Code,_,_).

read_file(I,Li,Lo) :-  get_byte(I,C), ((C = -1,!,Lo=[]); Lo=[C|L1], read_file(I,Li,L1)).  

% interpreter

exec(X,E,O) :- 
    parse(X,S),!,
    eval([],E,S,O).

evalone(Ei,Eo,X,O) :- eval(Ei,Eo,X,O),!.

eval(_,_,call(id(fail),_),_) :- !,fail.
eval(_,_,id(fail),_) :- !,fail.
eval(E,E,[],[]) :-!.
eval(Ei,Eo,block(X),O) :-!, eval_block(Ei,Eo,X,O).
eval(E,E,call(quote,[X]), X) :- !.
eval(E,E,lambda(X,Y), lambda(X,Y)) :- !.
eval(Ei,Eo,id(X),O) :- variable(Ei,Eo,bind,X,O),!.
eval(Ei,Eo,call(def,[call(N,A)|Y]),[]) :- variable(Ei,Eo,def,N,lambda(A,Y)),!.
eval(Ei,Eo,call(def,[X,Y]),[]) :- variable(Ei,Eo,def,X,Y),!.
eval(E,E,str(O), O) :- !.
eval(E,Eo,call(and,[X,Y]),Z) :-!, evalone(E,E1,X,_),!,eval(E1,Eo,Y,Z).
eval(E,Eo,call(or,[X,Y]),Z) :- !,(evalone(E,Eo,X,Z);!, eval(E,Eo,Y,Z)).
eval(E,E,call(not,X),[]) :- \+ eval(E,_,X,_), !.
eval(E,Eo,call(ifthen,[X,Y]),Z) :- !,((evalone(E,E1,X,_) -> (!, eval(E1,Eo,Y,Z))); !,Z =[]).
eval(E,Eo,call(if,X),Z) :- !,eval_if(E,Eo,X,Z). 
eval(E,Eo,call(all,X),Z) :- !,eval_all(E,Eo,X,[],Z).
eval(E,Eo,call(any,[H|T]),Z) :- !,(eval(E,E1,H,Z) ; eval(E1,Eo,call(any,T),Z)).
eval(E,Eo,call(every,X),Z) :- !,findall(A,eval_block(E,Eo,X,A),Z),!.
eval(E,Eo,call(once,T),A) :- !,eval_block(E,Eo,T,A),!.
eval(E,Eo,call(unf,[A,B]),A1) :- !,str_unf(E,E1,A,A1), str_unf(E1,Eo,B,A1).
eval(E,Eo,call(in,[A,B]),A1) :- !,str_unf(E,E1,A,A1), str_unf(E1,Eo,B,B1), member(A1,B1).
eval(E,Eo,evalcall(H,T),O) :- !,eval(E,E1,H,Ho), eval(E1,Eo,call(Ho,T),O).
eval(E,Eo,call(lambda(A,C),T),O) :- str_unf(E,Eo,T,To),eval_fun(E,[lambda(A,C)],To,O).
eval(E,Eo,call(H,T),O) :- builtin(H),!, eval(E,Eo,T,To), apply(H,To,O).
eval(E,Eo,call(C,T),A) :- !,defined(E,C,F),str_unf(E,Eo,T,To),eval_fun(E,F,To,A).
eval(E,Eo,[H|T],[Ho|To]) :- eval(E,E1,H,Ho), eval(E1,Eo,T,To).
eval(E,E,X,X) :- number(X).

eval_if(E,E,[],[]).
eval_if(Ei,Eo,[E],O) :- !, eval(Ei,Eo,E,O).
eval_if(Ei,Eo,[call(ifthen,[X,Y])|T],O) :- (evalone(Ei,E1,X,_) -> (!, eval(E1,Eo,Y,O))); eval_if(Ei,Eo,T,O). 

eval_block(E,E,[],[]). 
eval_block(E,Eo,[H],O) :- !, eval(E,Eo,H,O).
eval_block(E,Eo,[H|T],X) :-  eval(E,E1,H,_), !,eval_block(E1,Eo,T,X).

eval_all(E,E,[],X,X). 
eval_all(E,Eo,[H|T],_,X) :-  eval(E,E1,H,O), eval_all(E1,Eo,T,O,X).

% evaluate against a given list of functions
eval_fun(P,call(any,[A,B]),T,O) :- !, (eval_fun(P,A,T,O); eval_fun(P,B,T,O)).
eval_fun(P,lambda(A,C),T,O) :-!,str_unf([],Eo,A,T),eval_block(['_'-P|Eo],_,C,O).

% strucural unification
str_unf(E,Eo,id(X),O) :- !, variable(E,Eo,bind,X,O).
str_unf(E,Eo,call(quote,[X]),Y) :- !, quote_unf(E,Eo,X,Y).
str_unf(E,Eo,block(X),O) :- !, eval_block(E,Eo,X,O).
str_unf(E,Eo,[H|T], [Ho|To]) :-!, str_unf(E,E1,H,Ho),!, str_unf(E1,Eo,T,To),!.
str_unf(E,Eo,call(H,T), call(H,To)) :-!, str_unf(E,Eo,T,To),!.
str_unf(E,E,X,X) :- !.

quote_unf(E,E,id(X),X) :- !.
quote_unf(E,Eo,[H|T], [Ho|To]) :-!, quote_unf(E,E1,H,Ho),!, quote_unf(E1,Eo,T,To),!.
quote_unf(E,E,X,X) :- !.

% find all function defs, return a list of functions and an environment of defined things
defined(E,K,V) :- member(K-V,E).
defined(E,K,V) :- !, member('_'-P,E), defined(P,K,V).

% state
variable(E,E,_,'_',_):- !.
variable(E,[K-call(any,[Vi,V])|R],def,K,V) :- select(K-Vi, E, R),!.
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

say(str(X)) :- writef("%s ",[X]),!.
say(X) :- writef("%t ",[X]),!.

