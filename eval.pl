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

eval(Ei,Eo,[block|X],O) :-!, eval_block(Ei,Eo,X,O).
eval(E,E,[quote,X], X) :- !.
eval(E,E,[lambda|X], [lambda|X]) :- !.
eval(Ei,Eo,[list|X],O) :- !,eval_list(Ei,Eo,X,O).
eval(Ei,Eo,id(X),O) :- variable(Ei,Eo,bind,X,O),!.
eval(Ei,Eo,[def,[N|A],Y],[]) :- variable(Ei,Eo,def,N,[lambda,A,Y]),!.
eval(Ei,Eo,[def,X,Y],[]) :- variable(Ei,Eo,def,X,Y),!.
eval(_,_,id(fail),_) :- !,fail.
eval(_,_,[id(fail)|_],_) :- !,fail.
eval(E,E,str(O), O) :- !.

eval(E,Eo,[and,X,Y],Z) :-!, evalone(E,E1,X,_),!,eval(E1,Eo,Y,Z).
eval(E,Eo,[or,X,Y],Z) :- !,(evalone(E,Eo,X,Z);!, eval(E,Eo,Y,Z)).
eval(E,E,[not,X],[]) :- \+ eval(E,_,X,_), !.
eval(E,Eo,[ifthen,X,Y],Z) :- !,((evalone(E,E1,X,_) -> (!, eval(E1,Eo,Y,Z))); !,Z =[]).
eval(E,Eo,[if|X],Z) :- !,eval_if(E,Eo,X,Z). 
eval(E,Eo,[all|X],Z) :- !,eval_all(E,Eo,X,[],Z).
eval(E,Eo,[any|[H|T]],Z) :- !,(eval(E,E1,H,Z) ; eval(E1,Eo,[any|T],Z)).
eval(E,Eo,[every|X],Z) :- !,findall(A,eval_block(E,Eo,X,A),Z),!.
eval(E,Eo,[eval|T],A) :- !,subst_args(E,E1,T,To),!,eval_block(E1,Eo,To,A).
eval(E,Eo,[once|T],A) :- !,subst_args(E,E1,T,To),!,eval_block(E1,Eo,To,A),!.

eval(E,Eo,[C|T],A) :- defined(E,C,F),subst_args(E,Eo,T,To),eval_fun(E,F,To,A).
eval(E,Eo,[H|T],O) :- builtin(H),!, eval_list(E,Eo,T,To), apply(H,To,O).

eval(E,E,X,X) :- number(X); X = [].

eval_if(E,E,[],[]).
eval_if(Ei,Eo,[E],O) :- !, eval(Ei,Eo,E,O).
eval_if(Ei,Eo,[[ifthen,X,Y]|T],O) :- (evalone(Ei,E1,X,_) -> (!, eval(E1,Eo,Y,O))); eval_if(Ei,Eo,T,O). 

eval_list(E,E,[],[]).
eval_list(E,Eo,[H|T],[Ho|To]) :- eval(E,E1,H,Ho) , eval_list(E1,Eo,T,To).

eval_block(E,E,[],[]). 
eval_block(E,Eo,[H],O) :- !, eval(E,Eo,H,O).
eval_block(E,Eo,[H|T],X) :-  eval(E,E1,H,_), !,eval_block(E1,Eo,T,X).

eval_all(E,E,[],X,X). 
eval_all(E,Eo,[H|T],_,X) :-  eval(E,E1,H,O), eval_all(E1,Eo,T,O,X).


% substitute arguments for calling from environment
subst_args(E,Eo,id(X),O) :- !,variable(E,Eo,bind,X,O).
subst_args(E,E,[quote,X],[quote,X]) :-!.
subst_args(E,E,[cons,X,Y],[X|Y]) :-!.
subst_args(E,Eo,[block|X],O) :- !, eval_block(E,Eo,X,O).
subst_args(E,Eo,[list|T],To) :-!, subst_args(E,Eo,T,To).
subst_args(E,Eo,[H|T],[Ho|To]) :-!, subst_args(E,E1,H,Ho),  subst_args(E1,Eo,T,To).
subst_args(E,E,X,X) :- !.

% bind the function def and calling arguments together
bind_args(E,E,[list],[]):- !.
bind_args(E,Eo,id(X),O) :- variable(E,Eo,bind,X,Op),!, O=Op,!.
bind_args(E,Eo,[cons,X,Y],[Xa|Ya]) :- !, bind_args(E,E1,X,Xa),!, bind_args(E1,Eo,Y,Ya),!.
bind_args(E,Eo,[list|X],Xa) :- !, bind_args(E,Eo,X,Xa),!. 
bind_args(E,Eo,[H|T], [Ho|To]) :-!, bind_args(E,E1,H,Ho),!, bind_args(E1,Eo,T,To),!.
bind_args(E,E,X,X) :- !.

% evaluate against a given list of functions
eval_fun(P,[any,A,B],T,O) :- !, (eval_fun(P,A,T,O); eval_fun(P,B,T,O)).
eval_fun(P,[lambda,A,C],T,O) :-!,bind_args([],Eo,A,T),eval(['_'-P|Eo],_,C,O).

% find all function defs, return a list of functions and an environment of defined things
defined(E,K,V) :- member(K-V,E).
defined(E,K,V) :- !, member('_'-P,E), defined(P,K,V).

% state
variable(E,E,_,'_',_):- !.
variable(E,[K-[any,Vi,V]|R],def,K,V) :- select(K-Vi, E, R),!.
variable(E,E,bind,K,V) :- member(K-V,E),!.
variable(E,[K-V|E],_,K,V):- !.


% builtin functions
:- discontiguous builtin/1, apply/3.
builtin(add). apply(add,[X,Y],O) :- O is X+Y,!.
builtin(sub). apply(sub,[X,Y],O) :- O is X-Y,!.
builtin(mul). apply(mul,[X,Y],O) :- O is X*Y,!.
builtin(div). apply(div,[X,Y],O) :- O is X/Y .
builtin(unf). apply(unf,[X,Y],Y) :- X=Y,!.
builtin(eq). apply(eq,[X,Y],Y) :- X==Y,!.
builtin(lt). apply(lt,[X,Y],Y) :-  X <Y,!.
builtin(le). apply(le,[X,Y],Y) :-  X =<Y,!.
builtin(gt). apply(gt,[X,Y],Y) :-  X >Y,!.
builtin(ge). apply(ge,[X,Y],Y) :-  X >=Y,!.
builtin(in). apply(in,[X,Y],X) :-  member(X,Y).
builtin(say).
apply(say,[],[]):-nl,!.
apply(say,[H|T],[]) :- say(H),!,apply(say,T,[]),!.
builtin(cons). apply(cons,[X,Y],[X|Y]):-!.

say(str(X)) :- writef("%s ",[X]),!.
say(X) :- writef("%t ",[X]),!.

