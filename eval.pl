#!/usr/bin/swipl -q -t main -f 

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

eval(_,_,id(fail),_) :- !,fail.
eval(_,_,[id(fail)|_],_) :- !,fail.
eval(E,E,X,X) :- number(X); X = [].
eval(E,E,[quote,X], X) :- !.
eval(Ei,Eo,[list|X],[list|O]) :- !,eval_list(Ei,Eo,X,O).
eval(Ei,Eo,[block|X],O) :-!, eval_block(Ei,Eo,X,[],O).
eval(Ei,Eo,id(X),O) :- !,variable(Ei,Eo,X,O).
eval(Ei,Eo,[def,X,Y],[]) :- !,define(Ei,Eo,X,Y),!.

eval(E,Eo,[and,X,Y],Z) :- evalone(E,E1,X,_),!,eval(E1,Eo,Y,Z).
eval(E,Eo,[ifthen,X,Y],Z) :- (evalone(E,E1,X,_) -> (!, eval(E1,Eo,Y,Z))); !,Z =[].
eval(E,Eo,[if|X],Z) :- eval_if(E,Eo,X,Z). 
eval(E,Eo,[or,X,Y],Z) :- evalone(E,Eo,X,Z); eval(E,Eo,Y,Z).
eval(E,Eo,[all|X],Z) :- !,eval_block(E,Eo,X,[],Z).
eval(E,Eo,[any|[H|T]],Z) :- eval(E,E1,H,Z) ; eval(E1,Eo,[any|T],Z).
eval(E,Eo,[every|X],[list|Z]) :- findall(A,eval_block(E,Eo,X,[],A),Z),!.
eval(E,Eo,[eval|T],A) :- subst_args(E,E1,T,To),!,eval_block(E1,Eo,To,[],A).

eval(E,Eo,[C|T],A) :- fun_list(E,Ef,F,C),\+ F = [],!,subst_args(E,Eo,T,To),!,eval_fun(Ef,F,[C|To],A).
eval(E,Eo,[H|T],O) :- atom(H),!, eval_list(E,Eo,T,To), apply(H,To,O).

eval_if(E,E,[],[]).
eval_if(Ei,Eo,[E],O) :- !, eval(Ei,Eo,E,O).
eval_if(Ei,Eo,[[ifthen,X,Y]|T],O) :- (evalone(Ei,E1,X,_) -> (!, eval(E1,Eo,Y,O))); eval_if(Ei,Eo,T,O). 

eval_list(E,E,[],[]).
eval_list(E,Eo,[H|T],[Ho|To]) :- eval(E,E1,H,Ho) , eval_list(E1,Eo,T,To).

eval_block(E,E,[],X,X). 
eval_block(E,Eo,[H|T],_,X) :- !, eval(E,E1,H,O), eval_block(E1,Eo,T,O,X).


% substitute arguments for calling from environment
subst_args(E,E,[],[]) :-!.
subst_args(E,Eo,id(X),O) :- variable(E,Eo,X,O),!.
subst_args(E,E,X,X) :- number(X); atom(X).
subst_args(E,E,[quote,X],[quote,X]) :-!.
subst_args(E,Eo,[block|X],O) :- !,eval_block(E,Eo,X,[],O).
subst_args(E,Eo,[H|T],[Ho|To]) :-  subst_args(E,E1,H,Ho),  subst_args(E1,Eo,T,To).

% evaluate against a given list of functions
eval_fun(_,[],_,_) :- !,fail.
eval_fun(Ef,[def(X,A)-V|_],[X|In],O) :- bind_args(Ef,Eo,A,In),eval(Eo,_,V,O).
eval_fun(Ef,[_|T],X,O) :- !, eval_fun(Ef,T,X,O).

% find all function defs, return a list of functions and an environment of defined things
fun_list([],[],[],_) :- !.
fun_list([def(X,A)-V|T],[def(X,A)-V|Eo],[def(X,A)-V|O],X) :- fun_list(T,Eo,O,X),!.
fun_list([def(X,A)-V|T],[def(X,A)-V|Eo],O,F) :- fun_list(T,Eo,O,F),!.
fun_list([_|T],Eo,O,X) :- fun_list(T,Eo,O,X),!.

% bind the function def and calling arguments together
bind_args(E,E,[],[]):- !.
bind_args(E,Eo,id(X),O) :- variable(E,Eo,X,Op),!, O=Op,!.
bind_args(E,Eo,[cons,X,Y],[list|[Xa|Ya]]) :- !, bind_args(E,E1,X,Xa),!, bind_args(E1,Eo,Y,[list|Ya]),!.
bind_args(E,E1,[cons,X,[]],[list|Xa]) :- !, bind_args(E,E1,X,Xa),!.
bind_args(E,Eo,[H|T], [Ho|To]) :-!, bind_args(E,E1,H,Ho),!, bind_args(E1,Eo,T,To),!.
bind_args(E,E,X,X) :- !.

% state
variable(E,E,'_',_):- !.
variable([K-V|E],[K-V|E],K,V) :-!.
variable([K|T],[K|To],X,O) :- variable(T,To,X,O),!.
variable(E,[K-V|E],K,V):- !.

define(T,O ,[X|A],Y)  :- append(T, [def(X,A)-Y],O),!.
define(T,O ,id(X),Y)  :- append(T, [def(X,[])-Y],O),!.

% builtin functions

apply(add,[X,Y],O) :- O is X+Y,!.
apply(sub,[X,Y],O) :- O is X-Y,!.
apply(mul,[X,Y],O) :- O is X*Y,!.
apply(div,[X,Y],O) :- O is X/Y .
apply(unf,[X,Y],Y) :- X=Y,!.
apply(lt,[X,Y],Y) :-  X <Y,!.
apply(le,[X,Y],Y) :-  X =<Y,!.
apply(gt,[X,Y],Y) :-  X >Y,!.
apply(ge,[X,Y],Y) :-  X >=Y,!.
apply(in,[X,[list|Y]],X) :-  member(X,Y).
apply(say,[],[]):-!.
apply(say,[H|T],[]) :- write(H),nl,!,apply(say,T,[]),!.
apply(cons,[X,[list]],[list,X]) :-!.
apply(cons,[X,[list|Y]],[list|[X|Y]]):-!.
