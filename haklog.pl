#!/usr/bin/swipl -q -t start -f 

hk :- consult('parser.pl'),
    consult('eval.pl'),
    consult('unify.pl'),
    consult('print.pl'),
    consult('print.pl').

:- hk.

start :-    catch(main,E,(print_message(error,E),fail)),    halt.
start :-    halt.

main :- current_prolog_flag(argv,X),
        clean_arguments(X,[],[_,File|_]),
        prompt(_,''),
        (\+File = [] -> (
           string_to_atom(File,Name),
           open(Name,read,I)
        );
        current_input(I)),
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
    (parse(X,S);write('Syntax Error'),nl,fail),!,
    reserved(R),
    make_environment(R,E1),
    (eval(E1,E,S,O) *->hprint(O);write('Runtime Error'),nl,fail).

