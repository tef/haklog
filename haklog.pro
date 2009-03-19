#!/usr/bin/swipl -q -t start -f 

hk :- consult('parser.pro'),
    consult('eval.pro'),
    consult('lib.pro'),
    consult('unify.pro'),
    consult('print.pro'),
    consult('print.pro').

:- hk.

% this duplication isn't intentional, it is just so if you compile a binary
% with pl, use start_

start :-    catch(main,E,(print_message(error,E),fail)),    halt.
start :-    halt.

start_ :-    catch(main_,E,(print_message(error,E),fail)),    halt.
start_ :-    halt.

main :- current_prolog_flag(argv,X),
        clean_arguments(X,[],[_,File|_]),
        run_file(File).

main_ :- current_prolog_flag(argv,[_,X|_]),
        run_file(X).

env(E) :-       
    reserved(R),
    make_environment(R,E).

run_file(F) :-
    env(E),
    (exec_file(E,"common.hk",Eo);write("in common file"),nl,fail),
    exec_file(Eo,F,_).

exec_file(E,File,Eo) :- 
        prompt(_,''),
        (\+File = [] -> (
           string_to_atom(File,Name),
           open(Name,read,I)
        );
        current_input(I)),
        read_file(I,[],Code),
        exec(E,Code,Eo,_).

clean_arguments([--],H,[H,[],[]]).
clean_arguments([--|T],H,[H|T]).
clean_arguments([H|T],_,O) :- clean_arguments(T,H,O).


read_file(I,Li,Lo) :-  get_byte(I,C), ((C = -1,!,Lo=[]); Lo=[C|L1], read_file(I,Li,L1)).  

% interpreter
% featuring world most useful error messages

e(X) :- env(E),e(E,X,_,_).
e(X,O) :- env(E),e(E,X,_,O).
e(X,Eo,O) :- env(E),e(E,X,Eo,O).
p(X) :- parse(X,O), write(O),nl.
p(X,O) :- parse(X,O).
p(X,O,_) :- parse(X,O).

exec(Ei,X,E,O) :- 
    (parse(X,S);write('Syntax Error'),nl,fail),!,
    (eval(Ei,E,S,O) *-> [] ;write('Runtime Error'),nl,fail).


