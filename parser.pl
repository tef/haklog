#!/usr/bin/swipl -q -t start -f 

start :-    catch(main,E,(print_message(error,E),fail)),    halt.
start :-    halt.

main :- current_prolog_flag(argv,X),
        clean_arguments(X,[],[Cmd,File|_]),
        (\+ File = [];
            writef('usage: %w <filename>\n',[Cmd]),
            halt
        ),!,execute(File).

clean_arguments([--],H,[H,[],[]]).
clean_arguments([--|T],H,[H|T]).
clean_arguments([H|T],_,O) :- clean_arguments(T,H,O).

execute(Code) :-
    exec(Code,Output),
    writenl(Output).

% top down operator precedence parser 


% tokens
number(N) --> digit(D0), digits(D), { number_chars(N, [D0|D]) },!.

digits([D|T]) --> digit(D), digits(T).
digits([]) --> [].

digit(D) --> [D], {code_type(D, digit)}.

alnums([H|T]) --> alnum(H), alnums(T).
alnums([]) --> [].

csyms([H|T]) --> csym(H), csyms(T).
csyms([]) --> [].

alphas([H|T]) --> alpha(H), alphas(T).
alphas([]) --> [].

alnum(A) --> [A], {code_type(A, alnum)}.
alpha(A) --> [A], {code_type(A, alpha)}.
csym(C) --> [C], {code_type(C, csymf)}.

identifier(A) --> alpha(C), csyms(N), {string_to_atom([C|N],A)},!. 
variable(id(A)) --> "$", alnums(N), {string_to_atom(N,A)},!.
variable(id('_')) --> "_",!.

string([list|S]) --> "\"", chars(S).

chars([]) --> "\"".
chars(["\""|T]) --> "\\\"", chars(T).
chars([H|T]) --> [H], chars(T).

ws0 --> [X], {code_type(X, white)}, ws.
ws --> ws0.
ws --> [].

item(E) --> number(E),!.
item(E) --> variable(E),!.
item(E) --> string(E),!.

% containers

% a block is { ... }, can have terminators
block([H|T],N) --> exprn(H,N), ws,!, block(T,N).
block(X,N) --> ";", ws,!, block(X,N).
block([],_) --> [].

% a list of expressions (function args)
exprl([H|T],N) --> exprn(H,N), ws,!, exprl(T,N).
exprl([],_) --> [].

%helpers
exprl(L) --> ws,exprl(L, 100).
expr(L) --> ws,exprn(L,100).
block([block|L]) --> ws, block(L,100).

%expressions
exprn(O,N1) --> \+ infix(_,_,_), \+ postfix(_,_), identifier(X), !, idfollow(O,X,N1). 
exprn(O,N1) --> prefix(Op, N),!, { N =< N1 }, ws, exprn(R,N), !, follow([Op,R], O, N1).
exprn(O,N1) --> "(" ,!, ws,  exprn(Op, 100), ws, ")" , follow(Op, O ,N1).
exprn(O,N1) --> "[" ,!, ws,  exprl(Op, 100), ws, "]" , follow([list|Op], O ,N1).
exprn(O,N1) --> "{" ,!, ws, block(Op, 100), ws, "}" , follow([block|Op], O ,N1).
exprn(O,N) --> item(L), !, follow(L,O,N).

% follow parts
idfollow(O,X,N1) --> {90 < N1},ws0, exprn(L1,90),!, exprl(L,90), !,follow([X|[L1|L]], O, N1). 
idfollow(O,X,N1) --> !,follow(id(X), O, N1). 

% every expression is ast-fragment then a follow. the fragment is passed
% to follow, to check for infix stuff (that contains it)
follow(L,O,N1) --> "[", ws, exprl(Op, 100), ws, "]" , follow(index(L,Op), O ,N1).
follow(L,O,N1) --> ws, (infix(Op,As,N) -> {assoc(As,N, N1)}), !,ws, exprn(R,N),!, follow([Op,L,R], O, N1).
follow(L,O,N1) --> ws, (postfix(Op,N) -> {N =< N1}), follow([Op,L], O, N1).
follow(L,O,N1) --> ws, ":;" , {99 =< N1} , follow([def,L,[]], O, N1).
follow(O,O,_) --> ws.

assoc(right, A, B) :-  A =< B.
assoc(left, A, B) :- A < B.

infix(def, right, 99) --> ":-".
infix(if,left,94) --> "->".
infix(unf, left,80) --> "=".
infix(le, right,60) --> ">=".
infix(ge,right,60) --> "=<".
infix(gt,right,60) --> ">".
infix(lt,right,60) --> "<".
infix(cons,right,55) --> ",".
infix(add,right,50) --> "+".
infix(sub,right,50) --> "-".
infix(mul,right,45) --> "*".
infix(div,right,45) --> "/".
infix(conj,right,95) --> "&&". 
infix(and,right,95) --> "and".
infix(disj,right,96) --> "||".
infix(or,right,96) --> "or".
infix(in,right,60) --> "in".

prefix(not,10) --> "!".
prefix(quote,5) --> "'".
prefix(eval,5) --> "`".
postfix(post,5) --> "?".

parse(X,S) :- phrase(block(S),X),!. 

% interpreter
exec(X,E,O) :-
    parse(X,S),
    eval([],E,S,O).

evalone(Ei,Eo,X,O) :- eval(Ei,Eo,X,O),!.

eval(_,_,id(fail),_) :- !,fail.
eval(E,E,X,X) :- number(X); X = [].
eval(E,E,[quote,X], X) :- !.
eval(Ei,Eo,[list|X],[list|O]) :- !,eval_list(Ei,Eo,X,O).
eval(Ei,Eo,[block|X],O) :-!, eval_block(Ei,Eo,X,[],O).
eval(Ei,Eo,id(X),O) :- !,variable(Ei,Eo,X,O).
eval(Ei,Eo,[def,X,Y],[]) :- !,define(Ei,Eo,X,Y),!.
eval(E,Eo,[and,X,Y],Z) :- evalone(E,E1,X,_),eval(E1,Eo,Y,Z).
eval(E,Eo,[if,X,Y],Z) :- (evalone(E,E1,X,_) -> (!, eval(E1,Eo,Y,Z))); !,Z =[].
eval(E,Eo,[or,X,Y],Z) :- evalone(E,Eo,X,Z); eval(E,Eo,Y,Z).
eval(E,Eo,[conj,X,Y],Z) :- eval(E,E1,X,_), eval(E1,Eo,Y,Z).
eval(E,Eo,[disj,X,Y],Z) :- eval(E,Eo,X,Z); eval(E,Eo,Y,Z).
eval(E,Eo,[eval|T],A) :- subst_args(E,E1,T,To),eval_block(E1,Eo,To,[],A).
eval(E,Eo,[C|T],A) :- fun_list(E,Ef,F,C),\+ F = [],!,subst_args(E,Eo,T,To),eval_fun(Ef,F,[C|To],A).
eval(E,Eo,[H|T],O) :- atom(H),!, eval_list(E,Eo,T,To), applyonce(H,To,O).

eval_list(E,E,[],[]).
eval_list(E,Eo,[H|T],[Ho|To]) :- eval(E,E1,H,Ho) , eval_list(E1,Eo,T,To).

eval_block(E,E,[],X,X). 
eval_block(E,Eo,[H|T],_,X) :- eval(E,E1,H,O) , eval_block(E1,Eo,T,O,X).

variable(E,E,'_',_):- !.
variable([K-V|E],[K-V|E],K,V) :-!.
variable([K|T],[K|To],X,O) :- variable(T,To,X,O),!.
variable(E,[K-V|E],K,V):- !.

% substitute arguments for calling from environment
subst_args(E,E,[],[]) :-!.
subst_args(E,Eo,id(X),O) :- variable(E,Eo,X,O),!.
subst_args(E,E,X,X) :- number(X); atom(X).
subst_args(E,E,[quote,X],[quote,X]) :-!.
subst_args(E,Eo,[block|X],O) :- !,eval_block(E,Eo,X,[],O).
subst_args(E,Eo,[H|T],[Ho|To]) :-  subst_args(E,E1,H,Ho),  subst_args(E1,Eo,T,To).

% evaluate against a given list of functions
eval_fun(Ef,[def(X,A)-V|_],[X|In],O) :- bind_args(Ef,Eo,A,In), eval(Eo,_,V,O).
eval_fun(Ef,[_|T],X,O) :- !, eval_fun(Ef,T,X,O).

% find all function defs
fun_list([],[],[],_).
fun_list([def(X,A)-V|T],[def(X,A)-V|Eo],[def(X,A)-V|O],X) :- fun_list(T,Eo,O,X).
fun_list([def(X,A)-V|T],[def(X,A)-V|Eo],O,F) :- fun_list(T,Eo,O,F).
fun_list([_|T],Eo,O,X) :- fun_list(T,Eo,O,X).

% bind the function def and calling arguments together
bind_args(E,E,[],[]):- !.
bind_args(E,Eo,id(X),O) :- variable(E,Eo,X,Op),!, O=Op,!.
bind_args(E,Eo,[cons,X,Y],[list|[Xa|Ya]]) :- !, bind_args(E,E1,X,Xa),!, bind_args(E1,Eo,Y,[list|Ya]).
bind_args(E,E1,[cons,X,[]],[list|Xa]) :- !, bind_args(E,E1,X,Xa),!.
bind_args(E,Eo,[H|T], [Ho|To]) :-!, bind_args(E,E1,H,Ho),!, bind_args(E1,Eo,T,To).
bind_args(E,E,X,X) :- !.


define(T,O ,[X|A],Y)  :- append(T, [def(X,A)-Y],O),!.
define(T,O ,id(X),Y)  :- append(T, [def(X,[])-Y],O),!.

applyonce(X,Y,Z) :- apply(X,Y,Z),!.

apply(add,[X,Y],O) :- O is X+Y .
apply(sub,[X,Y],O) :- O is X-Y .
apply(mul,[X,Y],O) :- O is X*Y .
apply(div,[X,Y],O) :- O is X/Y .
apply(unf,[X,Y],Y) :- X=Y.
apply(lt,[X,Y],Y) :-  X <Y.
apply(le,[X,Y],Y) :-  X =<Y.
apply(gt,[X,Y],Y) :-  X >Y.
apply(ge,[X,Y],Y) :-  X >=Y.
apply(say,X,[]) :- write(X),!.
apply(cons,[X,[list]],[list,X]).
apply(cons,[X,[list|Y]],[list|[X|Y]]).
