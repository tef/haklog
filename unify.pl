% strucural unification
join(A,[],A) :-!.
join(A,B,C) :- append(A,B,C).

unify(E,E,L,R) :- var(L), var(R), L=R,!.
unify(E,Eo,L,R) :- var(R), !, unify_var(E,Eo,R,L).
unify(E,Eo,L,R) :- var(L), !, unify_var(E,Eo,L,R).
unify(E,E,[],[]) :- !.

% yikes this is a mess
unify(_,_,[],[H|_]) :- var(H) , !, fail.
unify(_,_,[H|_],[]) :- var(H) , !, fail.

unify(E,Eo,[L|Lt],[R|Rt]) :-  var(L), var(R), L=R,!, unify(E,Eo,Lt,Rt).
unify(E,Eo,L,[p(P,A)|Rt]) :-  var(L), !, unify_var_p(P,E,Eo,A,Rt,L).
unify(E,Eo,[p(P,A)|Lt],R) :-  var(R), !, unify_var_p(P,E,Eo,A,Lt,R).
unify(E,Eo,[L|Lt],[R|Rt]) :-  var(L), !,unify_var(E,E1,L,R), unify(E1,Eo,Lt,Rt). 
unify(E,Eo,[L|Lt],[R|Rt]) :-  var(R), !,unify_var(E,E1,R,L), unify(E1,Eo,Lt,Rt). 
unify(E,Eo,[p(P,A)|Lt],Ro) :-  !, unify_var(E,E1,R,Ro) ,unify_p_l(P,E1,Eo,A,Lt,R).
unify(E,Eo,Lo,[p(P,A)|Rt]) :-  !, unify_var(E,E1,L,Lo), unify_p_l(P,E1,Eo,A,Rt,L).
unify(E,Eo,p(P,A),Ro) :-  !, unify_var(E,E1,R,Ro) ,unify_p_l(P,E1,Eo,A,[],R).
unify(E,Eo,Lo,p(P,A)) :-  !, unify_var(E,E1,L,Lo) ,unify_p_l(P,E1,Eo,A,[],L).

unify(E,Eo,call(Ho,To), call(H,T)) :-!,unify(E,E1,Ho,H),unify(E1,Eo,To,T).
unify(E,Eo,lambda(Ho,To), lambda(H,T)) :-!,unify(E,E1,H,Ho), unify(E1,Eo,T,To).
unify(E,Eo,block(X),O) :- !, eval_block(E,E1,X,Xo), unify(E1,Eo,Xo,O).
unify(E,Eo,O,block(X)) :- !, eval_block(E,E1,X,Xo), unify(E1,Eo,O,Xo).
unify(E,E,X,X) :- !.

unify_var_p(bind,E,Eo,[L1,L2],Lt,R) :-   !, unify_var(E,E1,R,L1), unify_var(E1,E2,L2,R), unify(E2,Eo,Lt,[]).
unify_var_p(choose,E,Eo,[(L1,L2)],Lt,R) :-   !, (unify_var(E,E1,R,L1) *-> unify(E1,Eo,Lt,[]); (unify_var(E,E1,R,L2), unify(E1,Eo,Lt,[]))).
unify_var_p(ahead,E,Eo,L,Lt,R) :-   !,unify_var(E,E1,R,[L]), unify_var(E1,Eo,R,Lt).
unify_var_p(isnt,E,Eo,L,Lt,R) :-   !,\+ unify_var(E,_,[L],R), unify_var(E,Eo,R,Lt).
unify_var_p(any,E,Eo,L,Lt,R) :-   !,((unify_var(E,E1,R,L), unify(E1,Eo,Lt,[])); unify_var(E,Eo,R,Lt)).
unify_var_p(some,E,Eo,L,Lt,R) :-   !,unify_var(E,E1,R,L), unify(E1,Eo,Lt,[]).
unify_var_p(maybe,E,Eo,L,Lt,[R|Rt]) :-  !,((unify_var(E,E1,R,L), unify(E1,Eo,Lt,Rt)); unify(E,Eo,Lt,[R|Rt])). 
unify_var_p(zany,E,Eo,L,Lt,R) :-   !,( unify_var(E,Eo,R,Lt);(unify_var(E,E1,R,L), unify(E1,Eo,Lt,[]))).
unify_var_p(zsome,E,Eo,L,Lt,R) :-   !,unify_var(E,E1,R,L), unify(E1,Eo,Lt,[]).
unify_var_p(zmaybe,E,Eo,L,Lt,[R|Rt]) :-  !,(unify(E,Eo,Lt,[R|Rt]); (unify_var(E,E1,R,L), unify(E1,Eo,Lt,Rt))). 

unify_p_l(bind,E,Eo,[L1,L2],Lt,R) :-  !, unify(E,E1,L1,R), unify_var(E1,E2,L2,R), unify(E2,Eo,Lt,[]).
unify_p_l(choice,E,Eo,[L1,L2],Lt,R) :- !, (unify(E,E1,[L1],R) *-> unify(E1,Eo,Lt,[]); (unify(E,E1,[L2],R), unify(E1,Eo,Lt,[]))).
unify_p_l(ahead,E,Eo,L,Lt,R) :- !,unify(E,E1,[L],R), unify(E1,Eo,Lt,R).
unify_p_l(isnt,E,Eo,L,Lt,R) :- !,\+unify(E,_,[L],R), unify(E,Eo,Lt,R).
unify_p_l(any,E,Eo,[A|At],To,[Rh|Rt]) :- unify(E,E1,A,Rh), unify_p_l(any,E1,Eo,At,To,Rt).
unify_p_l(any,E,Eo,[],T,To):-unify(E,Eo,T,To).
unify_p_l(zany,E,Eo,[],T,To) :- unify(E,Eo,T,To).
unify_p_l(zany,E,Eo,[A|At],To,[H|T]) :- unify(E,E1,A,H), unify_p_l(zany,E1,Eo,At,To,T).
unify_p_l(some,E,Eo,[A|At],To,[H|T]) :- unify(E,E1,A,H), unify_p_l(any,E1,Eo,At,To,T).
unify_p_l(zsome,E,Eo,[A|At],To,[H|T]) :- unify(E,E1,A,H), unify_p_l(zany,E1,Eo,At,To,T).
unify_p_l(maybe,E,Eo,A,T,[H|T]) :- unify(E,Eo,A,H).
unify_p_l(maybe,E,Eo,_,T,To):- unify(E,Eo,T,To).
unify_p_l(zmaybe,E,Eo,_,T,To):- unify(E,Eo,T,To).

unify_var(E,E,[],[]) :-!.
unify_var(E,Eo,O,p(P,A)) :- !, unify_var_p(P,E,Eo,A,[],O).
unify_var(E,Eo,O,[p(P,A)|T]) :- !, unify_var_p(P,E,Eo,A,T,O).
unify_var(E,Eo,[Ho|To],[H|T]) :- !,unify_var(E,E1,Ho,H), unify_var(E1,Eo,To,T).
unify_var(E,Eo,call(Ho,To), call(H,T)) :-!,unify_var(E,E1,Ho,H),unify_var(E1,Eo,To,T).
unify_var(E,Eo,lambda(Ho,To), lambda(H,T)) :-!,unify_var(E,E1,H,Ho), unify_var(E1,Eo,T,To).
unify_var(E,Eo,O,block(X)) :- !, eval_block(E,E1,X,Xo), unify_var(E1,Eo,O,Xo).
unify_var(E,E,X,X) :- !.
