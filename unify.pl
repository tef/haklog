unify_some(E,Eo,[A|At],[H|T],To) :- unify(E,E1,A,H), unify_any(E1,Eo,At,T,To).
unify_zsome(E,Eo,[A|At],[H|T],To) :- unify(E,E1,A,H), unify_zany(E1,Eo,At,T,To).

unify_any(E,Eo,Ao,[any(H)|T],To) :- !, (unify(E,E1,A,H), append(A,At,Ao),unify_any(E1,Eo,At,T,To));Ao =[], T=To.
unify_any(E,Eo,[A|At],[H|T],To) :- unify(E,E1,A,H), unify_any(E1,Eo,At,T,To).
unify_any(E,E,[],T,T).

unify_zany(E,E,[],T,T).
unify_zany(E,Eo,[A|At],[H|T],To) :- unify(E,E1,A,H), unify_zany(E1,Eo,At,T,To).

unify_maybe(E,Eo,A,[H|T],T) :- unify(E,Eo,A,H).
unify_maybe(E,E,_,T,T).

unify_zmaybe(E,E,_,T,T).
unify_zmaybe(E,Eo,A,[H|T],T) :- unify(E,Eo,A,H).

% strucural unification
unify(E,E,L,R) :- var(L), var(R), L=R,!.
unify(E,Eo,L,R) :- var(R), !, unify_var(E,Eo,R,L).
unify(E,Eo,L,R) :- var(L), !, unify_var(E,Eo,L,R).
unify(E,E,[],[]) :- !.

% yikes this is a mess
unify(_,_,[],[H|_]) :- var(H) , !, fail.
unify(_,_,[H|_],[]) :- var(H) , !, fail.

unify(E,Eo,[L|Lt],[R|Rt]) :-  var(L), var(R), L=R,!, unify(E,Eo,Lt,Rt).
unify(E,Eo,[L|Lt],[R|Rt]) :- var(L), !,unify_var(E,E1,L,R), unify(E1,Eo,Lt,Rt). 
unify(E,Eo,[L|Lt],[R|Rt]) :-  var(R), !,unify_var(E,E1,R,L), unify(E1,Eo,Lt,Rt). 

unify(E,Eo,[bind(L1,L2)|Lt],R) :-  var(R), !, unify_var(E,E1,R,L1), unify_var(E1,E2,L2,R), unify(E2,Eo,Lt,[]).
unify(E,Eo,[choice(L1,L2)|Lt],R) :-  var(R), !, (unify_var(E,E1,R,L1) *-> unify(E1,Eo,Lt,[]); (unify_var(E,E1,R,L2), unify(E1,Eo,Lt,[]))).
unify(E,Eo,[ahead(L)|Lt],R) :-  var(R), !,unify_var(E,E1,R,[L]), unify_var(E1,Eo,R,Lt).
unify(E,Eo,[isnt(L)|Lt],R) :-  var(R), !,\+ unify_var(E,_,[L],R), unify_var(E,Eo,R,Lt).
unify(E,Eo,[any(L)|Lt],R) :-  var(R), !,((unify_var(E,E1,R,L), unify(E1,Eo,Lt,[])); unify_var(E,Eo,R,Lt)).
unify(E,Eo,[some(L)|Lt],R) :-  var(R), !,unify_var(E,E1,R,L), unify(E1,Eo,Lt,[]).
unify(E,Eo,[maybe(L)|Lt],[R|Rt]) :- var(R), !,((unify_var(E,E1,R,L), unify(E1,Eo,Lt,Rt)); unify(E,Eo,Lt,[R|Rt])). 
unify(E,Eo,[zany(L)|Lt],R) :-  var(R), !,( unify_var(E,Eo,R,Lt);(unify_var(E,E1,R,L), unify(E1,Eo,Lt,[]))).
unify(E,Eo,[zsome(L)|Lt],R) :-  var(R), !,unify_var(E,E1,R,L), unify(E1,Eo,Lt,[]).
unify(E,Eo,[zmaybe(L)|Lt],[R|Rt]) :- var(R), !,(unify(E,Eo,Lt,[R|Rt]); (unify_var(E,E1,R,L), unify(E1,Eo,Lt,Rt))). 

unify(E,Eo,L,[bind(R1,R2)|Rt]) :-  var(L), !, unify_var(E,E1,L,R1), unify_var(E1,E2,R2,L), unify(E2,Eo,[],Rt).
unify(E,Eo,L,[choice(R1,R2)|Rt]) :-  var(L), !, (unify_var(E,E1,L,R1) *-> unify(E1,Eo,[],Rt); (unify_var(E,E1,L,[R2]), unify(E1,Eo,[],Rt))).
unify(E,Eo,L,[isnt(R)|Rt]) :-  var(L), !,\+unify_var(E,_,L,[R]), unify_var(E,Eo,L,Rt).
unify(E,Eo,L,[any(R)|Rt]) :-  var(L), !,((unify_var(E,E1,L,R), unify(E1,Eo,[],Rt));unify_var(E,Eo,L,Rt)).
unify(E,Eo,L,[some(R)|Rt]) :-  var(L), !,unify_var(E,E1,L,R), unify(E1,Eo,[],Rt).
unify(E,Eo,[L|Lt],[maybe(R)|Rt]) :- var(L), !, ( (unify_var(E,E1,L,R), unify(E1,Eo,Lt,Rt)); unify(E,Eo,[L|Lt],Rt)). 
unify(E,Eo,L,[zany(R)|Rt]) :-  var(L), !,(unify_var(E,Eo,L,Rt);(unify_var(E,E1,L,R), unify(E1,Eo,[],Rt))).
unify(E,Eo,L,[zsome(R)|Rt]) :-  var(L), !,unify_var(E,E1,L,R), unify(E1,Eo,[],Rt).

unify(E,Eo,[bind(L1,L2)|Lt],R) :-  !, unify(E,E1,L1,R), unify_var(E1,E2,L2,R), unify(E2,Eo,Lt,[]).
unify(E,Eo,[choice(L1,L2)|Lt],R) :- !, (unify(E,E1,[L1],R) *-> unify(E1,Eo,Lt,[]); (unify(E,E1,[L2],R), unify(E1,Eo,Lt,[]))).
unify(E,Eo,[ahead(L)|Lt],R) :- !,unify(E,E1,[L],R), unify(E1,Eo,Lt,R).
unify(E,Eo,[isnt(L)|Lt],R) :- !,\+unify(E,_,[L],R), unify(E,Eo,Lt,R).
unify(E,Eo,[any(L)|Lt],R) :- !,unify_any(E,E1,L,R,Ro), unify(E1,Eo,Lt,Ro).
unify(E,Eo,[some(L)|Lt],R) :- !,unify_some(E,E1,L,R,Ro), unify(E1,Eo,Lt,Ro).
unify(E,Eo,[maybe(L)|Lt],R) :- !,unify_maybe(E,E1,L,R,Rt), unify(E1,Eo,Lt,Rt).
unify(E,Eo,[zany(L)|Lt],R) :- !,unify_zany(E,E1,L,R,Ro), unify(E1,Eo,Lt,Ro).
unify(E,Eo,[zsome(L)|Lt],R) :- !,unify_zsome(E,E1,L,R,Ro), unify(E1,Eo,Lt,Ro).
unify(E,Eo,[zmaybe(L)|Lt],R) :- !,unify_zmaybe(E,E1,L,R,Rt), unify(E1,Eo,Lt,Rt).

unify(E,Eo,L,[bind(R1,R2)|Rt]) :-  !, unify(E,E1,L,R1), unify_var(E1,E2,R2,L), unify(E2,Eo,[],Rt).
unify(E,Eo,L,[choice(R1,R2)|Rt]) :-  !, (unify(E,E1,L,R1) *-> unify(E1,Eo,[],Rt); (unify(E,E1,L,[R2]), unify(E1,Eo,[],Rt))).
unify(E,Eo,L,[ahead(R)|Rt]) :-!,unify(E,E1,L,[R]), unify(E1,Eo,L,Rt).
unify(E,Eo,L,[isnt(R)|Rt]) :-!,\+unify(E,_,L,[R]), unify(E,Eo,L,Rt).
unify(E,Eo,L,[any(R)|Rt]) :-!,unify_any(E,E1,R,L,Lo), unify(E1,Eo,Lo,Rt).
unify(E,Eo,L,[some(R)|Rt]) :-!,unify_some(E,E1,R,L,Lo), unify(E1,Eo,Lo,Rt).
unify(E,Eo,L,[maybe(R)|Rt]) :- !,unify_maybe(E,E1,R,L,Lt), unify(E1,Eo,Lt,Rt).
unify(E,Eo,L,[zany(R)|Rt]) :-!,unify_zany(E,E1,R,L,Lo), unify(E1,Eo,Lo,Rt).
unify(E,Eo,L,[zsome(R)|Rt]) :-!,unify_zsome(E,E1,R,L,Lo), unify(E1,Eo,Lo,Rt).
unify(E,Eo,L,[zmaybe(R)|Rt]) :- !,unify_zmaybe(E,E1,R,L,Lt), unify(E1,Eo,Lt,Rt).

unify(E,Eo,[Ho|To],[H|T]) :-!,write("shci"),unify(E,E1,Ho,H),unify(E1,Eo,To,T).
 
unify(E,Eo,bind(L,N),R) :-  unify(E,E1,L,R), unify_var(E1,Eo,N,R).
unify(E,Eo,choice(L1,L2),R) :- !,(unify(E,Eo,[L1],R) *->true; unify(E,Eo,[L2],R)).
unify(E,Eo,ahead(L),R) :- !,unify(E,E1,L,R), unify(E1,Eo,[],R).
unify(E,Eo,isnt(L),R) :- !,\+unify(E,_,L,R), unify(E,Eo,[],R).
unify(E,Eo,any(L),R) :- !,unify_any(E,E1,L,R,Ro), unify(E1,Eo,[],Ro).
unify(E,Eo,some(L),R) :- !,unify_some(E,E1,L,R,Ro), unify(E1,Eo,[],Ro).
unify(E,Eo,maybe(L),R) :- !,unify_maybe(E,E1,L,R,Rt), unify(E1,Eo,[],Rt).
unify(E,Eo,zany(L),R) :- !,unify_zany(E,E1,L,R,Ro), unify(E1,Eo,[],Ro).
unify(E,Eo,zsome(L),R) :- !,unify_zsome(E,E1,L,R,Ro), unify(E1,Eo,[],Ro).
unify(E,Eo,zmaybe(L),R) :- !,unify_zmaybe(E,E1,L,R,Rt), unify(E1,Eo,[],Rt).
unify(E,Eo,L,bind(R,N)) :-  !,unify(E,E1,L,R), unify_var(E1,Eo,L,N).
unify(E,Eo,L,choice(R1,R2)) :- !,(unify(E,Eo,L,[R1]) *-> true; unify(E,Eo,L,[R2])).
unify(E,Eo,L,ahead(R)) :-!,unify(E,E1,L,R), unify(E1,Eo,[],R).
unify(E,Eo,L,isnt(R)) :-!,\+,unify(E,_,L,R), unify(E,Eo,[],R).
unify(E,Eo,L,any(R)) :-!,unify_any(E,E1,R,L,Lo), unify(E1,Eo,Lo,[]).
unify(E,Eo,L,some(R)) :-!,unify_some(E,E1,R,L,Lo), unify(E1,Eo,Lo,[]).
unify(E,Eo,L,maybe(R)) :- !,unify_maybe(E,E1,R,L,Lt), unify(E1,Eo,Lt,[]).
unify(E,Eo,L,zany(R)) :-!,unify_zany(E,E1,R,L,Lo), unify(E1,Eo,Lo,[]).
unify(E,Eo,L,zsome(R)) :-!,unify_zsome(E,E1,R,L,Lo), unify(E1,Eo,Lo,[]).
unify(E,Eo,L,zmaybe(R)) :- !,unify_zmaybe(E,E1,R,L,Lt), unify(E1,Eo,Lt,[]).
unify(E,Eo,call(Ho,To), call(H,T)) :-!,unify(E,E1,Ho,H),unify(E1,Eo,To,T).
unify(E,Eo,lambda(Ho,To), lambda(H,T)) :-!,unify(E,E1,H,Ho), unify(E1,Eo,T,To).

unify(E,Eo,block(X),O) :- !, eval_block(E,E1,X,Xo), unify(E1,Eo,Xo,O).
unify(E,Eo,O,block(X)) :- !, eval_block(E,E1,X,Xo), unify(E1,Eo,O,Xo).

unify(E,E,X,X) :- !.

unify_var(E,E,[],[]) :-!.
unify_var(E,Eo,O,bind(H,N)) :-  !,unify_var(E,E1,O,H), unify_var(E1,Eo,N,O).
unify_var(E,Eo,O,choice(H1,H2)) :- !, (unify_var(E,Eo,O,H1) *-> true; unify_var(E,Eo,O,H2)).
unify_var(E,Eo,ahead(Ho),ahead(H)) :- !, unify_var(E,Eo,Ho,H).
unify_var(E,Eo,isnt(Ho),isnt(H)) :- !, unify_var(E,Eo,Ho,H).
unify_var(E,Eo,any(Ho),any(H)) :- !, unify_var(E,Eo,Ho,H).
unify_var(E,Eo,zany(Ho),zany(H)) :- !, unify_var(E,Eo,Ho,H).
unify_var(E,Eo,some(Ho),some(H)) :- !, unify_var(E,Eo,Ho,H).
unify_var(E,Eo,zsome(Ho),zsome(H)) :- !, unify_var(E,Eo,Ho,H).
unify_var(E,Eo,maybe(Ho),maybe(H)) :- !, unify_var(E,Eo,Ho,H).
unify_var(E,Eo,zmaybe(Ho),zmaybe(H)) :- !, unify_var(E,Eo,Ho,H).
unify_var(E,Eo,O,[bind(H,N)|Rt]) :-  !,unify_var(E,E1,O,H), unify_var(E1,E2,N,O), unify(E2,Eo,[],Rt).
unify_var(E,Eo,O,[choice(H1,H2)|T]) :- !, (unify_var(E,E1,O,H1) *-> unify(E1,Eo,[],T); (unify_var(E,E1,O,H2), unify(E1,Eo,[],T))).
unify_var(E,Eo,O,[ahead(H)|T]) :- !, unify_var(E,E1,O,H), unify(E1,Eo,O,T).
unify_var(E,Eo,O,[isnt(H)|T]) :- !, \+unify_var(E,_,O,H), unify(E,Eo,O,T).
unify_var(E,Eo,O,[any(H)|T]) :- !, ((unify_var(E,E1,O,H), unify(E1,Eo,[],T)); unify_var(E,Eo,O,T)).
unify_var(E,Eo,O,[zany(H)|T]) :- !, ( unify_var(E,Eo,O,T); (unify_var(E,E1,O,H), unify(E1,Eo,[],T))).
unify_var(E,Eo,O,[some(H)|T]) :- !, ((unify_var(E,E1,O,H), unify(E1,Eo,[],T)); unify_var(E,Eo,O,T)).
unify_var(E,Eo,O,[zsome(H)|T]) :- !, ( unify_var(E,Eo,O,T); (unify_var(E,E1,O,H), unify(E1,Eo,[],T))).
unify_var(E,Eo,O,[maybe(H)|T]) :- !, ((unify_var(E,E1,Ho,H), unify_var(E1,Eo,To,T), O=[Ho|To]); unify_var(E,Eo,O,T)).
unify_var(E,Eo,O,[zmaybe(H)|T]) :- !, ( unify_var(E,Eo,O,T);(unify_var(E,E1,Ho,H), unify_var(E1,Eo,To,T), O=[Ho|To])).
unify_var(E,Eo,[Ho|To],[H|T]) :- !,unify_var(E,E1,Ho,H), unify_var(E1,Eo,To,T).
unify_var(E,Eo,call(Ho,To), call(H,T)) :-!,unify_var(E,E1,Ho,H),unify_var(E1,Eo,To,T).
unify_var(E,Eo,lambda(Ho,To), lambda(H,T)) :-!,unify_var(E,E1,H,Ho), unify_var(E1,Eo,T,To).
unify_var(E,Eo,O,block(X)) :- !, eval_block(E,E1,X,Xo), unify_var(E1,Eo,O,Xo).
unify_var(E,E,X,X) :- !.
