% strucural unification
join(A,B,C) :- append(A,B,C),!;append([A],B,C).
%unify(_,_,L,R,_) :- writef("\nunify: (%w) (%w)\n",[L,R]), fail.
unify(E,Eo,L,R,O) :- (var(L) -> (var(R) -> (L=R, E=Eo,!);(!,unify_var(E,Eo,L,R),L=O));var(R), !, unify_var(E,Eo,R,L),R=O).
unify(E,E,[],[],[]) :- !.

unify(_,_,[],[H|_],_) :- var(H) , !, fail.
unify(_,_,[H|_],[],_) :- var(H) , !, fail.

unify(E,Eo,L,[p(P,A)|Rt],L) :-  var(L), !, unify_var_p(P,E,Eo,A,Rt,L).
unify(E,Eo,[p(P,A)|Lt],R,R) :-  var(R), !, unify_var_p(P,E,Eo,A,Lt,R).
unify(E,Eo,[L|Lt],[R|Rt],[L|O]) :-  var(L), !,unify_var(E,E1,L,R), unify(E1,Eo,Lt,Rt,O). 
unify(E,Eo,[L|Lt],[R|Rt],[R|O]) :-  var(R), !,unify_var(E,E1,R,L), unify(E1,Eo,Lt,Rt,O). 
unify(E,Eo,[p(P,A)|Lt],Ro,Ro) :-  !, unify_var(E,E1,R,Ro) ,unify_p_l(P,E1,Eo,A,Lt,R,_).
unify(E,Eo,Lo,[p(P,A)|Rt],Lo) :-  !, unify_var(E,E1,L,Lo), unify_p_l(P,E1,Eo,A,Rt,L,_).
unify(E,Eo,p(P,A),Ro,Ro) :-  !, unify_var(E,E1,R,Ro) ,unify_p_l(P,E1,Eo,A,[],R,_).
unify(E,Eo,Lo,p(P,A),Lo) :-  !, unify_var(E,E1,L,Lo) ,unify_p_l(P,E1,Eo,A,[],L,_).

unify(E,Eo,[Ho|To], [H|T],[Oh|Ot]) :-!,unify(E,E1,Ho,H,Oh),unify(E1,Eo,To,T,Ot).
unify(E,Eo,call(Ho,To), call(H,T),call(Oh,Ot)) :-!,unify(E,E1,Ho,H,Oh),unify(E1,Eo,To,T,Ot).
unify(E,Eo,lambda(Ho,To), lambda(H,T),lambda(Oh,Ot)) :-!,unify(E,E1,H,Ho,Oh), unify(E1,Eo,T,To,Ot).
unify(E,Eo,block(X),O,J) :- !, eval_block(E,E1,X,Xo), unify(E1,Eo,Xo,O,J).
unify(E,Eo,O,block(X),J) :- !, eval_block(E,E1,X,Xo), unify(E1,Eo,O,Xo,J).
unify(E,E,X,X,X) :- !.

unify_var(E,E,X,Y) :- var(Y),!,X=Y.
unify_var(E,Eo,[H|To],[H|T]) :-  var(H),!, unify_var(E,Eo,To,T).
unify_var(E,E,[],[]) :-!.
unify_var(E,Eo,O,p(P,A)) :- !, var(A) *-> unify_var_p(P,E,Eo,A,[],O); (unify_var_p(P,E,Eo,A,[],O),!).
unify_var(E,Eo,O,[p(P,A)|T]) :- !, var(A) *-> (unify_var_p(P,E,E1,A,[],Ho), join(Ho,To,O), unify_var(E1,Eo,To,T)); (unify_var_p(P,E,E1,A,[],Ho), join(Ho,To,O), unify_var(E1,Eo,To,T),!).

unify_var(E,Eo,[Ho|To],[H|T]) :- !,unify_var(E,E1,Ho,H), unify_var(E1,Eo,To,T).
unify_var(E,E,call(def,T), call(def,T)) :-!.
unify_var(E,Eo,call(Ho,To), call(H,T)) :-!,unify_var(E,E1,Ho,H),unify_var(E1,Eo,To,T).
unify_var(E,E,lambda(H,T), lambda(H,T)) :-!.
unify_var(E,Eo,O,block(X)) :- !, eval_block(E,E1,X,Xo), unify_var(E1,Eo,O,Xo).
unify_var(E,E,X,X) :- !.

unify_var_p(P,E,Eo,X,L,[p(P,X)|R]) :- var(X),!, unify_var(E,Eo,R,L).
unify_var_p(bind,E,Eo,[L1,L2],Lt,R) :-   !, unify_var(E,E1,R,L1), unify_var(E1,E2,L2,R), unify(E2,Eo,Lt,[],_).
unify_var_p(choice,E,Eo,[L1,L2],Lt,R) :-   !, (unify_var(E,E1,R,L1) *-> unify(E1,Eo,Lt,[],_); (unify_var(E,E1,R,L2), unify(E1,Eo,Lt,[],_))).
unify_var_p(ahead,E,Eo,L,Lt,R) :-   !,unify_var(E,E1,R,L), unify_var(E1,Eo,R,Lt).
unify_var_p(isnt,E,Eo,L,Lt,R) :-   !,\+ unify_var(E,_,[L],R), unify_var(E,Eo,R,Lt).
unify_var_p(any,E,Eo,L,Lt,R) :-   !,((unify_var(E,E1,R,L), unify(E1,Eo,Lt,[],_)); unify_var(E,Eo,R,Lt)).
unify_var_p(some,E,Eo,L,Lt,R) :-   !,unify_var(E,E1,R,L), unify(E1,Eo,Lt,[],_).
unify_var_p(maybe,E,Eo,L,Lt,[R|Rt]) :-  !,((unify_var(E,E1,R,L), unify(E1,Eo,Lt,Rt,_)); unify(E,Eo,Lt,[R|Rt],_)). 
unify_var_p(zany,E,Eo,L,Lt,R) :-   !,( unify_var(E,Eo,R,Lt);(unify_var(E,E1,R,L), unify(E1,Eo,Lt,[],_))).
unify_var_p(zsome,E,Eo,L,Lt,R) :-   !,unify_var(E,E1,R,L), unify(E1,Eo,Lt,[],_).
unify_var_p(zmaybe,E,Eo,L,Lt,[R|Rt]) :-  !,(unify(E,Eo,Lt,[R|Rt],_); (unify_var(E,E1,R,L), unify(E1,Eo,Lt,Rt,_))). 

unify_p_l(bind,E,Eo,[p(P,A),N],Lt,R,C):-  !,unify_p_l(P,E,E1,A,Lt,R,C),unify(E1,Eo,N,C,_).
unify_p_l(bind,E,Eo,[L1,L2],Lt,[R|Rt],R) :-  !, unify(E,E1,L1,R,O),unify(E1,E2,Lt,Rt,_),unify_var(E2,Eo,L2,O,_).
unify_p_l(bind,E,Eo,[L1,L2],Lt,R,R) :-  !, unify(E,E1,L1,R,O),unify(E1,E2,Lt,[],_),unify_var(E2,Eo,L2,O,_).
unify_p_l(choice,E,Eo,[L1,L2],Lt,[R|Rt],R) :- !, (unify(E,E1,L1,R,_) *-> unify(E1,Eo,Lt,Rt,_); (unify(E,E1,L2,R,_), unify(E1,Eo,Lt,Rt,_))).
unify_p_l(choice,E,Eo,[L1,L2],Lt,R,R) :- !, (unify(E,E1,L1,R,_) *-> unify(E1,Eo,Lt,[],_); (unify(E,E1,L2,R,_), unify(E1,Eo,Lt,[],_))).
unify_p_l(ahead,E,Eo,L,Lt,[R|Rt],[]) :- !,unify(E,E1,L,R,_), unify(E1,Eo,Lt,[R|Rt],_).
unify_p_l(ahead,E,Eo,L,Lt,R,R) :- !,unify(E,E1,L,R,_), unify(E1,Eo,Lt,R,_).
unify_p_l(isnt,E,Eo,L,Lt,R,R) :- !,\+unify(E,_,L,R,_), !,(R=[Rh|Rt], !,\+ unify(E,_,L,Rh,_),!,unify(E,Eo,Lt,[Rh|Rt],_));unify(E,Eo,Lt,R,_).
unify_p_l(any,E,Eo,[A|At],To,[Rh|Rt],[Rh|Ct]) :- unify(E,E1,A,Rh,_), unify_p_l(any,E1,Eo,At,To,Rt,Ct).
unify_p_l(any,E,Eo,[],T,To,[]):- !,unify(E,Eo,T,To,_).
unify_p_l(any,E,Eo,A,To,[Rh|Rt],[Rh|Ct]) :- unify(E,E1,A,Rh,_), unify_p_l(any,E1,Eo,A,To,Rt,Ct).
unify_p_l(any,E,Eo,_,T,To,[]):- unify(E,Eo,T,To,_).
unify_p_l(zany,E,Eo,[],T,To,[]) :- unify(E,Eo,T,To,_).
unify_p_l(zany,E,Eo,[A|At],To,[H|T],[H|C]) :- unify(E,E1,A,H,_), unify_p_l(zany,E1,Eo,At,To,T,C).
unify_p_l(some,E,Eo,[A|At],To,[H|T],[H|C]) :- unify(E,E1,A,H,_), unify_p_l(any,E1,Eo,At,To,T,C).
unify_p_l(zsome,E,Eo,[A|At],To,[H|T],[H|C]) :- unify(E,E1,A,H,_), unify_p_l(zany,E1,Eo,At,To,T,C).
unify_p_l(maybe,E,Eo,A,T,[H|To],H) :- unify(E,E1,A,H,_), unify(E1,Eo,T,To,_).
unify_p_l(maybe,E,Eo,_,T,To,_):- unify(E,Eo,T,To,_).
unify_p_l(zmaybe,E,Eo,_,T,To,_):- unify(E,Eo,T,To,_).
unify_p_l(zmaybe,E,Eo,A,T,[H|To],H) :- unify(E,E1,A,H,_), unify(E1,Eo,T,To,_).

