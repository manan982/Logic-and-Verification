/* 
1) YES
2) YES
3) YES 
4) NO 
5) YES
6) NO
7) YES
8) NO
9) NO
10) YES
*/

?-op(140, fy, neg).
?-op(160, xfy, [and, or, imp, revimp, uparrow, downarrow, notimp, notrevimp, equiv, notequiv]).

/* Returns true if the element is a member of the List  */ 

member(X, [X | _]).

member(X, [_ | Tail]) :- 
    member(X, Tail).

/* returns the new list after removing all instances of a certain element */

remove(X, [], []).

remove(X, [X | Tail], Newtail) :-
    remove(X, Tail, Newtail).

remove(X, [Head | Tail], [Head | Newtail]) :-
    remove(X, Tail, Newtail).

/* conjuctive(X) :- a predicate for if X is an alpha formula. */

conjunctive(_ and _).
conjunctive(neg(_ or _)).
conjunctive(neg(_ imp _)).
conjunctive(neg(_ revimp _)).
conjunctive(neg(_ uparrow _)).
conjunctive(_ downarrow _).
conjunctive(_ notimp _).
conjunctive(_ notrevimp _).

conjunctive(_ equiv _). 
conjunctive(neg(_ notequiv _)). 

/* disjunctive(X) :- a predicate for if X is a beta formula. */

disjunctive(neg(_ and _)).
disjunctive(_ or _).
disjunctive(_ imp _).
disjunctive(_ revimp _).
disjunctive(_ uparrow _).
disjunctive(neg(_ downarrow _)).
disjunctive(neg(_ notimp _)).
disjunctive(neg(_ notrevimp _)). 

disjunctive(neg(_ equiv _)).
disjunctive(_ notequiv _). 

/* a predicate for if X is a double negation, or a negated constant. */

unary(neg neg _).
unary(neg true).
unary(neg false).

/* Y and Z are the components of the formula X, as defined in the alpha and beta tables. */

components(X and Y, X, Y).
components(neg(X and Y), neg X, neg Y).

components(X or Y, X, Y).
components(neg(X or Y), neg X, neg Y).

components(X imp Y, neg X, Y).
components(neg(X imp Y), X, neg Y). 

components(X revimp Y, X, neg Y).
components(neg(X revimp Y), neg X, Y).

components(X uparrow Y, neg X, neg Y).
components(neg(X uparrow Y), X, Y).

components(X downarrow Y, neg X, neg Y).
components(neg(X downarrow Y), X, Y).

components(X notimp Y, X, neg Y).
components(neg(X notimp Y), neg X, Y).

components(X notrevimp Y, neg X, Y).
components(neg(X notrevimp Y), X, neg Y).

/* Equiv and nonequiv components added */

components(X equiv Y, X imp Y, Y imp X).
components(neg(X equiv Y), neg(X imp Y), neg(Y imp X)).

components(X notequiv Y, neg(X imp Y), neg(Y imp X)).
components(neg(X notequiv Y), X imp Y, Y imp X).


 /* Y is the component of the unary formula X. */

component(neg neg X, X).
component(neg true, false).
component(neg false, true).


/* several resolutionstep predicates which represent resolution proof steps. Simplifying unaray formulas, alpha and the beta rule are defined along with the actual resolution step  */

resolutionstep([Disjunction | Rest], New) :- 
    member(Formula, Disjunction),
    unary(Formula),
    component(Formula, Newformula),
    remove(Formula, Disjunction, Temporary),
    NewDisjunction = [Newformula | Temporary],
    New = [NewDisjunction | Rest].


/* Applying the beta rule in the resolution process */

resolutionstep([Disjunction | Rest], New) :- 
    member(Beta, Disjunction),
    disjunctive(Beta),
    components(Beta, Betaone, Betatwo),
    remove(Beta, Disjunction, Temporary),
    NewDisjunction = [Betaone, Betatwo | Temporary],
    New = [NewDisjunction | Rest].

/* Applying the alpha rule in the resolution process */

resolutionstep([Disjunction | Rest], New) :- 
    member(Alpha, Disjunction),
    conjunctive(Alpha),
    components(Alpha, Alphaone, Alphatwo), 
    remove(Alpha, Disjunction, Temporary),
    NewDisjunction1 = [Alphaone | Temporary],
    NewDisjunction2 = [Alphatwo | Temporary],
    New = [NewDisjunction1, NewDisjunction2 | Rest].


resolutionstep([Disjunction | Rest], [Disjunction | Newrest]) :- 
    resolutionstep(Rest, Newrest).

/* The actual resolution rule, remove instances of a clause and its negated clause from a formula if both are found */

resolutionstep([negClause | Rest], formula) :- 
     member(neg(negClause), Rest), 
     formula = [negClause | Rest],
     remove(negClause, formula, formula2), 
     remove(neg(negClause), formula2, newForm), 
	 New = [newForm].

/* Calling resolution step indefinetely until no longer possible to see if a resolution proof exists */
resolution(Conjuction, NewConjuction) :-
    resolutionstep(Conjuction, Formula),
    resolution(Formula, NewConjuction).

resolution(Conjuction, Conjuction).

/* Y is the CNF of X. */

clauseform(X, Y) :- resolution([[X]], Y).


expand_and_close(Resolution) :-closed(Resolution).

expand_and_close(Resolution) :- resolutionstep(Resolution, NewResolution), !, expand_and_close(NewResolution).


closed([Branch | Rest]) :-
    member(false, Branch),
    closed(Rest).

closed([Branch | Rest]) :-
    member(X, Branch),
    member(neg X, Branch),
    closed(Rest).

closed([]).

/* Checking if the complete resolution proof for X is closed.*/

test(X) :- if_then_else(expand_and_close([[X]]), yes, no).

yes :- write('YES').
no :- write('NO').


/* Either (A & B) V (!A & !C). */
if_then_else(A, B, C) :- A, !, B.

if_then_else(A, B, C) :- C.