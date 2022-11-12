:- style_check(-singleton).

% Définition de l'opérateur ?=
:- op(20,xfy,?=).

% Définition des règles de Martinelli-Montanari

% rename
% regle (x?=t, rename) : true si x et t sont des variables
% regle (x?=t, rename) : false sinon
regle(E, rename) :- arg(1, E, X), arg(2, E, T), var(X), var(T), !.

% simplify
% regle (x?=t, simplify) : true si x est une variable et t est une constante
% regle (x?=t, simplify) : false sinon
regle(E, simplify) :- arg(1, E, X), arg(2, E, T), var(X), atomic(T), !.

% expand
% regle (x?=t, expand) : true si t est composé et x n'apparait pas dans t
% regle (x?=t, expand) : false sinon
regle(E, expand) :- arg(1, E, X), arg(2, E, T), compound(T), var(X), \+ occur_check(X,T), !.

% check
% regle (x?=t, check) : true si x =/= t et x apparait dans t
% regle (x?=t, check) : false sinon
regle(E, check) :- arg(1, E, X), arg(2, E, T), var(X), X \== T, !, occur_check(X,T).

% orient
% regle (t?=x, orient) : true si x est une variable et t ne l'est pas
% regle (t?=x, orient) : false sinon
regle(E, orient) :- arg(1, E, T), arg(2, E, X), var(X), nonvar(T), !.


% decompose
% regle (x?=t, decompose) : true si x et t sont des fonctions de même symbole et la même arité
% regle (x?=t, decompose) : false sinon
regle(E, decompose) :- arg(1, E, X), arg(2, E, T), compound(X), compound(T), functor(X, N, A), functor(T, O, B), N==O, A==B, !.

% clash
% regle (x?=t, clash) : true si x et t sont des fonctions de même symbole et une arité différente ou x et t sont des fonctions de symboles différents
% regle (x?=t, clash) : false sinon
regle(E, clash) :- arg(1, E, X), arg(2, E, T), compound(X), compound(T), functor(X, N, A), functor(T, O, B), (N \== O ; A \== B), !.


% occur_check
% occur_check(X, T) : true si X apparait dans T
% occur_check(X, T) : false sinon
occur_check(X, T) :- compound(T), var(X), arg(_,T,V), (V==X ; (compound(V), occur_check(X, V)) ), !.

% application de la regle rename
% remplacement les occurences de la cariable X par la variable T
app(rename, E, P, Q) :- arg(1, E, X), arg(2, E, T), X=T, Q=P.

% application de la regle simplify
% remplacement les occurences de la cariable X par la constante T
app(simplify, E, P, Q) :- arg(1, E, X), arg(2, E, T), X=T, Q=P.

% application de la regle expand
% remplacement les occurences de la cariable X par la fonction T
app(expand, E, P, Q) :- arg(1, E, X), arg(2, E, T), X=T, Q=P.

% application de la regle orient
% inverse T et X
app(orient, E, P, Q) :- arg(1, E, T), arg(2, E, X), append([X?=T], P, Q).

% application de la regle decompose
% decompose les fonctions X et T en une liste d'équations
app(decompose, E, P, Q) :- arg(1, E, X), arg(2, E, T), X=..[_|L], T=..[_|K], union_list(L, K, R), append(R, P, Q).

% application de la regle clash
app(clash, _, _, _) :- fail.

% application de la regle check
app(check, _, _, _) :- fail.

% reduit
% reduit(R, E, P, Q) : true si R est une règle de MM,
% E est une équation,
% P est un systeme d'équations,
% Q est un systeme d'équations résultant de l'application de R sur E
reduit(R, E, P, Q) :- regle(E, R), app(R,E,P,Q), !.

% union_list
% union des termes de deux listes
union_list([X|A], [Y|B], C) :- union_list(A, B, D), append([X?=Y], D, C).
union_list([], [], C) :- C=[].

unifie([X|L]) :- reduit(decompose, X, L, R), write('Resultat : '), write(R), unifie(L).
unifie([]) :- write('\nTermine\n').




main :- write('Unification de : [f(c,d)?=f(a,b)]\n'),
        unifie([f(c,d)?=f(a,b)]).

% Lance le programme
:- main.