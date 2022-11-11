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

% decompose
% regle (x?=t, decompose) : true si x et t sont des fonctions de même symbole et la même arité
% regle (x?=t, decompose) : false sinon
regle(E, decompose) :- arg(1, E, X), arg(2, E, T), compound(X), compound(T), functor(X, N, A), functor(T, O, B), N==O, A==B, !.

% clash

% occur_check
occur_check(X, T) :- %TODO !.
