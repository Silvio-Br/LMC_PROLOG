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

% reduit
% reduit(R, E, P, Q) : R est une règle de MM,
% E est une équation,
% P est un systeme d'équations,
% Q est un systeme d'équations résultant de l'application de R sur E

% application de la regle rename
% remplacement des occurrences de la variable X par la variable T
reduit(rename, E, P, Q) :- regle(E, rename), arg(1, E, X), arg(2, E, T), Q=P, X=T, !.

% application de la regle simplify
% remplacement des occurrences de la variable X par la constante T
reduit(simplify, E, P, Q) :- regle(E, simplify), arg(1, E, X), arg(2, E, T), X=T, Q=P, !.

% application de la regle expand
% remplacement des occurrences de la variable X par la fonction T
reduit(expand, E, P, Q) :- regle(E, expand), arg(1, E, X), arg(2, E, T), X=T, Q=P, !.

% application de la regle orient
% inverse T et X
reduit(orient, E, P, Q) :- regle(E, orient), arg(1, E, T), arg(2, E, X), append([X?=T], P, Q), !.

% application de la regle decompose
% decompose les fonctions X et T en une liste d'équations
reduit(decompose, E, P, Q) :- regle(E, decompose), arg(1, E, X), arg(2, E, T), X=..[_|L], T=..[_|K], union_list(L, K, R), append(R, P, Q), !.

% application de la regle clash
reduit(clash, _, _, _) :- fail.

% application de la regle check
reduit(check, _, _, _) :- fail.

% union_list
% union des termes de deux listes pour appliquer la regle decompose
union_list([X|A], [Y|B], C) :- union_list(A, B, D), append([X?=Y], D, C).
union_list([], [], C) :- C=[].


% unifie
% unifie(P) : P est un systeme d'équations à résoudre sous la forme d'une liste
% unifie(P, S) : P est un systeme d'équations à résoudre sous la forme d'une liste et S la stratégie utilisé pour le résoudre
% unifie([]) : termine l'éxécution du programme

unifie([E|P], choix_premier) :- choix_premier(P, Q, E, _), !, unifie(Q, choix_premier).
unifie([E|P], choix_pondere_1) :- choix_pondere_1(P, Q, E, _), !, unifie(Q, choix_pondere_1).
%unifie([E|P], choix_pondere_2) :- reduit(S, E, P, Q), unifie(P, S).

unifie([], _) :- write('\nTermine\n').

%Unifie avec un seul parametre (choix_premier)
unifie([E|P]) :- choix_premier(P, Q, E, _), !, unifie(Q).
unifie([]) :- write('\nTermine\n').


% Les différentes stratégies possibles pour le résolution de l'équation

choix_premier([], Q, [], R) :- write('terminé'), !.

% Stratégie de choix premier
% choix_premier(P, Q, E, R)
choix_premier(P, Q, E, R) :- reduit(R, E, P, Q).

% Stratégies de choix pondérés
% choix pondéré 1
choix_pondere_1([], Q, E, R) :- choix_reduit_1(E, R, _), reduit(R, E, [], Q).
choix_pondere_1(P, Q, E, R) :- parcours_liste_1(P, E, C, L), choix_reduit_1(C, R, _), reduit(R, C, L, Q).


% choix pondéré 2
%choix_pondere_2(P, Q, E, R) :-

%Choix de la règle à appliquer avec poids
%E représente l'équation à résoudre
%P représente le poids de la règle
choix_reduit_1(E, R, P):- regle(E, clash), P=7, R='clash', !;
regle(E, check), P=6, R='check', !;
regle(E, rename), P=5, R='rename', !;
regle(E, simplify), P=4, R='simplify', !;
regle(E, orient), P=3, R='orient', !;
regle(E, decompose), P=2, R='decompose', !;
regle(E, expand), P=1, R='expand', !.

%Comparaison des equations pour le choix pondéré 1
%Si les deux équations sont de poids différents, on choisit celle qui a le plus grand poids
%Si les deux équations sont de poids identiques, on choisit la première
compare_equation_1(E1, E2, E, O):- choix_reduit_1(E1, _, P1), choix_reduit_1(E2, _, P2), P1>=P2, E=E1, O=[E2], !; E=E2, O=[E1].

%Comparaison des equations pour le choix pondéré 2
%Si les deux équations sont de poids différents, on choisit celle qui a le plus grand poids
%Si les deux équations sont de poids identiques, on choisit la première
compare_equation_2(E1, E2, E, O):- choix_reduit_2(E1, _, P1), choix_reduit_2(E2, _, P2), P1>=P2, E=E1, !, E=E2.

%Parcour de la liste des équations pour le choix pondéré 1
%Si la liste est vide, on retourne l'équation
%Si la liste n'est pas vide, on compare les équations
parcours_liste_1([E1|[]], E2, E, L) :- compare_equation_1(E1, E2, E, L), !.
parcours_liste_1([E1|P], E2, E, L):- parcours_liste_1(P, E2, E3, L2), compare_equation_1(E1, E3, E4, C), E=E4, append(C, L2, L), !.



main :- unifie([f(Y)?=f(X), X?=a], choix_pondere_1).

% Lance le programme
:- trace, main.