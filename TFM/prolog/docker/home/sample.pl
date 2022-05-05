father(paco, pepe).
father(juan, miguel).
mother(andrea, juan).
female(andrea).
male(miguel).
mother(maria, pepe).
female(maria).

parent(Dad,Child) :- father(Dad,Child).
parent(Mom,Child) :- mother(Mom,Child).

ancestor(F,S) :- parent(F, Z), ancestor(Z, S).
