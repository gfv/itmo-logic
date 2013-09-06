:- use_module(library(dcg/basics)).

axiom(nil). % костыль, который говорит, что, ничего не утверждая, мы правы
axiom(follows(Phi, follows(_Psi, Phi))).
axiom(follows(follows(Phi, Psi), follows(follows(Phi, follows(Psi, _Pi)), follows(Phi, Psi)))).
axiom(follows(Phi, follows(Psi, and(Phi, Psi)))).
axiom(follows(l_and(Phi, _Psi), Phi)).
axiom(follows(l_and(_Phi, Psi), Psi)).
axiom(follows(Phi, l_or(Phi, _Psi))).
axiom(follows(Psi, l_or(_Phi, Psi))).
axiom(follows(follows(Phi, Psi), follows(follows(Psi, Pi), follows(l_or(Phi, Psi), Pi)))).
axiom(follows(follows(Phi, Psi), follows(follows(Phi, l_not(Psi)), l_not(Phi)))).

modus_ponens(Phi, follows(Phi, Psi), Psi).

valid_expression(_Context, Expression) :- axiom(Expression).
valid_expression(Context, Expression) :-
        member(R1, Context),
        member(R2, Context),
        modus_ponens(R1, R2, Expression).

valid_proof(_Context, []) :- true.
valid_proof(Context, [Exp|RestExps]) :-
        valid_expression(Context, Exp), !,
        valid_proof([Exp|Context], RestExps).

valid_proof(Proof) :- valid_proof([], Proof).

%expression(Ex) --> [].
%expression(Ex) --> "(", expression, ")".
%expression(Ex) --> 
