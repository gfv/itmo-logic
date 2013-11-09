:- use_module(library(dcg/basics)).
:- use_module(library(pio)).
:- use_module(library(lists)).

% веселые аксиомы (l_ - это префикс не-встроенного предиката)
axiom(implies(Phi, implies(_Psi, Phi))).
axiom(implies(implies(Phi, Psi), implies(implies(Phi, implies(Psi, Pi)), implies(Phi, Pi)))).
axiom(implies(Phi, implies(Psi, l_and(Phi, Psi)))).
axiom(implies(l_and(Phi, _Psi), Phi)).
axiom(implies(l_and(_Phi, Psi), Psi)).
axiom(implies(Phi, l_or(Phi, _Psi))).
axiom(implies(Psi, l_or(_Phi, Psi))).
axiom(implies(implies(Phi, Psi), implies(implies(Psi, Pi), implies(l_or(Phi, Psi), Pi)))).
axiom(implies(implies(Phi, Psi), implies(implies(Phi, l_not(Psi)), l_not(Phi)))).

% не менее веселый modus ponens
modus_ponens(Phi, implies(Phi, Psi), Psi).

valid_expression(_Context, Expression) :- axiom(Expression).
valid_expression(Context, Expression) :-
        member(R1, Context),
        member(R2, Context),
        modus_ponens(R1, R2, Expression).

valid_proof(_Context, [], _Counter, success). % если больше не осталось утверждений на проверку - все хорошо
valid_proof(Context, [nil|Rest], Counter, Result) :- valid_proof(Context, Rest, Counter+1, Result). % пустые утверждения не нужны
valid_proof(Context, [Exp|RestExps], Counter, Result) :-
        valid_expression(Context, Exp), !,
        valid_proof([Exp|Context], RestExps, Counter+1, Result).
valid_proof(_Context, _Leftover, Counter, fail(Counter)).

verify_proof(ProofString, Result) :-
        proof(R, ProofString, []),
        valid_proof([], R, 1, Result).

portray_binary(L, R, Symbol) :- format('('), print(L), format(Symbol), print(R), format(')').
portray(var(Lst)) :- string_to_list(S, Lst), write(S).
portray(implies(L, R)) :- portray_binary(L, R, '->').
portray(l_and(L, R)) :- portray_binary(L, R, '&').
portray(l_or(L, R)) :- portray_binary(L, R, '|').
portray(l_not(Z)) :- format('!('), print(Z), format(')').

% Парсер начинается отсюда. С ума сойти, больше половины!
proof(Z) --> expression(Y), proof_tail([Y], Z).
proof_tail(Accum, Z) --> {reverse(Accum, Z)}.
proof_tail(Accum, Z) --> "\n", expression(Y), proof_tail([Y|Accum], Z).

% правоассоциативная импликация - это здорово!
expression(Z) --> disjunction(Z).
expression(Z) --> disjunction(X), "->", expression(Y), {Z = implies(X, Y)}.

% а вот левоассоциативность в DCG - это боль :/
disjunction(Z) --> conjunction(X), disjunction_tail(X, Z).
disjunction_tail(Accum, Z) --> {Z = Accum}.
disjunction_tail(Accum, Z) --> "|", conjunction(Y), disjunction_tail(l_or(Accum, Y), Z).

conjunction(Z) --> negation(X), conjunction_tail(X, Z).
conjunction_tail(Accum, Z) --> {Z = Accum}.
conjunction_tail(Accum, Z) --> "&", negation(Y), conjunction_tail(l_and(Accum, Y), Z).

negation(Z) --> "(", expression(Z), ")".
negation(Z) --> "!", negation(Y), {Z = l_not(Y)}.
negation(Z) --> variable(Z).

variable(Z) --> [C], variable_tail([C], Z), {"A" =< C, C =< "Z"}.
variable_tail(Accum, Z) --> {reverse(Accum, Y), Z = var(Y)}.
variable_tail(Accum, Z) --> [K], variable_tail([K|Accum], Z), {"0" =< K, K =< "9"}.



writeResult(success) :-
        format('Доказательство корректно.').

writeResult(fail(I)) :-
        format('Доказательство некорректно начиная с высказывания номер ~d', I).

writeResult(_) :- format('Sosnoole').

:-
        phrase_from_file(proof(P), 'in.txt'),
        valid_proof([], P, 1, Result),
        writeResult(Result).

        
%        open("out.txt", write, Out, type(text)),
        