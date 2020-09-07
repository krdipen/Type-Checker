assumeType([],[],[]).
assumeType([variable(X)|TAIL],[T1|T],[[variable(X),T1]|G]) :- assumeType(TAIL,T,G).

hasType([[variable(X),Type]|_],variable(X),T) :- Type = T, !.
hasType([[variable(_),_]|Tail],variable(X),T) :- hasType(Tail,variable(X),T).
hasType(_,E,tint) :- integer(E).
hasType(_,E,tbool) :- E = true.
hasType(_,E,tbool) :- E = false.
hasType(G,add(E1,E2),tint) :- hasType(G,E1,tint), hasType(G,E2,tint).
hasType(G,sbt(E1,E2),tint) :- hasType(G,E1,tint), hasType(G,E2,tint).
hasType(G,mul(E1,E2),tint) :- hasType(G,E1,tint), hasType(G,E2,tint).
hasType(G,div(E1,E2),tint) :- hasType(G,E1,tint), hasType(G,E2,tint).
hasType(G,and(E1,E2),tbool) :- hasType(G,E1,tbool), hasType(G,E2,tbool).
hasType(G,or(E1,E2),tbool) :- hasType(G,E1,tbool), hasType(G,E2,tbool).
hasType(G,not(E),tbool) :- hasType(G,E,tbool).
hasType(G,gt(E1,E2),tbool) :- hasType(G,E1,tint), hasType(G,E2,tint).
hasType(G,lt(E1,E2),tbool) :- hasType(G,E1,tint), hasType(G,E2,tint).
hasType(G,eq(E1,E2),tbool) :- hasType(G,E1,T), hasType(G,E2,T).
hasType(G,cond(E1,E2,E3),T) :- hasType(G,E1,tbool), hasType(G,E2,T), hasType(G,E3,T).
hasType(G,let(D,E),T) :- typeElaborates(G,D,G1), append(G1,G,G1G), hasType(G1G,E,T).
hasType(G,abst(X,E),arrow(T1,T2)) :- assumeType(X,T1,G1), append(G1,G,G1G), hasType(G1G,E,T2).
hasType(G,app(E1,E2),T1) :- hasType(G,E1,arrow(T2,T1)), hasType(G,E2,T2).
hasType(_,[],[]).
hasType(G,[HEAD|TAIL],[T1|TS]) :- hasType(G,HEAD,T1), hasType(G,TAIL,TS).
hasType(G,proj(1,[HEAD|_]),T) :- hasType(G,HEAD,T).
hasType(G,proj(N,[_|TAIL]),T) :- integer(N), M is N-1, hasType(G,proj(M,TAIL),T).

typeElaborates(G,def(variable(X),E),[[variable(X),T]]) :- hasType(G,E,T).
typeElaborates(G,seq(D1,D2),G2G1) :- typeElaborates(G,D1,G1), append(G1,G,G1G), typeElaborates(G1G,D2,G2), append(G2,G1,G2G1).
typeElaborates(G,pll(D1,D2),G2G1) :- typeElaborates(G,D1,G1), typeElaborates(G,D2,G2), append(G2,G1,G2G1).
typeElaborates(G,loc(D1,D2),G2) :- typeElaborates(G,D1,G1), append(G1,G,G1G), typeElaborates(G1G,D2,G2).
