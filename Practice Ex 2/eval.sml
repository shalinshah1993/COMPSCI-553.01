datatype expr =
	NUM of int
	| PLUS of expr * expr
	| MINUS of expr * expr
	| TIMES of expr * expr
	| DIV of expr * expr
	| F of expr list * (int list -> int)
;

fun eval exp = 
	case (exp) of 	
		NUM(x) => x
		| PLUS(x, y) => eval(x) + eval(y)
		| MINUS(x, y) => eval(x) - eval(y)
		| TIMES(x, y) => eval(x) * eval(y)
		| DIV(x, y) => eval(x) div eval(y)
;


eval(PLUS(NUM 2, NUM 3));
eval(MINUS(NUM 3, DIV(NUM 10, NUM 5)));
eval(TIMES(NUM 1, PLUS(NUM 1, NUM 1)));
eval(DIV(NUM 5, NUM 4));
