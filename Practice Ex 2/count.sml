fun counter func nil = 0
	| counter func (a::l) = 
		case (func a) of	
			true => 1 + (counter func l)
			| false => 0 + (counter func l)
;

counter (fn x=>x>0) [~2, ~10, 100, 0, 2, 3, 4];
