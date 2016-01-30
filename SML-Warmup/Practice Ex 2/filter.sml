fun filter func lst = 
	let
		fun fold oper id nil = id
		        | fold oper id (a::l) = if func a then oper(a, fold oper id l) else fold oper id l
	in
		fold (op @) nil lst
	end 
;
filter (fn [x]=>x>0) [[~2], [0],[1], [2], [3]];

