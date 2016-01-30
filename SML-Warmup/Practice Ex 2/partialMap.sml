fun mapPartial func lst = 
	let
		fun fold oper id nil = id
		        | fold oper id (a::l) = oper(case (if func a then SOME a else NONE) of SOME a => a | NONE => nil, fold oper id l)
	in
		fold (op @) nil lst
	end 
;
mapPartial (fn [x]=>x > 0) [[~2], [0], [1], [2], [3]];