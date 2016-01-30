fun map func lst = 
	let
		fun fold oper id nil = id
		        | fold oper id (a::l) = oper(func a, fold oper id l)
	in
		fold (op @) nil lst
	end 
;
map (fn [x]=>[x+1]) [[1], [2], [3]];
map (fn [x]=>[x*x]) [[1], [2], [3]];

