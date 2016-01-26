fun flatten oldList = 
	let
		fun fold oper id nil = id
		        | fold oper id (a::l) = oper(a, fold oper id l)
	in
		fold (op @) nil oldList
	end 
;

flatten [[1,2,3],[4],[5,6],[],[7]];
