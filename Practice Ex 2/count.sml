fun counter func lst =
	let
		val boolList = (
						let
					 		fun help func lst =
								let 
									fun fold oper id nil = id
								        | fold oper id (a::l) = oper(func a, fold oper id l)
								in
										fold (op @) nil lst
								end
						in
							help func lst
						end
						)

		fun countHelp func nil = 0
			| countHelp func (a::l) = 
				case a of	
					true => 1 + (countHelp func l)
					| false => 0 + (countHelp func l)
	in 
		countHelp func boolList
	end
;

counter (fn [x]=>[x>0]) [[~2], [~10], [100], [0], [2], [3], [4]];