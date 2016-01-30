fun squareList l =
	let
		fun help(nl, l) =
			if l = [] then nl
			else
				help(nl@[hd(l) * hd(l)], tl(l))
	in	
		help ([], l)
	end

;
