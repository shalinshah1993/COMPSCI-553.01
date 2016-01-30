fun isPrime (n:int) =
	let 
		fun help(n, d) =
			if d = 1 then true
			else 
				if n mod d = 0 then false 
				else help(n, d-1)
	in
		help(n, n-1) 
	end

;

