functor F (M: ORD_MAP where type Key.ord_key = string) (S: ORD_SET where type Key.ord_key = string) :>
	sig
		val proc: string list -> S.set M.map
	end
	=
	struct
		fun proc fileList = 
			let		
					fun map f nil = nil
						    |	map f (a::l) = (f a)::(map f l);

				    fun fold opr id nil = nil
				    	|	fold opr id (a::l) = opr(a, fold opr id l);

					fun makeMapSet fileName wordToInsert = 
						M.insert(M.empty, wordToInsert, S.add(S.empty, fileName));

					fun union nil = M.empty | 
						union (a::l) = M.unionWith (S.union) (a, union l);

					fun readFromFile (infile:string) = 
						let 
							val ins = TextIO.openIn infile 
							fun loop ins = 
								case TextIO.inputLine ins of 
									SOME line => fold (op @) nil (map (String.tokens (fn x => x = #"\n")) (String.tokens (fn x => x = #" ") line)) :: loop ins 
									| NONE => [] 
						in 
							(map (makeMapSet infile) (fold (op @) nil (loop ins before TextIO.closeIn ins)))
						end;
			in
				  union (fold (op @) nil (map readFromFile fileList))
			end
	end
;

structure memberSet = BinarySetFn(struct 
									type ord_key = string
									val compare = String.compare
								end);

structure memberMap = BinaryMapFn(struct 
									type ord_key = string
									val compare = String.compare
								end);

structure output = F (memberMap) (memberSet);