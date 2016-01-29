functor F (M: ORD_MAP where type Key.ord_key = string) (S: ORD_SET where type Key.ord_key = string)
	(*sig
		val proc: string list -> S.set M.map
	end*)
	=
	struct
		fun proc fileList = 
			let		
					fun map f nil = nil
						    |	map f (a::l) = (f a)::(map f l);

				    fun fold opr id nil = nil
				    	|	fold opr id (a::l) = opr(a, fold opr id l);

					fun makeMapSet wordToInsert fileName = 
						M.insert(M.empty, wordToInsert, S.add(S.empty, fileName));

					fun union nil = M.empty | 
						union (a::l) = M.unionWith (op @) (a, union l);

					fun readFromFile (infile:string) = 
						let 
							val ins = TextIO.openIn infile 
							fun loop ins = 
								case TextIO.inputLine ins of 
									SOME line => fold (op @) nil (map (String.tokens (fn x => x = #"\n")) (String.tokens (fn x => x = #" ") line)) :: loop ins 
									| NONE => [] 
						in 
							fold (op @) nil (loop ins before TextIO.closeIn ins))
						end;
			in
				 (fold (op @) nil (map readFromFile fileList))
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
output.proc ["input1.txt", "input2.txt"];

(*val rootSet = memberSet.addList(memberSet.empty, ["file1.txt", "file2.txt", "file3.txt", "file4.txt"]);
memberSet.numItems rootSet;*)
(*fun fold opr id nil = nil  	|	fold opr id (a::l) = opr(a, fold opr id l);
fun map f nil = nil		    |	map f (a::l) = (f a)::(map f l);


val root1 = memberMap.insert(memberMap.empty, "root1", ["rootSet", "child"]);
val root2 = memberMap.insert(memberMap.empty, "root2", ["hah", "nag"]);
val root3 = memberMap.insert(memberMap.empty, "root3", ["haha", "naga"]);*)
(*memberMap.find(root, "root");*)
(*memberMap.numItems (memberMap.unionWith (op @) (root1, root2));*)
(*fun loop nil = memberMap.empty | 
			loop (a::l) = memberMap.unionWith (op @) (a, loop l);
;
loop [root1, root2, root3];*)

(*val rootNodeMap = memberMap.insert(memberMap.empty, "root", memberSet.add(rootNodeSet, "root"));
memberMap.insert(rootNodeMap, "word2", memberSet.add(memberSet.empty, "fileName2"));
memberMap.insert(rootNodeMap, "word3", memberSet.add(memberSet.empty, "fileName3"));*)

