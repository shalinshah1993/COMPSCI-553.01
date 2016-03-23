signature TRANSLATE =
sig
	type level
	type access (*not the same as Frame.access*)
	type exp
	
	(*structure Frame : FRAME -- In book, but idk why? *)
	
	val outermost : level
	val newLevel : {parent: level, name: Temp.label, formals: bool list} -> level
	val formals : level -> access list
	val allocLocal : level -> bool -> access
	val procEntryExit : {level : level, body : exp} -> unit
	val getResult : unit -> Frame.frag list
	
	val seq : T.stm list -> T.stm
	
	val unEx : exp -> Tree.exp
	val unNx : exp -> Tree.stm
	val unCx : exp -> (Temp.label * Temp.label -> Tree.stm)
end
structure Translate : TRANSLATE =
struct
	structure F = Frame
	structure T = Tree
	structure Te = Temp
	structure A = Absyn
	
	type access = level * F.access
	
	datatype exp = Ex of T.exp
					| Nx of T.stm
					| Cx of T.label * T.label -> T.stm
					
	(* Functions *)
	fun unEx (Ex e) = e
		| unEx (Cx genstm) =
			let
				val r = Te.newtemp()
				val t = Te.newlabel()
				val f = Te.newlabel()
			in
				T.ESEQ(seq[T.MOVE(T.Temp r, T.CONST 1),
							genstm(t,f),
							T.LABEL f,
							T.MOVE(T.TEMP r, T.CONST 0),
							T.LABEL t],
						T.TEMP r)
			end
		| unEx (Nx s) = t.ESEQ(s, T.CONST 0)
		
	(* TODO
	fun unCx
	*)
	
	(* TODO
	fun unNx
	*)
end
