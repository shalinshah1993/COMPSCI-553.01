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
	
	(* Expression functions that do the meat of translation *)
	val intArithExp : (Absyn.oper * exp * exp) -> exp
	
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
	(* Ex stands for an "expression", represented as a Tree.exp *)
	fun unEx (Ex e) = e
		| unEx (Cx genstm) =
			let
				val r = Te.newtemp()
				val t = Te.newlabel() and f = Te.newlabel()
			in
				T.ESEQ(seq[T.MOVE(T.Temp r, T.CONST 1),
							genstm(t,f),
							T.LABEL f,
							T.MOVE(T.TEMP r, T.CONST 0),
							T.LABEL t],
						T.TEMP r)
			end
		| unEx (Nx s) = T.ESEQ(s, T.CONST 0)
		
	(* Cx stands for "conditional", represented as a function from label-pair to statement (give it a true and false destination)*)
	fun unCx (Cx genstm) = genstm
		| unCx (Ex (T.CONST 0)) = (fn (t,f) => T.JUMP(f, [f])) (* 0 would be binary false, so just jump to the false destination *)
		| unCx (Ex (T.CONST 1)) = (fn (t,f) => T.JUMP(t, [t])) (* 1 would be binary true, so just jump to the true destination*)
		| unCx (Ex e) = (fn(t,f) => T.CJUMP(T.EQ, e, T.CONST 1,t, f)) (*Evaluate if equality true or false, then jump to t/f destination *)
		(* Can never hav unCx (Nx, _), per Appel *)

	(* Nx stands for "no result", represented as a Tree statement*)
	fun unNx (Nx s) = s
		| unNx (Ex e) = T.EXP(e)
		| unNx (Cx genstm) = T.EXP(unEx(Cx genstm)) (*Need to return EXP, UnEx from book already takes Cx and returns a statement*)
	
	fun intArithExp (A.PlusOp, left, right) = ()
		| intArithExp (A.MinusOp, left, right) = ()
		| intArithExp (A.TimesOp, left, right) = ()
		| intArithExp (A.DivideOp, left, right) = ()
		| intArithExp (A.LtOp, left, right) = ()
		| intArithExp (A.LeOp, left, right) = ()
		| intArithExp (A.GtOp, left, right) = ()
		| intArithExp (A.GeOp, left, right) = ()
		| intArithExp (A.EqOp, left, right) = ()
		| intArithExp (A.NeqOp, left, right) = ()
	
end
