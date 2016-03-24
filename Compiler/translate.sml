signature TRANSLATE =
sig
	type level
	type access (*not the same as Frame.access*)
	type exp
	
	structure Frame : FRAME
	
	(* Functions Described in the book *)
	val fraglist : Frame.frag list ref
	val outermost : level
	val newLevel : {parent: level, name: Temp.label, formals: bool list} -> level
	val formals : level -> access list
	val allocLocal : level -> bool -> access
	val procEntryExit : {level : level, body : exp} -> unit
	val getResult : unit -> Frame.frag list
	
	val seq : Tree.stm list -> Tree.stm
	
	(* Expression functions that do the meat of translation *)
	val intExp : int -> exp
	val stringExp : string -> exp
	val nilExp : unit -> exp
	val intArithExp : (Absyn.oper * exp * exp) -> exp
	val assignExp : (exp * exp) -> exp
	val seqExp : (exp list) -> exp
	val letExp : (exp list * exp) -> exp
	val ifExp : (exp * exp) -> exp
	val ifElseExp : (exp * exp * exp) -> exp
	(*
		For exp
		While Exp
		StringComparison Exp
		
		Call Exp
		RecordExp
		Array Exp
	*)
	
	(* Var Expressions *)
	(*
		SimpleVar
		FieldVar
		SubscriptVar
	*)
	
	val unEx : exp -> Tree.exp
	val unNx : exp -> Tree.stm
	val unCx : exp -> (Temp.label * Temp.label -> Tree.stm)
end
structure Translate : TRANSLATE =
struct
	structure F = MIPSFrame
	structure T = Tree
	structure Te = Temp
	structure A = Absyn
	
	type access = level * F.access
	
	val fraglist = ref [] : F.frag list ref
	
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
				T.ESEQ(seq[T.MOVE(T.TEMP r, T.CONST 1),
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
	
	fun stringExp(lit) =
		let
			val label = Te.newlabel()
		in
			fraglist := F.STRING(label, lit)::!fraglist;
			Ex (T.NAME label)
		end
	
	fun intExp(n) = Ex(T.CONST n)
	
	fun nilExp = Ex (T.CONST 0)
	
	fun intArithExp (A.PlusOp, left, right) = Ex(T.BINOP(T.PLUS, unEx(left), unEx(right)))
		| intArithExp (A.MinusOp, left, right) = Ex(T.BINOP(T.MINUS, unEx(left), unEx(right)))
		| intArithExp (A.TimesOp, left, right) = Ex(T.BINOP(T.MUL, unEx(left), unEx(right)))
		| intArithExp (A.DivideOp, left, right) = Ex(T.BINOP(T.DIV, unEx(left), unEx(right)))
		| intArithExp (A.LtOp, left, right) = Cx(fn(t,f) => T.CJUMP(T.LT, unEx(left), unEx(right), t, f))
		| intArithExp (A.LeOp, left, right) = Cx(fn(t,f) => T.CJUMP(T.LE, unEx(left), unEx(right), t, f))
		| intArithExp (A.GtOp, left, right) = Cx(fn(t,f) => T.CJUMP(T.GT, unEx(left), unEx(right), t, f))
		| intArithExp (A.GeOp, left, right) = Cx(fn(t,f) => T.CJUMP(T.GE, unEx(left), unEx(right), t, f))
		| intArithExp (A.EqOp, left, right) = Cx(fn(t,f) => T.CJUMP(T.EQ, unEx(left), unEx(right), t, f))
		| intArithExp (A.NeqOp, left, right) = Cx(fn(t,f) => T.CJUMP(T.NE, unEx(left), unEx(right), t, f))
		
	fun assignExp (v, e) =
		let
			val vEx = unEx v
			val eEx = unEx e
		in
			Nx(T.MOVE(vEx, eEx)) (*MOVE stores right in left, don't want result*)
		end
		
	fun seqExp [] = nilExp
		| seqExp [e] = Ex (e)
		| seqExp (e::es) =
			Ex (T.ESEQ(unNx e, unEx(seqExp es)))
			
	fun letExp ([], body) = Ex (body)
		| letExp (decs, body) = Ex (T.ESEQ( T.SEQ(map unNx decs), unEx body))
	
	fun breakExp b = Nx (T.JUMP(T.NAME(b), [b]))
	
	fun ifExp (e1, e2) =
		let
			val e1Exp = unCx(e1)
			val thenLabel = Te.newlabel()
			val doneLabel = Te.newlabel()
			val rTemp = Te.newtemp()

		in
			case (e2) of
				(Cx genstm) =>
					Cx (fn (t,f) =>
						T.SEQ[(e1Exp) (thenLabel, doneLabel),
								T.LABEL thenLabel,
								(unCx genstm) (t,f),
								T.LABEL doneLabel])
				| (Nx s) =>
					Nx (T.SEQ[(e1Exp) (thenLabel,doneLabel),
								T.LABEL thenLabel,
								UnNx s,
								T.LABEL doneLabel])
				| (Ex e) =>
					Ex (T.ESEQ(T.SEQ[(e1Exp) (thenLabel,doneLabel),
									T.LABEL thenLabel,
									T.MOVE(T.TEMP rTemp, e),
									T.LABEL doneLabel],
								T.TEMP rTemp))
		end
		
	fun ifElseExp (e1, e2, e3) =
		let
			val e1Exp = unCx(e1)
			val thenLabel = Te.newlabel()
			val elseLabel = Te.newlabel()
			val doneLabel = Te.newlabel()
			val rTemp = Te.newtemp()
		in
			case (e2, e3) of (* Remember, both e2 and e3 are of same types -> Will throw warnings, but how to print errors without pos?*)
				(Cx e2C, Cs e3C) =>
					Cx (fn (t,f) =>
						T.SEQ[(e1Exp), (thenLabel, elseLabel),
								T.LABEL thenLabel,
								(unCx e2C) (t, f),
								T.LABEL elseLabel,
								(unCx e3C) (t,f)])
				| (Nx e2N, Nx e3N) =>
					Nx (T.SEQ[(e1Exp) (thenLabel, elseLabel),
								T.LABEL thenLabel,
								unNx e2N,
								T.JUMP (T.NAME doneLabel, [doneLabel]),
								T.LABEL elseLabel,
								unNx e3N,
								T.LABEL doneLabel])
				| (Ex e2E, Ex e3E) =>
					Ex (T.ESEQ(T.SEQ[(e1Exp) (thenLabel, elseLabel),
								T.LABEL thenLabel,
								T.MOVE (T.TEMP rTemp, e2E),
								T.JUMP (T.NAME doneLabel, [doneLabel]),
								T.LABEL elseLabel,
								T.MOVE (T.TEMP rTemp, e3E),
								T.LABEL doneLabel],
						T.TEMP rTemp))
								
		end
	
	fun getResult = !fraglist
end
