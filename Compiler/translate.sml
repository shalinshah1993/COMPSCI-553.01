signature TRANSLATE =
sig
	type level
	type access (*not the same as Frame.access*)
	type exp
	
	(*structure MIPSFrame : FRAME*)
	
	(* Functions Described in the book *)
	val fraglist : MIPSFrame.frag list ref
	val outermost : level
	val newLevel : {parent: level, name: Temp.label, formals: bool list} -> level
	val formals : level -> access list
	val allocLocal : level -> bool -> access
	val procEntryExit : {level : level, body : exp} -> unit
	val getResult : unit -> MIPSFrame.frag list
	
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
	val whileExp : (exp * exp) -> exp
	val forExp : (exp * Tree.label * exp * exp * exp) -> exp
	val arrayExp : (int * exp) -> exp
	val recordExp : {length : int, fields : exp list} -> exp
	val callExp : (level * Tree.label * exp list) -> exp
	(*
		StringComparison Exp
	*)
	
	val simpleVar : (access * level) -> exp
	val indexedVar : (exp * exp) -> exp
	
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
	structure Er = ErrorMsg
	
	val fraglist = ref [] : F.frag list ref
	
	datatype exp = Ex of T.exp
					| Nx of T.stm
					| Cx of T.label * T.label -> T.stm
					
	datatype level = Base
				| Level of {frame: F.frame, parent: level} * unit ref
				
	type access = level * F.access
	
	val outermost = Base
	
	fun newLevel({parent=parent, name=name, formals=formals}) = Level({frame=F.newFrame{name=name, formals=formals}, parent=parent}, ref ())
	
	fun formals inputLevel =
		case inputLevel of
			Base => []
			| Level ({frame=frame, parent=parent}, unique) =>
				let
					fun handleAccess(a::l) = (Level({frame=frame, parent=parent}, unique), a)::handleAccess(l)
					| handleAccess(nil) = []
				in
					handleAccess(tl(F.formals(frame)))
				end
				
	fun allocLocal(level) escapeBool = 
		case level of
			Level({frame=frame, parent=parent}, unique) => (level, F.allocLocal(frame) escapeBool)
					
	fun seq([]) = T.EXP(T.CONST 0)
		| seq([stm]) = stm
		| seq(stm::stmlist) = T.SEQ(stm, seq(stmlist))
					
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
		| unCx (Ex (T.CONST 0)) = (fn (t,f) => T.JUMP(T.NAME(f), [f])) (* 0 would be binary false, so just jump to the false destination *)
		| unCx (Ex (T.CONST 1)) = (fn (t,f) => T.JUMP(T.NAME(t), [t])) (* 1 would be binary true, so just jump to the true destination*)
		| unCx (Ex e) = (fn(t,f) => T.CJUMP(T.EQ, e, T.CONST 1, t, f)) (*Evaluate if equality true or false, then jump to t/f destination *)
		| unCx (Nx stm) = (fn(t, f) => stm)								(* This is just a HACK Nx can never occur as per Appel *)

	(* Nx stands for "no result", represented as a Tree statement*)
	fun unNx (Nx s) = s
		| unNx (Ex e) = T.EXP(e)
		| unNx (Cx genstm) = T.EXP(unEx(Cx genstm)) (*Need to return EXP, UnEx from book already takes Cx and returns a statement*)
	
	fun stringExp(lit) =
		let
			val label = Te.newlabel()
		in
			(fraglist := F.STRING(label, lit)::(!fraglist);
			Ex (T.NAME label))
		end
	
	fun intExp(n) = Ex(T.CONST n)
	
	fun nilExp () = Ex (T.CONST 0)
	
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
		
	fun seqExp [] = Ex (T.CONST 0)
		| seqExp [e] = e
		| seqExp (e::es) =
			Ex (T.ESEQ(unNx e, unEx(seqExp es)))
			
	fun letExp ([], body) = body
		| letExp (decs, body) = Ex (T.ESEQ( seq(map unNx decs), unEx body))
	
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
						seq[(e1Exp) (thenLabel, doneLabel),
								T.LABEL thenLabel,
								(unCx e2) (t,f),
								T.LABEL doneLabel])
				| (Nx s) =>
					Nx (seq[(e1Exp) (thenLabel,doneLabel),
								T.LABEL thenLabel,
								unNx e2,
								T.LABEL doneLabel])
				| (Ex e) =>
					Ex (T.ESEQ(seq[(e1Exp) (thenLabel,doneLabel),
									T.LABEL thenLabel,
									T.MOVE(T.TEMP rTemp, unEx e2),
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
			(* Remember, both e2 and e3 are of same types -> Will throw warnings, but how to print errors without pos? *)
			case (e2, e3) of 
				(Cx e2C, Cx e3C) =>
					Cx (fn (t,f) =>
						seq[(e1Exp) (thenLabel, elseLabel),
								T.LABEL thenLabel,
								(unCx e2) (t, f),
								T.LABEL elseLabel,
								(unCx e3) (t,f)])
				| (Nx e2N, Nx e3N) =>
					Nx (seq[(e1Exp) (thenLabel, elseLabel),
								T.LABEL thenLabel,
								unNx e2,
								T.JUMP (T.NAME doneLabel, [doneLabel]),
								T.LABEL elseLabel,
								unNx e3,
								T.LABEL doneLabel])
				| (Ex e2E, Ex e3E) =>
					Ex (T.ESEQ(seq[(e1Exp) (thenLabel, elseLabel),
								T.LABEL thenLabel,
								T.MOVE (T.TEMP rTemp, unEx e2),
								T.JUMP (T.NAME doneLabel, [doneLabel]),
								T.LABEL elseLabel,
								T.MOVE (T.TEMP rTemp, unEx e3),
								T.LABEL doneLabel],
						T.TEMP rTemp))
				| _ => (Er.error 0 "Both the expressions are not of the same type. Compiler Error!"; nilExp())
		end
		
	fun forExp (var, escape, lo, hi, body) =
		let
			val varExp = unEx var
			val loExp = unEx lo
			val hiExp = unEx hi
			val bodyExp = unNx body
			val bodyLabel = Te.newlabel()
			val forLabel = Te.newlabel()
		in
			Nx(seq[T.MOVE(varExp, loExp),
					T.CJUMP(T.LE, varExp, hiExp, bodyLabel, escape),
					T.LABEL bodyLabel,
					bodyExp,
					T.CJUMP(T.LT, varExp, hiExp, forLabel, escape),
					T.LABEL forLabel,
					T.MOVE(varExp, T.BINOP(T.PLUS, varExp, T.CONST 1)),
					T.JUMP(T.NAME forLabel, [forLabel]),
					T.LABEL escape])
		end
	
	fun whileExp (test, body) =
		let
			val testExp = unCx test
			val bodyExp = unNx body
			val testLabel = Te.newlabel()
			val bodyLabel = Te.newlabel()
			val doneLabel = Te.newlabel()
		in
			Nx (seq[T.LABEL testLabel,
				testExp (bodyLabel, doneLabel),
				T.LABEL bodyLabel,
				bodyExp,
				T.JUMP (T.NAME testLabel, [testLabel]),
				T.LABEL doneLabel])
		end
	
	fun arrayExp(length, initVal) = 
		let
			 val startAdd = T.TEMP(Te.newtemp())
		in
			Ex (T.ESEQ(seq 
					[T.MOVE(startAdd, F.externalCall("malloc", [T.BINOP(T.MUL, T.CONST(length), T.CONST(F.wordSize))])), 
					T.EXP (F.externalCall("initArray", [T.CONST(length), unEx(initVal)]))], 
					startAdd))
		end

	(* Instead of start address, return TEMP(r) as per appel *)
	fun recordExp({length = length, fields = fields}) =
		let
			val r = T.TEMP(Te.newtemp())

			fun initFields([], result, curOffset, labelR) = result
			| initFields(first::rest, result, curOffset, labelR):T.stm list = 
				initFields(rest, [(T.MOVE(T.MEM(T.BINOP(T.PLUS, (labelR), T.BINOP(T.MUL, T.CONST(curOffset), T.CONST(F.wordSize)))), unEx(first)))] @ result, curOffset + 1, labelR)
		in
			Ex (T.ESEQ(seq 
					[T.MOVE(r, F.externalCall("malloc", [T.BINOP(T.MUL, T.CONST(length), T.CONST(F.wordSize))])), 
					seq(initFields(fields, [], 0, r))], 
					r))
		end

	fun callExp(level, label, formals) = Ex(T.CALL(T.NAME(label), map unEx formals))
		
	fun simpleVar ((defaultLevel, defaultAccess):access, level:level) =
		let
			val (Level(frameRec, defaultRef)) = defaultLevel
			fun followStaticLinks(Level({parent, frame}, currentRef): level, currentAccess : T.exp) =
				if (defaultRef = currentRef) then
					F.exp(defaultAccess) (currentAccess)
				else
					followStaticLinks(parent, F.exp(hd(F.formals frame)) (currentAccess))					
		in
			Ex(followStaticLinks(level, T.TEMP(F.FP)))
		end
		
	fun indexedVar (var, index) =
		let
			val varExp = unEx var
			val indexExp = unEx index
			val offsetExp = T.BINOP(T.MUL, indexExp, T.CONST(F.wordSize))
		in
			Ex (T.MEM(T.BINOP(T.PLUS, varExp, offsetExp)))
		end
		
	fun procEntryExit({level=level, body=body}) =
		() (* TODO *)
	
	fun getResult () = !fraglist
end
