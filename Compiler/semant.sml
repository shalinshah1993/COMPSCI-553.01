structure Semant :> 
sig
	type tenv 
	type venv
	type expty
	type ty

	val transVar: venv * tenv * Absyn.var -> expty 
	val transExp: venv * tenv * Absyn.exp -> expty
	val transDec: venv * tenv * Absyn.dec -> {venv: venv, tenv: tenv} 
	val transTy: tenv * Absyn.ty -> ty
	
	val transProg: Absyn.exp -> unit
end 
=
struct

	structure A = Absyn
	structure P = PrintAbsyn
	structure S = Symbol
	structure E = Env
	structure T = Types

	type venv = Env.enventry Symbol.table
	type tenv = T.ty Symbol.table

 	type expty = {exp: Translate.exp, ty: T.ty}
 	type ty = T.ty

 	val error = ErrorMsg.error

 	(* Evaluates all NAME types except in array/ record *)
 	fun actual_ty (ty: T.ty, pos: A.pos) =
		case ty of
			T.NAME(s, tref) => 
				case !tref of
					SOME(t) => actual_ty (t,pos)
				   | NONE => (ErrorMsg.error pos ("Undefined type with name: "^(S.name s)); T.ERROR)
			| _ => ty

	(* Check if type2 is subtype of type1 and is NIL type allowed *)
	fun compareTypes (type1: T.ty, type2: T.ty, pos1: A.pos, pos2: A.pos) = 
		let
			val trueType1 = actual_ty (type1, pos1)
			val trueType2 = actual_ty (type2, pos2)
		in 
			if trueType1=T.ERROR orelse trueType2=T.ERROR then 
				true 
			else if trueType2 = T.UNIT then 
				true
			else if trueType1 = T.NIL then 
				(case trueType2 of
					T.NIL => (error pos1 "Error comparing two nils!"; false)
					| T.RECORD _ => true
					| _ => trueType1=trueType2)
			else if trueType2 = T.NIL then 
				(case trueType1 of
					T.NIL => (error pos2 "Error comparing two nils!"; false)
					| T.RECORD _ => true
					| _ => trueType1=trueType2)
			else 
				trueType1=trueType2
		end

	(* Check type of operand to INT *)
	fun checkInt({exp,ty}, pos) =
		case ty of
			T.INT => ()
			| _  => error pos "type INT required at this position"
	
	(* AST Traverse Function to type-check/ translate *)
	fun transExp (venv, tenv, expr) = 
		let
				fun trExp (A.NilExp) = {exp=(), ty=T.NIL}
					|	trExp (A.VarExp v) = {exp=(), ty=T.NIL}																	(* TODO *)

					| 	trExp (A.SeqExp(exps)) = 
							let
								fun parseExps([]) = {exp = (), ty = T.UNIT}
									|	parseExps((exp, pos)::[]) = transExp(venv, tenv, exp)
									|	parseExps((exp, pos)::l) = (transExp(venv, tenv, exp); parseExps(l))
							in
								parseExps(exps)
							end

					|	trExp (A.IntExp exp) = {exp=(), ty=T.INT}
					|	trExp (A.StringExp (exp, pos)) = {exp=(), ty=T.STRING}

					|	trExp (A.CallExp {func=func, args=args, pos=pos}) = {exp=(), ty=T.NIL} 									(* TODO *)

					|	trExp (A.OpExp{left=leftExp, oper=oper, right=rightExp, pos=pos}) = 
							if (oper=A.PlusOp orelse oper=A.MinusOp orelse oper=A.TimesOp orelse oper=A.DivideOp orelse oper=A.LtOp orelse oper=A.LeOp orelse oper=A.GtOp orelse oper=A.GeOp) then
								(checkInt(transExp(venv, tenv, leftExp), pos); checkInt(transExp(venv, tenv, rightExp), pos); {exp=(), ty=T.INT})
							else if (oper=A.EqOp orelse oper=A.NeqOp) then
								let
									val {exp=exp, ty=leftType} = transExp(venv, tenv, leftExp)
									val {exp=exp, ty=rightType} = transExp(venv, tenv, rightExp)
								in
									if (compareTypes (leftType, rightType, pos, pos) orelse compareTypes (rightType, leftType, pos, pos)) then 
										{exp=(), ty=T.INT}
							  		else 
							  		  	((ErrorMsg.error pos "Comparison two different types. Grrrr!"); {exp=(),ty=T.ERROR})
								end
							else
								(error pos "Could not discern operator type"; {exp=(), ty=T.NIL})

					|	trExp (A.AssignExp{var=var,exp=exp,pos=pos}) = 
							if (#ty (transVar(venv, tenv, var))) = (#ty (transExp(venv, tenv, exp))) then 
								{exp=(),ty=T.UNIT}
						  	else 
						  		(error pos "Types of variable and assigned expression do not match"; {exp=(),ty=T.ERROR})

					|	trExp (A.RecordExp {fields=fields, typ=typ, pos=pos}) = {exp=(), ty=T.NIL}								(* TODO *)
					|	trExp (A.LetExp {decs=decs,body=body,pos=pos}) = {exp=(), ty=T.NIL}										(* TODO *)
					|	trExp (A.IfExp {test=test, then'=thenExp, else'=elseExp, pos=pos}) = {exp=(), ty=T.NIL} 				(* TODO *)
					|	trExp (A.ForExp {var=var, escape=escape, lo=lo, hi=hi, body=body, pos=pos})= {exp=(), ty=T.NIL} 		(* TODO *)
					|	trExp (A.WhileExp {test=test, body=body, pos=pos}) = {exp=(), ty=T.NIL} 								(* TODO *)
					|	trExp (A.BreakExp pos) = {exp=(), ty=T.NIL} 															(* TODO *)
					|	trExp (A.ArrayExp {typ=typ, size=size, init=init, pos=pos}) = {exp=(), ty=T.NIL} 						(* TODO *)

					
		in
			trExp(expr)
		end

	(* Main function which traverses the AST *)
	fun transProg expr = 
		let
			val tenv = E.base_tenv
			val venv = E.base_venv
			val tree = transExp(tenv, venv, expr)
		in
			()
		end
end
