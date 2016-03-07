signature SEMANT = 
sig
	type expty
	type venv
	type tenv
	type ty
	
	val transVar: venv * tenv * Absyn.var -> expty 
	val	transExp: venv * tenv * Absyn.exp -> expty 
	val	transDec: venv * tenv * Absyn.dec -> {venv: venv, tenv: tenv} 
	val	transTy: tenv * Absyn.ty -> Types.ty 
		
	val	transProg: Absyn.exp -> unit
end

structure Semant :> SEMANT =
struct
	structure A = Absyn
	structure E = Env
	structure Er = ErrorMsg
	structure S = Symbol
	structure T = Types
	structure Tr = Translate
	
	type expty = {exp: Tr.exp, ty: T.ty}
	type venv = E.enventry S.table
	type tenv = T.ty S.table
	type ty = T.ty

	val loopDepth = ref 0
	val breakCount = ref 0

	(* Helper Functions *)
	fun actual_ty (ty: T.ty, pos: A.pos) =
		case ty of
			T.NAME(sym, tyOpt) => 
				(case !tyOpt of
					SOME(t) => (actual_ty (t, pos))
					| NONE => (Er.error pos ("Cannot evaluate the type: "^(S.name sym)); T.ERROR))
			| _ => ty
			
	fun assertEqualTypes (typeA: T.ty, typeB: T.ty, posA: A.pos, posB: A.pos) =
		if actual_ty (typeA, posA) = actual_ty (typeB, posB) then
			true
		else
			false
			
	fun assertSubTypes (typeA: T.ty, typeB: T.ty, posA: A.pos, posB: A.pos) =
		let 
			val actTypeA = actual_ty (typeA, posA)
			val actTypeB = actual_ty (typeB, posB)
		in
			if assertEqualTypes (typeA, typeB, posA, posB) then
				true
			else if (actTypeA = T.UNIT orelse actTypeB = T.UNIT) then
				true
			else if (actTypeA = T.NIL orelse actTypeB = T.NIL) then
				(case (actTypeA, actTypeB) of
					(T.NIL, T.RECORD _) => true
					| (T.RECORD _, T.NIL) => true
					| (_,_) => false)
			else
				false
		end
			
	fun checkType({exp,ty},expectedType,pos) =
		if ty=expectedType then
			()
		else
			(case expectedType of
				T.INT => Er.error pos ("Expected expression of type INT")
				| T.UNIT => Er.error pos ("Expected expression of type UNIT")
				| T.STRING => Er.error pos ("Expected expression of type STRING")
				| _ => Er.error pos ("Expected expression of different type"))

	fun transExp(venv,tenv,exp) = 
		let
			fun subTransExp (A.VarExp var) = transVar(venv,tenv,var)
			| subTransExp (A.NilExp) = {exp=(), ty=T.NIL}
			| subTransExp (A.IntExp i) = {exp=(), ty=T.INT}
			| subTransExp (A.StringExp (str,pos)) = {exp=(), ty=T.STRING}
			| subTransExp (A.CallExp {func=func, args=args, pos=pos}) = 
				(
				case S.look(venv, func) of 
					SOME (E.FunEntry {formals=formals, result=result}) => 
						let
							val transArgs = map subTransExp args
							fun checkArgsType ([], [], pos) = true
			  				| checkArgsType (_, [], pos) = false
			  				| checkArgsType ([], _, pos) = false
			  				| checkArgsType (arg1ty::arglst1, arg2ty::arglst2, pos) =
								if assertSubTypes(arg1ty,arg2ty, pos, pos) then
									checkArgsType(arglst1,arglst2, pos)
								else 
									false
						in
							if length(transArgs) <> length(formals) then
		  						(Er.error pos "Incorrect number of arguments in fuction "; {exp=(),ty=actual_ty(result, pos)})
		  					else if checkArgsType (formals, map (#ty) transArgs, pos)  then 
		  						{exp=(),ty=T.UNIT}
		  					else 
		  						(Er.error pos "Function has incorrect parameters"; {exp=(),ty=actual_ty(result, pos)})
						end
					|  _ => (Er.error pos "No such function exists"; {exp=(),ty=T.ERROR})
				)
			| subTransExp (A.OpExp {left=left, oper=oper, right=right, pos=pos}) = 
				if (oper=A.PlusOp orelse oper=A.MinusOp orelse oper=A.TimesOp orelse oper=A.DivideOp orelse oper=A.LtOp orelse oper=A.LeOp orelse oper=A.GtOp orelse oper=A.GeOp) then
					(checkType(transExp(venv,tenv,left),T.UNIT,pos);
					checkType(transExp(venv,tenv,right),T.UNIT,pos);
					{exp=(), ty=T.INT})
				else if (oper=A.EqOp orelse oper=A.NeqOp) then
					let
						val {exp=exp, ty=leftType} = transExp(venv,tenv,left)
						val {exp=exp, ty=rightType} = transExp(venv,tenv,right)
					in
						if assertSubTypes(leftType,rightType,pos,pos) then
							{exp=(), ty=actual_ty (leftType,pos)}
						else
							(Er.error pos "Type mismatch between left and right expressions of operand"; {exp=(),ty=T.ERROR})
					end
					
				else
					(Er.error pos "Could not discern the operator type"; {exp=(), ty=T.ERROR})
			| subTransExp (A.RecordExp {fields=fields, typ=typ, pos=pos}) = 
				let 
					val T.RECORD(fieldTypes, unique) = 
						(case S.look(tenv,typ) of
							SOME(t) => actual_ty (t,pos)
							| NONE => (Er.error pos ("Undefined field type"); T.RECORD([], ref())))
					fun resolveFieldLists((symbol, exp, pos)::fieldList, (tySymbol,ty)::fieldTypeList) =
						if(S.name symbol = S.name tySymbol) then
							if (assertSubTypes(#ty (transExp(venv,tenv,exp)), actual_ty(ty,pos), pos, pos) = true) then
								resolveFieldLists(fieldList,fieldTypeList)
							else
								(Er.error pos ("Field and type are not able to resolve to the same subtypes");false)
						else
							(Er.error pos ("Field and type cannot be resolved to same symbol");false)
					| resolveFieldLists([],[]) = true (*Everything has been resolved from the previous lists*)
					| resolveFieldLists(_,_) = false (*Makes the list of matches exhaustive, hides compiler error*)
				in
					if (resolveFieldLists(fields, fieldTypes)) then
						{exp=(), ty=T.RECORD(fieldTypes, ref())}
					else
						{exp=(), ty=T.ERROR}
				end
			| subTransExp (A.SeqExp exps) = 
				let
					fun subTransExps ([]) = {exp=(), ty=T.UNIT}
					| subTransExps ((exp, pos)::[]) = transExp(venv, tenv, exp)
					| subTransExps((exp, pos)::l) = (transExp(venv,tenv,exp);subTransExps l);
				in
					subTransExps exps
				end
			| subTransExp (A.AssignExp {var=var, exp=exp, pos=pos}) = 
				let
					val {exp=varExp, ty=varType} = transVar(venv,tenv,var)
					val {exp=expExp, ty=expType} = transExp(venv,tenv,exp)
				in
					if (assertEqualTypes(varType,expType,pos,pos)) then
						{exp=(), ty=T.UNIT}
					else
						(Er.error pos "Type mismatch in assigment expression; types cannot be compared";{exp=(),ty=T.ERROR})
				end
			| subTransExp (A.IfExp {test=test, then'=thenexp, else'=elsexp, pos=pos}) = 
				(case elsexp of
					NONE => 
						(let
							val realThenExp = transExp(venv,tenv,thenexp)
							val testExp = transExp(venv,tenv,test)
						in
							checkType(testExp, T.INT, pos);
							checkType(realThenExp, T.UNIT, pos);
							{exp=(), ty=T.UNIT}
						end)
					| SOME e => 
						(let
							val realThenExp = transExp(venv,tenv,thenexp)
							val realElseExp = transExp(venv,tenv,e)
							val testExp = transExp(venv,tenv,test)
						in
							checkType(testExp, T.INT, pos);
							checkType(realThenExp, T.UNIT, pos);
							checkType(realElseExp, T.UNIT, pos);
							{exp=(), ty=T.UNIT}
						end))
			| subTransExp (A.WhileExp {test=test, body=body, pos=pos}) = 
				let
					val _ = loopDepth := !loopDepth + 1
					val testExpTy = transExp(venv,tenv,test)
					val bodyExpTy = transExp(venv,tenv,body)
					val _ = loopDepth := !loopDepth - 1
					val _ = breakCount := 0
				in
					(checkType(testExpTy, T.INT, pos);
					checkType(bodyExpTy, T.UNIT, pos);
					{exp=(), ty=T.UNIT})
				end
			| subTransExp (A.ForExp {var=var, escape=escape, lo=lo, hi=hi, body=body, pos=pos}) = 
				let
					val _ = loopDepth := !loopDepth + 1
					val venv' = S.enter(venv, var, (E.VarEntry (T.INT)))
					val bodyExpTy = transExp(venv', tenv, body)
					val loExpTy = transExp(venv', tenv, lo)
					val hiExpTy = transExp(venv', tenv, hi)
					val _ = loopDepth := !loopDepth - 1
					val _ = breakCount := 0
				in
					(checkType(loExpTy, T.INT, pos);
					checkType(hiExpTy, T.INT, pos);
					checkType(bodyExpTy, T.UNIT, pos);
					{exp=(), ty=T.UNIT})
				end
			| subTransExp (A.BreakExp pos) = 
				let
					val _ = breakCount := !breakCount + 1
				in
					if !loopDepth = 0 then
						(Er.error pos "BREAK can occur only inside a loop"; { exp=(), ty=T.ERROR })
					else if !breakCount > 1 then
						(Er.error pos "No more loops to BREAK!"; { exp=(), ty=T.ERROR})
					else
						{ exp=(), ty=T.UNIT }
				end
			| subTransExp (A.LetExp {decs=decs, body=body, pos=pos}) =
				let
					fun extractDec (venv,tenv,decs) = 
						(case decs of
							[] => {venv=venv, tenv=tenv}
							| (dec::l) =>
								let
									val {venv=newVenv, tenv=newTenv} = transDec(venv,tenv,dec)
								in
									extractDec(newVenv, newTenv, l)
								end)
					val {venv=finalVenv, tenv=finalTenv} = extractDec(venv,tenv,decs)
				in
					transExp(finalVenv, finalTenv, body)
				end
			| subTransExp (A.ArrayExp {typ=typ, size=size, init=init, pos=pos}) = 
				(* Size must be int, init must be same type as basetype of array, and typ itself must be an array *)
				let
					val sizeExpTy = transExp(venv,tenv,size);
					val initExpTy = transExp(venv,tenv,init);
					val baseType =
						(case S.look(tenv,typ) of
							SOME (ty) => 
								(case (actual_ty(ty,pos)) of
									T.ARRAY(baseType, unique) => T.INT
									| _ => (Er.error pos ("Cannot define an array as anything other than as an array"); T.ERROR))
							| NONE => (Er.error pos ("Could not define base type of array"); T.ERROR));
				in
					checkType(sizeExpTy, T.INT, pos);
					assertEqualTypes(#ty initExpTy, baseType, pos,pos);
					{exp=(), ty=baseType}
				end
		in
			subTransExp exp
		end

	and transVar(venv,tenv,var) = 
		let
			fun subTransVar (A.SimpleVar(simVar,pos)) =
				(case S.look(venv, simVar) of
					SOME (E.VarEntry(t)) => {exp=(), ty=actual_ty(t,pos)}
					| _ => (Er.error pos ("Undefined variable " ^ S.name(simVar)); {exp=(), ty=T.ERROR}))
			| subTransVar (A.FieldVar (var, symbol, pos)) = 
				let
					val {exp=varExp, ty=varType} = transVar(venv, tenv, var);
				in
					(case varType of
						T.RECORD(fields, unique) => {exp=(), ty=(actual_ty (varType,pos))} 
						| _ => (Er.error pos ("Field variable must be of type T.RECORD"); {exp=(), ty=T.ERROR}))
				end
			| subTransVar (A.SubscriptVar (var, exp, pos)) = 
				(let
					val {exp=varExp, ty=varType} = transVar(venv,tenv,var);
					val expExpTy = transExp(venv,tenv,exp)
				in
					checkType(expExpTy, T.INT, pos);
					(case varType of
						T.ARRAY (baseType, unique) => {exp=(), ty = (actual_ty (baseType, pos))}
						| _ => (Er.error pos ("Variable must be of type T.ARRAY"); {exp=(), ty=T.ERROR}))
				end)
		in
			subTransVar var
		end

	and transDec(venv,tenv,dec) = 
		let 
			fun subTransDec (A.FunctionDec funcs) = 
				{venv=venv, tenv=tenv}
				
			| subTransDec (A.VarDec {name=name, escape=escape, typ=typ, init=init, pos=pos}) = 
				let 
					val {exp=varExp, ty=varTy} = transExp(venv,tenv,init)
				in
					{venv=S.enter(venv,name,E.VarEntry(varTy)),tenv=tenv}
				end
			| subTransDec (A.TypeDec [{name=name, ty=ty, pos=pos}]) = {venv=venv,tenv=S.enter(tenv,name,transTy(tenv,ty))}
			| subTransDec (_) = {venv=venv,tenv=tenv}
		in
			subTransDec dec
		end

	and transTy(tenv,ty) = 
		let
			fun subTransTy (A.NameTy (tySym, pos)) = 
				(case S.look(tenv, tySym) of
					SOME (t) => t
					| NONE => (Er.error pos ("Undefined type "^S.name(tySym)); T.ERROR))
			| subTransTy (A.RecordTy field) =
				let 
					val fieldVals =
						let
							fun extractFieldInfo({name, escape, typ, pos}) =
								(case S.look(tenv, typ) of
									SOME (t) => (name, t)
									| NONE => (Er.error pos("Undefined type"^S.name(name)); (name, T.ERROR)))
						in
							map extractFieldInfo field
						end
				in
					T.RECORD(fieldVals, ref())
				end
			| subTransTy (A.ArrayTy (sym,pos)) =
				(case S.look(tenv,sym) of
					SOME (t) => T.ARRAY(t, ref())
					| NONE => (Er.error pos("Undefined type "^S.name(sym)); T.ERROR))
		in
			subTransTy ty
		end
	
	(* Main function which traverses the AST *)
	fun transProg (expr:A.exp) = 
		let
			val venv = Env.base_venv
			val tenv = Env.base_tenv
			val tree = transExp(venv, tenv, expr)
		in
			()
	end
end
