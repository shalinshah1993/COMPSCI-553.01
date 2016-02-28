structure Semant :> 
sig
	val transProg: Absyn.exp -> unit
end 
=
struct

	structure A = Absyn
	structure P = PrintAbsyn
	structure S = Symbol
	structure E = Env
	structure T = Types

 	type expty = {exp: Translate.exp, ty: T.ty}

	type venv = Env.enventry Symbol.table
	type tenv = ty Symbol.table*)

	fun checkInt({exp,ty}, pos) =
	  case ty of
	      T.INT => ()
	    | _  => error pos "Expected type INT, found type " ^ ty

	fun transVar(venv, tenv, varty) =
	    let fun subTransVar (A.SimpleVar(id, pos)) = 
			(case Symbol.look(venv,id) of
		      SOME(E.VarEntry(ty)) => {exp=(), ty=actual_ty ty}
		                   | NONE  => (error pos ("undefined variable " ^ S.name id);
						       exp(), ty=Types.INT))
			| subTransVar (A.FieldVar(var,sym,pos)) = ()
			| subTransVar (A.SubscriptVar(bar,exp,pos)) = ()  
	    in
			subTransVar varty
	    end

	and transExp(venv, tenv, expty) =
	    let fun subTransExp (A.VarExp exp) = transVar (venv, tenv, exp)
			| subTransExp (A.NilExp exp) = {exp=(), ty=T.NIL}
			| subTransExp (A.IntExp exp) = {exp=(), ty=T.INT}
			| subTransExp (A.StringExp (exp, pos)) = {exp=(), ty=T.STRING}
			| subTransExp (A.CallExp {symbol, exps, pos}) = () (* TODO *)
			| subTransExp (A.OpExp {leftExp, oper, rightExp, pos}) = 
				if (oper=A.PlusOp | oper=A.MinusOp | oper=A.TimesOp | oper=A.DivideOp | oper=A.LtOp | oper=A.LeOp | oper=A.GtOp | oper=A.GeOp)
				then
					checkInt(transExp(venv, tenv, leftExp), pos);
					checkInt(transExp(venv, tenv, righExp), pos);
					{exp=(), ty=T.INT}
				else if (oper=A.EqOp | oper=A.NeqOp)
				then
					if (#ty transExp(venv, tenv, leftExp) = #ty transExp(venv, tenv, rightExp))
					then
						{exp=(), ty= #ty transExp(venv, tenv, leftExp)}
					else
						(error pos "Type mismatch in equality operation"; {exp=(), ty=T.NIL})
				else
					(error pos "Could not discern operator type"; {exp=(), ty=T.NIL})
			| subTransExp (A.RecordExp {fields, typ, pos}) = () (* TODO *)
			| subTransExp (A.SeqExp exps) = 
				let fun breakUpList [] => {exp=(), ty=T.UNIT}
					|	breakUpList (exp, pox)::l => (transExp(venv, tenv, exp); breakUpList(l))
				in
					breakUpList exps
				end
			| subTransExp (A.AssignExp {var, exp, pos}) = 
				if (#ty TransVar(venv, tenv, var) = #ty TransExp(venv,tenv,exp))
				then
					{exp=(), ty=T.UNIT}
				else
					(error pos "Type mismatch between variable and assigned value";
					{exp=(), ty=T.NIL})
			| subTransExp (A.IfExp {test, then', else', pos}) = () (* TODO *)
			| subTransExp (A.WhileExp {test, body, pos}) = () (* TODO *)
			| subTransExp (A.ForExp {var, escape, lo, hi, body, pos}) = () (* TODO *)
			| subTransExp (A.BreakExp pos) = () (* TODO *)
			| subTransExp (A.LetExp {decs, body, pos}) = () (* TODO *)
			| subTransExp (A.ArrayExp {typ, size, init, pos}) = () (* TODO *)
	    in
			subTransExp expty
	    end

	and transDec(venv, tenv, decty) = 
	    let fun subTransDec (A.FunctionDec [{name,params,result=SOME(rt,pos),body,pos}]) = 
			let val SOME(result_ty) = S.look(tenv,rt)
				fun transparam{name,typ,pos} = case S.look(tenv,typ) of
													SOME t => {name,name, ty=ty}
				val params' = map transparam params
				val venv' = S.enter(venv,name,E.FunEntry{formas= map #ty params', result=result_ty})
				fun enterparam ({name,ty},venv) = S.enter(venv,name,E.VarEntr{access=(),ty=ty})
				val venv'' = fold enterparam params' venv'
			in 
				TransExp(venv'', tenv) body; {venv=venv', tenv=tenv}
			end (* Need to figure out where to get proper exp for third arg *)
		  | subTransDec (A.VarDec{name, escape, typ=NONE, init, pos}) = 
				let val {exp,ty} = transExp(venv,tenv,init)
					in {tenv=tenv, venv=S.enter(venv,name,E.VarEntr{ty=ty})}
				end
		  | subTransDec (A.TypeDec[{name, ty, pos}]) = 
				{venv=venv,tenv=S.enter(tenv,name,TransTy(tenv,ty))};
	    in
			subTransDec decty
	    end (* TODO - All of this was from the book, need to confirm this works for recursive decs and that it works with our own semantics *)

	and transTy(tenv, ty) = 
	    let fun subTransTy (A.NameTy (sym, pos)) = (case S.look(tenv, sym) of 
							   NONE => (error pos "Undefined type of " ^ sym; T.NIL)
							| SOME(t)  = t) 
		  | subTransTy (A.RecordTy field) = () (* TODO *)
		  | subTransTy (A.ArrayTy (sym, pos)) = (case S.look(tenv, sym) of
								NONE => (error pos "Undefined array type of " ^ sym; T.NIL)
							|	SOME(t) => T.ARRAY(t, 0) (* TODO - what is 'unique'? *)
	    in 
		subTransTy ty
	    end

	fun transProg x = (); (* TODO *)

end
