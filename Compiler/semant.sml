signature Semant =
sig
    val transProg : Abysn.exp -> unit
end
structure Semant :> SEMANT =
struct

structure A = Absyn

fun transVar(venv, tenv) = (* Make this more general for multiple types of Absyn.var *)
    let fun subTransVar (A.SimpleVar(sym, pos)) = ()
	  | subTransVar (A.FieldVar(var,sym,pos)) = ()
	  | subTransVar (A.SubscriptVar(bar,exp,pos)) = ()  

and transExp(venv, tenv) = (* Make this more general for multiple types of Absyn.exp *)
    let fun subTransExp (A.VarExp exp) = ()
	  | subTransExp (A.NilExp exp) = ()
	  | subTransExp (A.IntExp exp) = ()
	  | subTransExp (A.StringExp (exp, pos)) = ()
	  | subTransExp (A.CallExp {symbol, exps, pos}) = () 
	  | subTransExp (A.OpExp {leftExp, oper, rightExp, pos}) = ()
	  | subTransExp (A.RecordExp {fields, typ, pos}) = ()
	  | subTransExp (A.SeqExp exps) = ()
	  | subTransExp (A.AssignExp {var, exp, pos}) = ()
	  | subTransExp (A.IfExp {test, then', else', pos}) = ()
	  | subTransExp (A.WhileExp {test, body, pos}) = ()
	  | subTransExp (A.ForExp {var, escape, lo, hi, body, pos}) = ()
	  | subTransExp (A.BreakExp pos) = ()
	  | subTransExp (A.LetExp {decs, body, pos}) = ()
	  | subTransExp (A.ArrayExp {typ, size, init, pos}) = ()

and transDec(venv, tenv) = (* Make this more general for multiple types of Absyn.dec *)
    let fun subTransDec (A.FunctionDec funcdecl) = ()
	  | subTransDec (A.VarDec{name, escape, typ, init, pos}) = ()
	  | subTransDec (A.TypeDec{name, ty, pos}) = ()  

and transTy(tenv) = (* Make this more general for multiple types of Abysn.ty *)
    let fun subTransTy(A.NameTy (sym, pos)) = ()
	  | subTransTy (A.RecordTy field) = ()
	  | subTransTy (A.ArrayTy (sym, pos)) = () 

fun transProg x = ();

end
