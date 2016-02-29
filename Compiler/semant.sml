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

	
	

	fun transProg x = (); (* TODO *)

end
