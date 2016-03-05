signature ENV =
sig
	type access
	type ty
	datatype enventry = 
		VarEntry of Types.ty
		| FunEntry of {formals: Types.ty list, result: Types.ty}
	val base_tenv : ty Symbol.table		(* predefined types *)
	val base_venv : enventry Symbol.table (* predefined functions *)
end
structure Env :> ENV =
struct
(* This isn't VETTED *)
	structure T = Types
	structure S = Symbol

	type access = unit 			(* TODO *)
	type ty = T.ty
	datatype enventry = VarEntry of T.ty
	                |	FunEntry of {formals: T.ty list, result: T.ty}

    (* Mapping int -> Ty.INT and string -> Ty.STRING *)
    val preDefTypes = [("int", T.INT), ("string", T.STRING)]
    fun mapType((name, ty), table) = 
		Symbol.enter(table, Symbol.symbol name, ty)
    val base_tenv = foldr mapType S.empty preDefTypes

    (* Mapping variable/ function to type/ parameters and return value *)
    val preDefVar = [("print", FunEntry {formals=[T.STRING], result=T.UNIT}), 
			 		("flush", FunEntry {formals=[], result=T.UNIT}), 
			 		("getchar", FunEntry {formals=[], result=T.STRING}), 
			 		("ord", FunEntry {formals=[T.STRING], result=T.INT}), 
			 		("chr", FunEntry {formals=[T.INT], result=T.STRING}), 
			 		("size", FunEntry {formals=[T.STRING], result=T.INT}), 
			 		("substring", FunEntry {formals=[T.STRING, T.INT, T.INT], result=T.STRING}), 
			 		("concat", FunEntry {formals=[T.STRING, T.STRING], result=T.STRING}), 
			 		("not", FunEntry {formals=[T.INT], result=T.INT}), 
			 		("exit", FunEntry {formals=[T.INT], result=T.UNIT})]
	fun mapVar((name, enventry), table) = 
		Symbol.enter(table, S.symbol name, enventry)
	val base_venv = foldr mapVar S.empty preDefVar
(* End of NON-VETTED stuff *)
end
