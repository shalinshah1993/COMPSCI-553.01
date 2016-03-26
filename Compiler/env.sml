signature ENV =
sig
	type access
	type ty
	 datatype enventry = VarEntry of {access: Translate.access, ty: Types.ty}
                    | FunEntry of {level: Translate.level, label: Temp.label, formals: Types.ty list, result: Types.ty}
	val base_tenv : Types.ty Symbol.table		(* predefined types *)
	val base_venv : enventry Symbol.table (* predefined functions *)
end
structure Env :> ENV =
struct
	structure T = Types
	structure S = Symbol
	structure Tr = Translate
	structure Te = Temp

	type access = unit 			(* TODO *)
	type ty = T.ty
	datatype enventry = VarEntry of {access: Translate.access, ty: Types.ty}
	                |	FunEntry of {level: Translate.level, label: Temp.label, formals: Types.ty list, result: Types.ty}

    (* Mapping int -> Ty.INT and string -> Ty.STRING *)
    val preDefTypes = [("int", T.INT), ("string", T.STRING)]
    fun mapType((name, ty), table) = 
		Symbol.enter(table, Symbol.symbol name, ty)
    val base_tenv = foldr mapType S.empty preDefTypes
	
	val base_level = Tr.newLevel{parent=Tr.outermost, name=Te.namedlabel("base"), formals=[]}

    (* Mapping variable/ function to type/ parameters and return value *)
    val preDefVar = [("print", FunEntry {level=base_level, label=Te.namedlabel("print"), formals=[T.STRING], result=T.UNIT}), 
			 		("flush", FunEntry {level=base_level, label=Te.namedlabel("flush"), formals=[], result=T.UNIT}), 
			 		("getchar", FunEntry {level=base_level, label=Te.namedlabel("getchar"), formals=[], result=T.STRING}), 
			 		("ord", FunEntry {level=base_level, label=Te.namedlabel("ord"), formals=[T.STRING], result=T.INT}), 
			 		("chr", FunEntry {level=base_level, label=Te.namedlabel("chr"), formals=[T.INT], result=T.STRING}), 
			 		("size", FunEntry {level=base_level, label=Te.namedlabel("size"), formals=[T.STRING], result=T.INT}), 
			 		("substring", FunEntry {level=base_level, label=Te.namedlabel("substring"), formals=[T.STRING, T.INT, T.INT], result=T.STRING}), 
			 		("concat", FunEntry {level=base_level, label=Te.namedlabel("concat"), formals=[T.STRING, T.STRING], result=T.STRING}), 
			 		("not", FunEntry {level=base_level, label=Te.namedlabel("not"), formals=[T.INT], result=T.INT}), 
			 		("exit", FunEntry {level=base_level, label=Te.namedlabel("exit"), formals=[T.INT], result=T.UNIT})]
	fun mapVar((name, enventry), table) = 
		Symbol.enter(table, S.symbol name, enventry)
	val base_venv = foldr mapVar S.empty preDefVar
(* End of NON-VETTED stuff *)
end
