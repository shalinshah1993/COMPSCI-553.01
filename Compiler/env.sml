signature ENV =
sig
	type access
	datatype enventry = VarEntry of {access: Translate.access, ty: Types.ty}
	                | FunEntry of {formals: Types.ty list, result: Types.ty, label: Temp.label, level: Translate.level}
	val base_tenv : Types.ty Symbol.table
	val base_venv : enventry Symbol.table
end