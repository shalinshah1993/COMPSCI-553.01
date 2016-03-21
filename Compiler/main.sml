signature MAIN =
sig
	val runFile: string -> unit
end

structure Main :> MAIN=
struct
	structure P = Parse
	structure Sem = Semant
	fun runFile filename = 
		let
			val ast = P.parse filename
			val outfile = TextIO.openOut ("printedAST.out")
		in
			PrintAbsyn.print(outfile, ast);
			Sem.transProg ast
		end
end
