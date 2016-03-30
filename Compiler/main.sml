signature MAIN =
sig
	val runFile: string -> unit
end

structure Main :> MAIN=
struct
	structure P = Parse
	structure Sem = Semant
	structure F = MIPSFrame
	structure S = Symbol
	
	fun printFrag (frag: F.frag) =
		case frag
		  of F.PROC {body=body, frame=frame} =>
			   (print("  body:\n");
			   Printtree.printtree (TextIO.stdOut, body))
		   | F.STRING (label, name) =>
			   (print("  label "^(S.name(label))^": "^name^"\n"));
			 

	  fun printFrags (fragments: F.frag list) =
		(print("frags:\n");
		app printFrag fragments)
	
	
	fun runFile filename = 
		let
			val ast = P.parse filename
			val outfile = TextIO.openOut ("printedAST.out")
		in
			let
				val {frags:MIPSFrame.frag list, ty:Types.ty} = Sem.transProg ast
			in
				(PrintAbsyn.print(outfile, ast);
				printFrags(frags))
			end
		end
end
