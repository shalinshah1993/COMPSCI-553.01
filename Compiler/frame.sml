signature FRAME 
=
sig 
	type frame
	type access
	val newFrame : {name:Temp.lable, formals:bool list} -> frame
	val name : frame -> Temp.label
	val formals : frame -> access list
	val allocLocal : frame -> bool -> access
	
	val FP : Temp.temp
	val wordSize : int
	val exp : access -> Tree.exp -> Tree.exp
	
	val externalCall : string * Tree.exp list -> Tree.exp
	
	val RV : Temp.temp (*as seen by callee*)
	
	val procEntryExit1 : frame * Tree.stm -> Tree.stm
	
	datatype frag
end

structure MIPSFrame :> FRAME 
= 
struct
	structure Tr = Tree
	structure S = Symbol
	structure Tp = Temp

	wordSize = 4

	val ZO = Temp.newtemp()   (* r0, zero *)
	val FP = Temp.newtemp()   (* Frame-pointer *)
	val SP = Temp.newtemp()   (* Stack-pointer *)
	val RA = Temp.newtemp()   (* Return address *)
	val RV = Temp.newtemp()   (* Return value *)

	(* can store on register or in frame on memory *)
	datatype access = InFrame of int 
					| InReg of Tp.temp

	datatype frag = PROC of {body: Tr.stm, frame: frame}
					| STRING of Tp.label * string
	
	type frame = {name: Tp.label, formals: access list, offset: int ref}
	
 	fun newFrame({name = name, formals = formals}) = 
 		let
 			val currOffset = ref 0

 			fun alllocFormals([]) = []
 			| allocLocal(hasEscaped::others) = 
 				(
 					if hasEscaped then
 						(currOffset := !currOffset - wordSize; InFrame(!currOffset)::allocFormals(rest))
 					else
 						InReg(Tp.newtemp())::allocFormals(rest)
 					end
 				)
 		in
 			{name = name, formals = allocFormals(formals), offset = currOffset}
 		end

 	fun name({name = name, formals = formals, offset = offset}) = name
 	
 	fun formals({name = name, formals = formals, offset = offset}) = formals	

 	fun allocLocal ({name = name, formals = formals, offset = currOffset}) hasEscaped = 
 		(
 			if hasEscaped then
 				(currOffset := !currOffset - wordSize; InFrame(!currOffset))
 			else
 				 InReg(Tp.newtemp())
 			end
 		)
end