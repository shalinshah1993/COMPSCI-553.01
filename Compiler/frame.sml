structure MIPSFrame :> FRAME 
= 
struct
	structure Tr = Tree
	structure S = Symbol
	structure Tp = Temp

	val wordSize = 4

	val ZO = Temp.newtemp()   (* r0, zero *)
	val FP = Temp.newtemp()   (* Frame-pointer *)
	val SP = Temp.newtemp()   (* Stack-pointer *)
	val RA = Temp.newtemp()   (* Return address *)
	val RV = Temp.newtemp()   (* Return value *)

	(* can store on register or in frame on memory *)
	datatype access = InFrame of int 
					| InReg of Tp.temp

	type frame = {name: Tp.label, formals: access list, offset: int ref}				
	
	datatype frag = PROC of {body: Tr.stm, frame: frame}
					| STRING of Tp.label * string
	

	
 	fun newFrame({name = name, formals = formals}) = 
 		let
 			val currOffset = ref 0

 			fun allocFormals([]) = []
 			| allocFormals(hasEscaped::others) = 
 				(
 					if hasEscaped then
 						(currOffset := !currOffset - wordSize; InFrame(!currOffset)::allocFormals(others))
 					else
 						InReg(Tp.newtemp())::allocFormals(others)
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
 		)
end