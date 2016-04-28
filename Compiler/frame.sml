signature FRAME = 
sig 
	type frame
	val wordSize : int

	datatype register = Reg of string
  	datatype access = InFrame of int
                  | InReg of Temp.temp

	val newFrame : {name: Temp.label,
					formals: bool list} -> frame
					
	val registerList : register list
	val name : frame -> Temp.label
	val formals : frame -> access list
	val allocLocal : frame -> bool -> access
	val colorList : Temp.temp list
	val exp : access -> Tree.exp -> Tree.exp

	val procEntryExit1 : frame * Tree.stm -> Tree.stm
	val procEntryExit2: frame * Assem.instr list -> Assem.instr list
	val procEntryExit3 : frame * Assem.instr list -> {prolog: string, body: Assem.instr list, epilog: string}

	val externalCall: string * Tree.exp list -> Tree.exp

	datatype frag = PROC of {body: Tree.stm, frame: frame}
            | STRING of Temp.label * string
			
	val zero : Temp.temp
    val FP : Temp.temp    
    val SP : Temp.temp
    val RV : Temp.temp
    val RA : Temp.temp

	val specialArgs : Temp.temp list
	val calleeSave : Temp.temp list
	val callerSave : Temp.temp list
	val argRegs : Temp.temp list
	
	val toString: Temp.label * string -> string
	val tempMap: register Temp.Table.table
	val getTempString: Temp.temp -> string
	val getTempReg: Temp.temp -> register
	val getColorMapString: (register Temp.Table.table * Temp.temp) -> string
end

structure MIPSFrame :> FRAME 
= 
struct
	structure Tr = Tree
	structure S = Symbol
	structure Tp = Temp
	structure A = Assem

	val wordSize = 4
	datatype register = Reg of string

	(* List of Registers for MIPS *)
	(* ZERO Register - value cannot be anything but 0 *)
	val zero = Temp.newtemp()

	(* Function Result Registers - Functions return integer results in v0, and 64-bit integer results in v0 and v1 *)
	val v0 = Temp.newtemp()
	val v1 = Temp.newtemp()

	(* Function Args Registers - hold the first four words of integer type arguments. *)
	val a0 = Temp.newtemp()
	val a1 = Temp.newtemp()
	val a2 = Temp.newtemp()
	val a3 = Temp.newtemp()

	(* Temp Registers - You as thy will *)
	val t0 = Temp.newtemp()
	val t1 = Temp.newtemp()
	val t2 = Temp.newtemp()
	val t3 = Temp.newtemp()
	val t4 = Temp.newtemp()
	val t5 = Temp.newtemp()
	val t6 = Temp.newtemp()
	val t7 = Temp.newtemp()
	val t8 = Temp.newtemp()
	val t9 = Temp.newtemp()

	(* Saved Register - Saved across function calls, saved by callee before using *)
	val s0 = Temp.newtemp()
	val s1 = Temp.newtemp()
	val s2 = Temp.newtemp()
	val s3 = Temp.newtemp()
	val s4 = Temp.newtemp()
	val s5 = Temp.newtemp()
	val s6 = Temp.newtemp()
	val s7 = Temp.newtemp()
	val s8 = Temp.newtemp()

	(* Frame-pointer - Points at the beginning of previous stored frame *)
	val FP = Temp.newtemp()   
	(* Stack-pointer - Points at the top of the stack *)
	val SP = Temp.newtemp()   
	(* Return address *)
	val RA = Temp.newtemp()   
	(* Return value *)
	val RV = Temp.newtemp()   

	val specialArgs = [zero,RV,FP,SP,RA]
	val argRegs = [a0,a1,a2,a3]
	val calleeSave = [s0,s1,s2,s3,s4,s5,s6,s7]
	val callerSave = [t0,t1,t2,t3,t4,t5,t6,t7]
	
	val colorList = calleeSave @ callerSave
	
	val registerList = [Reg("zero"), Reg("RV"), Reg("FP"), Reg("SP"), Reg("RA"), Reg("a0"), Reg("a1"), Reg("a2"), Reg("a3"), Reg("s0"), Reg("s1"), Reg("s2"), Reg("s3"), Reg("s4"), Reg("s5"), Reg("s6"), Reg("s7"), Reg("t0"), Reg("t1"), Reg("t2"), Reg("t3"), Reg("t4"), Reg("t5"), Reg("t6"), Reg("t7")]
	
	val tempList = ["$zero", "$RV", "$FP", "$SP", "$RA", "$a0", "$a1", "$a2", "$a3", "$s0", "$s1", "$s2", "$s3", "$s4", "$s5", "$s6", "$s7", "$t0", "$t1", "$t2", "$t3", "$t4", "$t5", "$t6", "$t7"]

	(* As per Appel, return NONE for everything except special regs using tempMap definition *)
	val specialRegList = [(FP, Reg("$fp")), (RV, Reg("$v0")), (RA, Reg("$ra")), (SP, Reg("$sp")), (zero, Reg("$0"))]
	
	val fullRegList = [(FP, Reg("$fp")), (RV, Reg("$v0")), (RA, Reg("$ra")), (SP, Reg("$sp")), (zero, Reg("$0")), (a0, Reg("$a0")), (a1, Reg("$a1")), (a2, Reg("$a2")), (a3, Reg("$a3")), (s0, Reg("$s0")), (s1, Reg("$s1")), (s2, Reg("$s2")), (s3, Reg("$s3")), (s4, Reg("$s4")), (s5, Reg("$s5")), (s6, Reg("$s6")), (s7, Reg("$s7")), (t0, Reg("$t0")), (t1, Reg("$t1")), (t2, Reg("$t2")), (t3, Reg("$t3")), (t4, Reg("$t4")), (t5, Reg("$t5")), (t6, Reg("$t6")), (t7, Reg("$t7"))]
	
	
	val tempMap = foldr (fn ((temp, regEntry), table) => Tp.Table.enter(table, temp, regEntry)) Tp.Table.empty fullRegList
	
	fun moveVarToReg (savedVar, saveReg) = Tr.MOVE (Tr.TEMP saveReg, Tr.TEMP savedVar)
	
	fun generateSequenceFromList [] = Tr.EXP (Tr.CONST 0)
		| generateSequenceFromList [a] = a
		| generateSequenceFromList (a::l) = (Tr.SEQ (a, (generateSequenceFromList l)))
	
	fun getTempString(temp) =
		case Tp.Table.look(tempMap, temp) of 
		  	NONE => ("$"^Tp.makestring(temp))
		    | SOME(Reg(regName)) => regName
			
	fun getColorMapString(colorMap, temp) =
		case Tp.Table.look(colorMap, temp) of
			NONE => ("$"^Tp.makestring(temp))
			| SOME (Reg(regName)) => regName

	fun getTempReg(temp) =
		case Tp.Table.look(tempMap, temp) of 
		  	NONE => Reg "Grr!"
		    | SOME(regName) => regName
	
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

 	(* For offset k we need frame pointer while for register we don't *)
	fun exp (InFrame(k)) fp:Tr.exp = Tr.MEM(Tr.BINOP(Tr.PLUS, fp, Tr.CONST(k)))
    | exp (InReg (t)) fp:Tr.exp = Tr.TEMP(t)
 
    fun procEntryExit1(frame:frame, body) = 
		let
			val saveRegisters = [RA] @ calleeSave
			val tempRegisters = map (fn t => Tp.newtemp()) saveRegisters
			val RR = generateSequenceFromList (ListPair.mapEq moveVarToReg (tempRegisters, saveRegisters))
			val RS = generateSequenceFromList (ListPair.mapEq moveVarToReg (saveRegisters, tempRegisters))
			val newBody = generateSequenceFromList [RS, body, RR]
			val functionParams = formals frame
			
			fun moveArguments (arg, accessLevel) =
				let
					val newAccess = exp accessLevel
				in
					Tr.MOVE (newAccess (Tr.TEMP FP), Tr.TEMP arg)
				end
				
			val viewShift = generateSequenceFromList (ListPair.map moveArguments (argRegs, functionParams))
		in
			body
		end
	
	fun procEntryExit2(frame, body) = 
		body @
			[A.OPER{assem="",
				src=[zero, RA, SP]@calleeSave,
				dst=[],
				jump=SOME[]}]
			
	fun intToStr i = 
		if i >= 0 then 
			Int.toString i
		else 
			"-" ^ Int.toString(~i)	

	(* Does this part still have JOUETTE in it? *)
	fun procEntryExit3({name=name, formals=params,offset=locals}:frame, body: Assem.instr list) =
		let
			val totalOffset = (!locals + (List.length argRegs)) * wordSize
		in
			{prolog=S.name name ^ ":\n" ^
					"\t\tsw $fp, 0($sp)\n" ^
					"\t\tmove $fp, $sp\n" ^
					"\t\taddiu $sp, $sp, " ^ intToStr(totalOffset) ^ "\n",
			body=body,
			epilog="move $sp, $fp\n" ^
              "\t\tlw $fp, 0($sp)\n" ^
              "\t\tjr $ra\n\n"}
		end
		(*{prolog="\n# PROCEDURE " ^ Symbol.name name ^ "\n",
		body=body,
		epilog= "\n# END " ^ Symbol.name name ^ "\n"}*)

    fun externalCall(funcName, argList) = Tr.CALL(Tr.NAME(Tp.namedlabel(funcName)), argList)

    fun toString(label, s) = S.name(label) ^ ": .ascii \"" ^ (String.toCString(s)) ^ "\"\n"

end