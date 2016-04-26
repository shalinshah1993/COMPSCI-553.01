signature CODEGEN =
sig
	val codegen : MIPSFrame.frame -> Tree.stm -> Assem.instr list
end
structure MIPSGen : CODEGEN =
struct
	structure A = Assem
	structure T = Tree
	structure Tm = Temp
	structure S = Symbol
	structure F = MIPSFrame
	fun codegen (frame) (stm: T.stm) : A.instr list =
		let
			val ilist = ref (nil: A.instr list)
			fun emit x = ilist := x::(!ilist)
			fun result(gen) =
				let 
					val t = Tm.newtemp()
				in
					gen t;
					t
				end
				
			fun relopToAssem(relOp : T.relop) =
				case(relOp) of
					T.EQ => "beq"
					| T.NE => "bne"
					| T.LT => "blt"
					| T.GT => "bgt"
					| T.LE => "ble"
					| T.GE => "bge"
					| _ => "ERROR!"

			fun getBinopString (binOp) = 
				case binOp of
					 T.PLUS => "add"
					| 	T.MINUS => "sub"
					| 	T.MUL => "mul"
					| 	T.DIV => "div"
					| 	T.AND => "and"
					| 	T.OR => "or"
				    |   T.LSHIFT => "lshift"
				    |   T.RSHIFT => "rshift"
				    |   T.ARSHIFT => "arshift"
				    |   T.XOR => "xor"
			
			fun munchStm(T.SEQ(a,b)) = 
				((munchStm a; munchStm b))
			| munchStm(T.LABEL lab) =
				(emit(A.LABEL{assem=S.name(lab) ^ ":\n", 
				lab=lab}))
	        | munchStm(T.JUMP(T.TEMP ra, _)) = 
				emit(A.OPER {assem = "jr `s0\n",
				           src = [ra],
				           dst = [],
				           jump = NONE})
	        | munchStm(T.JUMP(T.NAME labelName, l::rest)) = 
				emit(A.OPER {assem = "j `j0\n", 
	                      src = [],
	                      dst = [],
	                      jump = SOME(l::rest)})
			| munchStm(T.JUMP(e1, labList)) =
				(emit(A.OPER{assem="jr `j0\n",
					src=[munchExp e1],
					dst=[],
					jump=SOME(labList)}))
			| munchStm(T.CJUMP(oper, e1, e2, trueLabel, falseLabel)) =
				(emit(A.OPER{assem=(relopToAssem(oper)) ^ " `s0, `s1, " ^ S.name(trueLabel) ^ "\n j " ^ S.name(falseLabel) ^ "\n",
					src=[munchExp e1, munchExp e2],
					dst=[],
					jump=SOME([trueLabel, falseLabel])}))
			(*| munchStm(T.CJUMP(oper, T.CONST i, e1, trueLabel, falseLabel)) =
				emit(A.OPER{assem=(relopToAssem(oper)) ^ " `s0," ^ Int.toString i ^", " ^ S.name(trueLabel) ^ "\n j " ^ S.name(falseLabel) ^ "\n",
					src=[munchExp e1],
					dst=[],
					jump=SOME([trueLabel, falseLabel])})
					
					Match redundant
					
					*)
			(* ADD is COMMUTATIVE *)
			| munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, e1, T.CONST i)), e2))=
				(emit(A.OPER{assem="sw `s0, (`s1+" ^ Int.toString i ^ ")\n",
					src=[munchExp e1, munchExp e2],
					dst=[],
					jump=NONE}))
			| munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, e1)), e2))=
				(emit(A.OPER{assem="sw `s0, (`s1+" ^ Int.toString i ^ ")\n",
					src=[munchExp e1, munchExp e2],
					dst=[],
					jump=NONE}))
			| munchStm(T.MOVE(T.MEM(T.BINOP(T.MINUS, e1, T.CONST i)),e2))=
				(emit(A.OPER{assem="sw `s0, (`s1~" ^ Int.toString i ^ ")\n",
					src=[munchExp e1, munchExp e2],
					dst=[],
					jump=NONE}))
			| munchStm(T.MOVE(T.MEM(T.CONST i), e1))=
				(emit(A.OPER{assem="sw `s0,(r0+" ^ Int.toString i ^ ")\n",
					src=[munchExp e1],
					dst=[],
					jump=NONE}))
			| munchStm(T.MOVE(T.MEM(e1), e2))=
				(emit(A.OPER{assem="sw `s0, (`s1)\n",
					src=[munchExp e1, munchExp e2],
					dst=[],
					jump=NONE}))
			| munchStm(T.MOVE(T.TEMP t, e2))=
				(emit(A.OPER{assem="move `d0, `s0\n",
					src=[munchExp e2],
					dst=[t],
					jump=NONE}))
			(* Both the MOVE are without registers *)
			| munchStm(T.MOVE(e1, e2))=
				(emit(A.MOVE {assem = "move `d0, `s0\n",
                      src = munchExp(e2),
                      dst = munchExp(e1)}))
			| munchStm(T.EXP(e1))= ((munchExp(e1);()))

			(* Same ORDER as TREE structure for ass code pattern *)
			and munchExp(T.MEM(T.BINOP(T.PLUS,e1,T.CONST i))) = 
				(result(fn r => emit(A.OPER
					{assem="add `d0, "^ Int.toString(i) ^ ", `s0\n",
					src=[munchExp e1],
					dst=[r],
					jump=NONE})))
			| munchExp(T.MEM(T.BINOP(T.PLUS, T.CONST i, e1))) =
				(result(fn r => emit(A.OPER
					{assem="add `d0, "^ Int.toString(i) ^ ", `s0\n",
					src=[munchExp e1],
					dst=[r],
					jump=NONE})))
			| munchExp(T.MEM(T.CONST i)) =
				(result(fn r => emit(A.OPER
					{assem="lw `d0, (r0  + " ^ Int.toString i ^ ")\n",
					src=[],
					dst=[r],
					jump=NONE})))
			(* ZERO is identity for ADD/SUB *)
			| munchExp(T.BINOP(T.PLUS, T.CONST 0, T.CONST i)) =
            	(result(fn r => emit(A.OPER 
            		{assem = "addi `d0, `s0, " ^ Int.toString i ^ "\n",
                    src = [F.zero], 
                    dst = [r], 
                    jump = NONE})))
        	| munchExp(T.BINOP(T.PLUS, T.CONST i, T.CONST 0)) =
            	(result(fn r => emit(A.OPER 
            		{assem = "addi `d0, `s0, " ^ Int.toString i ^ "\n",
                    src = [F.zero], 
                    dst = [r], 
                    jump = NONE})))
        	| munchExp(T.BINOP(T.MINUS, T.CONST 0, T.CONST i)) =
            	(result(fn r => emit(A.OPER 
            		{assem = "addi `d0, `s0, " ^ Int.toString (~i) ^ "\n",
                    src = [F.zero], 
                    dst = [r], 
                    jump = NONE})))
        	| munchExp(T.BINOP(T.MINUS, T.CONST i, T.CONST 0)) =
            	(result(fn r => emit(A.OPER 
            		{assem = "addi `d0, `s0, " ^ Int.toString (~i) ^ "\n",
                    src = [F.zero], 
                    dst = [r], 
                    jump = NONE})))
			(* ADDITION is COMMUTATIVE *)
			| munchExp(T.BINOP(T.PLUS,e1,T.CONST i)) =
				(result(fn r => emit(A.OPER
					{assem="addi `d0, `s0, " ^ Int.toString i ^ "\n",
					src=[munchExp e1],
					dst=[r],
					jump=NONE})))
			| munchExp(T.BINOP(T.PLUS,T.CONST i,e1)) =
				(result(fn r => emit(A.OPER
					{assem="addi `d0, `s0, " ^ Int.toString i ^ "\n",
					src=[munchExp e1],
					dst=[r],
					jump=NONE})))
			(* AND is COMUTATIVE *)
			| munchExp(T.BINOP(T.AND, e1, T.CONST i)) =
        		(result(fn r => emit(A.OPER 
		        	{assem="andi `d0, `s0, " ^ Int.toString i ^ "\n",
					src=[munchExp e1], 
					dst=[r], 
					jump=NONE})))
    		| munchExp(T.BINOP(T.AND, T.CONST i, e1)) =
    			(result(fn r => emit(A.OPER 
    				{assem="andi `d0, `s0, " ^ Int.toString i ^ "\n",
					src=[munchExp e1], 
					dst=[r], 
					jump=NONE})))
        	(* OR is COMMUTATIVE *)
        	| 	munchExp(T.BINOP(T.OR, e1, T.CONST i)) =
         		(result(fn r => emit(A.OPER 
         			{assem="ori `d0, `s0, " ^ Int.toString i ^ "\n",
					src=[munchExp e1], 
					dst=[r], 
					jump=NONE})))
	        | munchExp(T.BINOP(T.OR, T.CONST i, e1)) =
            	(result(fn r => emit(A.OPER 
	            	{assem="ori `d0, `s0, " ^ Int.toString i ^ "\n",
					src=[munchExp e1], 
					dst=[r], 
					jump=NONE})))
            (* XOR is COMMUTATIVE *)
        	| munchExp(T.BINOP(T.XOR, e1, T.CONST i)) =
         		(result(fn r => emit(A.OPER 
         			{assem="xori `d0, `s0, " ^ Int.toString i ^ "\n",
					src=[munchExp e1], 
					dst=[r], 
					jump=NONE})))
	        | munchExp(T.BINOP(T.XOR, T.CONST i, e1)) =
            	(result(fn r => emit(A.OPER 
	            	{assem="xori `d0, `s0, " ^ Int.toString i ^ "\n",
					src=[munchExp e1], 
					dst=[r], 
					jump=NONE})))
			| munchExp(T.BINOP(binOp,e1,e2)) =
				(result(fn r => emit(A.OPER
					{assem=getBinopString(binOp) ^ " `d0, `s0, `s1\n",
					src=[munchExp e1, munchExp e2],
					dst=[r],
					jump=NONE})))
			| munchExp(T.MEM(e1)) =
				(result(fn r => emit(A.OPER
					{assem="lw `d0, 0(`s0) \n",
					src=[munchExp e1],
					dst=[r],
					jump=NONE})))
			| munchExp(T.TEMP t) = (t)
			| munchExp (T.ESEQ(_, _)) = ErrorMsg.impossible "Error! ESEQ should be removed during Tree linearlization"
			| munchExp(T.NAME label) = 
				(result(fn r => emit(A.OPER 
					{assem=("la `d0, " ^ S.name(label) ^ "\n"),
					src=[], 
					dst=[r], 
					jump=NONE})))
			| munchExp(T.CONST i) =
				(result(fn r => emit(A.OPER
					{assem="li `d0, " ^ Int.toString i ^ "\n",
					src=[],
					dst=[r],
					jump=NONE})))
			| munchExp(T.CALL(T.NAME(e), args))= 	
				(emit(A.OPER{
					assem="jal "^S.name(e)^"\n",
					src=munchArgs(0, args),
					dst=[F.RV],
					jump=NONE}); F.RV)										
			and munchArgs (i, []) = []
			| munchArgs(i, a::l) =
				let
				in
					if i < 4 then
						(munchStm(T.MOVE(T.TEMP (List.nth(F.argRegs, i)), T.TEMP (munchExp(a)))); List.nth(F.argRegs, i)::munchArgs(i+1, l))
					else
						raise ErrorMsg.impossible("Spilling!")
				end
		in
			munchStm stm;
			rev(!ilist)
		end
end