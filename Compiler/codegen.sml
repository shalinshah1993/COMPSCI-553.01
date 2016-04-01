signature CODEGEN =
sig
	structure MIPSFrame : FRAME
	val codegen : MIPSFrame.frame -> Tree.stm -> Assem.instr list
end
structure MIPSGen : CODEGEN =
struct
	structure A = Assem
	structure T = Tree
	structure Tm = Temp
	structure S = Symbol
	fun codegen (frame) (stm: T.stm) : A.instr list =
		let
			fun emit x = ilist := x::!ilist
			fun result(gen) =
				let 
					val t = Tm.newtemp()
				in
					gen t;
					t
				end
				
			fun relopToAssem(T.relop relOp) =
				case(relOp) of
					T.EQ => "beq"
					| T.NE => "bne"
					| T.LT => "blt"
					| T.GT => "bgt"
					| T.LE => "ble"
					| T.GE => "bge"
					| _ => "ERROR!"
			
			fun munchStm(T.SEQ(a,b)) = 
				(munchStm a; munchStm b)
			| munchStm(T.LABEL lab) =
				emit(A.LABEL{assem=lab ^ ":\n", 
				lab=lab})
			| munchStm(T.JUMP(T.NAME(lab), labList)) =
				emit(A.OPER{assem="j `j0\n",
					src=[],
					dst=[],
					jump=SOME([lab])})
			| munchStm(T.JUMP(e1, labList)) =
				emit(A.OPER{assem="jr `j0\n",
					src=[munchExp e1],
					dst=[],
					jump=SOME([labList])})
			| munchStm(T.CJUMP(oper, e1, e2, trueLabel, falseLabel)) =
				emit(A.OPER{assem=(relopToAssem(oper)) ^ " `s0, `s1, " ^ S.name(trueLabel) ^ "\n j " ^ S.name(falseLabel) ^ "\n",
					src=[munchExp e1, munchExp e2],
					dst=[],
					jump=SOME([trueLabel, falseLabel])})
			| munchStm(T.CJUMP(oper, T.CONST i, e1, trueLabel, falseLabel)) =
				emit(A.OPER{assem=(relopToAssem(oper)) ^ " `s0," ^ int i ^", " ^ S.name(trueLabel) ^ "\n j " ^ S.name(falseLabel) ^ "\n",
					src=[munchExp e1],
					dst=[],
					jump=SOME([trueLabel, falseLabel])})
			| munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, e1, T.CONST i)), e2))=
				emit(A.OPER{assem="sw `s0, (`s1+" ^ int i ^ ")\n",
					src=[munchExp e1, munchExp e2],
					dst=[],
					jump=NONE})
			| munchStm(T.MOVE(T.MEM(T.BINOP(T.MINUS, e1, T.CONST i)),e2))=
				emit(A.OPER{assem="sw `s0, (`s1~" ^ int i ^ ")\n",
					src=[munchExp e1, munchExp e2],
					dst=[],
					jump=NONE})
			| munchStm(T.MOVE(T.MEM(T.CONST i), e1))=
				emit(A.OPER{assem="sw `s0,(`r0+" ^ int i ^ ")\n",
					src=[munchExp e1],
					dst=[],
					jump=NONE})
			| munchStm(T.MOVE(T.MEM(e1), e2))=
				emit(A.OPER{assem="sw `s0, (`s1)\n",
					src=[munchExp e1, munchExp e2],
					dst=[],
					jump=NONE})
			| munchStm(T.MOVE(T.TEMP t, e2))=
				emit(A.OPER{assem="move `d0, `s0\n",
					src=[munchExp e2],
					dst=[t]})
			| munchStm(T.EXP(e1))= (munchExp(e1);())
				
			and munchExp(T.MEM(T.BINOP(T.PLUS,e1,T.CONST i))) = 
				result(fn r => emit(A.OPER
					{assem="LOAD `d0 <- M['s0+" ^ int i ^ "]\n",
					src=[munchExp e1],
					dst=[r],
					jump=NONE}))
			| munchExp(T.MEM(T.BINOP(T.PLUS, T.CONST i, e1))) =
				result(fn r => emit(A.OPER
					{assem="LOAD `d0 <- M[`s0+" ^ int i ^ "]\n",
					src=[munchExp e1],
					dst=[r],
					jump=NONE}))
			| munchExp(T.MEM(T.CONST i)) =
				result(fn r => emit(A.OPER
					{assem="LOAD `d0 <- M[r0+" ^ int i ^ "]\n",
					src=[],
					dst=[r],
					jump=NONE}))
			| munchExp(T.MEM(e1)) =
				result(fn r => emit(A.OPER
					{assem="LOAD 'd0 <- M[`s0+0\n",
					src=[munchExp e1],
					dst=[r],
					jump=NONE}))
			| munchExp(T.BINOP(T.PLUS,e1,T.CONST i)) =
				result(rn r => emit(A.OPER
					{assem="ADDI `d0 <- 's0+" ^ int i ^ "\n",
					src=[munchExp e1],
					dst=[r],
					jump=NONE}))
			| munchExp(T.BINOP(T.PLUS,T.CONST i,e1)) =
				result(fn r => emit(A.OPER
					{assem="ADDI `d0 <- `s0+" ^ int i ^ "\n",
					src=[munchExp e1],
					dst=[r],
					jump=NONE}))
			| munchExp(T.CONST i) =
				result(fn r => emit(A.OPER
					{assem="ADDI `d0 <- r0+" ^ int i ^ "\n",
					src=[],
					dst=[r],
					jump=NONE}))
			| munchExp(T.BINOP(T.PLUS,e1,e2)) =
				result(fn r => emit(A.OPER
					{assem="ADD `d0 <- 's0+'s1\n",
					src=[munchExp e1, munchExp e2],
					dst=[r],
					jump=NONE}))
			| munchExp(T.TEMP t) = t
		in
			munchStm stm;
			rev(!ilist)
		end
end