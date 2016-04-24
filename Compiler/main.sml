structure Main 
= 
struct

    structure Tr = Translate
    structure F = MIPSFrame
    structure Gen = MIPSGen
    structure S = Symbol
    structure R = RegAlloc
    structure C = color

    fun getsome (SOME x) = x

    fun emitproc out (instrs, alloc, frame) =
    let
        val _ = print ("emit " ^ Symbol.name(F.name frame) ^ "\n")
        val format0 = Assem.format(alloc)
        val {prolog=prolog,body=bodyInstrs,epilog=epilog} = F.procEntryExit3(frame,instrs)
        val instrs' = List.filter (fn Assem.MOVE {assem, dst, src} =>
                                        alloc dst <> alloc src
                                    | _ => true)
                                 bodyInstrs
    in
        TextIO.output(out,prolog);
        app (fn i => TextIO.output(out,format0 i)) instrs';
        TextIO.output(out,epilog)
    end    

    fun emitstr out (lab, s) = TextIO.output(out, s)

    fun genInstrs({body,frame}) =
    let
        val stms = Canon.linearize body
        val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
        val instrs = List.concat(map (Gen.codegen(frame)) stms') 
        val instrs' = F.procEntryExit2(frame, instrs)
    in
        instrs'
    end

    fun withOpenFile fname f = 
    let 
        val out = TextIO.openOut fname
    in 
        (f out before TextIO.closeOut out) 
        handle e => (TextIO.closeOut out; raise e)
    end 

    fun compile filename = 
    let 
        val outfile = TextIO.openOut ("output.txt")
        val absyn = Parse.parse filename
        (* val frags = (FindEscape.prog absyn; Semant.transProg absyn) *)
        val {frags, ty} = Semant.transProg absyn

        fun sepFrags(F.STRING(str), (procs,strs)) = (procs,strs @ [str])
              | sepFrags(F.PROC(proc), (procs,strs)) = (procs @ [proc],strs)

        val (procs, strs) = foldr sepFrags ([],[]) frags
        val procInstrs = map (fn (p as {body,frame}) => (genInstrs(p), frame)) procs
        val allocedProcs = map R.alloc procInstrs
        val allocedProcReg = map (fn (instr, colored, frame) => (instr, (fn t => (case Temp.Table.look(colored, t) of SOME(C.Frame.Reg(x)) => (print ((Int.toString(t))^" SOME\n"); "$"^x) | NONE => (print ((Int.toString(t))^" NONE\n"); "THIS IS A FAILURE " ^ Int.toString(t)))), frame)) allocedProcs
    in 
       (* withOpenFile (filename ^ ".s") (fn out => ((app (emitstr out) strs);
                                                  (app (emitproc out) allocedProcReg)))*)
        TextIO.output(outfile,"----COMPILER MOUNTAIN PRINT-OUT----\n\nPrinting AST\n\n");                                          
        PrintAbsyn.print(outfile, absyn);
        TextIO.output(outfile,"\n\nPrinting IR\n\n");
        app (fn s => Printtree.printtree(outfile,#body s)) procs;
        TextIO.output(outfile,"\n\nPrinting Linearized IR\n\n");
        app (fn s => Printtree.printtree(outfile, s)) (List.concat(map (fn s => (Canon.linearize (#body s))) procs));
        TextIO.output(outfile,"\n\nPrinting Assembly with Temps \n\n");
        app (fn s => TextIO.output(outfile,(Assem.format(Temp.makestring) s)))  (List.concat(map genInstrs (procs)));
        TextIO.output(outfile,"\n\nPrinting Assembly with Regs \n\n");
        app (emitproc outfile) allocedProcReg
    end
end