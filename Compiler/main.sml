structure Main = struct
  
  structure Tr = Translate
  structure F = MIPSFrame
  structure S = Symbol
  structure R = RegAlloc
  structure C = color

  fun getsome (SOME x) = x

  fun emitproc out (F.PROC{body,frame}) =
    let 
      (*val _ = print ("emit " ^ S.name(F.name frame) ^ "\n")
      val _ = Printtree.printtree(out,body)*)
      val stms = Canon.linearize body
      (*val _ = app (fn s => Printtree.printtree(out,s)) stms*)
      val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
      val instrs =   List.concat(map (MIPSGen.codegen frame) stms') 
  	  val {prolog, epilog, body=instrs'} = MIPSFrame.procEntryExit3(frame, instrs)
  	  val (instrs'', allocation) = R.alloc(instrs', frame)
	  
	  (* Test for liveness *)
	  (*val (g, nodelist) = MakeGraph.instrs2graph(instrs)
      val (igraph, liveoutmapping) = Liveness.interferenceGraph(g)
      val _ = Liveness.show(TextIO.stdOut, igraph)*)
	  (* End test *)
      val format0 = Assem.format(Temp.makestring)
      val format1 = Assem.format(fn (t) => ("$" ^ (case valOf(Temp.Table.look(allocation, t)) of C.Frame.Reg(x) => x)))
    in  
      app (fn i => TextIO.output(out,format0 i)) instrs
    end
    | emitproc out (F.STRING(lab,s)) = TextIO.output(out,s)

    fun withOpenFile fname f = 
     let val out = TextIO.openOut fname
     in (f out before TextIO.closeOut out) 
       handle e => (TextIO.closeOut out; raise e)
       end 

       fun compile filename = 
         let 
          val absyn = Parse.parse filename
          (* val frags = (FindEscape.prog absyn; Semant.transProg absyn) *)
          val frags = Semant.transProg absyn
        in 
          withOpenFile (filename ^ ".s") 
          (fn out => (app (emitproc out) (#frags frags)))
        end

      end






