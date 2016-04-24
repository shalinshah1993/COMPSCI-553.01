signature REG_ALLOC 
= 
sig
	structure Frame : FRAME
	type allocation = Frame.register Temp.Table.table
	val alloc : Assem.instr list * Frame.frame -> Assem.instr list * color.allocation * Frame.frame
end
structure RegAlloc : REG_ALLOC =
struct

	structure Frame = MIPSFrame
	structure C = color
	structure L = Liveness
	structure M = MakeGraph
	
	type allocation = Frame.register Temp.Table.table
	
	fun alloc (instList : Assem.instr list, inFrame: Frame.frame) =
		let
			val (gr, nlist) = M.instrs2graph(instList)
			val (intGraph, liveMap) = L.interferenceGraph(gr)
			
			val allocationMap = C.Frame.tempMap

			val (coloredAllocation, spills) =
				C.color{interference=intGraph,
						initial=allocationMap,
						registers=C.Frame.registerList}
						
		in
			(instList, coloredAllocation, inFrame)
		end
end
