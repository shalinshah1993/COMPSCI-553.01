signature REG_ALLOC 
= 
sig
	structure Frame : FRAME
	type allocation = Frame.register Temp.Table.table
	(*val alloc : Assem.instr list * Frame.frame -> Assem.instr list * allocation*)
end
structure RegAlloc : REG_ALLOC =
struct

	structure Frame = MIPSFrame
	structure C = color
	structure L = Liveness
	structure M = MakeGraph
	
	type allocation = Frame.register Temp.Table.table
	
	fun alloc (instList, inFrame) =
		let
			val (gr, nlist) = M.instrs2graph(instList)
			val (intGraph, liveMap) = L.interferenceGraph(gr)
			
			val registerList = Frame.specialArgs::Frame.argRegs::Frame.calleeSave::Frame.callerSave
			
			val allocationMap = Frame.tempMap
			
			val (coloredAllocation, spills) =
				C.color{interference=intGraph,
						initial=allocationMap,
						spillcost=(fn (x) => 0),
						registers=registerList}
		in
			(coloredAllocation, spills)
		end
end
