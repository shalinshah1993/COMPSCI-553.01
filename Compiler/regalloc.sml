signature REG_ALLOC 
= 
sig
	structure Frame : FRAME
	type allocation = Frame.register Temp.Table.table
	val alloc : Assem.instr list * Frame.frame -> Temp.temp list * string Temp.Table.table
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
			
			(*val registerList = Frame.specialArgs @ Frame.argRegs @ Frame.calleeSave @ Frame.callerSave*)
			
			val allocationMap = color.Frame.tempMap
			
			(*val (coloredAllocation, spills) =
				C.color{interference=intGraph,
						initial=allocationMap,
						spillcost=(fn (x) => 0),
						registers=color.Frame.registerList}*)
			val (coloredAllocation, spills) =
				C.color{interference=intGraph,
						initial=allocationMap,
						registers=color.Frame.registerList}
						
		in
			(spills, coloredAllocation)
		end
end
