signature COLOR 
= 
sig
	structure Frame : FRAME
  
  	type allocation = Frame.register Temp.Table.table
  
  	val color : {interference: Liveness.igraph,
				initial: allocation,
              	spillCost: Graph.node -> int,
              	registers: Frame.register list}
              	-> allocation * Temp.temp list  
end
structure color :> COLOR 
= 
struct
	structure Frame = MIPSFrame
	structure G = Graph
	structure Tp = Temp
	structure L = Liveness

	structure nodeSet = BinarySetFn(struct
								type ord_key = int
								val compare = Int.compare
								end)

	type allocation = Frame.register Tp.Table.table

	fun color (interference as Liveness.IGRAPH{graph, tnode, gtemp, moves}, initial, spillCost, registers) =
	let
		(* initial - temporary, not colored or processed *)
		(* number of available registers *)
		val K = length(registers)
		(* List of nodes *)
		val nodes = G.nodes(graph)

		(* precolored - machine registers, preassigned a color *)
		fun checkIfPrecolored(node) =
        (
        	case Tp.Table.look(initial, gtemp(node)) of
      			SOME _ => true
           	|  	NONE   => false
        )
        (* List of pre-colored and non-precolored nodes *)
        val (precolored, uncolored) = List.partition checkIfPrecolored nodes

		fun mapNodeWithAdj((node,value), t) = G.Table.enter(t, node, value)	
        fun getAdjCount(node) = length(Graph.adj node)

		(* degree - an array containing current degree of each node *)
		val degree = ref(foldl mapNodeWithAdj G.Table.empty (ListPair.zip(uncolored, (map getAdjCount uncolored))))
		(* adjList - for each uncolored node, this maps it to interfering nodes *)
	    val adjList = foldl mapNodeWithAdj G.Table.empty (ListPair.zip(uncolored, (map Graph.adj uncolored)))

	    (* Used LIST for maintaining all the data structures *)
		(* list of low degree non-move-related nodes *)
        val simplifyWorklist = ref(nodeSet.addList(nodeSet.empty, (List.filter (fn n => nodeSet.listItems(!n) < K) uncolored)))
        (* high degree nodes *)
		val spillWorklist = ref(nodeSet.addList(nodeSet.empty, (List.filter (fn n => nodeSet.listItems(!n) >= K) uncolored)))
		(* nodes marked for spilling during this round; initially empty *)
		val spilledNodes = ref []
		(* nodes successfully colored *)
		val coloredNodes = ref []
		(* stack containing temporaries removed from the graph *)
		val selectStack = ref []

		fun Main () =
			(* init lists already made so keep doing this in loop till they are empty *)
			if not nodeSet.isEmpty(!simplifyWorklist) then 
				(* do simplify *)
				Main()
			else if not (nodeSet.isEmpty(!spillWorklist)) then
				(* do spill *)
				Main()
			else
				(* do nothing *)
				()
	in
		Main()
	end
	
end