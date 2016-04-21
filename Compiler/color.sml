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
	structure G = Flow.Graph
	structure Tp = Temp
	structure L = Liveness

(*	structure nodeSet = BinarySetFn(struct
								type ord_key = int
								val compare = Int.compare
								end)*)
	structure nodeSet = BinarySetFn(struct
									type ord_key = Tp.temp
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
        fun getAdjCount(node) = length(G.adj node)

		(* degree - an array containing current degree of each node *)
		val degree = ref(foldl mapNodeWithAdj G.Table.empty (ListPair.zip(uncolored, (map getAdjCount uncolored))))
		(* adjList - for each uncolored node, this maps it to interfering nodes *)
	    val adjList = foldl mapNodeWithAdj G.Table.empty (ListPair.zip(uncolored, (map G.adj uncolored)))

	    (* Used LIST for maintaining all the data structures *)
		(* list of low degree non-move-related nodes *)
        val simplifyWorklist = ref (nodeSet.addList(nodeSet.empty, (List.filter (fn n => getAdjCount(n) < K) uncolored)))
        (* high degree nodes *)
		val spillWorklist = ref (nodeSet.addList(nodeSet.empty, (List.filter (fn n => getAdjCount(n) >= K) uncolored)))
		(* nodes marked for spilling during this round; initially empty *)
		val spilledNodes = ref []
		(* nodes successfully colored *)
		val coloredNodes = ref []
		(* stack containing temporaries removed from the graph *)
		val selectStack = ref []

		fun neighbours(node) =
        let
            val SOME(adjNodes) = G.Table.look(adjList, node)
            val adjNodesSet = nodeSet.addList(nodeSet.empty , adjNodes)
            val selectSet = nodeSet.addList(nodeSet.empty, !selectStack)
        in
            nodeSet.difference(adjNodesSet, selectSet)
        end

		(* As per appel's algo on page 246 *)
		fun simplify () =
		let
			val simplifyListHead::others = nodeSet.listItems(!simplifyWorklist)

			(* Decrement out for all the adjNode of node simplified *)
			fun decrementDegree(m) =
	        let
	            val SOME(d) = G.Table.look(!degree, m)
	        in
	            degree := G.Table.enter(!degree, m, d - 1);
	            (
	            	if d = K then
	                	(spillWorklist := nodeSet.delete(!spillWorklist, m); simplifyWorklist := nodeSet.add(!simplifyWorklist, m))
	            	else 
	            		()
	            )
	        end
		in
			simplifyWorklist := nodeSet.addList(nodeSet.empty, others);
			selectStack := simplifyListHead::(!selectStack);
			nodeSet.app decrementDegree neighbours(simplifyListHead)
		end

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