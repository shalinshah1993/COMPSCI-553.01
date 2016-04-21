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

	structure nodeSet = ListSetFn(struct
									type ord_key = Tp.temp
									val compare = Int.compare
								  	end)

	type allocation = Frame.register Tp.Table.table

	fun color ({interference=L.IGRAPH{graph=graph, tnode=tnode, gtemp=gtemp, moves=moves}, initial=initial, spillCost=spillCost, registers=registers}) =
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

		fun mapNodeWithAdj ((node,value), t) = G.Table.enter(t, node, value)	
        fun getAdjCount (node) = length(G.adj node)

		(* degree - an array containing current degree of each node *)
		val degree = ref(foldl mapNodeWithAdj G.Table.empty (ListPair.zip(uncolored, (map getAdjCount uncolored))))
		(* adjList - for each uncolored node, this maps it to interfering nodes *)
	    val adjList = foldl mapNodeWithAdj G.Table.empty (ListPair.zip(uncolored, (map G.adj uncolored)))

	    (* Used LIST for maintaining all the data structures *)
		(* list of low degree non-move-related nodes *)
        val simplifyWorklist = ref (nodeSet.addList(nodeSet.empty, map gtemp (List.filter (fn n => getAdjCount(n) < K) uncolored)))
        (* high degree nodes *)
		val spillWorklist = ref (nodeSet.addList(nodeSet.empty, map gtemp (List.filter (fn n => getAdjCount(n) >= K) uncolored)))
		(* nodes marked for spilling during this round; initially empty *)
		val spilledNodes = ref nodeSet.empty
		(* nodes successfully colored *)
		val coloredNodes = ref nodeSet.empty
		(* stack containing temporaries removed from the graph *)
		val selectStack = ref nodeSet.empty

		fun neighbours(node) =
        let
            val SOME(adjNodes) = G.Table.look(adjList, node)
            val adjNodesSet = nodeSet.addList(nodeSet.empty, map gtemp adjNodes)
            val selectSet = nodeSet.addList(nodeSet.empty, nodeSet.listItems(!selectStack))
        in
            nodeSet.difference(adjNodesSet, selectSet)
        end

		(* Decrement out for all the adjNode of node simplified *)
		fun decrementDegree(m) =
        let
        	val SOME(oldDegree) = G.Table.look(!degree, tnode(m))
        in
            degree := G.Table.enter(!degree, tnode(m), oldDegree - 1);
            (
            	if oldDegree = K then
                	(spillWorklist := nodeSet.delete(!spillWorklist, m); simplifyWorklist := nodeSet.add(!simplifyWorklist, m))
            	else 
            		()
            )
        end

		(* As per appel's algo on page 246 *)
		fun simplify () =
		let
			val simplifyListHead::others = nodeSet.listItems(!simplifyWorklist)
		in
			simplifyWorklist := nodeSet.delete(!simplifyWorklist, simplifyListHead);
			selectStack := nodeSet.add(!selectStack, simplifyListHead);
			nodeSet.app (decrementDegree) (neighbours(tnode(simplifyListHead)))
		end

		(* As per appel's algo on 248. I'm not using any heuristics, just the simplistic case remove first element *)
		fun selectSpill() = 
		let
			val spillListHead::other = nodeSet.listItems(!spillWorklist)
		in
			spillWorklist := nodeSet.delete(!spillWorklist, spillListHead);
			simplifyWorklist := nodeSet.add(!simplifyWorklist, spillListHead)
		end

		fun assignColors() = 
		let
			val name = value
		in
			body
		end

		fun Main () =
			(* init lists already made so keep doing this in loop till they are empty *)
			if not (nodeSet.isEmpty(!simplifyWorklist)) then 
				(* do simplify *)
				(simplify(); Main())
			else if not (nodeSet.isEmpty(!spillWorklist)) then
				(* do spill *)
				(selectSpill(); Main())
			else
				(* do nothing *)
				()
	in
		(Main(); assignColors())
	end
	
end