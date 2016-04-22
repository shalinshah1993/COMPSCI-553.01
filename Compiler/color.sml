signature COLOR 
= 
sig
	structure Frame : FRAME
  
  	type allocation = Frame.register Temp.Table.table
  
  	val color : {interference: Liveness.igraph,
				initial: Frame.register Temp.Table.table,
              	(*spillCost: Graph.node -> int,*)
              	registers: Frame.register list}
              	-> string Temp.Table.table * Temp.temp list  
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
	structure regSet = ListSetFn(struct
									type ord_key = string
									val compare = String.compare
								  	end)

	type allocation = Frame.register Tp.Table.table

	(*fun color ({interference=L.IGRAPH{graph=graph, tnode=tnode, gtemp=gtemp, moves=moves}, initial=initial, spillCost=spillCost, registers=registers}) =*)
	fun color ({interference=L.IGRAPH{graph=graph, tnode=tnode, gtemp=gtemp, moves=moves}, initial=initial, registers=registers}) =
	let
		(* initial - temporary table, not colored or processed *)
		(* number of available registers *)
		fun convertRegToString (reg) =
		(
			case reg of 
				Frame.Reg(x) => x
		)
		val registers = map convertRegToString registers

		val K = length(registers)
		(* List of nodes *)
		val nodes = G.nodes(graph)
		(* Color list *)
		val color = ref Tp.Table.empty

		(* precolored - machine registers, preassigned a color *)
		fun checkIfPrecolored(node) =
        (
        	case Tp.Table.look(initial, gtemp(node)) of
      			SOME(MIPSFrame.Reg(regname))  => true
           	|  	NONE => false
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
			(* pop item off select stack *)
			val n::others = nodeSet.listItems(!selectStack)
			val _ = nodeSet.delete(!selectStack, n)

			val okColors = ref (regSet.addList(regSet.empty, registers))
			val SOME(adjList) = G.Table.look(adjList, tnode n)
			(* Add all the precolored and already colored node to a set *)
			val colored = ref (nodeSet.addList(nodeSet.empty, nodeSet.listItems(!coloredNodes)))
			val _ = (colored := nodeSet.addList(!colored, map gtemp precolored))

			fun removeColorNode (node) =
			let
			 	val SOME(nodeID) = Tp.Table.look(!color, gtemp(node))
			 in
			 	if nodeSet.member(!colored, gtemp node) then 
			 		okColors := regSet.delete(!okColors, nodeID)
			 	else
			 		()
			 end 
		in
			if length(nodeSet.listItems(!selectStack)) <> 0 then
			(
				app removeColorNode adjList;
				if length(regSet.listItems(!okColors)) = 0 then 
					spilledNodes := nodeSet.add(!spilledNodes, n)
				else
				(
					coloredNodes := nodeSet.add(!coloredNodes, n);
					let
						val colorOfNode::others = regSet.listItems(!okColors)
						val _ = regSet.delete(!okColors, colorOfNode)
					in
						color := Tp.Table.enter(!color, n, colorOfNode)
					end
				)
			)
			else
			();
			assignColors()
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
		(Main(); assignColors(); (!color, nodeSet.listItems(!spilledNodes)))
	end
	
end