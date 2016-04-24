signature LIVENESS =
sig
	structure G : GRAPH
	datatype igraph =
		IGRAPH of {graph: Flow.Graph.graph,
					tnode: Temp.temp -> Flow.Graph.node,
					gtemp: Flow.Graph.node -> Temp.temp,
					moves: (Flow.Graph.node * Flow.Graph.node) list}
					
	val interferenceGraph :
		Flow.flowgraph -> igraph * (Flow.Graph.node -> Temp.temp list)
		
	val show : TextIO.outstream * igraph -> unit
end

structure Liveness :> LIVENESS = 
struct
	structure G = Flow.Graph
	structure Te = Temp
	structure tempSet = ListSetFn(struct
									type ord_key = Te.temp
									val compare = Int.compare
								  end)
	
	datatype igraph =
		IGRAPH of {graph: G.graph,
					tnode: Te.temp -> G.node,
					gtemp: G.node -> Te.temp,
					moves: (G.node * G.node) list}
					
	fun interferenceGraph (Flow.FGRAPH{control, def, use, ismove}) =
		let
			val nodeList = G.nodes(control)
			
			(* Initialize off of the nodelist *)
			val liveInVals = map (fn _ => []) nodeList
			val liveOutVals = map (fn _ => []) nodeList
			
			val intGraph = G.newGraph()
			val moves = []
			
			fun makeASet(listOfTempRegs) = tempSet.addList(tempSet.empty, listOfTempRegs)
			
			val tempRegList = foldr(fn (n, l) =>
				let
					val u = tempSet.union(makeASet((case G.Table.look(def, n) of
							SOME (ds) => ds
							| NONE => [])), 
										makeASet((case G.Table.look(use, n) of
							SOME (us) => us
							| NONE => [])))
				in
					tempSet.listItems(tempSet.union(makeASet(l), u))
				end) [] nodeList
							  
			val (tnode, gtemp) = foldr (fn (temp, (tempNode, nodeTemp)) => 
				let
					val interferenceNode = G.newNode(intGraph)
				in
					(Te.Table.enter(tempNode, temp, interferenceNode),
					G.Table.enter(nodeTemp, interferenceNode, temp))
				end)
				(Te.Table.empty, G.Table.empty) tempRegList
			
			fun makeALiveSet(listOfLiveTemps : Te.temp list) = 
				let
					fun createLiveSet(tempTable, tempList, []) = (tempTable, tempList)
					| createLiveSet(tempTable, tempList, a::l) =
						let
							val newTempList = a::tempList
							val newTempTable = Te.Table.enter(tempTable, a, ())
						in
							createLiveSet(newTempTable, newTempList, l)
						end
				in
					createLiveSet(Te.Table.empty, [], listOfLiveTemps)
				end
				
			fun getLivenessOfNode(node, nodeIns, nodeOuts) =
				let
					val defs = 
						case G.Table.look(def, node) of
							SOME (ds) => ds
							| NONE => []
							
					val uses =
						case G.Table.look(use, node) of
							SOME (us) => us
							| NONE => []
							
					val newNodeIns =
						tempSet.listItems(tempSet.union(makeASet(uses), tempSet.difference(makeASet(nodeOuts), makeASet(defs))))
					
					val successorNodes = G.succ(node)
					
					val newNodeOuts = 
						let
							fun find(nd, l, base) =
								if (base >= List.length(l)) then
									NONE
								else
									if G.eq(nd, List.nth(nodeList, base)) then
										SOME(base)
									else
										find(nd, l, base+1)
						in
							foldr(fn (successorNode, l) =>
								case find(successorNode, l, 0) of
									SOME i => tempSet.listItems(tempSet.union(makeASet(l), makeASet(List.nth(liveInVals, i))))
									| NONE => l) [] successorNodes
						end
					
				in
					(newNodeIns, newNodeOuts)
				end
				
			fun fixedPoints(ins, outs)=
				let
					val inoutzipper = ListPair.zip(ins, outs)
					val oldnodelist = ListPair.zip(nodeList, inoutzipper)
					
					val newnodelist = List.foldr (fn ((x, (inp, out)), list) => (x, getLivenessOfNode(x, inp, out))::list)
									[] oldnodelist
						
					val (nodeT, inoutpair) = ListPair.unzip(newnodelist)
					val (newins, newouts) = ListPair.unzip(inoutpair)
					
					fun interListCompare(a, b) = List.all(fn (i,j) => i=j) (ListPair.zip(a,b))
					
					fun intraListCompare(a, b) = List.all(fn(i,j) => interListCompare(i,j)) (ListPair.zip(a,b))
				in
					if (interListCompare(ins, newins) andalso interListCompare(outs,newouts)) then
						(newins, newouts)
					else
						fixedPoints(newins, newouts)
				end
				
			fun generateFullMappings() =
				let
					val (ins, outs) = fixedPoints(liveInVals, liveOutVals)
					
					val inpair = ListPair.zip(nodeList, ins)
					val outpair = ListPair.zip(nodeList, outs)
					val nodemap = foldr (fn((nd, li), tm)=> G.Table.enter(tm, nd, li)) G.Table.empty outpair
					val lmap = foldr (fn((nd, li), tm) => G.Table.enter(tm, nd, makeALiveSet(li))) G.Table.empty inpair
				in
					(lmap, nodemap)
				end
				
			val (globalLiveMap, globalNodeMap) = generateFullMappings()
			
			fun generateIGraphEdgesAndMoves() =
				foldr (fn (node, moves) =>
					let
						val defNode = case G.Table.look(def, node) of
								SOME (ds) => ds
								| NONE => []
						val useNode = case G.Table.look(use, node) of
								SOME (us) => us
								| NONE => []
						val moveNode = case G.Table.look(ismove, node) of
								SOME (im) => im
								| NONE => false
					in
						((case G.Table.look(globalLiveMap, node) of
							SOME (lt, ll) =>
								app (fn d =>
									app (fn ltmp =>
										case (Te.Table.look(tnode, d), Te.Table.look(tnode, ltmp)) of
											(SOME (iNodeA), SOME (iNodeB)) => G.mk_edge({from=iNodeA, to=iNodeB})) ll
									) (defNode));
									
						if moveNode then
							if (List.length(useNode) = 1 andalso List.length(defNode) = 1) then
								case (Te.Table.look(tnode, List.nth(defNode, 0)), Te.Table.look(tnode, List.nth(useNode, 0))) of
									(SOME (nodeA), SOME (nodeB))=> (nodeA, nodeB)::moves
							else
								moves
						else
							moves)
					end) [] nodeList

			val moves = generateIGraphEdgesAndMoves()
		in
			(
				IGRAPH {
						graph = intGraph,
						tnode = fn tmp =>
							case Te.Table.look(tnode, tmp) of
								SOME a => a,
						gtemp = fn n =>
							case G.Table.look(gtemp, n) of
								SOME t => t,
						moves = moves
					},
				fn x =>
					case G.Table.look(globalNodeMap, x) of
						SOME (l) => l
			)
		end
					
	fun show (outstream, IGRAPH{graph=graph, tnode=tnode, gtemp=gtemp, moves=moves})=
		let
			val stringFunc = (fn (x) => Temp.makestring (gtemp(x))) 
			val nodeGraph = G.nodes graph
			fun putNodesTogether(nd) = (stringFunc nd) ^ "-->" ^ (String.concatWith "," (map stringFunc (G.adj(nd))))
		in
			TextIO.output(outstream, String.concatWith "\n" (map putNodesTogether(nodeGraph)) ^ "\n" )
		end
end