signature COLOR 
= 
sig
	structure Frame : FRAME
  
  	type allocation = Frame.register Temp.Table.table
  
  	val color : {interference: Liveness.igraph,
				initial: allocation,
              	(*spillCost: Graph.node -> int,*)
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
	
	type allocation = Frame.register Temp.Table.table
	
	structure Set = BinarySetFn(struct
									type ord_key = Tp.temp
									val compare = Int.compare
								  	end)
									
	fun color ({interference=L.IGRAPH{graph=graph, tnode=tnode, gtemp=gtemp, moves=moves}, initial=initial, registers=registers}) =
		let
			
			(* List of nodes *)
			val nodes = G.nodes(graph)
			
			(* Color list *)
			val color = ref Tp.Table.empty
			
			(*Local sets for nodes and colors*)
			val nodeSet = Set.addList(Set.empty, (map gtemp (nodes)))
			val colorSet = ref (Set.addList(Set.empty, Frame.colorList))
			(*Reference variable to keep track of remaining colors*)
			val availableColors = colorSet
			
			(*Number of colors we have*)
			val K = Set.numItems(!colorSet)

			(*Reference to keep track of nodes visited*)
			val coloredNodes = ref Set.empty
			val colorMap = ref initial : allocation ref
			
			(* Helper Functions *)
			fun convertTempToReg(t) = 
			(print (("\nConverting: ") ^ ("$"^Tp.makestring(t)) ^ "\n");
				Frame.getTempReg(t))
			
			fun popNodeOffGraph (node) =
				let
					val predecessors = G.pred(node)
					val successors = G.succ(node)
					
					fun popPreds (a::l, node) =
						(G.rm_edge{from=a, to=node};
						popPreds(l, node))
					| popPreds([], node) = ()
						
					fun popSuccs (a::l, node) = 
						(G.rm_edge{from=node, to=a};
						popSuccs(l, node))
					| popSuccs([], node) = ()
				in
					(popPreds(predecessors, node);
					popSuccs(successors, node))
				end
			
			fun getAdjCount (node) = length(G.adj node)
			
			fun isPrecolored(node) =
				case Tp.Table.look(initial, gtemp(node)) of
					SOME _ => true
					| NONE => false
			
			fun maintainWorklists (nodes) =
				let
					val simplifyWorklist = (fn (n) => ((getAdjCount(tnode n) < K ) andalso (isPrecolored(tnode n) = false)))
					
					val spillWorklist = (fn (n) => ((getAdjCount(tnode n) >= K ) andalso (isPrecolored(tnode n) = false)))
				in
					((Set.filter simplifyWorklist nodes), (Set.filter spillWorklist nodes))
				end
				
			fun removeColor([]) = ()
			| removeColor(a::l) =
				((if Set.member((!coloredNodes), a) then
					(*Somehow the color wasn't deleted?*)
					((print "removeColor\n");(availableColors := Set.delete((!availableColors), valOf(Tp.Table.look((!color), a)))))
				else
					());
				removeColor(l))
			
			fun assignColor (node) =
				let
					val neighbors = G.adj(node)
				in
					(if Set.isEmpty((!availableColors)) = false then
						let
							val newColor = hd((Set.listItems((!availableColors))))
							val newNode = gtemp node
						in
							(coloredNodes := Set.add((!coloredNodes, newNode));
							print (("\nAvailable Color temp :") ^ (Int.toString(newColor)) ^ (" is register :") ^ (Frame.getTempString(newNode)) ^ ("\n"));
							colorMap := Tp.Table.enter((!colorMap), newNode, convertTempToReg(newColor));
							print (("After updated MAP: Coloring :") ^ (Int.toString(newNode)) ^ (" with color :") ^ (Frame.getTempString(newNode)) ^ ("\n"));
							color := Tp.Table.enter((!color), newNode, newColor));
							removeColor([newNode])
						end
					else
						print "Spilling: No colors left")
				end
			
			fun colorFullTable (simplify, spill) =
				if (Set.isEmpty(simplify) andalso Set.isEmpty(spill)) then
					()
				else
					(if Set.isEmpty(simplify) then
						print "Spilling: No trivial nodes left\n"
					else
						(let
							val simpHead = hd(Set.listItems(simplify))
							val simpNode = tnode(simpHead)
							val _ = assignColor (simpNode)
							val _ = popNodeOffGraph (simpNode)
							val nodeUnion = Set.union(simplify, spill)
							val remainingNodes = Set.delete(nodeUnion, simpHead)
							val (simplify', spill') = maintainWorklists(remainingNodes)
						in
							colorFullTable(simplify', spill')
						end))
						
			val (simp, spll) = maintainWorklists(nodeSet)
			val _ = colorFullTable(simp, spll)
		in
			(!colorMap, [])
		end
end