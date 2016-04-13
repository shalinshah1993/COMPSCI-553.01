signature MAKEGRAPH =
sig
	val instrs2graph: Assem.instr list -> Flow.flowgraph * Flow.Graph.node list
end 
structure MakeGraph :> MAKEGRAPH =
struct

	structure A = Assem
	structure F = Flow
	structure G = F.Graph
	structure T = G.Table
	
	fun instrs2graph instList = 
		let
			
			val newGraph = G.newGraph()
			val emptyTable = T.empty
				
			(* Define function that makes nodelist before nodelist to avoid error *)	
			fun makeNodeList([]) =
				({instTable = emptyTable,
				  defTable = emptyTable,
				  useTable = emptyTable,
				  isMoveTable = emptyTable}, [])
			| makeNodeList(a::l) =
				let
					val newNode = G.newNode(newGraph)
					val ({instTable, defTable, useTable, isMoveTable}, nodeList) = makeNodeList(l)
					
					fun setupNodeInfo(d,s,j) = {instTable = T.enter(instTable, newNode, a),
										  defTable = T.enter(defTable, newNode, d),
										  useTable = T.enter(useTable, newNode, s),
										  isMoveTable = T.enter(isMoveTable, newNode, j)}
				in
					((case a of
						A.OPER{assem, dst, src, jump} => 
							(setupNodeInfo(dst, src, false))
						| A.LABEL{assem, lab} => 
							(setupNodeInfo([], [], false))
						| A.MOVE{assem, dst, src} => 
							(setupNodeInfo([dst], [src], true))
							),
					nodeList @ [newNode])
				end
			
			(* Define the use of the tables for usage later *)
			val ({instTable, defTable, useTable, isMoveTable}, nodeList) = makeNodeList(instList)
			
			(* Connect the nodes together in the graph *)
			fun connectNodeList(inputInst, a::(m::l)) =
				let
					val lookupInst = T.look(inputInst, a)
					
					fun makeLabelNode(label, (from::to)) =
						case lookupInst of
							SOME (A.LABEL{assem,lab}) =>
								if label = lab then
									from
								else
									makeLabelNode (label, to)
							| SOME _ => makeLabelNode (label, to)
				in
					(G.mk_edge{from=a, to=m};
					(case lookupInst of
						SOME(A.OPER{assem,dst,src,jump}) =>
							(case jump of
								SOME labelList =>
									app (fn label => G.mk_edge({from=a, to=makeLabelNode(label, nodeList)})) labelList
								| NONE => ())
						| _ => ());
					connectNodeList(inputInst, (m::l))
					)
				end
			| connectNodeList(_, _) = ()
			
		in
			(connectNodeList(instTable, nodeList);
			(F.FGRAPH{control=newGraph, def=defTable, use=useTable, ismove=isMoveTable}, nodeList))
		end
		
	
end
