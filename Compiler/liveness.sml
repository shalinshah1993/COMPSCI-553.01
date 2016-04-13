signature LIVENESS =
sig
	datatype igraph =
		IGRAPH of {graph: IGraph.graph,
					tnode: Temp.temp -> IGraph.node,
					gtemp: IGraph.node -> Temp.temp,
					moves: (IGraph.node * IGraph.node) list}
					
	val interferenceGraph :
		Flow.flowgraph -> igraph * (Flow.Graph.node -> Temp.temp list)
		
	val show : outstream * igraph -> unit
end

structure Liveness :> LIVENESS = 
struct
	structure G = Flow.Graph
	structure Te = Temp
	
	type liveSet = unit Te.Table.table * Te.temp list
	type liveMap = liveSet G.Table.table
	
	datatype igraph =
		IGRAPH of {graph: IGraph.graph,
					tnode: Temp.temp -> IGraph.node,
					gtemp: IGraph.node -> Temp.temp,
					moves: (IGraph.node * IGraph.node) list}
					
	fun interferenceGraph (FGRAPH{control, def, use, ifmove})
					
					
	(* FIX *)
	fun show (outstream, IGRAPH{graph=graph, tnode=tnode, gtemp=gtemp, moves=moves})=
		()
end