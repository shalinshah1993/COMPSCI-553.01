signature LIVENESS =
sig
	datatype igraph =
		IGRAPH of {graph: Flow.Graph.graph,
					tnode: Temp.temp -> Flow.Graph.node,
					gtemp: Flow.Graph.node -> Temp.temp,
					moves: (Flow.Graph.node * Flow.Graph.node) list}
					
	(*val interferenceGraph :
		Flow.flowgraph -> igraph * (Flow.Graph.node -> Temp.temp list)*)
		
	val show : TextIO.outstream * igraph -> unit
end

structure Liveness :> LIVENESS = 
struct
	structure G = Flow.Graph
	structure Te = Temp
	
	type liveSet = unit Te.Table.table * Te.temp list
	type liveMap = liveSet G.Table.table
	
	datatype igraph =
		IGRAPH of {graph: G.graph,
					tnode: Temp.temp -> G.node,
					gtemp: G.node -> Temp.temp,
					moves: (G.node * G.node) list}
					
	(*fun interferenceGraph (FGRAPH{control, def, use, ifmove})*)
					
					
	(* FIX *)
	fun show (outstream, IGRAPH{graph=graph, tnode=tnode, gtemp=gtemp, moves=moves})=
			TextIO.output(outstream, String.concatWith "\n" (map (fn (n) => Temp.makestring (gtemp(n))) (G.nodes graph))) 
			(* String.concatWith makes printing lists easier *)

end