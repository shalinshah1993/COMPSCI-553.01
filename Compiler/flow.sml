signature FLOW =
sig
	structure Graph : GRAPH
	
	(* control: directed graph where each node represents an inst/block
	def: table of temps defined at each node
	use: table of temps in use at each node
	ismove: tells whether the instruction is a move instruction
		-> can be deleted if def and use are identical
	*)
	
	datatype flowgraph =
		FGRAPH of {control: Graph.graph,
					def: Temp.temp list Graph.Table.table,
					use: Temp.temp list Graph.Table.table,
					ismove: bool Graph.Table.table}
end
structure Flow :> FLOW =
struct
	structure Graph = Graph
	datatype flowgraph =
		FGRAPH of {control: Graph.graph,
					def: Temp.temp list Graph.Table.table,
					use: Temp.temp list Graph.Table.table,
					ismove: bool Graph.Table.table}
end