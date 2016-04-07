structure MakeGraph:
sig
	val instrs2graph: Assem.inster list -> Flow.flowgraph * Flow.Graph.node list
end