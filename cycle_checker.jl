using Graphs
using GraphIO
using EzXML

# Load your graph from GraphML
G = loadgraph(expanduser("~/coding_projects/drawing.graphml"), "G", GraphIO.GraphML.GraphMLFormat())

# Check if a cycle exists (works for both directed and undirected graphs)
has_cycles = is_cyclic(G)
println("Contains cycle: ", has_cycles)
