// Basic acyclic graphs with node and edge attributes. My goal is to leverage this
// for creating an encryption key hierarchy and prove some properties for these
// hierarchies so that I can point to the model when people start arguing about
// proper ways to manage keys and what can be safely done with keys.

open util/relation

// We will be working with nodes
abstract sig Node { }

// At some later point we will associate attributes with nodes
abstract sig NodeAttribute { }

// Similarly we will associate attributes with nodes
abstract sig EdgeAttribute { }

// Graphs consists of nodes, edges, node attributes, and edge attributes
some sig Graph {
  nodes: some Node,
  edges: Node -> set Node,
  nodeAttributes: set (nodes -> set NodeAttribute),
  edgeAttributes: set (edges -> set EdgeAttribute)
}

// We will only deal with acyclic graphs for the time being
pred acyclic(g: Graph) { all n: Node | (n -> n) not in ^(g.edges) }

// Force all graphs to be acyclic
fact { all g: Graph | acyclic[g] }

// The edges must connect nodes in the node set
pred validEdges(g: Graph) { (dom[g.edges] + ran[g.edges]) in g.nodes }

// All graphs must have valid edges
fact { all g: Graph | validEdges[g] }

// Only nodes in the graph can have attributes
pred validNodeAttributes(g: Graph) { g.nodeAttributes.NodeAttribute in g.nodes }

// Make sure node attributes are valid
fact { all g: Graph | validNodeAttributes[g] }

// Only edges in the graph can have edge attributes
pred validEdgeAttributes(g: Graph) { g.edgeAttributes.EdgeAttribute in g.edges }

// Make sure all graphs have valid edge attributes
fact { all g: Graph | validEdgeAttributes[g] }

run { } for 5 Node, 2 NodeAttribute, 1 EdgeAttribute, 1 Graph
