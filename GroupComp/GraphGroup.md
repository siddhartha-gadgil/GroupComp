# Fundamental Group, Covering spaces for Graphs

The first target is the Nielsen-Schreier theorem - every subgroup of a free group is free. Beyond the definition of the fundamental group, we need the following pieces (that are partly independent of each other):

* Any path is equivalent to a reduced path (with the same endpoints).
* Fundamental group of a wedge of circles is the free group
* Spanning trees:
    - Definition of subgraphs.
    - Definition of trees: connected, nonempty, unique reduced path between vertices.
    - Adding an edge to a tree gives a tree.
    - Existence of maximal trees in connected, based graphs (containing the basepoint).
    - Maximal trees are spanning trees.
* Fundamental groups of connected, graphs with basepoint.
    - Find a spanning tree and consider pairs of edges that are not in the tree.
    - Claim that the fundamental group is the free group on the edges not in the tree.
    - For this, define maps in both directions: from paths to the free group and from words to paths.
    - Show that these maps are inverses of each other.
* Covering spaces:
    - Definition of covering spaces and maps.
    - Path lifting and homotopy lifting.
    - Injections from the fundamental group of the covering space to the fundamental group of the base space.
    - Construction of the cover corresponding to a subgroup of the fundamental group of the base space.
    - Proof that the cover indeed corresponds to the subgroup.

---

# A sketch of a formal proof that the fundamental group of a graph is free on the set of edges not in a spanning tree

## The definition of a free group

A free group on a symmetric generating set can be explicitly defined as a structure involving the basis, the inclusion map, a lifting of a function on the basis and a proof of the uniqueness of the lift. A symmetric generating set is more convenient here as it avoids an explicit choice between a pair of opposite edges.

## Group-labelled graphs

Define a *group-labelled graph* associated with a graph $\Gamma$ and group $G$ to be a structure extending a graph with a function `label : E -> G` assigning a group element to each edge of the graph, such that `label (bar e) = (label e)^{-1}` for all edges `e`.

Every group-labelled graph $(\Gamma, G, label)$ determines a groupoid homomorphism (i.e., functor) from the fundamental groupoid of $\Gamma$ (and hence the fundamental group) to $G$ by multiplying along each path.

These are a useful construction for establishing the uniqueness of lift; comparison of homomorphisms on the fundamental group eventually reduces to comparison of labellings of the edges.

## Subgraphs and Spanning trees

These can be defined in analogy with other sub-structures in `mathlib`, such as sub-groups and sub-quivers. A spanning tree is a subgraph defined on the full vertex set with a unique path, up to homotopy, between any two vertices.

## Deriving edge labellings from homomorphisms on the fundamental group

Let $(\Gamma, v)$ be a pointed graph with a spanning tree and suppose $\phi : \pi_1(\Gamma, v) \to G$ is a group homomorphism. For every edge `e` of the graph `\Gamma` let `surround e` be the unique loop obtained by following the spanning tree from the base-point `v` to the source of `e`, adding `e`, and then returning to `e` along the path from the target of `e` to `v`. An edge-labelling of `\Gamma` with elements of the group `G` can be defined using the map `fun e |-> \phi([[surround e]])`; this determines a graph-labelled group. In fact, this labelling uniquely determines the homomorphism -- two homomorphisms are equal iff they give the same edge-labelling (with respect to a fixed spanning tree). It can be shown from the uniqueness of paths on a tree that any tree edge must have label corresponding to the identity element of `G`.

## Proving that the fundamental group of a graph is free

The inclusion map of the edges into the fundamental group is via the map `fun e |-> [surround e]`. 

A function from the non-tree edges to a group can be extended to an an edge-labelling assigning the label `1` (the identity element) to the tree edges. The determines a homomorphism from the fundamental group of the graph to the same group that lifts the chosen function.

To show uniqueness, it suffices to show that every lift gives rise to the same edge-labelling. On non-tree edges, this is forced by the fact that it is a lift, and the labels on the tree edges are always forced to be the identity element (following from the uniqueness of paths on a tree, as stated in the previous section).

Together, these show that the fundamental group of a graph is free.

## [TODO] Constructing a spanning tree for a graph

The easiest way to construct a spanning tree of a finite graph may be through the output of a depth-first traversal of the graph starting from the base-point. The following paper of Natarajan Shankar may be of use in verifying the correctness of DFS: https://dl.acm.org/doi/10.5555/2167938.2167943.  