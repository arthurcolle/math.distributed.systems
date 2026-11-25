# Ordinary homology forgets the direction of deadlock

Take the undirected triangle on vertices \(1,2,3\). Give it either the
cyclic orientation \(1\to2\to3\to1\), or the transitive orientation
\(1\to2,1\to3,2\to3\). The undirected graphs and their clique complexes
are identical, so every ordinary homology group is identical. The cyclic
orientation has no sink and contains a directed cycle. The transitive
orientation is acyclic and has sink \(3\).

Consequently, an invariant of the undirected clique complex alone cannot
distinguish these two directed behaviors. A distributed-protocol theorem
needs a directed complex or a protocol-specific state-transition model. The
example does not claim that a directed cycle by itself is a deadlock in
every distributed algorithm.
