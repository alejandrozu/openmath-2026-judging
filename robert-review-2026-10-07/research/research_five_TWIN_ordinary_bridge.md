# Twin selection, prior lifting and safe strengthening

Read-only ordinary proof analysis, 7 October 2026. Frozen source: Robert Huynh, commit `1efc324e155ef0b6a7081c5f695c6c825e7debef`. No Lean source has been edited or compiler invoked by this reviewer.

## The existing formal interface

`TwinCoreForcing.hasPair_of_twin_incidence` (lines 370–397) already proves the faithful host conclusion for finite sets \(I,R\), with \(R\ne\varnothing\), incidences \(J\subseteq I\times R\), group degrees at most six, right degrees at most three, and
\[
 |J|\ge 3|I|+|R|.
\]
An injective map of \((I\times\{0,1\})\sqcup R\) into the actual host must send both clones of every incidence to actual adjacent vertices. No cycles or selected subgraph are assumed in this interface.

It calls `TwinZeroSum.exists_nonempty_selected_incidence` (274–320) to obtain nonempty \(K\subseteq J\) whose group degrees are zero or four and right degrees zero or two. `TwinDoubleCycle.hasPair_of_selected_incidence` (436–495) then constructs actual simple cycles with identical supports and disjoint edge lists, before mapping them injectively into the host.

Pinned source: [the general host interface](https://github.com/roberthuynh/erdos-585/blob/1efc324e155ef0b6a7081c5f695c6c825e7debef/findings/supplement/lean/Openmath/Proofs/TwinCoreForcing.lean#L370-L397).

## A shorter known selection argument

AFK1984, Theorem 2.1 (heterogeneous powers of a prime), applies to incidence vectors in
\[
 (\mathbb Z/4\mathbb Z)^{|I|}\oplus
 (\mathbb Z/2\mathbb Z)^{|R|-1}.
\]
An incidence contributes one to its group coordinate and to its right coordinate, with one right coordinate omitted. The zero-sum threshold is
\[
 3|I|+(|R|-1).
\]
Thus the stated size inequality gives a nonempty zero-sum subset. Group degrees are divisible by four; the group cap six makes them zero or four. The selected total edge count is even, so the omitted right parity follows from all the other right parities. The right cap three makes every right degree zero or two.

This is a direct application of classical zero-sum theory, equivalent in conclusion to Robert's quadratic Boolean-polynomial implementation. It should not be credited as a new polynomial counting principle.

Primary: [AFK1984, Theorem 2.1 and Remark 3.6](https://web.math.princeton.edu/~nalon/PDFS/Publications/Regular%20subgraphs%20of%20almost%20regular%20graphs.pdf).

## Newly located exact lifting prior

Eppstein, *Hamiltonian Cycles in Subdivided Doubles*, arXiv 2510.18359v1, dated 21 October 2025, Definition 2, Theorems 1 and 2 (PDF pp. 2, 4–7), proves that subdivided doubles of connected four-regular multigraphs have Hamiltonian decompositions; in fact the complement of every Hamiltonian cycle is Hamiltonian. The published version is Ars Mathematica Contemporanea 26 (4.02), 2026, DOI 10.26493/1855-3974.3557.f2d.

To identify the prior exactly, take any active connected component of the selected incidence graph \(K\). Its group vertices have degree four and right vertices degree two. Suppress each right vertex to an edge labelled by that actual right vertex. This yields a connected four-regular loopless multigraph: the two group neighbours are distinct, while distinct right vertices may produce parallel edges. Duplicating each group into its two real clones gives precisely the subdivided double of this multigraph. Inactive groups and right vertices are omitted, rather than counted as a connected component.

Eppstein's Euler-tour construction assigns each of the two visits at a four-valent vertex to one of its two twins and reinserts the edge-labelled subdivision vertices. This is exactly the ordinary Euler-clone lift used in the refined manuscript. The prior is stronger about complements of arbitrary Hamiltonian cycles. It does **not** assume or prove Robert's capped-degree critical-density host-selection criterion.

Primary full text: [arXiv v1](https://arxiv.org/html/2510.18359v1). [Author's publication record](https://ics.uci.edu/~eppstein/pubs/p-subdub.html).

The honest candidate delta is therefore the criterion that locates such a subdivided double inside the actual host, together with the faithful formal encoding. The Eulerian lifting ingredient is known.

## Safe density strengthening: ordinary proof

**Claim.** Let \(G\) be a nonempty finite simple bipartite graph, of maximum degree at most six, with shores \(A,R\). Suppose each \(a\in A\) has a distinct equal-neighbourhood twin and
\[
 e(G)\ge 3|V(G)|-2.
\]
Then \(G\) has a faithful cycle pair.

Define shore deficits \(D_A=6|A|-e\) and \(D_R=6|R|-e\). They are nonnegative, their sum is at most four, and their difference is \(6(|A|-|R|)\). Hence \(|A|=|R|\), and \(D_A=D_R=d\in\{0,1,2\}\). A nonzero contribution of an equal-neighbourhood class to \(D_A\) is at least two, because its size is at least two. Therefore \(d=1\) is impossible.

If \(d=2\), then \(e+2=3|V|\), so the existing exact-density theorem applies. If \(d=0\), the graph is six-regular. A twin class of size at least four gives a \(K_{4,4}\) directly, using four of its six common neighbours. Otherwise every class has size two or three. Let \(g\) be their number. The incidence quotient has \(|J|=6g\), right degrees at most three, and
\[
 |R|=|A|=\sum_i k_i\le 3g.
\]
Thus \(3g+|R|\le |J|\); the existing general host interface supplies the pair.

**Formal status.** This is an ordinary checked extension suggested for a new wrapper. It is not yet a new compiled/printed endpoint. The nonempty-host guard is essential: the empty graph satisfies the lower-density inequality but has no pair.

## Six-regular hosts with at most two singleton classes: ordinary proof

**Claim.** Every nonempty finite simple six-regular bipartite graph has a faithful pair if at most two left equal-neighbourhood classes are singletons.

A class of size at least four again gives \(K_{4,4}\). Otherwise write \(p,q,s\) for the numbers of classes of sizes two, three and one, with \(s\le2\). Balanced regular shores give
\[
 |R|=2p+3q+s.
\]
Remove singleton left vertices from the incidence quotient, keeping every right vertex. Its \(g=p+q\) groups have degree six, its right degrees are at most three, and \(|J|=6g\). The selection budget is equivalent to
\[
 6(p+q)\ge3(p+q)+(2p+3q+s),
 \quad\text{or}\quad p\ge s.
\]

For \(s=0\) this is immediate. For \(s=1\), any neighbour of the singleton needs five remaining actual neighbours from complete classes of sizes two and three. Hence a size-two class exists.

For \(s=2\), \(p=0\) is impossible: a right vertex touching one or two singletons would need five or four neighbours from triples. If \(p=1\), a right vertex cannot touch both singletons, since the remaining four neighbours cannot be supplied by the one pair class and any number of triple classes. Their two six-element neighbourhoods are therefore disjoint. Every vertex in either neighbourhood must touch the unique pair class, because the remaining five neighbours decompose as two plus three. That class would have at least twelve neighbours, contradicting degree six. Therefore \(p\ge2\).

The existing quotient selection and clone-lift interface then gives the actual pair. The additional singleton extension is written in the supplied ordinary source, but is not a separately selected endpoint in the existing 106-source/84-print audit. It belongs to the same TWIN family and adds no automatic independent score.

## Publication wording

“Using a degree-constrained zero-sum selection, we obtain a sufficient condition for locating a subdivided-double subgraph in capped-degree bipartite hosts with repeated neighbourhoods. The subsequent Hamiltonian decomposition is the known subdivided-double mechanism. We state the actual-host forcing criterion and its density/low-singleton corollaries with their exact hypotheses.”

Priority of the precise forcing criterion remains unresolved. No absence-of-literature finding is treated as a certificate of newness.

