# Five-family primary-literature comparison

Research edition: 7 October 2026. This note compares QB, TWIN, FINITE, REG5 and HAAR at Robert Huynh's frozen commit 1efc324e155ef0b6a7081c5f695c6c825e7debef. It does not change the earlier judging documents, assert a solution of Erdős 585, or certify historical originality from an unsuccessful search. The companion JSON binds the exact source, declaration and primary-capture identities.

| Family | Known overlap | Remaining candidate delta | Publication treatment |
|---|---|---|---|
| QB | AFK's bipartite zero-sum bound forces a quartic subgraph at \(e\ge3n-2\), when \(\Delta\le6\). | Robert's simple-bipartite \(e\ge3n-5,\ n\ge3\) threshold is three edges stronger than that exact comparator; no earlier identical theorem was located in this bounded review. | Candidate additive refinement. Do not turn a quartic conclusion into a cycle-pair conclusion. |
| TWIN | The selection follows Olson's heterogeneous zero-sum theorem as stated in AFK. Eppstein's subdivided-double theorem already proves the Euler-clone lifting conclusion, and more. | The capped-degree, repeated-neighbourhood host criterion packages those known tools; priority of that precise criterion is unresolved. | Present the forcing criterion as a corollary using known tools. Do not credit either the zero-sum principle or clone lift as a new method. |
| FINITE | Values through five vertices are elementary. The explicit linear lower bounds do not improve the known superlinear asymptotic lower bound. | Specific larger small values, the 31/36 witnesses and their independently checkable encodings have unresolved prior comparisons. | State exact evidence separately: formal through seven; replayed computation through ten; formal lower bounds at eleven/twelve. |
| REG5 | Generic non-bipartite five-regular pair-free existence is already implied by the classical no-quartic examples recorded in Read–Wilson. | Exact 18/32/104 constructions and the least-order question remain a separate comparison; no exact prior identification was located here. | Useful certified examples, not a first-existence claim. The minimum claim remains census-dependent. |
| HAAR | Rank one is covered by prime-dihedral decomposition; characteristic two and centrally symmetric odd-prime palettes are covered by Abelian-Cayley decomposition. | Nonsymmetric odd-prime rank-two/rank-three constructions and the specified composite cyclic palette are candidates. Exact generalised-dihedral results located here give one Hamilton cycle, not two. | State the actual finite-support classification and explicit constructions, with the known subcases and unresolved decomposition priority visible. |

## QB: an additive threshold, not a Hamiltonicity theorem

The frozen endpoint Erdos585.qb5 assumes a finite simple bipartite graph, maximum degree at most six, \(n\ge3\), and \(3n\le e+5\). Its conclusion is a nonempty four-regular subgraph. QB4 is the same family with the weaker threshold and a shorter proof. The K2 boundary in the source explains why the vertex guard cannot be omitted.

AFK Remark 3.6, printed page 85, gives a nonempty \(q\)-divisible subgraph of a bipartite graph when \(e>(q-1)(n-1)\), for a prime power \(q\). With \(q=4\), integer edge counts give \(e\ge3n-2\). Under a degree cap six, every positive divisible degree is exactly four. Robert's threshold therefore lowers this sufficient edge count by three. This comparison neither proves that no earlier refinement exists nor makes the new bound optimal. [Alon–Friedland–Kalai 1984](https://web.math.princeton.edu/~nalon/PDFS/Publications/Regular%20subgraphs%20of%20almost%20regular%20graphs.pdf).

The same paper's printed Theorem 4.3 has \(\Delta\ge2q-2\) and a strict average-degree inequality involving \(\Delta+1\). Printed Remark 4.8(b) gives a different bipartite formula. Its matching-selection proof selects \(2q-1\) classes, so inserting \(q=4,\Delta=6\) without an additional applicability condition is not justified. In fact, the simple graph on 30 linearly ordered vertices with edges at distances 1, 3 and 5 is bipartite, has 81 edges and maximum degree six, and is three-degenerate. Thus it has no quartic subgraph despite average degree \(5.4>36/7\). This is a scope check on that tempting specialization, not a replacement interpretation of the printed theorem.

Suggested text: “We prove the sufficient threshold \(e\ge3n-5\) for nonempty quartic extraction in simple bipartite graphs of maximum degree six and order at least three. Relative to AFK Remark 3.6, this is an additive three-edge refinement. No Hamiltonian decomposition of the extracted subgraph is asserted.”

Improvement to retain: the vertex-deleted six-regular corollary belongs here. P2's extension to general simple graphs must retain its ordinary-proof status unless the new full proof is separately replayed. Thresholds \(3n-6\) or \(3n-7\) outside a finite census remain questions.

## TWIN: known selection and known lifting, with a host corollary

The formal host interface uses a nonempty right set \(R\), a group set \(I\), incidences \(J\subseteq I\times R\), group degrees at most six, right degrees at most three, and \(|J|\ge3|I|+|R|\). An injective map of the two clones of each group and the right vertices into the actual graph must preserve every incidence. This supplies two actual simple cycles with identical vertex sets and disjoint edges.

A short selection proof assigns each incidence its vector in
\[
(\mathbb Z/4\mathbb Z)^{|I|}\oplus(\mathbb Z/2\mathbb Z)^{|R|-1},
\]
omitting one right coordinate. Olson's theorem, stated as AFK Theorem 2.1 on printed page 81, supplies a nonempty zero-sum subset because \(|J|>3|I|+|R|-1\). The caps force group degrees zero/four and right degrees zero/two. The omitted right parity follows from the even total. This is an application of known heterogeneous zero-sum theory, not a new polynomial principle. [AFK1984, Theorem 2.1](https://web.math.princeton.edu/~nalon/PDFS/Publications/Regular%20subgraphs%20of%20almost%20regular%20graphs.pdf).

Suppress the active right vertices of one connected selected component. Each has degree two and joins two distinct groups, so the edge-labelled suppression is a connected loopless four-regular multigraph. Doubling every group into two false twins recovers precisely its subdivided double. Eppstein's v1 Definition 2 and Theorems 1–2 show that this graph has at least \(2^{|I_{\rm active}|}\) Hamilton cycles and that the complement of every Hamilton cycle is Hamiltonian. The Euler-tour/two-clone mechanism in Robert's ordinary proof is the same known construction. [Eppstein, arXiv:2510.18359v1](https://arxiv.org/html/2510.18359v1), [author's publication record](https://ics.uci.edu/~eppstein/pubs/p-subdub.html).

Consequently, the precise host criterion may be a useful newly stated corollary, but the existing ingredients do not support a claim of a new clone-lifting method. The direct host formulation was not located in the bounded search; its originality remains unresolved, and its derivation from known ingredients should be disclosed.

Two safe ordinary strengthenings are detailed in research_five_TWIN_ordinary_bridge.md:

1. For a **nonempty** finite simple bipartite host with \(\Delta\le6\), no singleton left twin class, and \(e\ge3v-2\), the pair is forced. The two shore deficits sum to at most four, hence the shores balance and their equal deficits are 0, 1 or 2. A singleton-free twin partition excludes deficit one; deficit two is the old exact-density theorem; deficit zero uses the general incidence budget.
2. A nonempty six-regular bipartite host with at most two singleton left classes also contains a pair. After separating class sizes \(2,3,1\) as \(p,q,s\), the incidence budget is \(p\ge s\). For \(s=1\), a singleton neighbour's remaining five neighbours require a pair class. For \(s=2,p=1\), the two singleton neighbourhoods would be disjoint but both lie in the unique pair class's six-neighbour set, a contradiction.

These are proposed ordinary corollaries of the existing interfaces. This research note has not compiled or printed new wrappers. Both belong to TWIN, without additional family credit. Eppstein's exponential-count/complement property is a further known consequence on the selected support, not a new strengthening attributable to this project.

## FINITE: exact values versus lower-bound certificates

The original definition is the maximum number of edges of a finite simple graph that avoids two edge-disjoint simple cycles with the same vertex set. It is not a Hamilton-decomposition extremal number on the whole host.

The elementary part is \(f(n)=\binom n2\) for \(n\le4\), and \(f(5)=9\): a pair needs degree four at each support vertex; K5 has a two-Hamilton-cycle decomposition, while K5 minus one edge cannot support a pair. Robert also has formal proofs \(f(6)=12,\ f(7)=16\). The known frozen public replay checks 106 authored source files and 84 selected standard-axiom declarations, including these values and the lower bounds \(f(11)\ge31,\ f(12)\ge36\). It does not formally prove the corresponding two upper bounds.

The supplied computation reports \(f(8),\ldots,f(12)=19,23,27,31,36\). The independently replayed author computation in the review package extends through ten. At eleven/twelve the historical upper-bound computations remain distinct from the formal lower certificates. No “formal exact through twelve” wording is justified by the selected endpoints.

The published CJMM theorem gives an upper bound \(cn(\log n)^t\) and discusses the PRS lower bound \(\Omega(n\log\log n)\); it does not give the small table. Robert's explicit linear families therefore do not improve the known asymptotic lower growth. The specific finite counts and encoded lower witnesses require their own prior comparison. No earlier exact larger table was located in this search; that absence is not a priority certificate. [Chakraborti–Janzer–Methuku–Montgomery, Theorem 1.2, published pages 1–3](https://doi.org/10.1016/j.aim.2025.110228).

Suggested text: “We give finite extremal certificates and explicit pair-free constructions. Exact kernel-checked values through seven, replayed computational values through ten, and kernel-checked lower bounds 31 and 36 at orders eleven and twelve are stated separately. The results do not close the asymptotic Erdős-585 gap.”

For a short publishable version, place the elementary values and large census ledger in a reproducibility appendix. Give the 31/36 constructions and their obstruction arguments in the body; do not call them new extremal values unless the upper certificates and historical comparison are resolved.

## REG5: classical existence, specific certificates, separate minimum

Read–Wilson's An Atlas of Graphs, chapter 5, printed page 155, records five-regular graphs without a four-regular subgraph. Since a faithful cycle pair unions to a four-regular graph on its support, that already implies generic five-regular pair-free existence. The book's authors and 26 November 1998 publication date are confirmed by the publisher. [Actual scanned chapter](https://oeis.org/A000088/a000088_14.pdf), [OUP record](https://academic.oup.com/book/54439?searchresult=1).

Sierksma's 1987 paper, printed pages 579–580, instead discusses the six-regular complete tripartite graph on nine vertices with no five-regular subgraph and classifies certain even-degree graphs on \(k+3\) vertices. That source does not identify the specific five-regular/no-quartic witness or Robert's 18-vertex construction. [Sierksma 1987](https://bibliotekanauki.pl/articles/741636.pdf), [publisher bibliography/DOI](https://www.impan.pl/en/publishing-house/journals-and-series/applicationes-mathematicae/all/19/3%2C4).

Robert's 18-vertex witness consists of two three-degenerate nine-vertex blocks joined through three edges; his source explicitly avoids a novelty claim for that construction. The 32-vertex example uses the same small-cut obstruction. The bipartite 104-vertex example must be kept separate: every finite regular bipartite graph has a perfect matching, so a five-regular bipartite graph necessarily has a quartic factor. Pair-freeness still can hold because a quartic factor need not admit two Hamilton cycles on any shared support.

Non-Hamiltonicity alone, including in classical substitution gadgets, is insufficient: it excludes a spanning cycle but not a pair on a proper subset. Likewise, failure of Hamilton decomposition on the full vertex set does not certify pair-freeness. The exact certificates at orders 18, 32 and 104 were not matched to an earlier primary construction in this bounded review.

The minimum order 18 is not a consequence of the formal existence endpoint. It relies on the full exclusion census through 16, whose second method checked only restricted classes and a small sample at 16. The review's fresh finite proof/graph checks do not turn that into an independently repeated complete minimum proof. There is no corresponding minimum claim for bipartite order 104.

Suggested text: “We record small, explicit, independently checkable five-regular pair-free graphs, including a bipartite example. Generic non-bipartite existence is classical. We distinguish the certified examples from the census-supported minimum-order conjecture/claim and make no first-example assertion.”

## HAAR: delimit the actual decomposition delta

Let \(V\) be a module over a prime field, possibly infinite, and let \(S\subseteq V\) be finite. The Haar graph has two labelled shores \(V\times\{0,1\}\), with \(x_0\sim(x+s)_1\) for \(s\in S\). The frozen forward theorem has no finite-ambient hypothesis: four distinct colours supply a pair on a finite support. The selected iff theorem in HaarGamma assumes a finite ambient. An ordinary local-degree proof removes that restriction on the converse, but a new formal infinite-ambient wrapper remains a separate check.

The four selected colours lie in an affine chart of dimension at most three. Its generated subgroup is finite; the witnesses are cycles on one finite component of that four-colour subgraph. No Hamilton cycle on an infinite ambient graph, or decomposition of all colours when \(|S|>4\), is claimed.

The known subcases are substantial:

- **Rank one.** After normalization the component is a reflection-generated Cayley graph of \(D_{2p}\). The prime-dihedral theorem already decomposes it into Hamilton cycles. V1 Theorem 3/Lemma 5 are enough for this comparison. [Zhou et al., arXiv:1810.07866v1](https://arxiv.org/html/1810.07866v1). The revised published work has a changed author list; do not silently mix that bibliography with v1.
- **Characteristic two.** The four-colour component is a connected four-regular Cayley graph of a finite Abelian group using the connections \((s,1)\).
- **Centrally symmetric odd-prime palettes.** If \(S=\{c\pm u,c\pm v\}\), shift the right shore by \(-c\). The graph is the Abelian Cayley graph on \(\langle u,v\rangle\times\mathbb Z_2\) with connections \((\pm u,1),(\pm v,1)\). Finite connected components are therefore covered by the same classical theorem. [Bermond–Favaron–Mahéo 1989, publisher's exact theorem abstract](https://www.sciencedirect.com/science/article/pii/0095895689900403).

The Abelian theorem's complete PDF was unavailable in this session; its precise published abstract was read, and the needed graph isomorphisms above are this review's explicit inference. This theorem must not be extended to an arbitrary nonsymmetric Haar palette without an actual Abelian-Cayley representation.

A new v3 generalized-dihedral preprint dated 5 October 2026 proves a Hamilton cycle in every connected finite generalized-dihedral Cayley digraph of order at least four. It proves **one** cycle, not a Hamilton decomposition. Its 2018 v2 was withdrawn, so the versions must be dated. A 2026 cyclic-Haar result similarly gives one Hamilton cycle when the cyclic order has at most three prime-power factors. Neither supplies the complementary two-cycle conclusion. [Chen–Ou–Qin–Xia–Yuan v3, Theorem 1.3](https://arxiv.org/html/1810.13311v3), [Bonvicini–Pisanski–Žitnik, Proposition 5.1](https://link.springer.com/article/10.1007/s00373-026-03016-w).

The nonsymmetric odd-prime rank-two and rank-three constructions, and the composite cyclic family \(V=\mathbb Z/(n^2),\ S=\{0,n,2n,1\},\ n\ge3\), were not subsumed by a decomposition theorem located in this bounded search. The composite statement is for this palette only, not every composite Haar graph. The odd/even matching permutations and connectedness proofs remain the exact frozen formal source of that conclusion.

Suggested text: “We give explicit complementary cycle constructions in prime-field Haar charts and in one composite cyclic family. Rank-one, characteristic-two and centrally symmetric subcases follow from classical Hamilton-decomposition theorems. We retain the nonsymmetric rank-two/rank-three and specified composite constructions as candidates pending a complete decomposition-priority comparison.”

Useful ordinary strengthening: for any four colours, the witness support is closed under their four incident edges. Hence, within the finite connected four-colour component containing it, it is the entire component, and the two cycles decompose that component. This is not a decomposition of the higher-valency host.

## Search and evidence limits

This review read the frozen source statements and source map, AFK's relevant printed statements, the actual Eppstein full paper, the actual Read–Wilson and Sierksma page images, and the cited dihedral/generalised-dihedral/cyclic-Haar primary theorem text. Searches covered exact small-value strings, five-regular pair-free/no-quartic terminology, Hamilton decompositions of ordinary/generalised dihedral Cayley graphs, and cyclic Haar decompositions. Self-indexed Robert pages and AI-generated literature summaries were not treated as independent prior work.

The main ErdősProblems page returned an access error during this session; the parent formulation is grounded in the frozen source and the published CJMM paper. The AFK author-hosted PDF and Eppstein PDF are preserved by SHA. The old-source Lean replay facts are read from the existing qualified public summary; no compiler was run by this research reviewer. The new ordinary improvements are not relabelled as formal results. No scoring record, author source or earlier PDF has been changed.
