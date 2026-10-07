Robert Huynh: Harvard Business School, MBA programme (author-reported affiliation). Alejandro Zarzuelo Urdiales: OpenMath. Author-review manuscript, 7 October 2026.

## Abstract

We collect eight related families of results concerning two edge-disjoint cycles with the same vertex set. The principal certified results are a quartic-extraction theorem for bipartite graphs of maximum degree six at the threshold $3n-5$, a cycle-pair criterion throughout the dense range for a restricted class with repeated neighbourhoods, explicit pair-free five-regular graphs, finite extremal constructions, a four-colour classification for prime-field Haar graphs, and an obstruction to a specified one-round recolouring detector. The substitution criterion and prescribed-vertex deletion equivalence are formally verified. The recolouring obstruction extends to arbitrary finite Sidon palettes in characteristic-three modules, without a finite ambient-space assumption, and the parabola family has a sharp two-round threshold. For exact four-colour prime-field palettes, every connected component has a Hamilton decomposition. A quantitative bipartite Hamiltonicity programme is retained with its remaining proof obligations explicit. The recolouring discussion separates the classical Sidon-set construction from its application to the detector. A linked proof repository supplies complete Lean sources, theorem statements, dependency pins, computational certificates and a comparison with the primary literature. None of these results closes the general asymptotic gap in Erdős 585 or proves that every bipartite six-regular graph contains the required pair. We state the exact hypotheses and the remaining proof or priority obligations for each family, so that the reader can assess the mathematical contributions without reading the longer verification dossier.

## 1. The problem and the contributions

Throughout, a *pair* in a simple graph $G$ means two genuine connected cycles $C_1,C_2$ with $V(C_1)=V(C_2)$ and $E(C_1)\cap E(C_2)=\varnothing$. A graph is *pair-free* if it contains no pair. Write $f(n)$ for the maximum number of edges in a pair-free simple graph on $n$ vertices. The problem is to determine the growth of $f(n)$.

The established general bounds are $\Omega(n\log\log n)\leq f(n)\leq n(\log n)^{O(1)}$. The lower-bound construction of Pyber, Rödl and Szemerédi contains no four-regular subgraph; the polylogarithmic upper bound is due to Chakraborti, Janzer, Methuku and Montgomery \[PRS, CJMM\]. Our results concern finite cases, restricted graph classes, intermediate extraction and the limitations of a particular proof method. We claim no improvement in that general asymptotic order.

A pair has a four-regular union on its common support. The converse fails: a four-regular graph can decompose into two disconnected two-factors rather than two connected cycles. This distinction separates the quartic-extraction theorem from the cycle-pair forcing results throughout the paper.

The eight families are mathematical groupings, not eight independent solutions of the parent problem. We consolidate weaker variants, repeated examples, support lemmas and immediate consequences within their family. Historical novelty is stated relative to the primary sources actually compared, rather than inferred from formal verification or from the number of declarations.

  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  Family    Precisely bounded contribution                                                                    Evidence boundary
  --------- ------------------------------------------------------------------------------------------------- --------------------------------------------------------------------------------
  QB        Bipartite $\Delta\leq6$, $e\geq3n-5$ implies a nonempty quartic                                   Main theorem formal

  TWIN      A pair in every nonempty capped host with $e\geq3n-2$ and no singleton left neighbourhood class   Extended actual-host criterion formal

  FINITE    Exact small values and larger explicit lower constructions                                        Formal exactness through seven; other coverage separated

  REG5      Pair-free five-regular graphs of orders 18, 32 and 104                                            Examples formal; minimum-order claim separately qualified

  SUB       Pair-free gadget substitution for $d\leq7$ and a vertex-deletion equivalence                      Full preservation, regularity, bipartiteness and equivalence formal

  HAAR      Four colours force a pair in every prime-field module; specified composite template               Every exact-four-colour component decomposes formally; known portions credited

  ONE       An arbitrarily large family defeats the supplied-colouring one-round detector                     One-round obstruction and actual full-host two-round sharpness formal

  BM        Candidate quantitative one-sided spectral Hamiltonicity adaptation                                Written main argument; missing formal infrastructure explicit
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

Complete technical proofs and the current verification ledger are in the [companion repository](https://github.com/alejandrozu/openmath-2026-judging/tree/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07). Exact named declarations are listed in Section 10. The repository also retains the longer written dossiers where reproducing every technical lemma would obscure the principal statements here.

## 2. Formal and graph conventions

Formal certificates use the upstream predicate `HasTwoEdgeDisjointCyclesSameVertexSet`: closed Lean graph walks that satisfy `IsCycle`, equal sets of visited vertices, and disjoint lists of traversed edges. Robert's finite-set predicate `HasPairF` is proved equivalent to it. Connectedness is part of the cycle predicate; equal degree sequences or disconnected two-factors are insufficient.

In the substitution section, the skeleton is a loopless labelled multigraph. Parallel edges remain distinct, and two parallel edges form a cycle of length two. The substituted graph itself is simple. In Haar graphs, the two shores are distinct copies of the underlying additive group, even when their coordinate values coincide. Recolouring changes edge labels, never host edges or vertex identities.

The frozen public source is Robert Huynh's revision `1efc324e155ef0b6a7081c5f695c6c825e7debef`. The previous audit compiled 106 public authored source files and checked 84 distinct selected declarations against the standard kernel axiom set. New proofs in this edition are additive and have their own source hashes and actual compiler receipts. Compilation does not establish novelty, and imported published theorems must retain their precise hypotheses. Unresolved target placeholders and unavailable private projects are excluded from certified claims.

## 3. Quartic extraction below the classical threshold

**Theorem Q.** Let $G$ be a finite simple bipartite graph with $n\geq3$, maximum degree at most six and $e(G)\geq3n-5$. Then $G$ contains a nonempty four-regular subgraph.

The theorem is [`Erdos585.qb5`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/Openmath/Proofs/QB5/Statement.lean#L42); `qb4`, at $3n-4$, is a weaker earlier version. The threshold is independent of a particular labelled graph or finite census. Robert's proof is a universal Lean proof, including a bounded case analysis evaluated by the kernel.

The closest located comparator is Alon, Friedland and Kalai \[AFK, Remark 3.6\]. For bipartite graphs, their divisibility argument yields a nonempty four-divisible subgraph once $e>3(n-1)$. With maximum degree at most seven, nonzero degrees in that subgraph must be four, so the integer threshold is $3n-2$. Theorem Q lowers it by three edges under the stronger maximum-degree-six assumption. One must not transfer results whose proof selects seven matching classes directly into the degree-six setting.

**Proof architecture.** Remove vertices whose degree cannot belong to a quartic and reduce a minimal counterexample to a saturated bipartite graph. In an unbalanced saturated piece, a Hall-type deficiency barrier prevents the desired factor. The reduction tracks the deficiencies of both shores and the exact density loss when a vertex or obstruction piece is removed. The critical cases split into smaller pieces or into the explicitly handled low-deficiency configurations. The verified cover identifies every such configuration, with the finite residual branch evaluated inside Lean. The complete recursive reduction, factor construction and cover proof are linked rather than replaced by a numerical experiment.

**Corollary Q1.** If $B$ is a bipartite six-regular graph and $v$ is any vertex, then $B-v$ contains a nonempty four-regular subgraph. Indeed, if $B$ has $N$ vertices, deletion gives $n=N-1$ and $e=3N-6=3n-3\geq3n-5$, while preserving bipartiteness and the degree cap. This corollary does not assert that $B-v$ contains a pair.

The candidate original contribution is the precise improved threshold and its proof mechanism. This is not a new proof of the existence of regular subgraphs in general, nor a Hamilton decomposition theorem. The sharpness of $3n-5$ and the possible extensions to $3n-6$ or $3n-7$ remain separate questions.

## 4. Repeated neighbourhoods force an actual pair

**Theorem T.** Let $G$ be a nonempty finite simple graph on disjoint shores $A\sqcup R$, with edges only between shores, maximum degree at most six and $e(G)\geq3|V(G)|-2$. Suppose every $a\in A$ has a distinct vertex $b\in A$ with exactly the same neighbourhood in $R$. Then $G$ contains a pair.

The frozen source proves the exact-count case. The added endpoint [`OpenMathReview.TwinDensityExtension.hasPair_of_no_singleton_twins_dense`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/TwinDensityExtension.lean#L132) proves the full inequality range. Hypotheses are read directly from $G$; no quotient cycle or successful pair is assumed. Nonemptiness is essential because the empty graph satisfies $e+2\geq3n$ without containing a pair.

**Proof.** Put $a=|A|$, $r=|R|$. The two nonnegative shore deficits $6a-e$ and $6r-e$ sum to at most four and differ by $6(a-r)$, so $a=r$ and their common value $d$ is at most two. A nonzero deficit from a repeated-neighbourhood class has multiplicity at least two, ruling out $d=1$. A class of size at least four must have six common neighbours, or its deficit would exceed two; it gives $K_{4,4}$.

Otherwise let $p,q$ count the classes of sizes two and three and let $g=p+q$. The quotient incidence graph has left degrees at most six and right degrees at most three. Write $m$ for its number of incidences. If $d=0$, then $m=6g$ and $r=2p+3q$, so $m\geq3g+r$. If $d=2$, exactly one pair class loses one common neighbour; hence $m=6g-1$ and $p\geq1$, giving the same inequality.

Apply the classical zero-sum selection \[AFK, Theorem 2.1\] in $(\mathbb Z/4\mathbb Z)^g\oplus(\mathbb Z/2\mathbb Z)^{r-1}$. The bound $m\geq3g+r$ gives a nonempty selected incidence set whose left degrees are zero or four. The omitted right parity follows from the even selected total, so right degrees are zero or two. Take an active connected component and suppress the degree-two right vertices. The result is a connected four-regular loopless multigraph with individually labelled edges. Its subdivided double embeds in $G$ using two actual twins in each active class. The known Euler-tour lift gives two complementary Hamilton cycles on that subgraph \[Eppstein\]; their actual supports and edges map faithfully into $G$. ∎

The selected subgraph is precisely a subdivided double, and Eppstein's prior is stronger: every Hamilton cycle there has a Hamiltonian complement. The selection is classical Olson/AFK zero-sum theory. The possible contribution is the exact actual-host criterion and its formalization, rather than a new counting principle or Eulerian lift. Its priority remains unresolved and it may be a routine corollary of those ingredients. The at-most-two-singleton extension is tracked separately.

## 5. Finite extremal profiles and lower constructions

The source reports the profile

$$
(f(1),\ldots,f(12))=(0,1,3,6,9,12,16,19,23,27,31,36).
$$

The evidence is not uniform across this row. Exact values through seven have formal statements; the finite procedures through ten were independently replayed in the prior audit. The displayed exact upper exclusions at eleven and twelve remain source-reported computational coverage, while the lower bounds $f(11)\geq31$ and $f(12)\geq36$ have independently compiled construction proofs. We do not promote a lower witness into an exact maximum.

**Basic counting.** If a pair has support of size $s$, its two cycles use $2s$ distinct edges, hence $2s\leq\binom{s}{2}$ and $s\geq5$. Therefore $f(n)=\binom n2$ for $n\leq4$, and $K_5$ minus an edge is pair-free. Adding a new vertex with three earlier neighbours preserves pair-freeness: any pair containing that vertex would require four distinct incident edges. This supplies useful linear extensions without claiming an asymptotic improvement.

**Larger witnesses.** The two-hub, adjacent-hub and matching-subdivision constructions are supplied with explicit edge descriptions and genuine pair-exclusion proofs. The 11-vertex and 12-vertex lower witnesses have 31 and 36 edges, respectively. The repository records vertex counts, edge counts and theorem statements alongside their edge lists, so that construction and extremal exactness can be checked separately.

The publication contribution is a reproducible finite record and any newly identified construction mechanism. The trivial small values and routine extension argument are background; a complete minimality or extremality claim requires both attainment and exhaustive upper coverage. The linear construction families do not surpass the known $\Omega(n\log\log n)$ lower order. A reusable certificate implementation can still be valuable even where the underlying numerical value is already known.

## 6. Five-regular pair-free examples

**Theorem W.** There exist simple five-regular pair-free graphs on 18 and 32 vertices, and a simple bipartite five-regular pair-free graph on 104 vertices.

Their regularity, actual vertex counts and pair exclusion are formalized. The three examples are concrete certified witnesses, not three different asymptotic theorems. The 104-vertex source also supplies a second valid assignment that is not isomorphic to the formal witness; it illustrates the same construction family.

**The 104-vertex mechanism.** A bipartite gadget has six inner and seven outer vertices. Its inner vertices all have degree five, and its outer deficiency is distributed as $1,2,2$ over three ports. The gadget is built from $K_{3,3}$ by adding vertices with three earlier neighbours, so it contains no four-regular subgraph and no pair. Eight copies are joined according to a five-regular bipartite multigraph skeleton. Small cuts of sizes two and three confine any alleged pair to a pair-free block. The existing formal proof uses this cut certificate directly, rather than relying on the general substitution theorem in Section 7.

The source reports an exhaustive exclusion of five-regular pair-free graphs through order sixteen, which would establish that eighteen is the smallest order. That is a stronger statement than Theorem W: the large exclusion census was not independently rerun in full. We therefore state eighteen as a certified example and keep the least-order claim conditional on acceptance of the complete census.

Generic non-bipartite five-regular pair-free existence is classical: Read and Wilson \[RW, p.155\] record five-regular graphs without a quartic subgraph, which therefore have no pair. This does not identify the eighteen-vertex witness, prove its minimum order, or settle bipartite pair-freeness. A five-regular bipartite graph always has a quartic factor by removing a perfect matching, so the bipartite example needs actual cycle-pair exclusion. Exact witness and construction priority remain separate questions.

## 7. Substitution and prescribed-vertex deletion

**Definition.** A $d$-gadget is a finite simple bipartite graph $\Gamma$ with shores $I,O$, every inner vertex of degree $d$, every outer vertex of degree at most $d$, and $|O|=|I|+1$. The total outer deficiency is $d$. A valid substitution into a loopless $d$-regular multigraph $L$ replaces every skeleton vertex by a copy of $\Gamma$ and every labelled skeleton edge by one link between outer ports. Each port receives exactly its deficiency in links, and the final graph is simple.

**Theorem S (formal preservation theorem).** If $d\leq7$, both $\Gamma$ and $L$ are pair-free, and $G$ is a valid substitution, then $G$ is pair-free and $d$-regular. If $L$ is bipartite, so is $G$.

**Proof.** Suppose a pair has common support $S$. In one gadget copy, put $S_I=S\cap I$ and $S_O=S\cap O$, and let $x$ count its used link edges in the union of the two cycles. Every selected vertex has union degree four. Counting internal edge ends on the two shores gives

$$
x=4(|S_O|-|S_I|).
$$

There are at most $d\leq7$ links at that copy, so $x$ is zero or four. If it is zero, connectedness confines both cycles to the same pair-free gadget. Otherwise both cycles meet the copy and its complement, and each uses an even positive number of cut edges. Four in total therefore means exactly two per cycle. Contract the gadget copies along either cycle: the retained labelled link edges form a connected two-regular loopless multigraph on the same set of visited copies. They are a cycle, including the possible length-two case. The two projected cycles are edge-disjoint because the link correspondence is a bijection. This contradicts pair-freeness of $L$. Regularity follows from filling deficiencies; the bipartition follows by reversing gadget shores on one side of the skeleton. ∎

The degree bound is the single-passage threshold in this proof. For eight available links, the counting identity also allows $x=8$, so a two-passage pattern is no longer excluded by this argument. This is a boundary of the method, not a counterexample to every possible substitution theorem at larger degree.

**Corollary S1 (formal prescribed-vertex equivalence).** Let B6 assert that every nonempty finite simple bipartite six-regular graph contains a pair. Then B6 is equivalent to the statement that, for every such graph $B$ and every vertex $o$, the graph $B-o$ contains a pair. For the nontrivial direction, if $B-o$ is pair-free, it is a six-gadget whose six distinct neighbours of $o$ each have deficiency one. Substitute it into the supplied pair-free bipartite six-regular multigraph skeleton. Distinct unit-deficiency ports make the resulting substitution simple; Theorem S gives a bipartite six-regular pair-free graph, contradicting B6. The opposite implication is immediate.

The new single endpoint [`RobertPublishable.SUB.theorem_R1`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/R1.lean#L13) proves pair-freeness, actual degree $d$ and bipartiteness from the faithful gadget/link/port data. It derives connected projected cycles and counts parallel edges separately. Its preservation proof even permits heterogeneous pair-free copy fibres with cut size at most seven, and a locally finite infinite skeleton; cycles remain finite closed walks. The endpoint [`RobertPublishable.SUB.prescribed_vertex_equivalence`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/PrescribedVertex.lean#L89) also constructs and verifies the explicit sixteen-vertex, forty-eight-edge pair-free bipartite six-regular multigraph skeleton and the actual six distinct unit ports of the deleted gadget. Both sides quantify over finite nonempty hosts. Neither assertion proves B6.

## 8. Haar graphs and a four-colour threshold

Let $V$ be an additive group and $S\subset V$ a finite palette. The Haar graph $H(V,S)$ has shores $V\times\{0\}$ and $V\times\{1\}$, with $x_0$ adjacent to $(x+s)_1$ for each $s\in S$. Every colour is a translation matching. These graphs are not automatically ordinary Cayley graphs on an abelian group.

**Theorem H.** Let $p$ be prime and let $V$ be any $\mathbb F_p$-module. If $|S|\geq4$, then $H(V,S)$ contains a pair. Conversely, a pair requires at least four colours. The forward theorem is formal without finiteness of $V$; the new [`OpenMathReview.HaarInfinite.hasPair_iff`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/HaarInfinite.lean#L110) completes the converse under the same unrestricted ambient-module hypotheses. This is a finite cycle-pair assertion, not an infinite Hamilton cycle.

**Hamilton decomposition corollary.** If $|S|=4$, every connected component of $H(V,S)$ is finite and decomposes into two Hamilton cycles. Given a pair, its union supplies four distinct neighbours at every support vertex, exhausting the four host neighbours. Its support is therefore closed under all host edges. Connectedness makes that support the whole component. Translations and the shore-reversing map $(x,b)\mapsto(-x,1-b)$ are actual graph automorphisms, so a pair can be moved to any vertex. The new endpoint [`RobertPublishable.HaarComponent.every_connected_component`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/HaarComponents.lean#L73) formalizes both the spanning cycles and the exhaustion of component edges. This is a strengthened formulation of the four-colour result, not an additional independent discovery. For more than four colours, the pair lies in a selected four-colour subgraph; the conclusion does not decompose the larger-palette host.

**Proof architecture.** Choose four distinct colours and translate one to zero. Their affine span has rank one, two or three. Each normalized rank has an explicit connected cycle-pair construction. Injective additive coordinate maps, with a separate shift on the right shore, transport the witnesses into the original Haar graph. The construction proves successor orbits and connectedness, rather than merely two-factor degrees. For the converse, every vertex on the common support has four distinct neighbours in the cycle union, while a Haar vertex has exactly $|S|$ neighbours.

The prime-line case is covered by the dihedral decomposition theorem \[Zhou et al., Theorem 3\]. Degree-four abelian Cayley decomposition \[BFM\] covers characteristic two and centrally symmetric odd-prime palettes: for $S=\{c\pm u,c\pm v\}$, shifting the right shore by $-c$ identifies the four-colour component with an abelian Cayley graph on the subgroup generated by $(\pm u,1),(\pm v,1)$ in $V\times\mathbb Z_2$. Neither comparison settles every nonsymmetric odd-prime rank-two or rank-three palette.

The recent generalized-dihedral preprint \[Chen et al., v3\] proves one Hamilton cycle; the cyclic-Haar result \[BPZ, Proposition 5.1\] also proves one cycle under its factorization hypotheses. Neither is a decomposition theorem. Thus the candidate new portion is the residual complementary-cycle construction and the specified composite template, subject to exact priority review.

**Composite template.** In the cyclic ambient group $\mathbb Z/n^2\mathbb Z$, the four shifts $\{0,n,2n,1\}$ force a pair for every $n\geq3$. For odd $n$, marked translation orbits are spliced into connected red and blue factors. For even $n$, a six-edge exchange merges the blue orbits while preserving the connected red factor. The formal endpoint covers both parities. This is a specified family, not a classification of every composite group or every palette.

## 9. A recolouring barrier and the quantitative expander route

### 9.1 One component-union round

Let $q=3^k$ with $k\geq2$, let $F=\mathbb F_q$, and take the Haar graph on $F^2$ with palette $P=\{(a,a^2):a\in F\}$. Colour each translation matching by its parameter $a$. The graph is simple, connected, bipartite and four-cycle-free, has $N=2q^2$ vertices and degree $q$.

An allowed *round* chooses two colours and swaps them on any union of connected components of their bichromatic graph. It may change arbitrarily many edges or components. The detector examines all bichromatic cycles exposed from the supplied canonical colouring by zero or one such round, and may compare cycles from different resulting states.

**Theorem R.** Every exposed cycle has induced host degree at most three on its support. It consequently has no edge-disjoint host cycle on that same support. For every fixed $C>0$ and $A\geq0$, this obstruction occurs at arbitrarily large orders with $q>C(\log N)^A$.

**Proof.** The parabola is a Sidon set, and in characteristic three this is equivalent to a 2-cap: every subset of at most four points is affinely independent \[HTW, Theorem 3.2\]. Both this equivalence and the parabola construction predate the present work. For a nonempty set $T$ of at most three colours, choose $a_0\in T$ and put $U=\operatorname{span}_{\mathbb F_3}\{v_a-v_{a_0}:a\in T\}$. A component has shores $X+U$ and $X+v_{a_0}+U$: two-edge walks generate the differences, and selected edges stay in those cosets. A fourth palette point in this affine coset would contradict the 2-cap property. The component is therefore induced in the whole host and has degree $|T|\leq3$. After one allowed round, every exposed bichromatic cycle uses at most three original colours. Its support lies in such an induced component; a pair would require four distinct incident host edges at each support vertex, a contradiction. Finally $q=\sqrt{N/2}$ exceeds every fixed polylogarithm along this family. ∎

The contribution is the actual recolouring-detector obstruction, not a new Sidon construction, an avoiding graph of polynomial degree, or a claim about unrestricted Kempe sequences. The full graph already contains pairs by Theorem H. Standard Kempe-equivalence results concern reachability under unrestricted sequences and do not decide this fixed-radius question \[GO\].

**General Sidon-palette theorem.** Let $V$ be any $\mathbb F_3$-module and $S\subset V$ a finite Sidon palette. Under its canonical translation colouring, every cycle exposed after one component-union round has no edge-disjoint host cycle on the same support. The actual endpoint [`OpenMathReview.InfiniteAffinePaletteBarrier.sidon_exposed_cycle_no_partner`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/InfiniteAffinePaletteBarrier.lean#L54) is kernel verified without `Fintype V`. Its proof first derives the geometric closure from the algebraic Sidon condition, then proves the actual canonical matching labels, legal swaps, component inducedness and cycle exclusion. No detector failure or degree bound is a conclusion-shaped premise. If $|S|\geq4$, Theorem H simultaneously supplies an uncoloured pair, emphasizing the limitation of the detector.

**Theorem R2 (formal two-round sharpness).** For every $k\geq2$, the canonical parabola-coloured full host over $\mathbb F_{3^k}$ fails the zero/one-round detector, but two legal component-union rounds expose an actual pair on a common support of exactly 54 vertices. Choose $t\notin\{0,1,-1\}$ and the four colours $0,1,t,1+t$. Their injective rank-three chart transports the $p=3$ construction into the full host. The first round swaps selected components with colours $0$ and $t$; the second swaps the marked component with colours $1$ and $1+t$ after the first move. The proof checks component closure, the literal successive label swaps, matching identification and the connected final cycles. The endpoint [`RobertPublishable.TWO.family_exactly_two_component_union_rounds`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/CycleComposition.lean#L171) combines the lower bound and this full-host witness. Thus two is the minimum number of component-union rounds for this family. The usual construction describes three component flips followed by one; the theorem does not assert minimum individual-flip count.

### 9.2 Quantitative bipartite Hamiltonicity

For a balanced bipartite $d$-regular graph, write $W$ for the biadjacency matrix. Its nontrivial singular-value condition is $s_2(W)\leq(1-\delta)d$; the negative adjacency eigenvalue $-d$ is inherent in bipartiteness and must not be inserted into a two-sided absolute-gap theorem.

**BM quantitative candidate.** The written dossier proposes an absolute-constant threshold $d\geq C_{\rm BM}\delta^{-5}(\log n)^3$ for Hamiltonicity in this one-sided bipartite setting, with a conservative power-six route also recorded. The graph has positive degree and even order $n\geq4$; the asymptotic proof requires its stated sufficiently-large-order convention. The complete sampling, router and rounding argument is linked in the repository. This edition does not call the main theorem Lean verified without an exact audited endpoint.

Müyesser \[M\] proves a power-six two-sided spectral theorem and explicitly notes a bipartite one-sided analogue after Corollary 1.4. Bradač and Janzer \[BJ\] already prove Hamiltonicity and stronger resilience results for regular bipartite expanders. Consequently generic bipartite Hamiltonicity is background. The potentially original delta is the explicit power-five quantitative ledger and its faithful side/parity implementation.

The written power budget is: the sampled layer degree needs $D\gtrsim\delta^{-2}\log n$; the router supports $k\asymp\delta^2 qn/(\log n)^2$ terminals; and the perturbation slack permits reservoir fraction $q\asymp\delta$. Substituting $D\asymp kd/n$ gives the candidate power $\delta^{-5}$. Each of those statements has technical premises, including matrix sampling, bounded endpoint multiplicity, actual disjoint paths and balanced divisibility. A count of exponents is not a substitute for proving them.

The new graph-semantic proofs verify Hamilton-cycle remainder transfer and the balanced-deletion cut loss $t|S|$, rather than the coarser $2t|S|$ bound. They retain the Hamiltonicity/regular-factor premises explicitly and do not certify the main BM theorem. The isolated written cherry-packing lemma also needs $d>0$: with $d=0$, empty shores and one requested path satisfy its literal inequality but provide no path. The new Lean counterexample certifies that defect; positive degree already holds in the intended application. The factor and vertex-deletion consequences are attached to the accepted Hamiltonicity input, not separately counted discoveries. Equal deletions from the two shores are necessary for a spanning bipartite cycle. In edge-expansion language, the power-five and power-six routes correspond to inverse-expansion powers ten and twelve. The avoidance-conditioned extraction bridge E110 remains open; neither route yields an unconditional improvement to the general upper bound for $f(n)$. The unavailable private exponent-eleven and B2 projects are outside this manuscript's certified claims.

## 10. Proof repository, novelty and reproducibility

The [review repository](https://github.com/alejandrozu/openmath-2026-judging/tree/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07) provides the frozen author sources, new additive Lean proofs, complete written arguments, graph certificates, primary-literature comparisons and a result-to-declaration index. The manuscript remains short by linking proof infrastructure rather than reproducing every helper declaration and operational audit.

  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  Claim                             Exact existing Lean endpoint or evidence
  --------------------------------- ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  Q                                 [`Erdos585.qb5`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/Openmath/Proofs/QB5/Statement.lean#L42)

  Q1                                [`Erdos585.exists_four_regular_avoiding_of_bipartite_six_regular`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/Openmath/Proofs/QB4/Statement.lean#L230)

  T                                 [`OpenMathReview.TwinDensityExtension.hasPair_of_no_singleton_twins_dense`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/TwinDensityExtension.lean#L132)

  Finite lower witnesses            [`Erdos585.thirty_one_le_maxEdges_eleven`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/Openmath/Proofs/Final.lean#L112), [`Erdos585.thirty_six_le_maxEdges_twelve`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/Openmath/Proofs/Final.lean#L116)

  H                                 [`OpenMathReview.HaarInfinite.hasPair_iff`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/HaarInfinite.lean#L110)

  Exact-four-colour decomposition   [`RobertPublishable.HaarComponent.every_connected_component`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/HaarComponents.lean#L73)

  Composite Haar                    [`Erdos585.HaarCompositeEven.hasTwoEdgeDisjointCyclesSameVertexSet_all`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/Openmath/Proofs/HaarCompositeEven.lean#L441)

  R                                 [`Erdos585.ParabolaBarrier104.arbitrary_polylog_barrier`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/Openmath/Proofs/ParabolaBarrier104.lean#L145)

  S                                 [`RobertPublishable.SUB.theorem_R1`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/R1.lean#L13)

  General Sidon barrier             [`OpenMathReview.InfiniteAffinePaletteBarrier.sidon_exposed_cycle_no_partner`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/InfiniteAffinePaletteBarrier.lean#L54)

  S1                                [`RobertPublishable.SUB.prescribed_vertex_equivalence`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/PrescribedVertex.lean#L89)

  Two-round sharpness               [`RobertPublishable.TWO.family_exactly_two_component_union_rounds`](https://github.com/alejandrozu/openmath-2026-judging/blob/8dd7bbaff24ae0a0cf07056b8d26c8ff9375568f/robert-review-2026-10-07/lean/CycleComposition.lean#L171)

  BM                                Main Hamiltonicity endpoint remains unverified; exact helper scopes in the theorem index
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

The frozen audit used Lean 4.33.1, Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`, and Formal Conjectures revision `137aec5c7abd3aa61f7a73138a97279acfc79e93`. Selected existing declarations use only `propext`, `Classical.choice` and `Quot.sound`; the finite quartic case check uses kernel reduction, not `native_decide`. New declarations have their own axiom outputs. A proof replay and its dependency pin establish what was checked, not who discovered the mathematics first.

The novelty record distinguishes an exact located predecessor, a result not implied by that predecessor, and an unresolved priority question. Our strongest present publication candidates are the precise extraction threshold, the restricted twin-forcing theorem, the specified recolouring obstruction and any Haar cases surviving exact decomposition comparisons. Finite examples and classifications must retain their evidence and attribution boundaries. Substitution preservation and the prescribed-vertex equivalence are formally complete; their historical priority remains unresolved. BM retains its explicit main proof obligations. Supporting interfaces and classical ingredients do not become additional discoveries by proximity to compiled code.

**Acknowledgements and provenance.** These results were judged and evaluated by Alejandro Zarzuelo Urdiales in connection with OpenMath 2026 at Harvard and MIT. This edition preserves Robert Huynh's mathematical and source attribution. The original work used AI agents for proof development and review; the author repository records that history. The present concise synthesis and additional formal work are supplied for author review. Competition difficulty and progress coefficients are maintained in the separate judging record, rather than treated as mathematical publication claims.

## References

\[AFK\] N. Alon, S. Friedland and G. Kalai, Regular subgraphs of almost regular graphs, Journal of Combinatorial Theory, Series B 37 (1984), 79-91. [Author-hosted paper](https://web.math.princeton.edu/~nalon/PDFS/Publications/Regular%20subgraphs%20of%20almost%20regular%20graphs.pdf).

\[CJMM\] D. Chakraborti, O. Janzer, A. Methuku and R. Montgomery, Edge-disjoint cycles with the same vertex set, Advances in Mathematics 469 (2025), 110228. [Primary preprint](https://arxiv.org/abs/2404.07190).

\[PRS\] L. Pyber, V. Rödl and E. Szemerédi, Dense graphs without 3-regular subgraphs, Journal of Combinatorial Theory, Series B 63 (1995), 41-54. The lower-bound application used here is discussed in \[CJMM\].

\[JS\] O. Janzer and B. Sudakov, Resolution of the Erdős-Sauer problem on regular subgraphs, Forum of Mathematics, Pi 11 (2023). [Primary preprint](https://arxiv.org/abs/2204.12455).

\[Meredith\] G. H. J. Meredith, Regular n-valent n-connected nonHamiltonian non-n-edge-colorable graphs, Journal of Combinatorial Theory, Series B 14 (1973), 55-60. [Publisher record](https://doi.org/10.1016/S0095-8956(73)80006-1).

\[BFM\] J.-C. Bermond, O. Favaron and M. Mahéo, Hamiltonian decomposition of Cayley graphs of degree 4, Journal of Combinatorial Theory, Series B 46 (1989), 142-153. [Publisher record](https://doi.org/10.1016/0095-8956(89)90040-3).

\[HTW\] Y. Huang, M. Tait and R. Won, Sidon sets and 2-caps in $\mathbb F_3^n$, Involve 12 (2019), 995-1003. [Published primary paper](https://msp.org/involve/2019/12-6/involve-v12-n6-p06-p.pdf), particularly Theorems 3.2 and 3.4.

\[GO\] J. Goedgebeur and P. R. J. Östergård, Switching 3-edge-colorings of cubic graphs. [Primary preprint, arXiv:2105.01363](https://arxiv.org/abs/2105.01363).

\[M\] A. Müyesser, Hamiltonicity of mildly pseudorandom regular graphs, arXiv: 2609.35766v1 (28 September 2026). [Primary paper](https://arxiv.org/html/2609.35766v1).

\[BJ\] D. Bradač and O. Janzer, Hamiltonicity of regular sublinear expanders, arXiv: 2605.15043v1 (14 May 2026). [Primary paper](https://arxiv.org/html/2605.15043v1).

\[Eppstein\] D. Eppstein, Hamiltonian Cycles in Subdivided Doubles, Ars Mathematica Contemporanea 26 (4.02) (2026), 1-9; arXiv: 2510.18359v1 (21 October 2025). [Primary theorem and proof](https://arxiv.org/html/2510.18359v1).

\[RW\] R. C. Read and R. J. Wilson, An Atlas of Graphs, Oxford University Press (1998), Chapter 5, p.155. [Publisher](https://academic.oup.com/book/54439), [chapter scan](https://oeis.org/A000088/a000088_14.pdf).

\[Zhou et al.\] H. Zhou, L. Xu, Y. Cui, Q. Ding, Y. Luo, X. Gao and D. Yang, Hamiltonian decomposition of the Cayley graph on the dihedral group $D_{2p}$ where $p$ is a prime, arXiv: 1810.07866v1 (2018). [Exact cited version](https://arxiv.org/html/1810.07866v1).

\[Chen et al.\] J. Chen, J. Ou, Y.-L. Qin, B. Xia and K. Yuan, Hamilton cycles in generalized dihedral Cayley graphs and digraphs, arXiv: 1810.13311v3 (5 October 2026). [Current cited preprint](https://arxiv.org/html/1810.13311v3). This is not the withdrawn earlier version.

\[BPZ\] S. Bonvicini, T. Pisanski and A. Žitnik, All generalized rose window graphs are hamiltonian, Graphs and Combinatorics 42, article 27 (2026), Proposition 5.1. [Primary publication](https://doi.org/10.1007/s00373-026-03016-w).

\[RH\] R. Huynh, Erdős 585 public sources and findings, revision `1efc324e155ef0b6a7081c5f695c6c825e7debef`. [Frozen findings](https://github.com/roberthuynh/erdos-585/blob/1efc324e155ef0b6a7081c5f695c6c825e7debef/findings/FINDINGS.md). The companion retains the complete source map and its associated written proof dossiers.
