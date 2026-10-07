# Correction to the isolated cherry-packing lemma

Robert Huynh's frozen `bipartite-hamilton/REPORT.md`, Section5.5, omitted a positive-degree hypothesis. Its literal statement permits d=0, empty shores and r=1; all premises then hold while no path exists. [CherryBoundary.lean](../lean/CherryBoundary.lean) formally verifies this counterexample and the limited positive-degree one-cherry statement. It does not verify arbitrary-r packing or main BM.

The corrected ordinary statement is: let H have maximum degree at most **d>0**, let F_P,F_Q be disjoint, and let r≥0 be an integer. If every vertex of F_Q has at least θ≥2 neighbours in F_P and (θ−1)|F_Q|≥3rd, then r vertex-disjoint paths with centre in F_Q and two ends in F_P exist.

For r=0 the conclusion is immediate. Otherwise positivity forces F_Q to be nonempty, so θ≤d follows from the maximum-degree hypothesis. After j<r paths have been chosen, remove their 2j left vertices and j centres. The remaining cross-edge count is at least θ(|F_Q|−j)−2jd. Since j(θ−1+2d)≤j(3d−1)<3rd≤(θ−1)|F_Q|, this count exceeds the number of remaining centres. Some centre therefore has two remaining left neighbours and the greedy construction continues.

Positive degree already holds in the intended main BM application. This correction repairs the isolated written lemma; it is not evidence that the rest of the spectral sampling and router proof is complete. The original dossier and its hashes are preserved.
