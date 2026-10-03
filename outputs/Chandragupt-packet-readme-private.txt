A rank-23 scheme for 3x3 matrix multiplication with 138 nonzero coefficients

Status: work in progress. The scheme, its verification and the evaluator report are final; the paper, the novelty document and the reproduction script are being completed. Everything here is dated and the dates are honest: the first commit is from 2026-09-27 and the scheme was found on 2026-09-30.

The claim

We give an exact rational bilinear algorithm that multiplies two 3x3 matrices with 23 multiplications (the same rank as Laderman 1976) using 138 nonzero coefficients in total across the three coefficient matrices U, V, W. The previous smallest published count at rank 23 is 139 (Smirnov 2013). The scheme is not equivalent to Smirnov's or to any published rank-23 scheme under the usual transformations.

What is claimed: a reduction of the support (number of nonzero coefficients) from 139 to 138 at rank 23. What is not claimed: any reduction of tensor rank; rank 23 is the best known for 3x3 and rank 22 remains open. In practical terms the scheme uses 83 additions instead of 84 (Laderman: 98); its coefficients are +-1 and, after rescaling, twelve values +-2 and +-1/2, which are bit shifts. Its floating-point accuracy is the same as Smirnov's scheme and Laderman's.

Verify it in one minute

The scheme is solutions/support_138/solution.json (coefficients +-2^k, k in -4..4, as submitted) and solutions/support_138_gauged/solution.json (the same scheme after rescaling, 126 entries +-1 and 12 entries +-2 or +-1/2). Either file is a JSON object with keys u, v, w, each a list of 23 rows of 9 entries; an entry is an integer or a pair [numerator, denominator].

Two independent checkers, both without dependencies:

python3 verify/verify.py                     # every scheme under solutions/, exact rational arithmetic
python3 verify/verify.py solutions/support_138_gauged --export-int scheme_int.txt
gcc -O2 -o verify_c verify/verify.c && ./verify_c scheme_int.txt     # integer arithmetic only


A third, machine-checked verification is the Lean 4 certificate in lean/ (core Lean only, no Mathlib, toolchain pinned; cd lean && lake build, about 15 seconds): theorems scheme138_valid and scheme138_support are proved by decide on the integer-scaled scheme, and likewise for the gauged 138, the exotic 139 and the core-1809 143. lean/README.md explains what is proved and how to regenerate the data files from the JSON.

All checkers test the 729 Brent identities: for all a, b, c in 0..8, sum over the 23 terms of u[t][a] v[t][b] w[t][c] equals T[a][b][c], where T[3i+j][3j+k][3k+i] = 1 and all other entries are 0. Entries of A and B are indexed row-major, entries of C as 3 * column + row. Rank is the number of terms; support is the number of nonzero entries of U, V and W together.

The official evaluator of the AutoLab hill alejandrozu/matrix-multiplication-tensor-3x3 (hill tree 526770e74b465dbd444049d169e2f373eeb0339d) checked the submission as experiment b8e0716a on 2026-09-30: PASSED, rank 23, support 138, 729 Brent identities and 2 private replays checked, coefficient domain Q. The report is in evaluation/evaluator_report_b8e0716a.txt, with a leaderboard snapshot next to it.

How it was found

The published rank-23 schemes with the fewest nonzeros all have coefficients +-1, and exhaustive searches over GF(2) (which sees exactly those coefficients) stop at 139. The 138 has coefficients +-2^k, so its nonzero pattern is not a valid scheme over GF(2), and no GF(2) method can see it. It was found by a support-capped random walk over GF(3) with Smirnov's "core" planted (the 81 entries of the needed products fixed to 1), followed by a numerical lift of the resulting zero pattern over the reals, snapping to powers of two, and an exact repair (U and V rounded, W solved exactly over Q). The walk is deterministic: seed 3158 of walk3 on Smirnov's core at cap 138 produces the pattern. bash reproduce/reproduce.sh recreates the exact scheme from that seed in about 12 seconds (walk, numerical lift, snap, exact repair, verification) with the pinned versions in reproduce/requirements.txt; reproduce/README.md gives the expected output.

What else is here
src/: the research code of the whole event (exact checker, flip-graph and tabu walkers over GF(2) and GF(3), SAT neighbourhood tools, numerical search with exact repair). results/approaches.md is the full log of what was tried, with every negative result.
solutions/: our schemes. official_139 and official_141 are the earlier submissions (Smirnov's class and a known 141). exotic_139_support_139 is the 138 rewritten on one pair of terms (support 139, also invisible over GF(2)). core1809_support_143 is a new, inequivalent rank-23 scheme at support 143 found on a different core.
kaggle/: the batch search run on Kaggle notebooks after the find: the runner, every wave's configuration, per-notebook summaries, compressed raw hits and logs, and the analysis. kaggle/analysis/REPORT_138_structure.md (sections A to M) is the detailed account: structure and symmetry of the 138, its one-parameter family, local optimality, cost comparison, the classification of everything found at supports 139-142 (68 symmetry classes, all explained by one construction), the census of all 1,811 cores, the GF(5) search, and the limits.
results/: the collections of published schemes used for comparison (17,387 verified), the literature notes, and the artifacts of the exact GF(2) sweeps.
reports/: the narrative report and the blog draft (Markdown and Word).
evaluation/: the official evaluator report, submission identifiers and leaderboard snapshot.
HANDOFF.md: the running session handoff kept during the event, left as a record.
Limitations, stated plainly
138 is not proven minimal. The evidence against a 137 reachable by our method is empirical: no hit in 416,104 GF(3) walks with three parameter settings, 110,344 GF(5) walks, and a GF(3) census of all 1,811 cores in which only two cores produce any scheme at support 144 or below (the earlier GF(2) census found three further published cores responding at 142-144, and only Smirnov's core reaches below 142).
Local optimality of the 138 (no single coefficient can be removed) is a numerical result (least squares from 40 starts per entry), not an exact proof; the exact statements are the verification itself and the inequivalence invariant.
Nothing here bears on tensor rank 22.
The Lean certificate proves that the schemes satisfy the Brent identities and have the stated supports; it proves nothing about minimality or about rank 22.
Disclosures

Author: Chandragupt Sharma.

Most of the code and analysis in this repository was written with Claude (Anthropic's Claude Code, models Opus 5.5 and Fable 5.1) under the author's direction; AutoLab agent jobs used glm-5.2 for the agent coding step. Compute: a laptop, rented CPU nodes on AutoLab, and free Kaggle notebook compute.