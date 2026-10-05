# Independent exact recount of the 3,840-class witness

The independent calculation completed on 4 October 2026 at 22:58:26 UTC. Its elapsed time was 14.437 seconds and measured peak working set was 122,916,864 bytes, including JSON and numeric input ingestion. It agrees exactly with the submitted raw numerator and reduced rational density. It does not change the separate status of the active Lean replay.

Only the decimal strings in the frozen source payload were read. No entrant program, compiler or external numerical receipt was executed. The exact source hashes of the model, counter, certificate, arithmetic/symmetry files and ten data parts are retained in the receipt. The parser checks 1,248 blocks of shape 20×20, a 192×192 upper-triangular one-based block index, bounds 0≤r≤65,536, complete index coverage and the equality of fractional support with the nonzero block indices.

Let Q=65,536. The literal coarse base matrix B has entries in {0, 35139, 51064, Q}; its formula is reproduced directly from `Model.lean`. For each fractional upper-triangular pair, let D_ij be its embedded integer numerator matrix minus B_ij. Lower-triangular matrices are its transposes, exactly as in the source definition; hard blocks have zero centered matrix. Every row and column of D is checked to sum to zero. The maximum absolute centered entry is M=51,064.

The centered expansion is evaluated with exactly the source conventions, including repeated coarse and fine labels. Write P_ijk=D_ik D_jk^T. The triangle, cycle, diamond and tetrahedron contractions are respectively the sums of D_ij(x,y)P_ijk(x,y), P_ijk(x,y)P_ijl(x,y), D_ij(x,y)P_ijk(x,y)P_ijl(x,y), and the six centered edge matrices over all four fine labels. The triangle coefficient is ∑_l[B_il B_jl B_kl−(Q−B_il)(Q−B_jl)(Q−B_kl)]. The cycle coefficient is B_ij B_kl+(Q−B_ij)(Q−B_kl), and the diamond coefficient is 2B_kl−Q.

All indices in these contractions range over their full finite sets. Symmetry permits an unordered triangle to represent six ordered triangles and an unordered tetrahedron to represent 24 ordered tetrahedra. A perturbation edge on a repeated coarse index is zero, so those complete-support triangles and tetrahedra have distinct coarse indices. There are 1,152 unordered triangles and 288 unordered tetrahedra. Cycle and diamond terms need a different convention because repeated opposite coarse indices are allowed: use i≤j and k≤l, multiplying by two for each strict inequality and by one for an equality. Summing these multiplicities recovers exactly 161,472 source cycle terms and 36,864 diamond terms. The independently enumerated path count is 32,448 ordered paths, represented by 17,472 stored canonical matrices.

The baseline root sum can be multiplied by 192. This is justified by an independently checked finite transitivity action on the literal base matrix: a cyclic shift of its three a-coordinates and XOR shifts of its e, s and four-bit coordinates map 0 to each coarse vertex, are bijections, and preserve every base entry. Each root sum includes all 192³ ordered triples and both colors.

NumPy int64 is used only where explicit absolute bounds preclude overflow. Each path entry is bounded by 20M²=52,150,641,920. Each full triangle contraction is bounded by 8,000M³=1,065,208,151,601,152,000, below 2^63. The triangle coefficient is bounded by 192Q³=54,043,195,528,445,952. Higher contractions use signed radix limbs: for a radix R, write an integer array A=A₀+RA₁+R²A₂, with the first two limbs in [0,R) and a signed final limb. Each small dot product is evaluated in int64 and then recombined with Python's arbitrary-size integers.

For tetrahedra, split the six factors into two triple products, each bounded by M³ and therefore already safe in int64. With R=2^20, every 160,000-term limb dot has absolute value below 160,000R²=175,921,860,444,160,000<2^63. For cycles and diamonds, R=2^13 gives bounds 400R²=26,843,545,600 and 400MR²=1,370,738,812,518,400. No floating-point operations or Chinese-remainder uniqueness assumptions are used. A small pilot compares the limb contractions directly with plain Python big-integer products.

The independently computed contributions to the total numerator are:

| Contribution | Exact integer |
|---|---:|
| Base | 519197985000573395335769216006152519680000 |
| Four triangle terms | −3654957610728878894197757971070976000 |
| Three cycle terms | 2020031051473785532473285819804879360 |
| Six diamond terms | 85036728523835256115263835671075840 |
| Tetrahedron terms | −2737724451410292081085558982653440 |

Their sum is **519196432373018212667371525712277942005760**. The denominator Q⁶·3840⁴ is **17226794825372509712833339501233265704960000**. Reducing this fraction gives exactly **8450462766487926638466333426306607129 / 280384030360880691940646801777885184000**.

The script is `check_luke3840_exact.py`. The portable pickle-free input `luke3840_exact_inputs.npz` is 148,632 bytes, with SHA-256 `5ea4d69dd06cbf34520acbbaa4f5c573258aeab40698d5e8cae34e9a3c6fa9ba`. Its manifest binds the compressed arrays to the preserved source hashes and script hash. The full dated output is `luke3840_independent_exact_recount.json`; the pilot and feasibility records are separate. To reproduce without touching the archived receipts, copy the script and numeric input into a fresh directory, then run `python check_luke3840_exact.py --inputs luke3840_exact_inputs.npz`. Python and NumPy are the only mathematical runtime dependencies. Use the original source folder and manifest for an independent review of the parser's binding to the literal Lean data.

This check supports the exact finite weighted-table arithmetic. Historical priority, the event-production chronology, declared resources, and the Lean compiler/runtime trust boundary remain separate questions. Agreement from this independent calculation must not be reported as a Lean replay pass.
