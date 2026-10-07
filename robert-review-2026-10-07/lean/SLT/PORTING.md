# Attribution and porting record

This five-module matrix-Bernstein dependency is due to Yuanhe Zhang, Jason D. Lee and Fanghui Liu, from [SLT](https://github.com/YuanheZ/lean-stat-learning-theory) at revision `d0f506f0a695018265dccb33bcb05e2f5ca1c876`. It is known foundational mathematics, not an original Robert Huynh result or a proof of the main BM Hamiltonicity theorem.

The original per-file headers and Apache2 license are preserved. The Lean4.32-to4.33 port changes only reflexive conditional simplification in Basic and typed diagonal-product simplification in MatCalc; final axiom/type/instance commands are appended to MatBern. Mathematical statements are unchanged. [Actual port qualification](../../proofs/new-audits/SLT_KNOWN_DEPENDENCY/full-qualification.json) records source revisions, exact changes, eight invocations and the three preserved API failures. The final matrix-Bernstein theorem uses the actual operator norm and only standard kernel axioms.
