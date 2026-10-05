/- GPetersen2W2.lean — window checks for GP(k,2), spokes as sixth colour class, 27 ≤ k < 37
   (split into several modules only to bound the memory of each compiler process) -/
import GPetersen2Defs

namespace GPetersen2

theorem Wpart2 : ∀ k, k < 37 → 27 ≤ k → winsAll k := by decide +kernel

end GPetersen2
