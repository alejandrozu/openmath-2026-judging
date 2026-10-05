/- GPetersen2W1.lean — window checks for GP(k,2), spokes as sixth colour class, 5 ≤ k < 27
   (split into several modules only to bound the memory of each compiler process) -/
import GPetersen2Defs

namespace GPetersen2

theorem Wpart1 : ∀ k, k < 27 → 5 ≤ k → winsAll k := by decide +kernel

end GPetersen2
