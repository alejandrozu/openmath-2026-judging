/- GPetersen2W3.lean — window checks for GP(k,2), spokes as sixth colour class, 37 ≤ k < 45
   (split into several modules only to bound the memory of each compiler process) -/
import GPetersen2Defs

namespace GPetersen2

theorem Wpart3 : ∀ k, k < 45 → 37 ≤ k → winsAll k := by decide +kernel

end GPetersen2
