import SupportData

noncomputable section
namespace OpenMathReview.Support138Family
open scoped BigOperators
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- Literal zero positions remain zero, without asserting nonzero values inside support. -/
theorem u_zero_outside (s : K) (i : Fin 23) (a : Fin 9) (hzero : baseU i a = 0) :
    u s i a = 0 := by
  fin_cases i <;> fin_cases a <;>
    first
    | rfl
    | norm_num [baseU] at hzero

#print axioms u_zero_outside

/-- Literal zero positions remain zero, without asserting nonzero values inside support. -/
theorem v_zero_outside (s : K) (i : Fin 23) (a : Fin 9) (hzero : baseV i a = 0) :
    v s i a = 0 := by
  fin_cases i <;> fin_cases a <;>
    first
    | rfl
    | norm_num [baseV] at hzero

#print axioms v_zero_outside

/-- Literal zero positions remain zero, without asserting nonzero values inside support. -/
theorem w_zero_outside (s : K) (i : Fin 23) (a : Fin 9) (hzero : baseW i a = 0) :
    w s i a = 0 := by
  fin_cases i <;> fin_cases a <;>
    first
    | rfl
    | norm_num [baseW] at hzero

#print axioms w_zero_outside

end OpenMathReview.Support138Family
