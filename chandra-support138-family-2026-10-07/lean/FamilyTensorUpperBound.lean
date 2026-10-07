import SupportBound
import MaskedRow0Fixed
import MaskedRow1Fixed
import MaskedRow2Fixed
import MaskedRow3Fixed
import MaskedRow4Fixed
import MaskedRow5Fixed
import MaskedRow6Fixed
import MaskedRow7Fixed
import MaskedRow8Fixed

noncomputable section
namespace OpenMathReview.Support138Family
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

theorem rational_family_identities (s : K) (hs : s ≠ 0) (hm : s ≠ -2)
    (a b c : Fin 9) : coefficient s a b c = target a b c := by
  fin_cases a
  · exact masked_identities_row0 s hs hm b c
  · exact masked_identities_row1 s hs hm b c
  · exact masked_identities_row2 s hs hm b c
  · exact masked_identities_row3 s hs hm b c
  · exact masked_identities_row4 s hs hm b c
  · exact masked_identities_row5 s hs hm b c
  · exact masked_identities_row6 s hs hm b c
  · exact masked_identities_row7 s hs hm b c
  · exact masked_identities_row8 s hs hm b c

#print axioms rational_family_identities
#print axioms rational_family_support_le
#check @rational_family_identities
#check @rational_family_support_le
end OpenMathReview.Support138Family
