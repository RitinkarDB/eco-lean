import EcoLean.DebreauRepresentation.OpenGapLemmaSubtypeReduction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Set.Countable
import Mathlib.Order.Monotone.Basic

/-!
# Open gap lemma

This file is intended to prove the patched countable open gap lemma in subtype
form, and then recover the set-level version by reduction.
-/

universe u

namespace EcoLean
namespace Preference

/--
`Real.arctan` lands inside the arctan interval.
-/
theorem mapsIntoArctanInterval_arctan :
    MapsIntoArctanInterval Real.arctan := by
  intro r
  constructor
  · exact Real.neg_pi_div_two_lt_arctan r
  · exact Real.arctan_lt_pi_div_two r

/--
Set-level patched countable open gap lemma, once the subtype-level version is
proved.
-/
theorem countableOpenGapLemma
    (hSub : CountableOpenGapLemmaOnSubtypes) :
    CountableOpenGapLemma := by
  exact countableOpenGapLemma_of_subtypeVersion hSub

/--
Target theorem: the patched countable open gap lemma for countable linear
orders already realised as subtypes of `ℝ`.
-/
theorem countableOpenGapLemmaOnSubtypes_proof :
    CountableOpenGapLemmaOnSubtypes := by
  intro T _ _ e he hCompat
  -- real proof starts here
  sorry

end Preference
end EcoLean
