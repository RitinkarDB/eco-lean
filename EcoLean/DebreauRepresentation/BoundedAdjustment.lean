import EcoLean.DebreauRepresentation.GapAdjustment
import EcoLean.DebreauRepresentation.CutLemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Bounded postcomposition of a restricted utility

This file postcomposes a restricted utility representation with `Real.arctan`.

Since `Real.arctan` is strictly increasing and has image contained in
`(-(π / 2), π / 2)`, this preserves representation while making the restricted
utility globally bounded.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
The bounded version of a restricted utility, obtained by postcomposing with
`Real.arctan`.
-/
noncomputable def arctanRestricted
    {D : Set α}
    (u : Utility.UtilityFunction D) : Utility.UtilityFunction D :=
  fun d => Real.arctan (u d)

@[simp] theorem arctanRestricted_apply
    {D : Set α}
    (u : Utility.UtilityFunction D) (d : D) :
    arctanRestricted u d = Real.arctan (u d) := by
  rfl

/--
Postcomposing a restricted utility by `Real.arctan` preserves representation.
-/
theorem represents_arctanRestricted
    {D : Set α}
    (P : Preference α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D)) :
    Represents (arctanRestricted u) (restrict P D) := by
  exact represents_postcomposeRestricted_strictMono P u hu Real.arctan_strictMono

/--
The image of the arctan-adjusted restricted utility is bounded above.
-/
theorem restrictedUtilityImage_bddAbove_arctanRestricted
    {D : Set α}
    (u : Utility.UtilityFunction D) :
    BddAbove (restrictedUtilityImage (arctanRestricted u)) := by
  refine ⟨Real.pi / 2, ?_⟩
  intro r hr
  rcases hr with ⟨d, rfl⟩
  exact le_of_lt (Real.arctan_lt_pi_div_two (u d))

/--
The image of the arctan-adjusted restricted utility is bounded below.
-/
theorem restrictedUtilityImage_bddBelow_arctanRestricted
    {D : Set α}
    (u : Utility.UtilityFunction D) :
    BddBelow (restrictedUtilityImage (arctanRestricted u)) := by
  refine ⟨-(Real.pi / 2), ?_⟩
  intro r hr
  rcases hr with ⟨d, rfl⟩
  exact le_of_lt (Real.neg_pi_div_two_lt_arctan (u d))

/--
For the arctan-adjusted restricted utility, every lower value set is bounded
above.
-/
theorem lowerValueSet_bddAbove_arctanRestricted
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (x : α) :
    BddAbove (lowerValueSet P D (arctanRestricted u) x) := by
  refine ⟨Real.pi / 2, ?_⟩
  intro r hr
  rcases hr with ⟨d, hd, rfl⟩
  exact le_of_lt (Real.arctan_lt_pi_div_two (u d))

/--
For the arctan-adjusted restricted utility, every upper value set is bounded
below.
-/
theorem upperValueSet_bddBelow_arctanRestricted
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (x : α) :
    BddBelow (upperValueSet P D (arctanRestricted u) x) := by
  refine ⟨-(Real.pi / 2), ?_⟩
  intro r hr
  rcases hr with ⟨d, hd, rfl⟩
  exact le_of_lt (Real.neg_pi_div_two_lt_arctan (u d))

/--
For the arctan-adjusted restricted utility, the lower cut is at most the upper
cut whenever both value sets are nonempty.
-/
theorem lowerCut_le_upperCut_arctanRestricted
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    {x : α}
    (hLowerNonempty : (lowerValueSet P D (arctanRestricted u) x).Nonempty)
    (hUpperNonempty : (upperValueSet P D (arctanRestricted u) x).Nonempty) :
    lowerCut P D (arctanRestricted u) x ≤ upperCut P D (arctanRestricted u) x := by
  apply lowerCut_le_upperCut
    (P := P) (hT := hT) (D := D) (u := arctanRestricted u)
    (hu := represents_arctanRestricted P u hu)
    (hLowerNonempty := hLowerNonempty)
    (hBdd := upperValueSet_bddBelow_arctanRestricted P D u x)
    (hUpperNonempty := hUpperNonempty)

/--
A packaged version of the countable-dense restriction theorem with a bounded
restricted utility.
-/
theorem exists_countable_dense_restriction_with_boundedUtility
    [TopologicalSpace α]
    [SecondCountableTopology α]
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (hCont : ContinuousPref P)
    (hNoGaps : NoGaps P) :
    ∃ D : Set α,
      D.Countable ∧
      DebreuDense P D ∧
      ∃ u : Utility.UtilityFunction D,
        Represents u (restrict P D) ∧
        BddAbove (restrictedUtilityImage u) ∧
        BddBelow (restrictedUtilityImage u) := by
  rcases exists_countable_dense_restriction_with_utility P hC hT hCont hNoGaps with
    ⟨D, hDcount, hDdense, u, hu⟩
  refine ⟨D, hDcount, hDdense, arctanRestricted u, ?_, ?_, ?_⟩
  · exact represents_arctanRestricted P u hu
  · exact restrictedUtilityImage_bddAbove_arctanRestricted u
  · exact restrictedUtilityImage_bddBelow_arctanRestricted u

end Preference
end EcoLean
