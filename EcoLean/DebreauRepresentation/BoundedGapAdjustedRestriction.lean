import EcoLean.DebreauRepresentation.GapAdjustedRestriction
import EcoLean.DebreauRepresentation.BoundedAdjustment

/-!
# Bounded gap-adjusted restricted utilities

This file packages the output of the countable restriction step together with
boundedness and gap adjustment.

The key point is that a strictly increasing postcomposition preserves both
representation and boundedness of the restricted utility image.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
If the image of a restricted utility is bounded above, then so is the image of
any strictly increasing postcomposition.
-/
theorem restrictedUtilityImage_bddAbove_postcomposeStrictMono
    {D : Set α}
    (u : Utility.UtilityFunction D)
    {φ : ℝ → ℝ}
    (hφ : StrictMono φ)
    (hAbove : BddAbove (restrictedUtilityImage u)) :
    BddAbove (restrictedUtilityImage (postcomposeRestricted u φ)) := by
  rcases hAbove with ⟨M, hM⟩
  refine ⟨φ M, ?_⟩
  intro r hr
  rcases hr with ⟨d, rfl⟩
  exact hφ.monotone (hM (by exact ⟨d, rfl⟩))

/--
If the image of a restricted utility is bounded below, then so is the image of
any strictly increasing postcomposition.
-/
theorem restrictedUtilityImage_bddBelow_postcomposeStrictMono
    {D : Set α}
    (u : Utility.UtilityFunction D)
    {φ : ℝ → ℝ}
    (hφ : StrictMono φ)
    (hBelow : BddBelow (restrictedUtilityImage u)) :
    BddBelow (restrictedUtilityImage (postcomposeRestricted u φ)) := by
  rcases hBelow with ⟨M, hM⟩
  refine ⟨φ M, ?_⟩
  intro r hr
  rcases hr with ⟨d, rfl⟩
  exact hφ.monotone (hM (by exact ⟨d, rfl⟩))

/--
If every restricted utility admits a gap adjustment, then every complete,
transitive, continuous preference on a second-countable space admits a
countable gap-compatible dense subset together with a bounded, gap-adjusted
restricted utility representation.
-/
theorem exists_countable_gapCompatibleDense_restriction_with_boundedGapAdjustedUtility
    [TopologicalSpace α]
    [SecondCountableTopology α]
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (hCont : ContinuousPref P)
    (hGapAdj :
      ∀ {D : Set α} (u : Utility.UtilityFunction D), GapAdjustmentExists u) :
    ∃ D : Set α,
      D.Countable ∧
      GapCompatibleDense P D ∧
      ∃ u : Utility.UtilityFunction D,
        Represents u (restrict P D) ∧
        IsGapAdjustedRestrictedUtility u ∧
        BddAbove (restrictedUtilityImage u) ∧
        BddBelow (restrictedUtilityImage u) := by
  rcases exists_countable_gapCompatibleDense_restriction_with_boundedUtility
      P hC hT hCont with
    ⟨D, hDcount, hDgap, u, hu, hAbove, hBelow⟩
  rcases hGapAdj u with ⟨φ, hφ, hGap⟩
  refine ⟨D, hDcount, hDgap, postcomposeRestricted u φ, ?_, ?_, ?_, ?_⟩
  · exact represents_postcomposeRestricted_strictMono P u hu hφ
  · exact hGap
  · exact restrictedUtilityImage_bddAbove_postcomposeStrictMono u hφ hAbove
  · exact restrictedUtilityImage_bddBelow_postcomposeStrictMono u hφ hBelow

end Preference
end EcoLean
