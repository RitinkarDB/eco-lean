import EcoLean.DebreauRepresentation.OrderGapAdjustmentTransfer
import EcoLean.DebreauRepresentation.BoundPreservingGapAdjustment
import EcoLean.DebreauRepresentation.OpenGapOrderVersion

/-!
# Transfer of the bounded order-version open gap lemma to restricted utilities
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
If the pulled-back embedding lands in the arctan interval, then the image of
the pulled-back restricted utility is bounded above.
-/
theorem restrictedUtilityImage_bddAbove_pullbackRestrictedUtility
    {D : Set α}
    (u : Utility.UtilityFunction D)
    (g : restrictedUtilityImage u → ℝ)
    (hg : MapsIntoArctanIntervalOn g) :
    BddAbove (restrictedUtilityImage (pullbackRestrictedUtility u g)) := by
  refine ⟨Real.pi / 2, ?_⟩
  intro r hr
  rcases hr with ⟨d, rfl⟩
  exact le_of_lt (hg ⟨u d, ⟨d, rfl⟩⟩).2

/--
If the pulled-back embedding lands in the arctan interval, then the image of
the pulled-back restricted utility is bounded below.
-/
theorem restrictedUtilityImage_bddBelow_pullbackRestrictedUtility
    {D : Set α}
    (u : Utility.UtilityFunction D)
    (g : restrictedUtilityImage u → ℝ)
    (hg : MapsIntoArctanIntervalOn g) :
    BddBelow (restrictedUtilityImage (pullbackRestrictedUtility u g)) := by
  refine ⟨-(Real.pi / 2), ?_⟩
  intro r hr
  rcases hr with ⟨d, rfl⟩
  exact le_of_lt (hg ⟨u d, ⟨d, rfl⟩⟩).1

/--
If the order-version open gap lemma holds, then every countable restricted
utility admits a bound-preserving gap-adjusted replacement.
-/
theorem boundPreservingGapAdjustmentExists_of_countable_restrictedUtility
    {D : Set α}
    [Countable D]
    (u : Utility.UtilityFunction D)
    (hOrder : CountableOpenGapLemmaOnOrders) :
    BoundPreservingGapAdjustmentExists u := by
  classical
  letI : Countable ↥(restrictedUtilityImage u) := by
    simpa using
      (Set.Countable.to_subtype (restrictedUtilityImage_countable u))
  have hEmb : BoundedOpenGapEmbedding ↥(restrictedUtilityImage u) := by
    simpa using (hOrder ↥(restrictedUtilityImage u))
  rcases hEmb with ⟨g, hgmono, hgint, hggap⟩
  let u' : Utility.UtilityFunction D := pullbackRestrictedUtility u g
  refine ⟨u', ?_, ?_, ?_, ?_⟩
  · exact sameOrder_pullbackRestrictedUtility u g hgmono
  · simpa [IsGapAdjustedRestrictedUtility, u', restrictedUtilityImage_pullbackRestrictedUtility] using hggap
  · exact restrictedUtilityImage_bddAbove_pullbackRestrictedUtility u g hgint
  · exact restrictedUtilityImage_bddBelow_pullbackRestrictedUtility u g hgint

end Preference
end EcoLean
