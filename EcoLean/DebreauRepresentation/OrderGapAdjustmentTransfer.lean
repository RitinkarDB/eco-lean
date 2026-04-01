import EcoLean.DebreauRepresentation.OpenGapOrderVersion
import EcoLean.DebreauRepresentation.OpenGapReduction
import EcoLean.DebreauRepresentation.GapAdjustment

/-!
# Transfer of the order-version open gap lemma to restricted utilities
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
Pull back an embedding of the restricted utility image to a new restricted
utility on the original domain.
-/
def pullbackRestrictedUtility
    {D : Set α}
    (u : Utility.UtilityFunction D)
    (g : restrictedUtilityImage u → ℝ) :
    Utility.UtilityFunction D :=
  fun d => g ⟨u d, ⟨d, rfl⟩⟩

/--
The image of the pulled-back restricted utility is exactly the range of `g`.
-/
theorem restrictedUtilityImage_pullbackRestrictedUtility
    {D : Set α}
    (u : Utility.UtilityFunction D)
    (g : restrictedUtilityImage u → ℝ) :
    restrictedUtilityImage (pullbackRestrictedUtility u g) = Set.range g := by
  ext r
  constructor
  · intro hr
    rcases hr with ⟨d, rfl⟩
    exact ⟨⟨u d, ⟨d, rfl⟩⟩, rfl⟩
  · intro hr
    rcases hr with ⟨x, rfl⟩
    rcases x with ⟨s, hs⟩
    rcases hs with ⟨d, rfl⟩
    exact ⟨d, rfl⟩

/--
Pulling back a strictly increasing embedding preserves the induced weak order
on the restricted domain.
-/
theorem sameOrder_pullbackRestrictedUtility
    {D : Set α}
    (u : Utility.UtilityFunction D)
    (g : restrictedUtilityImage u → ℝ)
    (hg : StrictMono g) :
    SameOrderRestrictedUtility u (pullbackRestrictedUtility u g) := by
  intro x y
  simpa [SameOrderRestrictedUtility, pullbackRestrictedUtility, ge_iff_le] using
    (hg.le_iff_le
      (a := ⟨u y, ⟨y, rfl⟩⟩)
      (b := ⟨u x, ⟨x, rfl⟩⟩)).symm

/--
If the order-version open gap lemma holds, then every countable restricted
utility admits a gap-adjusted replacement.
-/
theorem gapAdjustmentExists_of_countable_restrictedUtility
    {D : Set α}
    [Countable D]
    (u : Utility.UtilityFunction D)
    (hOrder : CountableOpenGapLemmaOnOrders) :
    GapAdjustmentExists u := by
  classical
  letI : Countable ↥(restrictedUtilityImage u) := by
    simpa using
      (Set.Countable.to_subtype (restrictedUtilityImage_countable u))
  have hEmb : BoundedOpenGapEmbedding ↥(restrictedUtilityImage u) := by
    simpa using (hOrder ↥(restrictedUtilityImage u))
  rcases hEmb with ⟨g, hgmono, hgint, hggap⟩
  let u' : Utility.UtilityFunction D := pullbackRestrictedUtility u g
  refine ⟨u', ?_, ?_⟩
  · exact sameOrder_pullbackRestrictedUtility u g hgmono
  · simpa [IsGapAdjustedRestrictedUtility, u', restrictedUtilityImage_pullbackRestrictedUtility] using hggap

end Preference
end EcoLean
