import EcoLean.DebreauRepresentation.OpenGapReduction

/-!
# Reduction of the open gap lemma to countable subtypes of `ℝ`

This file reduces the patched countable open gap lemma for arbitrary countable
subsets of `ℝ` to the corresponding statement for countable linear orders
already realised as subtypes of `ℝ`.
-/

universe u

namespace EcoLean
namespace Preference

/--
A subtype-level version of the patched countable open gap lemma.

This is the form one typically proves by working directly with a countable
linearly ordered type already embedded in `ℝ`.
-/
def CountableOpenGapLemmaOnSubtypes : Prop :=
  ∀ (T : Type) [LinearOrder T] [Countable T] (e : T → ℝ),
    StrictMono e →
    DomainGapCompatible e →
    BoundPreservingOpenGapAdjustmentOn (Set.range e)

/--
If the subtype-level patched countable open gap lemma holds, then the set-level
version holds for all countable subsets of `ℝ`.
-/
theorem countableOpenGapLemma_of_subtypeVersion
    (hSub : CountableOpenGapLemmaOnSubtypes) :
    CountableOpenGapLemma := by
  intro S hS hCompat
  let T : Type := ↥S
  haveI : Countable T := by
    simpa [T] using (Set.Countable.to_subtype hS)
  let e : T → ℝ := fun x => x.1
  have he : StrictMono e := by
    intro a b hab
    exact hab
  have hrange : Set.range e = S := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hCompat' : DomainGapCompatible e := by
    intro a b hab hNoMid
    simpa [e, hrange] using hCompat hab hNoMid
  simpa [hrange, e] using hSub T e he hCompat'

end Preference
end EcoLean
