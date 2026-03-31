import EcoLean.DebreauRepresentation.BoundedAdjustment
import EcoLean.DebreauRepresentation.MidpointOrder

/-!
# Boundedness lemmas for lower and upper value sets

This file shows that once the restricted utility image is bounded above and
below, the associated lower and upper value sets inherit the corresponding
boundedness properties.

It also packages the bounded countable-dense restriction together with the
midpoint candidate on the whole space.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
Every lower value set is contained in the image of the restricted utility.
-/
theorem lowerValueSet_subset_restrictedUtilityImage
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (x : α) :
    lowerValueSet P D u x ⊆ restrictedUtilityImage u := by
  intro r hr
  rcases hr with ⟨d, hd, rfl⟩
  exact ⟨d, rfl⟩

/--
Every upper value set is contained in the image of the restricted utility.
-/
theorem upperValueSet_subset_restrictedUtilityImage
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (x : α) :
    upperValueSet P D u x ⊆ restrictedUtilityImage u := by
  intro r hr
  rcases hr with ⟨d, hd, rfl⟩
  exact ⟨d, rfl⟩

/--
If the image of the restricted utility is bounded above, then every lower value
set is bounded above.
-/
theorem lowerValueSet_bddAbove_of_image_bddAbove
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (x : α)
    (hBdd : BddAbove (restrictedUtilityImage u)) :
    BddAbove (lowerValueSet P D u x) := by
  rcases hBdd with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro r hr
  exact hM (lowerValueSet_subset_restrictedUtilityImage P D u x hr)

/--
If the image of the restricted utility is bounded below, then every upper value
set is bounded below.
-/
theorem upperValueSet_bddBelow_of_image_bddBelow
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (x : α)
    (hBdd : BddBelow (restrictedUtilityImage u)) :
    BddBelow (upperValueSet P D u x) := by
  rcases hBdd with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro r hr
  exact hM (upperValueSet_subset_restrictedUtilityImage P D u x hr)

/--
If the restricted utility image is bounded above and below, then the lower cut
is at most the upper cut whenever the corresponding value sets are nonempty.
-/
theorem lowerCut_le_upperCut_of_image_bdd
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    {x : α}
    (hAbove : BddAbove (restrictedUtilityImage u))
    (hBelow : BddBelow (restrictedUtilityImage u))
    (hLowerNonempty : (lowerValueSet P D u x).Nonempty)
    (hUpperNonempty : (upperValueSet P D u x).Nonempty) :
    lowerCut P D u x ≤ upperCut P D u x := by
  exact lowerCut_le_upperCut P hT D u hu
    hLowerNonempty
    (upperValueSet_bddBelow_of_image_bddBelow P D u x hBelow)
    hUpperNonempty

section Topological

variable [TopologicalSpace α] [SecondCountableTopology α]

/--
There exists a countable Debreu-dense subset together with a bounded restricted
utility representation whose lower and upper value sets are bounded at every
point, and whose midpoint candidate agrees with the restricted utility on the
dense subset.
-/
theorem exists_countable_dense_restriction_with_boundedCuts
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
        BddBelow (restrictedUtilityImage u) ∧
        (∀ x : α, BddAbove (lowerValueSet P D u x)) ∧
        (∀ x : α, BddBelow (upperValueSet P D u x)) ∧
        (∀ d : D, midpointUtility P D u d.1 = u d) := by
  rcases exists_countable_dense_restriction_with_boundedUtility P hC hT hCont hNoGaps with
    ⟨D, hDcount, hDdense, u, hu, hAbove, hBelow⟩
  refine ⟨D, hDcount, hDdense, u, hu, hAbove, hBelow, ?_, ?_, ?_⟩
  · intro x
    exact lowerValueSet_bddAbove_of_image_bddAbove P D u x hAbove
  · intro x
    exact upperValueSet_bddBelow_of_image_bddBelow P D u x hBelow
  · intro d
    exact midpointUtility_eq_on_dense P hC hT D u hu d

end Topological

end Preference
end EcoLean
