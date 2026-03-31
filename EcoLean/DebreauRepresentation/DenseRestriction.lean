import EcoLean.DebreauRepresentation.CountableDense

/-!
# Restricting a preference to a subset

This file prepares the next stage of the Debreau-style proof by restricting a
preference to a countable Debreu-dense subset.

The main point is that completeness and transitivity pass to the restricted
preference, so the countable representation theorem from Chapter 1 can be
applied on the subtype.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
Restrict a preference on `α` to a subset `D`.
-/
def restrict (P : Preference α) (D : Set α) : Preference D where
  weakPref x y := P.weakPref x.1 y.1

/--
Restriction preserves weak preference exactly as expected.
-/
@[simp] theorem restrict_weakPref_iff
    (P : Preference α) (D : Set α) (x y : D) :
    (restrict P D).weakPref x y ↔ P.weakPref x.1 y.1 := by
  rfl

/--
If `P` is complete, then its restriction to any subset is complete.
-/
theorem complete_restrict
    (P : Preference α)
    (hC : P.Complete)
    (D : Set α) :
    (restrict P D).Complete := by
  intro x y
  rcases hC x.1 y.1 with hxy | hyx
  · exact Or.inl hxy
  · exact Or.inr hyx

/--
If `P` is transitive, then its restriction to any subset is transitive.
-/
theorem transitive_restrict
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α) :
    (restrict P D).Transitive := by
  intro x y z hxy hyz
  exact hT x.1 y.1 z.1 hxy hyz

section Topological

variable [TopologicalSpace α]

/--
The upper contour set of the restricted preference is the preimage of the
ambient upper contour set under the subtype map.
-/
theorem upperContourSet_restrict
    (P : Preference α) (D : Set α) (x : D) :
    upperContourSet (restrict P D) x =
      Subtype.val ⁻¹' upperContourSet P x.1 := by
  ext y
  rfl

/--
The lower contour set of the restricted preference is the preimage of the
ambient lower contour set under the subtype map.
-/
theorem lowerContourSet_restrict
    (P : Preference α) (D : Set α) (x : D) :
    lowerContourSet (restrict P D) x =
      Subtype.val ⁻¹' lowerContourSet P x.1 := by
  ext y
  rfl

/--
Continuity passes to the restriction of a preference to a subset.
-/
theorem continuousPref_restrict
    (P : Preference α)
    (hCont : ContinuousPref P)
    (D : Set α) :
    ContinuousPref (restrict P D) := by
  constructor
  · intro x
    rw [upperContourSet_restrict]
    exact IsClosed.preimage continuous_subtype_val (hCont.1 x.1)
  · intro x
    rw [lowerContourSet_restrict]
    exact IsClosed.preimage continuous_subtype_val (hCont.2 x.1)

end Topological

section CountableDense

variable [TopologicalSpace α] [SecondCountableTopology α]

/--
If `P` is complete, transitive, continuous, and gapless, then there exists a
countable subset `D` together with a utility representation of the restriction
of `P` to `D`.
-/
theorem exists_countable_dense_restriction_with_utility
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (hCont : ContinuousPref P)
    (hNoGaps : NoGaps P) :
    ∃ D : Set α,
      D.Countable ∧
      DebreuDense P D ∧
      ∃ u : Utility.UtilityFunction D, Represents u (restrict P D) := by
  rcases exists_countable_debreuDense_of_noGaps P hC hCont hNoGaps with
    ⟨D, hDcount, hDdense⟩
  letI : Countable D := by
    simpa using hDcount
  letI : Encodable D := Encodable.ofCountable D
  have hC' : (restrict P D).Complete :=
    complete_restrict P hC D
  have hT' : (restrict P D).Transitive :=
    transitive_restrict P hT D
  rcases exists_utility_of_encodable_complete_transitive (restrict P D) hC' hT' with
    ⟨u, hu⟩
  exact ⟨D, hDcount, hDdense, u, hu⟩

end CountableDense

end Preference
end EcoLean
