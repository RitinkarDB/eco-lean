import EcoLean.DebreauRepresentation.Gaps
import Mathlib.Topology.Bases

/-!
# Countable gap-compatible dense subsets

This file replaces the stronger `DebreuDense` notion by a version that is
compatible with gaps.

A subset `D` is gap-compatible dense if every strict interval either contains a
point of `D` or is itself a gap.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
A subset `D` is gap-compatible dense for `P` if every strict preference interval
either contains some point of `D` strictly between its endpoints or is a gap.
-/
def GapCompatibleDense (P : Preference α) (D : Set α) : Prop :=
  ∀ ⦃x y : α⦄, P.StrictPref x y →
    (∃ z ∈ D, StrictBetween P x z y) ∨ Gap P x y

/--
If `D` is gap-compatible dense and `x ≻ y`, then either there is a point of `D`
strictly between `x` and `y`, or `(x, y)` is a gap.
-/
theorem gapCompatibleDense_iff
    (P : Preference α) {D : Set α} :
    GapCompatibleDense P D ↔
      ∀ ⦃x y : α⦄, P.StrictPref x y →
        (∃ z ∈ D, StrictBetween P x z y) ∨ Gap P x y := by
  rfl

section Topological

variable [TopologicalSpace α]

/--
Any dense subset is gap-compatible dense for a complete continuous preference.

Indeed, if a strict interval is not a gap, then the set of points strictly
between the endpoints is a nonempty open set, so a dense subset must meet it.
-/
theorem gapCompatibleDense_of_dense
    (P : Preference α)
    (hC : P.Complete)
    (hCont : ContinuousPref P)
    {D : Set α}
    (hDense : Dense D) :
    GapCompatibleDense P D := by
  intro x y hxy
  by_cases hGap : Gap P x y
  · exact Or.inr hGap
  · left
    have hopen : IsOpen {z : α | StrictBetween P x z y} :=
      isOpen_setOf_strictBetween P hC hCont x y
    have hnonempty : ({z : α | StrictBetween P x z y} : Set α).Nonempty := by
      by_contra hEmpty
      apply hGap
      refine ⟨hxy, ?_⟩
      intro z hz
      exact hEmpty ⟨z, hz⟩
    have hval : DenseRange (Subtype.val : D → α) :=
      hDense.denseRange_val
    rcases hval.exists_mem_open hopen hnonempty with ⟨d, hd⟩
    exact ⟨d, d.property, hd⟩

end Topological

section SecondCountable

variable [TopologicalSpace α] [SecondCountableTopology α]

/--
On a second-countable space, a complete continuous preference admits a countable
gap-compatible dense subset.
-/
theorem exists_countable_gapCompatibleDense
    (P : Preference α)
    (hC : P.Complete)
    (hCont : ContinuousPref P) :
    ∃ D : Set α, D.Countable ∧ GapCompatibleDense P D := by
  rcases TopologicalSpace.exists_countable_dense α with ⟨D, hDcount, hDdense⟩
  refine ⟨D, hDcount, ?_⟩
  exact gapCompatibleDense_of_dense P hC hCont hDdense

end SecondCountable

end Preference
end EcoLean
