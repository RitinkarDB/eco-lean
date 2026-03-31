import EcoLean.DebreauRepresentation.CountableBase

/-!
# Debreu-dense subsets

The classical proof of Debreu's second-countable representation theorem proceeds
through countable order-dense sets and the analysis of gaps, rather than through
a direct weighted sum over basis elements.

This file introduces the basic order-theoretic notions that will later feed into
the construction of a continuous utility representation.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
`z` lies strictly between `x` and `y` if `x ≻ z` and `z ≻ y`.

This is the order-theoretic notion of a point that separates `x` from `y`
inside a strict preference interval.
-/
def StrictBetween (P : Preference α) (x z y : α) : Prop :=
  P.StrictPref x z ∧ P.StrictPref z y

/--
A subset `D` is Debreu-dense for `P` if every strict preference interval
contains some element of `D`.
-/
def DebreuDense (P : Preference α) (D : Set α) : Prop :=
  ∀ ⦃x y : α⦄, P.StrictPref x y → ∃ z ∈ D, StrictBetween P x z y

/--
To say that `z` lies strictly between `x` and `y` means exactly that
`x ≻ z` and `z ≻ y`.
-/
theorem strictBetween_iff
    (P : Preference α) {x z y : α} :
    StrictBetween P x z y ↔ P.StrictPref x z ∧ P.StrictPref z y := by
  rfl

/--
If `D` is Debreu-dense, then every strict interval contains a point of `D`.
-/
theorem exists_mem_of_debreuDense
    (P : Preference α) {D : Set α}
    (hD : DebreuDense P D)
    {x y : α}
    (hxy : P.StrictPref x y) :
    ∃ z ∈ D, P.StrictPref x z ∧ P.StrictPref z y := by
  simpa [DebreuDense, StrictBetween] using hD hxy

/--
Membership in a Debreu-dense set gives a point strictly between the endpoints
of any strict preference interval witnessing density.
-/
theorem strictBetween_of_mem_debreuDense
    (P : Preference α) {D : Set α}
    (hD : DebreuDense P D)
    {x y : α}
    (hxy : P.StrictPref x y) :
    ∃ z, z ∈ D ∧ P.StrictPref x z ∧ P.StrictPref z y := by
  rcases exists_mem_of_debreuDense P hD hxy with ⟨z, hzD, hxz, hzy⟩
  exact ⟨z, hzD, hxz, hzy⟩

section Topological

variable [TopologicalSpace α]

/--
If `P` is complete and continuous, then every strict upper contour set is open.

This is re-exported here because strict intervals will later be built by
intersecting strict contour sections with basis elements.
-/
theorem isOpen_strictUpperContourSet'
    (P : Preference α)
    (hC : P.Complete)
    (hCont : ContinuousPref P)
    (x : α) :
    IsOpen (strictUpperContourSet P x) :=
  isOpen_strictUpperContourSet P hC hCont x

/--
If `P` is complete and continuous, then every strict lower contour set is open.
-/
theorem isOpen_strictLowerContourSet'
    (P : Preference α)
    (hC : P.Complete)
    (hCont : ContinuousPref P)
    (x : α) :
    IsOpen (strictLowerContourSet P x) :=
  isOpen_strictLowerContourSet P hC hCont x

/--
For fixed `x` and `y`, the set of points strictly between `x` and `y` is open
whenever `P` is complete and continuous.
-/
theorem isOpen_setOf_strictBetween
    (P : Preference α)
    (hC : P.Complete)
    (hCont : ContinuousPref P)
    (x y : α) :
    IsOpen {z : α | StrictBetween P x z y} := by
  have hUpper : IsOpen (strictLowerContourSet P x) :=
    isOpen_strictLowerContourSet P hC hCont x
  have hLower : IsOpen (strictUpperContourSet P y) :=
    isOpen_strictUpperContourSet P hC hCont y
  have hEq :
      {z : α | StrictBetween P x z y} =
        strictLowerContourSet P x ∩ strictUpperContourSet P y := by
    ext z
    simp [StrictBetween, strictLowerContourSet, strictUpperContourSet]
  rw [hEq]
  exact hUpper.inter hLower

end Topological

end Preference
end EcoLean
