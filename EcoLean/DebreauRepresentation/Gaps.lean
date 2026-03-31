import EcoLean.DebreauRepresentation.DebreuDense

/-!
# Gaps in a preference order

This file introduces the notion of a gap in a strict preference interval.

A pair `(x, y)` forms a gap if `x ≻ y` but there is no point strictly between
them. This is one of the central order-theoretic notions in Debreu-style
representation arguments.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
`x` and `y` form a gap if `x ≻ y` and there is no point strictly between them.
-/
def Gap (P : Preference α) (x y : α) : Prop :=
  P.StrictPref x y ∧ ∀ z : α, ¬ StrictBetween P x z y

/--
To say that `(x, y)` is a gap means exactly that `x ≻ y` and there is no point
strictly between them.
-/
theorem gap_iff
    (P : Preference α) {x y : α} :
    Gap P x y ↔ P.StrictPref x y ∧ ∀ z : α, ¬ StrictBetween P x z y := by
  rfl

/--
If `(x, y)` is a gap, then in particular `x ≻ y`.
-/
theorem strictPref_of_gap
    (P : Preference α) {x y : α}
    (hGap : Gap P x y) :
    P.StrictPref x y := by
  exact hGap.1

/--
If `(x, y)` is a gap, then no point lies strictly between `x` and `y`.
-/
theorem not_strictBetween_of_gap
    (P : Preference α) {x y z : α}
    (hGap : Gap P x y) :
    ¬ StrictBetween P x z y := by
  exact hGap.2 z

/--
A strict interval is not a gap if it contains a point strictly between its
endpoints.
-/
theorem not_gap_of_exists_strictBetween
    (P : Preference α) {x y : α}
    (hxyz : ∃ z : α, StrictBetween P x z y) :
    ¬ Gap P x y := by
  intro hGap
  rcases hxyz with ⟨z, hz⟩
  exact hGap.2 z hz

/--
If a set `D` is Debreu-dense, then no strict interval can be a gap.

Indeed, every strict interval contains some point of `D`, and hence some point
strictly between its endpoints.
-/
theorem not_gap_of_debreuDense
    (P : Preference α) {D : Set α}
    (hD : DebreuDense P D)
    {x y : α}
    (hxy : P.StrictPref x y) :
    ¬ Gap P x y := by
  intro hGap
  rcases hD hxy with ⟨z, hzD, hxz, hzy⟩
  exact hGap.2 z ⟨hxz, hzy⟩

/--
The whole space is Debreu-dense exactly when every strict interval contains a
point strictly between its endpoints.
-/
theorem debreuDense_univ_iff
    (P : Preference α) :
    DebreuDense P (Set.univ : Set α) ↔
      ∀ ⦃x y : α⦄, P.StrictPref x y → ∃ z : α, StrictBetween P x z y := by
  constructor
  · intro hD x y hxy
    rcases hD hxy with ⟨z, hz, hBetween⟩
    exact ⟨z, hBetween⟩
  · intro h x y hxy
    rcases h hxy with ⟨z, hz⟩
    exact ⟨z, Set.mem_univ z, hz⟩

/--
To have no gaps means that every strict interval contains a point strictly
between its endpoints.
-/
def NoGaps (P : Preference α) : Prop :=
  ∀ ⦃x y : α⦄, P.StrictPref x y → ∃ z : α, StrictBetween P x z y

/--
`P` has no gaps if and only if the whole space is Debreu-dense for `P`.
-/
theorem noGaps_iff_debreuDense_univ
    (P : Preference α) :
    NoGaps P ↔ DebreuDense P (Set.univ : Set α) := by
  simpa [NoGaps] using (debreuDense_univ_iff P).symm

section Topological

variable [TopologicalSpace α]

/--
The set of points strictly between `x` and `y` is empty exactly when there is
no point strictly between `x` and `y`.
-/
theorem setOf_strictBetween_eq_empty_iff
    (P : Preference α) (x y : α) :
    {z : α | StrictBetween P x z y} = ∅ ↔
      ∀ z : α, ¬ StrictBetween P x z y := by
  constructor
  · intro hEmpty z hz
    have : z ∈ ({z : α | StrictBetween P x z y} : Set α) := hz
    simpa [hEmpty] using this
  · intro hNo
    ext z
    simp [hNo z]

/--
A gap can be characterised as a strict preference interval whose set of
intermediate points is empty.
-/
theorem gap_iff_setOf_strictBetween_eq_empty
    (P : Preference α) {x y : α} :
    Gap P x y ↔
      P.StrictPref x y ∧ {z : α | StrictBetween P x z y} = ∅ := by
  constructor
  · intro hGap
    refine ⟨hGap.1, ?_⟩
    exact (setOf_strictBetween_eq_empty_iff P x y).2 hGap.2
  · intro h
    refine ⟨h.1, ?_⟩
    exact (setOf_strictBetween_eq_empty_iff P x y).1 h.2

end Topological

end Preference
end EcoLean
