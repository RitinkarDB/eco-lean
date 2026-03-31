import EcoLean.DebreauRepresentation.GapCompatibleRestriction
import EcoLean.DebreauRepresentation.SeparatedValues
import Mathlib.Tactic.Linarith

/-!
# Gap-compatible middle points and separated values

This file records the consequences of gap-compatible density that are actually
available without further hypotheses.

A gap-compatible dense subset need not provide separated values for every strict
interval. What it does provide is:

- either a point of the subset strictly between the endpoints,
- or a genuine gap.

Separated values can then be extracted once one has two nested points of the
subset inside the interval.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
If `x ≻ y` and `D` is gap-compatible dense, then either `D` contains a point
strictly between `x` and `y`, or `(x, y)` is a gap.
-/
theorem exists_middlePoint_or_gap_of_strictPref
    (P : Preference α)
    (D : Set α)
    (hD : GapCompatibleDense P D)
    {x y : α}
    (hxy : P.StrictPref x y) :
    (∃ z ∈ D, StrictBetween P x z y) ∨ Gap P x y := by
  exact hD hxy

/--
If `x ≻ y` and no point of `D` lies strictly between `x` and `y`, then
`(x, y)` is a gap.
-/
theorem gap_of_not_exists_middlePoint_of_strictPref
    (P : Preference α)
    (D : Set α)
    (hD : GapCompatibleDense P D)
    {x y : α}
    (hxy : P.StrictPref x y)
    (hNot : ¬ ∃ z ∈ D, StrictBetween P x z y) :
    Gap P x y := by
  rcases exists_middlePoint_or_gap_of_strictPref P D hD hxy with hMid | hGap
  · exact False.elim (hNot hMid)
  · exact hGap

/--
If `D` contains two nested points inside the strict interval `x ≻ y`, then one
obtains separated restricted-utility values from `D`.

Concretely, if `x ≻ d ≻ z ≻ y` with `d, z ∈ D`, then `u z` lies in the upper
value set of `y`, `u d` lies in the lower value set of `x`, and `u z < u d`.
-/
theorem exists_separated_values_of_two_step_chain
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    {x y d z : α}
    (hdD : d ∈ D)
    (hzD : z ∈ D)
    (hxd : P.StrictPref x d)
    (hdz : P.StrictPref d z)
    (hzy : P.StrictPref z y) :
    ∃ r s : ℝ,
      r ∈ upperValueSet P D u y ∧
      s ∈ lowerValueSet P D u x ∧
      r < s := by
  let dD : D := ⟨d, hdD⟩
  let zD : D := ⟨z, hzD⟩
  refine ⟨u zD, u dD, ?_, ?_, ?_⟩
  · exact ⟨zD, hzy.1, rfl⟩
  · exact ⟨dD, hxd.1, rfl⟩
  · have hlt : u dD > u zD := by
      exact (strictPref_iff_lt_of_represents_restrict P D u hu).mp hdz
    linarith

/--
A convenient reformulation of the previous theorem using two strict-between
witnesses.

If `d ∈ D` lies strictly between `x` and `z`, and `z ∈ D` lies strictly between
`d` and `y`, then one obtains separated restricted-utility values for the
interval `x ≻ y`.
-/
theorem exists_separated_values_of_two_step_between
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    {x y d z : α}
    (hdD : d ∈ D)
    (hzD : z ∈ D)
    (hxdz : StrictBetween P x d z)
    (hdzy : StrictBetween P d z y) :
    ∃ r s : ℝ,
      r ∈ upperValueSet P D u y ∧
      s ∈ lowerValueSet P D u x ∧
      r < s := by
  exact exists_separated_values_of_two_step_chain
    P D u hu hdD hzD hxdz.1 hdzy.1 hdzy.2

end Preference
end EcoLean
