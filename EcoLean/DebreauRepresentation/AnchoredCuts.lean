import EcoLean.DebreauRepresentation.BoundedAdjustment
import Mathlib.Tactic.Linarith

/-!
# Anchored lower and upper cuts

This file modifies the lower and upper value sets by adjoining fixed endpoints
of the bounded interval `[-π / 2, π / 2]`.

The point is to avoid separate global nonemptiness hypotheses when forming
suprema and infima.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
The anchored lower value set at `x`: the original lower value set together with
the left endpoint `-π / 2`.
-/
def anchoredLowerValueSet
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) (x : α) : Set ℝ :=
  lowerValueSet P D u x ∪ {-(Real.pi / 2)}

/--
The anchored upper value set at `x`: the original upper value set together with
the right endpoint `π / 2`.
-/
def anchoredUpperValueSet
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) (x : α) : Set ℝ :=
  upperValueSet P D u x ∪ {Real.pi / 2}

/--
The anchored lower cut at `x`.
-/
noncomputable def anchoredLowerCut
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) (x : α) : ℝ :=
  sSup (anchoredLowerValueSet P D u x)

/--
The anchored upper cut at `x`.
-/
noncomputable def anchoredUpperCut
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) (x : α) : ℝ :=
  sInf (anchoredUpperValueSet P D u x)

@[simp] theorem mem_anchoredLowerValueSet
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) (x : α) (r : ℝ) :
    r ∈ anchoredLowerValueSet P D u x ↔
      r ∈ lowerValueSet P D u x ∨ r = -(Real.pi / 2) := by
  simp [anchoredLowerValueSet, or_comm]

@[simp] theorem mem_anchoredUpperValueSet
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) (x : α) (r : ℝ) :
    r ∈ anchoredUpperValueSet P D u x ↔
      r ∈ upperValueSet P D u x ∨ r = Real.pi / 2 := by
  simp [anchoredUpperValueSet, or_comm]

/--
The anchored lower value set is always nonempty.
-/
theorem anchoredLowerValueSet_nonempty
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) (x : α) :
    (anchoredLowerValueSet P D u x).Nonempty := by
  refine ⟨-(Real.pi / 2), ?_⟩
  simp [anchoredLowerValueSet]

/--
The anchored upper value set is always nonempty.
-/
theorem anchoredUpperValueSet_nonempty
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) (x : α) :
    (anchoredUpperValueSet P D u x).Nonempty := by
  refine ⟨Real.pi / 2, ?_⟩
  simp [anchoredUpperValueSet]

/--
For the arctan-adjusted restricted utility, every anchored lower value set is
bounded above.
-/
theorem anchoredLowerValueSet_bddAbove_arctanRestricted
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (x : α) :
    BddAbove (anchoredLowerValueSet P D (arctanRestricted u) x) := by
  refine ⟨Real.pi / 2, ?_⟩
  intro r hr
  rcases hr with hr | rfl
  · rcases hr with ⟨d, hd, rfl⟩
    exact le_of_lt (Real.arctan_lt_pi_div_two (u d))
  · have hpi : 0 ≤ Real.pi / 2 := by positivity
    linarith



/--
For the arctan-adjusted restricted utility, every anchored upper value set is
bounded below.
-/
theorem anchoredUpperValueSet_bddBelow_arctanRestricted
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (x : α) :
    BddBelow (anchoredUpperValueSet P D (arctanRestricted u) x) := by
  refine ⟨-(Real.pi / 2), ?_⟩
  intro r hr
  rcases hr with hr | rfl
  · rcases hr with ⟨d, hd, rfl⟩
    exact le_of_lt (Real.neg_pi_div_two_lt_arctan (u d))
  · have hpi : 0 ≤ Real.pi / 2 := by positivity
    linarith
/--
Any element of an anchored lower value set is at most the anchored lower cut,
provided the anchored lower value set is bounded above.
-/
theorem le_anchoredLowerCut_of_mem
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x : α} {s : ℝ}
    (hBdd : BddAbove (anchoredLowerValueSet P D u x))
    (hs : s ∈ anchoredLowerValueSet P D u x) :
    s ≤ anchoredLowerCut P D u x := by
  unfold anchoredLowerCut
  exact le_csSup hBdd hs

/--
The anchored upper cut is at most any element of the anchored upper value set,
provided the anchored upper value set is bounded below.
-/
theorem anchoredUpperCut_le_of_mem
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x : α} {s : ℝ}
    (hBdd : BddBelow (anchoredUpperValueSet P D u x))
    (hs : s ∈ anchoredUpperValueSet P D u x) :
    anchoredUpperCut P D u x ≤ s := by
  unfold anchoredUpperCut
  exact csInf_le hBdd hs

/--
The left endpoint belongs to every anchored lower value set.
-/
theorem leftEndpoint_mem_anchoredLowerValueSet
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (x : α) :
    -(Real.pi / 2) ∈ anchoredLowerValueSet P D u x := by
  simp [anchoredLowerValueSet]

/--
The right endpoint belongs to every anchored upper value set.
-/
theorem rightEndpoint_mem_anchoredUpperValueSet
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (x : α) :
    Real.pi / 2 ∈ anchoredUpperValueSet P D u x := by
  simp [anchoredUpperValueSet]

/--
The left endpoint is below every anchored upper cut for the arctan-adjusted
restricted utility.
-/
theorem leftEndpoint_le_anchoredUpperCut_arctanRestricted
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (x : α) :
    -(Real.pi / 2) ≤ anchoredUpperCut P D (arctanRestricted u) x := by
  unfold anchoredUpperCut
  exact (le_csInf_iff
    (anchoredUpperValueSet_bddBelow_arctanRestricted P D u x)
    (anchoredUpperValueSet_nonempty P D (arctanRestricted u) x)).2 (by
      intro s hs
      rcases hs with hs | rfl
      · rcases hs with ⟨d, hd, rfl⟩
        exact le_of_lt (Real.neg_pi_div_two_lt_arctan (u d))
      · have hpi : 0 ≤ Real.pi / 2 := by positivity
        linarith)

/--
Every anchored lower cut is below the right endpoint for the arctan-adjusted
restricted utility.
-/
theorem anchoredLowerCut_le_rightEndpoint_arctanRestricted
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (x : α) :
    anchoredLowerCut P D (arctanRestricted u) x ≤ Real.pi / 2 := by
  unfold anchoredLowerCut
  apply csSup_le
  · exact anchoredLowerValueSet_nonempty P D (arctanRestricted u) x
  · intro s hs
    rcases hs with hs | rfl
    · rcases hs with ⟨d, hd, rfl⟩
      exact le_of_lt (Real.arctan_lt_pi_div_two (u d))
    · have hpi : 0 ≤ Real.pi / 2 := by positivity
      linarith

      
end Preference
end EcoLean
