import EcoLean.DebreauRepresentation.DenseRestriction

/-!
# Lower and upper cuts from a dense restricted utility

This file introduces the lower and upper sections of a point relative to a
subset `D`, together with the corresponding sets of utility values.

These are the basic objects used in the extension step of a Debreau-style
representation proof.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
The points of `D` that are weakly below `x`.
-/
def lowerSectionIn (P : Preference α) (D : Set α) (x : α) : Set D :=
  {d | P.weakPref x d.1}

/--
The points of `D` that are weakly above `x`.
-/
def upperSectionIn (P : Preference α) (D : Set α) (x : α) : Set D :=
  {d | P.weakPref d.1 x}

/--
The utility values attained on points of `D` weakly below `x`.
-/
def lowerValueSet
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) (x : α) : Set ℝ :=
  u '' lowerSectionIn P D x

/--
The utility values attained on points of `D` weakly above `x`.
-/
def upperValueSet
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) (x : α) : Set ℝ :=
  u '' upperSectionIn P D x

@[simp] theorem mem_lowerSectionIn
    (P : Preference α) (D : Set α) (x : α) (d : D) :
    d ∈ lowerSectionIn P D x ↔ P.weakPref x d.1 := by
  rfl

@[simp] theorem mem_upperSectionIn
    (P : Preference α) (D : Set α) (x : α) (d : D) :
    d ∈ upperSectionIn P D x ↔ P.weakPref d.1 x := by
  rfl

@[simp] theorem mem_lowerValueSet
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) (x : α) (r : ℝ) :
    r ∈ lowerValueSet P D u x ↔
      ∃ d : D, P.weakPref x d.1 ∧ u d = r := by
  constructor
  · intro hr
    rcases hr with ⟨d, hd, rfl⟩
    exact ⟨d, hd, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d, hd, rfl⟩

@[simp] theorem mem_upperValueSet
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) (x : α) (r : ℝ) :
    r ∈ upperValueSet P D u x ↔
      ∃ d : D, P.weakPref d.1 x ∧ u d = r := by
  constructor
  · intro hr
    rcases hr with ⟨d, hd, rfl⟩
    exact ⟨d, hd, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d, hd, rfl⟩

/--
If `x ≽ y`, then the lower section of `y` inside `D` is contained in the lower
section of `x`.
-/
theorem lowerSectionIn_mono_of_weakPref
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    {x y : α}
    (hxy : P.weakPref x y) :
    lowerSectionIn P D y ⊆ lowerSectionIn P D x := by
  intro d hd
  exact hT x y d.1 hxy hd

/--
If `x ≽ y`, then the upper section of `x` inside `D` is contained in the upper
section of `y`.
-/
theorem upperSectionIn_mono_of_weakPref
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    {x y : α}
    (hxy : P.weakPref x y) :
    upperSectionIn P D x ⊆ upperSectionIn P D y := by
  intro d hd
  exact hT d.1 x y hd hxy

/--
If `x ≽ y`, then the lower value set of `y` is contained in the lower value set
of `x`.
-/
theorem lowerValueSet_mono_of_weakPref
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x y : α}
    (hxy : P.weakPref x y) :
    lowerValueSet P D u y ⊆ lowerValueSet P D u x := by
  intro r hr
  rcases hr with ⟨d, hd, rfl⟩
  exact ⟨d, lowerSectionIn_mono_of_weakPref P hT D hxy hd, rfl⟩

/--
If `x ≽ y`, then the upper value set of `x` is contained in the upper value set
of `y`.
-/
theorem upperValueSet_mono_of_weakPref
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x y : α}
    (hxy : P.weakPref x y) :
    upperValueSet P D u x ⊆ upperValueSet P D u y := by
  intro r hr
  rcases hr with ⟨d, hd, rfl⟩
  exact ⟨d, upperSectionIn_mono_of_weakPref P hT D hxy hd, rfl⟩

/--
Any lower-section utility value is bounded above by any upper-section utility
value, provided `u` represents the restriction of `P` to `D`.
-/
theorem lowerValue_le_upperValue
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    {x : α} {r s : ℝ}
    (hr : r ∈ lowerValueSet P D u x)
    (hs : s ∈ upperValueSet P D u x) :
    r ≤ s := by
  rcases hr with ⟨dl, hdl, rfl⟩
  rcases hs with ⟨du, hdu, rfl⟩
  have hPref : P.weakPref du.1 dl.1 := by
    exact hT du.1 x dl.1 hdu hdl
  have hRep : u du ≥ u dl := by
    exact (hu du dl).mp hPref
  simpa [ge_iff_le] using hRep

section Complete

/--
If `P` is complete, then for any `d ∈ D`, the utility value `u d` belongs to
the lower value set of `d`.
-/
theorem self_mem_lowerValueSet
    (P : Preference α)
    (hC : P.Complete)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (d : D) :
    u d ∈ lowerValueSet P D u d.1 := by
  refine ⟨d, ?_, rfl⟩
  exact weakPref_refl_of_complete P hC d.1

/--
If `P` is complete, then for any `d ∈ D`, the utility value `u d` belongs to
the upper value set of `d`.
-/
theorem self_mem_upperValueSet
    (P : Preference α)
    (hC : P.Complete)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (d : D) :
    u d ∈ upperValueSet P D u d.1 := by
  refine ⟨d, ?_, rfl⟩
  exact weakPref_refl_of_complete P hC d.1

end Complete

/--
The lower cut generated by `u` and `D` at the point `x`.
-/
noncomputable def lowerCut
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) (x : α) : ℝ :=
  sSup (lowerValueSet P D u x)

/--
The upper cut generated by `u` and `D` at the point `x`.
-/
noncomputable def upperCut
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) (x : α) : ℝ :=
  sInf (upperValueSet P D u x)

end Preference
end EcoLean
