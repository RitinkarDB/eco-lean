import EcoLean.DebreauRepresentation.StrictSections
import Mathlib.Topology.Bases

/-!
# Countable-basis lemmas for strict contour sections

This file packages the basic second-countability tools that will be used in the
Debreau-style utility construction.

Once strict contour sections are known to be open, second countability lets us
write them as countable unions of basis elements.

The natural output of the mathlib basis theorem is an indexed union
`⋃ a ∈ s, a`. Since later constructions sometimes prefer `⋃₀ S`, we also
provide small corollaries converting to that form.
-/

universe u

namespace EcoLean
namespace Preference

open TopologicalSpace

variable {α : Type u} [TopologicalSpace α]

/--
In a second-countable space, any topological basis contains a countable
subfamily which is still a topological basis.
-/
theorem exists_countable_isTopologicalBasis_subset
    [SecondCountableTopology α]
    {B : Set (Set α)}
    (hB : IsTopologicalBasis B) :
    ∃ B₀ ⊆ B, B₀.Countable ∧ IsTopologicalBasis B₀ := by
  simpa using hB.exists_countable

/--
A double union over a family of sets is the same as the `sUnion` of that family.
-/
theorem biUnion_eq_sUnion {S : Set (Set α)} :
    (⋃ a ∈ S, a : Set α) = ⋃₀ S := by
  ext x
  simp

/--
If `B` is a topological basis on a second-countable space, then each strict
upper contour section is a countable union of basis elements from `B`.

This is the natural shape returned by
`IsTopologicalBasis.exists_countable_biUnion_of_isOpen`.
-/
theorem strictUpperContourSet_eq_iUnion_countable_of_isTopologicalBasis
    [SecondCountableTopology α]
    {B : Set (Set α)}
    (hB : IsTopologicalBasis B)
    (P : Preference α)
    (hC : P.Complete)
    (hCont : ContinuousPref P)
    (x : α) :
    ∃ s ⊆ B, s.Countable ∧
      strictUpperContourSet P x = ⋃ a ∈ s, a := by
  have hopen : IsOpen (strictUpperContourSet P x) :=
    isOpen_strictUpperContourSet P hC hCont x
  exact hB.exists_countable_biUnion_of_isOpen hopen

/--
If `B` is a topological basis on a second-countable space, then each strict
lower contour section is a countable union of basis elements from `B`.

This is the natural shape returned by
`IsTopologicalBasis.exists_countable_biUnion_of_isOpen`.
-/
theorem strictLowerContourSet_eq_iUnion_countable_of_isTopologicalBasis
    [SecondCountableTopology α]
    {B : Set (Set α)}
    (hB : IsTopologicalBasis B)
    (P : Preference α)
    (hC : P.Complete)
    (hCont : ContinuousPref P)
    (x : α) :
    ∃ s ⊆ B, s.Countable ∧
      strictLowerContourSet P x = ⋃ a ∈ s, a := by
  have hopen : IsOpen (strictLowerContourSet P x) :=
    isOpen_strictLowerContourSet P hC hCont x
  exact hB.exists_countable_biUnion_of_isOpen hopen

/--
A `sUnion` version of the countable-basis decomposition for strict upper
contour sections.
-/
theorem strictUpperContourSet_eq_sUnion_countable_of_isTopologicalBasis
    [SecondCountableTopology α]
    {B : Set (Set α)}
    (hB : IsTopologicalBasis B)
    (P : Preference α)
    (hC : P.Complete)
    (hCont : ContinuousPref P)
    (x : α) :
    ∃ S : Set (Set α), S ⊆ B ∧ S.Countable ∧
      strictUpperContourSet P x = ⋃₀ S := by
  rcases strictUpperContourSet_eq_iUnion_countable_of_isTopologicalBasis
      hB P hC hCont x with ⟨S, hSB, hSc, hEq⟩
  refine ⟨S, hSB, hSc, ?_⟩
  rw [hEq, biUnion_eq_sUnion]

/--
A `sUnion` version of the countable-basis decomposition for strict lower
contour sections.
-/
theorem strictLowerContourSet_eq_sUnion_countable_of_isTopologicalBasis
    [SecondCountableTopology α]
    {B : Set (Set α)}
    (hB : IsTopologicalBasis B)
    (P : Preference α)
    (hC : P.Complete)
    (hCont : ContinuousPref P)
    (x : α) :
    ∃ S : Set (Set α), S ⊆ B ∧ S.Countable ∧
      strictLowerContourSet P x = ⋃₀ S := by
  rcases strictLowerContourSet_eq_iUnion_countable_of_isTopologicalBasis
      hB P hC hCont x with ⟨S, hSB, hSc, hEq⟩
  refine ⟨S, hSB, hSc, ?_⟩
  rw [hEq, biUnion_eq_sUnion]

end Preference
end EcoLean
