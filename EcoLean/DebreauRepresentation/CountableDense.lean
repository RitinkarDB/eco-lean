import EcoLean.DebreauRepresentation.Gaps

/-!
# Countable Debreu-dense subsets

A countable Debreu-dense subset need not exist in the presence of gaps.
Accordingly, the theorem proved here assumes `NoGaps P`.

Under second countability, we obtain a countable dense subset of the ambient
topological space. If `P` has no gaps, then every strict interval is a nonempty
open set, so the countable dense subset meets every strict interval.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u} [TopologicalSpace α]

/--
If `P` is complete, continuous, and gapless on a second-countable space, then
there exists a countable Debreu-dense subset of the space.
-/
theorem exists_countable_debreuDense_of_noGaps
    [SecondCountableTopology α]
    (P : Preference α)
    (hC : P.Complete)
    (hCont : ContinuousPref P)
    (hNoGaps : NoGaps P) :
    ∃ D : Set α, D.Countable ∧ DebreuDense P D := by
  rcases TopologicalSpace.exists_countable_dense α with ⟨D, hDcount, hDdense⟩
  refine ⟨D, hDcount, ?_⟩
  intro x y hxy
  rcases hNoGaps hxy with ⟨z, hzBetween⟩

  have hopen : IsOpen {w : α | StrictBetween P x w y} :=
    isOpen_setOf_strictBetween P hC hCont x y

  have hnonempty : ({w : α | StrictBetween P x w y} : Set α).Nonempty := by
    exact ⟨z, hzBetween⟩

  have hval : DenseRange (Subtype.val : D → α) :=
    hDdense.denseRange_val

  rcases hval.exists_mem_open hopen hnonempty with ⟨d, hd⟩
  exact ⟨d, d.property, hd⟩

end Preference
end EcoLean
