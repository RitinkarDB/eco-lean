import EcoLean.SocialChoice.Theorems.Arrow.FiniteCoalitions
import EcoLean.SocialChoice.Theorems.Arrow.ProfileConstructions
import EcoLean.SocialChoice.Theorems.Arrow.ProfileVariants
import EcoLean.SocialChoice.Theorems.Arrow.SingleVoterVariants
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

section ShrinkingCoalition

variable {V : Type u} {A : Type v}
variable [Fintype V] [DecidableEq V]

/--
A finite coalition with more than one member is nonempty.
-/
theorem nonempty_of_card_gt_one
    (S : Finset V)
    (hS : 1 < S.card) :
    S.Nonempty := by
  exact Finset.card_pos.mp (lt_trans Nat.zero_lt_one hS)

/--
A finite coalition with more than one member contains some voter.
-/
theorem exists_mem_of_card_gt_one
    (S : Finset V)
    (hS : 1 < S.card) :
    ∃ i : V, i ∈ S := by
  rcases nonempty_of_card_gt_one S hS with ⟨i, hi⟩
  exact ⟨i, hi⟩

/--
Erasing a member of a coalition yields a subset of the original coalition.
-/
theorem erase_subset
    (S : Finset V) (i : V) :
    S.erase i ⊆ S := by
  intro j hj
  exact Finset.mem_of_mem_erase hj

/--
If `i ∈ S`, then `S.erase i` is a proper subset of `S`.
-/
theorem erase_ssubset
    (S : Finset V) {i : V}
    (hi : i ∈ S) :
    S.erase i ⊂ S := by
  exact Finset.erase_ssubset hi

/--
If `i ∈ S`, then `S.erase i ≠ S`.
-/
theorem erase_ne_self
    (S : Finset V) {i : V}
    (hi : i ∈ S) :
    S.erase i ≠ S := by
  exact (erase_ssubset S hi).ne

/--
Scaffold for the key shrinking step.

Later we want to prove: if `S` is a universally decisive finite coalition and
has more than one member, then some proper finite subset is universally decisive.
-/
theorem exists_smaller_universallyDecisive
    {F : SocialWelfareFunction V A}
    (S : Finset V)
    (hS : FinsetUniversallyDecisive F S)
    (hcard : 1 < S.card) :
    ∃ T : Finset V, T ⊂ S ∧ FinsetUniversallyDecisive F T := by
  sorry

end ShrinkingCoalition

end Arrow

end SocialChoice
end EcoLean
