import EcoLean.SocialChoice.Theorems.Arrow.ShrinkingPairStep
import EcoLean.SocialChoice.Theorems.Arrow.SingletonTransfer
import EcoLean.SocialChoice.Properties.CollectiveRationality
import EcoLean.SocialChoice.Properties.Pareto
import EcoLean.SocialChoice.Properties.IIA

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

section ShrinkingStep

variable {V : Type u} {A : Type v}
variable [Fintype V] [DecidableEq V]

/--
If `S.erase i` is not universally decisive, then some pair witnesses that failure.
-/
theorem exists_pair_not_decisive_of_not_universallyDecisive
    {F : SocialWelfareFunction V A}
    (S : Finset V)
    {i : V}
    (hNot : ¬ FinsetUniversallyDecisive F (S.erase i)) :
    ∃ x y : A, x ≠ y ∧ ¬ Decisive F (↑(S.erase i) : Set V) x y := by
  classical
  by_contra hNoWitness
  apply hNot
  intro x y hxy
  by_contra hNotDec
  apply hNoWitness
  exact ⟨x, y, hxy, hNotDec⟩

/--
If `S` is universally decisive and `S.erase i` is not, then `{i}` is universally decisive.
-/
theorem singleton_universallyDecisive_of_erase_not_universallyDecisive
    {F : SocialWelfareFunction V A}
    (hRat : RationalSWF F)
    (hPareto : WeakPareto F)
    (hIIA : IIA F)
    (S : Finset V)
    (hS : FinsetUniversallyDecisive F S)
    {i : V}
    (hi : i ∈ S)
    (hNotErase : ¬ FinsetUniversallyDecisive F (S.erase i)) :
    UniversallyDecisive F ({i} : Set V) := by
  rcases exists_pair_not_decisive_of_not_universallyDecisive (S := S) (i := i) hNotErase with
    ⟨x, y, hxy, hNotDec⟩
  have hSinglePair : Decisive F ({i} : Set V) x y := by
    apply singleton_decisive_of_universal_and_erase_not_decisive S hS hi hxy hNotDec
  exact singleton_universallyDecisive_of_pair hRat hPareto hIIA hxy hSinglePair

/--
Main shrinking dichotomy, once the singleton-transfer lemma is available.
-/
theorem erase_or_singleton_universallyDecisive
    {F : SocialWelfareFunction V A}
    (hRat : RationalSWF F)
    (hPareto : WeakPareto F)
    (hIIA : IIA F)
    (S : Finset V)
    (hS : FinsetUniversallyDecisive F S)
    {i : V}
    (hi : i ∈ S) :
    FinsetUniversallyDecisive F (S.erase i) ∨
      UniversallyDecisive F ({i} : Set V) := by
  by_cases hErase : FinsetUniversallyDecisive F (S.erase i)
  · exact Or.inl hErase
  · exact Or.inr <|
      singleton_universallyDecisive_of_erase_not_universallyDecisive
        hRat hPareto hIIA S hS hi hErase

/--
If removing `i` preserves universal decisiveness, then there is a proper smaller
finite universally decisive coalition.
-/
theorem smaller_of_erase_universallyDecisive
    {F : SocialWelfareFunction V A}
    (S : Finset V)
    {i : V}
    (hi : i ∈ S)
    (hErase : FinsetUniversallyDecisive F (S.erase i)) :
    ∃ T : Finset V, T ⊂ S ∧ FinsetUniversallyDecisive F T := by
  refine ⟨S.erase i, Finset.erase_ssubset hi, hErase⟩

end ShrinkingStep

end Arrow

end SocialChoice
end EcoLean
