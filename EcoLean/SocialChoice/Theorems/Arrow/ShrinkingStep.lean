import EcoLean.SocialChoice.Theorems.Arrow.ShrinkingPairStep

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

section ShrinkingStep

variable {V : Type u} {A : Type v}
variable [Fintype V] [DecidableEq V]

theorem erase_or_singleton_universallyDecisive
    {F : SocialWelfareFunction V A}
    (S : Finset V)
    (hS : FinsetUniversallyDecisive F S)
    {i : V}
    (hi : i ∈ S) :
    FinsetUniversallyDecisive F (S.erase i) ∨
      UniversallyDecisive F ({i} : Set V) := by
  by_cases hErase : FinsetUniversallyDecisive F (S.erase i)
  · exact Or.inl hErase
  · right
    intro x y hxy
    have hSxy : Decisive F (↑S : Set V) x y := by
      exact hS x y hxy
    rcases erase_or_singleton_decisive S hSxy hi with hsmall | hsingle
    · exfalso
      exact hErase (by
        intro a b hab
        exact hsmall)
    · exact hsingle

theorem smaller_of_erase_universallyDecisive
    {F : SocialWelfareFunction V A}
    (S : Finset V)
    {i : V}
    (hi : i ∈ S)
    (hErase : FinsetUniversallyDecisive F (S.erase i)) :
    ∃ T : Finset V, T ⊂ S ∧ FinsetUniversallyDecisive F T := by
  refine ⟨S.erase i, erase_ssubset S hi, hErase⟩

end ShrinkingStep

end Arrow

end SocialChoice
end EcoLean
