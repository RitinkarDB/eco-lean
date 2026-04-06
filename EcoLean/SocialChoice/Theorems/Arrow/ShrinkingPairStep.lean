import EcoLean.SocialChoice.Theorems.Arrow.SingletonCoalitions

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

section ShrinkingPairStep

variable {V : Type u} {A : Type v}
variable [Fintype V] [DecidableEq V]

/--
Pairwise shrinking-step scaffold.

If a finite coalition `S` is decisive for `x` over `y` and `i ∈ S`, then the
intended Arrow argument will show that either `S.erase i` is still decisive for
`x` over `y`, or the singleton coalition `{i}` has decisive power for that pair.

This is the pairwise version of the shrinking dichotomy
-/
theorem erase_or_singleton_decisive
    {F : SocialWelfareFunction V A}
    (S : Finset V)
    {x y : A}
    (hS : Decisive F (↑S : Set V) x y)
    {i : V}
    (hi : i ∈ S) :
    Decisive F (↑(S.erase i) : Set V) x y ∨
      Decisive F ({i} : Set V) x y := by
  sorry

/--
If removing `i` preserves pairwise decisiveness, then there is a proper smaller
finite coalition decisive for that pair.
-/
theorem smaller_of_erase_decisive
    {F : SocialWelfareFunction V A}
    (S : Finset V)
    {x y : A}
    {i : V}
    (hi : i ∈ S)
    (hErase : Decisive F (↑(S.erase i) : Set V) x y) :
    ∃ T : Finset V, T ⊂ S ∧ Decisive F (↑T : Set V) x y := by
  refine ⟨S.erase i, erase_ssubset S hi, hErase⟩

/--
If the singleton set coalition is decisive for a pair, then the corresponding
singleton finset coalition is decisive for that pair.
-/
theorem finset_decisive_singleton_of_set
    {F : SocialWelfareFunction V A}
    {i : V} {x y : A}
    (h : Decisive F ({i} : Set V) x y) :
    Decisive F (↑(singletonCoalition i) : Set V) x y := by
  simpa [coe_singletonCoalition, singletonCoalition] using h

end ShrinkingPairStep

end Arrow

end SocialChoice
end EcoLean
