import EcoLean.SocialChoice.Theorems.Arrow.ShrinkingPairStep

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

section PivotalVoter

variable {V : Type u} {A : Type v}
variable [Fintype V] [DecidableEq V]

/--
If `S` is decisive for `x` over `y`, `i ∈ S`, and `S.erase i` is not decisive
for `x` over `y`, then the singleton coalition `{i}` is decisive for `x` over `y`.

This is just the non-left branch of the pairwise shrinking dichotomy.
-/
theorem singleton_decisive_of_erase_not_decisive
    {F : SocialWelfareFunction V A}
    (S : Finset V)
    {x y : A}
    (hS : Decisive F (↑S : Set V) x y)
    {i : V}
    (hi : i ∈ S)
    (hNotErase : ¬ Decisive F (↑(S.erase i) : Set V) x y) :
    Decisive F ({i} : Set V) x y := by
  rcases erase_or_singleton_decisive S hS hi with hErase | hSingle
  · exfalso
    exact hNotErase hErase
  · exact hSingle

/--
If `S` is universally decisive, `i ∈ S`, and `S.erase i` fails to be decisive
for some distinct pair, then `{i}` is decisive for that pair.
-/
theorem singleton_decisive_of_universal_and_erase_not_decisive
    {F : SocialWelfareFunction V A}
    (S : Finset V)
    (hS : FinsetUniversallyDecisive F S)
    {i : V}
    (hi : i ∈ S)
    {x y : A}
    (hxy : x ≠ y)
    (hNotErase : ¬ Decisive F (↑(S.erase i) : Set V) x y) :
    Decisive F ({i} : Set V) x y := by
  apply singleton_decisive_of_erase_not_decisive S (hS x y hxy) hi hNotErase

end PivotalVoter

end Arrow

end SocialChoice
end EcoLean
