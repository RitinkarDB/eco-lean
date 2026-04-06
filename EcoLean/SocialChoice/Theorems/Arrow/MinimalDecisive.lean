import EcoLean.SocialChoice.Theorems.Arrow.DecisiveTransfer

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

/--
A coalition `S` is minimally universally decisive if it is universally decisive,
and no proper subset of `S` is universally decisive.
-/
def MinimallyUniversallyDecisive
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) (S : Set V) : Prop :=
  UniversallyDecisive F S ∧
    ∀ T : Set V, T ⊆ S → T ≠ S → ¬ UniversallyDecisive F T

namespace MinimallyUniversallyDecisive

variable {V : Type u} {A : Type v}
variable {F : SocialWelfareFunction V A} {S T : Set V}

theorem universallyDecisive
    (h : MinimallyUniversallyDecisive F S) :
    UniversallyDecisive F S :=
  h.1

theorem decisive
    (h : MinimallyUniversallyDecisive F S)
    {x y : A} (hxy : x ≠ y) :
    Decisive F S x y := by
  exact h.1 x y hxy

theorem not_universallyDecisive_of_subset_ne
    (h : MinimallyUniversallyDecisive F S)
    (hTS : T ⊆ S)
    (hne : T ≠ S) :
    ¬ UniversallyDecisive F T :=
  h.2 T hTS hne

end MinimallyUniversallyDecisive

end Arrow

end SocialChoice
end EcoLean
