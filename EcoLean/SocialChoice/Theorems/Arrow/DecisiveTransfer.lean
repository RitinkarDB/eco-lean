import EcoLean.SocialChoice.Theorems.Arrow.DecisiveFacts
import EcoLean.SocialChoice.Theorems.Arrow.ProfileConstructions
import EcoLean.SocialChoice.Theorems.Arrow.ProfileVariants

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

section DecisiveTransfer

variable {V : Type u} {A : Type v}

/--
If a coalition is universally decisive, then it is decisive for any given
distinct ordered pair.
-/
theorem decisive_of_universallyDecisive
    {F : SocialWelfareFunction V A}
    {S : Set V}
    (hS : UniversallyDecisive F S)
    {x y : A}
    (hxy : x ≠ y) :
    Decisive F S x y := by
  exact hS x y hxy

end DecisiveTransfer

end Arrow

end SocialChoice
end EcoLean
