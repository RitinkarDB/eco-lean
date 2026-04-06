import EcoLean.SocialChoice.Theorems.Arrow.PivotalVoter
import EcoLean.SocialChoice.Properties.Pareto
import EcoLean.SocialChoice.Properties.IIA

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

section SingletonTransfer

variable {V : Type u} {A : Type v}
variable [Fintype V] [DecidableEq V]

/--
If `{i}` is decisive for `x ≻ y`, then it is also decisive for `x ≻ z`.

This is a standard Arrow transfer step using IIA and profile constructions.
-/
theorem singleton_transfer_left
    {F : SocialWelfareFunction V A}
    (hPareto : WeakPareto F)
    (hIIA : IIA F)
    {i : V}
    {x y z : A}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hSingle : Decisive F ({i} : Set V) x y) :
    Decisive F ({i} : Set V) x z := by
  sorry

/--
If `{i}` is decisive for `x ≻ y`, then it is also decisive for `z ≻ y`.
-/
theorem singleton_transfer_right
    {F : SocialWelfareFunction V A}
    (hPareto : WeakPareto F)
    (hIIA : IIA F)
    {i : V}
    {x y z : A}
    (hxy : x ≠ y)
    (hzy : z ≠ y)
    (hSingle : Decisive F ({i} : Set V) x y) :
    Decisive F ({i} : Set V) z y := by
  sorry

/--
If the singleton coalition `{i}` is decisive for one ordered pair of distinct
alternatives, then under Weak Pareto and IIA it is universally decisive.
-/
theorem singleton_universallyDecisive_of_pair
    {F : SocialWelfareFunction V A}
    (hPareto : WeakPareto F)
    (hIIA : IIA F)
    {i : V}
    {x y : A}
    (hxy : x ≠ y)
    (hSingle : Decisive F ({i} : Set V) x y) :
    UniversallyDecisive F ({i} : Set V) := by
  sorry

end SingletonTransfer

end Arrow

end SocialChoice
end EcoLean
