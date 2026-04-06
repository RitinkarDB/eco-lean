import EcoLean.SocialChoice.Theorems.Arrow.SingletonTransfer

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

section SingletonSwap

variable {V : Type u} {A : Type v}
variable [Fintype V] [DecidableEq V]

/--
Missing Arrow bridge.

If a singleton coalition is decisive for one ordered pair `x ≻ y`, then under
the Arrow hypotheses it can be shown to control the reversed pair `y ≻ x` as
well, via a third alternative and IIA-based profile manipulations.

We isolate this as the next target rather than forcing it inside the universal
theorem.
-/
theorem singleton_transfer_swap
    {F : SocialWelfareFunction V A}
    (hRat : RationalSWF F)
    (hPareto : WeakPareto F)
    (hIIA : IIA F)
    {i : V}
    {x y z : A}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hSingle : Decisive F ({i} : Set V) x y) :
    Decisive F ({i} : Set V) y x := by
  sorry

end SingletonSwap

end Arrow

end SocialChoice
end EcoLean
