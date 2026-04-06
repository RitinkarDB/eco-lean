import EcoLean.SocialChoice.Basic.SocialWelfareFunction
import EcoLean.SocialChoice.Properties.Pareto
import EcoLean.SocialChoice.Properties.IIA
import EcoLean.SocialChoice.Properties.SWFDictatorship
import EcoLean.SocialChoice.Properties.CollectiveRationality
import Mathlib.Data.Fintype.Card

universe u v

namespace EcoLean
namespace SocialChoice

/--
Arrow's Impossibility Theorem (finite version, scaffold).

For a finite set of voters and at least three alternatives, any social welfare
function satisfying rationality, Weak Pareto, and IIA is dictatorial.
-/
theorem arrow
    {V : Type u} {A : Type v}
    [Fintype V] [Fintype A]
    (F : SocialWelfareFunction V A)
    (hA : 3 ≤ Fintype.card A)
    (hRat : RationalSWF F)
    (hPareto : WeakPareto F)
    (hIIA : IIA F) :
    DictatorialSWF F := by
  sorry

end SocialChoice
end EcoLean
