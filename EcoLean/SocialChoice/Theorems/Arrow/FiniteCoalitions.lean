import EcoLean.SocialChoice.Theorems.Arrow.MinimalDecisive
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

section FiniteCoalitions

variable {V : Type u} {A : Type v}

/--
A finite coalition is universally decisive if its underlying set is universally decisive.
-/
def FinsetUniversallyDecisive
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) (S : Finset V) : Prop :=
  UniversallyDecisive F (↑S : Set V)

/--
A finite coalition is minimally universally decisive if it is universally decisive
and no proper finite subset is universally decisive.
-/
def FinsetMinimallyUniversallyDecisive
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) (S : Finset V) : Prop :=
  FinsetUniversallyDecisive F S ∧
    ∀ T : Finset V, T ⊆ S → T ≠ S → ¬ FinsetUniversallyDecisive F T

namespace FinsetUniversallyDecisive

variable {F : SocialWelfareFunction V A} {S : Finset V}

theorem to_set
    (h : FinsetUniversallyDecisive F S) :
    UniversallyDecisive F (↑S : Set V) :=
  h

theorem decisive
    (h : FinsetUniversallyDecisive F S)
    {x y : A} (hxy : x ≠ y) :
    Decisive F (↑S : Set V) x y := by
  exact h x y hxy

end FinsetUniversallyDecisive

namespace FinsetMinimallyUniversallyDecisive

variable {F : SocialWelfareFunction V A} {S T : Finset V}

theorem universallyDecisive
    (h : FinsetMinimallyUniversallyDecisive F S) :
    FinsetUniversallyDecisive F S :=
  h.1

theorem not_universallyDecisive_of_ssubset
    (h : FinsetMinimallyUniversallyDecisive F S)
    (hTS : T ⊆ S)
    (hne : T ≠ S) :
    ¬ FinsetUniversallyDecisive F T :=
  h.2 T hTS hne

end FinsetMinimallyUniversallyDecisive

/--
If the voter type is finite, the full electorate as a finset is available as a candidate coalition.
-/
def fullCoalition (V : Type u) [Fintype V] : Finset V :=
  Finset.univ

theorem fullCoalition_universallyDecisive_of_set_version
    {F : SocialWelfareFunction V A}
    [Fintype V]
    (h : UniversallyDecisive F (Set.univ : Set V)) :
    FinsetUniversallyDecisive F (fullCoalition V) := by
  simpa [FinsetUniversallyDecisive, fullCoalition]

end FiniteCoalitions

end Arrow

end SocialChoice
end EcoLean
