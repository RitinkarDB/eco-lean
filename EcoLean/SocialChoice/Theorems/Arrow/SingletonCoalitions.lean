import EcoLean.SocialChoice.Theorems.Arrow.FiniteCoalitions

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

section SingletonCoalitions

variable {V : Type u} {A : Type v}

/--
The finset singleton coalition corresponding to voter `i`.
-/
def singletonCoalition (i : V) : Finset V :=
  {i}

/--
The set underlying the singleton finset coalition is the singleton set.
-/
theorem coe_singletonCoalition
    (i : V) :
    ((singletonCoalition i : Finset V) : Set V) = ({i} : Set V) := by
  ext j
  simp [singletonCoalition]

/--
If the singleton set coalition is universally decisive, then so is the
corresponding singleton finset coalition.
-/
theorem finsetUniversallyDecisive_singleton_of_set
    {F : SocialWelfareFunction V A}
    {i : V}
    (h : UniversallyDecisive F ({i} : Set V)) :
    FinsetUniversallyDecisive F (singletonCoalition i) := by
  simpa [FinsetUniversallyDecisive, coe_singletonCoalition, singletonCoalition] using h

/--
If the singleton finset coalition is universally decisive, then so is the
corresponding singleton set coalition.
-/
theorem setUniversallyDecisive_singleton_of_finset
    {F : SocialWelfareFunction V A}
    {i : V}
    (h : FinsetUniversallyDecisive F (singletonCoalition i)) :
    UniversallyDecisive F ({i} : Set V) := by
  simpa [FinsetUniversallyDecisive, coe_singletonCoalition, singletonCoalition] using h

end SingletonCoalitions

end Arrow

end SocialChoice
end EcoLean
