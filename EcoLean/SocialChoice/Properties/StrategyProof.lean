import EcoLean.SocialChoice.Properties.Manipulation

universe u v

namespace EcoLean
namespace SocialChoice

/--
A social choice function is strategy-proof if no voter can manipulate it.
-/
def StrategyProof
    {V : Type u} {A : Type v}
    (f : SocialChoiceFunction V A) : Prop :=
  ¬ Manipulable f

namespace StrategyProof

variable {V : Type u} {A : Type v} {f : SocialChoiceFunction V A}

theorem of_forall_not_manipulableBy
    (h : ∀ i : V, ¬ ManipulableBy f i) :
    StrategyProof f := by
  intro hM
  rcases hM with ⟨i, hi⟩
  exact h i hi

theorem not_manipulableBy
    (h : StrategyProof f) (i : V) :
    ¬ ManipulableBy f i := by
  intro hi
  exact h ⟨i, hi⟩

end StrategyProof

end SocialChoice
end EcoLean
