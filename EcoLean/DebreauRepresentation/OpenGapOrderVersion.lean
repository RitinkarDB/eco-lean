import EcoLean.DebreauRepresentation.GapAdjustment
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Order.Monotone.Basic

/-!
# Order-version of the open gap lemma
-/

namespace EcoLean
namespace Preference

/--
A real-valued map on a type `T` lands inside the arctan interval if all of its
values lie strictly between `-π / 2` and `π / 2`.
-/
def MapsIntoArctanIntervalOn {T : Type} (g : T → ℝ) : Prop :=
  ∀ t : T, -(Real.pi / 2) < g t ∧ g t < Real.pi / 2

/--
A bounded open-gap embedding of a linear order into `ℝ`.
-/
def BoundedOpenGapEmbedding (T : Type) [LinearOrder T] : Prop :=
  ∃ g : T → ℝ,
    StrictMono g ∧
    MapsIntoArctanIntervalOn g ∧
    HasOnlyOpenGaps (Set.range g)

/--
Order-version of the countable open gap lemma.
-/
def CountableOpenGapLemmaOnOrders : Prop :=
  ∀ (T : Type) [LinearOrder T] [Countable T],
    BoundedOpenGapEmbedding T

/--
`Real.arctan` lands inside the arctan interval.
-/
theorem mapsIntoArctanIntervalOn_arctan :
    MapsIntoArctanIntervalOn Real.arctan := by
  intro r
  constructor
  · exact Real.neg_pi_div_two_lt_arctan r
  · exact Real.arctan_lt_pi_div_two r

end Preference
end EcoLean
