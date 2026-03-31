import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace EcoLean.GameTheory

universe u

abbrev ProbMeasure (Ω : Type u) [MeasurableSpace Ω] :=
  MeasureTheory.ProbabilityMeasure Ω

end EcoLean.GameTheory
