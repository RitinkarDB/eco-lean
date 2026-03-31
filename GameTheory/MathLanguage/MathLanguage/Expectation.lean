import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Real.Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace EcoLean.GameTheory

universe u

section

variable {Ω : Type u} [MeasurableSpace Ω]

def expectation (P : MeasureTheory.ProbabilityMeasure Ω) (X : Ω → ℝ) : ℝ :=
  ∫ ω, X ω ∂(P : MeasureTheory.Measure Ω)

end

end EcoLean.GameTheory
