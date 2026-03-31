import EcoLean.GameTheory.MathLanguage.Expectation
import EcoLean.GameTheory.StaticGames.FormalRepresentation
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Real.Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace EcoLean.GameTheory

universe u v

namespace StaticGame

/--
Player `i`'s payoff as a random variable on the space of action profiles.
-/
def payoffRV (G : StaticGame) (i : G.Player) : G.ActionProfile → ℝ :=
  fun a => G.payoff i a

/--
Player `i`'s payoff after deviating unilaterally to `ai`,
viewed as a random variable on the space of action profiles.
-/
def devPayoffRV (G : StaticGame) [DecidableEq G.Player]
    (i : G.Player) (ai : G.Action i) : G.ActionProfile → ℝ :=
  fun a => G.payoff i (G.deviate a i ai)

/--
Expected payoff of player `i` under a probability measure on action profiles.
-/
noncomputable def expectedPayoff
    (G : StaticGame)
    [MeasurableSpace G.ActionProfile]
    (P : MeasureTheory.ProbabilityMeasure G.ActionProfile)
    (i : G.Player) : ℝ :=
  expectation P (G.payoffRV i)

/--
Expected payoff of player `i` from deviating unilaterally to `ai`,
under a probability measure on action profiles.
-/
noncomputable def expectedDevPayoff
    (G : StaticGame) [DecidableEq G.Player]
    [MeasurableSpace G.ActionProfile]
    (P : MeasureTheory.ProbabilityMeasure G.ActionProfile)
    (i : G.Player) (ai : G.Action i) : ℝ :=
  expectation P (G.devPayoffRV i ai)

@[simp] theorem payoffRV_apply (G : StaticGame) (i : G.Player) (a : G.ActionProfile) :
    G.payoffRV i a = G.payoff i a := rfl

@[simp] theorem devPayoffRV_apply (G : StaticGame) [DecidableEq G.Player]
    (i : G.Player) (ai : G.Action i) (a : G.ActionProfile) :
    G.devPayoffRV i ai a = G.payoff i (G.deviate a i ai) := rfl

end StaticGame

end EcoLean.GameTheory
