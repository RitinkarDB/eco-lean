import EcoLean.GameTheory.StaticGames.FormalRepresentation

/-!
# Equilibrium notions for static games

This file adds the basic best-response and Nash-equilibrium vocabulary on top
of the existing `StaticGame` representation.  It does not change the game
record: all notions are predicates over the current API of action profiles,
unilateral deviations, and real-valued payoffs.
-/

namespace EcoLean.GameTheory

namespace StaticGame

universe u v

variable (G : StaticGame)

section Equilibrium

variable [DecidableEq G.Player]

/-- Player `i` has no profitable unilateral deviation from profile `a`. -/
def IsBestResponseAt (a : G.ActionProfile) (i : G.Player) : Prop :=
  ∀ ai : G.Action i, G.payoff i a ≥ G.devPayoff a i ai

/-- A unilateral deviation that strictly improves player `i`'s payoff. -/
def ProfitableDeviation
    (a : G.ActionProfile) (i : G.Player) (ai : G.Action i) : Prop :=
  G.devPayoff a i ai > G.payoff i a

/-- Nash equilibrium for a static game in pure strategies. -/
def IsNashEquilibrium (a : G.ActionProfile) : Prop :=
  ∀ i : G.Player, G.IsBestResponseAt a i

@[simp] theorem devPayoff_self (a : G.ActionProfile) (i : G.Player) :
    G.devPayoff a i (a i) = G.payoff i a := by
  simp [StaticGame.devPayoff]

theorem payoff_ge_deviation_of_nash
    {a : G.ActionProfile}
    (hNash : G.IsNashEquilibrium a)
    (i : G.Player) (ai : G.Action i) :
    G.payoff i a ≥ G.devPayoff a i ai :=
  hNash i ai

theorem bestResponseAt_of_nash
    {a : G.ActionProfile}
    (hNash : G.IsNashEquilibrium a)
    (i : G.Player) :
    G.IsBestResponseAt a i :=
  hNash i

theorem nash_of_bestResponseAt
    {a : G.ActionProfile}
    (hBest : ∀ i : G.Player, G.IsBestResponseAt a i) :
    G.IsNashEquilibrium a :=
  hBest

theorem bestResponseAt_iff_no_profitableDeviation
    (a : G.ActionProfile) (i : G.Player) :
    G.IsBestResponseAt a i ↔
      ∀ ai : G.Action i, ¬ G.ProfitableDeviation a i ai := by
  constructor
  · intro hBest ai hProf
    exact not_lt_of_ge (hBest ai) hProf
  · intro hNo ai
    exact le_of_not_gt (hNo ai)

theorem nash_iff_no_profitableDeviation
    (a : G.ActionProfile) :
    G.IsNashEquilibrium a ↔
      ∀ (i : G.Player) (ai : G.Action i),
        ¬ G.ProfitableDeviation a i ai := by
  constructor
  · intro hNash i ai
    exact (G.bestResponseAt_iff_no_profitableDeviation a i).mp (hNash i) ai
  · intro hNo i
    exact (G.bestResponseAt_iff_no_profitableDeviation a i).mpr (hNo i)

end Equilibrium

end StaticGame

end EcoLean.GameTheory
