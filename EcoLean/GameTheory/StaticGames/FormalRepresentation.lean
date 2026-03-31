import EcoLean.GameTheory.Introduction.AbstractGameModels
import Mathlib.Data.Real.Basic

namespace EcoLean.GameTheory

universe u v

/--
A static game in strategic form:
players, feasible actions, and player-indexed payoff functions on action profiles.
-/
structure StaticGame where
  Player : Type u
  Action : Player → Type v
  payoff : Player → DProfile Action → ℝ

namespace StaticGame

/-- The type of action profiles of a static game. -/
abbrev ActionProfile (G : StaticGame) := DProfile G.Action

/-- The utility profile induced by an action profile. -/
def payoffProfile (G : StaticGame) (a : G.ActionProfile) : Profile G.Player ℝ :=
  fun i => G.payoff i a

@[simp] theorem payoffProfile_apply (G : StaticGame) (a : G.ActionProfile) (i : G.Player) :
    G.payoffProfile a i = G.payoff i a := rfl

/-- Unilateral deviation from an action profile. -/
def deviate (G : StaticGame) [DecidableEq G.Player]
    (a : G.ActionProfile) (i : G.Player) (ai : G.Action i) : G.ActionProfile :=
  DProfile.update a i ai

@[simp] theorem deviate_self (G : StaticGame) [DecidableEq G.Player]
    (a : G.ActionProfile) (i : G.Player) (ai : G.Action i) :
    G.deviate a i ai i = ai := by
  simp [StaticGame.deviate]

theorem deviate_ne (G : StaticGame) [DecidableEq G.Player]
    (a : G.ActionProfile) {i j : G.Player} (ai : G.Action i) (h : j ≠ i) :
    G.deviate a i ai j = a j := by
  simp [StaticGame.deviate, DProfile.update_ne, h]

@[simp] theorem deviate_eq_self (G : StaticGame) [DecidableEq G.Player]
    (a : G.ActionProfile) (i : G.Player) :
    G.deviate a i (a i) = a := by
  simp [StaticGame.deviate]

/-- Player `i`'s payoff after deviating unilaterally to `ai`. -/
def devPayoff (G : StaticGame) [DecidableEq G.Player]
    (a : G.ActionProfile) (i : G.Player) (ai : G.Action i) : ℝ :=
  G.payoff i (G.deviate a i ai)

end StaticGame

end EcoLean.GameTheory
