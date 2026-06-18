import EcoLean.GameTheory.StaticGames.IESDS

/-!
# Rationalizability

Point-rationalizability for static games, following Battigalli–Catonini–De Vito, *Game Theory:
Analysis of Strategic Thinking* (and Bernheim/Pearce). The development reuses the `Restriction`
vocabulary of `IESDS.lean`.

An action `ai` is a *best response within* a restriction `X` (`BestResponseWithin`) if it is optimal
against some configuration of the opponents drawn from `X`. A restriction `X` is a *best-response set*
(`IsBestResponseSet`) if every surviving action is a best response within `X`. The *rationalizable*
actions are those belonging to some best-response set — equivalently, the largest best-response set.

Main results:

* `rationalizable_isBestResponseSet` / `subset_rationalizable_of_isBestResponseSet` — `Rationalizable`
  is itself a best-response set, and it is the largest one.
* `nash_mem_rationalizable` — every action played in a Nash equilibrium is rationalizable (the
  singleton restriction at the equilibrium is a best-response set).
* `rationalizable_subset_survives` — rationalizable actions survive iterated elimination of strictly
  dominated strategies (a best response is never strictly dominated against a restriction containing
  its justifying belief).

Together: in a static game, the actions played in a Nash equilibrium are rationalizable, and
rationalizable actions survive IESDS.
-/

namespace EcoLean.GameTheory

namespace StaticGame

universe u v

/-- `ai` is a *best response within the restriction `X`* for player `i`: it is optimal against some
configuration of the opponents drawn from `X`. -/
def BestResponseWithin (G : StaticGame) [DecidableEq G.Player]
    (X : G.Restriction) (i : G.Player) (ai : G.Action i) : Prop :=
  ∃ a : G.ActionProfile, (∀ j, j ≠ i → a j ∈ X j) ∧
    ∀ ci : G.Action i, G.devPayoff a i ai ≥ G.devPayoff a i ci

/-- `X` is a *best-response set*: every surviving action is a best response within `X`. -/
def IsBestResponseSet (G : StaticGame) [DecidableEq G.Player] (X : G.Restriction) : Prop :=
  ∀ (i : G.Player), ∀ ai ∈ X i, G.BestResponseWithin X i ai

/-- The *rationalizable* actions of `G`: those belonging to some best-response set. Equivalently, the
largest best-response set (`rationalizable_isBestResponseSet`). -/
def Rationalizable (G : StaticGame) [DecidableEq G.Player] : G.Restriction :=
  fun i => {ai | ∃ X : G.Restriction, G.IsBestResponseSet X ∧ ai ∈ X i}

variable {G : StaticGame} [DecidableEq G.Player]

theorem mem_rationalizable_iff (i : G.Player) (ai : G.Action i) :
    ai ∈ G.Rationalizable i ↔ ∃ X : G.Restriction, G.IsBestResponseSet X ∧ ai ∈ X i :=
  Iff.rfl

/-! ### Rationalizable is the largest best-response set -/

/-- The rationalizable actions form a best-response set: the justifying belief of an action in a
best-response set `X` lives in `X`, hence in `Rationalizable`. -/
theorem rationalizable_isBestResponseSet : G.IsBestResponseSet G.Rationalizable := by
  intro i ai hai
  obtain ⟨X, hX, haiX⟩ := hai
  obtain ⟨a, haX, hbest⟩ := hX i ai haiX
  exact ⟨a, fun j hj => ⟨X, hX, haX j hj⟩, hbest⟩

/-- Every best-response set is contained in the rationalizable actions. -/
theorem subset_rationalizable_of_isBestResponseSet {X : G.Restriction}
    (hX : G.IsBestResponseSet X) (i : G.Player) : X i ⊆ G.Rationalizable i :=
  fun _ hai => ⟨X, hX, hai⟩

/-! ### Nash equilibria are rationalizable -/

/-- Every action played in a Nash equilibrium is rationalizable: the singleton restriction at the
equilibrium profile is a best-response set, each action being a best response to the profile itself. -/
theorem nash_mem_rationalizable {a : G.ActionProfile} (hNash : G.IsNashEquilibrium a) (i : G.Player) :
    a i ∈ G.Rationalizable i := by
  refine ⟨fun j => {a j}, ?_, Set.mem_singleton_iff.mpr rfl⟩
  intro j aj haj
  rw [Set.mem_singleton_iff] at haj
  subst haj
  refine ⟨a, fun k _ => Set.mem_singleton_iff.mpr rfl, fun cj => ?_⟩
  rw [G.devPayoff_self]
  exact hNash j cj

/-! ### Rationalizable actions survive iterated strict dominance -/

/-- A best response within `X` is never strictly dominated on any larger restriction `Y`: its
justifying belief stays admissible for `Y`, and a best response there cannot be beaten. -/
theorem bestResponseWithin_not_strictlyDominatedOn {X Y : G.Restriction} {i : G.Player}
    {ai : G.Action i} (hbr : G.BestResponseWithin X i ai) (hXY : ∀ j, X j ⊆ Y j) :
    ¬ G.StrictlyDominatedOn Y i ai := by
  obtain ⟨a, haX, hbest⟩ := hbr
  rintro ⟨bi, _, hdom⟩
  have h := hdom a fun j hj => hXY j (haX j hj)
  exact absurd (hbest bi) (not_le.mpr h)

theorem rationalizable_subset_iesds :
    ∀ (n : ℕ) (i : G.Player), G.Rationalizable i ⊆ G.iesds n i := by
  intro n
  induction n with
  | zero => intro i ai _; exact Set.mem_univ _
  | succ k ih =>
      intro i ai hai
      rw [iesds_succ]
      show ai ∈ G.iesds k i ∧ ¬ G.StrictlyDominatedOn (G.iesds k) i ai
      exact ⟨ih i hai,
        bestResponseWithin_not_strictlyDominatedOn (rationalizable_isBestResponseSet i ai hai) ih⟩

/-- Rationalizable actions survive iterated elimination of strictly dominated strategies. -/
theorem rationalizable_subset_survives (i : G.Player) : G.Rationalizable i ⊆ G.survives i :=
  fun _ hai n => rationalizable_subset_iesds n i hai

end StaticGame

end EcoLean.GameTheory
