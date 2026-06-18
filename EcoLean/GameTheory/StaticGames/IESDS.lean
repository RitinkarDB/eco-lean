import EcoLean.GameTheory.StaticGames.Dominance

/-!
# Iterated elimination of strictly dominated strategies

Iterated elimination of strictly dominated strategies (IESDS) for static games, following
Battigalli–Catonini–De Vito, *Game Theory: Analysis of Strategic Thinking*.

A *restriction* `X` records, for each player, the set of actions still available
(`Restriction G := ∀ i, Set (G.Action i)`). Dominance is taken *relative to a restriction*: an action
`bi` is strictly dominated on `X` (`StrictlyDominatedOn`) if some surviving action `ai ∈ X i` does
strictly better than `bi` against every configuration of the opponents drawn from `X`. One round of
elimination (`eliminate`) drops every such action; `iesds n` is the `n`-fold iterate starting from the
full action sets, and `survives` is the set of actions that remain at every stage.

Main results:

* `strictlyDominatedOn_univ_iff` — at the full restriction, dominance on `X` is exactly strict
  dominance in the sense of `Dominance.lean`, so the first round removes precisely the strictly
  dominated actions.
* `nash_mem_survives` — every action played in a Nash equilibrium survives every round of elimination
  (a best response is never strictly dominated against a restriction containing the equilibrium).
-/

namespace EcoLean.GameTheory

namespace StaticGame

universe u v

/-- A restriction of a static game: the set of actions still available to each player. -/
abbrev Restriction (G : StaticGame) := ∀ i : G.Player, Set (G.Action i)

/-- Action `bi` is *strictly dominated on the restriction `X`* for player `i`: some surviving action
`ai ∈ X i` yields a strictly higher payoff than `bi` against every opponent configuration drawn from
`X`. -/
def StrictlyDominatedOn (G : StaticGame) [DecidableEq G.Player]
    (X : G.Restriction) (i : G.Player) (bi : G.Action i) : Prop :=
  ∃ ai ∈ X i, ∀ a : G.ActionProfile, (∀ j, j ≠ i → a j ∈ X j) →
    G.devPayoff a i ai > G.devPayoff a i bi

/-- One round of elimination: from each player's surviving set, drop every action that is strictly
dominated on the current restriction. -/
def eliminate (G : StaticGame) [DecidableEq G.Player] (X : G.Restriction) : G.Restriction :=
  fun i => {ai | ai ∈ X i ∧ ¬ G.StrictlyDominatedOn X i ai}

/-- The `n`-fold iterate of elimination, starting from the full action sets. -/
def iesds (G : StaticGame) [DecidableEq G.Player] : ℕ → G.Restriction
  | 0 => fun _ => Set.univ
  | (n + 1) => G.eliminate (G.iesds n)

/-- The actions surviving iterated elimination of strictly dominated strategies: those remaining at
every stage. -/
def survives (G : StaticGame) [DecidableEq G.Player] : G.Restriction :=
  fun i => {ai | ∀ n, ai ∈ G.iesds n i}

variable {G : StaticGame} [DecidableEq G.Player]

/-! ### Basic structure of the elimination sequence -/

theorem eliminate_subset (X : G.Restriction) (i : G.Player) : G.eliminate X i ⊆ X i :=
  fun _ h => h.1

@[simp] theorem iesds_zero (i : G.Player) : G.iesds 0 i = Set.univ := rfl

theorem iesds_succ (n : ℕ) : G.iesds (n + 1) = G.eliminate (G.iesds n) := rfl

theorem iesds_succ_subset (n : ℕ) (i : G.Player) : G.iesds (n + 1) i ⊆ G.iesds n i :=
  G.eliminate_subset (G.iesds n) i

/-- The elimination sequence is decreasing: later stages survive fewer actions. -/
theorem iesds_antitone {i : G.Player} : ∀ {m n : ℕ}, m ≤ n → G.iesds n i ⊆ G.iesds m i := by
  intro m n h
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact (iesds_succ_subset _ i).trans ih

theorem survives_subset_iesds (n : ℕ) (i : G.Player) : G.survives i ⊆ G.iesds n i :=
  fun _ h => h n

/-! ### Relation to one-shot strict dominance

At the full restriction, dominance on `X` coincides with strict dominance over the whole game, so the
first elimination round removes exactly the strictly dominated actions. -/

theorem strictlyDominatedOn_univ_iff (i : G.Player) (bi : G.Action i) :
    G.StrictlyDominatedOn (fun _ => Set.univ) i bi ↔ G.IsStrictlyDominated i bi := by
  constructor
  · rintro ⟨ai, _, hdom⟩
    exact ⟨ai, fun a => hdom a fun _ _ => Set.mem_univ _⟩
  · rintro ⟨ai, hdom⟩
    exact ⟨ai, Set.mem_univ _, fun a _ => hdom a⟩

/-! ### Nash equilibria survive elimination -/

/-- A best response is never strictly dominated against a restriction that contains the equilibrium
profile: deviating to a dominating action would be profitable, contradicting the equilibrium. -/
theorem nash_not_strictlyDominatedOn {a : G.ActionProfile} (hNash : G.IsNashEquilibrium a)
    {X : G.Restriction} (hmem : ∀ j, a j ∈ X j) (i : G.Player) :
    ¬ G.StrictlyDominatedOn X i (a i) := by
  rintro ⟨ai, _, hdom⟩
  have h := hdom a fun j _ => hmem j
  rw [G.devPayoff_self] at h
  exact absurd (hNash i ai) (not_le.mpr h)

/-- Every action played in a Nash equilibrium survives every round of elimination. -/
theorem nash_mem_iesds {a : G.ActionProfile} (hNash : G.IsNashEquilibrium a) :
    ∀ (n : ℕ) (i : G.Player), a i ∈ G.iesds n i := by
  intro n
  induction n with
  | zero => intro i; exact Set.mem_univ _
  | succ k ih =>
      intro i
      rw [iesds_succ]
      show a i ∈ G.iesds k i ∧ ¬ G.StrictlyDominatedOn (G.iesds k) i (a i)
      exact ⟨ih i, nash_not_strictlyDominatedOn hNash ih i⟩

/-- Every action played in a Nash equilibrium survives iterated elimination. -/
theorem nash_mem_survives {a : G.ActionProfile} (hNash : G.IsNashEquilibrium a) (i : G.Player) :
    a i ∈ G.survives i :=
  fun n => nash_mem_iesds hNash n i

end StaticGame

end EcoLean.GameTheory
