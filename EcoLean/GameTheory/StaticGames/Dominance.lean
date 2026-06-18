import EcoLean.GameTheory.StaticGames.Equilibrium

/-!
# Dominance for static games

Strict and weak dominance, dominant actions, and dominant-strategy equilibrium, following
Battigalli–Catonini–De Vito, *Game Theory: Analysis of Strategic Thinking*. All notions are
pure-strategy predicates over the existing `StaticGame` API.

An action `ai` of player `i` (strictly/weakly) dominates `bi` when it does (strictly/weakly) better
against every configuration of the other players. The other players' configuration is quantified here
as an arbitrary action profile `a`: since the deviation `G.deviate a i ·` overwrites player `i`'s own
component, the value `G.devPayoff a i x` depends only on the opponents' components of `a`, so
quantifying over all profiles is exactly quantifying over all opponent configurations.

The main facts are:

* `isDominant_iff_forall_isBestResponseAt` — a (weakly) dominant action is exactly one that is a best
  response against every profile.
* `not_isNashEquilibrium_of_strictlyDominated` — a strictly dominated action is never a best response,
  hence never played in a Nash equilibrium.
* `isNashEquilibrium_of_dominantStrategyEquilibrium` — a profile of dominant actions is a Nash
  equilibrium.
-/

namespace EcoLean.GameTheory

namespace StaticGame

universe u v

variable (G : StaticGame) [DecidableEq G.Player]

/-! ### Definitions -/

/-- Action `ai` *strictly dominates* `bi` for player `i`: it yields a strictly higher payoff than `bi`
against every configuration of the other players. -/
def StrictlyDominates (i : G.Player) (ai bi : G.Action i) : Prop :=
  ∀ a : G.ActionProfile, G.devPayoff a i ai > G.devPayoff a i bi

/-- Action `ai` *weakly dominates* `bi` for player `i`: never worse against any configuration, and
strictly better against at least one. -/
def WeaklyDominates (i : G.Player) (ai bi : G.Action i) : Prop :=
  (∀ a : G.ActionProfile, G.devPayoff a i ai ≥ G.devPayoff a i bi) ∧
    (∃ a : G.ActionProfile, G.devPayoff a i ai > G.devPayoff a i bi)

/-- `bi` is *strictly dominated* for player `i` if some action strictly dominates it. -/
def IsStrictlyDominated (i : G.Player) (bi : G.Action i) : Prop :=
  ∃ ai : G.Action i, G.StrictlyDominates i ai bi

/-- `bi` is *weakly dominated* for player `i` if some action weakly dominates it. -/
def IsWeaklyDominated (i : G.Player) (bi : G.Action i) : Prop :=
  ∃ ai : G.Action i, G.WeaklyDominates i ai bi

/-- `ai` is a *(weakly) dominant* action for player `i`: a best response against every configuration
of the other players. -/
def IsDominant (i : G.Player) (ai : G.Action i) : Prop :=
  ∀ (a : G.ActionProfile) (ci : G.Action i), G.devPayoff a i ai ≥ G.devPayoff a i ci

/-- `ai` is a *strictly dominant* action for player `i`: it strictly dominates every other action. -/
def IsStrictlyDominant (i : G.Player) (ai : G.Action i) : Prop :=
  ∀ ci : G.Action i, ci ≠ ai → G.StrictlyDominates i ai ci

/-- A *dominant-strategy equilibrium*: every player plays a (weakly) dominant action. -/
def IsDominantStrategyEquilibrium (a : G.ActionProfile) : Prop :=
  ∀ i : G.Player, G.IsDominant i (a i)

variable {G}

/-! ### Order properties of strict dominance -/

theorem StrictlyDominates.trans {i : G.Player} {ai bi ci : G.Action i}
    (h₁ : G.StrictlyDominates i ai bi) (h₂ : G.StrictlyDominates i bi ci) :
    G.StrictlyDominates i ai ci :=
  fun a => lt_trans (h₂ a) (h₁ a)

theorem StrictlyDominates.asymm [Nonempty G.ActionProfile] {i : G.Player} {ai bi : G.Action i}
    (h : G.StrictlyDominates i ai bi) (h' : G.StrictlyDominates i bi ai) : False := by
  obtain ⟨a⟩ := ‹Nonempty G.ActionProfile›
  exact lt_asymm (h a) (h' a)

theorem StrictlyDominates.irrefl [Nonempty G.ActionProfile] {i : G.Player} (ai : G.Action i) :
    ¬ G.StrictlyDominates i ai ai := by
  intro h
  obtain ⟨a⟩ := ‹Nonempty G.ActionProfile›
  exact lt_irrefl _ (h a)

/-- Strict dominance implies weak dominance (the strict witness needs at least one profile). -/
theorem StrictlyDominates.weaklyDominates [Nonempty G.ActionProfile] {i : G.Player}
    {ai bi : G.Action i} (h : G.StrictlyDominates i ai bi) : G.WeaklyDominates i ai bi := by
  obtain ⟨a₀⟩ := ‹Nonempty G.ActionProfile›
  exact ⟨fun a => le_of_lt (h a), a₀, h a₀⟩

/-! ### Double deviation

Deviating twice in the same component keeps only the last deviation, so the payoff of a second
deviation does not see the first. -/

theorem deviate_deviate (a : G.ActionProfile) (i : G.Player) (ai ci : G.Action i) :
    G.deviate (G.deviate a i ai) i ci = G.deviate a i ci := by
  funext j
  by_cases h : j = i
  · subst h; simp [StaticGame.deviate]
  · simp [StaticGame.deviate, h]

theorem devPayoff_deviate (a : G.ActionProfile) (i : G.Player) (ai ci : G.Action i) :
    G.devPayoff (G.deviate a i ai) i ci = G.devPayoff a i ci := by
  unfold StaticGame.devPayoff
  rw [deviate_deviate]

/-! ### Dominance and best response -/

/-- A (weakly) dominant action is exactly an action that is a best response against every profile. -/
theorem isDominant_iff_forall_isBestResponseAt (i : G.Player) (ai : G.Action i) :
    G.IsDominant i ai ↔ ∀ a : G.ActionProfile, G.IsBestResponseAt (G.deviate a i ai) i := by
  constructor
  · intro h a ci
    show G.devPayoff a i ai ≥ G.devPayoff (G.deviate a i ai) i ci
    rw [devPayoff_deviate]
    exact h a ci
  · intro h a ci
    have hb := h a ci
    rw [devPayoff_deviate] at hb
    exact hb

/-- A strictly dominated action is never a best response: deviating to a dominating action is
profitable. -/
theorem strictlyDominated_not_isBestResponseAt {a : G.ActionProfile} {i : G.Player}
    (h : G.IsStrictlyDominated i (a i)) : ¬ G.IsBestResponseAt a i := by
  obtain ⟨ci, hci⟩ := h
  intro hbest
  have h1 : G.devPayoff a i ci > G.devPayoff a i (a i) := hci a
  rw [G.devPayoff_self] at h1
  exact absurd (hbest ci) (not_le.mpr h1)

/-- Consequently, an action that is strictly dominated for some player is never played in a Nash
equilibrium. -/
theorem not_isNashEquilibrium_of_strictlyDominated {a : G.ActionProfile} {i : G.Player}
    (h : G.IsStrictlyDominated i (a i)) : ¬ G.IsNashEquilibrium a :=
  fun hNash => strictlyDominated_not_isBestResponseAt h (hNash i)

/-! ### Dominant-strategy equilibrium -/

/-- A profile of (weakly) dominant actions is a Nash equilibrium. -/
theorem isNashEquilibrium_of_dominantStrategyEquilibrium {a : G.ActionProfile}
    (h : G.IsDominantStrategyEquilibrium a) : G.IsNashEquilibrium a := by
  intro i ci
  have hd := h i a ci
  rwa [G.devPayoff_self] at hd

/-- A strictly dominant action is in particular (weakly) dominant. -/
theorem IsStrictlyDominant.isDominant {i : G.Player} {ai : G.Action i}
    (h : G.IsStrictlyDominant i ai) : G.IsDominant i ai := by
  classical
  intro a ci
  by_cases hci : ci = ai
  · subst hci; exact le_refl _
  · exact le_of_lt (h ci hci a)

/-- If `ai` is strictly dominant, every other action is strictly dominated (by `ai`). -/
theorem isStrictlyDominated_of_ne_of_strictlyDominant {i : G.Player} {ai ci : G.Action i}
    (h : G.IsStrictlyDominant i ai) (hci : ci ≠ ai) : G.IsStrictlyDominated i ci :=
  ⟨ai, h ci hci⟩

end StaticGame

end EcoLean.GameTheory
