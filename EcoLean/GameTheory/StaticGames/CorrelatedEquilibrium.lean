import EcoLean.GameTheory.StaticGames.Dominance
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Correlated equilibrium

Correlated equilibrium (Aumann) for finite static games, following Battigalli–Catonini–De Vito,
*Game Theory: Analysis of Strategic Thinking*.

A *correlated distribution* is a probability distribution `μ` over the action profiles. Player `i`'s
expected payoff is `expectedPayoff μ i`, and the expected payoff when `i` departs from the recommended
action via a function `δ : Action i → Action i` is `expectedDeviationPayoff μ i δ`. A *correlated
equilibrium* (`IsCorrelatedEquilibrium`) is a correlated distribution under which no departure is
profitable in expectation for any player — Aumann's ex-ante formulation.

Main results:

* `isCorrelatedEquilibrium_dirac` — the point mass at a (pure) Nash equilibrium is a correlated
  equilibrium, so `exists_correlatedEquilibrium_of_nash` gives existence whenever a pure Nash
  equilibrium exists.
* `IsCorrelatedEquilibrium.convexCombo` — the set of correlated equilibria is convex (the defining
  constraints are affine in `μ`), in contrast to the set of Nash equilibria.
* `correlatedEquilibrium_eq_zero_of_strictlyDominated` — every profile recommending a strictly
  dominated action carries zero probability, the correlated analogue of
  `not_isNashEquilibrium_of_strictlyDominated`.

A finite type of players with finite action sets is assumed throughout, so distributions over action
profiles can be summed.
-/

namespace EcoLean.GameTheory

namespace StaticGame

open scoped BigOperators Classical

universe u v

variable (G : StaticGame) [Fintype G.Player] [DecidableEq G.Player] [∀ i, Fintype (G.Action i)]

/-! ### Definitions -/

/-- Player `i`'s expected payoff under a distribution `μ` over action profiles. -/
noncomputable def expectedPayoff (μ : G.ActionProfile → ℝ) (i : G.Player) : ℝ :=
  ∑ a : G.ActionProfile, μ a * G.payoff i a

/-- Player `i`'s expected payoff when, instead of obeying the recommendation, `i` plays according to
the departure function `δ` (mapping the recommended action to an actual action). -/
noncomputable def expectedDeviationPayoff
    (μ : G.ActionProfile → ℝ) (i : G.Player) (δ : G.Action i → G.Action i) : ℝ :=
  ∑ a : G.ActionProfile, μ a * G.devPayoff a i (δ (a i))

/-- `μ` is a probability distribution over action profiles. -/
def IsCorrelatedDistribution (μ : G.ActionProfile → ℝ) : Prop :=
  (∀ a, 0 ≤ μ a) ∧ ∑ a : G.ActionProfile, μ a = 1

/-- `μ` is a *correlated equilibrium* (Aumann): a distribution over action profiles under which no
player can gain, in expectation, by departing from the recommended action through any function `δ`. -/
def IsCorrelatedEquilibrium (μ : G.ActionProfile → ℝ) : Prop :=
  G.IsCorrelatedDistribution μ ∧
    ∀ (i : G.Player) (δ : G.Action i → G.Action i),
      G.expectedDeviationPayoff μ i δ ≤ G.expectedPayoff μ i

/-- The Dirac (point-mass) distribution at a profile `a₀`. -/
noncomputable def dirac (a₀ : G.ActionProfile) : G.ActionProfile → ℝ :=
  fun a => if a = a₀ then 1 else 0

variable {G}

/-- Summation against a Dirac mass picks out the value at the mass point. -/
theorem sum_dirac_mul (a₀ : G.ActionProfile) (g : G.ActionProfile → ℝ) :
    ∑ a : G.ActionProfile, G.dirac a₀ a * g a = g a₀ := by
  simp only [dirac]
  rw [Finset.sum_eq_single a₀ (fun b _ hb => by rw [if_neg hb, zero_mul])
        (fun h => absurd (Finset.mem_univ a₀) h), if_pos rfl, one_mul]

/-! ### A pure Nash equilibrium induces a correlated equilibrium -/

/-- The point mass at a pure Nash equilibrium is a correlated equilibrium: conditional on the (unique)
recommendation, obeying is optimal because the profile is a Nash equilibrium. -/
theorem isCorrelatedEquilibrium_dirac {a : G.ActionProfile} (hNash : G.IsNashEquilibrium a) :
    G.IsCorrelatedEquilibrium (G.dirac a) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a'
    simp only [dirac]
    split_ifs <;> norm_num
  · simpa using sum_dirac_mul a (fun _ => (1 : ℝ))
  · intro i δ
    simp only [expectedPayoff, expectedDeviationPayoff]
    rw [sum_dirac_mul a (fun a' => G.devPayoff a' i (δ (a' i))),
      sum_dirac_mul a (fun a' => G.payoff i a')]
    exact hNash i (δ (a i))

/-- A correlated equilibrium exists whenever a pure Nash equilibrium does. -/
theorem exists_correlatedEquilibrium_of_nash {a : G.ActionProfile} (hNash : G.IsNashEquilibrium a) :
    ∃ μ : G.ActionProfile → ℝ, G.IsCorrelatedEquilibrium μ :=
  ⟨G.dirac a, isCorrelatedEquilibrium_dirac hNash⟩

/-! ### The set of correlated equilibria is convex -/

theorem expectedPayoff_combo (t : ℝ) (μ ν : G.ActionProfile → ℝ) (i : G.Player) :
    G.expectedPayoff (fun a => t * μ a + (1 - t) * ν a) i
      = t * G.expectedPayoff μ i + (1 - t) * G.expectedPayoff ν i := by
  simp only [expectedPayoff, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem expectedDeviationPayoff_combo (t : ℝ) (μ ν : G.ActionProfile → ℝ) (i : G.Player)
    (δ : G.Action i → G.Action i) :
    G.expectedDeviationPayoff (fun a => t * μ a + (1 - t) * ν a) i δ
      = t * G.expectedDeviationPayoff μ i δ + (1 - t) * G.expectedDeviationPayoff ν i δ := by
  simp only [expectedDeviationPayoff, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- Convex combinations of correlated equilibria are correlated equilibria: the distribution and
incentive constraints are all affine in `μ`. -/
theorem IsCorrelatedEquilibrium.convexCombo {μ ν : G.ActionProfile → ℝ}
    (hμ : G.IsCorrelatedEquilibrium μ) (hν : G.IsCorrelatedEquilibrium ν)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    G.IsCorrelatedEquilibrium (fun a => t * μ a + (1 - t) * ν a) := by
  obtain ⟨⟨hμpos, hμsum⟩, hμic⟩ := hμ
  obtain ⟨⟨hνpos, hνsum⟩, hνic⟩ := hν
  have h1t : 0 ≤ 1 - t := by linarith
  refine ⟨⟨fun a => ?_, ?_⟩, fun i δ => ?_⟩
  · exact add_nonneg (mul_nonneg ht0 (hμpos a)) (mul_nonneg h1t (hνpos a))
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hμsum, hνsum]; ring
  · rw [expectedPayoff_combo, expectedDeviationPayoff_combo]
    have hμd := hμic i δ
    have hνd := hνic i δ
    nlinarith [mul_le_mul_of_nonneg_left hμd ht0, mul_le_mul_of_nonneg_left hνd h1t]

/-! ### Strictly dominated actions get zero probability -/

/-- In any correlated equilibrium, every profile recommending a strictly dominated action `bi` to
player `i` carries zero probability: departing from `bi` to the dominating action `ai` would be a
profitable deviation. This is the correlated-equilibrium analogue of
`not_isNashEquilibrium_of_strictlyDominated`. -/
theorem correlatedEquilibrium_eq_zero_of_strictlyDominated {μ : G.ActionProfile → ℝ}
    (hμ : G.IsCorrelatedEquilibrium μ) {i : G.Player} {ai bi : G.Action i}
    (hdom : G.StrictlyDominates i ai bi) {a₀ : G.ActionProfile} (ha₀ : a₀ i = bi) :
    μ a₀ = 0 := by
  obtain ⟨⟨hpos, _⟩, hic⟩ := hμ
  classical
  -- The departure that replaces the recommendation `bi` by the dominating action `ai`.
  set δ : G.Action i → G.Action i := fun x => if x = bi then ai else x with hδ
  -- The per-profile payoff gain from this departure is never positive, and is negative exactly on the
  -- profiles where `bi` is recommended to `i`.
  have hle : ∀ b : G.ActionProfile,
      μ b * (G.payoff i b - G.devPayoff b i (δ (b i))) ≤ 0 := by
    intro b
    by_cases hb : b i = bi
    · have hδb : δ (b i) = ai := by rw [hδ]; simp [hb]
      have hpb : G.payoff i b = G.devPayoff b i bi := by rw [← hb, G.devPayoff_self]
      rw [hδb, hpb]
      exact mul_nonpos_iff.2 (Or.inl ⟨hpos b, by linarith [hdom b]⟩)
    · have hδb : δ (b i) = b i := by rw [hδ]; simp [hb]
      simp [hδb]
  -- That total gain is `expectedPayoff − expectedDeviationPayoff`, which is `≥ 0` at equilibrium.
  have hsum : ∑ b : G.ActionProfile, μ b * (G.payoff i b - G.devPayoff b i (δ (b i)))
      = G.expectedPayoff μ i - G.expectedDeviationPayoff μ i δ := by
    simp only [expectedPayoff, expectedDeviationPayoff]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hge : 0 ≤ ∑ b : G.ActionProfile, μ b * (G.payoff i b - G.devPayoff b i (δ (b i))) := by
    rw [hsum]; linarith [hic i δ]
  -- If `a₀` had positive probability, that one term would be strictly negative, forcing the total
  -- (a sum of nonpositive terms) below zero — contradicting the equilibrium inequality.
  by_contra hne
  have hpos0 : 0 < μ a₀ := lt_of_le_of_ne (hpos a₀) (Ne.symm hne)
  have hδ0 : δ (a₀ i) = ai := by rw [hδ]; simp [ha₀]
  have hp0 : G.payoff i a₀ = G.devPayoff a₀ i bi := by rw [← ha₀, G.devPayoff_self]
  have hlt : μ a₀ * (G.payoff i a₀ - G.devPayoff a₀ i (δ (a₀ i))) < 0 := by
    rw [hδ0, hp0]
    exact mul_neg_of_pos_of_neg hpos0 (by linarith [hdom a₀])
  have hsumlt : ∑ b : G.ActionProfile, μ b * (G.payoff i b - G.devPayoff b i (δ (b i))) < 0 := by
    have h := Finset.sum_lt_sum (fun b (_ : b ∈ Finset.univ) => hle b)
      ⟨a₀, Finset.mem_univ a₀, hlt⟩
    simpa only [Finset.sum_const_zero] using h
  linarith [hge, hsumlt]

end StaticGame

end EcoLean.GameTheory
