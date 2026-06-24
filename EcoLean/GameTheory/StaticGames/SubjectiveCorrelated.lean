import EcoLean.GameTheory.StaticGames.BayesianCorrelated
import EcoLean.GameTheory.StaticGames.CorrelatedRationalizability

/-!
# Subjective correlated equilibrium and rationalizability (§8.5.5, Theorem 32 — easy direction)

Battigalli–Catonini–De Vito §8.5.5. A *subjective correlated equilibrium* of a complete-information
game `G` is a Bayesian (Nash) equilibrium of a state-independent Bayesian elaboration of `G` — with
**no common-prior assumption**. Theorem 32 states that an action profile is correlated-rationalizable
iff it is selected in such an equilibrium.

This file proves the **easy direction (⟸)**: every action played by some type in an equilibrium `σ`
of a subjective elaboration is correlated-rationalizable. The set `Cᵢ = σᵢ(Tᵢ)` of played actions is
a *correlated-best-response set* — each played action `σᵢ(tᵢ)` is a best reply to the conjecture
`inducedConjecture σ i tᵢ` (the normalised pushforward of `i`'s interim belief along the realised-play
map), which is supported on `C` and against which optimality is exactly the Bayesian-equilibrium
condition (up to the positive normalising constant `typeMass i tᵢ`). The existing bridge
`subset_correlatedRationalizable_of_isCorrelatedBestResponseSet` then concludes.

* `typeMass`, `inducedConjecture`, `sum_inducedConjecture_unnorm_mul` (pushforward identity).
* `correlatedRationalizable_of_subjectiveElaboration_equilibrium` (Theorem 32, ⟸).
-/

namespace EcoLean.GameTheory

open scoped BigOperators
open Classical

namespace BayesianGame

variable {G : BayesianGame} [Fintype G.State] [Fintype G.Player] [DecidableEq G.Player]
  [∀ i, Fintype (G.PlayerType i)] [∀ i, DecidableEq (G.PlayerType i)] [∀ i, Fintype (G.Action i)]

/-- The prior probability that player `i` has type `tᵢ`. -/
noncomputable def typeMass (i : G.Player) (tᵢ : G.PlayerType i) : ℝ :=
  ∑ ω, if G.signal i ω = tᵢ then G.prior i ω else 0

/-- The conjecture induced by type `tᵢ`: the normalised pushforward of `i`'s interim belief along the
realised-play map `ω ↦ (σⱼ(τⱼ(ω)))ⱼ`. -/
noncomputable def inducedConjecture (σ : G.Strategy) (i : G.Player) (tᵢ : G.PlayerType i) :
    (∀ j, G.Action j) → ℝ :=
  fun a => (∑ ω, if G.signal i ω = tᵢ ∧ G.realizedProfile σ ω = a then G.prior i ω else 0)
    / G.typeMass i tᵢ

/-- **Pushforward identity** (against the *unnormalised* induced conjecture): averaging `h` equals
averaging `h ∘ realizedProfile` over the states consistent with type `tᵢ`. -/
theorem sum_inducedConjecture_unnorm_mul (σ : G.Strategy) (i : G.Player) (tᵢ : G.PlayerType i)
    (h : (∀ j, G.Action j) → ℝ) :
    ∑ a, (∑ ω, if G.signal i ω = tᵢ ∧ G.realizedProfile σ ω = a then G.prior i ω else 0) * h a
      = ∑ ω, (if G.signal i ω = tᵢ then G.prior i ω else 0) * h (G.realizedProfile σ ω) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hsig : G.signal i ω = tᵢ
  · rw [if_pos hsig, Finset.sum_eq_single (G.realizedProfile σ ω)
      (fun a _ hne => by rw [if_neg (fun hc => hne hc.2.symm), zero_mul])
      (fun hmem => absurd (Finset.mem_univ _) hmem), if_pos ⟨hsig, rfl⟩]
  · rw [if_neg hsig, zero_mul,
      Finset.sum_eq_zero fun a _ => by rw [if_neg (fun hc => hsig hc.1), zero_mul]]

/-- The total unnormalised mass of the induced conjecture is `typeMass i tᵢ`. -/
theorem sum_inducedConjecture_unnorm (σ : G.Strategy) (i : G.Player) (tᵢ : G.PlayerType i) :
    (∑ a, ∑ ω, if G.signal i ω = tᵢ ∧ G.realizedProfile σ ω = a then G.prior i ω else 0)
      = G.typeMass i tᵢ := by
  have := G.sum_inducedConjecture_unnorm_mul σ i tᵢ (fun _ => 1)
  simpa [typeMass] using this

variable {ū : G.Player → (∀ j, G.Action j) → ℝ}

/-- The induced conjecture is a probability distribution (given a positive type mass and a nonnegative
prior). -/
theorem inducedConjecture_isCorrelatedDistribution (hprior : ∀ i ω, 0 ≤ G.prior i ω)
    {i : G.Player} {tᵢ : G.PlayerType i} (hpos : 0 < G.typeMass i tᵢ) (σ : G.Strategy) :
    (completeInfoGame G ū).IsCorrelatedDistribution (G.inducedConjecture σ i tᵢ) := by
  refine ⟨fun a => div_nonneg (Finset.sum_nonneg fun ω _ => ?_) (le_of_lt hpos), ?_⟩
  · split_ifs with h
    · exact hprior i ω
    · exact le_refl 0
  · unfold inducedConjecture
    rw [← Finset.sum_div, sum_inducedConjecture_unnorm, div_self (ne_of_gt hpos)]

/-- The induced conjecture is supported on the played-action restriction `Cⱼ = σⱼ(Tⱼ)`. -/
theorem inducedConjecture_supportedOn {i : G.Player} {tᵢ : G.PlayerType i} (σ : G.Strategy) :
    (completeInfoGame G ū).BeliefSupportedOn (G.inducedConjecture σ i tᵢ)
      (fun j => {aⱼ | ∃ tⱼ, σ j tⱼ = aⱼ}) i := by
  rintro a ⟨j, _, hjC⟩
  unfold inducedConjecture
  rw [div_eq_zero_iff]
  left
  exact Finset.sum_eq_zero fun ω _ =>
    if_neg (fun hc => hjC ⟨G.signal j ω, congrFun hc.2 j⟩)

/-- Best-reply payoff against the induced conjecture is the interim deviation payoff, scaled by the
(positive) type mass. -/
theorem sum_inducedConjecture_devPayoff (hstateIndep : ∀ i ω a, G.payoff i ω a = ū i a)
    (σ : G.Strategy) (i : G.Player) (tᵢ : G.PlayerType i) (ci : G.Action i) :
    (∑ a, G.inducedConjecture σ i tᵢ a * (completeInfoGame G ū).devPayoff a i ci)
      = G.interimDevPayoff σ i tᵢ ci / G.typeMass i tᵢ := by
  unfold inducedConjecture
  simp only [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  have hdev : ∀ a, (completeInfoGame G ū).devPayoff a i ci = ū i (Function.update a i ci) :=
    fun _ => rfl
  simp only [hdev]
  rw [G.sum_inducedConjecture_unnorm_mul σ i tᵢ (fun a => ū i (Function.update a i ci))]
  unfold interimDevPayoff
  exact Finset.sum_congr rfl fun ω _ => by rw [hstateIndep i ω]

/-- **Theorem 32 (⟸).** In a subjective Bayesian elaboration (state-independent payoffs, every type of
positive probability), every action played by some type in a Bayesian Nash equilibrium is
correlated-rationalizable in the underlying complete-information game. -/
theorem correlatedRationalizable_of_subjectiveElaboration_equilibrium
    (hstateIndep : ∀ i ω a, G.payoff i ω a = ū i a) (hprior : ∀ i ω, 0 ≤ G.prior i ω)
    (hpos : ∀ i tᵢ, 0 < G.typeMass i tᵢ) {σ : G.Strategy} (hσ : G.IsBayesianNashEquilibrium σ)
    (i : G.Player) (ω : G.State) :
    G.realizedProfile σ ω i ∈ (completeInfoGame G ū).CorrelatedRationalizable i := by
  have hCBR : (completeInfoGame G ū).IsCorrelatedBestResponseSet
      (fun j => {aⱼ | ∃ tⱼ, σ j tⱼ = aⱼ}) := by
    rintro j aⱼ ⟨tⱼ, rfl⟩
    refine ⟨G.inducedConjecture σ j tⱼ,
      inducedConjecture_isCorrelatedDistribution hprior (hpos j tⱼ) σ,
      inducedConjecture_supportedOn σ, fun ci => ?_⟩
    rw [sum_inducedConjecture_devPayoff hstateIndep, sum_inducedConjecture_devPayoff hstateIndep]
    rw [div_le_div_iff_of_pos_right (hpos j tⱼ)]
    have hself : G.interimDevPayoff σ j tⱼ (σ j tⱼ) = G.interimPayoff σ j tⱼ :=
      G.interimDevPayoff_self σ j tⱼ
    rw [hself]
    exact hσ j tⱼ ci
  exact StaticGame.subset_correlatedRationalizable_of_isCorrelatedBestResponseSet hCBR i
    ⟨G.signal i ω, rfl⟩

end BayesianGame

end EcoLean.GameTheory
