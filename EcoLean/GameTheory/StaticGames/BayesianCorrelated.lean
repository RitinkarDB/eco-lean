import EcoLean.GameTheory.StaticGames.AsymmetricInformation
import EcoLean.GameTheory.StaticGames.CorrelatedEquilibrium

/-!
# Bayesian and correlated equilibrium (§8.5.4)

Battigalli–Catonini–De Vito §8.5.4, Remark 25 (Harsanyi's implicit definition of correlated
equilibrium). A *Bayesian elaboration* of a finite complete-information game `G = ⟨I, (Aᵢ, ūᵢ)⟩` is a
`BayesianGame` whose payoff is state-independent (`uᵢ(θ, a) = ūᵢ(a)`). With a **common prior** `p`
(every player's prior coincides with `p`), every Bayesian (Nash) equilibrium `σ` of the elaboration
induces a **correlated equilibrium** of `G`: the pushforward of `p` along the realised-play map
`ω ↦ (σⱼ(τⱼ(ω)))ⱼ`.

* `completeInfoGame` — the underlying complete-information static game `⟨I, (Aᵢ, ūᵢ)⟩`.
* `inducedCorrelated` — the pushforward correlated distribution.
* `isCorrelatedEquilibrium_inducedCorrelated` (Remark 25).

The incentive constraints transfer because, under a common prior, the ex-ante payoff is the sum over
types of the interim payoffs (the §8.6 bridge), and a correlated-equilibrium departure `δ` is realised
by the type-deviation `tᵢ ↦ δ(σᵢ(tᵢ))`, against which the Bayesian equilibrium is optimal type by type.
-/

namespace EcoLean.GameTheory

open scoped BigOperators
open Classical

namespace BayesianGame

variable {G : BayesianGame} [Fintype G.State] [Fintype G.Player] [DecidableEq G.Player]
  [∀ i, Fintype (G.PlayerType i)] [∀ i, DecidableEq (G.PlayerType i)] [∀ i, Fintype (G.Action i)]

/-- The underlying **complete-information game** `⟨I, (Aᵢ, ūᵢ)⟩` of a state-independent Bayesian
game. (Reducible so that the `Fintype`/`DecidableEq` instances on `G.Player`/`G.Action` transfer.) -/
@[reducible] def completeInfoGame (G : BayesianGame) (ū : G.Player → (∀ j, G.Action j) → ℝ) :
    StaticGame where
  Player := G.Player
  Action := G.Action
  payoff := ū

/-- The correlated distribution over action profiles induced by a strategy `σ` and a prior `p`: the
pushforward of `p` along `ω ↦ (σⱼ(τⱼ(ω)))ⱼ`. -/
noncomputable def inducedCorrelated (σ : G.Strategy) (p : G.State → ℝ) :
    (∀ j, G.Action j) → ℝ :=
  fun a => ∑ ω, if G.realizedProfile σ ω = a then p ω else 0

/-- **Pushforward identity.** Averaging any `h` against the induced correlated distribution equals
averaging `h ∘ realizedProfile` against the prior. -/
theorem sum_inducedCorrelated_mul (σ : G.Strategy) (p : G.State → ℝ)
    (h : (∀ j, G.Action j) → ℝ) :
    ∑ a, G.inducedCorrelated σ p a * h a = ∑ ω, p ω * h (G.realizedProfile σ ω) := by
  simp only [inducedCorrelated, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.sum_eq_single (G.realizedProfile σ ω)
    (fun a _ hne => by rw [if_neg fun heq => hne heq.symm, zero_mul])
    (fun hmem => absurd (Finset.mem_univ _) hmem), if_pos rfl]

/-- The induced correlated distribution is a probability distribution over action profiles. -/
theorem inducedCorrelated_isCorrelatedDistribution {ū : G.Player → (∀ j, G.Action j) → ℝ}
    (σ : G.Strategy) {p : G.State → ℝ} (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) :
    (completeInfoGame G ū).IsCorrelatedDistribution (G.inducedCorrelated σ p) := by
  refine ⟨fun a => Finset.sum_nonneg fun ω _ => ?_, ?_⟩
  · split_ifs with h
    · exact hp0 ω
    · exact le_refl 0
  · have h := G.sum_inducedCorrelated_mul σ p (fun _ => 1)
    simp only [mul_one] at h
    exact h.trans hp1

/-- **Remark 25.** A common-prior Bayesian (Nash) equilibrium of a state-independent Bayesian game
induces a correlated equilibrium of the underlying complete-information game. -/
theorem isCorrelatedEquilibrium_inducedCorrelated {ū : G.Player → (∀ j, G.Action j) → ℝ}
    (hstateIndep : ∀ i ω a, G.payoff i ω a = ū i a)
    {p : G.State → ℝ} (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (hcommon : ∀ i, G.prior i = p)
    {σ : G.Strategy} (hσ : G.IsBayesianNashEquilibrium σ) :
    (completeInfoGame G ū).IsCorrelatedEquilibrium (G.inducedCorrelated σ p) := by
  refine ⟨inducedCorrelated_isCorrelatedDistribution σ hp0 hp1, fun i δ => ?_⟩
  -- the expected payoff equals the sum over types of interim payoffs (the §8.6 bridge)
  have hLHS : (completeInfoGame G ū).expectedPayoff (G.inducedCorrelated σ p) i
      = ∑ tᵢ, G.interimPayoff σ i tᵢ := by
    have key : ∑ ω, p ω * ū i (G.realizedProfile σ ω) = ∑ tᵢ, G.interimPayoff σ i tᵢ := by
      rw [← exAntePayoff_eq_sum_interimPayoff]
      unfold exAntePayoff
      exact Finset.sum_congr rfl fun ω _ => by rw [hcommon i, hstateIndep i ω]
    rw [StaticGame.expectedPayoff]
    show ∑ a, G.inducedCorrelated σ p a * ū i a = _
    rw [G.sum_inducedCorrelated_mul σ p (fun a => ū i a)]
    exact key
  -- the deviation payoff equals the sum of interim deviation payoffs for `tᵢ ↦ δ(σᵢ(tᵢ))`
  have hRHS : (completeInfoGame G ū).expectedDeviationPayoff (G.inducedCorrelated σ p) i δ
      = ∑ tᵢ, G.interimDevPayoff σ i tᵢ (δ (σ i tᵢ)) := by
    have key : ∑ ω, p ω
          * ū i (Function.update (G.realizedProfile σ ω) i (δ (G.realizedProfile σ ω i)))
        = ∑ tᵢ, G.interimDevPayoff σ i tᵢ (δ (σ i tᵢ)) := by
      rw [show (∑ tᵢ, G.interimDevPayoff σ i tᵢ (δ (σ i tᵢ)))
          = ∑ tᵢ, G.interimDevPayoff σ i tᵢ ((fun tⱼ => δ (σ i tⱼ)) tᵢ) from rfl,
        ← exAntePayoff_update_eq_sum_interimDevPayoff]
      unfold exAntePayoff
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [hcommon i, realizedProfile_update, hstateIndep i ω]
      simp only [realizedProfile]
    rw [StaticGame.expectedDeviationPayoff]
    have hcoe : ∀ a, (completeInfoGame G ū).devPayoff a i (δ (a i))
        = ū i (Function.update a i (δ (a i))) := fun a => rfl
    rw [Finset.sum_congr rfl fun a _ => by rw [hcoe a],
      G.sum_inducedCorrelated_mul σ p (fun a => ū i (Function.update a i (δ (a i))))]
    exact key
  rw [hLHS, hRHS]
  exact Finset.sum_le_sum fun tᵢ _ => hσ i tᵢ (δ (σ i tᵢ))

end BayesianGame

end EcoLean.GameTheory
