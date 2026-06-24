import EcoLean.GameTheory.StaticGames.DirectedRationalizability
import EcoLean.GameTheory.StaticGames.MixedStrategies

/-!
# Anonymous self-confirming equilibrium with incomplete information (§8.7.2)

Battigalli–Catonini–De Vito §8.7.2 (anonymous recurrent interaction). A *simple Bayesian game* is a
`PayoffUncertaintyGame` `Ĝ = ⟨I, Θ₀, (Θᵢ, Aᵢ, uᵢ)⟩` together with type-independent priors
`q₀ ∈ Δ(Θ₀)`, `qᵢ ∈ Δ(Θᵢ)`. Each role `i` is filled by agents drawn from a large population; a
*mixed action* `αᵢ(·|θᵢ) ∈ Δ(Aᵢ)` records the fractions of `i`-agents of characteristic `θᵢ` playing
each pure action. Each agent holds a conjecture `μ_{i,θᵢ,aᵢ}` over `Θ₀ × Θ₋ᵢ × A₋ᵢ`.

* `populationBelief` — the independent full-profile distribution induced by `(q₀, q, α)`.
* `messageProb` — the probability of a feedback message under a conjecture (or the population play).
* `IsAnonymousSelfConfirmingEquilibrium` (Definition 42): for every role `i`, characteristic `θᵢ` and
  action `aᵢ` played with positive frequency, `μ_{i,θᵢ,aᵢ}` is a *confirmed best response*.
* `equalizing_principle` — a probability vector maximising a linear functional puts all its mass on
  maximisers.
* `mixedBayesNash_isAnonymousSelfConfirmingEquilibriumProfile` (Remark 29): every mixed Bayes–Nash
  equilibrium of the simple Bayesian game is an anonymous self-confirming equilibrium profile —
  the agents' conjecture is the true population belief, so confirmation is immediate and rationality
  is the equalizing principle.
-/

namespace EcoLean.GameTheory

open scoped BigOperators
open Classical

/-- **Equalizing principle.** If `p ∈ Δ(A)` maximises the linear functional `q ↦ ∑ q a · V a` over the
simplex, then every action in the support of `p` is a maximiser of `V`. -/
theorem equalizing_principle {A : Type*} [Fintype A] {V : A → ℝ} {p : A → ℝ}
    (hp : p ∈ stdSimplex ℝ A)
    (hmax : ∀ b ∈ stdSimplex ℝ A, ∑ a, b a * V a ≤ ∑ a, p a * V a)
    {a₀ : A} (ha₀ : p a₀ ≠ 0) : ∀ a', V a' ≤ V a₀ := by
  set Mx := ∑ a, p a * V a with hMx
  have hdsum : ∀ a', (∑ a, (Pi.single a' (1 : ℝ) : A → ℝ) a * V a) = V a' := by
    intro a'
    rw [Finset.sum_eq_single a' (fun a _ hne => by rw [Pi.single_eq_of_ne hne, zero_mul])
      (fun h => absurd (Finset.mem_univ a') h), Pi.single_eq_same, one_mul]
  have hVle : ∀ a', V a' ≤ Mx := by
    intro a'
    have := hmax _ (single_mem_stdSimplex ℝ a')
    rwa [hdsum a'] at this
  have hsum0 : ∑ a, p a * (Mx - V a) = 0 := by
    have h1 : ∑ a, p a * (Mx - V a) = Mx * (∑ a, p a) - ∑ a, p a * V a := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [h1, hp.2, mul_one, ← hMx, sub_self]
  have hterm : p a₀ * (Mx - V a₀) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => mul_nonneg (hp.1 a) (by linarith [hVle a]))).mp hsum0 a₀ (Finset.mem_univ a₀)
  have hVa₀ : Mx - V a₀ = 0 := by
    rcases mul_eq_zero.mp hterm with h | h
    · exact absurd h ha₀
    · exact h
  intro a'
  linarith [hVle a', hVa₀]

namespace PayoffUncertaintyGame

variable {G : PayoffUncertaintyGame} [Fintype G.Player] [DecidableEq G.Player]
  [Fintype G.Residual] [∀ i, Fintype (G.InfoType i)] [∀ i, Fintype (G.Action i)]
  {M : G.Player → Type*}

/-- The **population belief** induced by type priors `(q₀, q)` and mixed actions `α`: the independent
full-profile distribution with `θ₀ ∼ q₀`, each `θⱼ ∼ qⱼ`, each `aⱼ ∼ αⱼ(·|θⱼ)`. -/
noncomputable def populationBelief (q0 : G.Residual → ℝ) (q : ∀ i, G.InfoType i → ℝ)
    (α : ∀ i, G.InfoType i → G.Action i → ℝ) : G.FullProfile → ℝ :=
  fun fp => q0 fp.1 * ∏ j, (q j (fp.2.1 j) * α j (fp.2.1 j) (fp.2.2 j))

/-- The population belief is a probability distribution over full profiles. -/
theorem populationBelief_isDistribution {q0 : G.Residual → ℝ} {q : ∀ i, G.InfoType i → ℝ}
    {α : ∀ i, G.InfoType i → G.Action i → ℝ} (hq0 : q0 ∈ stdSimplex ℝ G.Residual)
    (hq : ∀ i, q i ∈ stdSimplex ℝ (G.InfoType i))
    (hα : ∀ i θᵢ, α i θᵢ ∈ stdSimplex ℝ (G.Action i)) :
    G.IsDistribution (G.populationBelief q0 q α) := by
  refine ⟨fun fp => mul_nonneg (hq0.1 fp.1) (Finset.prod_nonneg fun j _ =>
    mul_nonneg ((hq j).1 _) ((hα j (fp.2.1 j)).1 _)), ?_⟩
  unfold populationBelief
  rw [Fintype.sum_prod_type]
  have hinner : ∀ θ₀ : G.Residual,
      (∑ ta : (∀ j, G.InfoType j) × (∀ j, G.Action j),
        q0 θ₀ * ∏ j, (q j (ta.1 j) * α j (ta.1 j) (ta.2 j))) = q0 θ₀ := by
    intro θ₀
    rw [← Finset.mul_sum, Fintype.sum_prod_type]
    have hA : ∀ T : ∀ j, G.InfoType j,
        (∑ A : ∀ j, G.Action j, ∏ j, (q j (T j) * α j (T j) (A j))) = ∏ j, q j (T j) := by
      intro T
      rw [Finset.sum_congr rfl fun A _ => (Finset.prod_mul_distrib :
          (∏ j, (q j (T j) * α j (T j) (A j))) = (∏ j, q j (T j)) * ∏ j, α j (T j) (A j)),
        ← Finset.mul_sum]
      rw [show (∑ A : ∀ j, G.Action j, ∏ j, α j (T j) (A j)) = 1 from by
        rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
        exact Finset.prod_eq_one fun j _ => (hα j (T j)).2, mul_one]
    rw [Finset.sum_congr rfl fun T _ => hA T, ← Fintype.piFinset_univ, ← Finset.prod_univ_sum,
      Finset.prod_eq_one fun j _ => (hq j).2, mul_one]
  rw [Finset.sum_congr rfl fun θ₀ _ => hinner θ₀]
  exact hq0.2

/-- The probability that an agent in role `i` with characteristic `θᵢ` playing `aᵢ` receives feedback
message `m`, under belief `μ` over full profiles: the `μ`-mass of profiles whose feedback (with `i`'s
own type `θᵢ` and action `aᵢ`) is `m`. -/
noncomputable def messageProb (f : ∀ i, G.Residual → (∀ j, G.InfoType j) → (∀ j, G.Action j) → M i)
    (i : G.Player) (θᵢ : G.InfoType i) (aᵢ : G.Action i) (μ : G.FullProfile → ℝ) (m : M i) : ℝ :=
  ∑ fp : G.FullProfile,
    if f i fp.1 (Function.update fp.2.1 i θᵢ) (Function.update fp.2.2 i aᵢ) = m then μ fp else 0

/-- **Definition 42.** `(α, μ)` is an *anonymous self-confirming equilibrium* of the simple Bayesian
game with feedback `(BG, f)`: `α` is a population profile of mixed actions, and for every role `i`,
characteristic `θᵢ` and action `aᵢ` played with positive frequency, the conjecture `μ i θᵢ aᵢ` is a
confirmed best response — `aᵢ` maximises `i`'s expected payoff under `μ i θᵢ aᵢ`, and `μ i θᵢ aᵢ`
reproduces the true feedback-message distribution. -/
def IsAnonymousSelfConfirmingEquilibrium
    (q0 : G.Residual → ℝ) (q : ∀ i, G.InfoType i → ℝ)
    (f : ∀ i, G.Residual → (∀ j, G.InfoType j) → (∀ j, G.Action j) → M i)
    (α : ∀ i, G.InfoType i → G.Action i → ℝ)
    (μ : ∀ i, G.InfoType i → G.Action i → G.FullProfile → ℝ) : Prop :=
  (∀ i θᵢ, α i θᵢ ∈ stdSimplex ℝ (G.Action i)) ∧
    ∀ (i : G.Player) (θᵢ : G.InfoType i) (aᵢ : G.Action i), α i θᵢ aᵢ ≠ 0 →
      G.IsDistribution (μ i θᵢ aᵢ) ∧ G.IsBestResponseToBelief (μ i θᵢ aᵢ) i θᵢ aᵢ ∧
        ∀ m : M i, G.messageProb f i θᵢ aᵢ (μ i θᵢ aᵢ) m
          = G.messageProb f i θᵢ aᵢ (G.populationBelief q0 q α) m

/-- `α` is an *anonymous self-confirming equilibrium population profile* if some profile of confirmed
conjectures supports it. -/
def IsAnonymousSelfConfirmingEquilibriumProfile
    (q0 : G.Residual → ℝ) (q : ∀ i, G.InfoType i → ℝ)
    (f : ∀ i, G.Residual → (∀ j, G.InfoType j) → (∀ j, G.Action j) → M i)
    (α : ∀ i, G.InfoType i → G.Action i → ℝ) : Prop :=
  ∃ μ : ∀ i, G.InfoType i → G.Action i → G.FullProfile → ℝ,
    G.IsAnonymousSelfConfirmingEquilibrium q0 q f α μ

/-- A profile of mixed actions `α` is a **mixed Bayes–Nash equilibrium** of the simple Bayesian game:
each type `θᵢ` plays a best mixed reply to the population belief — no mixed deviation `βᵢ` improves
`i`'s interim expected payoff. -/
def IsMixedBayesNashEquilibrium (q0 : G.Residual → ℝ) (q : ∀ i, G.InfoType i → ℝ)
    (α : ∀ i, G.InfoType i → G.Action i → ℝ) : Prop :=
  (∀ i θᵢ, α i θᵢ ∈ stdSimplex ℝ (G.Action i)) ∧
    ∀ (i : G.Player) (θᵢ : G.InfoType i) (βᵢ : G.Action i → ℝ), βᵢ ∈ stdSimplex ℝ (G.Action i) →
      ∑ aᵢ, βᵢ aᵢ * G.expectedPayoff (G.populationBelief q0 q α) i θᵢ aᵢ
        ≤ ∑ aᵢ, α i θᵢ aᵢ * G.expectedPayoff (G.populationBelief q0 q α) i θᵢ aᵢ

/-- **Remark 29.** Every mixed Bayes–Nash equilibrium of a simple Bayesian game is an anonymous
self-confirming equilibrium profile, for any feedback: take each agent's conjecture to be the true
population belief. Confirmation is then immediate (the conjecture *is* the population belief), and
rationality is the equalizing principle — every action played with positive frequency is a pure best
response to the population belief. -/
theorem mixedBayesNash_isAnonymousSelfConfirmingEquilibriumProfile
    {q0 : G.Residual → ℝ} {q : ∀ i, G.InfoType i → ℝ}
    {f : ∀ i, G.Residual → (∀ j, G.InfoType j) → (∀ j, G.Action j) → M i}
    {α : ∀ i, G.InfoType i → G.Action i → ℝ}
    (hq0 : q0 ∈ stdSimplex ℝ G.Residual) (hq : ∀ i, q i ∈ stdSimplex ℝ (G.InfoType i))
    (hα : G.IsMixedBayesNashEquilibrium q0 q α) :
    G.IsAnonymousSelfConfirmingEquilibriumProfile q0 q f α := by
  refine ⟨fun i θᵢ aᵢ => G.populationBelief q0 q α, hα.1, fun i θᵢ aᵢ haᵢ => ?_⟩
  refine ⟨populationBelief_isDistribution hq0 hq hα.1, fun aᵢ' => ?_, fun _ => rfl⟩
  exact equalizing_principle (hα.1 i θᵢ) (fun b hb => hα.2 i θᵢ b hb) haᵢ aᵢ'

end PayoffUncertaintyGame

end EcoLean.GameTheory
