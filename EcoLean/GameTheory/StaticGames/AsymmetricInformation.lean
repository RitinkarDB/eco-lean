import EcoLean.GameTheory.StaticGames.BayesianGames

/-!
# Games with asymmetric information: ex ante vs. interim (§8.6)

Battigalli–Catonini–De Vito §8.6. A game with *asymmetric information about an initial chance move*
has a chance state `ω ∈ Ω`, priors `pᵢ ∈ Δ(Ω)`, signal functions `τᵢ : Ω → Tᵢ`, and a
state-dependent payoff `ûᵢ : Ω × A → ℝ`. This is exactly the data of a `BayesianGame` (with
`State = Ω`, `signal = τ`, `prior = p`, and the state-dependent `payoff = û`).

The book's §8.6 result is the equivalence between the **ex ante** (strategic-form) Nash equilibrium of
the game `(I, (Σᵢ, Uᵢ))` with `Σᵢ = Aᵢ^Tᵢ` and `Uᵢ(σ) = ∑_ω pᵢ(ω) ûᵢ(ω, σ(τ(ω)))`, and the
**interim** Bayesian Nash equilibrium (`IsBayesianNashEquilibrium`, optimal type by type). We prove the
two coincide (Remark 23): `isExAnteNashEquilibrium_iff_bayesianNashEquilibrium`.

The equivalence is unconditional: the ex ante payoff is the sum over types of the (unnormalised)
interim payoffs, and an ex ante deviation decomposes into independent per-type deviations, so the ex
ante maximisation splits into independent per-type maximisations.
-/

namespace EcoLean.GameTheory

open scoped BigOperators

namespace BayesianGame

variable {G : BayesianGame} [Fintype G.State] [DecidableEq G.Player]
  [∀ i, Fintype (G.PlayerType i)] [∀ i, DecidableEq (G.PlayerType i)]

/-- The **ex ante** (strategic-form) payoff `Uᵢ(σ) = ∑_ω pᵢ(ω) ûᵢ(ω, σ(τ(ω)))`. -/
def exAntePayoff (σ : G.Strategy) (i : G.Player) : ℝ :=
  ∑ ω, G.prior i ω * G.payoff i ω (G.realizedProfile σ ω)

/-- An **ex ante Nash equilibrium**: no player profits by switching to a different type-contingent
strategy `σᵢ'` evaluated at the ex ante stage. -/
def IsExAnteNashEquilibrium (σ : G.Strategy) : Prop :=
  ∀ (i : G.Player) (σᵢ' : G.PlayerType i → G.Action i),
    G.exAntePayoff (Function.update σ i σᵢ') i ≤ G.exAntePayoff σ i

/-- Realising an ex ante deviation `σᵢ'`: player `i` plays `σᵢ'(τᵢ(ω))`, everyone else is unchanged. -/
theorem realizedProfile_update (σ : G.Strategy) (i : G.Player)
    (σᵢ' : G.PlayerType i → G.Action i) (ω : G.State) :
    G.realizedProfile (Function.update σ i σᵢ') ω
      = Function.update (G.realizedProfile σ ω) i (σᵢ' (G.signal i ω)) := by
  funext j
  by_cases h : j = i
  · subst h; simp only [realizedProfile, Function.update_self]
  · simp only [realizedProfile, Function.update_of_ne h]

/-- The ex ante payoff is the sum over types of the (unnormalised) interim payoffs. -/
theorem exAntePayoff_eq_sum_interimPayoff (σ : G.Strategy) (i : G.Player) :
    G.exAntePayoff σ i = ∑ tᵢ, G.interimPayoff σ i tᵢ := by
  simp only [exAntePayoff, interimPayoff]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.sum_ite_eq]
  simp

/-- An ex ante deviation decomposes into independent per-type interim deviations. -/
theorem exAntePayoff_update_eq_sum_interimDevPayoff (σ : G.Strategy) (i : G.Player)
    (σᵢ' : G.PlayerType i → G.Action i) :
    G.exAntePayoff (Function.update σ i σᵢ') i = ∑ tᵢ, G.interimDevPayoff σ i tᵢ (σᵢ' tᵢ) := by
  simp only [exAntePayoff, interimDevPayoff, realizedProfile_update]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [Finset.sum_eq_single (G.signal i ω)
    (fun tᵢ _ hne => by rw [if_neg (Ne.symm hne), zero_mul])
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [if_pos rfl]

/-- **§8.6 (Remark 23).** The ex ante (strategic-form) Nash equilibria of a game with asymmetric
information are exactly its interim Bayesian Nash equilibria. -/
theorem isExAnteNashEquilibrium_iff_bayesianNashEquilibrium (σ : G.Strategy) :
    G.IsExAnteNashEquilibrium σ ↔ G.IsBayesianNashEquilibrium σ := by
  constructor
  · intro hexante i tᵢ aᵢ
    by_contra hlt
    push_neg at hlt
    have hdev := hexante i (Function.update (σ i) tᵢ aᵢ)
    rw [exAntePayoff_update_eq_sum_interimDevPayoff,
      exAntePayoff_eq_sum_interimPayoff] at hdev
    have key : ∀ tⱼ, G.interimPayoff σ i tⱼ
        ≤ G.interimDevPayoff σ i tⱼ ((Function.update (σ i) tᵢ aᵢ) tⱼ) := by
      intro tⱼ
      by_cases h : tⱼ = tᵢ
      · subst h; rw [Function.update_self]; exact le_of_lt hlt
      · rw [Function.update_of_ne h, interimDevPayoff_self]
    have hstrict : G.interimPayoff σ i tᵢ
        < G.interimDevPayoff σ i tᵢ ((Function.update (σ i) tᵢ aᵢ) tᵢ) := by
      rw [Function.update_self]; exact hlt
    exact absurd hdev
      (not_le.mpr (Finset.sum_lt_sum (fun tⱼ _ => key tⱼ) ⟨tᵢ, Finset.mem_univ _, hstrict⟩))
  · intro hbne i σᵢ'
    rw [exAntePayoff_update_eq_sum_interimDevPayoff, exAntePayoff_eq_sum_interimPayoff]
    exact Finset.sum_le_sum (fun tᵢ _ => hbne i tᵢ (σᵢ' tᵢ))

end BayesianGame

end EcoLean.GameTheory
