import EcoLean.GameTheory.StaticGames.DirectedRationalizability

/-!
# Self-confirming equilibrium with incomplete information (§8.7.1)

Battigalli–Catonini–De Vito §8.7.1 (long-run interaction). Fix a game with payoff uncertainty
`Ĝ = ⟨I, Θ₀, (Θᵢ, Aᵢ, uᵢ)⟩` (a `PayoffUncertaintyGame`) together with a profile of feedback
functions `fᵢ : Θ × A → Mᵢ`, and a *true state of nature* `θ* = (r, t)` (residual `r`, information
types `t`). A profile of actions and conjectures `(a*ᵢ, μᵢ)` is a **self-confirming equilibrium at
θ*** (Definition 41) when, for every `i`:

* (rationality) `a*ᵢ` is a best reply for type `tᵢ` to `μᵢ` (`IsBestResponseToBelief`);
* (confirmed conjectures) `μᵢ` puts probability one on the event that the feedback `i` would observe
  matches the feedback actually generated at `(θ*, a*)`.

The headline result is **Remark 26**: every Nash equilibrium of the true game `Ĝθ*` is a
self-confirming-equilibrium action profile at `θ*` — witnessed by the Dirac conjecture concentrated on
the true full profile. (The incomplete-information generalisation of §6.3's `nash ⟹ SCE`.)
-/

namespace EcoLean.GameTheory

open scoped BigOperators

namespace PayoffUncertaintyGame

variable {G : PayoffUncertaintyGame} [Fintype G.Player] [DecidableEq G.Player]
  [Fintype G.Residual] [∀ i, Fintype (G.InfoType i)] [∀ i, Fintype (G.Action i)]
  {M : G.Player → Type*}
  (f : ∀ i, G.Residual → (∀ j, G.InfoType j) → (∀ j, G.Action j) → M i)

/-- The **true game `Ĝθ*`** at a state of nature `(r, t)` has a Nash equilibrium `a` when no player
profits by unilaterally deviating, evaluating payoffs at the true state. -/
def IsNashAtState (r : G.Residual) (t : ∀ j, G.InfoType j) (a : ∀ j, G.Action j) : Prop :=
  ∀ (i : G.Player) (aᵢ' : G.Action i),
    G.payoff i r t (Function.update a i aᵢ') ≤ G.payoff i r t a

/-- Conjecture `μ` of player `i` is **confirmed** at the true state `(r, t)` and action profile `a`:
`μ` puts no weight on full profiles whose induced feedback (with `i`'s own type `tᵢ` and action `aᵢ`)
differs from the feedback actually generated at `(θ*, a*)`. (Probability one on the matching event.) -/
def ConfirmedAt (μ : G.FullProfile → ℝ) (i : G.Player) (r : G.Residual) (t : ∀ j, G.InfoType j)
    (a : ∀ j, G.Action j) : Prop :=
  ∀ fp : G.FullProfile,
    f i fp.1 (Function.update fp.2.1 i (t i)) (Function.update fp.2.2 i (a i)) ≠ f i r t a →
      μ fp = 0

/-- **Definition 41.** `(a, μ)` is a *self-confirming equilibrium at `θ* = (r, t)`* of the game with
payoff uncertainty and feedback `(Ĝ, f)`: every player's action is a best reply to a confirmed
conjecture. -/
def IsSelfConfirmingEquilibriumAt (r : G.Residual) (t : ∀ j, G.InfoType j) (a : ∀ j, G.Action j)
    (μ : G.Player → G.FullProfile → ℝ) : Prop :=
  ∀ i, G.IsDistribution (μ i) ∧ G.IsBestResponseToBelief (μ i) i (t i) (a i) ∧
    ConfirmedAt f (μ i) i r t a

/-- `a` is a *self-confirming-equilibrium action profile at `θ*`* if some profile of conjectures makes
it one. -/
def IsSelfConfirmingEquilibriumActionProfileAt (r : G.Residual) (t : ∀ j, G.InfoType j)
    (a : ∀ j, G.Action j) : Prop :=
  ∃ μ : G.Player → G.FullProfile → ℝ, IsSelfConfirmingEquilibriumAt f r t a μ

/-- **Remark 26.** Every Nash equilibrium of the true game `Ĝθ*` is a self-confirming-equilibrium
action profile at `θ*` of the game with payoff uncertainty and feedback `(Ĝ, f)`. The witnessing
conjecture for each player is the Dirac measure on the true full profile `(r, t, a)`. -/
theorem isSCEActionProfileAt_of_isNashAtState (r : G.Residual) (t : ∀ j, G.InfoType j)
    (a : ∀ j, G.Action j) (hNash : G.IsNashAtState r t a) :
    IsSelfConfirmingEquilibriumActionProfileAt f r t a := by
  classical
  refine ⟨fun _ fp => if fp = (⟨r, t, a⟩ : G.FullProfile) then 1 else 0, fun i => ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
  · -- nonnegativity
    intro fp
    by_cases h : fp = (⟨r, t, a⟩ : G.FullProfile) <;> simp [h]
  · -- total mass one
    simp only [Finset.sum_ite_eq' Finset.univ (⟨r, t, a⟩ : G.FullProfile)]
    simp
  · -- rationality: the Dirac expected payoff is the true-state payoff, so best reply = Nash
    have hexp : ∀ aᵢ', G.expectedPayoff
        (fun fp => if fp = (⟨r, t, a⟩ : G.FullProfile) then 1 else 0) i (t i) aᵢ'
        = G.payoff i r (Function.update t i (t i)) (Function.update a i aᵢ') := by
      intro aᵢ'
      simp only [expectedPayoff, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ (⟨r, t, a⟩ : G.FullProfile)]
      simp
    intro aᵢ'
    rw [hexp aᵢ', hexp (a i)]
    simp only [Function.update_eq_self]
    exact hNash i aᵢ'
  · -- confirmed conjectures: the Dirac support `{(r,t,a)}` lies in the matching event
    intro fp hmismatch
    by_cases h : fp = (⟨r, t, a⟩ : G.FullProfile)
    · exfalso; apply hmismatch; subst h; simp
    · simp [h]

end PayoffUncertaintyGame

end EcoLean.GameTheory
