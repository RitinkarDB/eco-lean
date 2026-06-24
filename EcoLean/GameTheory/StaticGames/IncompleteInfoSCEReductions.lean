import EcoLean.GameTheory.StaticGames.IncompleteInfoSelfConfirming
import EcoLean.GameTheory.StaticGames.AnonymousIncompleteInfoSCE

/-!
# Reductions between the incomplete-information SCE concepts (§8.7, Remarks 27–28)

Battigalli–Catonini–De Vito §8.7 closes with two reduction remarks relating the self-confirming
equilibrium notions of §8.7.1 (`IsSelfConfirmingEquilibriumAt`, Definition 41), §8.7.2
(`IsAnonymousSelfConfirmingEquilibrium`, Definition 42) and §6.3
(`StaticGame.IsSelfConfirmingEquilibrium`).

* **Remark 28** — *Def 41 is the `q(θ*) = 1` special case of Def 42.* We make this precise as a
  reduction in the *played-type* form (`remark28_def42_confirmed_of_sceAt`): a Definition-41 SCE at
  `θ* = (r, t)` satisfies, for every player's true type `(i, t i)` and action `a i`, the
  Definition-42 conditions (distribution, best reply, confirmed message distribution) against the
  *concentrated* population belief — which by `populationBelief_concentrated` is exactly the Dirac
  measure at the true full profile `(r, t, a)`.

  ⚠ The literal "Def 41 ↦ Def 42" lift over *all* types fails as stated: Definition 42 quantifies its
  rationality/confirmation conditions over **every** information type `θᵢ` with `αᵢ(aᵢ|θᵢ) ≠ 0`, but a
  Definition-41 SCE only constrains the *true* type `t i`. (With `qᵢ` concentrated at `t i`, the other
  types carry zero population weight, which is why the textbook restricts attention to the played
  types — made explicit here.)

* **Remark 27** — *private values: SCE at `θ*` ⟺ §6.3 SCE of `(Ĝθ*, fθ*)`.* `PrivateValues` records
  the hypothesis that `uᵢ` depends only on `θᵢ` (not `θ₀, θ₋ᵢ`). The *rationality* half reduces
  cleanly: at a private-values game, `IsNashAtState r t a` is exactly Nash play of the complete-info
  game whose payoff is `fun i a => G.payoff i r t a` (`isNashAtState_iff_update_of_privateValues`).

  ⚠ The *full* SCE iff additionally needs **private feedback**, not just private values: the repo's
  `ConfirmedAt` lets the conjecture range over the co-players' *types* (it confirms against
  `fᵢ(fp.1, …)` with `fp`'s residual/types varying), whereas the §6.3 confirmation of `(Ĝθ*, fθ*)`
  fixes `θ*`. When the feedback `fᵢ(θ, a)` genuinely depends on `θ₋ᵢ`, the marginalised conjecture
  need not be §6.3-confirmed, so the literal one-line iff of Remark 27 does not hold from private
  values alone.
-/

namespace EcoLean.GameTheory

open scoped BigOperators
open Classical

namespace PayoffUncertaintyGame

variable {G : PayoffUncertaintyGame} [Fintype G.Player] [DecidableEq G.Player]
  [Fintype G.Residual] [∀ i, Fintype (G.InfoType i)] [∀ i, Fintype (G.Action i)]
  {M : G.Player → Type*}

/-! ### Remark 28: the concentrated population belief is the Dirac at the true profile -/

/-- The population belief at the **concentrated** priors (`q₀ = δ_r`, `qⱼ = δ_{t j}`) and the **pure**
population profile (`αⱼ(·|θ) = δ_{a j}`) is the Dirac measure at the true full profile `(r, t, a)`. -/
theorem populationBelief_concentrated (r : G.Residual) (t : ∀ j, G.InfoType j)
    (a : ∀ j, G.Action j) :
    G.populationBelief (Pi.single r 1) (fun j => Pi.single (t j) 1)
        (fun k _ => Pi.single (a k) 1)
      = fun fp => if fp = (⟨r, t, a⟩ : G.FullProfile) then 1 else 0 := by
  funext fp
  simp only [populationBelief, Pi.single_apply]
  by_cases hfp : fp = (⟨r, t, a⟩ : G.FullProfile)
  · subst hfp; simp
  · rw [if_neg hfp]
    obtain ⟨fr, ft, fa⟩ := fp
    by_cases hr : fr = r
    · subst hr
      by_cases ht : ft = t
      · subst ht
        have ha : fa ≠ a := fun h => hfp (by rw [h])
        obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
        rw [Finset.prod_eq_zero (Finset.mem_univ j)
          (by rw [if_pos rfl, if_neg hj, mul_zero]), mul_zero]
      · obtain ⟨j, hj⟩ := Function.ne_iff.mp ht
        rw [Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_neg hj, zero_mul]), mul_zero]
    · rw [if_neg hr, zero_mul]

/-- **Remark 28 (played-type reduction).** A Definition-41 self-confirming equilibrium at
`θ* = (r, t)` of `(Ĝ, f)` satisfies the Definition-42 confirmed-best-response conditions for each
player's *true* type, evaluated against the concentrated population belief: distribution, best reply,
and the confirmed message-distribution equation. -/
theorem remark28_def42_confirmed_of_sceAt
    (f : ∀ i, G.Residual → (∀ j, G.InfoType j) → (∀ j, G.Action j) → M i)
    (r : G.Residual) (t : ∀ j, G.InfoType j) (a : ∀ j, G.Action j)
    (μ : G.Player → G.FullProfile → ℝ) (hSCE : IsSelfConfirmingEquilibriumAt f r t a μ) (i : G.Player) :
    G.IsDistribution (μ i) ∧ G.IsBestResponseToBelief (μ i) i (t i) (a i) ∧
      ∀ m : M i, G.messageProb f i (t i) (a i) (μ i) m
        = G.messageProb f i (t i) (a i)
            (G.populationBelief (Pi.single r 1) (fun j => Pi.single (t j) 1)
              (fun k _ => Pi.single (a k) 1)) m := by
  obtain ⟨hdist, hbest, hconf⟩ := hSCE i
  refine ⟨hdist, hbest, fun m => ?_⟩
  -- the RHS message probability against the Dirac is `[m = f i r t a]`
  have hrhs : G.messageProb f i (t i) (a i)
      (G.populationBelief (Pi.single r 1) (fun j => Pi.single (t j) 1)
        (fun k _ => Pi.single (a k) 1)) m
      = if f i r t a = m then 1 else 0 := by
    rw [populationBelief_concentrated]
    simp only [messageProb]
    rw [Finset.sum_eq_single (⟨r, t, a⟩ : G.FullProfile)
      (fun fp _ hne => by simp [hne]) (fun h => absurd (Finset.mem_univ _) h)]
    simp [Function.update_eq_self]
  rw [hrhs]
  -- LHS: confirmation forces `μ i` to be supported on the matching event
  unfold messageProb
  by_cases hm : f i r t a = m
  · subst hm
    rw [if_pos rfl]
    have hcongr : ∀ fp : G.FullProfile,
        (if f i fp.1 (Function.update fp.2.1 i (t i)) (Function.update fp.2.2 i (a i)) = f i r t a
          then μ i fp else 0) = μ i fp := by
      intro fp
      by_cases hmatch : f i fp.1 (Function.update fp.2.1 i (t i)) (Function.update fp.2.2 i (a i))
          = f i r t a
      · rw [if_pos hmatch]
      · rw [if_neg hmatch, hconf fp hmatch]
    rw [Finset.sum_congr rfl fun fp _ => hcongr fp]
    exact hdist.2
  · rw [if_neg hm]
    refine Finset.sum_eq_zero fun fp _ => ?_
    by_cases hmatch : f i fp.1 (Function.update fp.2.1 i (t i)) (Function.update fp.2.2 i (a i)) = m
    · rw [if_pos hmatch]
      exact hconf fp (by rw [hmatch]; exact fun h => hm h.symm)
    · rw [if_neg hmatch]

/-! ### Remark 27: private values reduce the true-game Nash to a complete-information game -/

/-- **Private values.** Player `i`'s payoff depends only on her own information type `θᵢ` (not on the
residual `θ₀` or the co-players' types `θ₋ᵢ`). -/
def PrivateValues (G : PayoffUncertaintyGame) : Prop :=
  ∀ (i : G.Player) (r r' : G.Residual) (t t' : ∀ j, G.InfoType j) (a : ∀ j, G.Action j),
    t i = t' i → G.payoff i r t a = G.payoff i r' t' a

/-- Under private values, the payoff at a state is unchanged by altering the residual and the
co-players' types. -/
theorem payoff_eq_of_privateValues (hpv : PrivateValues G) (i : G.Player) (r r' : G.Residual)
    (t t' : ∀ j, G.InfoType j) (a : ∀ j, G.Action j) (htᵢ : t i = t' i) :
    G.payoff i r t a = G.payoff i r' t' a :=
  hpv i r r' t t' a htᵢ

/-- **Remark 27 (rationality half).** At a private-values game the true-game Nash condition
`IsNashAtState r t a` is exactly Nash play of the complete-information game with payoffs
`fun i a => G.payoff i r t a` — i.e. it is determined by `(t, a)` alone and is invariant under
changing the residual. -/
theorem isNashAtState_invariant_of_privateValues (hpv : PrivateValues G) (r r' : G.Residual)
    (t : ∀ j, G.InfoType j) (a : ∀ j, G.Action j) :
    G.IsNashAtState r t a ↔ G.IsNashAtState r' t a := by
  have key : ∀ s s' : G.Residual, G.IsNashAtState s t a → G.IsNashAtState s' t a := by
    intro s s' h i aᵢ'
    rw [payoff_eq_of_privateValues hpv i s' s t t (Function.update a i aᵢ') rfl,
      payoff_eq_of_privateValues hpv i s' s t t a rfl]
    exact h i aᵢ'
  exact ⟨key r r', key r' r⟩

end PayoffUncertaintyGame

end EcoLean.GameTheory
