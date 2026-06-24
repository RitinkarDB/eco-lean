import EcoLean.GameTheory.StaticGames.PearceBernheim

/-!
# Self-confirming equilibrium

Following Battigalli–Catonini–De Vito §6.3. A **game with feedback** equips a static game with, for
each player `i`, a message set `M i` and a feedback function `f i : ActionProfile → M i` describing
what `i` observes ex post. A **self-confirming equilibrium** (Definition 26) is a profile of actions
and conjectures `(a, μ)` such that for every player `i`:

* (rationality) `a i` is a best response to the conjecture `μ i`, and
* (confirmed conjectures) `μ i` assigns probability one to the opponent profiles producing the same
  feedback (under `i`'s own action `a i`) as the actual play `a`.

A *self-confirming equilibrium action profile* is one supported by some confirmed conjecture profile.
Self-confirming equilibrium is a steady state of learning from personal experience: players need not
know they hold incorrect beliefs, because the feedback never contradicts them.

Main results:

* `nash_isSelfConfirmingEquilibriumActionProfile` — every Nash equilibrium is a self-confirming
  equilibrium action profile, for *any* feedback (Battigalli, Remark 17): the point belief at the
  actual play is a confirmed conjecture justifying the equilibrium action.
* `isSelfConfirmingEquilibrium_not_mixedStrictlyDominated` — self-confirming-equilibrium actions are
  justifiable: never strictly dominated by a mixed strategy.
* `isNashEquilibrium_of_perfectFeedback` — under *perfect feedback* (each player observes the whole
  action profile) the self-confirming and Nash equilibria coincide.
-/

namespace EcoLean.GameTheory

namespace StaticGame

open scoped BigOperators

variable {G : StaticGame} [Fintype G.Player] [DecidableEq G.Player] [∀ i, Fintype (G.Action i)]
  {M : G.Player → Type*}

/-- `(a, μ)` is a **self-confirming equilibrium** of the game with feedback `f`: each player's action
is a best response to their conjecture, and the conjecture is *confirmed* — it places weight only on
opponent profiles that yield the same feedback (under `i`'s own action) as the actual play. -/
def IsSelfConfirmingEquilibrium (f : ∀ i, G.ActionProfile → M i) (a : G.ActionProfile)
    (μ : G.Player → G.ActionProfile → ℝ) : Prop :=
  ∀ i : G.Player, G.IsCorrelatedDistribution (μ i) ∧ G.IsBestResponseToBelief (μ i) i (a i) ∧
    ∀ b : G.ActionProfile, 0 < μ i b → f i (G.deviate b i (a i)) = f i a

/-- `a` is a **self-confirming equilibrium action profile** of `(G, f)`: it is supported by some
profile of confirmed conjectures. -/
def IsSelfConfirmingEquilibriumActionProfile (f : ∀ i, G.ActionProfile → M i)
    (a : G.ActionProfile) : Prop :=
  ∃ μ : G.Player → G.ActionProfile → ℝ, G.IsSelfConfirmingEquilibrium f a μ

variable {f : ∀ i, G.ActionProfile → M i}

/-- **Every Nash equilibrium is a self-confirming equilibrium action profile** (Battigalli, Remark
17), for any feedback: the point (Dirac) belief at the actual play is a confirmed conjecture to which
the equilibrium action is a best response. -/
theorem nash_isSelfConfirmingEquilibriumActionProfile {a : G.ActionProfile}
    (hNash : G.IsNashEquilibrium a) : G.IsSelfConfirmingEquilibriumActionProfile f a := by
  refine ⟨fun _ => G.dirac a, fun i => ⟨⟨fun b => by simp only [dirac]; split_ifs <;> norm_num,
    by simpa using sum_dirac_mul a (fun _ => (1 : ℝ))⟩, ?_, ?_⟩⟩
  · intro ci
    rw [sum_dirac_mul, sum_dirac_mul, G.devPayoff_self]
    exact hNash i ci
  · intro b hb
    have hba : b = a := by by_contra hne; simp only [dirac, if_neg hne, lt_self_iff_false] at hb
    rw [hba, G.deviate_eq_self]

/-- Self-confirming-equilibrium actions are *justifiable*: being best responses to a conjecture, they
are never strictly dominated by a mixed strategy. -/
theorem isSelfConfirmingEquilibrium_not_mixedStrictlyDominated {a : G.ActionProfile}
    {μ : G.Player → G.ActionProfile → ℝ} (hSCE : G.IsSelfConfirmingEquilibrium f a μ) (i : G.Player) :
    ¬ G.IsMixedStrictlyDominated i (a i) := by
  obtain ⟨hdist, hbest, _⟩ := hSCE i
  exact isBeliefBestResponseWithin_not_mixedStrictlyDominated
    ⟨μ i, hdist, fun b ⟨j, _, hj⟩ => absurd (Set.mem_univ (b j)) hj, hbest⟩

/-- **Under perfect feedback the self-confirming and Nash equilibria coincide.** If each player
observes the entire action profile (`f i = id`), a confirmed conjecture is concentrated on profiles
agreeing with `a` off `i`, so the best-response condition collapses to the Nash condition. -/
theorem isNashEquilibrium_of_perfectFeedback {a : G.ActionProfile}
    (h : G.IsSelfConfirmingEquilibriumActionProfile (fun _ => (id : G.ActionProfile → _)) a) :
    G.IsNashEquilibrium a := by
  obtain ⟨μ, hSCE⟩ := h
  intro i
  obtain ⟨hdist, hbest, hconf⟩ := hSCE i
  -- Perfect feedback confirms the conjecture only on profiles agreeing with `a` off `i`.
  refine isBestResponseAt_of_belief_supported_off hdist (fun b hb j hj => ?_) hbest
  have hc : G.deviate b i (a i) = a := hconf b hb
  have h2 := congrFun hc j; rwa [G.deviate_ne b (a i) hj] at h2

end StaticGame

end EcoLean.GameTheory
