import EcoLean.GameTheory.StaticGames.SelfConfirmingEquilibrium
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Learning and solution concepts (Chapter 7)

Following Battigalli–Catonini–De Vito Chapter 7. A **trajectory** `traj : ℕ → ActionProfile` is the
sequence of action profiles produced when a finite game is played recurrently. A trajectory is
*consistent with adaptive learning* if, from some point on, each profile is a best response to a
conjecture based on the recently observed play — the justification operator `ρ` applied to the
observation window. The chapter relates the long-run behaviour of adaptive learners to the static
solution concepts.

This file formalizes the two **convergence theorems**, which tie learning to the equilibrium concepts
already developed:

* `isNashEquilibrium_of_convergesTo_of_consistent` (**Theorem 25(2)**, perfectly observed actions): a
  convergent trajectory consistent with adaptive learning converges to a Nash equilibrium.
* `isSelfConfirmingEquilibriumActionProfile_of_convergesTo_of_fConsistent` (**Theorem 27**, imperfectly
  observed actions via the feedback functions of §6.3): a convergent `f`-consistent trajectory
  converges to a self-confirming equilibrium action profile.

and the long-run-frequency results:

* `justify` / `rhoPow` — the justification operator `ρ` on profile sets, and its iterates `ρᵏ(A)`.
* `eventually_mem_rhoPow_of_consistent` (**Theorem 25(1)**): an adaptively-consistent trajectory
  eventually plays only `ρᵏ`-rationalizable profiles, for every `k` — only rationalizable actions are
  chosen in the long run.
* `LimitDistribution` (**Definition 32**) and `limitDistribution_support_eventually_window`
  (**Lemma 21**): the long-run empirical distribution of a trajectory, and the fact that from some
  time on only support profiles occur, and every support profile occurs in every long window.

(Theorems 24 and 26 — relating the limit distribution to correlated/self-confirming equilibrium — are
left for follow-up; they need the `ρ`-closedness of an equilibrium's support.)
-/

namespace EcoLean.GameTheory

namespace StaticGame

open scoped BigOperators
open Filter Topology

variable {G : StaticGame} [Fintype G.Player] [DecidableEq G.Player] [∀ i, Fintype (G.Action i)]

/-- A trajectory **converges to** `a` if it is eventually constant equal to `a` — the standard notion
of convergence in the discrete profile space. -/
def TrajectoryConvergesTo (traj : ℕ → G.ActionProfile) (a : G.ActionProfile) : Prop :=
  ∃ t₀, ∀ t, t₀ < t → traj t = a

/-- `a` is **adaptively justified** by a set `C` of observed profiles: each player's action is a best
response to a conjecture concentrated on profiles whose opponent part agrees, off `i`, with some
profile of `C`. This is the per-period requirement built from the justification operator `ρ`. -/
def IsAdaptivelyJustified (C : Set G.ActionProfile) (a : G.ActionProfile) : Prop :=
  ∀ i : G.Player, ∃ μ : G.ActionProfile → ℝ, G.IsCorrelatedDistribution μ ∧
    (∀ b, 0 < μ b → ∃ c ∈ C, ∀ j, j ≠ i → b j = c j) ∧ G.IsBestResponseToBelief μ i (a i)

/-- A trajectory is **consistent with adaptive learning** (perfectly observed actions; Definition 31):
from some time on, each profile is adaptively justified by the recently observed profiles. -/
def ConsistentWithAdaptiveLearning (traj : ℕ → G.ActionProfile) : Prop :=
  ∀ tStart : ℕ, ∃ T, ∀ t, tStart + T < t →
    G.IsAdaptivelyJustified {c | ∃ τ, tStart ≤ τ ∧ τ < t ∧ traj τ = c} (traj t)

/-- **Theorem 25(2).** A convergent trajectory consistent with adaptive learning converges to a Nash
equilibrium: past the convergence time the observation window collapses to `{a}`, so each player best
responds to the point belief at `a`, which is the Nash condition. -/
theorem isNashEquilibrium_of_convergesTo_of_consistent {traj : ℕ → G.ActionProfile}
    {a : G.ActionProfile} (hconv : G.TrajectoryConvergesTo traj a)
    (hcons : G.ConsistentWithAdaptiveLearning traj) : G.IsNashEquilibrium a := by
  obtain ⟨t₀, hconv⟩ := hconv
  obtain ⟨T, hT⟩ := hcons (t₀ + 1)
  have hjust := hT ((t₀ + 1) + T + 1) (by omega)
  rw [hconv _ (by omega : t₀ < (t₀ + 1) + T + 1)] at hjust
  intro i
  obtain ⟨μ, hdist, hsupp, hbest⟩ := hjust i
  refine isBestResponseAt_of_belief_supported_off hdist (fun b hb j hj => ?_) hbest
  obtain ⟨c, ⟨τ, hτlo, _, hτc⟩, hbc⟩ := hsupp b hb
  rw [hbc j hj, ← hτc, hconv τ (by omega)]

/-! ### The justification operator and long-run rationalizability -/

/-- The **justification operator** `ρ` on sets of profiles: the profiles adaptively justified by the
observed set `C`. A trajectory is adaptively consistent exactly when each late profile lies in `ρ`
of its observation window. -/
def justify (C : Set G.ActionProfile) : Set G.ActionProfile := {a | G.IsAdaptivelyJustified C a}

/-- The justification operator is monotone: more observed profiles can only justify more. -/
theorem justify_mono {C D : Set G.ActionProfile} (h : C ⊆ D) : G.justify C ⊆ G.justify D := by
  intro a ha i
  obtain ⟨μ, hdist, hsupp, hbest⟩ := ha i
  refine ⟨μ, hdist, fun b hb => ?_, hbest⟩
  obtain ⟨c, hc, hbc⟩ := hsupp b hb
  exact ⟨c, h hc, hbc⟩

/-- `ρᵏ(A)`: the `k`-th iterate of the justification operator from the full profile set `A`. The
rationalizable profiles are `⋂ₖ ρᵏ(A)`. -/
def rhoPow (G : StaticGame) [Fintype G.Player] [DecidableEq G.Player] [∀ i, Fintype (G.Action i)] :
    ℕ → Set G.ActionProfile
  | 0 => Set.univ
  | k + 1 => G.justify (G.rhoPow k)

/-- **Theorem 25(1).** A trajectory consistent with adaptive learning eventually plays only
`ρᵏ`-profiles, for every `k`: in the long run only (iteratively) rationalizable profiles are chosen.
The proof is an induction on `k` — each step feeds the inductive window-bound through the monotone
justification operator. -/
theorem eventually_mem_rhoPow_of_consistent {traj : ℕ → G.ActionProfile}
    (hcons : G.ConsistentWithAdaptiveLearning traj) (k : ℕ) :
    ∃ tk, ∀ t, tk < t → traj t ∈ G.rhoPow k := by
  induction k with
  | zero => exact ⟨0, fun t _ => Set.mem_univ _⟩
  | succ k ih =>
      obtain ⟨tk, htk⟩ := ih
      obtain ⟨T, hT⟩ := hcons (tk + 1)
      refine ⟨tk + 1 + T, fun t ht => ?_⟩
      have hwin : {c | ∃ τ, tk + 1 ≤ τ ∧ τ < t ∧ traj τ = c} ⊆ G.rhoPow k := by
        rintro c ⟨τ, hτlo, _, hτc⟩
        rw [← hτc]; exact htk τ (by omega)
      exact justify_mono hwin (hT t ht)

/-! ### Limit distributions and Lemma 21 -/

section LimitDistributions

variable [∀ i, DecidableEq (G.Action i)]

/-- The **empirical frequency** of profile `a` over the periods `1 ≤ τ < t`. -/
noncomputable def freq (traj : ℕ → G.ActionProfile) (a : G.ActionProfile) (t : ℕ) : ℝ :=
  (((Finset.Ico 1 t).filter (fun τ => traj τ = a)).card : ℝ) / t

theorem freq_nonneg (traj : ℕ → G.ActionProfile) (a : G.ActionProfile) (t : ℕ) :
    0 ≤ G.freq traj a t :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **Definition 32.** `μ` is the *limit distribution* of `traj` when every profile's long-run
empirical frequency converges to `μ a`, and any zero-probability profile is eventually never played. -/
structure LimitDistribution (traj : ℕ → G.ActionProfile) (μ : G.ActionProfile → ℝ) : Prop where
  /-- Condition 32(i): the frequency of each profile converges to its probability. -/
  tendsto_freq : ∀ a, Tendsto (G.freq traj a) atTop (𝓝 (μ a))
  /-- Condition 32(ii): a zero-probability profile is eventually never played. -/
  eventually_ne : ∀ a, μ a = 0 → ∃ tBar, ∀ t, tBar < t → traj t ≠ a

/-- A profile of positive probability is played at some time beyond any given `tBar` — equivalently,
it is played infinitely often. (If it were dropped after `tBar`, its frequency would be at most
`tBar / t → 0`, forcing `μ a = 0`.) -/
theorem LimitDistribution.exists_ge_of_ne_zero {traj : ℕ → G.ActionProfile}
    {μ : G.ActionProfile → ℝ} (h : G.LimitDistribution traj μ) {a : G.ActionProfile}
    (ha : μ a ≠ 0) (tBar : ℕ) : ∃ τ, tBar ≤ τ ∧ traj τ = a := by
  by_contra hcon
  push_neg at hcon
  have hbound : ∀ t : ℕ, G.freq traj a t ≤ (tBar : ℝ) / t := by
    intro t
    have hcard : ((Finset.Ico 1 t).filter (fun τ => traj τ = a)).card ≤ tBar := by
      have hsub : (Finset.Ico 1 t).filter (fun τ => traj τ = a) ⊆ Finset.Ico 1 tBar := by
        intro τ hτ
        rw [Finset.mem_filter] at hτ
        rw [Finset.mem_Ico] at hτ ⊢
        refine ⟨hτ.1.1, ?_⟩
        by_contra hge
        exact hcon τ (not_lt.mp hge) hτ.2
      calc ((Finset.Ico 1 t).filter (fun τ => traj τ = a)).card
          ≤ (Finset.Ico 1 tBar).card := Finset.card_le_card hsub
        _ = tBar - 1 := by rw [Nat.card_Ico]
        _ ≤ tBar := Nat.sub_le _ _
    unfold freq
    gcongr
  have hle : μ a ≤ 0 := le_of_tendsto_of_tendsto' (h.tendsto_freq a)
    (tendsto_const_div_atTop_nhds_zero_nat (tBar : ℝ)) hbound
  have hge : 0 ≤ μ a :=
    ge_of_tendsto (h.tendsto_freq a) (Eventually.of_forall fun t => G.freq_nonneg traj a t)
  exact ha (le_antisymm hle hge)

/-- **Lemma 21.** If `μ` is the limit distribution of `traj`, then for every `tBar` there is a time
past which only support profiles occur, and every support profile occurs in the window `[tBar, t)`:
`aₜ ∈ supp μ ⊆ {aτ : tBar ≤ τ < t}`. -/
theorem limitDistribution_support_eventually_window {traj : ℕ → G.ActionProfile}
    {μ : G.ActionProfile → ℝ} (h : G.LimitDistribution traj μ) (tBar : ℕ) :
    ∃ T, ∀ t, tBar + T < t →
      μ (traj t) ≠ 0 ∧ ∀ a, μ a ≠ 0 → ∃ τ, tBar ≤ τ ∧ τ < t ∧ traj τ = a := by
  classical
  -- Part A: a time `boundA` past which only support profiles are played.
  let gA : G.ActionProfile → ℕ := fun a => if ha : μ a = 0 then (h.eventually_ne a ha).choose else 0
  let boundA : ℕ := Finset.univ.sup gA
  -- Part B: for every support profile `a`, a window time `gB a < boundB` realising it ≥ `tBar`.
  let gB : G.ActionProfile → ℕ :=
    fun a => if ha : μ a ≠ 0 then (h.exists_ge_of_ne_zero ha tBar).choose else 0
  let boundB : ℕ := Finset.univ.sup gB
  refine ⟨boundA + boundB, fun t ht => ⟨?_, ?_⟩⟩
  · -- `μ (traj t) ≠ 0`
    intro hμ0
    have hg : gA (traj t) = (h.eventually_ne (traj t) hμ0).choose := dif_pos hμ0
    have hlt : gA (traj t) < t := lt_of_le_of_lt (Finset.le_sup (Finset.mem_univ (traj t))) (by omega)
    rw [hg] at hlt
    exact (h.eventually_ne (traj t) hμ0).choose_spec t hlt rfl
  · -- support ⊆ window
    intro a ha
    have hg : gB a = (h.exists_ge_of_ne_zero ha tBar).choose := dif_pos ha
    obtain ⟨hτlo, hτa⟩ := (h.exists_ge_of_ne_zero ha tBar).choose_spec
    have hlt : gB a < t := lt_of_le_of_lt (Finset.le_sup (Finset.mem_univ a)) (by omega)
    rw [hg] at hlt
    exact ⟨_, hτlo, hlt, hτa⟩

end LimitDistributions

variable {M : G.Player → Type*}

/-- A trajectory is **`f`-consistent with adaptive learning** (imperfectly observed actions;
Definition 33): from some time on, each player's action is a best response to a conjecture
concentrated on profiles whose feedback — under the player's own current action — matches a recently
observed message. -/
def FConsistentWithAdaptiveLearning (f : ∀ i, G.ActionProfile → M i)
    (traj : ℕ → G.ActionProfile) : Prop :=
  ∀ tStart : ℕ, ∃ T, ∀ t, tStart + T < t → ∀ i : G.Player, ∃ μ : G.ActionProfile → ℝ,
    G.IsCorrelatedDistribution μ ∧
    (∀ b, 0 < μ b → ∃ τ, tStart ≤ τ ∧ τ < t ∧ f i (traj τ) = f i (G.deviate b i (traj t i))) ∧
    G.IsBestResponseToBelief μ i (traj t i)

/-- **Theorem 27.** A convergent trajectory `f`-consistent with adaptive learning converges to a
self-confirming equilibrium action profile: past the convergence time every observed message equals
the actual play's feedback, so the limiting conjectures are confirmed and justify the limit action. -/
theorem isSelfConfirmingEquilibriumActionProfile_of_convergesTo_of_fConsistent
    {f : ∀ i, G.ActionProfile → M i} {traj : ℕ → G.ActionProfile} {a : G.ActionProfile}
    (hconv : G.TrajectoryConvergesTo traj a) (hcons : G.FConsistentWithAdaptiveLearning f traj) :
    G.IsSelfConfirmingEquilibriumActionProfile f a := by
  obtain ⟨t₀, hconv⟩ := hconv
  obtain ⟨T, hT⟩ := hcons (t₀ + 1)
  have hjust := hT ((t₀ + 1) + T + 1) (by omega)
  have hti : ∀ i, traj ((t₀ + 1) + T + 1) i = a i := fun i =>
    congrFun (hconv _ (by omega)) i
  choose μ hdist hsupp hbest using hjust
  refine ⟨μ, fun i => ⟨hdist i, ?_, ?_⟩⟩
  · have hbi := hbest i; rwa [hti i] at hbi
  · intro b hb
    obtain ⟨τ, hτlo, _, hτeq⟩ := hsupp i b hb
    rw [hti i] at hτeq
    rw [← hτeq, hconv τ (by omega)]

/-! ### Theorem 24: a correlated-equilibrium limit distribution is adaptively consistent -/

section Theorem24

variable [∀ i, DecidableEq (G.Action i)]

/-- The support of a (canonical) correlated equilibrium is *self-justifying*: every recommended
profile `a` is adaptively justified by the support, the justifying belief for player `i` being the
posterior over the others' play conditional on `i`'s own recommendation `aᵢ`. The required
best-response inequality is exactly the equilibrium's incentive constraint for the departure that
replaces `aᵢ` by the candidate action. -/
theorem isAdaptivelyJustified_of_isCorrelatedEquilibrium {μ : G.ActionProfile → ℝ}
    (hce : G.IsCorrelatedEquilibrium μ) {a : G.ActionProfile} (ha : μ a ≠ 0) :
    G.IsAdaptivelyJustified {b | μ b ≠ 0} a := by
  obtain ⟨⟨hμnn, _⟩, hμic⟩ := hce
  intro i
  have hμa : 0 < μ a := lt_of_le_of_ne (hμnn a) (Ne.symm ha)
  set m : ℝ := ∑ b : G.ActionProfile, (if b i = a i then μ b else 0) with hm
  have hmpos : 0 < m := by
    rw [hm]
    refine Finset.sum_pos' (fun b _ => by split_ifs; exacts [hμnn b, le_refl 0])
      ⟨a, Finset.mem_univ a, ?_⟩
    rw [if_pos rfl]; exact hμa
  refine ⟨fun b => (if b i = a i then μ b else 0) / m, ⟨fun b => ?_, ?_⟩, ?_, ?_⟩
  · exact div_nonneg (by split_ifs; exacts [hμnn b, le_refl 0]) hmpos.le
  · rw [← Finset.sum_div, ← hm, div_self hmpos.ne']
  · intro b hb
    have hb' : 0 < (if b i = a i then μ b else 0) / m := hb
    have hbpos : 0 < (if b i = a i then μ b else 0) := by
      have hmul := mul_pos hb' hmpos
      rwa [div_mul_cancel₀ _ hmpos.ne'] at hmul
    have hbi : b i = a i := by by_contra hc; rw [if_neg hc] at hbpos; exact lt_irrefl 0 hbpos
    rw [if_pos hbi] at hbpos
    exact ⟨b, ne_of_gt hbpos, fun j _ => rfl⟩
  · intro ci
    set δ : G.Action i → G.Action i := fun x => if x = a i then ci else x with hδ
    have hpt : ∀ b, (if b i = a i then μ b else 0) * (G.devPayoff b i (a i) - G.devPayoff b i ci)
        = μ b * (G.payoff i b - G.devPayoff b i (δ (b i))) := by
      intro b
      by_cases hbi : b i = a i
      · rw [if_pos hbi]
        have h1 : G.devPayoff b i (a i) = G.payoff i b := by rw [← hbi, G.devPayoff_self]
        have h2 : δ (b i) = ci := by rw [hδ]; simp [hbi]
        rw [h1, h2]
      · rw [if_neg hbi]
        have h2 : δ (b i) = b i := by rw [hδ]; simp [hbi]
        rw [h2, G.devPayoff_self]; ring
    have hge : 0 ≤ ∑ b, (if b i = a i then μ b else 0)
        * (G.devPayoff b i (a i) - G.devPayoff b i ci) := by
      rw [Finset.sum_congr rfl (fun b _ => hpt b)]
      have heq : ∑ b, μ b * (G.payoff i b - G.devPayoff b i (δ (b i)))
          = G.expectedPayoff μ i - G.expectedDeviationPayoff μ i δ := by
        simp only [expectedPayoff, expectedDeviationPayoff, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [heq]; linarith [hμic i δ]
    have hsplit : ∑ b, (if b i = a i then μ b else 0) / m
          * (G.devPayoff b i (a i) - G.devPayoff b i ci)
        = (∑ b, (if b i = a i then μ b else 0) / m * G.devPayoff b i (a i))
          - ∑ b, (if b i = a i then μ b else 0) / m * G.devPayoff b i ci := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun b _ => by ring
    have hrw : ∑ b, (if b i = a i then μ b else 0) / m
          * (G.devPayoff b i (a i) - G.devPayoff b i ci)
        = (∑ b, (if b i = a i then μ b else 0)
          * (G.devPayoff b i (a i) - G.devPayoff b i ci)) / m := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun b _ => by ring
    have hfac : (0:ℝ) ≤ ∑ b, (if b i = a i then μ b else 0) / m
        * (G.devPayoff b i (a i) - G.devPayoff b i ci) := by
      rw [hrw]; exact div_nonneg hge hmpos.le
    rw [hsplit] at hfac
    show ∑ b, (if b i = a i then μ b else 0) / m * G.devPayoff b i ci
        ≤ ∑ b, (if b i = a i then μ b else 0) / m * G.devPayoff b i (a i)
    linarith [hfac]

/-- **Theorem 24.** If a trajectory's limit distribution is a (canonical) correlated equilibrium, then
the trajectory is consistent with adaptive learning: from some time on, every profile lies in the
justification operator applied to the recently observed window (its support, which the equilibrium
justifies). -/
theorem consistentWithAdaptiveLearning_of_limitDistribution_isCorrelatedEquilibrium
    {traj : ℕ → G.ActionProfile} {μ : G.ActionProfile → ℝ}
    (hμ : G.LimitDistribution traj μ) (hce : G.IsCorrelatedEquilibrium μ) :
    G.ConsistentWithAdaptiveLearning traj := by
  intro tStart
  obtain ⟨T, hT⟩ := limitDistribution_support_eventually_window hμ tStart
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨htmem, htwindow⟩ := hT t ht
  exact justify_mono (fun a ha => htwindow a ha)
    (isAdaptivelyJustified_of_isCorrelatedEquilibrium hce htmem)

end Theorem24

end StaticGame

end EcoLean.GameTheory
