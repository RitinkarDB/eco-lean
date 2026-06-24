import EcoLean.GameTheory.StaticGames.SubjectiveCorrelated

/-!
# Subjective correlated equilibrium: the construction (§8.5.5, Theorem 32 — hard direction)

Battigalli–Catonini–De Vito §8.5.5. The **hard direction (⟹)** of Theorem 32: every
correlated-rationalizable action profile is realised by an equilibrium of a state-independent Bayesian
elaboration with positive-probability types.

We build the elaboration from `C = CorrelatedRationalizable`: state space the rationalizable profiles
`{a // ∀ j, aⱼ ∈ Cⱼ}`, types `Tᵢ = {aᵢ // aᵢ ∈ Cᵢ}`, signal `τᵢ ω = ωᵢ`, prior from the per-action
justifying conjectures, and payoffs state-independent. The **identity strategy** is a Bayesian Nash
equilibrium realising every rationalizable profile at its own state.
-/

namespace EcoLean.GameTheory

open scoped BigOperators
open Classical Finset

namespace StaticGame

variable {G : StaticGame} [Fintype G.Player] [DecidableEq G.Player]
  [∀ i, Fintype (G.Action i)] [∀ i, DecidableEq (G.Action i)]

/-- The rationalizable actions of player `i`, as a finite type. -/
abbrev RatType (G : StaticGame) [Fintype G.Player] [DecidableEq G.Player]
    [∀ i, Fintype (G.Action i)] (i : G.Player) : Type _ :=
  {aᵢ : G.Action i // aᵢ ∈ G.CorrelatedRationalizable i}

/-- A justifying conjecture for a rationalizable action. -/
noncomputable def conjFor (i : G.Player) (tᵢ : RatType G i) : G.ActionProfile → ℝ :=
  (G.correlatedRationalizable_isCorrelatedBestResponseSet i tᵢ.val tᵢ.property).choose

theorem conjFor_supportedOn (i : G.Player) (tᵢ : RatType G i) :
    G.BeliefSupportedOn (conjFor i tᵢ) G.CorrelatedRationalizable i :=
  (G.correlatedRationalizable_isCorrelatedBestResponseSet i tᵢ.val tᵢ.property).choose_spec.2.1

theorem conjFor_best (i : G.Player) (tᵢ : RatType G i) :
    G.IsBestResponseToBelief (conjFor i tᵢ) i tᵢ.val :=
  (G.correlatedRationalizable_isCorrelatedBestResponseSet i tᵢ.val tᵢ.property).choose_spec.2.2

/-- **The reindexing lemma.** Averaging an `i`-invariant `g` against a conjecture `μ` supported on `C`
equals the sum, over rationalizable profiles `ω` with `i`-coordinate `tᵢ`, of the `i`-marginalised
weight times `g`. (The combinatorial heart of the construction: re-grouping the belief sum by the
suggested-action state.) -/
theorem conjFor_sum_reindex (i : G.Player) (tᵢ : RatType G i) (μ : G.ActionProfile → ℝ)
    (hμ : G.BeliefSupportedOn μ G.CorrelatedRationalizable i)
    (g : G.ActionProfile → ℝ) (hg : ∀ a v, g (Function.update a i v) = g a) :
    (∑ a, μ a * g a)
      = ∑ b ∈ univ.filter (fun b : G.ActionProfile => ∀ j, b j ∈ G.CorrelatedRationalizable j),
          if b i = tᵢ.val then (∑ v, μ (Function.update b i v)) * g b else 0 := by
  -- group the full sum by the map `a ↦ update a i tᵢ.val`
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun a => Function.update a i tᵢ.val)
    (t := univ) (fun a _ => mem_univ _)]
  -- each fiber collapses to the marginalised term
  have hfib : ∀ b : G.ActionProfile,
      (∑ a ∈ univ.filter (fun a => Function.update a i tᵢ.val = b), μ a * g a)
        = if b i = tᵢ.val then (∑ v, μ (Function.update b i v)) * g b else 0 := by
    intro b
    by_cases hb : b i = tᵢ.val
    · rw [if_pos hb]
      have himg : (univ.filter (fun a => Function.update a i tᵢ.val = b))
          = univ.image (fun v => Function.update b i v) := by
        ext a
        simp only [mem_filter, mem_univ, true_and, mem_image]
        constructor
        · intro ha
          refine ⟨a i, ?_⟩
          funext j
          by_cases hj : j = i
          · subst hj; rw [Function.update_self]
          · rw [Function.update_of_ne hj, ← ha, Function.update_of_ne hj]
        · rintro ⟨v, rfl⟩
          funext j
          by_cases hj : j = i
          · subst hj; rw [Function.update_self]; exact hb.symm
          · rw [Function.update_of_ne hj, Function.update_of_ne hj]
      rw [himg, Finset.sum_image (fun v _ w _ hvw => by
        have := congrFun hvw i; rwa [Function.update_self, Function.update_self] at this)]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [hg]
    · rw [if_neg hb]
      refine Finset.sum_eq_zero fun a ha => ?_
      rw [mem_filter] at ha
      exact absurd (by rw [← ha.2, Function.update_self]) hb
  rw [Finset.sum_congr rfl fun b _ => hfib b]
  -- drop the non-rationalizable `b` (zero weight by the support condition)
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun b _ hb => ?_).symm
  simp only [mem_filter, mem_univ, true_and, not_forall] at hb
  obtain ⟨j, hj⟩ := hb
  by_cases hbi : b i = tᵢ.val
  · rw [if_pos hbi]
    have hji : j ≠ i := by
      rintro rfl; exact hj (hbi ▸ tᵢ.property)
    rw [show (∑ v, μ (Function.update b i v)) = 0 from
      Finset.sum_eq_zero fun v _ => hμ _ ⟨j, hji, by rw [Function.update_of_ne hji]; exact hj⟩,
      zero_mul]
  · rw [if_neg hbi]

/-- The **subjective Bayesian elaboration** built from the rationalizable set. -/
@[reducible] noncomputable def ratElaboration (G : StaticGame) [Fintype G.Player] [DecidableEq G.Player]
    [∀ i, Fintype (G.Action i)] [∀ i, DecidableEq (G.Action i)] : BayesianGame where
  Player := G.Player
  State := {a : G.ActionProfile // ∀ j, a j ∈ G.CorrelatedRationalizable j}
  PlayerType := RatType G
  Action := G.Action
  signal := fun i ω => ⟨ω.val i, ω.property i⟩
  prior := fun i ω => (1 / ((G.CorrelatedRationalizable i).ncard : ℝ))
    * ∑ v, conjFor i ⟨ω.val i, ω.property i⟩ (Function.update ω.val i v)
  payoff := fun i _ a => G.payoff i a

/-- The identity strategy: play the suggested action. -/
def ratIdStrategy : (ratElaboration G).Strategy := fun _ tᵢ => tᵢ.val

theorem ratIdStrategy_realizedProfile (ω : (ratElaboration G).State) :
    (ratElaboration G).realizedProfile ratIdStrategy ω = ω.val := rfl

/-- The interim deviation payoff is the correlated best-reply payoff against the justifying
conjecture, scaled by the nonnegative constant `1/|Cᵢ|`. -/
theorem interimDevPayoff_ratElaboration (i : G.Player) (tᵢ : RatType G i) (ci : G.Action i) :
    (ratElaboration G).interimDevPayoff ratIdStrategy i tᵢ ci
      = (1 / ((G.CorrelatedRationalizable i).ncard : ℝ))
        * ∑ a, conjFor i tᵢ a * G.devPayoff a i ci := by
  have hsub : (∑ b ∈ univ.filter (fun b : G.ActionProfile => ∀ j, b j ∈ G.CorrelatedRationalizable j),
        if b i = tᵢ.val then (∑ v, conjFor i tᵢ (Function.update b i v)) * G.devPayoff b i ci else 0)
      = ∑ ω : (ratElaboration G).State,
          if ω.val i = tᵢ.val then
            (∑ v, conjFor i tᵢ (Function.update ω.val i v)) * G.devPayoff ω.val i ci else 0 :=
    Finset.sum_subtype
      (univ.filter (fun b : G.ActionProfile => ∀ j, b j ∈ G.CorrelatedRationalizable j))
      (fun x => by simp) _
  rw [conjFor_sum_reindex i tᵢ (conjFor i tᵢ) (conjFor_supportedOn i tᵢ)
    (fun a => G.devPayoff a i ci) (fun a v => by
      simp only [StaticGame.devPayoff, StaticGame.deviate, DProfile.update, Function.update_idem]),
    hsub, Finset.mul_sum, BayesianGame.interimDevPayoff]
  refine Finset.sum_congr rfl fun ω _ => ?_
  show (if (ratElaboration G).signal i ω = tᵢ then (ratElaboration G).prior i ω else 0)
      * (ratElaboration G).payoff i ω
        (Function.update ((ratElaboration G).realizedProfile ratIdStrategy ω) i ci) = _
  rw [ratIdStrategy_realizedProfile]
  by_cases hω : ω.val i = tᵢ.val
  · rw [if_pos (show (ratElaboration G).signal i ω = tᵢ from Subtype.ext hω), if_pos hω]
    show ((1 / ((G.CorrelatedRationalizable i).ncard : ℝ))
        * ∑ v, conjFor i ⟨ω.val i, ω.property i⟩ (Function.update ω.val i v))
        * G.payoff i (Function.update ω.val i ci)
      = (1 / ((G.CorrelatedRationalizable i).ncard : ℝ))
        * ((∑ v, conjFor i tᵢ (Function.update ω.val i v)) * G.devPayoff ω.val i ci)
    rw [show (⟨ω.val i, ω.property i⟩ : RatType G i) = tᵢ from Subtype.ext hω]
    show (1 / ((G.CorrelatedRationalizable i).ncard : ℝ)
        * ∑ v, conjFor i tᵢ (Function.update ω.val i v)) * G.devPayoff ω.val i ci = _
    ring
  · rw [if_neg (fun h => hω (Subtype.ext_iff.mp h)), if_neg hω, zero_mul, mul_zero]

/-- **Theorem 32 (⟹).** The identity strategy of the rationalizable-set elaboration is a Bayesian Nash
equilibrium. -/
theorem ratIdStrategy_isBayesianNashEquilibrium :
    (ratElaboration G).IsBayesianNashEquilibrium ratIdStrategy := by
  intro i tᵢ ci
  rw [← (ratElaboration G).interimDevPayoff_self ratIdStrategy i tᵢ]
  show (ratElaboration G).interimDevPayoff ratIdStrategy i tᵢ ci
    ≤ (ratElaboration G).interimDevPayoff ratIdStrategy i tᵢ (ratIdStrategy i tᵢ)
  rw [interimDevPayoff_ratElaboration, interimDevPayoff_ratElaboration]
  exact mul_le_mul_of_nonneg_left (conjFor_best i tᵢ ci) (by positivity)

/-- **Theorem 32 (⟹), profile form.** Every correlated-rationalizable profile is realised, at its own
state, by the Bayesian Nash equilibrium `ratIdStrategy` of the subjective elaboration. -/
theorem correlatedRationalizable_selected_in_subjectiveEquilibrium
    (a : G.ActionProfile) (ha : ∀ j, a j ∈ G.CorrelatedRationalizable j) :
    (ratElaboration G).IsBayesianNashEquilibrium ratIdStrategy ∧
      ∀ i, (ratElaboration G).realizedProfile ratIdStrategy ⟨a, ha⟩ i = a i :=
  ⟨ratIdStrategy_isBayesianNashEquilibrium, fun _ => rfl⟩

end StaticGame

end EcoLean.GameTheory
