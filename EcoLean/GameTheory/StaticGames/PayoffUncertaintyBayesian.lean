import EcoLean.GameTheory.StaticGames.SubjectiveCorrelated
import EcoLean.GameTheory.StaticGames.DirectedRationalizability

/-!
# Bayesian games based on a game with payoff uncertainty (§8.5.5, Theorem 33 — easy direction)

Battigalli–Catonini–De Vito §8.5.5, Theorem 33 (the payoff-uncertainty generalisation of Theorem 32).
A *Bayesian game based on* `Ĝ` appends a state space `Ω`, signal functions `τᵢ : Ω → Tᵢ`, information-
type decoders `ϑᵢ : Tᵢ → Θᵢ` and `ϑ₀ : Ω → Θ₀`, and priors `pᵢ`, with payoffs inherited from `Ĝ`. A
profile of information-types and actions `(θᵢ, aᵢ)` is *rationalizable in `Ĝ`* iff it is realised
`(ϑᵢ(τᵢ(ω)), σᵢ(τᵢ(ω)))` by an equilibrium of some such Bayesian game.

This file proves the **easy direction (⟸)**: the realised type-action pairs of an equilibrium are
rationalizable. Mirrors Theorem 32 over `FullProfile`s; the one new point is that overriding `i`'s
information type to `ϑᵢ(tᵢ)` is a no-op on the states consistent with `tᵢ`.
-/

namespace EcoLean.GameTheory

open scoped BigOperators
open Classical

/-- A **Bayesian game based on** the payoff-uncertainty game `G`: a state space with signals,
information-type decoders, and priors. -/
structure SubjectiveBayesianGame (G : PayoffUncertaintyGame) where
  /-- The states of the world. -/
  Ω : Type*
  [fintypeΩ : Fintype Ω]
  /-- Each player's signal (type) space. -/
  T : G.Player → Type*
  [fintypeT : ∀ i, Fintype (T i)]
  [decEqT : ∀ i, DecidableEq (T i)]
  /-- The signal `i` observes at a state. -/
  τ : ∀ i, Ω → T i
  /-- The information type a signal decodes to. -/
  ϑ : ∀ i, T i → G.InfoType i
  /-- The residual state of nature at each world. -/
  ϑ₀ : Ω → G.Residual
  /-- Each player's prior over states. -/
  p : G.Player → Ω → ℝ

namespace PayoffUncertaintyGame

open Finset

/-- The **exogenous marginal** of a conjecture `μ` for player `i` (§8.5.1): marginalise out `i`'s own
information type and *all* action profiles, keeping the residual and the others' information types —
the belief over `Θ₀ × Θ₋ᵢ`. Realised as a full-profile function (constant in `i`'s type and in
actions). -/
noncomputable def exogMarginal {G : PayoffUncertaintyGame} [Fintype G.Player] [DecidableEq G.Player]
    [∀ i, Fintype (G.InfoType i)] [∀ i, Fintype (G.Action i)] (i : G.Player)
    (μ : G.FullProfile → ℝ) : G.FullProfile → ℝ :=
  fun fp => ∑ θᵢ' : G.InfoType i, ∑ a : (∀ j, G.Action j), μ ⟨fp.1, Function.update fp.2.1 i θᵢ', a⟩

/-- The full-conjecture restriction induced by an **exogenous**-belief restriction `Δe`: a conjecture
is admissible iff its exogenous marginal is. -/
def fullRestrictionOfExog {G : PayoffUncertaintyGame} [Fintype G.Player] [DecidableEq G.Player]
    [∀ i, Fintype (G.InfoType i)] [∀ i, Fintype (G.Action i)] (Δe : G.BeliefRestriction) :
    G.BeliefRestriction :=
  fun i θᵢ => {μ | PayoffUncertaintyGame.exogMarginal i μ ∈ Δe i θᵢ}

end PayoffUncertaintyGame

namespace SubjectiveBayesianGame

variable {G : PayoffUncertaintyGame} [Fintype G.Player] [DecidableEq G.Player]
  [Fintype G.Residual] [∀ i, Fintype (G.InfoType i)] [∀ i, DecidableEq (G.InfoType i)]
  [∀ i, Fintype (G.Action i)] [∀ i, DecidableEq (G.Action i)]
  (B : SubjectiveBayesianGame G)

attribute [instance] SubjectiveBayesianGame.fintypeΩ SubjectiveBayesianGame.fintypeT
  SubjectiveBayesianGame.decEqT

/-- A strategy for `B`: each player maps signals to actions. -/
abbrev Strategy : Type _ := ∀ i, B.T i → G.Action i

/-- The underlying repo `BayesianGame` whose state-dependent payoff is inherited from `G`. -/
@[reducible] def toBayesianGame : BayesianGame where
  Player := G.Player
  State := B.Ω
  PlayerType := B.T
  Action := G.Action
  signal := B.τ
  prior := B.p
  payoff := fun i ω a => G.payoff i (B.ϑ₀ ω) (fun j => B.ϑ j (B.τ j ω)) a

/-- The full profile `(θ₀, (θⱼ), (aⱼ))` realised at state `ω` under strategy `σ`. -/
def decode (σ : B.Strategy) (ω : B.Ω) : G.FullProfile :=
  ⟨B.ϑ₀ ω, fun j => B.ϑ j (B.τ j ω), fun j => σ j (B.τ j ω)⟩

/-- The conjecture induced by type `tᵢ`: the normalised pushforward of `i`'s interim belief along the
realised-full-profile map. -/
noncomputable def inducedFullConjecture (σ : B.Strategy) (i : G.Player) (tᵢ : B.T i) :
    G.FullProfile → ℝ :=
  fun fp => (∑ ω, if B.τ i ω = tᵢ ∧ B.decode σ ω = fp then B.p i ω else 0)
    / (B.toBayesianGame).typeMass i tᵢ

/-- Pushforward identity against the unnormalised induced conjecture. -/
theorem sum_decode_unnorm_mul (σ : B.Strategy) (i : G.Player) (tᵢ : B.T i)
    (h : G.FullProfile → ℝ) :
    ∑ fp, (∑ ω, if B.τ i ω = tᵢ ∧ B.decode σ ω = fp then B.p i ω else 0) * h fp
      = ∑ ω, (if B.τ i ω = tᵢ then B.p i ω else 0) * h (B.decode σ ω) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hsig : B.τ i ω = tᵢ
  · rw [if_pos hsig, Finset.sum_eq_single (B.decode σ ω)
      (fun a _ hne => by rw [if_neg (fun hc => hne hc.2.symm), zero_mul])
      (fun hmem => absurd (Finset.mem_univ _) hmem), if_pos ⟨hsig, rfl⟩]
  · rw [if_neg hsig, zero_mul,
      Finset.sum_eq_zero fun a _ => by rw [if_neg (fun hc => hsig hc.1), zero_mul]]

/-- The total unnormalised mass equals the type mass. -/
theorem sum_decode_unnorm (σ : B.Strategy) (i : G.Player) (tᵢ : B.T i) :
    (∑ fp, ∑ ω, if B.τ i ω = tᵢ ∧ B.decode σ ω = fp then B.p i ω else 0)
      = (B.toBayesianGame).typeMass i tᵢ := by
  have := B.sum_decode_unnorm_mul σ i tᵢ (fun _ => 1)
  simpa [BayesianGame.typeMass, toBayesianGame] using this

/-- The induced conjecture is a probability distribution. -/
theorem inducedFullConjecture_isDistribution (hp : ∀ i ω, 0 ≤ B.p i ω) {i : G.Player} {tᵢ : B.T i}
    (hpos : 0 < (B.toBayesianGame).typeMass i tᵢ) (σ : B.Strategy) :
    G.IsDistribution (B.inducedFullConjecture σ i tᵢ) := by
  refine ⟨fun fp => div_nonneg (Finset.sum_nonneg fun ω _ => ?_) (le_of_lt hpos), ?_⟩
  · split_ifs with h
    · exact hp i ω
    · exact le_refl 0
  · unfold inducedFullConjecture
    rw [← Finset.sum_div, B.sum_decode_unnorm σ i tᵢ, div_self (ne_of_gt hpos)]

/-- The induced conjecture is supported on the realised type-action pairs. -/
theorem inducedFullConjecture_supportedOn {i : G.Player} {tᵢ : B.T i} (σ : B.Strategy) :
    G.BeliefSupportedOn (B.inducedFullConjecture σ i tᵢ)
      (fun j => {p | ∃ tⱼ, (B.ϑ j tⱼ, σ j tⱼ) = p}) i := by
  rintro fp ⟨j, _, hjC⟩
  unfold inducedFullConjecture
  rw [div_eq_zero_iff]
  left
  refine Finset.sum_eq_zero fun ω _ => ?_
  rw [if_neg ?_]
  rintro ⟨_, hdec⟩
  refine hjC ⟨B.τ j ω, ?_⟩
  rw [← hdec]
  rfl

/-- The expected payoff against the induced conjecture is the interim deviation payoff of the
underlying Bayesian game, scaled by the type mass. The override of `i`'s information type to `ϑᵢ(tᵢ)`
is a no-op on the states consistent with `tᵢ`. -/
theorem sum_inducedFullConjecture_expectedPayoff {i : G.Player} {tᵢ : B.T i} (σ : B.Strategy)
    (aᵢ : G.Action i) :
    G.expectedPayoff (B.inducedFullConjecture σ i tᵢ) i (B.ϑ i tᵢ) aᵢ
      = (B.toBayesianGame).interimDevPayoff σ i tᵢ aᵢ / (B.toBayesianGame).typeMass i tᵢ := by
  unfold PayoffUncertaintyGame.expectedPayoff inducedFullConjecture
  simp only [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  rw [B.sum_decode_unnorm_mul σ i tᵢ
    (fun fp => G.payoff i fp.1 (Function.update fp.2.1 i (B.ϑ i tᵢ)) (Function.update fp.2.2 i aᵢ)),
    BayesianGame.interimDevPayoff]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hω : B.τ i ω = tᵢ
  · rw [if_pos hω]
    have hnoop : Function.update (fun j => B.ϑ j (B.τ j ω)) i (B.ϑ i tᵢ)
        = (fun j => B.ϑ j (B.τ j ω)) := by
      funext k
      by_cases hk : k = i
      · subst hk; rw [Function.update_self]; exact (congrArg (B.ϑ k) hω).symm
      · rw [Function.update_of_ne hk]
    simp only [decode, toBayesianGame, hnoop]
    rfl
  · rw [if_neg hω, zero_mul, zero_mul]

/-- `σᵢ(tᵢ)` is a best response, for information type `ϑᵢ(tᵢ)`, to the induced conjecture — exactly
the underlying Bayesian-equilibrium condition (up to the positive type mass). -/
theorem inducedFullConjecture_best {i : G.Player} {tᵢ : B.T i}
    (hpos : 0 < (B.toBayesianGame).typeMass i tᵢ) {σ : B.Strategy}
    (hσ : (B.toBayesianGame).IsBayesianNashEquilibrium σ) :
    G.IsBestResponseToBelief (B.inducedFullConjecture σ i tᵢ) i (B.ϑ i tᵢ) (σ i tᵢ) := by
  intro aᵢ'
  rw [B.sum_inducedFullConjecture_expectedPayoff, B.sum_inducedFullConjecture_expectedPayoff,
    div_le_div_iff_of_pos_right hpos,
    show (B.toBayesianGame).interimDevPayoff σ i tᵢ (σ i tᵢ)
      = (B.toBayesianGame).interimPayoff σ i tᵢ from (B.toBayesianGame).interimDevPayoff_self σ i tᵢ]
  exact hσ i tᵢ aᵢ'

/-- **Theorem 33 (⟸).** In a Bayesian game based on `Ĝ` (positive-probability types), the realised
information-type/action pair of any player in a Bayesian Nash equilibrium is rationalizable in `Ĝ`. -/
theorem rationalizable_of_basedOn_equilibrium (hp : ∀ i ω, 0 ≤ B.p i ω)
    (hpos : ∀ i tᵢ, 0 < (B.toBayesianGame).typeMass i tᵢ) {σ : B.Strategy}
    (hσ : (B.toBayesianGame).IsBayesianNashEquilibrium σ) (i : G.Player) (ω : B.Ω) :
    (B.ϑ i (B.τ i ω), σ i (B.τ i ω)) ∈ G.Rationalizable i := by
  have hBR : G.IsBestResponseSet (fun j => {p | ∃ tⱼ, (B.ϑ j tⱼ, σ j tⱼ) = p}) := by
    rintro j p ⟨tⱼ, rfl⟩
    exact ⟨B.inducedFullConjecture σ j tⱼ,
      B.inducedFullConjecture_isDistribution hp (hpos j tⱼ) σ,
      B.inducedFullConjecture_supportedOn σ, B.inducedFullConjecture_best (hpos j tⱼ) hσ⟩
  exact PayoffUncertaintyGame.subset_rationalizable_of_isBestResponseSet hBR i ⟨B.τ i ω, rfl⟩

/-! ### Theorem 34 (⟸): directed (Δ-) rationalizability -/

/-- `BG` (with strategy `σ`) **yields the belief restrictions `Δ`** if every type's induced
conjecture is admissible under the exogenous-belief restriction `Δ` (§8.5.1). -/
def YieldsRestrictions (σ : B.Strategy) (Δ : G.BeliefRestriction) : Prop :=
  ∀ (i : G.Player) (tᵢ : B.T i), B.inducedFullConjecture σ i tᵢ ∈ Δ i (B.ϑ i tᵢ)

/-- **Theorem 34 (⟸).** If a Bayesian game based on `Ĝ` yields the restrictions on exogenous
beliefs `Δ` and `σ` is an equilibrium, then every realised information-type/action pair is
`Δ`-rationalizable in `Ĝ`. -/
theorem deltaRationalizable_of_basedOn_equilibrium (hp : ∀ i ω, 0 ≤ B.p i ω)
    (hpos : ∀ i tᵢ, 0 < (B.toBayesianGame).typeMass i tᵢ) {σ : B.Strategy} {Δ : G.BeliefRestriction}
    (hyield : B.YieldsRestrictions σ Δ)
    (hσ : (B.toBayesianGame).IsBayesianNashEquilibrium σ) (i : G.Player) (ω : B.Ω) :
    (B.ϑ i (B.τ i ω), σ i (B.τ i ω)) ∈ G.DeltaRationalizable Δ i := by
  have hBR : G.IsDeltaBestResponseSet Δ (fun j => {p | ∃ tⱼ, (B.ϑ j tⱼ, σ j tⱼ) = p}) := by
    rintro j p ⟨tⱼ, rfl⟩
    exact ⟨B.inducedFullConjecture σ j tⱼ, hyield j tⱼ,
      B.inducedFullConjecture_isDistribution hp (hpos j tⱼ) σ,
      B.inducedFullConjecture_supportedOn σ, B.inducedFullConjecture_best (hpos j tⱼ) hσ⟩
  exact PayoffUncertaintyGame.subset_deltaRationalizable_of_isDeltaBestResponseSet hBR i
    ⟨B.τ i ω, rfl⟩

/-- `BG` (with strategy `σ`) **yields the exogenous-belief restrictions `Δe`** (the textbook's Def,
§8.5.1): every type's induced conjecture has an admissible exogenous marginal `margΘ₀×Θ₋ᵢ ∈ Δe`. -/
def YieldsExogRestrictions (σ : B.Strategy) (Δe : G.BeliefRestriction) : Prop :=
  ∀ (i : G.Player) (tᵢ : B.T i),
    PayoffUncertaintyGame.exogMarginal i (B.inducedFullConjecture σ i tᵢ) ∈ Δe i (B.ϑ i tᵢ)

/-- **Theorem 34 (⟸), exogenous form.** A game based on `Ĝ` that yields the exogenous restrictions
`Δe`, in equilibrium, realises only `Δe`-rationalizable pairs. (Immediate from the full-conjecture
form with `Δ := fullRestrictionOfExog Δe`.) -/
theorem deltaRationalizable_exog_of_basedOn_equilibrium (hp : ∀ i ω, 0 ≤ B.p i ω)
    (hpos : ∀ i tᵢ, 0 < (B.toBayesianGame).typeMass i tᵢ) {σ : B.Strategy} {Δe : G.BeliefRestriction}
    (hyield : B.YieldsExogRestrictions σ Δe)
    (hσ : (B.toBayesianGame).IsBayesianNashEquilibrium σ) (i : G.Player) (ω : B.Ω) :
    (B.ϑ i (B.τ i ω), σ i (B.τ i ω)) ∈ G.DeltaRationalizable (G.fullRestrictionOfExog Δe) i :=
  B.deltaRationalizable_of_basedOn_equilibrium (Δ := G.fullRestrictionOfExog Δe) hp hpos hyield hσ i ω

/-
**Theorem 34 — DONE, both directions, exogenous route, axiom-clean.** With the exogenous-marginal
restriction `fullRestrictionOfExog Δe` (admitting `μ` iff `exogMarginal i μ ∈ Δe`), the construction
preserves the relevant marginal, so both directions go through:

* ⟸ `deltaRationalizable_exog_of_basedOn_equilibrium` (above): an equilibrium of a game based on `Ĝ`
  that *yields* `Δe` realises only `Δe`-rationalizable pairs.
* ⟹ `deltaRatBased_{yieldsExog, isBayesianNashEquilibrium, realizes}` (below, in
  `namespace PayoffUncertaintyGame`): the construction `ratBasedOn (DeltaRationalizable …) deltaConj`
  yields `Δe`, its identity strategy is a Bayesian Nash equilibrium, and the type `⟨p, h⟩` realises
  every `Δe`-rationalizable pair `p`.

The ⟹ rests on the generic-in-`C` construction `ratBasedOn` + the *marginal-preservation* crux
`exogMarginal_inducedFullConjecture_ratBasedOn` (`exogMarginal i (induced) = exogMarginal i (conj)`,
proved via `typeMass_ratBasedOn = 1/(C i).ncard` forcing the normalisation factor to `1`).
-/

end SubjectiveBayesianGame

/-! ### Theorem 33 (⟹): the construction -/

namespace PayoffUncertaintyGame

open Finset

variable {G : PayoffUncertaintyGame} [Fintype G.Player] [DecidableEq G.Player]
  [Fintype G.Residual] [∀ i, Fintype (G.InfoType i)] [∀ i, DecidableEq (G.InfoType i)]
  [∀ i, Fintype (G.Action i)] [∀ i, DecidableEq (G.Action i)]

/-- A rationalizable information-type/action pair of player `i`, as a finite type. -/
abbrev RatPairType (G : PayoffUncertaintyGame) [Fintype G.Player] [DecidableEq G.Player]
    [Fintype G.Residual] [∀ i, Fintype (G.InfoType i)] [∀ i, Fintype (G.Action i)] (i : G.Player) :
    Type _ :=
  {p : G.InfoType i × G.Action i // p ∈ G.Rationalizable i}

/-- A justifying conjecture for a rationalizable pair. -/
noncomputable def conjForFull (i : G.Player) (tᵢ : RatPairType G i) : G.FullProfile → ℝ :=
  (G.rationalizable_isBestResponseSet i tᵢ.val tᵢ.property).choose

theorem conjForFull_isDistribution (i : G.Player) (tᵢ : RatPairType G i) :
    G.IsDistribution (conjForFull i tᵢ) :=
  (G.rationalizable_isBestResponseSet i tᵢ.val tᵢ.property).choose_spec.1

theorem conjForFull_supportedOn (i : G.Player) (tᵢ : RatPairType G i) :
    G.BeliefSupportedOn (conjForFull i tᵢ) G.Rationalizable i :=
  (G.rationalizable_isBestResponseSet i tᵢ.val tᵢ.property).choose_spec.2.1

theorem conjForFull_best (i : G.Player) (tᵢ : RatPairType G i) :
    G.IsBestResponseToBelief (conjForFull i tᵢ) i tᵢ.val.1 tᵢ.val.2 :=
  (G.rationalizable_isBestResponseSet i tᵢ.val tᵢ.property).choose_spec.2.2

/-- The **Bayesian game based on `Ĝ`** built from the rationalizable set: states are rationalizable
full profiles, types are rationalizable pairs, the info-type decoder reads the pair's type, and the
prior is the doubly-marginalised justifying conjecture. -/
@[reducible] noncomputable def ratBased (G : PayoffUncertaintyGame) [Fintype G.Player]
    [DecidableEq G.Player] [Fintype G.Residual] [∀ i, Fintype (G.InfoType i)]
    [∀ i, DecidableEq (G.InfoType i)] [∀ i, Fintype (G.Action i)] [∀ i, DecidableEq (G.Action i)] :
    SubjectiveBayesianGame G where
  Ω := {fp : G.FullProfile // ∀ j, (fp.2.1 j, fp.2.2 j) ∈ G.Rationalizable j}
  T := RatPairType G
  τ := fun i ω => ⟨(ω.val.2.1 i, ω.val.2.2 i), ω.property i⟩
  ϑ := fun i tᵢ => tᵢ.val.1
  ϑ₀ := fun ω => ω.val.1
  p := fun i ω => (1 / ((G.Rationalizable i).ncard : ℝ))
    * ∑ θ', ∑ a', conjForFull i ⟨(ω.val.2.1 i, ω.val.2.2 i), ω.property i⟩
        ⟨ω.val.1, Function.update ω.val.2.1 i θ', Function.update ω.val.2.2 i a'⟩

/-- The identity-decoding strategy: play the action component of the suggested pair. -/
def ratBasedStrategy : (ratBased G).Strategy := fun _ tᵢ => tᵢ.val.2

/-- **The double-marginal reindexing lemma** (generic in the restriction `C`). Averaging an
`i`-slot-invariant `g` against a conjecture `μ` supported on `C` equals the sum, over full profiles
`b` with all coordinates in `C` and `i`-pair `pi`, of the doubly-`i`-marginalised weight times `g b`. -/
theorem sum_reindex_of (i : G.Player) (C : G.Restriction) (pi : G.InfoType i × G.Action i)
    (hpi : pi ∈ C i) (μ : G.FullProfile → ℝ)
    (hμ : G.BeliefSupportedOn μ C i) (g : G.FullProfile → ℝ)
    (hg : ∀ (fp : G.FullProfile) θ' a',
      g ⟨fp.1, Function.update fp.2.1 i θ', Function.update fp.2.2 i a'⟩ = g fp) :
    (∑ fp, μ fp * g fp)
      = ∑ b ∈ univ.filter (fun b : G.FullProfile => ∀ j, (b.2.1 j, b.2.2 j) ∈ C j),
          if (b.2.1 i, b.2.2 i) = pi
            then (∑ θ', ∑ a', μ ⟨b.1, Function.update b.2.1 i θ', Function.update b.2.2 i a'⟩) * g b
            else 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun fp : G.FullProfile =>
      (⟨fp.1, Function.update fp.2.1 i pi.1, Function.update fp.2.2 i pi.2⟩ : G.FullProfile))
    (t := univ) (fun a _ => mem_univ _)]
  have hfib : ∀ b : G.FullProfile,
      (∑ fp ∈ univ.filter (fun fp =>
          (⟨fp.1, Function.update fp.2.1 i pi.1, Function.update fp.2.2 i pi.2⟩
            : G.FullProfile) = b), μ fp * g fp)
        = if (b.2.1 i, b.2.2 i) = pi
            then (∑ θ', ∑ a', μ ⟨b.1, Function.update b.2.1 i θ', Function.update b.2.2 i a'⟩) * g b
            else 0 := by
    rintro ⟨bθ, bT, bA⟩
    by_cases hb : (bT i, bA i) = pi
    · rw [if_pos hb]
      have hbi1 : bT i = pi.1 := (Prod.ext_iff.mp hb).1
      have hbi2 : bA i = pi.2 := (Prod.ext_iff.mp hb).2
      have himg : (univ.filter (fun fp : G.FullProfile =>
            (⟨fp.1, Function.update fp.2.1 i pi.1, Function.update fp.2.2 i pi.2⟩
              : G.FullProfile) = ⟨bθ, bT, bA⟩))
          = (univ : Finset (G.InfoType i × G.Action i)).image
              (fun p => (⟨bθ, Function.update bT i p.1, Function.update bA i p.2⟩
                : G.FullProfile)) := by
        ext ⟨fθ, fT, fA⟩
        simp only [mem_filter, mem_univ, true_and, mem_image, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, h2, h3⟩
          refine ⟨(fT i, fA i), rfl, funext fun k => ?_, funext fun k => ?_⟩
          · by_cases hk : k = i
            · subst hk; rw [Function.update_self]
            · rw [Function.update_of_ne hk, ← h2, Function.update_of_ne hk]
          · by_cases hk : k = i
            · subst hk; rw [Function.update_self]
            · rw [Function.update_of_ne hk, ← h3, Function.update_of_ne hk]
        · rintro ⟨p, rfl, rfl, rfl⟩
          refine ⟨rfl, funext fun k => ?_, funext fun k => ?_⟩
          · by_cases hk : k = i
            · rw [hk, Function.update_self]; exact hbi1.symm
            · rw [Function.update_of_ne hk, Function.update_of_ne hk]
          · by_cases hk : k = i
            · rw [hk, Function.update_self]; exact hbi2.symm
            · rw [Function.update_of_ne hk, Function.update_of_ne hk]
      rw [himg, Finset.sum_image (fun p _ q _ hpq => by
        have h2 := congrArg (fun fp : G.FullProfile => fp.2.1 i) hpq
        have h3 := congrArg (fun fp : G.FullProfile => fp.2.2 i) hpq
        simp only [Function.update_self] at h2 h3
        exact Prod.ext h2 h3)]
      rw [Finset.sum_congr rfl (fun x _ => by rw [hg (bθ, bT, bA) x.1 x.2]),
        ← Finset.sum_mul, Fintype.sum_prod_type]
    · rw [if_neg hb]
      refine Finset.sum_eq_zero fun fp hfp => ?_
      rw [mem_filter] at hfp
      apply absurd _ hb
      have h2 : Function.update fp.2.1 i pi.1 = bT :=
        congrArg (fun x : G.FullProfile => x.2.1) hfp.2
      have h3 : Function.update fp.2.2 i pi.2 = bA :=
        congrArg (fun x : G.FullProfile => x.2.2) hfp.2
      rw [← h2, ← h3, Function.update_self, Function.update_self]
  rw [Finset.sum_congr rfl fun b _ => hfib b]
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun b _ hb => ?_).symm
  simp only [mem_filter, mem_univ, true_and, not_forall] at hb
  obtain ⟨j, hj⟩ := hb
  by_cases hbi : (b.2.1 i, b.2.2 i) = pi
  · rw [if_pos hbi]
    have hji : j ≠ i := by rintro rfl; exact hj (hbi ▸ hpi)
    rw [show (∑ θ', ∑ a', μ ⟨b.1, Function.update b.2.1 i θ', Function.update b.2.2 i a'⟩) = 0 from
      Finset.sum_eq_zero fun θ' _ => Finset.sum_eq_zero fun a' _ =>
        hμ _ ⟨j, hji, by
          simp only [Function.update_of_ne hji]; exact hj⟩,
      zero_mul]
  · rw [if_neg hbi]

/-- The double-marginal reindexing specialised to the rationalizable restriction. -/
theorem conjForFull_sum_reindex (i : G.Player) (tᵢ : RatPairType G i) (μ : G.FullProfile → ℝ)
    (hμ : G.BeliefSupportedOn μ G.Rationalizable i) (g : G.FullProfile → ℝ)
    (hg : ∀ (fp : G.FullProfile) θ' a',
      g ⟨fp.1, Function.update fp.2.1 i θ', Function.update fp.2.2 i a'⟩ = g fp) :
    (∑ fp, μ fp * g fp)
      = ∑ b ∈ univ.filter (fun b : G.FullProfile => ∀ j, (b.2.1 j, b.2.2 j) ∈ G.Rationalizable j),
          if (b.2.1 i, b.2.2 i) = tᵢ.val
            then (∑ θ', ∑ a', μ ⟨b.1, Function.update b.2.1 i θ', Function.update b.2.2 i a'⟩) * g b
            else 0 :=
  G.sum_reindex_of i G.Rationalizable tᵢ.val tᵢ.property μ hμ g hg

/-- **The interim deviation payoff of the based-on-`Ĝ` equilibrium equals the justifying
expected payoff** (up to the normalising constant). This is the bridge that turns the best-reply
property of `conjForFull` into the Bayesian equilibrium property. -/
theorem interimDevPayoff_ratBased (i : G.Player) (tᵢ : RatPairType G i) (aᵢ : G.Action i) :
    (ratBased G).toBayesianGame.interimDevPayoff ratBasedStrategy i tᵢ aᵢ
      = (1 / ((G.Rationalizable i).ncard : ℝ))
        * G.expectedPayoff (conjForFull i tᵢ) i tᵢ.val.1 aᵢ := by
  rw [show G.expectedPayoff (conjForFull i tᵢ) i tᵢ.val.1 aᵢ
        = ∑ fp : G.FullProfile, conjForFull i tᵢ fp
            * G.payoff i fp.1 (Function.update fp.2.1 i tᵢ.val.1) (Function.update fp.2.2 i aᵢ)
      from rfl,
    G.conjForFull_sum_reindex i tᵢ (conjForFull i tᵢ)
      (conjForFull_supportedOn i tᵢ) _
      (fun fp θ' a' => by simp only [Function.update_idem]),
    Finset.mul_sum, BayesianGame.interimDevPayoff,
    Finset.sum_subtype (univ.filter
        (fun fp : G.FullProfile => ∀ j, (fp.2.1 j, fp.2.2 j) ∈ G.Rationalizable j))
      (fun x => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ x)))
      (fun b => (1 / ((G.Rationalizable i).ncard : ℝ))
        * (if (b.2.1 i, b.2.2 i) = tᵢ.val
            then (∑ θ', ∑ a', conjForFull i tᵢ
                  ⟨b.1, Function.update b.2.1 i θ', Function.update b.2.2 i a'⟩)
              * G.payoff i b.1 (Function.update b.2.1 i tᵢ.val.1) (Function.update b.2.2 i aᵢ)
            else 0))]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hb : ((ω : G.FullProfile).2.1 i, (ω : G.FullProfile).2.2 i) = tᵢ.val
  · have hτ : (ratBased G).τ i ω = tᵢ := Subtype.ext hb
    have hconj : conjForFull i
          (⟨((ω : G.FullProfile).2.1 i, (ω : G.FullProfile).2.2 i), ω.property i⟩ : RatPairType G i)
        = conjForFull i tᵢ := congrArg (conjForFull i) (Subtype.ext hb)
    have hnoop : Function.update (ω : G.FullProfile).2.1 i tᵢ.val.1 = (ω : G.FullProfile).2.1 := by
      rw [show tᵢ.val.1 = (ω : G.FullProfile).2.1 i from (Prod.ext_iff.mp hb).1.symm,
        Function.update_eq_self]
    have hpay : (ratBased G).toBayesianGame.payoff i ω
          (Function.update ((ratBased G).toBayesianGame.realizedProfile ratBasedStrategy ω) i aᵢ)
        = G.payoff i (ω : G.FullProfile).1 (Function.update (ω : G.FullProfile).2.1 i tᵢ.val.1)
            (Function.update (ω : G.FullProfile).2.2 i aᵢ) := by
      show G.payoff i (ω : G.FullProfile).1 (fun j => (ω : G.FullProfile).2.1 j)
          (Function.update (fun j => (ω : G.FullProfile).2.2 j) i aᵢ) = _
      rw [hnoop]
    have hprior : (ratBased G).toBayesianGame.prior i ω
        = (1 / ((G.Rationalizable i).ncard : ℝ)) * ∑ θ', ∑ a', conjForFull i tᵢ
            ⟨(ω : G.FullProfile).1, Function.update (ω : G.FullProfile).2.1 i θ',
              Function.update (ω : G.FullProfile).2.2 i a'⟩ := by
      show (1 / ((G.Rationalizable i).ncard : ℝ)) * ∑ θ', ∑ a', conjForFull i
          (⟨((ω : G.FullProfile).2.1 i, (ω : G.FullProfile).2.2 i), ω.property i⟩ : RatPairType G i)
          ⟨(ω : G.FullProfile).1, Function.update (ω : G.FullProfile).2.1 i θ',
            Function.update (ω : G.FullProfile).2.2 i a'⟩ = _
      rw [hconj]
    rw [if_pos hτ, if_pos hb, hpay, hprior]
    ring
  · have hτ : ¬ (ratBased G).τ i ω = tᵢ := fun h => hb (Subtype.ext_iff.mp h)
    rw [if_neg hτ, if_neg hb, zero_mul, mul_zero]

/-- **The based-on-`Ĝ` identity strategy is a Bayesian Nash equilibrium.** -/
theorem ratBasedStrategy_isBayesianNashEquilibrium :
    (ratBased G).toBayesianGame.IsBayesianNashEquilibrium ratBasedStrategy := by
  intro i tᵢ aᵢ
  rw [← (ratBased G).toBayesianGame.interimDevPayoff_self ratBasedStrategy i tᵢ,
    interimDevPayoff_ratBased, interimDevPayoff_ratBased]
  exact mul_le_mul_of_nonneg_left (conjForFull_best i tᵢ aᵢ) (by positivity)

/-- **Theorem 33 (⟹).** Every rationalizable information-type/action pair is *selected* by the
based-on-`Ĝ` Bayesian equilibrium: the type `⟨p, h⟩` has information type `p.1` and plays `p.2`, so
its realised pair is exactly `p`. -/
theorem ratBased_realizes_rationalizable (i : G.Player) (p : G.InfoType i × G.Action i)
    (h : p ∈ G.Rationalizable i) :
    ((ratBased G).ϑ i ⟨p, h⟩, ratBasedStrategy i ⟨p, h⟩) = p := rfl

/-! #### Theorem 34 (⟹): the construction generic in the restriction `C` -/

/-- The based-on-`Ĝ` construction generic in a restriction `C` and a justifying-conjecture family
`conj`: states are profiles with every coordinate in `C`, types are `C`-pairs, the prior is the
doubly-marginalised `conj`. -/
@[reducible] noncomputable def ratBasedOn (C : G.Restriction)
    (conj : ∀ i, {p : G.InfoType i × G.Action i // p ∈ C i} → G.FullProfile → ℝ) :
    SubjectiveBayesianGame G where
  Ω := {fp : G.FullProfile // ∀ j, (fp.2.1 j, fp.2.2 j) ∈ C j}
  T := fun i => {p : G.InfoType i × G.Action i // p ∈ C i}
  τ := fun i ω => ⟨(ω.val.2.1 i, ω.val.2.2 i), ω.property i⟩
  ϑ := fun i tᵢ => tᵢ.val.1
  ϑ₀ := fun ω => ω.val.1
  p := fun i ω => (1 / ((C i).ncard : ℝ))
    * ∑ θ', ∑ a', conj i ⟨(ω.val.2.1 i, ω.val.2.2 i), ω.property i⟩
        ⟨ω.val.1, Function.update ω.val.2.1 i θ', Function.update ω.val.2.2 i a'⟩

/-- The identity-decoding strategy for the generic construction. -/
def ratBasedOnStrategy (C : G.Restriction)
    (conj : ∀ i, {p : G.InfoType i × G.Action i // p ∈ C i} → G.FullProfile → ℝ) :
    (ratBasedOn C conj).Strategy := fun _ tᵢ => tᵢ.val.2

variable (C : G.Restriction)
  (conj : ∀ i, {p : G.InfoType i × G.Action i // p ∈ C i} → G.FullProfile → ℝ)

/-- The generic interim-deviation-payoff bridge (Theorem 34 ⟹ analogue of
`interimDevPayoff_ratBased`). -/
theorem interimDevPayoff_ratBasedOn
    (hsupp : ∀ i tᵢ, G.BeliefSupportedOn (conj i tᵢ) C i) (i : G.Player)
    (tᵢ : {p : G.InfoType i × G.Action i // p ∈ C i}) (aᵢ : G.Action i) :
    (ratBasedOn C conj).toBayesianGame.interimDevPayoff (ratBasedOnStrategy C conj) i tᵢ aᵢ
      = (1 / ((C i).ncard : ℝ)) * G.expectedPayoff (conj i tᵢ) i tᵢ.val.1 aᵢ := by
  rw [show G.expectedPayoff (conj i tᵢ) i tᵢ.val.1 aᵢ
        = ∑ fp : G.FullProfile, conj i tᵢ fp
            * G.payoff i fp.1 (Function.update fp.2.1 i tᵢ.val.1) (Function.update fp.2.2 i aᵢ)
      from rfl,
    G.sum_reindex_of i C tᵢ.val tᵢ.property (conj i tᵢ) (hsupp i tᵢ) _
      (fun fp θ' a' => by simp only [Function.update_idem]),
    Finset.mul_sum, BayesianGame.interimDevPayoff,
    Finset.sum_subtype (univ.filter
        (fun fp : G.FullProfile => ∀ j, (fp.2.1 j, fp.2.2 j) ∈ C j))
      (fun x => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ x)))
      (fun b => (1 / ((C i).ncard : ℝ))
        * (if (b.2.1 i, b.2.2 i) = tᵢ.val
            then (∑ θ', ∑ a', conj i tᵢ
                  ⟨b.1, Function.update b.2.1 i θ', Function.update b.2.2 i a'⟩)
              * G.payoff i b.1 (Function.update b.2.1 i tᵢ.val.1) (Function.update b.2.2 i aᵢ)
            else 0))]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hb : ((ω : G.FullProfile).2.1 i, (ω : G.FullProfile).2.2 i) = tᵢ.val
  · have hτ : (ratBasedOn C conj).τ i ω = tᵢ := Subtype.ext hb
    have hconj : conj i
          (⟨((ω : G.FullProfile).2.1 i, (ω : G.FullProfile).2.2 i), ω.property i⟩
            : {p : G.InfoType i × G.Action i // p ∈ C i})
        = conj i tᵢ := congrArg (conj i) (Subtype.ext hb)
    have hnoop : Function.update (ω : G.FullProfile).2.1 i tᵢ.val.1 = (ω : G.FullProfile).2.1 := by
      rw [show tᵢ.val.1 = (ω : G.FullProfile).2.1 i from (Prod.ext_iff.mp hb).1.symm,
        Function.update_eq_self]
    have hpay : (ratBasedOn C conj).toBayesianGame.payoff i ω
          (Function.update ((ratBasedOn C conj).toBayesianGame.realizedProfile
            (ratBasedOnStrategy C conj) ω) i aᵢ)
        = G.payoff i (ω : G.FullProfile).1 (Function.update (ω : G.FullProfile).2.1 i tᵢ.val.1)
            (Function.update (ω : G.FullProfile).2.2 i aᵢ) := by
      show G.payoff i (ω : G.FullProfile).1 (fun j => (ω : G.FullProfile).2.1 j)
          (Function.update (fun j => (ω : G.FullProfile).2.2 j) i aᵢ) = _
      rw [hnoop]
    have hprior : (ratBasedOn C conj).toBayesianGame.prior i ω
        = (1 / ((C i).ncard : ℝ)) * ∑ θ', ∑ a', conj i tᵢ
            ⟨(ω : G.FullProfile).1, Function.update (ω : G.FullProfile).2.1 i θ',
              Function.update (ω : G.FullProfile).2.2 i a'⟩ := by
      show (1 / ((C i).ncard : ℝ)) * ∑ θ', ∑ a', conj i
          (⟨((ω : G.FullProfile).2.1 i, (ω : G.FullProfile).2.2 i), ω.property i⟩
            : {p : G.InfoType i × G.Action i // p ∈ C i})
          ⟨(ω : G.FullProfile).1, Function.update (ω : G.FullProfile).2.1 i θ',
            Function.update (ω : G.FullProfile).2.2 i a'⟩ = _
      rw [hconj]
    rw [if_pos hτ, if_pos hb, hpay, hprior]
    ring
  · have hτ : ¬ (ratBasedOn C conj).τ i ω = tᵢ := fun h => hb (Subtype.ext_iff.mp h)
    rw [if_neg hτ, if_neg hb, zero_mul, mul_zero]

/-- The generic construction's identity strategy is a Bayesian Nash equilibrium. -/
theorem ratBasedOn_isBayesianNashEquilibrium
    (hsupp : ∀ i tᵢ, G.BeliefSupportedOn (conj i tᵢ) C i)
    (hbest : ∀ i tᵢ, G.IsBestResponseToBelief (conj i tᵢ) i tᵢ.val.1 tᵢ.val.2) :
    (ratBasedOn C conj).toBayesianGame.IsBayesianNashEquilibrium (ratBasedOnStrategy C conj) := by
  intro i tᵢ aᵢ
  rw [← (ratBasedOn C conj).toBayesianGame.interimDevPayoff_self (ratBasedOnStrategy C conj) i tᵢ,
    interimDevPayoff_ratBasedOn C conj hsupp, interimDevPayoff_ratBasedOn C conj hsupp]
  exact mul_le_mul_of_nonneg_left (hbest i tᵢ aᵢ) (by positivity)

/-- **The generic construction's type mass is `1 / (C i).ncard`.** Hence `ncard · typeMass = 1`, the
fact that forces the marginal-preservation normalisation to be exact. -/
theorem typeMass_ratBasedOn (hdist : ∀ i tᵢ, G.IsDistribution (conj i tᵢ))
    (hsupp : ∀ i tᵢ, G.BeliefSupportedOn (conj i tᵢ) C i) (i : G.Player)
    (tᵢ : {p : G.InfoType i × G.Action i // p ∈ C i}) :
    (ratBasedOn C conj).toBayesianGame.typeMass i tᵢ = 1 / ((C i).ncard : ℝ) := by
  have hr := G.sum_reindex_of i C tᵢ.val tᵢ.property (conj i tᵢ) (hsupp i tᵢ)
    (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)
  simp only [mul_one] at hr
  rw [(hdist i tᵢ).2] at hr
  have key : (ratBasedOn C conj).toBayesianGame.typeMass i tᵢ
      = (1 / ((C i).ncard : ℝ)) * ∑ b ∈ univ.filter
            (fun fp : G.FullProfile => ∀ j, (fp.2.1 j, fp.2.2 j) ∈ C j),
          (if (b.2.1 i, b.2.2 i) = tᵢ.val
            then (∑ θ', ∑ a', conj i tᵢ
                  ⟨b.1, Function.update b.2.1 i θ', Function.update b.2.2 i a'⟩)
            else 0) := by
    rw [BayesianGame.typeMass, Finset.mul_sum,
      Finset.sum_subtype (univ.filter
          (fun fp : G.FullProfile => ∀ j, (fp.2.1 j, fp.2.2 j) ∈ C j))
        (fun x => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ x)))
        (fun b => (1 / ((C i).ncard : ℝ))
          * (if (b.2.1 i, b.2.2 i) = tᵢ.val
              then (∑ θ', ∑ a', conj i tᵢ
                    ⟨b.1, Function.update b.2.1 i θ', Function.update b.2.2 i a'⟩)
              else 0))]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hb : ((ω : G.FullProfile).2.1 i, (ω : G.FullProfile).2.2 i) = tᵢ.val
    · have hτ : (ratBasedOn C conj).τ i ω = tᵢ := Subtype.ext hb
      have hconj : conj i
            (⟨((ω : G.FullProfile).2.1 i, (ω : G.FullProfile).2.2 i), ω.property i⟩
              : {p : G.InfoType i × G.Action i // p ∈ C i})
          = conj i tᵢ := congrArg (conj i) (Subtype.ext hb)
      have hprior : (ratBasedOn C conj).toBayesianGame.prior i ω
          = (1 / ((C i).ncard : ℝ)) * ∑ θ', ∑ a', conj i tᵢ
              ⟨(ω : G.FullProfile).1, Function.update (ω : G.FullProfile).2.1 i θ',
                Function.update (ω : G.FullProfile).2.2 i a'⟩ := by
        show (1 / ((C i).ncard : ℝ)) * ∑ θ', ∑ a', conj i
            (⟨((ω : G.FullProfile).2.1 i, (ω : G.FullProfile).2.2 i), ω.property i⟩
              : {p : G.InfoType i × G.Action i // p ∈ C i})
            ⟨(ω : G.FullProfile).1, Function.update (ω : G.FullProfile).2.1 i θ',
              Function.update (ω : G.FullProfile).2.2 i a'⟩ = _
        rw [hconj]
      rw [if_pos hτ, if_pos hb, hprior]
    · have hτ : ¬ (ratBasedOn C conj).τ i ω = tᵢ := fun h => hb (Subtype.ext_iff.mp h)
      rw [if_neg hτ, if_neg hb, mul_zero]
  rw [key, ← hr, mul_one]

/-- The generic construction's induced conjecture, evaluated: it is supported on valid profiles with
`i`-pair `tᵢ`, where it equals the doubly-marginalised `conj` over the normalising mass. -/
theorem inducedFullConjecture_ratBasedOn_apply (i : G.Player)
    (tᵢ : {p : G.InfoType i × G.Action i // p ∈ C i}) (gp : G.FullProfile) :
    (ratBasedOn C conj).inducedFullConjecture (ratBasedOnStrategy C conj) i tᵢ gp
      = (if (∀ j, (gp.2.1 j, gp.2.2 j) ∈ C j) ∧ (gp.2.1 i, gp.2.2 i) = tᵢ.val
          then (1 / ((C i).ncard : ℝ)) * ∑ φ, ∑ b, conj i tᵢ
                ⟨gp.1, Function.update gp.2.1 i φ, Function.update gp.2.2 i b⟩
          else 0)
        / (ratBasedOn C conj).toBayesianGame.typeMass i tᵢ := by
  rw [SubjectiveBayesianGame.inducedFullConjecture]
  congr 1
  by_cases hgp : ∀ j, (gp.2.1 j, gp.2.2 j) ∈ C j
  · rw [Finset.sum_eq_single (⟨gp, hgp⟩ : (ratBasedOn C conj).Ω)]
    · by_cases hpair : (gp.2.1 i, gp.2.2 i) = tᵢ.val
      · rw [if_pos ⟨Subtype.ext hpair, rfl⟩, if_pos ⟨hgp, hpair⟩]
        show (ratBasedOn C conj).p i ⟨gp, hgp⟩ = _
        simp only [ratBasedOn]
        rw [congrArg (conj i) (Subtype.ext hpair)]
      · rw [if_neg (fun h => hpair (Subtype.ext_iff.mp h.1)), if_neg (fun h => hpair h.2)]
    · intro ω _ hω
      rw [if_neg]; rintro ⟨_, hdec⟩; exact hω (Subtype.ext hdec)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg (fun h => hgp h.1)]
    refine Finset.sum_eq_zero fun ω _ => ?_
    rw [if_neg]; rintro ⟨_, hdec⟩; exact hgp (hdec ▸ ω.property)

/-- Summing over action profiles with `i`-coordinate fixed to `v`, then over the `i`-coordinate,
recovers the full action sum (the `i`-coordinate-overwrite bijection). -/
theorem action_collapse (i : G.Player) (F : (∀ j, G.Action j) → ℝ) (v : G.Action i) :
    (∑ a ∈ univ.filter (fun a : (∀ j, G.Action j) => a i = v),
        ∑ b : G.Action i, F (Function.update a i b)) = ∑ d, F d := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij' (fun ab _ => Function.update ab.1 i ab.2)
    (fun d _ => (Function.update d i v, d i)) (fun _ _ => Finset.mem_univ _) (fun d _ => ?_)
    (fun ab hab => ?_) (fun d _ => ?_) (fun _ _ => rfl)
  · rw [Finset.mem_product, Finset.mem_filter]
    exact ⟨⟨Finset.mem_univ _, Function.update_self _ _ _⟩, Finset.mem_univ _⟩
  · rw [Finset.mem_product, Finset.mem_filter] at hab
    have ha : ab.1 i = v := hab.1.2
    refine Prod.ext ?_ ?_
    · show Function.update (Function.update ab.1 i ab.2) i v = ab.1
      rw [Function.update_idem, ← ha, Function.update_eq_self]
    · show (Function.update ab.1 i ab.2) i = ab.2
      rw [Function.update_self]
  · show Function.update (Function.update d i v) i (d i) = d
    rw [Function.update_idem, Function.update_eq_self]

/-- **Marginal preservation (Theorem 34 ⟹ crux).** The generic construction's induced conjecture has
the same exogenous marginal as the justifying conjecture: marginalising out `i`'s own slots undoes
the construction's `i`-pinning. -/
theorem exogMarginal_inducedFullConjecture_ratBasedOn
    (hdist : ∀ i tᵢ, G.IsDistribution (conj i tᵢ))
    (hsupp : ∀ i tᵢ, G.BeliefSupportedOn (conj i tᵢ) C i) (i : G.Player)
    (tᵢ : {p : G.InfoType i × G.Action i // p ∈ C i}) :
    PayoffUncertaintyGame.exogMarginal i
        ((ratBasedOn C conj).inducedFullConjecture (ratBasedOnStrategy C conj) i tᵢ)
      = PayoffUncertaintyGame.exogMarginal i (conj i tᵢ) := by
  have htm : (ratBasedOn C conj).toBayesianGame.typeMass i tᵢ = 1 / ((C i).ncard : ℝ) :=
    typeMass_ratBasedOn C conj hdist hsupp i tᵢ
  have hncard : ((C i).ncard : ℝ) ≠ 0 := by
    have : (C i).Nonempty := ⟨tᵢ.val, tᵢ.property⟩
    exact_mod_cast ((Set.ncard_pos (C i).toFinite).mpr this).ne'
  funext fp
  rw [PayoffUncertaintyGame.exogMarginal, PayoffUncertaintyGame.exogMarginal]
  have hMzero : ∀ a, (∃ j, j ≠ i ∧ (fp.2.1 j, a j) ∉ C j) →
      (∑ φ, ∑ b, conj i tᵢ ⟨fp.1, Function.update fp.2.1 i φ, Function.update a i b⟩) = 0 := by
    rintro a ⟨j, hji, hjC⟩
    refine Finset.sum_eq_zero fun φ _ => Finset.sum_eq_zero fun b _ => hsupp i tᵢ _ ⟨j, hji, ?_⟩
    simpa only [Function.update_of_ne hji] using hjC
  -- Step 1: each induced value simplifies to `if cond then (conj-mass) else 0`.
  have hindeq : ∀ θᵢ' a, (ratBasedOn C conj).inducedFullConjecture (ratBasedOnStrategy C conj) i tᵢ
        ⟨fp.1, Function.update fp.2.1 i θᵢ', a⟩
      = if (∀ j, (Function.update fp.2.1 i θᵢ' j, a j) ∈ C j) ∧ (θᵢ', a i) = tᵢ.val
        then ∑ φ, ∑ b, conj i tᵢ ⟨fp.1, Function.update fp.2.1 i φ, Function.update a i b⟩ else 0 := by
    intro θᵢ' a
    rw [inducedFullConjecture_ratBasedOn_apply, htm]
    simp only [Function.update_self, Function.update_idem]
    split_ifs with hc
    · rw [mul_comm, mul_div_assoc, div_self (one_div_ne_zero hncard), mul_one]
    · rw [zero_div]
  rw [Finset.sum_congr rfl fun θᵢ' _ => Finset.sum_congr rfl fun a _ => hindeq θᵢ' a,
    Finset.sum_comm]
  -- Step 2: collapse the `θᵢ'` sum (pinned to `tᵢ.val.1`).
  have hθ : ∀ a, (∑ θᵢ', if (∀ j, (Function.update fp.2.1 i θᵢ' j, a j) ∈ C j) ∧ (θᵢ', a i) = tᵢ.val
        then (∑ φ, ∑ b, conj i tᵢ ⟨fp.1, Function.update fp.2.1 i φ, Function.update a i b⟩) else 0)
      = if a i = tᵢ.val.2
        then (∑ φ, ∑ b, conj i tᵢ ⟨fp.1, Function.update fp.2.1 i φ, Function.update a i b⟩) else 0 := by
    intro a
    rw [Finset.sum_eq_single tᵢ.val.1]
    · by_cases hai : a i = tᵢ.val.2
      · rw [if_pos hai]
        by_cases hv : ∀ j, j ≠ i → (fp.2.1 j, a j) ∈ C j
        · have hcond : (∀ j, (Function.update fp.2.1 i tᵢ.val.1 j, a j) ∈ C j)
              ∧ (tᵢ.val.1, a i) = tᵢ.val := by
            refine ⟨fun j => ?_, Prod.ext rfl hai⟩
            by_cases hj : j = i
            · subst hj; rw [Function.update_self, hai]; exact tᵢ.property
            · rw [Function.update_of_ne hj]; exact hv j hj
          rw [if_pos hcond]
        · rw [if_neg fun h => hv fun j hj => by
            have := h.1 j; rwa [Function.update_of_ne hj] at this]
          push_neg at hv
          obtain ⟨j, hji, hjC⟩ := hv
          exact (hMzero a ⟨j, hji, hjC⟩).symm
      · rw [if_neg hai, if_neg fun h => hai (Prod.ext_iff.mp h.2).2]
    · intro θ' _ hθ'
      rw [if_neg fun h => hθ' (Prod.ext_iff.mp h.2).1]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun a _ => hθ a, ← Finset.sum_filter, Finset.sum_comm]
  -- Step 3: collapse each inner action sum via `action_collapse`.
  exact Finset.sum_congr rfl fun φ _ =>
    action_collapse i (fun d => conj i tᵢ ⟨fp.1, Function.update fp.2.1 i φ, d⟩) tᵢ.val.2

/-! #### Theorem 34 (⟹): the construction yields the exogenous restrictions -/

variable (Δe : G.BeliefRestriction)

/-- The Δ-justifying conjecture family used by the Δ-construction. -/
noncomputable def deltaConj (i : G.Player)
    (tᵢ : {p : G.InfoType i × G.Action i // p ∈ G.DeltaRationalizable (G.fullRestrictionOfExog Δe) i}) :
    G.FullProfile → ℝ :=
  (G.deltaRationalizable_isDeltaBestResponseSet (G.fullRestrictionOfExog Δe) i tᵢ.val
    tᵢ.property).choose

theorem deltaConj_isDistribution (i tᵢ) : G.IsDistribution (deltaConj Δe i tᵢ) :=
  (G.deltaRationalizable_isDeltaBestResponseSet (G.fullRestrictionOfExog Δe) i tᵢ.val
    tᵢ.property).choose_spec.2.1

theorem deltaConj_supportedOn (i tᵢ) :
    G.BeliefSupportedOn (deltaConj Δe i tᵢ) (G.DeltaRationalizable (G.fullRestrictionOfExog Δe)) i :=
  (G.deltaRationalizable_isDeltaBestResponseSet (G.fullRestrictionOfExog Δe) i tᵢ.val
    tᵢ.property).choose_spec.2.2.1

theorem deltaConj_best (i tᵢ) : G.IsBestResponseToBelief (deltaConj Δe i tᵢ) i tᵢ.val.1 tᵢ.val.2 :=
  (G.deltaRationalizable_isDeltaBestResponseSet (G.fullRestrictionOfExog Δe) i tᵢ.val
    tᵢ.property).choose_spec.2.2.2

theorem deltaConj_exogMem (i tᵢ) :
    PayoffUncertaintyGame.exogMarginal i (deltaConj Δe i tᵢ) ∈ Δe i tᵢ.val.1 :=
  (G.deltaRationalizable_isDeltaBestResponseSet (G.fullRestrictionOfExog Δe) i tᵢ.val
    tᵢ.property).choose_spec.1

/-- **Theorem 34 (⟹), *yields* part.** The Δ-construction yields the exogenous restrictions `Δe`. -/
theorem deltaRatBased_yieldsExog :
    (ratBasedOn (G.DeltaRationalizable (G.fullRestrictionOfExog Δe)) (deltaConj Δe)).YieldsExogRestrictions
      (ratBasedOnStrategy (G.DeltaRationalizable (G.fullRestrictionOfExog Δe)) (deltaConj Δe)) Δe := by
  intro i tᵢ
  rw [exogMarginal_inducedFullConjecture_ratBasedOn _ _ (deltaConj_isDistribution Δe)
    (deltaConj_supportedOn Δe)]
  exact deltaConj_exogMem Δe i tᵢ

/-- **Theorem 34 (⟹), *equilibrium* part.** The Δ-construction's identity strategy is a Bayesian
Nash equilibrium. -/
theorem deltaRatBased_isBayesianNashEquilibrium :
    (ratBasedOn (G.DeltaRationalizable (G.fullRestrictionOfExog Δe))
        (deltaConj Δe)).toBayesianGame.IsBayesianNashEquilibrium (ratBasedOnStrategy (G.DeltaRationalizable (G.fullRestrictionOfExog Δe)) (deltaConj Δe)) :=
  ratBasedOn_isBayesianNashEquilibrium _ _ (deltaConj_supportedOn Δe) (deltaConj_best Δe)

/-- **Theorem 34 (⟹), *realisation* part.** Every `Δe`-rationalizable pair `p` is realised: the
type `⟨p, h⟩` has information type `p.1` and plays `p.2`. -/
theorem deltaRatBased_realizes (i : G.Player) (p : G.InfoType i × G.Action i)
    (h : p ∈ G.DeltaRationalizable (G.fullRestrictionOfExog Δe) i) :
    ((ratBasedOn (G.DeltaRationalizable (G.fullRestrictionOfExog Δe)) (deltaConj Δe)).ϑ i ⟨p, h⟩,
      ratBasedOnStrategy (G.DeltaRationalizable (G.fullRestrictionOfExog Δe)) (deltaConj Δe) i ⟨p, h⟩) = p := rfl

end PayoffUncertaintyGame

end EcoLean.GameTheory
