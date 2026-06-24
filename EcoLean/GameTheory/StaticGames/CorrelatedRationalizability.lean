import EcoLean.GameTheory.StaticGames.Pearce

/-!
# Correlated (belief-based) rationalizability

Following Battigalli–Catonini–De Vito, *Game Theory: Analysis of Strategic Thinking* (Chapter 4), a
player's *conjecture* is a probability distribution (a correlated belief) over the opponents' action
profiles, and an action is *justified* on a restriction `X` when it is a best response to some
conjecture supported on `X`. This is the belief-based rationalizability the book uses — strictly more
permissive than the *point*-rationalizability of `Rationalizability.lean`, since a correlated belief
may spread weight over several opponent profiles.

* `BeliefSupportedOn` / `IsBeliefBestResponseWithin` — a conjecture supported on `X`, and an action
  justified by such a conjecture.
* `IsCorrelatedBestResponseSet` / `CorrelatedRationalizable` — a self-justifying restriction, and the
  largest one (the **justification operator**'s greatest fixed point).
* `correlatedRationalizable_isCorrelatedBestResponseSet` / `subset_...` — `CorrelatedRationalizable`
  is itself a correlated-best-response set, and it is the largest.
* `rationalizable_subset_correlatedRationalizable` — every point-rationalizable action is
  correlated-rationalizable (a point conjecture is the Dirac belief).
* `nash_mem_correlatedRationalizable` — Nash plays are correlated-rationalizable.
* `isBeliefBestResponseWithin_not_mixedStrictlyDominated` — a justified action is never strictly
  dominated by a mixed strategy (the easy half of Pearce's lemma, belief form).
* `correlatedRationalizable_subset_survives` — correlated-rationalizable actions survive iterated
  elimination of strictly dominated strategies.

The converse — that every action surviving iterated elimination of strictly dominated *mixed*
strategies is correlated-rationalizable (the hard half of Pearce's lemma, iterated; the full
Pearce–Bernheim characterization) — needs the restricted separating-hyperplane argument and is left
for a follow-up.
-/

namespace EcoLean.GameTheory

namespace StaticGame

open scoped BigOperators

variable {G : StaticGame} [Fintype G.Player] [DecidableEq G.Player] [∀ i, Fintype (G.Action i)]

/-- A conjecture `μ` (a correlated belief over opponent profiles) is *supported on the restriction
`X`* for player `i`: it puts no weight on profiles where some opponent plays outside `X`. -/
def BeliefSupportedOn (μ : G.ActionProfile → ℝ) (X : G.Restriction) (i : G.Player) : Prop :=
  ∀ a : G.ActionProfile, (∃ j, j ≠ i ∧ a j ∉ X j) → μ a = 0

/-- `ai` is *justified within the restriction `X`*: it is a best response to some correlated belief
over the opponents' profiles supported on `X`. -/
def IsBeliefBestResponseWithin (X : G.Restriction) (i : G.Player) (ai : G.Action i) : Prop :=
  ∃ μ : G.ActionProfile → ℝ,
    G.IsCorrelatedDistribution μ ∧ G.BeliefSupportedOn μ X i ∧ G.IsBestResponseToBelief μ i ai

/-- `X` is a *correlated-best-response set*: every surviving action is justified within `X`. -/
def IsCorrelatedBestResponseSet (X : G.Restriction) : Prop :=
  ∀ (i : G.Player), ∀ ai ∈ X i, G.IsBeliefBestResponseWithin X i ai

/-- The *correlated-rationalizable* actions: those in some correlated-best-response set. Equivalently,
the largest correlated-best-response set (`correlatedRationalizable_isCorrelatedBestResponseSet`). -/
def CorrelatedRationalizable (G : StaticGame) [Fintype G.Player] [DecidableEq G.Player]
    [∀ i, Fintype (G.Action i)] : G.Restriction :=
  fun i => {ai | ∃ X : G.Restriction, G.IsCorrelatedBestResponseSet X ∧ ai ∈ X i}

theorem mem_correlatedRationalizable_iff (i : G.Player) (ai : G.Action i) :
    ai ∈ G.CorrelatedRationalizable i ↔
      ∃ X : G.Restriction, G.IsCorrelatedBestResponseSet X ∧ ai ∈ X i :=
  Iff.rfl

/-! ### Monotonicity of justification, and the largest fixed point -/

/-- Justification is monotone in the restriction: a belief supported on `X` is supported on any
larger `Y`, so an action justified within `X` is justified within `Y`. -/
theorem isBeliefBestResponseWithin_mono {X Y : G.Restriction} {i : G.Player} {ai : G.Action i}
    (hbr : G.IsBeliefBestResponseWithin X i ai) (hXY : ∀ j, X j ⊆ Y j) :
    G.IsBeliefBestResponseWithin Y i ai := by
  obtain ⟨μ, hμdist, hμsupp, hμbest⟩ := hbr
  refine ⟨μ, hμdist, ?_, hμbest⟩
  rintro a ⟨j, hj, hjY⟩
  exact hμsupp a ⟨j, hj, fun hjX => hjY (hXY j hjX)⟩

/-- Every correlated-best-response set is contained in the correlated-rationalizable actions. -/
theorem subset_correlatedRationalizable_of_isCorrelatedBestResponseSet {X : G.Restriction}
    (hX : G.IsCorrelatedBestResponseSet X) (i : G.Player) :
    X i ⊆ G.CorrelatedRationalizable i :=
  fun _ hai => ⟨X, hX, hai⟩

/-- The correlated-rationalizable actions form a correlated-best-response set: the justifying belief
of an action lives in some `X ⊆ CorrelatedRationalizable`, hence is supported on the latter. -/
theorem correlatedRationalizable_isCorrelatedBestResponseSet :
    G.IsCorrelatedBestResponseSet G.CorrelatedRationalizable := by
  intro i ai hai
  obtain ⟨X, hX, haiX⟩ := hai
  exact isBeliefBestResponseWithin_mono (hX i ai haiX)
    (subset_correlatedRationalizable_of_isCorrelatedBestResponseSet hX)

/-! ### Point-rationalizability and Nash equilibria are correlated-rationalizable -/

/-- The (point-)rationalizable actions form a correlated-best-response set: a point best response to a
profile `a` drawn from `Rationalizable` is a best response to the Dirac belief at `a`. -/
theorem rationalizable_isCorrelatedBestResponseSet :
    G.IsCorrelatedBestResponseSet G.Rationalizable := by
  intro i ai hai
  obtain ⟨a, haR, hbest⟩ := rationalizable_isBestResponseSet i ai hai
  refine ⟨G.dirac a, ⟨fun a' => by simp only [dirac]; split_ifs <;> norm_num,
    by simpa using sum_dirac_mul a (fun _ => (1 : ℝ))⟩, ?_, ?_⟩
  · rintro a' ⟨j, hj, hjR⟩
    show G.dirac a a' = 0
    simp only [dirac]
    rw [if_neg (fun h => by subst h; exact hjR (haR j hj))]
  · intro ci
    rw [sum_dirac_mul, sum_dirac_mul]
    exact hbest ci

/-- Every point-rationalizable action is correlated-rationalizable. -/
theorem rationalizable_subset_correlatedRationalizable (i : G.Player) :
    G.Rationalizable i ⊆ G.CorrelatedRationalizable i :=
  subset_correlatedRationalizable_of_isCorrelatedBestResponseSet
    rationalizable_isCorrelatedBestResponseSet i

/-- Every action played in a Nash equilibrium is correlated-rationalizable. -/
theorem nash_mem_correlatedRationalizable {a : G.ActionProfile} (hNash : G.IsNashEquilibrium a)
    (i : G.Player) : a i ∈ G.CorrelatedRationalizable i :=
  rationalizable_subset_correlatedRationalizable i (nash_mem_rationalizable hNash i)

/-! ### Justified actions are undominated and survive elimination -/

/-- A justified action is never strictly dominated by a mixed strategy: the dominating mixture would
beat it against every profile, hence in expectation under any conjecture, contradicting that it is a
best response. This is the easy half of Pearce's lemma in belief form. -/
theorem isBeliefBestResponseWithin_not_mixedStrictlyDominated {X : G.Restriction} {i : G.Player}
    {ai : G.Action i} (hbr : G.IsBeliefBestResponseWithin X i ai) :
    ¬ G.IsMixedStrictlyDominated i ai := by
  obtain ⟨μ, ⟨hμnn, hμsum⟩, _, hμbest⟩ := hbr
  rintro ⟨σ, ⟨hσnn, hσsum⟩, hσdom⟩
  -- Swap sums: the mixture's expected payoff under `μ` strictly exceeds `ai`'s.
  have hswap : ∑ a, μ a * (∑ ci, σ ci * G.devPayoff a i ci)
      = ∑ ci, σ ci * (∑ a, μ a * G.devPayoff a i ci) := by
    simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun ci _ => Finset.sum_congr rfl fun a _ => by ring
  have hub : ∑ ci, σ ci * (∑ a, μ a * G.devPayoff a i ci)
      ≤ ∑ a, μ a * G.devPayoff a i ai :=
    calc ∑ ci, σ ci * (∑ a, μ a * G.devPayoff a i ci)
        ≤ ∑ ci, σ ci * (∑ a, μ a * G.devPayoff a i ai) :=
          Finset.sum_le_sum fun ci _ => mul_le_mul_of_nonneg_left (hμbest ci) (hσnn ci)
      _ = ∑ a, μ a * G.devPayoff a i ai := by rw [← Finset.sum_mul, hσsum, one_mul]
  have hpos : ∃ a₀, 0 < μ a₀ := by
    by_contra h; push_neg at h
    have : ∑ a, μ a ≤ 0 := Finset.sum_nonpos fun a _ => h a
    rw [hμsum] at this; linarith
  obtain ⟨a₀, ha₀⟩ := hpos
  have hlt : ∑ a, μ a * G.devPayoff a i ai
      < ∑ a, μ a * (∑ ci, σ ci * G.devPayoff a i ci) :=
    Finset.sum_lt_sum (fun a _ => mul_le_mul_of_nonneg_left (le_of_lt (hσdom a)) (hμnn a))
      ⟨a₀, Finset.mem_univ a₀, mul_lt_mul_of_pos_left (hσdom a₀) ha₀⟩
  rw [hswap] at hlt
  linarith [hub, hlt]

/-- A justified action is never strictly dominated on the restriction it is justified within: the
dominator would beat it on every profile the conjecture deems possible, contradicting optimality. -/
theorem isBeliefBestResponseWithin_not_strictlyDominatedOn {X : G.Restriction} {i : G.Player}
    {ai : G.Action i} (hbr : G.IsBeliefBestResponseWithin X i ai) :
    ¬ G.StrictlyDominatedOn X i ai := by
  obtain ⟨μ, ⟨hμnn, hμsum⟩, hμsupp, hμbest⟩ := hbr
  rintro ⟨ci, _, hdom⟩
  have hsupp : ∀ a, 0 < μ a → ∀ j, j ≠ i → a j ∈ X j := by
    intro a hpos j hj
    by_contra hjX
    exact hpos.ne' (hμsupp a ⟨j, hj, hjX⟩)
  have hpos : ∃ a₀, 0 < μ a₀ := by
    by_contra h; push_neg at h
    have : ∑ a, μ a ≤ 0 := Finset.sum_nonpos fun a _ => h a
    rw [hμsum] at this; linarith
  obtain ⟨a₀, ha₀⟩ := hpos
  have hlt : ∑ a, μ a * G.devPayoff a i ai < ∑ a, μ a * G.devPayoff a i ci := by
    refine Finset.sum_lt_sum (fun a _ => ?_) ⟨a₀, Finset.mem_univ a₀, ?_⟩
    · rcases eq_or_lt_of_le (hμnn a) with h0 | h0
      · rw [← h0, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hdom a (hsupp a h0))) (le_of_lt h0)
    · exact mul_lt_mul_of_pos_left (hdom a₀ (hsupp a₀ ha₀)) ha₀
  exact absurd (hμbest ci) (not_le.mpr hlt)

theorem correlatedRationalizable_subset_iesds :
    ∀ (n : ℕ) (i : G.Player), G.CorrelatedRationalizable i ⊆ G.iesds n i := by
  intro n
  induction n with
  | zero => intro i ai _; exact Set.mem_univ _
  | succ k ih =>
      intro i ai hai
      rw [iesds_succ]
      refine ⟨ih i hai, isBeliefBestResponseWithin_not_strictlyDominatedOn ?_⟩
      exact isBeliefBestResponseWithin_mono
        (correlatedRationalizable_isCorrelatedBestResponseSet i ai hai) ih

/-- Correlated-rationalizable actions survive iterated elimination of strictly dominated strategies. -/
theorem correlatedRationalizable_subset_survives (i : G.Player) :
    G.CorrelatedRationalizable i ⊆ G.survives i :=
  fun _ hai n => correlatedRationalizable_subset_iesds n i hai

/-- If `a i` is a best response to a conjecture concentrated on profiles that agree with `a` off `i`,
then `a i` is a best response at `a` (the Nash condition for player `i`). The deviation payoff is
constant — equal to its value at `a` — across the conjecture's support, so the averaged
best-response inequality collapses to the pointwise one. -/
theorem isBestResponseAt_of_belief_supported_off {a : G.ActionProfile} {i : G.Player}
    {μ : G.ActionProfile → ℝ} (hdist : G.IsCorrelatedDistribution μ)
    (hsupp : ∀ b, 0 < μ b → ∀ j, j ≠ i → b j = a j)
    (hbest : G.IsBestResponseToBelief μ i (a i)) : G.IsBestResponseAt a i := by
  obtain ⟨hμnn, hμsum⟩ := hdist
  have hdev : ∀ ci, ∑ b, μ b * G.devPayoff b i ci = G.devPayoff a i ci := by
    intro ci
    have hterm : ∀ b, μ b * G.devPayoff b i ci = μ b * G.devPayoff a i ci := by
      intro b
      rcases eq_or_lt_of_le (hμnn b) with h0 | h0
      · rw [← h0, zero_mul, zero_mul]
      · congr 1
        have hoff := hsupp b h0
        have hagree : G.deviate b i ci = G.deviate a i ci := by
          funext j; by_cases hj : j = i
          · subst hj; rw [G.deviate_self, G.deviate_self]
          · rw [G.deviate_ne b ci hj, G.deviate_ne a ci hj, hoff j hj]
        show G.payoff i (G.deviate b i ci) = G.payoff i (G.deviate a i ci)
        rw [hagree]
    rw [Finset.sum_congr rfl (fun b _ => hterm b), ← Finset.sum_mul, hμsum, one_mul]
  intro ci
  have hb := hbest ci
  rw [hdev ci, hdev (a i), G.devPayoff_self] at hb
  exact hb

end StaticGame

end EcoLean.GameTheory
