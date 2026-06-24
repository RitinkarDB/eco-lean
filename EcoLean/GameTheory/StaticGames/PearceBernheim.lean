import EcoLean.GameTheory.StaticGames.CorrelatedRationalizability

/-!
# Pearce's theorem: correlated rationalizability = iterated mixed dominance

Following Battigalli–Catonini–De Vito, *Game Theory: Analysis of Strategic Thinking* (§4.4), this file
proves the **Pearce–Bernheim characterization**: an action is correlated-rationalizable iff it belongs
to the largest restriction *closed under strict dominance by mixed strategies*. The engine is the
**hard half of Pearce's lemma, relative to a restriction** (`exists_belief_of_not_mixedStrictlyDominatedOn`):
an action not strictly dominated by a mixture against the `X`-supported profiles is a best response to
a correlated belief supported on `X`. This is a separating-hyperplane argument — Gordan's theorem
(`EconLib.LinearInequalities.exists_separating_distribution_via_farkas`, itself from Farkas's lemma)
applied to the gain matrix over the finite set of `X`-supported opponent profiles.

* `IsMixedStrictlyDominatedOn` — strict dominance by a mixture, relative to a restriction.
* `exists_belief_of_not_mixedStrictlyDominatedOn` / `isBeliefBestResponseWithin_not_mixedStrictlyDominatedOn`
  — the two halves of the restricted Pearce lemma, assembled into
  `not_mixedStrictlyDominatedOn_iff_isBeliefBestResponseWithin`.
* `IsMixedClosedSet` — a restriction with no mixed-dominated surviving action.
* `isCorrelatedBestResponseSet_iff_isMixedClosedSet` — being a correlated-best-response set is exactly
  being closed under mixed dominance (the restricted Pearce lemma, per element).
* `mem_correlatedRationalizable_iff_mixedClosed` — **Pearce's theorem**: the correlated-rationalizable
  actions are exactly those in the largest mixed-dominance-closed restriction.
-/

namespace EcoLean.GameTheory

namespace StaticGame

open scoped BigOperators

variable {G : StaticGame} [Fintype G.Player] [DecidableEq G.Player] [∀ i, Fintype (G.Action i)]

/-- `bi` is *strictly dominated by a mixed strategy, relative to the restriction `X`*: some mixture
`σ` over `i`'s actions strictly beats `bi` against every opponent configuration drawn from `X`. -/
def IsMixedStrictlyDominatedOn (X : G.Restriction) (i : G.Player) (bi : G.Action i) : Prop :=
  ∃ σ : G.Action i → ℝ, σ ∈ stdSimplex ℝ (G.Action i) ∧
    ∀ a : G.ActionProfile, (∀ j, j ≠ i → a j ∈ X j) →
      G.devPayoff a i bi < ∑ ai, σ ai * G.devPayoff a i ai

/-- Global mixed dominance (`MixedDominance.lean`) is the special case `X = ⊤`. -/
theorem mixedStrictlyDominatedOn_univ_iff (i : G.Player) (bi : G.Action i) :
    G.IsMixedStrictlyDominatedOn (fun _ => Set.univ) i bi ↔ G.IsMixedStrictlyDominated i bi := by
  constructor
  · rintro ⟨σ, hσ, hdom⟩; exact ⟨σ, hσ, fun a => hdom a fun _ _ => Set.mem_univ _⟩
  · rintro ⟨σ, hσ, hdom⟩; exact ⟨σ, hσ, fun a _ => hdom a⟩

/-! ### The restricted Pearce lemma -/

/-- *Easy half.* A justified action is not strictly dominated by a mixture relative to the restriction
it is justified within: the mixture would beat it in expectation under the justifying conjecture. -/
theorem isBeliefBestResponseWithin_not_mixedStrictlyDominatedOn {X : G.Restriction} {i : G.Player}
    {bi : G.Action i} (hbr : G.IsBeliefBestResponseWithin X i bi) :
    ¬ G.IsMixedStrictlyDominatedOn X i bi := by
  obtain ⟨μ, ⟨hμnn, hμsum⟩, hμsupp, hμbest⟩ := hbr
  rintro ⟨σ, ⟨hσnn, hσsum⟩, hσdom⟩
  have hsupp : ∀ a, 0 < μ a → ∀ j, j ≠ i → a j ∈ X j := fun a hp j hj => by
    by_contra hjX; exact hp.ne' (hμsupp a ⟨j, hj, hjX⟩)
  have hswap : ∑ a, μ a * (∑ ci, σ ci * G.devPayoff a i ci)
      = ∑ ci, σ ci * (∑ a, μ a * G.devPayoff a i ci) := by
    simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun ci _ => Finset.sum_congr rfl fun a _ => by ring
  have hub : ∑ ci, σ ci * (∑ a, μ a * G.devPayoff a i ci) ≤ ∑ a, μ a * G.devPayoff a i bi :=
    calc ∑ ci, σ ci * (∑ a, μ a * G.devPayoff a i ci)
        ≤ ∑ ci, σ ci * (∑ a, μ a * G.devPayoff a i bi) :=
          Finset.sum_le_sum fun ci _ => mul_le_mul_of_nonneg_left (hμbest ci) (hσnn ci)
      _ = ∑ a, μ a * G.devPayoff a i bi := by rw [← Finset.sum_mul, hσsum, one_mul]
  have hpos : ∃ a₀, 0 < μ a₀ := by
    by_contra hh; push_neg at hh
    have : ∑ a, μ a ≤ 0 := Finset.sum_nonpos fun a _ => hh a
    rw [hμsum] at this; linarith
  obtain ⟨a₀, ha₀⟩ := hpos
  have hlt : ∑ a, μ a * G.devPayoff a i bi < ∑ a, μ a * (∑ ci, σ ci * G.devPayoff a i ci) := by
    refine Finset.sum_lt_sum (fun a _ => ?_) ⟨a₀, Finset.mem_univ a₀, ?_⟩
    · rcases eq_or_lt_of_le (hμnn a) with h0 | h0
      · rw [← h0, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hσdom a (hsupp a h0))) (le_of_lt h0)
    · exact mul_lt_mul_of_pos_left (hσdom a₀ (hsupp a₀ ha₀)) ha₀
  rw [hswap] at hlt; linarith

open scoped Classical in
/-- *Hard half (Pearce, restricted).* An action not strictly dominated by a mixture relative to `X` is
a best response to a correlated belief supported on `X`. Gordan's theorem applied to the gain matrix
over the finite set of `X`-supported opponent profiles produces the belief. -/
theorem exists_belief_of_not_mixedStrictlyDominatedOn {X : G.Restriction} {i : G.Player}
    {bi : G.Action i} (h : ¬ G.IsMixedStrictlyDominatedOn X i bi) :
    G.IsBeliefBestResponseWithin X i bi := by
  classical
  haveI : Nonempty (G.Action i) := ⟨bi⟩
  let S : Finset G.ActionProfile := Finset.univ.filter (fun a => ∀ j, j ≠ i → a j ∈ X j)
  have hmemS : ∀ a, a ∈ S ↔ ∀ j, j ≠ i → a j ∈ X j := fun a => by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hSne : S.Nonempty
  · haveI : Nonempty ↥S := Finset.nonempty_coe_sort.mpr hSne
    obtain ⟨y, hymem, hyle⟩ := EconLib.LinearInequalities.exists_separating_distribution_via_farkas
      (fun (ci : G.Action i) (k : ↥S) => G.devPayoff k.1 i ci - G.devPayoff k.1 i bi)
      (by
        rintro ⟨x, hx, hpos⟩
        refine h ⟨x, hx, fun a ha => ?_⟩
        have hp := hpos ⟨a, (hmemS a).mpr ha⟩
        have hsum : ∑ ci, x ci * (G.devPayoff a i ci - G.devPayoff a i bi)
            = (∑ ci, x ci * G.devPayoff a i ci) - G.devPayoff a i bi := by
          rw [show (∑ ci, x ci * (G.devPayoff a i ci - G.devPayoff a i bi))
              = ∑ ci, (x ci * G.devPayoff a i ci - x ci * G.devPayoff a i bi) from
            Finset.sum_congr rfl fun ci _ => by ring, Finset.sum_sub_distrib, ← Finset.sum_mul,
            hx.2, one_mul]
        rw [hsum] at hp; linarith)
    set μ : G.ActionProfile → ℝ := fun a => if ha : a ∈ S then y ⟨a, ha⟩ else 0 with hμ
    have hμpos : ∀ a (ha : a ∈ S), μ a = y ⟨a, ha⟩ := fun a ha => by simp only [hμ, dif_pos ha]
    have hμneg : ∀ a, a ∉ S → μ a = 0 := fun a ha => by simp only [hμ, dif_neg ha]
    have hyμ : ∀ k : ↥S, μ k.1 = y k := fun k => by simp only [hμ, dif_pos k.2, Subtype.coe_eta]
    have hred : ∀ f : G.ActionProfile → ℝ, ∑ a, μ a * f a = ∑ k : ↥S, y k * f k.1 := by
      intro f
      rw [← Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => by rw [hμneg a ha, zero_mul]),
        ← Finset.sum_coe_sort S (fun a => μ a * f a)]
      exact Finset.sum_congr rfl fun k _ => by rw [hyμ k]
    refine ⟨μ, ⟨fun a => ?_, ?_⟩, ?_, ?_⟩
    · by_cases ha : a ∈ S
      · rw [hμpos a ha]; exact hymem.1 _
      · exact le_of_eq (hμneg a ha).symm
    · have h1 := hred (fun _ => (1 : ℝ)); simp only [mul_one] at h1; rw [h1]; exact hymem.2
    · rintro a ⟨j, hj, hjX⟩
      exact hμneg a (fun haS => hjX ((hmemS a).mp haS j hj))
    · intro ci
      rw [hred (fun a => G.devPayoff a i ci), hred (fun a => G.devPayoff a i bi)]
      have hle := hyle ci
      have hsub : ∑ k : ↥S, y k * (G.devPayoff k.1 i ci - G.devPayoff k.1 i bi)
          = (∑ k : ↥S, y k * G.devPayoff k.1 i ci) - ∑ k : ↥S, y k * G.devPayoff k.1 i bi := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
      rw [hsub] at hle; linarith
  · -- `S` empty: `bi` is vacuously mixed-dominated on `X`, contradicting `h`.
    exact absurd ⟨Pi.single bi 1, single_mem_stdSimplex ℝ bi,
      fun a ha => absurd ((hmemS a).mpr ha)
        (by rw [Finset.not_nonempty_iff_eq_empty.mp hSne]; exact Finset.notMem_empty a)⟩ h

/-- **The restricted Pearce lemma.** Relative to a restriction `X`, an action is a best response to
some conjecture supported on `X` iff it is not strictly dominated by a mixed strategy on `X`. -/
theorem not_mixedStrictlyDominatedOn_iff_isBeliefBestResponseWithin {X : G.Restriction}
    {i : G.Player} {bi : G.Action i} :
    ¬ G.IsMixedStrictlyDominatedOn X i bi ↔ G.IsBeliefBestResponseWithin X i bi :=
  ⟨exists_belief_of_not_mixedStrictlyDominatedOn,
    fun hbr => isBeliefBestResponseWithin_not_mixedStrictlyDominatedOn hbr⟩

/-! ### Pearce's theorem -/

/-- `X` is *closed under mixed dominance*: no surviving action is strictly dominated by a mixed
strategy relative to `X`. -/
def IsMixedClosedSet (X : G.Restriction) : Prop :=
  ∀ (i : G.Player), ∀ ai ∈ X i, ¬ G.IsMixedStrictlyDominatedOn X i ai

/-- A restriction is a correlated-best-response set iff it is closed under mixed dominance — the
restricted Pearce lemma applied to each surviving action. -/
theorem isCorrelatedBestResponseSet_iff_isMixedClosedSet (X : G.Restriction) :
    G.IsCorrelatedBestResponseSet X ↔ G.IsMixedClosedSet X :=
  ⟨fun hX i ai hai => isBeliefBestResponseWithin_not_mixedStrictlyDominatedOn (hX i ai hai),
    fun hX i ai hai => exists_belief_of_not_mixedStrictlyDominatedOn (hX i ai hai)⟩

/-- **Pearce's theorem (Pearce–Bernheim).** The correlated-rationalizable actions are exactly those in
the largest restriction closed under strict dominance by mixed strategies — rationalizability is the
fixed-point form of iterated elimination of strictly dominated (mixed) strategies. -/
theorem mem_correlatedRationalizable_iff_mixedClosed (i : G.Player) (ai : G.Action i) :
    ai ∈ G.CorrelatedRationalizable i ↔ ∃ X : G.Restriction, G.IsMixedClosedSet X ∧ ai ∈ X i := by
  rw [mem_correlatedRationalizable_iff]
  exact ⟨fun ⟨X, hX, haiX⟩ => ⟨X, (isCorrelatedBestResponseSet_iff_isMixedClosedSet X).mp hX, haiX⟩,
    fun ⟨X, hX, haiX⟩ => ⟨X, (isCorrelatedBestResponseSet_iff_isMixedClosedSet X).mpr hX, haiX⟩⟩

/-- `CorrelatedRationalizable` is itself closed under mixed dominance: no rationalizable action is
strictly dominated by a mixture against the rationalizable profiles. -/
theorem correlatedRationalizable_isMixedClosedSet : G.IsMixedClosedSet G.CorrelatedRationalizable :=
  (isCorrelatedBestResponseSet_iff_isMixedClosedSet _).mp
    correlatedRationalizable_isCorrelatedBestResponseSet

end StaticGame

end EcoLean.GameTheory
