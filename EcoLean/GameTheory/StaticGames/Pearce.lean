import EcoLean.GameTheory.StaticGames.MixedDominance
import EcoLean.GameTheory.StaticGames.CorrelatedEquilibrium
import EcoLean.MathematicalMiscellany.Farkas

/-!
# Pearce's lemma

Pearce's characterization of mixed strict dominance: for a finite game, an action is strictly
dominated by a mixed strategy iff it is **never a best response** to any belief over the opponents'
action profiles.

* `mixedStrictlyDominated_not_isBestResponseToBelief` — the easy direction (dominated ⟹ never a best
  response), a strict averaging argument.
* `exists_belief_of_not_mixedStrictlyDominated` — the hard direction (not dominated ⟹ a best response
  to some belief), obtained from **Farkas's lemma** through Gordan's theorem of the alternative
  (`LinearInequalities.exists_separating_distribution_via_farkas`) applied to the gain matrix
  `g ci a = devPayoff a i ci - devPayoff a i bi`.

A finite type of players with finite action sets is assumed throughout, so beliefs over action
profiles can be summed.
-/

namespace EcoLean.GameTheory

namespace StaticGame

open scoped BigOperators

variable {G : StaticGame} [Fintype G.Player] [DecidableEq G.Player] [∀ i, Fintype (G.Action i)]

/-- `bi` is a *best response to the belief `μ`* (a distribution over opponent profiles): no action
yields a higher expected payoff than `bi` under `μ`. -/
def IsBestResponseToBelief (μ : G.ActionProfile → ℝ) (i : G.Player) (bi : G.Action i) : Prop :=
  ∀ ci : G.Action i, (∑ a, μ a * G.devPayoff a i ci) ≤ ∑ a, μ a * G.devPayoff a i bi

/-! ### Easy direction: dominated ⟹ never a best response -/

/-- A mixed-strictly-dominated action is never a best response to any belief: averaging the
best-response inequalities with the dominating mixture yields a strict contradiction. -/
theorem mixedStrictlyDominated_not_isBestResponseToBelief {i : G.Player} {bi : G.Action i}
    (hdom : G.IsMixedStrictlyDominated i bi) {μ : G.ActionProfile → ℝ}
    (hμ : G.IsCorrelatedDistribution μ) : ¬ G.IsBestResponseToBelief μ i bi := by
  obtain ⟨σ, ⟨hσnn, hσsum⟩, hσdom⟩ := hdom
  obtain ⟨hμnn, hμsum⟩ := hμ
  intro hbr
  -- Swap the order of summation: average `i`'s payoff over `σ`.
  have hswap : ∑ a, μ a * (∑ ci, σ ci * G.devPayoff a i ci)
      = ∑ ci, σ ci * (∑ a, μ a * G.devPayoff a i ci) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun ci _ => Finset.sum_congr rfl fun a _ => by ring
  -- The averaged best-response inequality.
  have hub : ∑ ci, σ ci * (∑ a, μ a * G.devPayoff a i ci)
      ≤ ∑ a, μ a * G.devPayoff a i bi := by
    calc ∑ ci, σ ci * (∑ a, μ a * G.devPayoff a i ci)
        ≤ ∑ ci, σ ci * (∑ a, μ a * G.devPayoff a i bi) :=
          Finset.sum_le_sum fun ci _ => mul_le_mul_of_nonneg_left (hbr ci) (hσnn ci)
      _ = ∑ a, μ a * G.devPayoff a i bi := by rw [← Finset.sum_mul, hσsum, one_mul]
  -- But strict dominance makes the average strictly larger.
  have hpos : ∃ a₀, 0 < μ a₀ := by
    by_contra h
    push_neg at h
    have : ∑ a, μ a ≤ 0 := Finset.sum_nonpos fun a _ => h a
    rw [hμsum] at this; linarith
  obtain ⟨a₀, ha₀⟩ := hpos
  have hlt : ∑ a, μ a * G.devPayoff a i bi
      < ∑ a, μ a * (∑ ci, σ ci * G.devPayoff a i ci) :=
    Finset.sum_lt_sum (fun a _ => mul_le_mul_of_nonneg_left (le_of_lt (hσdom a)) (hμnn a))
      ⟨a₀, Finset.mem_univ a₀, mul_lt_mul_of_pos_left (hσdom a₀) ha₀⟩
  rw [hswap] at hlt
  linarith [hub, hlt]

/-! ### Hard direction: not dominated ⟹ best response to some belief -/

open scoped Classical in
/-- If `bi` is **not** strictly dominated by any mixed strategy, then `bi` is a best response to some
belief over the opponents' profiles — the hard half of Pearce's lemma. It is exactly
`LinearInequalities.exists_separating_distribution_via_farkas` (Gordan's theorem of the alternative,
**derived from Farkas's lemma**) applied to the gain matrix `g ci a = devPayoff a i ci - devPayoff a i bi`. -/
theorem exists_belief_of_not_mixedStrictlyDominated (i : G.Player) (bi : G.Action i)
    (h : ¬ G.IsMixedStrictlyDominated i bi) :
    ∃ μ : G.ActionProfile → ℝ, G.IsCorrelatedDistribution μ ∧ G.IsBestResponseToBelief μ i bi := by
  classical
  haveI : Nonempty (G.Action i) := ⟨bi⟩
  by_cases hane : Nonempty G.ActionProfile
  · haveI := hane
    obtain ⟨y, hymem, hyle⟩ :=
      EconLib.LinearInequalities.exists_separating_distribution_via_farkas
        (fun (ci : G.Action i) (a : G.ActionProfile) => G.devPayoff a i ci - G.devPayoff a i bi)
        (by
          rintro ⟨x, hx, hpos⟩
          refine h ⟨x, hx, fun a => ?_⟩
          have hp := hpos a
          have hsum : ∑ ci, x ci * (G.devPayoff a i ci - G.devPayoff a i bi)
              = (∑ ci, x ci * G.devPayoff a i ci) - G.devPayoff a i bi := by
            rw [show (∑ ci, x ci * (G.devPayoff a i ci - G.devPayoff a i bi))
                = ∑ ci, (x ci * G.devPayoff a i ci - x ci * G.devPayoff a i bi) from
              Finset.sum_congr rfl fun ci _ => by ring, Finset.sum_sub_distrib, ← Finset.sum_mul,
              hx.2, one_mul]
          rw [hsum] at hp
          linarith)
    refine ⟨y, hymem, fun ci => ?_⟩
    have hyi : ∑ a, y a * (G.devPayoff a i ci - G.devPayoff a i bi) ≤ 0 := hyle ci
    have hsum : ∑ a, y a * (G.devPayoff a i ci - G.devPayoff a i bi)
        = (∑ a, y a * G.devPayoff a i ci) - ∑ a, y a * G.devPayoff a i bi := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [hsum] at hyi
    linarith
  · exact absurd ⟨Pi.single bi 1, single_mem_stdSimplex ℝ bi, fun a => (hane ⟨a⟩).elim⟩ h

/-- **Pearce's lemma.** An action is strictly dominated by a mixed strategy iff it is never a best
response to a belief over the opponents' profiles. -/
theorem isMixedStrictlyDominated_iff_not_exists_belief (i : G.Player) (bi : G.Action i) :
    G.IsMixedStrictlyDominated i bi ↔
      ¬ ∃ μ : G.ActionProfile → ℝ, G.IsCorrelatedDistribution μ ∧ G.IsBestResponseToBelief μ i bi := by
  constructor
  · rintro hdom ⟨μ, hμ, hbr⟩
    exact mixedStrictlyDominated_not_isBestResponseToBelief hdom hμ hbr
  · intro hno
    by_contra hd
    exact hno (exists_belief_of_not_mixedStrictlyDominated i bi hd)

end StaticGame

end EcoLean.GameTheory
