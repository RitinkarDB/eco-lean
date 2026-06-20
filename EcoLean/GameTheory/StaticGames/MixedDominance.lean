import EcoLean.GameTheory.StaticGames.Rationalizability
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Strict dominance by mixed strategies

Strict dominance by a *mixed* strategy and its consequences, following Battigalli–Catonini–De Vito.
An action `bi` is strictly dominated by a mixed strategy when some probability distribution over the
player's actions does strictly better than `bi` against every opponent configuration. This is the
relevant notion for rationalizability: an action dominated by a mixture is never a best response.

Main results:

* `IsStrictlyDominated.isMixedStrictlyDominated` — pure strict dominance is the degenerate case.
* `mixedStrictlyDominated_not_bestResponseWithin` — a mixed-dominated action is never a best response
  within any restriction (the easy half of Pearce's lemma).
* `mixedStrictlyDominated_not_rationalizable` / `not_isNashEquilibrium_of_mixedStrictlyDominated` —
  hence it is not rationalizable and never played in a Nash equilibrium.

The converse (every never-best-response action is dominated by a mixture — the hard half of Pearce's
lemma, giving rationalizable = surviving) requires a separating-hyperplane argument and is not proved
here.

Finite action sets are assumed so the mixed payoff can be summed.
-/

namespace EcoLean.GameTheory

namespace StaticGame

open scoped BigOperators

variable {G : StaticGame} [DecidableEq G.Player] [∀ i, Fintype (G.Action i)]

/-- `bi` is *strictly dominated by a mixed strategy* for player `i`: some probability distribution `σ`
over `i`'s actions yields a strictly higher expected payoff than `bi` against every configuration of
the other players. -/
def IsMixedStrictlyDominated (i : G.Player) (bi : G.Action i) : Prop :=
  ∃ σ : G.Action i → ℝ, σ ∈ stdSimplex ℝ (G.Action i) ∧
    ∀ a : G.ActionProfile, G.devPayoff a i bi < ∑ ai, σ ai * G.devPayoff a i ai

/-- Pure strict dominance is the special case of mixed strict dominance with the degenerate
distribution concentrated on the dominating action. -/
theorem IsStrictlyDominated.isMixedStrictlyDominated {i : G.Player} {bi : G.Action i}
    (h : G.IsStrictlyDominated i bi) : G.IsMixedStrictlyDominated i bi := by
  classical
  obtain ⟨d, hd⟩ := h
  refine ⟨fun x => if x = d then 1 else 0, ⟨fun x => ?_, ?_⟩, fun a => ?_⟩
  · show (0 : ℝ) ≤ if x = d then (1 : ℝ) else 0
    split_ifs <;> norm_num
  · show (∑ x, if x = d then (1 : ℝ) else 0) = 1
    rw [Finset.sum_eq_single d (fun x _ hx => if_neg hx)
      (fun hh => absurd (Finset.mem_univ d) hh), if_pos rfl]
  · show G.devPayoff a i bi < ∑ x, (if x = d then (1 : ℝ) else 0) * G.devPayoff a i x
    rw [Finset.sum_eq_single d (fun x _ hx => by rw [if_neg hx, zero_mul])
      (fun hh => absurd (Finset.mem_univ d) hh), if_pos rfl, one_mul]
    exact hd a

/-- A mixed-dominated action is never a best response within any restriction: a best response would
weakly beat every pure action, hence weakly beat the dominating mixture, contradicting strict
dominance. This is the easy direction of Pearce's lemma. -/
theorem mixedStrictlyDominated_not_bestResponseWithin {i : G.Player} {bi : G.Action i}
    (h : G.IsMixedStrictlyDominated i bi) (X : G.Restriction) :
    ¬ G.BestResponseWithin X i bi := by
  obtain ⟨σ, ⟨hσnn, hσsum⟩, hσdom⟩ := h
  rintro ⟨a, _, hbest⟩
  have hle : ∑ ai, σ ai * G.devPayoff a i ai ≤ G.devPayoff a i bi :=
    calc ∑ ai, σ ai * G.devPayoff a i ai
        ≤ ∑ ai, σ ai * G.devPayoff a i bi :=
          Finset.sum_le_sum fun ai _ => mul_le_mul_of_nonneg_left (hbest ai) (hσnn ai)
      _ = G.devPayoff a i bi := by rw [← Finset.sum_mul, hσsum, one_mul]
  exact absurd (hσdom a) (not_lt.mpr hle)

/-- A mixed-dominated action is not rationalizable. -/
theorem mixedStrictlyDominated_not_rationalizable {i : G.Player} {bi : G.Action i}
    (h : G.IsMixedStrictlyDominated i bi) : bi ∉ G.Rationalizable i := fun hbi =>
  mixedStrictlyDominated_not_bestResponseWithin h G.Rationalizable
    (rationalizable_isBestResponseSet i bi hbi)

/-- A mixed-dominated action is never played in a Nash equilibrium. -/
theorem not_isNashEquilibrium_of_mixedStrictlyDominated {a : G.ActionProfile} {i : G.Player}
    (h : G.IsMixedStrictlyDominated i (a i)) : ¬ G.IsNashEquilibrium a := fun hNash =>
  mixedStrictlyDominated_not_rationalizable h (nash_mem_rationalizable hNash i)

end StaticGame

end EcoLean.GameTheory
