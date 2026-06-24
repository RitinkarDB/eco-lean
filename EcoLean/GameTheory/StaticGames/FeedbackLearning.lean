import EcoLean.GameTheory.StaticGames.AnonymousSelfConfirmingEquilibrium
import EcoLean.GameTheory.StaticGames.LearningAndSolutionConcepts

/-!
# Feedback learning and self-confirming equilibrium (Theorem 26)

Following Battigalli–Catonini–De Vito §7.2. Under imperfect observation each player `i` only sees a
feedback message `f i (a)` of the action profile `a`. A trajectory is *`f`-consistent with adaptive
learning* when each late action is a best response to a conjecture compatible with the recently
observed messages. **Theorem 26**: if the trajectory's limit distribution is (the product profile of)
an anonymous self-confirming equilibrium, then it is `f`-consistent with adaptive learning.

The justifying conjecture of each played action is supplied by the equilibrium; the confirmed-message
condition forces its support to lie among the profiles feedback-equivalent to a positive-probability
profile, and Lemma 21 places such profiles inside every long observation window.
-/

namespace EcoLean.GameTheory

namespace StaticGame

open scoped BigOperators
open Classical

variable {G : StaticGame} [Fintype G.Player] [DecidableEq G.Player] [∀ i, Fintype (G.Action i)]
  [∀ i, DecidableEq (G.Action i)] {M : G.Player → Type*}

/-- **Theorem 26.** If a trajectory's limit distribution is the independent population distribution of
an anonymous self-confirming equilibrium, then the trajectory is `f`-consistent with adaptive
learning. -/
theorem fConsistentWithAdaptiveLearning_of_limitDistribution_anonymousSCE
    {f : ∀ i, G.ActionProfile → M i} {traj : ℕ → G.ActionProfile} {α : G.MixedProfile}
    {μ : ∀ i, G.Action i → G.ActionProfile → ℝ}
    (hlim : G.LimitDistribution traj (G.mixedProfileDist α))
    (hsce : G.IsAnonymousSelfConfirmingEquilibrium f α μ) :
    G.FConsistentWithAdaptiveLearning f traj := by
  intro tStart
  obtain ⟨T, hT⟩ := limitDistribution_support_eventually_window hlim tStart
  refine ⟨T, fun t ht i => ?_⟩
  obtain ⟨htmem, htwindow⟩ := hT t ht
  -- `traj t i` is played with positive frequency, hence in the support of `αᵢ`.
  have htraj_i : α i (traj t i) ≠ 0 := fun h0 =>
    htmem (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  obtain ⟨hμdist, hμbest, hμconf⟩ := hsce.2 i (traj t i) htraj_i
  refine ⟨μ i (traj t i), hμdist, fun b hb => ?_, hμbest⟩
  set m₀ := f i (G.deviate b i (traj t i)) with hm₀
  -- The conjecture's message distribution puts positive mass on `m₀`.
  have hmpμ : 0 < G.messageProb f i (traj t i) (μ i (traj t i)) m₀ := by
    refine Finset.sum_pos' (fun b'' _ => by split_ifs; exacts [hμdist.1 b'', le_refl 0])
      ⟨b, Finset.mem_univ b, ?_⟩
    rw [if_pos hm₀.symm]; exact hb
  -- By confirmation, so does the true population's message distribution.
  rw [hμconf m₀] at hmpμ
  have hex : ∃ b', 0 <
      (if f i (G.deviate b' i (traj t i)) = m₀ then G.mixedProfileDist α b' else 0) := by
    by_contra hc
    push_neg at hc
    exact absurd hmpμ (not_lt.2 (Finset.sum_nonpos fun b' _ => hc b'))
  obtain ⟨b', hb'pos⟩ := hex
  have hcond : f i (G.deviate b' i (traj t i)) = m₀ ∧ 0 < G.mixedProfileDist α b' := by
    split_ifs at hb'pos with h
    · exact ⟨h, hb'pos⟩
    · exact absurd hb'pos (lt_irrefl 0)
  -- Every coordinate of `b'` has positive `αⱼ`-probability.
  have hb'j : ∀ j, α j (b' j) ≠ 0 := fun j =>
    Finset.prod_ne_zero_iff.mp hcond.2.ne' j (Finset.mem_univ j)
  -- The witness profile: `i` plays `traj t i`, the others as in `b'` — still positive probability.
  have ha_ne : G.mixedProfileDist α (Function.update b' i (traj t i)) ≠ 0 := by
    rw [mixedProfileDist, Finset.prod_ne_zero_iff]
    intro j _
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]; exact htraj_i
    · rw [Function.update_of_ne hj]; exact hb'j j
  -- Lemma 21 places it in the observation window, with the right feedback.
  obtain ⟨τ, hτlo, hτhi, hτeq⟩ := htwindow (Function.update b' i (traj t i)) ha_ne
  exact ⟨τ, hτlo, hτhi, by rw [hτeq]; exact hcond.1.trans hm₀⟩

end StaticGame

end EcoLean.GameTheory
