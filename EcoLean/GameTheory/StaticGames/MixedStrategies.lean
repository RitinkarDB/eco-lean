import EcoLean.GameTheory.StaticGames.FormalRepresentation
import EcoLean.GameTheory.StaticGames.Equilibrium
import EcoLean.MathematicalMiscellany.Kakutani

/-!
# Mixed strategies and mixed (Nash) equilibrium of a finite game

Following Battigalli–Catonini–De Vito, *Game Theory: Analysis of Strategic Thinking* (§6.1):

* **Definition 20 (mixed extension).** The mixed extension of a finite game
  `G = ⟨I, (Aᵢ, uᵢ)⟩` has, for each player, the mixed-action set `Δ(Aᵢ) = stdSimplex ℝ Aᵢ`, and the
  expected payoff `ūᵢ(α) = ∑_{a ∈ A} uᵢ(a) ∏_{j} αⱼ(aⱼ)` (independent randomization).
* **Definition 21 (mixed equilibrium).** A mixed profile `α` is a mixed equilibrium of `G` iff it is
  a Nash equilibrium of the mixed extension.
* **Theorem 13.** Every finite game has a mixed equilibrium — because each `Δ(Aᵢ)` is nonempty,
  convex and compact, and `ūᵢ` is multilinear (hence continuous and linear, so quasiconcave, in `αᵢ`),
  so the "nice game" Nash-existence argument (Kakutani on the product of simplices) applies.

This file defines `mixedPayoff` (`ūᵢ`) and `IsMixedNashEquilibrium`, proves the foundational analytic
facts (continuity; linearity in the own coordinate), and assembles the existence theorem
`exists_mixedNashEquilibrium` from `Kakutani.kakutaniFixedPointProperty_pi_stdSimplex` (the product
strategy space has the Kakutani fixed-point property) together with the best-response correspondence
on the product of simplices.
-/

namespace EcoLean
namespace GameTheory
namespace StaticGame

open EconLib
open scoped BigOperators

variable (G : StaticGame) [Fintype G.Player] [DecidableEq G.Player]
  [∀ i, Fintype (G.Action i)]

/-- A **mixed strategy profile**: a real weight `α i a` on each pure action, for each player.
Intended to satisfy `α i ∈ stdSimplex ℝ (G.Action i)` (a probability distribution). -/
abbrev MixedProfile : Type _ := ∀ i, G.Action i → ℝ

/-- The **mixed (expected) payoff** to player `i` — the payoff of player `i` in the mixed extension
of `G` (Battigalli–Catonini–De Vito, Definition 20):
`ūᵢ(α) = ∑_{a} (∏_j αⱼ(aⱼ)) · uᵢ(a)`, the expectation of `uᵢ` under independent randomization. -/
noncomputable def mixedPayoff (i : G.Player) (α : G.MixedProfile) : ℝ :=
  ∑ a : G.ActionProfile, (∏ j, α j (a j)) * G.payoff i a

/-- The mixed expected payoff is **continuous** in the mixed profile: it is a polynomial in the
weights (a finite sum of finite products of coordinate evaluations). -/
theorem continuous_mixedPayoff (i : G.Player) :
    Continuous (fun α : G.MixedProfile => G.mixedPayoff i α) := by
  unfold mixedPayoff
  refine continuous_finset_sum _ (fun a _ => ?_)
  refine Continuous.mul ?_ continuous_const
  refine continuous_finset_prod _ (fun j _ => ?_)
  exact (continuous_apply (a j)).comp (continuous_apply j)

/-- A **mixed (Nash) equilibrium** (Battigalli–Catonini–De Vito, Definition 21): every coordinate is
a probability distribution, and no player can strictly improve their mixed expected payoff by
deviating to another mixed strategy.  Equivalently, a Nash equilibrium of the mixed extension. -/
def IsMixedNashEquilibrium (α : G.MixedProfile) : Prop :=
  (∀ i, α i ∈ stdSimplex ℝ (G.Action i)) ∧
    ∀ i, ∀ βᵢ ∈ stdSimplex ℝ (G.Action i),
      G.mixedPayoff i (Function.update α i βᵢ) ≤ G.mixedPayoff i α

/-! ### Multilinearity of the mixed payoff

The mixed payoff is **multilinear**: fixing everyone but player `i`, it is linear in `i`'s own mixed
strategy.  This gives the two facts the Kakutani/Berge argument needs — the deviation objective is
quasiconcave (indeed affine) in the own strategy, and is jointly continuous. -/

/-- **Own-strategy factorisation.**  Deviating player `i` to `τ` factors the product over players,
exposing the linear dependence on `τ`. -/
lemma mixedPayoff_update (i : G.Player) (σ : G.MixedProfile) (τ : G.Action i → ℝ) :
    G.mixedPayoff i (Function.update σ i τ)
      = ∑ a : G.ActionProfile, (τ (a i) * ∏ j ∈ Finset.univ \ {i}, σ j (a j)) * G.payoff i a := by
  unfold mixedPayoff
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have hfun : (fun j => (Function.update σ i τ) j (a j))
      = Function.update (fun j => σ j (a j)) i (τ (a i)) := by
    funext j
    simp only [Function.update_apply]
    rcases eq_or_ne j i with h | h
    · subst h; simp
    · simp [h]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ i)]

/-- The deviation objective `τ ↦ ūᵢ(σ with i := τ)` is **affine (linear) in `τ`**. -/
lemma mixedPayoff_update_affine (i : G.Player) (σ : G.MixedProfile) (τ₁ τ₂ : G.Action i → ℝ)
    (a b : ℝ) :
    G.mixedPayoff i (Function.update σ i (a • τ₁ + b • τ₂))
      = a * G.mixedPayoff i (Function.update σ i τ₁)
        + b * G.mixedPayoff i (Function.update σ i τ₂) := by
  rw [mixedPayoff_update, mixedPayoff_update, mixedPayoff_update, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a' _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- The deviation objective is concave (being affine) on the simplex. -/
lemma mixedPayoff_update_concaveOn (i : G.Player) (σ : G.MixedProfile) :
    ConcaveOn ℝ (stdSimplex ℝ (G.Action i)) (fun τ => G.mixedPayoff i (Function.update σ i τ)) := by
  refine ⟨convex_stdSimplex ℝ _, fun τ₁ _ τ₂ _ a b _ _ _ => ?_⟩
  simp only [smul_eq_mul]
  exact le_of_eq (mixedPayoff_update_affine G i σ τ₁ τ₂ a b).symm

/-- The deviation objective is quasiconcave on the simplex. -/
lemma mixedPayoff_update_quasiconcaveOn (i : G.Player) (σ : G.MixedProfile) :
    QuasiconcaveOn ℝ (stdSimplex ℝ (G.Action i))
      (fun τ => G.mixedPayoff i (Function.update σ i τ)) :=
  (mixedPayoff_update_concaveOn G i σ).quasiconcaveOn

/-- The deviation objective is **jointly continuous** in `(σ, τ)`. -/
lemma continuous_mixedPayoff_update (i : G.Player) :
    Continuous (fun p : G.MixedProfile × (G.Action i → ℝ) =>
      G.mixedPayoff i (Function.update p.1 i p.2)) :=
  (G.continuous_mixedPayoff i).comp (continuous_update i)

/-! ### Mixed best-response correspondence and existence -/

/-- Player `i`'s **mixed best-response correspondence**: the maximisers of the deviation objective
over the simplex of mixed strategies (a constant feasible set). -/
noncomputable def mixedBestResponse (i : G.Player) :
    Correspondence G.MixedProfile (G.Action i → ℝ) :=
  Correspondence.argmax (fun σ τ => G.mixedPayoff i (Function.update σ i τ))
    (Correspondence.const (stdSimplex ℝ (G.Action i)))

/-- The product best-response correspondence on the mixed-strategy profile space. -/
noncomputable def mixedBestResponseProduct : Correspondence G.MixedProfile G.MixedProfile :=
  Correspondence.pi fun i => G.mixedBestResponse i

open scoped Classical in
/-- **Nash's theorem for finite games (Battigalli–Catonini–De Vito, Theorem 13).**  Every finite game
whose mixed-strategy profile space has dimension `≥ 2` has a mixed (Nash) equilibrium.  The mixed
extension is a "nice game": the strategy sets `Δ(Aᵢ)` form a compact convex body `K = ∏ᵢ Δ(Aᵢ)`
(which has the Kakutani fixed-point property by the general body theorem), and the deviation
objective is continuous and quasiconcave, so the product best-response correspondence satisfies the
Kakutani premises; a fixed point of it is exactly a mixed equilibrium. -/
theorem exists_mixedNashEquilibrium [∀ i, Nonempty (G.Action i)]
    (hdim : 2 ≤ Module.finrank ℝ G.MixedProfile) :
    ∃ σ, G.IsMixedNashEquilibrium σ := by
  haveI : ∀ i, T2Space (G.Action i → ℝ) := fun i =>
    @Pi.t2Space (G.Action i) (fun _ => ℝ) inferInstance fun _ => OrderClosedTopology.to_t2Space
  haveI : T2Space G.MixedProfile :=
    @Pi.t2Space G.Player (fun i => G.Action i → ℝ) inferInstance fun _ => inferInstance
  set K : Set G.MixedProfile := Set.pi Set.univ (fun i => stdSimplex ℝ (G.Action i)) with hKdef
  have hΔne : ∀ i, (stdSimplex ℝ (G.Action i)).Nonempty := fun i =>
    ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary (G.Action i))⟩
  have hKne : K.Nonempty := by
    rw [hKdef, Set.univ_pi_nonempty_iff]; exact hΔne
  have hKcomp : IsCompact K := by
    rw [hKdef]; exact isCompact_univ_pi fun i => isCompact_stdSimplex ℝ (G.Action i)
  have hKconv : Convex ℝ K := by
    rw [hKdef]; exact convex_pi fun i _ => convex_stdSimplex ℝ (G.Action i)
  have hKclosed : IsClosed K := by
    rw [hKdef]; exact isClosed_set_pi fun i _ => isClosed_stdSimplex ℝ (G.Action i)
  -- continuity of player `i`'s deviation objective as a function of its own strategy
  have hsecτ : ∀ (i : G.Player) (σ : G.MixedProfile),
      Continuous (fun τ => G.mixedPayoff i (Function.update σ i τ)) := fun i σ =>
    (G.continuous_mixedPayoff_update i).comp (continuous_const.prodMk continuous_id)
  -- per-player nonemptiness of the best response (reused twice)
  have hBRne : ∀ i, Correspondence.NonemptyValuedOn (G.mixedBestResponse i) K := fun i =>
    Correspondence.argmax_nonemptyValuedOn_of_compact
      (Correspondence.compactValuedOn_const (isCompact_stdSimplex ℝ (G.Action i)))
      (Correspondence.nonemptyValuedOn_const (hΔne i))
      (fun σ _ => (hsecτ i σ).continuousOn)
  -- the product best-response satisfies the Kakutani premises on `K`
  have hPrem : Correspondence.KakutaniPremises K G.mixedBestResponseProduct := by
    refine
      { compact_domain := hKcomp
        convex_domain := hKconv
        nonempty_domain := hKne
        mapsTo_domain := Correspondence.pi_mapsToOn fun i =>
          Correspondence.argmax_mapsToOn (fun _ _ => Set.Subset.rfl)
        nonempty_values := Correspondence.pi_nonemptyValuedOn hBRne
        compact_values := Correspondence.pi_compactValuedOn fun i =>
          Correspondence.argmax_compactValuedOn_of_compact
            (Correspondence.compactValuedOn_const (isCompact_stdSimplex ℝ (G.Action i)))
            (Correspondence.nonemptyValuedOn_const (hΔne i))
            (fun σ _ => (hsecτ i σ).continuousOn)
        convex_values := Correspondence.pi_convexValuedOn fun i =>
          Correspondence.argmax_convexValuedOn_of_quasiconcave (hBRne i)
            (fun σ _ => G.mixedPayoff_update_quasiconcaveOn i σ)
        closed_graph := Correspondence.pi_closedGraphOn hKclosed fun i =>
          Correspondence.argmax_const_closedGraphOn hKclosed
            (isClosed_stdSimplex ℝ (G.Action i)) (hΔne i)
            (G.continuous_mixedPayoff_update i).continuousOn }
  -- a fixed point of the product best-response exists, and is a mixed equilibrium
  obtain ⟨σ, _, hσfix⟩ :=
    (Correspondence.kakutaniFixedPointProperty_of_isCompact_convex_finrank
      hdim hKne hKcomp hKconv).hasFixedPointOn hPrem
  have hmem : ∀ i, σ i ∈ G.mixedBestResponse i σ := by
    rw [mixedBestResponseProduct, Correspondence.mem_pi_iff] at hσfix; exact hσfix
  refine ⟨σ, fun i => ?_, fun i βᵢ hβ => ?_⟩
  · have h := hmem i
    rw [mixedBestResponse, Correspondence.mem_argmax_iff] at h
    exact h.1
  · have h := hmem i
    rw [mixedBestResponse, Correspondence.mem_argmax_iff] at h
    have hle := h.2 βᵢ hβ
    rwa [Function.update_eq_self] at hle

end StaticGame
end GameTheory
end EcoLean
