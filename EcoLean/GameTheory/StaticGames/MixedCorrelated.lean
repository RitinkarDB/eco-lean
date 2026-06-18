import EcoLean.GameTheory.StaticGames.MixedStrategies
import EcoLean.GameTheory.StaticGames.CorrelatedEquilibrium

/-!
# Mixed Nash equilibria induce correlated equilibria

The independent (product) distribution of a mixed Nash equilibrium is a correlated equilibrium —
the inclusion *mixed Nash ⊆ correlated equilibria* for finite games (Aumann).

Given a mixed profile `α`, the **product distribution** `productDist α a = ∏ⱼ αⱼ(aⱼ)` is the
distribution over action profiles under which players randomize independently. Its expected payoff is
the mixed payoff (`expectedPayoff_productDist`), and a departure `δ : Action i → Action i` from the
recommendation pushes `αᵢ` forward to `pushforward i (αᵢ) δ` — a mixed strategy whose mixed payoff
equals the corresponding expected deviation payoff (`expectedDeviationPayoff_productDist`). The Nash
optimality of `αᵢ` against any mixed deviation therefore rules out every profitable departure, giving
the correlated-equilibrium incentive constraints.

Main results: `isCorrelatedEquilibrium_productDist_of_mixedNash`, and the corollary
`exists_correlatedEquilibrium` — every finite game has a correlated equilibrium (combining this with
Nash's theorem `exists_mixedNashEquilibrium`).

This file depends on `MixedStrategies` (hence the Kakutani development) and is kept out of the
`StaticGames` barrel.
-/

namespace EcoLean.GameTheory

namespace StaticGame

open scoped BigOperators Classical

variable (G : StaticGame) [Fintype G.Player] [DecidableEq G.Player] [∀ i, Fintype (G.Action i)]

/-! ### The product distribution and the departure pushforward -/

/-- The **product (independent) distribution** induced by a mixed profile `α`: players randomize
independently, so a profile `a` has probability `∏ⱼ αⱼ(aⱼ)`. -/
noncomputable def productDist (α : G.MixedProfile) : G.ActionProfile → ℝ :=
  fun a => ∏ j, α j (a j)

/-- The **pushforward** of player `i`'s mixed strategy `τ` under a departure function `δ`: the
probability of playing `x` is the total weight `τ` places on recommendations that `δ` maps to `x`. -/
noncomputable def pushforward (i : G.Player) (τ : G.Action i → ℝ) (δ : G.Action i → G.Action i) :
    G.Action i → ℝ :=
  fun x => ∑ y ∈ Finset.univ.filter (fun y => δ y = x), τ y

variable {G}

theorem productDist_nonneg {α : G.MixedProfile} (hα : ∀ i, α i ∈ stdSimplex ℝ (G.Action i))
    (a : G.ActionProfile) : 0 ≤ G.productDist α a :=
  Finset.prod_nonneg fun j _ => (hα j).1 (a j)

theorem productDist_sum_one {α : G.MixedProfile} (hα : ∀ i, α i ∈ stdSimplex ℝ (G.Action i)) :
    ∑ a : G.ActionProfile, G.productDist α a = 1 := by
  simp only [productDist]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  exact Finset.prod_eq_one fun j _ => (hα j).2

/-- The pushforward of a mixed strategy is again a mixed strategy (a probability distribution). -/
theorem pushforward_mem_stdSimplex {i : G.Player} {τ : G.Action i → ℝ}
    (hτ : τ ∈ stdSimplex ℝ (G.Action i)) (δ : G.Action i → G.Action i) :
    G.pushforward i τ δ ∈ stdSimplex ℝ (G.Action i) := by
  refine ⟨fun x => ?_, ?_⟩
  · exact Finset.sum_nonneg fun y _ => hτ.1 y
  · simp only [pushforward]
    rw [Finset.sum_fiberwise_of_maps_to (fun y (_ : y ∈ Finset.univ) => Finset.mem_univ (δ y))]
    exact hτ.2

/-! ### The two payoff identities -/

/-- The expected payoff under the product distribution is exactly the mixed payoff. -/
theorem expectedPayoff_productDist (α : G.MixedProfile) (i : G.Player) :
    G.expectedPayoff (G.productDist α) i = G.mixedPayoff i α := rfl

/-- The expected payoff of a departure `δ` under the product distribution equals the mixed payoff
obtained by replacing `αᵢ` with its pushforward `pushforward i (αᵢ) δ`. The recommendation drawn from
`αᵢ` and then relabelled by `δ` has the same law as a draw from the pushforward. -/
theorem expectedDeviationPayoff_productDist (α : G.MixedProfile) (i : G.Player)
    (δ : G.Action i → G.Action i) :
    G.expectedDeviationPayoff (G.productDist α) i δ
      = G.mixedPayoff i (Function.update α i (G.pushforward i (α i) δ)) := by
  rw [mixedPayoff_update]
  simp only [expectedDeviationPayoff, productDist, StaticGame.devPayoff]
  -- Group the profiles by the relabelled profile `deviate a i (δ (a i))`.
  have key : ∑ a : G.ActionProfile, (∏ j, α j (a j)) * G.payoff i (G.deviate a i (δ (a i)))
      = ∑ b : G.ActionProfile,
          ∑ a ∈ Finset.univ.filter (fun a => G.deviate a i (δ (a i)) = b),
            (∏ j, α j (a j)) * G.payoff i (G.deviate a i (δ (a i))) :=
    (Finset.sum_fiberwise_of_maps_to
      (fun a (_ : a ∈ Finset.univ) => Finset.mem_univ (G.deviate a i (δ (a i)))) _).symm
  rw [key]
  refine Finset.sum_congr rfl fun b _ => ?_
  -- On the fibre over `b`, the payoff factor is constant.
  have hstep : ∑ a ∈ Finset.univ.filter (fun a => G.deviate a i (δ (a i)) = b),
        (∏ j, α j (a j)) * G.payoff i (G.deviate a i (δ (a i)))
      = ∑ a ∈ Finset.univ.filter (fun a => G.deviate a i (δ (a i)) = b),
          (∏ j, α j (a j)) * G.payoff i b :=
    Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.mp ha).2]
  rw [hstep, ← Finset.sum_mul]
  congr 1
  -- The fibre sum of the weights is `pushforward (b i)` times the opponents' product.
  simp only [pushforward, Finset.sum_mul]
  refine Finset.sum_nbij' (fun a => a i) (fun y => G.deviate b i y) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [← (Finset.mem_filter.mp ha).2, G.deviate_self]⟩
  · intro y hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    show G.deviate (G.deviate b i y) i (δ ((G.deviate b i y) i)) = b
    rw [G.deviate_self, deviate_deviate, (Finset.mem_filter.mp hy).2, G.deviate_eq_self]
  · intro a ha
    show G.deviate b i (a i) = a
    rw [← (Finset.mem_filter.mp ha).2, deviate_deviate, G.deviate_eq_self]
  · intro y _
    exact G.deviate_self b i y
  · intro a ha
    have ha2 : G.deviate a i (δ (a i)) = b := (Finset.mem_filter.mp ha).2
    show ∏ j, α j (a j) = α i (a i) * ∏ j ∈ Finset.univ \ {i}, α j (b j)
    have hb : (∏ j ∈ Finset.univ \ {i}, α j (b j)) = ∏ j ∈ Finset.univ \ {i}, α j (a j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hji : j ≠ i := fun heq => (Finset.mem_sdiff.mp hj).2 (Finset.mem_singleton.mpr heq)
      rw [← ha2, G.deviate_ne a (δ (a i)) hji]
    rw [hb]
    exact Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ i) (fun j => α j (a j))

/-! ### Mixed Nash ⇒ correlated equilibrium -/

/-- The product distribution of a mixed Nash equilibrium is a correlated equilibrium: no departure
function is profitable, since each player's mixed strategy is already optimal against the others. -/
theorem isCorrelatedEquilibrium_productDist_of_mixedNash {α : G.MixedProfile}
    (hα : G.IsMixedNashEquilibrium α) : G.IsCorrelatedEquilibrium (G.productDist α) := by
  obtain ⟨hsimplex, hbest⟩ := hα
  refine ⟨⟨productDist_nonneg hsimplex, productDist_sum_one hsimplex⟩, fun i δ => ?_⟩
  rw [expectedDeviationPayoff_productDist, expectedPayoff_productDist]
  exact hbest i _ (pushforward_mem_stdSimplex (hsimplex i) δ)

/-- Every finite game has a correlated equilibrium: take the product distribution of a mixed Nash
equilibrium, which exists by Nash's theorem. -/
theorem exists_correlatedEquilibrium [∀ i, Nonempty (G.Action i)]
    (hdim : 2 ≤ Module.finrank ℝ G.MixedProfile) :
    ∃ μ : G.ActionProfile → ℝ, G.IsCorrelatedEquilibrium μ := by
  obtain ⟨α, hα⟩ := G.exists_mixedNashEquilibrium hdim
  exact ⟨G.productDist α, isCorrelatedEquilibrium_productDist_of_mixedNash hα⟩

end StaticGame

end EcoLean.GameTheory
