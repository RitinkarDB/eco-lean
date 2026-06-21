import EcoLean.GameTheory.StaticGames.Equilibrium
import EcoLean.GameTheory.StaticGames.MixedStrategies
import EcoLean.MathematicalMiscellany.Kakutani

/-!
# Nice games and Nash existence (Debreu–Glicksberg–Fan)

A *nice game* (Battigalli–Catonini–De Vito) has, for each player, a nonempty compact convex set of
feasible actions inside a finite-dimensional real vector space, with a payoff that is continuous in
the whole profile and quasiconcave in the player's own action. Every nice game has a Nash equilibrium
*within the feasible sets* (`exists_isNashEquilibriumOn`).

The argument is the standard Kakutani fixed-point one: each player's best-response correspondence
(`niceBestResponse`, the `argmax` of the deviation payoff over the constant feasible set) is nonempty-,
compact- and convex-valued with a closed graph, so the product correspondence
(`niceBestResponseProduct`) satisfies the Kakutani premises on the product of the feasible sets, which
has the Kakutani fixed-point property (it is a nonempty compact convex body in the finite-dimensional
profile space). A fixed point is exactly a Nash equilibrium within the feasible sets.

This generalizes `MixedStrategies.exists_mixedNashEquilibrium`: the mixed extension is the nice game
whose feasible sets are the simplices `Δ(Aᵢ)`. The file depends on the Kakutani development and is kept
out of the `StaticGames` barrel.
-/

namespace EcoLean.GameTheory

namespace StaticGame

open EconLib
open Correspondence

variable {G : StaticGame} [DecidableEq G.Player]

/-- A **Nash equilibrium within the feasible sets `K`**: each player's action is feasible, and no
feasible deviation is profitable. With `K i = Set.univ` this is the ordinary `IsNashEquilibrium`. -/
def IsNashEquilibriumOn (K : ∀ i, Set (G.Action i)) (a : G.ActionProfile) : Prop :=
  (∀ i, a i ∈ K i) ∧ ∀ (i : G.Player), ∀ bi ∈ K i, G.devPayoff a i bi ≤ G.payoff i a

theorem isNashEquilibriumOn_univ_iff (a : G.ActionProfile) :
    G.IsNashEquilibriumOn (fun _ => Set.univ) a ↔ G.IsNashEquilibrium a := by
  constructor
  · intro h i ai; exact h.2 i ai (Set.mem_univ _)
  · exact fun h => ⟨fun _ => Set.mem_univ _, fun i ai _ => h i ai⟩

/-- Player `i`'s best-response correspondence within the feasible sets: the maximisers of the
deviation payoff over the (constant) feasible set `K i`. -/
noncomputable def niceBestResponse (K : ∀ i, Set (G.Action i)) (i : G.Player) :
    Correspondence G.ActionProfile (G.Action i) :=
  Correspondence.argmax (fun a ai => G.devPayoff a i ai) (Correspondence.const (K i))

/-- The product best-response correspondence on the profile space. -/
noncomputable def niceBestResponseProduct (K : ∀ i, Set (G.Action i)) :
    Correspondence G.ActionProfile G.ActionProfile :=
  Correspondence.pi fun i => G.niceBestResponse K i

section Existence

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

variable [Fintype G.Player] [∀ i, NormedAddCommGroup (G.Action i)]
  [∀ i, NormedSpace ℝ (G.Action i)] [FiniteDimensional ℝ G.ActionProfile]

/-- **Nash existence for nice games (Debreu–Glicksberg–Fan).** If every player has a nonempty,
compact, convex feasible set in a finite-dimensional action space, the profile space has dimension at
least `2`, each payoff is continuous and quasiconcave in the own action, then there is a Nash
equilibrium within the feasible sets. -/
theorem exists_isNashEquilibriumOn
    (hdim : 2 ≤ Module.finrank ℝ G.ActionProfile)
    {K : ∀ i, Set (G.Action i)}
    (hKne : ∀ i, (K i).Nonempty) (hKcomp : ∀ i, IsCompact (K i))
    (hKconv : ∀ i, Convex ℝ (K i))
    (hCont : ∀ i, Continuous (G.payoff i))
    (hQuasi : ∀ (i : G.Player) (a : G.ActionProfile),
      QuasiconcaveOn ℝ (K i) (fun ai => G.devPayoff a i ai)) :
    ∃ a : G.ActionProfile, G.IsNashEquilibriumOn K a := by
  -- Build `T2Space` as an explicit term from `R1Space` + the metric `T0Space`; the default
  -- `T2Space` search for a normed `ℝ`-space otherwise explores the order topology and loops.
  haveI hR1 : ∀ i, R1Space (G.Action i) := fun i => inferInstance
  haveI hT2i : ∀ i, T2Space (G.Action i) := fun i =>
    R1Space.t2Space_iff_t0Space.mpr MetricSpace.instT0Space
  haveI : T2Space G.ActionProfile := Pi.t2Space
  set Kprod : Set G.ActionProfile := Set.pi Set.univ K with hKprod
  have hKpne : Kprod.Nonempty := by rw [hKprod, Set.univ_pi_nonempty_iff]; exact hKne
  have hKpcomp : IsCompact Kprod := by rw [hKprod]; exact isCompact_univ_pi hKcomp
  have hKpconv : Convex ℝ Kprod := by rw [hKprod]; exact convex_pi fun i _ => hKconv i
  have hKpclosed : IsClosed Kprod := by
    rw [hKprod]; exact isClosed_set_pi fun i _ => (hKcomp i).isClosed
  -- joint continuity of the deviation objective, and continuity in the own action
  have hdevCont : ∀ i,
      Continuous (fun p : G.ActionProfile × G.Action i => G.devPayoff p.1 i p.2) :=
    fun i => (hCont i).comp (continuous_update i)
  have hsec : ∀ (i : G.Player) (a : G.ActionProfile),
      Continuous (fun ai => G.devPayoff a i ai) :=
    fun i a => (hdevCont i).comp (continuous_const.prodMk continuous_id)
  have hBRne : ∀ i, NonemptyValuedOn (G.niceBestResponse K i) Kprod := fun i =>
    Correspondence.argmax_nonemptyValuedOn_of_compact
      (Correspondence.compactValuedOn_const (hKcomp i))
      (Correspondence.nonemptyValuedOn_const (hKne i))
      (fun a _ => (hsec i a).continuousOn)
  have hPrem : Correspondence.KakutaniPremises Kprod (G.niceBestResponseProduct K) := by
    refine
      { compact_domain := hKpcomp
        convex_domain := hKpconv
        nonempty_domain := hKpne
        mapsTo_domain := Correspondence.pi_mapsToOn fun i =>
          Correspondence.argmax_mapsToOn (fun _ _ => Set.Subset.rfl)
        nonempty_values := Correspondence.pi_nonemptyValuedOn hBRne
        compact_values := Correspondence.pi_compactValuedOn fun i =>
          Correspondence.argmax_compactValuedOn_of_compact
            (Correspondence.compactValuedOn_const (hKcomp i))
            (Correspondence.nonemptyValuedOn_const (hKne i))
            (fun a _ => (hsec i a).continuousOn)
        convex_values := Correspondence.pi_convexValuedOn fun i =>
          Correspondence.argmax_convexValuedOn_of_quasiconcave (hBRne i)
            (fun a _ => hQuasi i a)
        closed_graph := Correspondence.pi_closedGraphOn hKpclosed fun i =>
          Correspondence.argmax_const_closedGraphOn hKpclosed
            ((hKcomp i).isClosed) (hKne i) ((hdevCont i).continuousOn) }
  obtain ⟨a, _, hafix⟩ :=
    (Correspondence.kakutaniFixedPointProperty_of_isCompact_convex_finrank
      hdim hKpne hKpcomp hKpconv).hasFixedPointOn hPrem
  have hmem : ∀ i, a i ∈ G.niceBestResponse K i a := by
    rw [niceBestResponseProduct, Correspondence.mem_pi_iff] at hafix; exact hafix
  refine ⟨a, fun i => ?_, fun i bi hbi => ?_⟩
  · have h := hmem i
    rw [niceBestResponse, Correspondence.mem_argmax_iff] at h
    exact h.1
  · have h := hmem i
    rw [niceBestResponse, Correspondence.mem_argmax_iff] at h
    have hle := h.2 bi hbi
    rwa [G.devPayoff_self] at hle

end Existence

/-! ### The mixed extension is a nice game

The mixed extension of a finite game is the nice game whose action spaces are the real vector spaces
`G.Action i → ℝ` and whose feasible sets are the simplices `Δ(Aᵢ)`. Applying the nice-game theorem
recovers `MixedStrategies.exists_mixedNashEquilibrium`. -/

/-- The **mixed extension** of a finite game `G`, packaged as a `StaticGame` whose action spaces are
the real vector spaces `G.Action i → ℝ` and whose payoff is the mixed (expected) payoff `ūᵢ`. It is
`reducible` so that the finite-dimensional normed instances on `G.Action i → ℝ` transfer through the
`Action` projection. -/
@[reducible] noncomputable def mixedExtension (G : StaticGame) [Fintype G.Player]
    [DecidableEq G.Player] [∀ i, Fintype (G.Action i)] : StaticGame where
  Player := G.Player
  Action := fun i => G.Action i → ℝ
  payoff := fun i => G.mixedPayoff i

variable {G : StaticGame} [Fintype G.Player] [DecidableEq G.Player] [∀ i, Fintype (G.Action i)]

set_option maxHeartbeats 800000 in
/-- **Nash's theorem for finite games, via the nice-game theorem.** Every finite game has a mixed
equilibrium: its mixed extension is a nice game whose feasible sets are the simplices `Δ(Aᵢ)`, so
`exists_isNashEquilibriumOn` applies. This recovers `MixedStrategies.exists_mixedNashEquilibrium`. -/
theorem exists_mixedNashEquilibrium_of_niceGame [∀ i, Nonempty (G.Action i)]
    (hdim : 2 ≤ Module.finrank ℝ G.MixedProfile) :
    ∃ σ, G.IsMixedNashEquilibrium σ := by
  classical
  obtain ⟨σ, hσ⟩ := exists_isNashEquilibriumOn (G := G.mixedExtension)
    (K := fun i => stdSimplex ℝ (G.Action i)) hdim
    (fun i => ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary (G.Action i))⟩)
    (fun i => isCompact_stdSimplex ℝ (G.Action i))
    (fun i => convex_stdSimplex ℝ (G.Action i))
    (fun i => G.continuous_mixedPayoff i)
    (fun i a => G.mixedPayoff_update_quasiconcaveOn i a)
  exact ⟨σ, hσ⟩

end StaticGame

end EcoLean.GameTheory
