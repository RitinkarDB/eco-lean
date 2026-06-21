import EcoLean.GameTheory.StaticGames.Equilibrium
import EcoLean.MathematicalMiscellany.SetsFunctionsCorrespondences

/-!
# Best-response correspondences and fixed-point existence for static games

This file connects the existing pure-strategy `StaticGame` API to the
correspondence/fixed-point infrastructure in `MathLanguage`.

The main construction is the product best-response correspondence. A fixed
point of this correspondence is exactly a Nash equilibrium, so any future
Kakutani theorem can be plugged in through `KakutaniFixedPointProperty`.
-/

namespace EcoLean.GameTheory

namespace StaticGame

open EconLib
open Correspondence

universe u v

variable (G : StaticGame)

section BestResponseCorrespondence

variable [DecidableEq G.Player]

/-- Player `i`'s payoff from deviating to `ai` at profile `a`. -/
def deviationObjective (i : G.Player) (a : G.ActionProfile) (ai : G.Action i) : ℝ :=
  G.devPayoff a i ai

@[simp] theorem deviationObjective_apply
    (i : G.Player) (a : G.ActionProfile) (ai : G.Action i) :
    G.deviationObjective i a ai = G.devPayoff a i ai := rfl

/--
The feasible actions for player `i`, as a constant correspondence over action
profiles. For the current `StaticGame` API, feasibility is encoded by the
dependent action type itself.
-/
def feasibleActionCorrespondence (i : G.Player) :
    Correspondence G.ActionProfile (G.Action i) :=
  Correspondence.const Set.univ

omit [DecidableEq G.Player] in
@[simp] theorem mem_feasibleActionCorrespondence
    (i : G.Player) (a : G.ActionProfile) (ai : G.Action i) :
    ai ∈ G.feasibleActionCorrespondence i a :=
  trivial

/--
Player `i`'s best-response correspondence at a profile `a`.

This is intentionally defined as an `argmax` so the Berge maximum-theorem API
can be applied directly when continuity/compactness/quasiconcavity hypotheses
are available.
-/
def bestResponseCorrespondence (i : G.Player) :
    Correspondence G.ActionProfile (G.Action i) :=
  Correspondence.argmax (G.deviationObjective i) (G.feasibleActionCorrespondence i)

@[simp] theorem mem_bestResponseCorrespondence_iff
    {i : G.Player} {a : G.ActionProfile} {ai : G.Action i} :
    ai ∈ G.bestResponseCorrespondence i a ↔
      ∀ ai' : G.Action i, G.devPayoff a i ai' ≤ G.devPayoff a i ai := by
  simp [bestResponseCorrespondence, feasibleActionCorrespondence, deviationObjective]

/--
The product best-response correspondence: a profile `b` is selected at `a`
when each component `b i` is a best response for player `i` at `a`.
-/
def bestResponseProduct : Correspondence G.ActionProfile G.ActionProfile :=
  Correspondence.pi fun i : G.Player => G.bestResponseCorrespondence i

@[simp] theorem mem_bestResponseProduct_iff
    {a b : G.ActionProfile} :
    b ∈ G.bestResponseProduct a ↔
      ∀ i : G.Player, b i ∈ G.bestResponseCorrespondence i a := by
  change b ∈ Correspondence.pi (fun i : G.Player => G.bestResponseCorrespondence i) a ↔
    ∀ i : G.Player, b i ∈ G.bestResponseCorrespondence i a
  exact Correspondence.mem_pi_iff

theorem bestResponseProduct_component
    {a b : G.ActionProfile} (hb : b ∈ G.bestResponseProduct a)
    (i : G.Player) :
    b i ∈ G.bestResponseCorrespondence i a :=
  (G.mem_bestResponseProduct_iff.mp hb) i

/--
A profile is a fixed point of the product best-response correspondence iff it
is a Nash equilibrium.
-/
theorem fixedPoint_bestResponseProduct_iff
    {a : G.ActionProfile} :
    a ∈ Correspondence.fixedPoints G.bestResponseProduct ↔ G.IsNashEquilibrium a := by
  constructor
  · intro ha i ai
    have hBest : a i ∈ G.bestResponseCorrespondence i a :=
      (G.mem_bestResponseProduct_iff.mp ha) i
    have hDev : G.devPayoff a i ai ≤ G.devPayoff a i (a i) :=
      (G.mem_bestResponseCorrespondence_iff.mp hBest) ai
    simpa [G.devPayoff_self a i] using hDev
  · intro hNash
    rw [Correspondence.mem_fixedPoints_iff, G.mem_bestResponseProduct_iff]
    intro i
    rw [G.mem_bestResponseCorrespondence_iff]
    intro ai
    simpa [G.devPayoff_self a i] using hNash i ai

/-- Carrier-relative version of `fixedPoint_bestResponseProduct_iff`. -/
theorem fixedPointOn_bestResponseProduct_iff
    {K : Set G.ActionProfile} {a : G.ActionProfile} :
    Correspondence.FixedPointOn G.bestResponseProduct K a ↔
      a ∈ K ∧ G.IsNashEquilibrium a := by
  constructor
  · intro ha
    exact ⟨ha.1, (G.fixedPoint_bestResponseProduct_iff.mp ha.2)⟩
  · intro ha
    exact ⟨ha.1, (G.fixedPoint_bestResponseProduct_iff.mpr ha.2)⟩

/-- A fixed point of the product best-response correspondence gives a Nash equilibrium. -/
theorem exists_nashEquilibrium_of_hasFixedPointOn_bestResponseProduct
    {K : Set G.ActionProfile}
    (hK : Correspondence.HasFixedPointOn G.bestResponseProduct K) :
    ∃ a ∈ K, G.IsNashEquilibrium a := by
  rcases hK with ⟨a, ha⟩
  exact ⟨a, ha.1, (G.fixedPoint_bestResponseProduct_iff.mp ha.2)⟩

/--
Componentwise best-response hypotheses assemble into the Kakutani hypotheses
for the product best-response correspondence on the unconstrained profile
space.

This is the reusable product step for Nash existence: Berge-style arguments
can prove the component hypotheses, and this theorem packages them into the
single correspondence consumed by `KakutaniFixedPointProperty`.
-/
theorem kakutaniPremises_bestResponseProduct_univ
    [∀ i : G.Player, TopologicalSpace (G.Action i)]
    [∀ i : G.Player, AddCommMonoid (G.Action i)]
    [∀ i : G.Player, Module ℝ (G.Action i)]
    (hCompactDomain : IsCompact (Set.univ : Set G.ActionProfile))
    (hNonemptyDomain : (Set.univ : Set G.ActionProfile).Nonempty)
    (hBRNonempty :
      ∀ i : G.Player,
        Correspondence.NonemptyValuedOn
          (G.bestResponseCorrespondence i) (Set.univ : Set G.ActionProfile))
    (hBRCompact :
      ∀ i : G.Player,
        Correspondence.CompactValuedOn
          (G.bestResponseCorrespondence i) (Set.univ : Set G.ActionProfile))
    (hBRConvex :
      ∀ i : G.Player,
        Correspondence.ConvexValuedOn (𝕜 := ℝ)
          (G.bestResponseCorrespondence i) (Set.univ : Set G.ActionProfile))
    (hBRClosedGraph :
      ∀ i : G.Player,
        Correspondence.ClosedGraphOn
          (G.bestResponseCorrespondence i) (Set.univ : Set G.ActionProfile)) :
    Correspondence.KakutaniPremises
      (Set.univ : Set G.ActionProfile) G.bestResponseProduct := by
  exact
    { compact_domain := hCompactDomain
      convex_domain := convex_univ
      nonempty_domain := hNonemptyDomain
      mapsTo_domain := by
        intro a _ha b _hb
        exact trivial
      nonempty_values := by
        simpa [bestResponseProduct] using
          Correspondence.pi_nonemptyValuedOn
            (F := fun i : G.Player => G.bestResponseCorrespondence i)
            hBRNonempty
      compact_values := by
        simpa [bestResponseProduct] using
          Correspondence.pi_compactValuedOn
            (F := fun i : G.Player => G.bestResponseCorrespondence i)
            hBRCompact
      convex_values := by
        simpa [bestResponseProduct] using
          Correspondence.pi_convexValuedOn
            (F := fun i : G.Player => G.bestResponseCorrespondence i)
            hBRConvex
      closed_graph := by
        simpa [bestResponseProduct] using
          Correspondence.pi_closedGraphOn
            (F := fun i : G.Player => G.bestResponseCorrespondence i)
            isClosed_univ hBRClosedGraph }

/--
Berge-style payoff hypotheses imply the Kakutani hypotheses for the product
best-response correspondence on the unconstrained profile space.

Each player's action space is assumed compact and nonempty; each payoff is
continuous in `(profile, own action)` and quasiconcave in own action. The
result is intentionally still phrased as `KakutaniPremises`, so an actual
Kakutani theorem can be supplied later without changing this game-theory API.
-/
theorem kakutaniPremises_bestResponseProduct_univ_of_payoff
    [∀ i : G.Player, TopologicalSpace (G.Action i)]
    [∀ i : G.Player, T2Space (G.Action i)]
    [∀ i : G.Player, AddCommMonoid (G.Action i)]
    [∀ i : G.Player, Module ℝ (G.Action i)]
    (hActionCompact :
      ∀ i : G.Player, IsCompact (Set.univ : Set (G.Action i)))
    (hActionNonempty :
      ∀ i : G.Player, (Set.univ : Set (G.Action i)).Nonempty)
    (hPayoffContinuous :
      ∀ i : G.Player,
        Continuous fun p : G.ActionProfile × G.Action i =>
          G.deviationObjective i p.1 p.2)
    (hPayoffQuasi :
      ∀ (i : G.Player) (a : G.ActionProfile),
        QuasiconcaveOn ℝ (Set.univ : Set (G.Action i))
          (G.deviationObjective i a)) :
    Correspondence.KakutaniPremises
      (Set.univ : Set G.ActionProfile) G.bestResponseProduct := by
  classical
  have hProfileCompact : IsCompact (Set.univ : Set G.ActionProfile) := by
    simpa using isCompact_univ_pi fun i : G.Player => hActionCompact i
  have hProfileNonempty : (Set.univ : Set G.ActionProfile).Nonempty := by
    choose a ha using hActionNonempty
    exact ⟨a, trivial⟩
  have hSectionContinuous :
      ∀ i : G.Player, ∀ ⦃a : G.ActionProfile⦄, a ∈ Set.univ →
        ContinuousOn (G.deviationObjective i a) (Set.univ : Set (G.Action i)) := by
    intro i a _ha
    have h :
        Continuous fun ai : G.Action i => G.deviationObjective i a ai :=
      (hPayoffContinuous i).comp (continuous_const.prodMk continuous_id)
    exact h.continuousOn
  have hBRNonempty :
      ∀ i : G.Player,
        Correspondence.NonemptyValuedOn
          (G.bestResponseCorrespondence i) (Set.univ : Set G.ActionProfile) := by
    intro i
    simpa [bestResponseCorrespondence, feasibleActionCorrespondence] using
      Correspondence.argmax_nonemptyValuedOn_of_compact
        (u := G.deviationObjective i)
        (F := G.feasibleActionCorrespondence i)
        (A := (Set.univ : Set G.ActionProfile))
        (Correspondence.compactValuedOn_const
          (X := G.ActionProfile) (S := (Set.univ : Set (G.Action i)))
          (hActionCompact i))
        (Correspondence.nonemptyValuedOn_const
          (X := G.ActionProfile) (S := (Set.univ : Set (G.Action i)))
          (hActionNonempty i))
        (hSectionContinuous i)
  have hBRCompact :
      ∀ i : G.Player,
        Correspondence.CompactValuedOn
          (G.bestResponseCorrespondence i) (Set.univ : Set G.ActionProfile) := by
    intro i
    simpa [bestResponseCorrespondence, feasibleActionCorrespondence] using
      Correspondence.argmax_compactValuedOn_of_compact
        (u := G.deviationObjective i)
        (F := G.feasibleActionCorrespondence i)
        (A := (Set.univ : Set G.ActionProfile))
        (Correspondence.compactValuedOn_const
          (X := G.ActionProfile) (S := (Set.univ : Set (G.Action i)))
          (hActionCompact i))
        (Correspondence.nonemptyValuedOn_const
          (X := G.ActionProfile) (S := (Set.univ : Set (G.Action i)))
          (hActionNonempty i))
        (hSectionContinuous i)
  have hBRConvex :
      ∀ i : G.Player,
        Correspondence.ConvexValuedOn (𝕜 := ℝ)
          (G.bestResponseCorrespondence i) (Set.univ : Set G.ActionProfile) := by
    intro i
    simpa [bestResponseCorrespondence, feasibleActionCorrespondence] using
      Correspondence.argmax_convexValuedOn_of_quasiconcave
        (u := G.deviationObjective i)
        (F := G.feasibleActionCorrespondence i)
        (A := (Set.univ : Set G.ActionProfile))
        (hBRNonempty i)
        (by
          intro a _ha
          simpa [feasibleActionCorrespondence] using hPayoffQuasi i a)
  have hBRClosedGraph :
      ∀ i : G.Player,
        Correspondence.ClosedGraphOn
          (G.bestResponseCorrespondence i) (Set.univ : Set G.ActionProfile) := by
    intro i
    simpa [bestResponseCorrespondence, feasibleActionCorrespondence] using
      Correspondence.argmax_const_closedGraphOn
        (X := G.ActionProfile) (Y := G.Action i)
        (u := G.deviationObjective i)
        (A := (Set.univ : Set G.ActionProfile))
        (K := (Set.univ : Set (G.Action i)))
        isClosed_univ isClosed_univ (hActionNonempty i)
        (hPayoffContinuous i).continuousOn
  exact G.kakutaniPremises_bestResponseProduct_univ
    hProfileCompact hProfileNonempty hBRNonempty hBRCompact hBRConvex hBRClosedGraph

/--
If the strategy-profile carrier has the Kakutani fixed-point property and the
product best-response correspondence satisfies the Kakutani hypotheses, then
the game has a Nash equilibrium in that carrier.
-/
theorem exists_nashEquilibrium_of_kakutaniPremises
    [TopologicalSpace G.ActionProfile] [AddCommMonoid G.ActionProfile]
    [Module ℝ G.ActionProfile]
    {K : Set G.ActionProfile}
    (hKfixed : Correspondence.KakutaniFixedPointProperty K)
    (hBR : Correspondence.KakutaniPremises K G.bestResponseProduct) :
    ∃ a ∈ K, G.IsNashEquilibrium a := by
  exact G.exists_nashEquilibrium_of_hasFixedPointOn_bestResponseProduct
    (hKfixed.hasFixedPointOn hBR)

/--
The unconstrained version, useful when the strategy type already encodes the
feasible strategy space.
-/
theorem exists_nashEquilibrium_of_kakutaniPremises_univ
    [TopologicalSpace G.ActionProfile] [AddCommMonoid G.ActionProfile]
    [Module ℝ G.ActionProfile]
    (hKfixed : Correspondence.KakutaniFixedPointProperty
      (Set.univ : Set G.ActionProfile))
    (hBR : Correspondence.KakutaniPremises
      (Set.univ : Set G.ActionProfile) G.bestResponseProduct) :
    ∃ a : G.ActionProfile, G.IsNashEquilibrium a := by
  rcases G.exists_nashEquilibrium_of_kakutaniPremises hKfixed hBR with
    ⟨a, _ha, hNash⟩
  exact ⟨a, hNash⟩

end BestResponseCorrespondence

end StaticGame

end EcoLean.GameTheory
