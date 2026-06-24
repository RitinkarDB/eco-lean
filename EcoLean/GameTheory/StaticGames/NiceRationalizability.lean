import EcoLean.GameTheory.StaticGames.NiceBestResponse
import Mathlib.Analysis.Convex.Topology

/-!
# Point rationalizability in nice games (Theorem 30)

Following Battigalli–Catonini–De Vito §3.3 / §8.2. A **nice game** has, for each player, a compact
action interval `[loᵢ, hiᵢ] ⊆ ℝ` and a payoff that is jointly continuous and strictly concave in the
own action. Restrictions are products of compact subintervals. Over such a restriction `K`:

* `rSet K i` — `i`'s best replies to some *deterministic* conjecture drawn from the others' boxes;
* `ndpSet K i` — `i`'s actions not strictly dominated by another *pure* action against those boxes.

**Theorem 30 (per step)** `rSet_eq_ndpSet`: in a nice game these coincide — the engine being Lemma 7
(`bestReply_eq_not_pureDominated`) applied with the conjecture box as the compact connected parameter
space. Iterating (`rPow_eq_ndpPow`) gives `rᵏ = NDpᵏ`.
-/

namespace EcoLean.GameTheory

open Set

/-- A **nice game**: finitely many players, each with a compact action interval `[loᵢ, hiᵢ]`, and a
jointly continuous payoff that is strictly concave in the own action. -/
structure NiceGame where
  /-- The players. -/
  Player : Type*
  [fintypePlayer : Fintype Player]
  [decEqPlayer : DecidableEq Player]
  /-- Lower action bound. -/
  lo : Player → ℝ
  /-- Upper action bound. -/
  hi : Player → ℝ
  /-- The action interval is nonempty. -/
  hlohi : ∀ i, lo i ≤ hi i
  /-- The payoff to each player as a function of the action profile. -/
  payoff : Player → (Player → ℝ) → ℝ
  /-- Each payoff is continuous in the whole profile. -/
  cont : ∀ i, Continuous (payoff i)
  /-- Each payoff is strictly concave in the own action over the action interval. -/
  strictConcave : ∀ (i : Player) (a : Player → ℝ),
    StrictConcaveOn ℝ (Set.Icc (lo i) (hi i)) (fun aᵢ => payoff i (Function.update a i aᵢ))

namespace NiceGame

attribute [instance] NiceGame.fintypePlayer NiceGame.decEqPlayer

variable (G : NiceGame)

/-- A **restriction** records, for each player, a compact subinterval `[klo i, khi i]` of surviving
actions. -/
@[ext] structure Restriction where
  /-- Lower surviving bound. -/
  klo : G.Player → ℝ
  /-- Upper surviving bound. -/
  khi : G.Player → ℝ
  /-- The surviving interval is a nonempty subinterval of the action interval. -/
  valid : ∀ i, G.lo i ≤ klo i ∧ klo i ≤ khi i ∧ khi i ≤ G.hi i

variable {G}

/-- The **conjecture box** of a restriction: profiles with every coordinate in its surviving
interval. (For player `i`, only the coordinates `j ≠ i` matter, since `i`'s own action is overridden
in the payoff; including `i`'s coordinate is harmless.) -/
def Restriction.box (K : G.Restriction) : Set (G.Player → ℝ) :=
  Set.pi Set.univ (fun j => Set.Icc (K.klo j) (K.khi j))

/-- The set of `i`'s **best replies to a deterministic conjecture** drawn from the box of `K`. -/
def rSet (K : G.Restriction) (i : G.Player) : Set ℝ :=
  {aᵢ | aᵢ ∈ Set.Icc (G.lo i) (G.hi i) ∧
    ∃ a ∈ K.box, IsMaxOn (fun bᵢ => G.payoff i (Function.update a i bᵢ))
      (Set.Icc (G.lo i) (G.hi i)) aᵢ}

/-- The set of `i`'s actions **not strictly dominated by another pure action** against the box of
`K`. -/
def ndpSet (K : G.Restriction) (i : G.Player) : Set ℝ :=
  {aᵢ | aᵢ ∈ Set.Icc (G.lo i) (G.hi i) ∧
    ¬ ∃ bᵢ ∈ Set.Icc (G.lo i) (G.hi i),
      ∀ a ∈ K.box, G.payoff i (Function.update a i aᵢ) < G.payoff i (Function.update a i bᵢ)}

/-- **Theorem 30 (per step) / Lemma 7 in a nice game.** Over any restriction, `i`'s best replies to a
deterministic conjecture are exactly its actions not strictly dominated by another pure action. -/
theorem rSet_eq_ndpSet (K : G.Restriction) (i : G.Player) : G.rSet K i = G.ndpSet K i := by
  -- the conjecture box, as a compact connected nonempty type
  have hboxcompact : IsCompact K.box :=
    isCompact_univ_pi fun j => isCompact_Icc
  have hboxconv : Convex ℝ K.box := convex_pi fun j _ => convex_Icc _ _
  have hboxne : K.box.Nonempty :=
    ⟨K.klo, fun j _ => ⟨le_refl _, (K.valid j).2.1⟩⟩
  haveI : CompactSpace ↥K.box := isCompact_iff_compactSpace.mp hboxcompact
  haveI : PreconnectedSpace ↥K.box :=
    Subtype.preconnectedSpace hboxconv.isPreconnected
  haveI : Nonempty ↥K.box := hboxne.to_subtype
  -- the reindexed payoff `u : box → ℝ → ℝ`
  set u : ↥K.box → ℝ → ℝ := fun a bᵢ => G.payoff i (Function.update a.1 i bᵢ) with hu
  have hcont : Continuous (Function.uncurry u) := by
    have : Continuous (fun p : ↥K.box × ℝ => Function.update p.1.1 i p.2) :=
      (continuous_update i).comp (continuous_subtype_val.prodMap continuous_id)
    exact (G.cont i).comp this
  have hstrict : ∀ a : ↥K.box, StrictConcaveOn ℝ (Set.Icc (G.lo i) (G.hi i)) (u a) :=
    fun a => G.strictConcave i a.1
  have hkey := bestReply_eq_not_pureDominated (lo := G.lo i) (hi := G.hi i) (G.hlohi i) hcont hstrict
  -- translate the abstract equality back to `rSet`/`ndpSet`
  ext aᵢ
  rw [rSet, ndpSet, Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · rintro ⟨haI, a, hamem, hmax⟩
    have : aᵢ ∈ {a | a ∈ Set.Icc (G.lo i) (G.hi i)
        ∧ ∃ c : ↥K.box, IsMaxOn (u c) (Set.Icc (G.lo i) (G.hi i)) a} := ⟨haI, ⟨a, hamem⟩, hmax⟩
    rw [hkey] at this
    obtain ⟨haI', hnd⟩ := this
    refine ⟨haI', fun ⟨b, hbI, hdom⟩ => hnd ⟨b, hbI, fun c => hdom c.1 c.2⟩⟩
  · rintro ⟨haI, hnd⟩
    have : aᵢ ∈ {a | a ∈ Set.Icc (G.lo i) (G.hi i)
        ∧ ¬ ∃ b ∈ Set.Icc (G.lo i) (G.hi i), ∀ c : ↥K.box, u c a < u c b} := by
      refine ⟨haI, fun ⟨b, hbI, hdom⟩ => hnd ⟨b, hbI, fun a hamem => hdom ⟨a, hamem⟩⟩⟩
    rw [← hkey] at this
    obtain ⟨haI', c, hmax⟩ := this
    exact ⟨haI', c.1, c.2, hmax⟩

/-- Every best-reply set lies in the action interval. -/
theorem rSet_subset_Icc (K : G.Restriction) (i : G.Player) :
    G.rSet K i ⊆ Set.Icc (G.lo i) (G.hi i) := fun _ h => h.1

/-- The not-pure-dominated set lies in the action interval. -/
theorem ndpSet_subset_Icc (K : G.Restriction) (i : G.Player) :
    G.ndpSet K i ⊆ Set.Icc (G.lo i) (G.hi i) := fun _ h => h.1

/-- A best reply to some conjecture always exists, so the best-reply set is nonempty. -/
theorem rSet_nonempty (K : G.Restriction) (i : G.Player) : (G.rSet K i).Nonempty := by
  obtain ⟨a, ha⟩ : K.box.Nonempty := ⟨K.klo, fun j _ => ⟨le_refl _, (K.valid j).2.1⟩⟩
  have hupd : Continuous (fun bᵢ : ℝ => Function.update a i bᵢ) :=
    continuous_const.update i continuous_id
  have hcont : Continuous (fun bᵢ => G.payoff i (Function.update a i bᵢ)) := (G.cont i).comp hupd
  obtain ⟨aᵢ, haᵢI, haᵢmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (G.hlohi i)) hcont.continuousOn
  exact ⟨aᵢ, haᵢI, a, ha, haᵢmax⟩

/-- The not-pure-dominated set is nonempty (it equals the best-reply set). -/
theorem ndpSet_nonempty (K : G.Restriction) (i : G.Player) : (G.ndpSet K i).Nonempty := by
  rw [← rSet_eq_ndpSet]; exact G.rSet_nonempty K i

/-- The **point-rationalizability operator**: maps a restriction to the restriction of best replies
— an interval by Lemma 7 — recorded by its inf/sup bounds. -/
noncomputable def rOp (K : G.Restriction) : G.Restriction where
  klo i := sInf (G.rSet K i)
  khi i := sSup (G.rSet K i)
  valid i := by
    have hne := G.rSet_nonempty K i
    have hbb : BddBelow (G.rSet K i) := ⟨G.lo i, fun x hx => (G.rSet_subset_Icc K i hx).1⟩
    have hba : BddAbove (G.rSet K i) := ⟨G.hi i, fun x hx => (G.rSet_subset_Icc K i hx).2⟩
    exact ⟨le_csInf hne (fun x hx => (G.rSet_subset_Icc K i hx).1), csInf_le_csSup hne hbb hba,
      csSup_le hne (fun x hx => (G.rSet_subset_Icc K i hx).2)⟩

/-- The **pure-dominance operator**: same, recorded from the not-pure-dominated set. -/
noncomputable def ndpOp (K : G.Restriction) : G.Restriction where
  klo i := sInf (G.ndpSet K i)
  khi i := sSup (G.ndpSet K i)
  valid i := by
    have hne := G.ndpSet_nonempty K i
    have hbb : BddBelow (G.ndpSet K i) := ⟨G.lo i, fun x hx => (G.ndpSet_subset_Icc K i hx).1⟩
    have hba : BddAbove (G.ndpSet K i) := ⟨G.hi i, fun x hx => (G.ndpSet_subset_Icc K i hx).2⟩
    exact ⟨le_csInf hne (fun x hx => (G.ndpSet_subset_Icc K i hx).1), csInf_le_csSup hne hbb hba,
      csSup_le hne (fun x hx => (G.ndpSet_subset_Icc K i hx).2)⟩

/-- The two operators coincide — **Theorem 30, per step** at the level of restrictions. -/
theorem rOp_eq_ndpOp (K : G.Restriction) : G.rOp K = G.ndpOp K := by
  ext i
  · show sInf (G.rSet K i) = sInf (G.ndpSet K i)
    rw [rSet_eq_ndpSet]
  · show sSup (G.rSet K i) = sSup (G.ndpSet K i)
    rw [rSet_eq_ndpSet]

/-- The `k`-fold point-rationalizability restriction `rᵏ`. -/
noncomputable def rPow (K : G.Restriction) (k : ℕ) : G.Restriction := G.rOp^[k] K

/-- The `k`-fold pure-dominance restriction `NDpᵏ`. -/
noncomputable def ndpPow (K : G.Restriction) (k : ℕ) : G.Restriction := G.ndpOp^[k] K

/-- **Theorem 30.** In a nice game, iterated point rationalizability equals iterated elimination of
strictly pure-dominated actions: `rᵏ = NDpᵏ` for every `k`. -/
theorem rPow_eq_ndpPow (K : G.Restriction) (k : ℕ) : G.rPow K k = G.ndpPow K k := by
  have hop : G.rOp = G.ndpOp := funext G.rOp_eq_ndpOp
  show G.rOp^[k] K = G.ndpOp^[k] K
  rw [hop]

end NiceGame

end EcoLean.GameTheory
