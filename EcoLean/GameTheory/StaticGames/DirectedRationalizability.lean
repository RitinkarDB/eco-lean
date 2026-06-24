import EcoLean.GameTheory.StaticGames.Pearce

/-!
# Rationalizability under payoff uncertainty, and directed (Δ-) rationalizability

Following Battigalli–Catonini–De Vito §8.1–8.3. A **game with payoff uncertainty**
`Ĝ = ⟨I, Θ₀, (Θᵢ, Aᵢ, uᵢ : Θ × A → ℝ)⟩` has, for each player `i`, an *information type* `θᵢ ∈ Θᵢ`
(known only to `i`), an action set `Aᵢ`, and a payoff `uᵢ` depending on the full parameter
`θ = (θ₀, (θⱼ)ⱼ)` — residual uncertainty `θ₀` plus everyone's information types — and the action
profile `a = (aⱼ)ⱼ`.

A player `i` of type `θᵢ` holds a *conjecture* `μᵢ` over `Θ₀ × Θ₋ᵢ × A₋ᵢ`; action `aᵢ` is *justified*
on a restriction `C` (with `Cᵢ ⊆ Θᵢ × Aᵢ`) when it best-responds, for `θᵢ`, to some conjecture
supported on `C`. The **justification operator** iterates this; its greatest fixed point is
**rationalizability** (Def 36). **Directed (Δ-) rationalizability** (§8.3) further restricts the
admissible conjectures to a family `Δ` (e.g. exogenous beliefs about `θ`), giving a refinement.

We model a conjecture as a distribution over *full* profiles `Θ₀ × (∀ j, Θⱼ) × (∀ j, Aⱼ)`, overriding
`i`'s own type/action slots with the true type and the candidate action in the payoff. This is
equivalent to a distribution over `Θ₀ × Θ₋ᵢ × A₋ᵢ` (the `i`-marginal is irrelevant after the
override and unconstrained), but avoids dependent `j ≠ i` tuples.

* `IsJustifiedWithin` / `IsBestResponseSet` / `Rationalizable` — justification, self-justifying sets,
  and the greatest fixed point (mirroring `CorrelatedRationalizability`).
* `rationalizable_isBestResponseSet` / `subset_rationalizable_of_isBestResponseSet` — `Rationalizable`
  is itself a best-response set, and it is the largest.
* `IsDeltaJustifiedWithin` / `DeltaRationalizable` — the Δ-restricted (directed) versions, with the
  same greatest-fixed-point structure.
* `deltaRationalizable_mono` — a wider belief restriction yields a (weakly) larger solution.
* `deltaRationalizable_subset_rationalizable` — **directed rationalizability refines
  rationalizability**: restricting beliefs can only remove type-action pairs.
-/

namespace EcoLean.GameTheory

open scoped BigOperators

/-- A finite **game with payoff uncertainty** (Battigalli–Catonini–De Vito §8.1):
`Ĝ = ⟨I, Θ₀, (Θᵢ, Aᵢ, uᵢ : Θ × A → ℝ)⟩`.  `Residual` is the residual-uncertainty space `Θ₀`,
`InfoType i` is player `i`'s information-type space `Θᵢ`, `Action i` is `Aᵢ`, and `payoff i`
is `uᵢ`, depending on `θ₀`, the information-type profile, and the action profile. -/
structure PayoffUncertaintyGame where
  /-- The players. -/
  Player : Type*
  /-- The residual-uncertainty space `Θ₀` (never resolved by strategic reasoning). -/
  Residual : Type*
  /-- Player `i`'s information-type space `Θᵢ` (known only to `i`). -/
  InfoType : Player → Type*
  /-- Player `i`'s action set `Aᵢ`. -/
  Action : Player → Type*
  /-- Player `i`'s parameterized payoff `uᵢ : Θ × A → ℝ`, as a function of `θ₀`, the
  information-type profile `(θⱼ)ⱼ`, and the action profile `(aⱼ)ⱼ`. -/
  payoff : Player → Residual → (∀ j, InfoType j) → (∀ j, Action j) → ℝ

namespace PayoffUncertaintyGame

variable {G : PayoffUncertaintyGame} [Fintype G.Player] [DecidableEq G.Player]
  [Fintype G.Residual] [∀ i, Fintype (G.InfoType i)] [∀ i, Fintype (G.Action i)]

/-- A *full profile*: residual uncertainty `θ₀`, an information type for every player, and an action
for every player. Conjectures range over these; a player's own slots are overridden in the payoff. -/
abbrev FullProfile (G : PayoffUncertaintyGame) : Type _ :=
  G.Residual × (∀ j, G.InfoType j) × (∀ j, G.Action j)

/-- A *restriction* `C`: for each player a set of admissible `(information-type, action)` pairs
`Cᵢ ⊆ Θᵢ × Aᵢ`. (Residual uncertainty `Θ₀` is never restricted.) -/
abbrev Restriction (G : PayoffUncertaintyGame) : Type _ :=
  ∀ i, Set (G.InfoType i × G.Action i)

/-- The conjecture-`μ` expected payoff to player `i` of type `θᵢ` choosing `aᵢ`: the average of `uᵢ`
over full profiles, with `i`'s own type set to `θᵢ` and action to `aᵢ`. -/
noncomputable def expectedPayoff (μ : G.FullProfile → ℝ) (i : G.Player)
    (θᵢ : G.InfoType i) (aᵢ : G.Action i) : ℝ :=
  ∑ fp : G.FullProfile,
    μ fp * G.payoff i fp.1 (Function.update fp.2.1 i θᵢ) (Function.update fp.2.2 i aᵢ)

/-- `μ` is a probability distribution over full profiles. -/
def IsDistribution (μ : G.FullProfile → ℝ) : Prop :=
  (∀ fp, 0 ≤ μ fp) ∧ ∑ fp, μ fp = 1

/-- `aᵢ` is a *best response* for type `θᵢ` to conjecture `μ`: it maximises `i`'s expected payoff. -/
def IsBestResponseToBelief (μ : G.FullProfile → ℝ) (i : G.Player) (θᵢ : G.InfoType i)
    (aᵢ : G.Action i) : Prop :=
  ∀ aᵢ' : G.Action i, G.expectedPayoff μ i θᵢ aᵢ' ≤ G.expectedPayoff μ i θᵢ aᵢ

/-- Conjecture `μ` is *supported on the restriction `C`* (off `i`): no weight on full profiles where
some opponent `j ≠ i` has `(θⱼ, aⱼ) ∉ Cⱼ`. -/
def BeliefSupportedOn (μ : G.FullProfile → ℝ) (C : G.Restriction) (i : G.Player) : Prop :=
  ∀ fp : G.FullProfile, (∃ j, j ≠ i ∧ (fp.2.1 j, fp.2.2 j) ∉ C j) → μ fp = 0

/-- `aᵢ` is *justified for type `θᵢ` within `C`*: it best-responds, for `θᵢ`, to some distribution
supported on `C`. This is the one-step justification operator of §8.2. -/
def IsJustifiedWithin (C : G.Restriction) (i : G.Player) (θᵢ : G.InfoType i)
    (aᵢ : G.Action i) : Prop :=
  ∃ μ : G.FullProfile → ℝ,
    G.IsDistribution μ ∧ G.BeliefSupportedOn μ C i ∧ G.IsBestResponseToBelief μ i θᵢ aᵢ

/-- `C` is a *best-response set*: every admissible pair `(θᵢ, aᵢ) ∈ Cᵢ` is justified within `C`. -/
def IsBestResponseSet (C : G.Restriction) : Prop :=
  ∀ (i : G.Player), ∀ p ∈ C i, G.IsJustifiedWithin C i p.1 p.2

/-- The *rationalizable* type-action pairs (Def 36): those in some best-response set. Equivalently the
largest best-response set — the greatest fixed point of the justification operator. -/
def Rationalizable (G : PayoffUncertaintyGame) [Fintype G.Player] [DecidableEq G.Player]
    [Fintype G.Residual] [∀ i, Fintype (G.InfoType i)] [∀ i, Fintype (G.Action i)] :
    G.Restriction :=
  fun i => {p | ∃ C : G.Restriction, G.IsBestResponseSet C ∧ p ∈ C i}

theorem mem_rationalizable_iff (i : G.Player) (p : G.InfoType i × G.Action i) :
    p ∈ G.Rationalizable i ↔ ∃ C : G.Restriction, G.IsBestResponseSet C ∧ p ∈ C i :=
  Iff.rfl

/-! ### Monotonicity of justification, and the largest fixed point -/

/-- Justification is monotone in the restriction: a belief supported on `C` is supported on any
larger `D`, so a pair justified within `C` is justified within `D`. -/
theorem isJustifiedWithin_mono {C D : G.Restriction} {i : G.Player} {θᵢ : G.InfoType i}
    {aᵢ : G.Action i} (h : G.IsJustifiedWithin C i θᵢ aᵢ) (hCD : ∀ j, C j ⊆ D j) :
    G.IsJustifiedWithin D i θᵢ aᵢ := by
  obtain ⟨μ, hdist, hsupp, hbest⟩ := h
  refine ⟨μ, hdist, ?_, hbest⟩
  rintro fp ⟨j, hj, hjD⟩
  exact hsupp fp ⟨j, hj, fun hjC => hjD (hCD j hjC)⟩

/-- Every best-response set is contained in the rationalizable pairs. -/
theorem subset_rationalizable_of_isBestResponseSet {C : G.Restriction}
    (hC : G.IsBestResponseSet C) (i : G.Player) : C i ⊆ G.Rationalizable i :=
  fun _ hp => ⟨C, hC, hp⟩

/-- The rationalizable pairs form a best-response set: the justifying belief of a pair lives in some
`C ⊆ Rationalizable`, hence is supported on the latter. -/
theorem rationalizable_isBestResponseSet : G.IsBestResponseSet G.Rationalizable := by
  intro i p hp
  obtain ⟨C, hC, hpC⟩ := hp
  exact isJustifiedWithin_mono (hC i p hpC)
    (subset_rationalizable_of_isBestResponseSet hC)

/-! ### Directed (Δ-) rationalizability -/

/-- A *belief restriction* `Δ`: for each player and information type, a set of admissible conjectures
(e.g. exogenous restrictions on first-order beliefs about `θ`). The unrestricted case is
`fun _ _ => Set.univ`. -/
abbrev BeliefRestriction (G : PayoffUncertaintyGame) : Type _ :=
  ∀ i, G.InfoType i → Set (G.FullProfile → ℝ)

/-- `aᵢ` is *Δ-justified for type `θᵢ` within `C`*: justified by a conjecture that, in addition to
being supported on `C`, is admissible under the belief restriction `Δ`. -/
def IsDeltaJustifiedWithin (Δ : G.BeliefRestriction) (C : G.Restriction) (i : G.Player)
    (θᵢ : G.InfoType i) (aᵢ : G.Action i) : Prop :=
  ∃ μ : G.FullProfile → ℝ,
    μ ∈ Δ i θᵢ ∧ G.IsDistribution μ ∧ G.BeliefSupportedOn μ C i ∧
      G.IsBestResponseToBelief μ i θᵢ aᵢ

/-- `C` is a *Δ-best-response set*: every admissible pair is Δ-justified within `C`. -/
def IsDeltaBestResponseSet (Δ : G.BeliefRestriction) (C : G.Restriction) : Prop :=
  ∀ (i : G.Player), ∀ p ∈ C i, G.IsDeltaJustifiedWithin Δ C i p.1 p.2

/-- The **directed (Δ-) rationalizable** type-action pairs (§8.3): those in some Δ-best-response set —
the greatest fixed point of the Δ-restricted justification operator. -/
def DeltaRationalizable (G : PayoffUncertaintyGame) [Fintype G.Player] [DecidableEq G.Player]
    [Fintype G.Residual] [∀ i, Fintype (G.InfoType i)] [∀ i, Fintype (G.Action i)]
    (Δ : G.BeliefRestriction) : G.Restriction :=
  fun i => {p | ∃ C : G.Restriction, G.IsDeltaBestResponseSet Δ C ∧ p ∈ C i}

/-- Δ-justification is monotone in the restriction (same proof as `isJustifiedWithin_mono`). -/
theorem isDeltaJustifiedWithin_mono {Δ : G.BeliefRestriction} {C D : G.Restriction} {i : G.Player}
    {θᵢ : G.InfoType i} {aᵢ : G.Action i} (h : G.IsDeltaJustifiedWithin Δ C i θᵢ aᵢ)
    (hCD : ∀ j, C j ⊆ D j) : G.IsDeltaJustifiedWithin Δ D i θᵢ aᵢ := by
  obtain ⟨μ, hΔ, hdist, hsupp, hbest⟩ := h
  refine ⟨μ, hΔ, hdist, ?_, hbest⟩
  rintro fp ⟨j, hj, hjD⟩
  exact hsupp fp ⟨j, hj, fun hjC => hjD (hCD j hjC)⟩

theorem subset_deltaRationalizable_of_isDeltaBestResponseSet {Δ : G.BeliefRestriction}
    {C : G.Restriction} (hC : G.IsDeltaBestResponseSet Δ C) (i : G.Player) :
    C i ⊆ G.DeltaRationalizable Δ i :=
  fun _ hp => ⟨C, hC, hp⟩

theorem deltaRationalizable_isDeltaBestResponseSet (Δ : G.BeliefRestriction) :
    G.IsDeltaBestResponseSet Δ (G.DeltaRationalizable Δ) := by
  intro i p hp
  obtain ⟨C, hC, hpC⟩ := hp
  exact isDeltaJustifiedWithin_mono (hC i p hpC)
    (subset_deltaRationalizable_of_isDeltaBestResponseSet hC)

/-! ### Directed rationalizability refines rationalizability -/

/-- A Δ-justified pair is Δ'-justified whenever `Δ ⊆ Δ'` (more admissible beliefs). -/
theorem isDeltaJustifiedWithin_mono_belief {Δ Δ' : G.BeliefRestriction} {C : G.Restriction}
    {i : G.Player} {θᵢ : G.InfoType i} {aᵢ : G.Action i}
    (h : G.IsDeltaJustifiedWithin Δ C i θᵢ aᵢ) (hΔ : ∀ i θ, Δ i θ ⊆ Δ' i θ) :
    G.IsDeltaJustifiedWithin Δ' C i θᵢ aᵢ := by
  obtain ⟨μ, hμΔ, hrest⟩ := h
  exact ⟨μ, hΔ i θᵢ hμΔ, hrest⟩

/-- **Monotonicity in the belief restriction.** A wider family of admissible conjectures yields a
(weakly) larger directed-rationalizable set. -/
theorem deltaRationalizable_mono {Δ Δ' : G.BeliefRestriction} (hΔ : ∀ i θ, Δ i θ ⊆ Δ' i θ)
    (i : G.Player) : G.DeltaRationalizable Δ i ⊆ G.DeltaRationalizable Δ' i := by
  rintro p ⟨C, hC, hpC⟩
  exact ⟨C, fun j q hq => isDeltaJustifiedWithin_mono_belief (hC j q hq) hΔ, hpC⟩

/-- A Δ-best-response set is a (plain) best-response set: drop the belief-admissibility requirement. -/
theorem isBestResponseSet_of_isDeltaBestResponseSet {Δ : G.BeliefRestriction} {C : G.Restriction}
    (hC : G.IsDeltaBestResponseSet Δ C) : G.IsBestResponseSet C := by
  intro i p hp
  obtain ⟨μ, _, hdist, hsupp, hbest⟩ := hC i p hp
  exact ⟨μ, hdist, hsupp, hbest⟩

/-- **Directed rationalizability refines rationalizability.** Imposing belief restrictions can only
remove type-action pairs: every Δ-rationalizable pair is rationalizable. -/
theorem deltaRationalizable_subset_rationalizable (Δ : G.BeliefRestriction) (i : G.Player) :
    G.DeltaRationalizable Δ i ⊆ G.Rationalizable i := by
  rintro p ⟨C, hC, hpC⟩
  exact ⟨C, isBestResponseSet_of_isDeltaBestResponseSet hC, hpC⟩

/-- With the trivial (all-conjectures-admissible) belief restriction, directed rationalizability is
ordinary rationalizability: the two justification operators coincide. -/
theorem deltaRationalizable_univ_eq_rationalizable (i : G.Player) :
    G.DeltaRationalizable (fun _ _ => Set.univ) i = G.Rationalizable i := by
  ext p
  constructor
  · intro hp; exact deltaRationalizable_subset_rationalizable _ i hp
  · rintro ⟨C, hC, hpC⟩
    exact ⟨C, fun j q hq => by
      obtain ⟨μ, hdist, hsupp, hbest⟩ := hC j q hq
      exact ⟨μ, Set.mem_univ _, hdist, hsupp, hbest⟩, hpC⟩

/-! ### Theorem 28: every information-type retains a rationalizable action

The justification operator cannot eliminate any information-type — only the actions a type may play.
Iterating from the full restriction, every type always keeps at least one justified action (a best
response to a Dirac belief on a profile drawn from the previous round), and the (finite) iteration
stabilises to a best-response set that is rationalizable. -/

/-- The one-step justification operator on restrictions (the operator `ρ` of §8.2). -/
def justifyOp (C : G.Restriction) : G.Restriction :=
  fun i => {p | G.IsJustifiedWithin C i p.1 p.2}

theorem justifyOp_mono {C D : G.Restriction} (hCD : ∀ j, C j ⊆ D j) (i : G.Player) :
    G.justifyOp C i ⊆ G.justifyOp D i :=
  fun _ hp => isJustifiedWithin_mono hp hCD

/-- The iterated justification operator from the full restriction: `ρᵏ(Θ × A)`. -/
def rhoPow (G : PayoffUncertaintyGame) [Fintype G.Player] [DecidableEq G.Player]
    [Fintype G.Residual] [∀ i, Fintype (G.InfoType i)] [∀ i, Fintype (G.Action i)] :
    ℕ → G.Restriction
  | 0 => fun _ => Set.univ
  | k + 1 => G.justifyOp (G.rhoPow k)

theorem rhoPow_subset_succ : ∀ (k : ℕ) (i : G.Player), G.rhoPow (k + 1) i ⊆ G.rhoPow k i := by
  intro k
  induction k with
  | zero => exact fun i _ _ => Set.mem_univ _
  | succ k ih => exact fun i => justifyOp_mono ih i

/-- Every information-type retains a justified action at every iteration: build a Dirac belief on a
profile drawn (off `i`) from the previous round, and take a best response to it. -/
theorem rhoPow_nonempty [Nonempty G.Residual] [∀ i, Nonempty (G.InfoType i)]
    [∀ i, Nonempty (G.Action i)] :
    ∀ (k : ℕ) (i : G.Player) (θᵢ : G.InfoType i), ∃ aᵢ, (θᵢ, aᵢ) ∈ G.rhoPow k i := by
  intro k
  induction k with
  | zero => exact fun i _ => ⟨Classical.arbitrary (G.Action i), Set.mem_univ _⟩
  | succ k ih =>
    intro i θᵢ
    classical
    have hwit : ∀ j, ∃ p : G.InfoType j × G.Action j, p ∈ G.rhoPow k j := fun j =>
      ⟨(Classical.arbitrary (G.InfoType j), (ih j (Classical.arbitrary (G.InfoType j))).choose),
        (ih j (Classical.arbitrary (G.InfoType j))).choose_spec⟩
    set fp₀ : G.FullProfile := ⟨Classical.arbitrary G.Residual,
      fun j => (hwit j).choose.1, fun j => (hwit j).choose.2⟩ with hfp
    set μ : G.FullProfile → ℝ := fun fp => if fp = fp₀ then 1 else 0 with hμ
    have hμdist : G.IsDistribution μ := by
      refine ⟨fun fp => by simp only [hμ]; split_ifs <;> norm_num, ?_⟩
      simp only [hμ]
      rw [Finset.sum_ite_eq' Finset.univ fp₀ (fun _ => (1 : ℝ))]
      simp
    have hμsupp : G.BeliefSupportedOn μ (G.rhoPow k) i := by
      rintro fp ⟨j, _, hjnot⟩
      have hne : fp ≠ fp₀ := by rintro rfl; exact hjnot (hwit j).choose_spec
      simp only [hμ]; exact if_neg hne
    obtain ⟨aᵢ, _, haᵢ⟩ := Finset.exists_max_image Finset.univ
      (fun aᵢ => G.expectedPayoff μ i θᵢ aᵢ) ⟨Classical.arbitrary (G.Action i), Finset.mem_univ _⟩
    exact ⟨aᵢ, μ, hμdist, hμsupp, fun aᵢ' => haᵢ aᵢ' (Finset.mem_univ _)⟩

/-- The (finite) iteration stabilises to a fixed point of the justification operator. -/
theorem exists_rhoPow_fixed : ∃ N, G.justifyOp (G.rhoPow N) = G.rhoPow N := by
  set c : ℕ → ℕ := fun k => ∑ i, (G.rhoPow k i).ncard with hc
  have hanti : ∀ k, c (k + 1) ≤ c k := fun k =>
    Finset.sum_le_sum fun i _ => Set.ncard_le_ncard (rhoPow_subset_succ k i) (Set.toFinite _)
  obtain ⟨N, hN⟩ : ∃ N, c (N + 1) = c N := by
    obtain ⟨N, hNmem⟩ := Nat.sInf_mem (Set.range_nonempty c)
    exact ⟨N, le_antisymm (hanti N) (by rw [hNmem]; exact Nat.sInf_le ⟨N + 1, rfl⟩)⟩
  refine ⟨N, funext fun i => ?_⟩
  have hsub : G.rhoPow (N + 1) i ⊆ G.rhoPow N i := rhoPow_subset_succ N i
  have heqcard : (G.rhoPow N i).ncard ≤ (G.rhoPow (N + 1) i).ncard := by
    by_contra hlt
    push_neg at hlt
    have : c (N + 1) < c N :=
      Finset.sum_lt_sum (fun j _ => Set.ncard_le_ncard (rhoPow_subset_succ N j) (Set.toFinite _))
        ⟨i, Finset.mem_univ i, hlt⟩
    omega
  show G.rhoPow (N + 1) i = G.rhoPow N i
  exact Set.eq_of_subset_of_ncard_le hsub heqcard (Set.toFinite _)

/-- **Theorem 28** (first part). In a finite game with payoff uncertainty every information-type of
every player retains at least one rationalizable action: rationalizability never eliminates a type. -/
theorem rationalizable_nonempty [Nonempty G.Residual] [∀ i, Nonempty (G.InfoType i)]
    [∀ i, Nonempty (G.Action i)] (i : G.Player) (θᵢ : G.InfoType i) :
    ∃ aᵢ, (θᵢ, aᵢ) ∈ G.Rationalizable i := by
  obtain ⟨N, hN⟩ := exists_rhoPow_fixed (G := G)
  have hbrs : G.IsBestResponseSet (G.rhoPow N) := by
    intro j p hp
    have hp' : p ∈ G.justifyOp (G.rhoPow N) j := (congrFun hN j).symm ▸ hp
    exact hp'
  obtain ⟨aᵢ, haᵢ⟩ := rhoPow_nonempty N i θᵢ
  exact ⟨aᵢ, G.rhoPow N, hbrs, haᵢ⟩

/-! ### Theorem 29: rationalizability equals iterated dominance

For finite games, the justification operator `ρ` coincides with the elimination of strictly
dominated pairs `ND` (Lemma 23 / Theorem 29). The engine is the payoff-uncertainty analogue of
Pearce's lemma — a separating-hyperplane (Gordan) argument over the `C`-supported profiles. -/

/-- The payoff of player `i` with information-type `θᵢ` playing `aᵢ`, at the full profile `fp`. -/
def devValue (i : G.Player) (θᵢ : G.InfoType i) (aᵢ : G.Action i) (fp : G.FullProfile) : ℝ :=
  G.payoff i fp.1 (Function.update fp.2.1 i θᵢ) (Function.update fp.2.2 i aᵢ)

/-- `aᵢ` is *strictly dominated for `θᵢ` by a mixed strategy within `C`* (Definition 37): some mixture
`σ` over `i`'s actions strictly beats `aᵢ` against every profile drawn (off `i`) from `C`. -/
def IsMixedDominatedOn (C : G.Restriction) (i : G.Player) (θᵢ : G.InfoType i)
    (aᵢ : G.Action i) : Prop :=
  ∃ σ : G.Action i → ℝ, σ ∈ stdSimplex ℝ (G.Action i) ∧
    ∀ fp : G.FullProfile, (∀ j, j ≠ i → (fp.2.1 j, fp.2.2 j) ∈ C j) →
      G.devValue i θᵢ aᵢ fp < ∑ aᵢ', σ aᵢ' * G.devValue i θᵢ aᵢ' fp

/-- *Easy half.* A justified action is not strictly dominated by a mixture within the same `C`. -/
theorem isJustifiedWithin_not_mixedDominatedOn {C : G.Restriction} {i : G.Player}
    {θᵢ : G.InfoType i} {aᵢ : G.Action i} (h : G.IsJustifiedWithin C i θᵢ aᵢ) :
    ¬ G.IsMixedDominatedOn C i θᵢ aᵢ := by
  obtain ⟨μ, ⟨hμnn, hμsum⟩, hμsupp, hμbest⟩ := h
  rintro ⟨σ, ⟨hσnn, hσsum⟩, hσdom⟩
  have hsupp : ∀ fp, 0 < μ fp → ∀ j, j ≠ i → (fp.2.1 j, fp.2.2 j) ∈ C j := fun fp hp j hj => by
    by_contra hjX; exact hp.ne' (hμsupp fp ⟨j, hj, hjX⟩)
  have hswap : ∑ fp, μ fp * (∑ ci, σ ci * G.devValue i θᵢ ci fp)
      = ∑ ci, σ ci * (∑ fp, μ fp * G.devValue i θᵢ ci fp) := by
    simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun ci _ => Finset.sum_congr rfl fun fp _ => by ring
  have hub : ∑ ci, σ ci * (∑ fp, μ fp * G.devValue i θᵢ ci fp)
      ≤ ∑ fp, μ fp * G.devValue i θᵢ aᵢ fp :=
    calc ∑ ci, σ ci * (∑ fp, μ fp * G.devValue i θᵢ ci fp)
        ≤ ∑ ci, σ ci * (∑ fp, μ fp * G.devValue i θᵢ aᵢ fp) :=
          Finset.sum_le_sum fun ci _ => mul_le_mul_of_nonneg_left (hμbest ci) (hσnn ci)
      _ = ∑ fp, μ fp * G.devValue i θᵢ aᵢ fp := by rw [← Finset.sum_mul, hσsum, one_mul]
  have hpos : ∃ fp₀, 0 < μ fp₀ := by
    by_contra hh; push_neg at hh
    have : ∑ fp, μ fp ≤ 0 := Finset.sum_nonpos fun fp _ => hh fp
    rw [hμsum] at this; linarith
  obtain ⟨fp₀, hfp₀⟩ := hpos
  have hlt : ∑ fp, μ fp * G.devValue i θᵢ aᵢ fp
      < ∑ fp, μ fp * (∑ ci, σ ci * G.devValue i θᵢ ci fp) := by
    refine Finset.sum_lt_sum (fun fp _ => ?_) ⟨fp₀, Finset.mem_univ fp₀, ?_⟩
    · rcases eq_or_lt_of_le (hμnn fp) with h0 | h0
      · rw [← h0, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hσdom fp (hsupp fp h0))) (le_of_lt h0)
    · exact mul_lt_mul_of_pos_left (hσdom fp₀ (hsupp fp₀ hfp₀)) hfp₀
  rw [hswap] at hlt
  linarith

open scoped Classical in
/-- *Hard half (Lemma 23).* An action not strictly dominated by a mixture within `C` is justified
within `C`: Gordan's theorem applied to the gain matrix over the `C`-supported profiles. -/
theorem exists_belief_of_not_mixedDominatedOn {C : G.Restriction} {i : G.Player}
    {θᵢ : G.InfoType i} {aᵢ : G.Action i} (h : ¬ G.IsMixedDominatedOn C i θᵢ aᵢ) :
    G.IsJustifiedWithin C i θᵢ aᵢ := by
  classical
  haveI : Nonempty (G.Action i) := ⟨aᵢ⟩
  let S : Finset G.FullProfile :=
    Finset.univ.filter (fun fp => ∀ j, j ≠ i → (fp.2.1 j, fp.2.2 j) ∈ C j)
  have hmemS : ∀ fp, fp ∈ S ↔ ∀ j, j ≠ i → (fp.2.1 j, fp.2.2 j) ∈ C j := fun fp => by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hSne : S.Nonempty
  · haveI : Nonempty ↥S := Finset.nonempty_coe_sort.mpr hSne
    obtain ⟨y, hymem, hyle⟩ := EconLib.LinearInequalities.exists_separating_distribution_via_farkas
      (fun (ci : G.Action i) (k : ↥S) => G.devValue i θᵢ ci k.1 - G.devValue i θᵢ aᵢ k.1)
      (by
        rintro ⟨x, hx, hpos⟩
        refine h ⟨x, hx, fun fp hfp => ?_⟩
        have hp := hpos ⟨fp, (hmemS fp).mpr hfp⟩
        have hsum : ∑ ci, x ci * (G.devValue i θᵢ ci fp - G.devValue i θᵢ aᵢ fp)
            = (∑ ci, x ci * G.devValue i θᵢ ci fp) - G.devValue i θᵢ aᵢ fp := by
          rw [show (∑ ci, x ci * (G.devValue i θᵢ ci fp - G.devValue i θᵢ aᵢ fp))
              = ∑ ci, (x ci * G.devValue i θᵢ ci fp - x ci * G.devValue i θᵢ aᵢ fp) from
            Finset.sum_congr rfl fun ci _ => by ring, Finset.sum_sub_distrib, ← Finset.sum_mul,
            hx.2, one_mul]
        rw [hsum] at hp; linarith)
    set μ : G.FullProfile → ℝ := fun fp => if hfp : fp ∈ S then y ⟨fp, hfp⟩ else 0 with hμ
    have hμpos : ∀ fp (hfp : fp ∈ S), μ fp = y ⟨fp, hfp⟩ := fun fp hfp => by simp only [hμ, dif_pos hfp]
    have hμneg : ∀ fp, fp ∉ S → μ fp = 0 := fun fp hfp => by simp only [hμ, dif_neg hfp]
    have hyμ : ∀ k : ↥S, μ k.1 = y k := fun k => by simp only [hμ, dif_pos k.2, Subtype.coe_eta]
    have hred : ∀ f : G.FullProfile → ℝ, ∑ fp, μ fp * f fp = ∑ k : ↥S, y k * f k.1 := by
      intro f
      rw [← Finset.sum_subset (Finset.subset_univ S) (fun fp _ hfp => by rw [hμneg fp hfp, zero_mul]),
        ← Finset.sum_coe_sort S (fun fp => μ fp * f fp)]
      exact Finset.sum_congr rfl fun k _ => by rw [hyμ k]
    refine ⟨μ, ⟨fun fp => ?_, ?_⟩, ?_, ?_⟩
    · by_cases hfp : fp ∈ S
      · rw [hμpos fp hfp]; exact hymem.1 _
      · exact le_of_eq (hμneg fp hfp).symm
    · have h1 := hred (fun _ => (1 : ℝ)); simp only [mul_one] at h1; rw [h1]; exact hymem.2
    · rintro fp ⟨j, hj, hjX⟩
      exact hμneg fp (fun hfpS => hjX ((hmemS fp).mp hfpS j hj))
    · intro ci
      have hbe : ∀ c, G.expectedPayoff μ i θᵢ c = ∑ fp, μ fp * G.devValue i θᵢ c fp := fun _ => rfl
      rw [hbe, hbe, hred (fun fp => G.devValue i θᵢ ci fp), hred (fun fp => G.devValue i θᵢ aᵢ fp)]
      have hle := hyle ci
      have hsub : ∑ k : ↥S, y k * (G.devValue i θᵢ ci k.1 - G.devValue i θᵢ aᵢ k.1)
          = (∑ k : ↥S, y k * G.devValue i θᵢ ci k.1) - ∑ k : ↥S, y k * G.devValue i θᵢ aᵢ k.1 := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
      rw [hsub] at hle; linarith
  · exact absurd ⟨Pi.single aᵢ 1, single_mem_stdSimplex ℝ aᵢ,
      fun fp hfp => absurd ((hmemS fp).mpr hfp)
        (by rw [Finset.not_nonempty_iff_eq_empty.mp hSne]; exact Finset.notMem_empty fp)⟩ h

/-- **Lemma 23 / Theorem 29 (per element).** Within `C`, an action is justified iff it is not strictly
dominated by a mixed strategy. -/
theorem isJustifiedWithin_iff_not_mixedDominatedOn {C : G.Restriction} {i : G.Player}
    {θᵢ : G.InfoType i} {aᵢ : G.Action i} :
    G.IsJustifiedWithin C i θᵢ aᵢ ↔ ¬ G.IsMixedDominatedOn C i θᵢ aᵢ :=
  ⟨isJustifiedWithin_not_mixedDominatedOn, exists_belief_of_not_mixedDominatedOn⟩

/-- The elimination-of-dominated-actions operator `ND`: drop from `C` the pairs strictly dominated by
a mixture within `C`. -/
def ndOp (C : G.Restriction) : G.Restriction :=
  fun i => {p | p ∈ C i ∧ ¬ G.IsMixedDominatedOn C i p.1 p.2}

/-- The iterated dominance operator `NDᵏ(Θ × A)`. -/
def ndPow (G : PayoffUncertaintyGame) [Fintype G.Player] [DecidableEq G.Player]
    [Fintype G.Residual] [∀ i, Fintype (G.InfoType i)] [∀ i, Fintype (G.Action i)] :
    ℕ → G.Restriction
  | 0 => fun _ => Set.univ
  | k + 1 => G.ndOp (G.ndPow k)

/-- **Theorem 29.** Rationalizability equals iterated elimination of strictly dominated strategies:
`ρᵏ(Θ × A) = NDᵏ(Θ × A)` at every stage. The step uses Lemma 23 together with the fact that the
justification iterates are decreasing (so a pair justified within `ρᵏ` already lies in `ρᵏ`). -/
theorem rhoPow_eq_ndPow : ∀ k : ℕ, G.rhoPow k = G.ndPow k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    ext p
    show G.IsJustifiedWithin (G.rhoPow k) i p.1 p.2
      ↔ (p ∈ G.ndPow k i ∧ ¬ G.IsMixedDominatedOn (G.ndPow k) i p.1 p.2)
    rw [ih, isJustifiedWithin_iff_not_mixedDominatedOn]
    refine ⟨fun hndom => ⟨?_, hndom⟩, fun h => h.2⟩
    have hjust : G.IsJustifiedWithin (G.ndPow k) i p.1 p.2 :=
      isJustifiedWithin_iff_not_mixedDominatedOn.mpr hndom
    rw [← ih] at hjust
    have hmem : p ∈ G.rhoPow k i := rhoPow_subset_succ k i hjust
    rwa [ih] at hmem

end PayoffUncertaintyGame

end EcoLean.GameTheory
