import EcoLean.ChoicePreferenceUtility.OnSet
import EcoLean.GameTheory.MathLanguage.ProbabilityMeasures
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-!
# Lotteries and vNM-style preference axioms

This file starts the expected-utility side of the game-theory foundations.
Lotteries are represented by mathlib probability mass functions.  The
definitions are intentionally thin wrappers around the existing
`EcoLean.Preference` API: the primitive object is still a weak preference
relation, now specialized to lotteries and restricted to a carrier set when
needed.

The continuity axiom below is the Archimedean/mixture continuity axiom used in
von Neumann-Morgenstern expected utility theory.  It is not a Debreu-style
topological continuity theorem for preferences over commodity spaces.
-/

universe u

namespace EcoLean
namespace GameTheory
namespace ExpectedUtility

variable {Outcome : Type u}

/-! ## Lotteries and mixtures -/

/-- A lottery over outcomes, represented as a probability mass function. -/
abbrev Lottery (Outcome : Type u) := PMF Outcome

/-- The set of lotteries whose support is contained in a carrier of outcomes. -/
def LotteriesOn (S : Set Outcome) : Set (Lottery Outcome) :=
  {p | p.support ⊆ S}

/-- The degenerate lottery putting probability one on `x`. -/
noncomputable def degenerate (x : Outcome) : Lottery Outcome :=
  PMF.pure x

/--
The mixture lottery that plays `p` with probability `a` and `q` with the
remaining probability.
-/
noncomputable def mix (p q : Lottery Outcome) (a : NNReal) (ha : a ≤ 1) :
    Lottery Outcome :=
  (PMF.bernoulli a ha).bind fun b => if b then p else q

/-- The real-valued probability assigned by a lottery to an outcome. -/
noncomputable def prob (p : Lottery Outcome) (x : Outcome) : ℝ :=
  (p x).toReal

/-- The finite expected value of an outcome utility index under a lottery. -/
noncomputable def expectedValue [Fintype Outcome]
    (u : Outcome → ℝ) (p : Lottery Outcome) : ℝ :=
  ∑ x : Outcome, prob p x * u x

/-- A carrier of lotteries is closed under binary probabilistic mixtures. -/
def MixtureClosed (S : Set (Lottery Outcome)) : Prop :=
  ∀ ⦃p q : Lottery Outcome⦄, p ∈ S → q ∈ S →
    ∀ (a : NNReal) (ha : a ≤ 1), mix p q a ha ∈ S

@[simp] theorem mem_lotteriesOn_iff {S : Set Outcome} {p : Lottery Outcome} :
    p ∈ LotteriesOn S ↔ p.support ⊆ S :=
  Iff.rfl

theorem lotteriesOn_mono {S T : Set Outcome}
    (hST : S ⊆ T) :
    LotteriesOn S ⊆ LotteriesOn T := by
  intro p hp x hx
  exact hST (hp hx)

theorem degenerate_mem_lotteriesOn {S : Set Outcome} {x : Outcome}
    (hx : x ∈ S) :
    degenerate x ∈ LotteriesOn S := by
  intro y hy
  have hyx : y = x := (PMF.mem_support_pure_iff x y).mp hy
  simpa [hyx] using hx

theorem mix_mem_lotteriesOn {S : Set Outcome} {p q : Lottery Outcome}
    (hp : p ∈ LotteriesOn S) (hq : q ∈ LotteriesOn S)
    (a : NNReal) (ha : a ≤ 1) :
    mix p q a ha ∈ LotteriesOn S := by
  intro x hx
  rw [mix] at hx
  rcases (PMF.mem_support_bind_iff (p := PMF.bernoulli a ha)
      (f := fun b => if b then p else q) x).mp hx with ⟨b, _hb, hxb⟩
  cases b <;> simp at hxb
  · exact hq hxb
  · exact hp hxb

theorem lotteriesOn_mixtureClosed (S : Set Outcome) :
    MixtureClosed (LotteriesOn S) := by
  intro p q hp hq a ha
  exact mix_mem_lotteriesOn hp hq a ha

theorem mix_apply
    (p q : Lottery Outcome) (a : NNReal) (ha : a ≤ 1) (x : Outcome) :
    mix p q a ha x =
      (a : ENNReal) * p x + ((1 - a : NNReal) : ENNReal) * q x := by
  rw [mix, PMF.bind_apply]
  rw [tsum_fintype]
  simp [PMF.bernoulli_apply]

theorem prob_mix
    (p q : Lottery Outcome) (a : NNReal) (ha : a ≤ 1) (x : Outcome) :
    prob (mix p q a ha) x =
      (a : ℝ) * prob p x + ((1 - a : NNReal) : ℝ) * prob q x := by
  unfold prob
  have hsub : (1 - (a : ENNReal)).toReal = ((1 - a : NNReal) : ℝ) := by
    have h : ((1 - a : NNReal) : ENNReal) = 1 - (a : ENNReal) := by
      simp [ENNReal.coe_sub]
    rw [← h]
    exact ENNReal.coe_toReal (1 - a)
  rw [mix_apply]
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (p.apply_ne_top x))
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (q.apply_ne_top x))]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp [hsub]

theorem expectedValue_mix [Fintype Outcome]
    (u : Outcome → ℝ)
    (p q : Lottery Outcome) (a : NNReal) (ha : a ≤ 1) :
    expectedValue u (mix p q a ha) =
      (a : ℝ) * expectedValue u p +
        ((1 - a : NNReal) : ℝ) * expectedValue u q := by
  unfold expectedValue
  simp_rw [prob_mix]
  calc
    (∑ x : Outcome,
        ((a : ℝ) * prob p x + ((1 - a : NNReal) : ℝ) * prob q x) * u x)
        =
          ∑ x : Outcome,
            ((a : ℝ) * (prob p x * u x) +
              ((1 - a : NNReal) : ℝ) * (prob q x * u x)) := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            ring
    _ =
        (a : ℝ) * (∑ x : Outcome, prob p x * u x) +
          ((1 - a : NNReal) : ℝ) * (∑ x : Outcome, prob q x * u x) := by
        rw [Finset.sum_add_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum]

theorem expectedValue_degenerate [Fintype Outcome] [DecidableEq Outcome]
    (u : Outcome → ℝ) (x : Outcome) :
    expectedValue u (degenerate x) = u x := by
  unfold expectedValue prob degenerate
  rw [Finset.sum_eq_single x]
  · simp [PMF.pure_apply]
  · intro y _hy hne
    simp [PMF.pure_apply, hne]
  · intro hx
    exact False.elim (hx (Finset.mem_univ x))

/-! ## vNM preference axioms -/

/--
Independence: on a carrier of lotteries, mixing both sides with the same third
lottery preserves and reflects weak preference whenever the mixing weight is
strictly between zero and one.
-/
def VNMIndependent
    (P : Preference (Lottery Outcome))
    (S : Set (Lottery Outcome)) : Prop :=
  ∀ ⦃p q r : Lottery Outcome⦄,
    p ∈ S → q ∈ S → r ∈ S →
      ∀ (a : NNReal) (ha : a ≤ 1), 0 < a →
        (P.weakPref p q ↔ P.weakPref (mix p r a ha) (mix q r a ha))

/--
Archimedean/mixture continuity: if `p ≽ q ≽ r`, then `q` is indifferent to a
mixture of `p` and `r`.
-/
def VNMContinuous
    (P : Preference (Lottery Outcome))
    (S : Set (Lottery Outcome)) : Prop :=
  ∀ ⦃p q r : Lottery Outcome⦄,
    p ∈ S → q ∈ S → r ∈ S →
      P.weakPref p q → P.weakPref q r →
        ∃ (a : NNReal), ∃ (ha : a ≤ 1),
          P.Indiff (mix p r a ha) q

/-- The rationality plus mixture axioms used by the vNM utility theorem. -/
def VNMRational
    (P : Preference (Lottery Outcome))
    (S : Set (Lottery Outcome)) : Prop :=
  P.RationalOn S ∧ MixtureClosed S ∧ VNMIndependent P S ∧ VNMContinuous P S

/--
Expected-utility representation, abstracted as ordinary utility representation
on a carrier of lotteries.

Later finite-support specializations can identify `U` with the expectation of
an outcome utility index.  Keeping this definition separate avoids baking a
specific integrability or support assumption into the public API.
-/
def ExpectedUtilityRepresentsOn
    (P : Preference (Lottery Outcome))
    (S : Set (Lottery Outcome))
    (U : Lottery Outcome → ℝ) : Prop :=
  P.RepresentsOn S U

/--
Finite expected-utility representation by an outcome utility index.

This is the concrete representation form used in the vNM theorem.
-/
def ExpectedValueRepresentsOn [Fintype Outcome]
    (P : Preference (Lottery Outcome))
    (S : Set (Lottery Outcome))
    (u : Outcome → ℝ) : Prop :=
  ExpectedUtilityRepresentsOn P S (expectedValue u)

theorem expectedValue_generatedPref_representsOn [Fintype Outcome]
    (u : Outcome → ℝ) (S : Set (Lottery Outcome)) :
    ExpectedValueRepresentsOn
      (Utility.generatedPref (expectedValue u)) S u := by
  intro p q _hp _hq
  rfl

theorem expectedValue_generatedPref_independent [Fintype Outcome]
    (u : Outcome → ℝ) (S : Set (Lottery Outcome)) :
    VNMIndependent (Utility.generatedPref (expectedValue u)) S := by
  intro p q r _hp _hq _hr a ha hpos
  have haR : 0 < (a : ℝ) := by
    exact_mod_cast hpos
  simp [Utility.generatedPref, expectedValue_mix]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem expectedValue_generatedPref_continuous [Fintype Outcome]
    (u : Outcome → ℝ) (S : Set (Lottery Outcome)) :
    VNMContinuous (Utility.generatedPref (expectedValue u)) S := by
  intro p q r _hp _hq _hr hpq hqr
  let Up := expectedValue u p
  let Uq := expectedValue u q
  let Ur := expectedValue u r
  change Up ≥ Uq at hpq
  change Uq ≥ Ur at hqr
  by_cases hEq : Up = Ur
  · refine ⟨1, le_rfl, ?_⟩
    have hUq : Uq = Up := by
      nlinarith
    constructor
    · change expectedValue u (mix p r 1 le_rfl) ≥ Uq
      rw [expectedValue_mix]
      simp [Up, Uq, hUq]
    · change Uq ≥ expectedValue u (mix p r 1 le_rfl)
      rw [expectedValue_mix]
      simp [Up, Uq, hUq]
  · have hUrUp : Ur < Up := by
      have hle : Ur ≤ Up := by
        linarith
      exact lt_of_le_of_ne hle (Ne.symm hEq)
    let aR : ℝ := (Uq - Ur) / (Up - Ur)
    have haR_nonneg : 0 ≤ aR := by
      dsimp [aR]
      exact div_nonneg (by linarith) (by linarith)
    have haR_le_one : aR ≤ 1 := by
      dsimp [aR]
      rw [div_le_one (by linarith)]
      linarith
    let a : NNReal := Real.toNNReal aR
    have ha : a ≤ 1 := by
      dsimp [a]
      rw [Real.toNNReal_le_one]
      exact haR_le_one
    refine ⟨a, ha, ?_⟩
    have ha_coe : (a : ℝ) = aR := by
      exact Real.coe_toNNReal aR haR_nonneg
    have hsub_coe : ((1 - a : NNReal) : ℝ) = 1 - aR := by
      rw [NNReal.coe_sub ha, ha_coe]
      norm_num
    have hmix : expectedValue u (mix p r a ha) = Uq := by
      rw [expectedValue_mix]
      rw [ha_coe, hsub_coe]
      change aR * Up + (1 - aR) * Ur = Uq
      dsimp [aR]
      have hden_ne : Up - Ur ≠ 0 := by
        nlinarith
      field_simp [hden_ne]
      ring
    constructor
    · change expectedValue u (mix p r a ha) ≥ Uq
      rw [hmix]
    · change Uq ≥ expectedValue u (mix p r a ha)
      rw [hmix]

theorem expectedValue_generatedPref_vnmRational [Fintype Outcome]
    (u : Outcome → ℝ) {S : Set (Lottery Outcome)}
    (hS : MixtureClosed S) :
    VNMRational (Utility.generatedPref (expectedValue u)) S := by
  exact
    ⟨(Utility.generatedPref (expectedValue u)).rationalOn_of_representsOn
        (expectedValue_generatedPref_representsOn u S),
      hS,
      expectedValue_generatedPref_independent u S,
      expectedValue_generatedPref_continuous u S⟩

theorem rationalOn_of_vnmRational
    {P : Preference (Lottery Outcome)} {S : Set (Lottery Outcome)}
    (h : VNMRational P S) :
    P.RationalOn S :=
  h.1

theorem independent_of_vnmRational
    {P : Preference (Lottery Outcome)} {S : Set (Lottery Outcome)}
    (h : VNMRational P S) :
    VNMIndependent P S :=
  h.2.2.1

theorem continuous_of_vnmRational
    {P : Preference (Lottery Outcome)} {S : Set (Lottery Outcome)}
    (h : VNMRational P S) :
    VNMContinuous P S :=
  h.2.2.2

theorem mixtureClosed_of_vnmRational
    {P : Preference (Lottery Outcome)} {S : Set (Lottery Outcome)}
    (h : VNMRational P S) :
    MixtureClosed S :=
  h.2.1

theorem rationalOn_of_expectedUtilityRepresentsOn
    {P : Preference (Lottery Outcome)} {S : Set (Lottery Outcome)}
    {U : Lottery Outcome → ℝ}
    (hRep : ExpectedUtilityRepresentsOn P S U) :
    P.RationalOn S :=
  P.rationalOn_of_representsOn hRep

theorem vnmIndependent_of_expectedValueRepresentsOn [Fintype Outcome]
    {P : Preference (Lottery Outcome)}
    {S : Set (Lottery Outcome)}
    {u : Outcome → ℝ}
    (hS : MixtureClosed S)
    (hRep : ExpectedValueRepresentsOn P S u) :
    VNMIndependent P S := by
  intro p q r hp hq hr a ha hpos
  have haR : 0 < (a : ℝ) := by
    exact_mod_cast hpos
  have hpr : mix p r a ha ∈ S := hS hp hr a ha
  have hqr : mix q r a ha ∈ S := hS hq hr a ha
  rw [hRep hp hq, hRep hpr hqr]
  rw [expectedValue_mix, expectedValue_mix]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem vnmContinuous_of_expectedValueRepresentsOn [Fintype Outcome]
    {P : Preference (Lottery Outcome)}
    {S : Set (Lottery Outcome)}
    {u : Outcome → ℝ}
    (hS : MixtureClosed S)
    (hRep : ExpectedValueRepresentsOn P S u) :
    VNMContinuous P S := by
  intro p q r hp hq hr hpq hqr
  let Up := expectedValue u p
  let Uq := expectedValue u q
  let Ur := expectedValue u r
  have hpqU : Up ≥ Uq := by
    change expectedValue u p ≥ expectedValue u q
    exact (hRep hp hq).mp hpq
  have hqrU : Uq ≥ Ur := by
    change expectedValue u q ≥ expectedValue u r
    exact (hRep hq hr).mp hqr
  by_cases hEq : Up = Ur
  · refine ⟨1, le_rfl, ?_⟩
    have hUq : Uq = Up := by
      nlinarith
    have hmixS : mix p r 1 le_rfl ∈ S := hS hp hr 1 le_rfl
    have hmix : expectedValue u (mix p r 1 le_rfl) = Uq := by
      rw [expectedValue_mix]
      simp [Up, Uq, hUq]
    constructor
    · exact (hRep hmixS hq).mpr (by rw [hmix])
    · exact (hRep hq hmixS).mpr (by rw [hmix])
  · have hUrUp : Ur < Up := by
      have hle : Ur ≤ Up := by
        linarith
      exact lt_of_le_of_ne hle (Ne.symm hEq)
    let aR : ℝ := (Uq - Ur) / (Up - Ur)
    have haR_nonneg : 0 ≤ aR := by
      dsimp [aR]
      exact div_nonneg (by linarith) (by linarith)
    have haR_le_one : aR ≤ 1 := by
      dsimp [aR]
      rw [div_le_one (by linarith)]
      linarith
    let a : NNReal := Real.toNNReal aR
    have ha : a ≤ 1 := by
      dsimp [a]
      rw [Real.toNNReal_le_one]
      exact haR_le_one
    refine ⟨a, ha, ?_⟩
    have hmixS : mix p r a ha ∈ S := hS hp hr a ha
    have ha_coe : (a : ℝ) = aR := by
      exact Real.coe_toNNReal aR haR_nonneg
    have hsub_coe : ((1 - a : NNReal) : ℝ) = 1 - aR := by
      rw [NNReal.coe_sub ha, ha_coe]
      norm_num
    have hmix : expectedValue u (mix p r a ha) = Uq := by
      rw [expectedValue_mix]
      rw [ha_coe, hsub_coe]
      change aR * Up + (1 - aR) * Ur = Uq
      dsimp [aR]
      have hden_ne : Up - Ur ≠ 0 := by
        nlinarith
      field_simp [hden_ne]
      ring
    constructor
    · exact (hRep hmixS hq).mpr (by rw [hmix])
    · exact (hRep hq hmixS).mpr (by rw [hmix])

theorem vnmRational_of_expectedValueRepresentsOn [Fintype Outcome]
    {P : Preference (Lottery Outcome)}
    {S : Set (Lottery Outcome)}
    {u : Outcome → ℝ}
    (hS : MixtureClosed S)
    (hRep : ExpectedValueRepresentsOn P S u) :
    VNMRational P S :=
  ⟨rationalOn_of_expectedUtilityRepresentsOn hRep,
    hS,
    vnmIndependent_of_expectedValueRepresentsOn hS hRep,
    vnmContinuous_of_expectedValueRepresentsOn hS hRep⟩

end ExpectedUtility
end GameTheory
end EcoLean
