import EcoLean.GameTheory.ExpectedUtility.Lottery

/-!
# The forward vNM construction

This file contains the constructive core of the forward direction of the
von Neumann-Morgenstern utility theorem.

Given best and worst lotteries bounding a carrier, mixture continuity assigns
to every lottery a certainty-equivalent weight: the lottery is indifferent to a
mixture of the best and worst lotteries with that weight.  The remaining
representation proof obligations are isolated as two explicit predicates:

* the selected weights represent the preference order;
* the selected weight of a lottery is affine in its outcome probabilities.

Those are the hard induction/independence parts of the AFP proof.  Keeping them
as named obligations gives later files a precise target rather than a vague
placeholder theorem.
-/

universe u

namespace EcoLean
namespace GameTheory
namespace ExpectedUtility

variable {Outcome : Type u}

/-! ## Best and worst degenerate lotteries -/

/--
The preference over outcomes induced by comparing their degenerate lotteries.
-/
noncomputable def degeneratePreference
    (P : Preference (Lottery Outcome)) : Preference Outcome where
  weakPref x y := P.weakPref (degenerate x) (degenerate y)

theorem degeneratePreference_complete
    {P : Preference (Lottery Outcome)}
    {S : Set (Lottery Outcome)}
    (hRat : P.RationalOn S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S) :
    (degeneratePreference P).Complete := by
  intro x y
  exact hRat.1 (hDegenerate x) (hDegenerate y)

theorem degeneratePreference_transitive
    {P : Preference (Lottery Outcome)}
    {S : Set (Lottery Outcome)}
    (hRat : P.RationalOn S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S) :
    (degeneratePreference P).Transitive := by
  intro x y z hxy hyz
  exact hRat.2 (hDegenerate x) (hDegenerate y) (hDegenerate z) hxy hyz

theorem exists_best_degenerate
    [Fintype Outcome] [Nonempty Outcome]
    {P : Preference (Lottery Outcome)}
    {S : Set (Lottery Outcome)}
    (hRat : P.RationalOn S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S) :
    ∃ x : Outcome, ∀ y : Outcome,
      P.weakPref (degenerate x) (degenerate y) := by
  let DP := degeneratePreference P
  have hC : DP.Complete := degeneratePreference_complete hRat hDegenerate
  have hT : DP.Transitive := degeneratePreference_transitive hRat hDegenerate
  rcases DP.exists_best_of_finite_of_complete_transitive
      hC hT (A := Set.univ) Set.finite_univ Set.univ_nonempty with
    ⟨x, _hx, hxbest⟩
  exact ⟨x, fun y => hxbest y trivial⟩

theorem exists_worst_degenerate
    [Fintype Outcome] [Nonempty Outcome]
    {P : Preference (Lottery Outcome)}
    {S : Set (Lottery Outcome)}
    (hRat : P.RationalOn S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S) :
    ∃ x : Outcome, ∀ y : Outcome,
      P.weakPref (degenerate y) (degenerate x) := by
  let DP := degeneratePreference P
  have hC : DP.Complete := degeneratePreference_complete hRat hDegenerate
  have hT : DP.Transitive := degeneratePreference_transitive hRat hDegenerate
  let DPdual : Preference Outcome := { weakPref := fun x y => DP.weakPref y x }
  have hCdual : DPdual.Complete := by
    intro x y
    exact hC y x
  have hTdual : DPdual.Transitive := by
    intro x y z hxy hyz
    exact hT z y x hyz hxy
  rcases Preference.exists_best_of_finite_of_complete_transitive
      (P := DPdual) hCdual hTdual (A := Set.univ)
      Set.finite_univ Set.univ_nonempty with
    ⟨x, _hx, hxworst⟩
  exact ⟨x, fun y => hxworst y trivial⟩

/--
Chosen best and worst outcomes among degenerate lotteries.
-/
structure DegenerateBounds
    (P : Preference (Lottery Outcome))
    (S : Set (Lottery Outcome)) where
  bestOutcome : Outcome
  worstOutcome : Outcome
  best_is_best : ∀ y : Outcome,
    P.weakPref (degenerate bestOutcome) (degenerate y)
  worst_is_worst : ∀ y : Outcome,
    P.weakPref (degenerate y) (degenerate worstOutcome)

namespace DegenerateBounds

variable {P : Preference (Lottery Outcome)}
variable {S : Set (Lottery Outcome)}

noncomputable def best (B : DegenerateBounds P S) : Lottery Outcome :=
  degenerate B.bestOutcome

noncomputable def worst (B : DegenerateBounds P S) : Lottery Outcome :=
  degenerate B.worstOutcome

theorem best_weakPref_worst (B : DegenerateBounds P S) :
    P.weakPref B.best B.worst :=
  B.best_is_best B.worstOutcome

theorem best_mem
    (B : DegenerateBounds P S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S) :
    B.best ∈ S :=
  hDegenerate B.bestOutcome

theorem worst_mem
    (B : DegenerateBounds P S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S) :
    B.worst ∈ S :=
  hDegenerate B.worstOutcome

/--
The extra "step 1" obligation from Parsert/Kaliszyk: degenerate best and worst
outcomes must bound every lottery in the carrier, not merely every degenerate
lottery.
-/
def BoundsAllLotteries (B : DegenerateBounds P S) : Prop :=
  ∀ p : Lottery Outcome, p ∈ S →
    P.weakPref B.best p ∧ P.weakPref p B.worst

theorem bounds_mixtureGenerated
    (B : DegenerateBounds P S)
    (hRat : P.RationalOn S)
    (hIndependent : VNMIndependent P S)
    (hMixtureClosed : MixtureClosed S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S)
    {p : Lottery Outcome}
    (hpGenerated : MixtureGenerated (Set.univ : Set Outcome) p) :
    P.weakPref B.best p ∧ P.weakPref p B.worst := by
  have hBestS : B.best ∈ S := B.best_mem hDegenerate
  have hWorstS : B.worst ∈ S := B.worst_mem hDegenerate
  induction hpGenerated with
  | ofOutcome hx =>
      constructor
      · exact B.best_is_best _
      · exact B.worst_is_worst _
  | mix hp hq a ha ihp ihq =>
      rename_i p0 q0
      have hpS : p0 ∈ S :=
        hp.mem_of_degenerate_mem_of_mixtureClosed
          (fun x _hx => hDegenerate x) hMixtureClosed
      have hqS : q0 ∈ S :=
        hq.mem_of_degenerate_mem_of_mixtureClosed
          (fun x _hx => hDegenerate x) hMixtureClosed
      have hMixBestQS : mix B.best q0 a ha ∈ S :=
        hMixtureClosed hBestS hqS a ha
      have hMixPQS : mix p0 q0 a ha ∈ S :=
        hMixtureClosed hpS hqS a ha
      have hMixWorstQS : mix B.worst q0 a ha ∈ S :=
        hMixtureClosed hWorstS hqS a ha
      constructor
      · have hBestPrefMixBestQ :
            P.weakPref B.best (mix B.best q0 a ha) := by
          have h :=
            weakPref_mix_right_of_independent hRat hIndependent
              hBestS hqS hBestS ihq.1 a ha
          simpa using h
        have hMixBestQPrefMixPQ :
            P.weakPref (mix B.best q0 a ha) (mix p0 q0 a ha) :=
          weakPref_mix_left_of_independent hRat hIndependent
            hBestS hpS hqS ihp.1 a ha
        exact hRat.2 hBestS hMixBestQS hMixPQS
          hBestPrefMixBestQ hMixBestQPrefMixPQ
      · have hMixPQPrefMixWorstQ :
            P.weakPref (mix p0 q0 a ha) (mix B.worst q0 a ha) :=
          weakPref_mix_left_of_independent hRat hIndependent
            hpS hWorstS hqS ihp.2 a ha
        have hMixWorstQPrefWorst :
            P.weakPref (mix B.worst q0 a ha) B.worst := by
          have h :=
            weakPref_mix_right_of_independent hRat hIndependent
              hqS hWorstS hWorstS ihq.2 a ha
          simpa using h
        exact hRat.2 hMixPQS hMixWorstQS hWorstS
          hMixPQPrefMixWorstQ hMixWorstQPrefWorst

theorem boundsAllLotteries_of_forall_mixtureGenerated
    (B : DegenerateBounds P S)
    (hRat : P.RationalOn S)
    (hIndependent : VNMIndependent P S)
    (hMixtureClosed : MixtureClosed S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S)
    (hGenerated : ∀ p : Lottery Outcome, p ∈ S →
      MixtureGenerated (Set.univ : Set Outcome) p) :
    B.BoundsAllLotteries := by
  intro p hp
  exact B.bounds_mixtureGenerated hRat hIndependent hMixtureClosed
    hDegenerate (hGenerated p hp)

end DegenerateBounds

theorem exists_degenerateBounds
    [Fintype Outcome] [Nonempty Outcome]
    {P : Preference (Lottery Outcome)}
    {S : Set (Lottery Outcome)}
    (hRat : P.RationalOn S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S) :
    ∃ _ : DegenerateBounds P S, True := by
  rcases exists_best_degenerate hRat hDegenerate with ⟨best, hbest⟩
  rcases exists_worst_degenerate hRat hDegenerate with ⟨worst, hworst⟩
  exact ⟨⟨best, worst, hbest, hworst⟩, trivial⟩

theorem exists_degenerateBounds_boundsAllLotteries_of_vnmRational_generated
    [Fintype Outcome] [Nonempty Outcome]
    {P : Preference (Lottery Outcome)}
    {S : Set (Lottery Outcome)}
    (hVNM : VNMRational P S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S)
    (hGenerated : ∀ p : Lottery Outcome, p ∈ S →
      MixtureGenerated (Set.univ : Set Outcome) p) :
    ∃ B : DegenerateBounds P S, B.BoundsAllLotteries := by
  rcases exists_degenerateBounds
      (rationalOn_of_vnmRational hVNM) hDegenerate with
    ⟨B, _⟩
  exact
    ⟨B, B.boundsAllLotteries_of_forall_mixtureGenerated
      (rationalOn_of_vnmRational hVNM)
      (independent_of_vnmRational hVNM)
      (mixtureClosed_of_vnmRational hVNM)
      hDegenerate hGenerated⟩

theorem expectedValueRepresentsOn_const_zero_of_all_indifferent
    [Fintype Outcome]
    {P : Preference (Lottery Outcome)}
    {S : Set (Lottery Outcome)}
    (hAll : ∀ p : Lottery Outcome, p ∈ S →
      ∀ q : Lottery Outcome, q ∈ S → P.Indiff p q) :
    ExpectedValueRepresentsOn P S (fun _ : Outcome => 0) := by
  intro p q hp hq
  constructor
  · intro _hpq
    simp [expectedValue]
  · intro _hge
    exact (hAll p hp q hq).1

/--
Data needed to run the certainty-equivalent part of the vNM construction.

`best` and `worst` bound all lotteries in `S`, and mixture continuity supplies
an indifference between every lottery in `S` and some mixture of those bounds.
-/
structure VNMConstructionData
    (P : Preference (Lottery Outcome))
    (S : Set (Lottery Outcome)) where
  best : Lottery Outcome
  worst : Lottery Outcome
  best_mem : best ∈ S
  worst_mem : worst ∈ S
  best_weakPref : ∀ p : Lottery Outcome, p ∈ S → P.weakPref best p
  weakPref_worst : ∀ p : Lottery Outcome, p ∈ S → P.weakPref p worst
  continuous : VNMContinuous P S

noncomputable def VNMConstructionData.ofDegenerateBounds
    {P : Preference (Lottery Outcome)}
    {S : Set (Lottery Outcome)}
    (B : DegenerateBounds P S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S)
    (hBounds : B.BoundsAllLotteries)
    (hContinuous : VNMContinuous P S) :
    VNMConstructionData P S where
  best := B.best
  worst := B.worst
  best_mem := B.best_mem hDegenerate
  worst_mem := B.worst_mem hDegenerate
  best_weakPref := fun p hp => (hBounds p hp).1
  weakPref_worst := fun p hp => (hBounds p hp).2
  continuous := hContinuous

theorem exists_constructionData_of_vnmRational_generated
    [Fintype Outcome] [Nonempty Outcome]
    {P : Preference (Lottery Outcome)}
    {S : Set (Lottery Outcome)}
    (hVNM : VNMRational P S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S)
    (hGenerated : ∀ p : Lottery Outcome, p ∈ S →
      MixtureGenerated (Set.univ : Set Outcome) p) :
    ∃ _ : VNMConstructionData P S, True := by
  rcases exists_degenerateBounds_boundsAllLotteries_of_vnmRational_generated
      hVNM hDegenerate hGenerated with
    ⟨B, hBounds⟩
  exact
    ⟨VNMConstructionData.ofDegenerateBounds B hDegenerate hBounds
      (continuous_of_vnmRational hVNM), trivial⟩

namespace VNMConstructionData

variable {P : Preference (Lottery Outcome)}
variable {S : Set (Lottery Outcome)}

theorem all_indifferent_of_best_indiff_worst
    (D : VNMConstructionData P S)
    (hRat : P.RationalOn S)
    (hBestWorst : P.Indiff D.best D.worst) :
    ∀ p : Lottery Outcome, p ∈ S →
      ∀ q : Lottery Outcome, q ∈ S → P.Indiff p q := by
  intro p hp q hq
  have hT := hRat.2
  have hWorstPrefP : P.weakPref D.worst p :=
    hT D.worst_mem D.best_mem hp hBestWorst.2 (D.best_weakPref p hp)
  have hWorstPrefQ : P.weakPref D.worst q :=
    hT D.worst_mem D.best_mem hq hBestWorst.2 (D.best_weakPref q hq)
  constructor
  · exact hT hp D.worst_mem hq (D.weakPref_worst p hp) hWorstPrefQ
  · exact hT hq D.worst_mem hp (D.weakPref_worst q hq) hWorstPrefP

theorem expectedValueRepresentsOn_const_zero_of_best_indiff_worst
    [Fintype Outcome]
    (D : VNMConstructionData P S)
    (hRat : P.RationalOn S)
    (hBestWorst : P.Indiff D.best D.worst) :
    ExpectedValueRepresentsOn P S (fun _ : Outcome => 0) :=
  expectedValueRepresentsOn_const_zero_of_all_indifferent
    (D.all_indifferent_of_best_indiff_worst hRat hBestWorst)

/-- The existential statement supplied by mixture continuity for `p`. -/
theorem exists_weight
    (D : VNMConstructionData P S)
    (p : Lottery Outcome) (hp : p ∈ S) :
    ∃ (a : NNReal), ∃ (ha : a ≤ 1),
      P.Indiff (mix D.best D.worst a ha) p := by
  exact D.continuous D.best_mem hp D.worst_mem
    (D.best_weakPref p hp) (D.weakPref_worst p hp)

/--
The selected certainty-equivalent weight of `p`: a probability of the best
lottery in a mixture with the worst lottery.
-/
noncomputable def weight
    (D : VNMConstructionData P S)
    (p : Lottery Outcome) (hp : p ∈ S) : NNReal :=
  Classical.choose (D.exists_weight p hp)

theorem weight_mem_congr
    (D : VNMConstructionData P S)
    (p : Lottery Outcome) (hp hp' : p ∈ S) :
    D.weight p hp = D.weight p hp' := by
  unfold weight
  congr

/-- The selected certainty-equivalent weight lies in `[0, 1]`. -/
noncomputable def weight_le_one
    (D : VNMConstructionData P S)
    (p : Lottery Outcome) (hp : p ∈ S) :
    D.weight p hp ≤ 1 :=
  Classical.choose (Classical.choose_spec (D.exists_weight p hp))

/--
The selected best/worst mixture is indifferent to the original lottery.
-/
theorem mix_weight_indiff
    (D : VNMConstructionData P S)
    (p : Lottery Outcome) (hp : p ∈ S) :
    P.Indiff
      (mix D.best D.worst (D.weight p hp) (D.weight_le_one p hp)) p :=
  Classical.choose_spec (Classical.choose_spec (D.exists_weight p hp))

/--
The outcome utility index induced by the certainty-equivalent construction.

Each outcome receives the selected weight of its degenerate lottery.
-/
noncomputable def outcomeUtility
    (D : VNMConstructionData P S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S)
    (x : Outcome) : ℝ :=
  D.weight (degenerate x) (hDegenerate x)

/--
The AFP proof separates the genuinely strict best/worst case from the
degenerate case where all lotteries are indifferent.  This utility index makes
that split explicit: it is constant in the degenerate case and otherwise uses
the certainty-equivalent weights of degenerate lotteries.
-/
noncomputable def generalOutcomeUtility
    (D : VNMConstructionData P S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S) :
    Outcome → ℝ := by
  classical
  exact
    if P.Indiff D.best D.worst then
      fun _ => 0
    else
      D.outcomeUtility hDegenerate

theorem degenerate_mix_weight_indiff
    (D : VNMConstructionData P S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S)
    (x : Outcome) :
    P.Indiff
      (mix D.best D.worst
        (D.weight (degenerate x) (hDegenerate x))
        (D.weight_le_one (degenerate x) (hDegenerate x)))
      (degenerate x) :=
  D.mix_weight_indiff (degenerate x) (hDegenerate x)

/--
The selected certainty-equivalent weights represent the preference order on
`S`.

This is one of the two remaining hard proof obligations in the full forward
vNM theorem.
-/
def WeightRepresents
    (D : VNMConstructionData P S) : Prop :=
  ∀ ⦃p q : Lottery Outcome⦄, (hp : p ∈ S) → (hq : q ∈ S) →
    (P.weakPref p q ↔ (D.weight p hp : ℝ) ≥ (D.weight q hq : ℝ))

/--
The selected best/worst mixture line is ordered exactly by its probability of
the best lottery.

This is the one-dimensional strict-case core of the forward vNM proof.
-/
def BestWorstMixtureOrder
    (D : VNMConstructionData P S) : Prop :=
  ∀ (a : NNReal) (ha : a ≤ 1) (b : NNReal) (hb : b ≤ 1),
    (P.weakPref (mix D.best D.worst a ha) (mix D.best D.worst b hb) ↔
      (a : ℝ) ≥ (b : ℝ))

theorem weightRepresents_of_bestWorstMixtureOrder
    (D : VNMConstructionData P S)
    (hRat : P.RationalOn S)
    (hS : MixtureClosed S)
    (hOrder : D.BestWorstMixtureOrder) :
    D.WeightRepresents := by
  intro p q hp hq
  let wp := D.weight p hp
  let wq := D.weight q hq
  let hwp := D.weight_le_one p hp
  let hwq := D.weight_le_one q hq
  let mp := mix D.best D.worst wp hwp
  let mq := mix D.best D.worst wq hwq
  have hmpS : mp ∈ S := hS D.best_mem D.worst_mem wp hwp
  have hmqS : mq ∈ S := hS D.best_mem D.worst_mem wq hwq
  have hmpIndiff : P.Indiff mp p := D.mix_weight_indiff p hp
  have hmqIndiff : P.Indiff mq q := D.mix_weight_indiff q hq
  have hOrderWeights :
      P.weakPref mp mq ↔ (wp : ℝ) ≥ (wq : ℝ) :=
    hOrder wp hwp wq hwq
  constructor
  · intro hpq
    exact hOrderWeights.mp
      (hRat.2 hmpS hq hmqS
        (hRat.2 hmpS hp hq hmpIndiff.1 hpq)
        hmqIndiff.2)
  · intro hge
    have hmpmq : P.weakPref mp mq := hOrderWeights.mpr hge
    exact hRat.2 hp hmqS hq
      (hRat.2 hp hmpS hmqS hmpIndiff.2 hmpmq)
      hmqIndiff.1

/--
The selected weight is affine in lottery probabilities with respect to an
outcome utility index.

For the canonical construction, `u` should be `D.outcomeUtility hDegenerate`.
This is the other hard proof obligation in the full forward vNM theorem.
-/
def WeightAffine [Fintype Outcome]
    (D : VNMConstructionData P S)
    (u : Outcome → ℝ) : Prop :=
  ∀ (p : Lottery Outcome) (hp : p ∈ S),
    (D.weight p hp : ℝ) = expectedValue u p

/--
Linearity of the selected certainty-equivalent weight over binary mixtures.

This corresponds to Parsert/Kaliszyk's `my-U-is-linear-function`; once this is
available, `MixtureGenerated` induction turns it into finite expected-value
linearity.
-/
def WeightMixLinear
    (D : VNMConstructionData P S)
    (hS : MixtureClosed S) : Prop :=
  ∀ ⦃p q : Lottery Outcome⦄, (hp : p ∈ S) → (hq : q ∈ S) →
    ∀ (a : NNReal) (ha : a ≤ 1),
      (D.weight (mix p q a ha) (hS hp hq a ha) : ℝ) =
        (a : ℝ) * (D.weight p hp : ℝ) +
          ((1 - a : NNReal) : ℝ) * (D.weight q hq : ℝ)

theorem weightAffine_of_weightMixLinear_on_mixtureGenerated
    [Fintype Outcome]
    (D : VNMConstructionData P S)
    (hS : MixtureClosed S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S)
    (hLinear : D.WeightMixLinear hS)
    {p : Lottery Outcome}
    (hpGenerated : MixtureGenerated (Set.univ : Set Outcome) p) :
    ∀ hp : p ∈ S,
      (D.weight p hp : ℝ) = expectedValue (D.outcomeUtility hDegenerate) p := by
  classical
  induction hpGenerated with
  | ofOutcome hx =>
      intro hp
      rw [expectedValue_degenerate]
      change (D.weight (degenerate _) hp : ℝ) =
        (D.weight (degenerate _) (hDegenerate _) : ℝ)
      exact_mod_cast D.weight_mem_congr (degenerate _) hp (hDegenerate _)
  | mix hp hq a ha ihp ihq =>
      rename_i p0 q0
      intro hmixS
      have hpS : p0 ∈ S :=
        hp.mem_of_degenerate_mem_of_mixtureClosed
          (fun x _hx => hDegenerate x) hS
      have hqS : q0 ∈ S :=
        hq.mem_of_degenerate_mem_of_mixtureClosed
          (fun x _hx => hDegenerate x) hS
      have hmixS' : mix p0 q0 a ha ∈ S :=
        hS hpS hqS a ha
      calc
        (D.weight (mix p0 q0 a ha) hmixS : ℝ)
            = (D.weight (mix p0 q0 a ha) hmixS' : ℝ) := by
                exact_mod_cast
                  D.weight_mem_congr (mix p0 q0 a ha) hmixS hmixS'
        _ =
            (a : ℝ) * (D.weight p0 hpS : ℝ) +
              ((1 - a : NNReal) : ℝ) * (D.weight q0 hqS : ℝ) :=
                hLinear hpS hqS a ha
        _ =
            (a : ℝ) * expectedValue (D.outcomeUtility hDegenerate) p0 +
              ((1 - a : NNReal) : ℝ) *
                expectedValue (D.outcomeUtility hDegenerate) q0 := by
                rw [ihp hpS, ihq hqS]
        _ = expectedValue (D.outcomeUtility hDegenerate) (mix p0 q0 a ha) :=
            (expectedValue_mix (D.outcomeUtility hDegenerate) p0 q0 a ha).symm

theorem weightAffine_of_weightMixLinear
    [Fintype Outcome]
    (D : VNMConstructionData P S)
    (hS : MixtureClosed S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S)
    (hGenerated : ∀ p : Lottery Outcome, p ∈ S →
      MixtureGenerated (Set.univ : Set Outcome) p)
    (hLinear : D.WeightMixLinear hS) :
    D.WeightAffine (D.outcomeUtility hDegenerate) := by
  intro p hp
  exact D.weightAffine_of_weightMixLinear_on_mixtureGenerated
    hS hDegenerate hLinear (hGenerated p hp) hp

/--
Once the certainty-equivalent weights are known to represent preferences and
to be affine in probabilities, they produce a finite expected-utility
representation.
-/
theorem expectedValueRepresentsOn_of_weightRepresents_of_weightAffine
    [Fintype Outcome]
    (D : VNMConstructionData P S)
    (u : Outcome → ℝ)
    (hRep : D.WeightRepresents)
    (hAff : D.WeightAffine u) :
    ExpectedValueRepresentsOn P S u := by
  intro p q hp hq
  rw [← hAff p hp, ← hAff q hq]
  exact hRep hp hq

/--
The same bridge specialized to the canonical outcome utility generated by the
selected weights of degenerate lotteries.
-/
theorem expectedValueRepresentsOn_of_constructedUtility
    [Fintype Outcome]
    (D : VNMConstructionData P S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S)
    (hRep : D.WeightRepresents)
    (hAff : D.WeightAffine (D.outcomeUtility hDegenerate)) :
    ExpectedValueRepresentsOn P S (D.outcomeUtility hDegenerate) :=
  D.expectedValueRepresentsOn_of_weightRepresents_of_weightAffine
    (D.outcomeUtility hDegenerate) hRep hAff

/--
Existence form of the forward bridge: once the two remaining AFP-style proof
obligations for the selected certainty-equivalent weights are discharged, the
constructed outcome utility index gives an expected-utility representation.
-/
theorem exists_expectedValueRepresentsOn_of_constructedUtility
    [Fintype Outcome]
    (D : VNMConstructionData P S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S)
    (hRep : D.WeightRepresents)
    (hAff : D.WeightAffine (D.outcomeUtility hDegenerate)) :
    ∃ u : Outcome → ℝ, ExpectedValueRepresentsOn P S u :=
  ⟨D.outcomeUtility hDegenerate,
    D.expectedValueRepresentsOn_of_constructedUtility hDegenerate hRep hAff⟩

/--
Single-entry forward bridge matching Parsert/Kaliszyk's `general-U` split.

The degenerate best/worst case is fully discharged here.  In the strict case,
the caller supplies the two remaining AFP-style obligations for the constructed
certainty-equivalent weights.
-/
theorem expectedValueRepresentsOn_of_generalOutcomeUtility
    [Fintype Outcome]
    (D : VNMConstructionData P S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S)
    (hRat : P.RationalOn S)
    (hRep : ¬ P.Indiff D.best D.worst → D.WeightRepresents)
    (hAff : ¬ P.Indiff D.best D.worst →
      D.WeightAffine (D.outcomeUtility hDegenerate)) :
    ExpectedValueRepresentsOn P S (D.generalOutcomeUtility hDegenerate) := by
  by_cases hBestWorst : P.Indiff D.best D.worst
  · have hConst :
        ExpectedValueRepresentsOn P S (fun _ : Outcome => 0) :=
      D.expectedValueRepresentsOn_const_zero_of_best_indiff_worst hRat hBestWorst
    simpa [generalOutcomeUtility, hBestWorst] using hConst
  · have hConstructed :
        ExpectedValueRepresentsOn P S (D.outcomeUtility hDegenerate) :=
      D.expectedValueRepresentsOn_of_constructedUtility
        hDegenerate (hRep hBestWorst) (hAff hBestWorst)
    simpa [generalOutcomeUtility, hBestWorst] using hConstructed

theorem expectedValueRepresentsOn_of_generalOutcomeUtility_of_weightMixLinear
    [Fintype Outcome]
    (D : VNMConstructionData P S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S)
    (hRat : P.RationalOn S)
    (hS : MixtureClosed S)
    (hGenerated : ∀ p : Lottery Outcome, p ∈ S →
      MixtureGenerated (Set.univ : Set Outcome) p)
    (hRep : ¬ P.Indiff D.best D.worst → D.WeightRepresents)
    (hLinear : ¬ P.Indiff D.best D.worst → D.WeightMixLinear hS) :
    ExpectedValueRepresentsOn P S (D.generalOutcomeUtility hDegenerate) :=
  D.expectedValueRepresentsOn_of_generalOutcomeUtility hDegenerate hRat hRep
    (fun hStrict =>
      D.weightAffine_of_weightMixLinear hS hDegenerate hGenerated
        (hLinear hStrict))

theorem expectedValueRepresentsOn_of_generalOutcomeUtility_of_mixOrder_and_weightMixLinear
    [Fintype Outcome]
    (D : VNMConstructionData P S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S)
    (hRat : P.RationalOn S)
    (hS : MixtureClosed S)
    (hGenerated : ∀ p : Lottery Outcome, p ∈ S →
      MixtureGenerated (Set.univ : Set Outcome) p)
    (hOrder : ¬ P.Indiff D.best D.worst → D.BestWorstMixtureOrder)
    (hLinear : ¬ P.Indiff D.best D.worst → D.WeightMixLinear hS) :
    ExpectedValueRepresentsOn P S (D.generalOutcomeUtility hDegenerate) :=
  D.expectedValueRepresentsOn_of_generalOutcomeUtility_of_weightMixLinear
    hDegenerate hRat hS hGenerated
    (fun hStrict =>
      D.weightRepresents_of_bestWorstMixtureOrder hRat hS (hOrder hStrict))
    hLinear

end VNMConstructionData

theorem exists_expectedValueRepresentsOn_of_vnmRational_generated
    [Fintype Outcome] [Nonempty Outcome]
    {P : Preference (Lottery Outcome)}
    {S : Set (Lottery Outcome)}
    (hVNM : VNMRational P S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S)
    (hGenerated : ∀ p : Lottery Outcome, p ∈ S →
      MixtureGenerated (Set.univ : Set Outcome) p)
    (hRep : ∀ D : VNMConstructionData P S,
      ¬ P.Indiff D.best D.worst → D.WeightRepresents)
    (hLinear : ∀ D : VNMConstructionData P S,
      ¬ P.Indiff D.best D.worst →
        D.WeightMixLinear (mixtureClosed_of_vnmRational hVNM)) :
    ∃ u : Outcome → ℝ, ExpectedValueRepresentsOn P S u := by
  rcases exists_constructionData_of_vnmRational_generated
      hVNM hDegenerate hGenerated with
    ⟨D, _⟩
  exact
    ⟨D.generalOutcomeUtility hDegenerate,
      D.expectedValueRepresentsOn_of_generalOutcomeUtility_of_weightMixLinear
        hDegenerate
        (rationalOn_of_vnmRational hVNM)
        (mixtureClosed_of_vnmRational hVNM)
        hGenerated
        (hRep D)
        (hLinear D)⟩

theorem exists_expectedValueRepresentsOn_of_vnmRational_generated_of_mixOrder
    [Fintype Outcome] [Nonempty Outcome]
    {P : Preference (Lottery Outcome)}
    {S : Set (Lottery Outcome)}
    (hVNM : VNMRational P S)
    (hDegenerate : ∀ x : Outcome, degenerate x ∈ S)
    (hGenerated : ∀ p : Lottery Outcome, p ∈ S →
      MixtureGenerated (Set.univ : Set Outcome) p)
    (hOrder : ∀ D : VNMConstructionData P S,
      ¬ P.Indiff D.best D.worst → D.BestWorstMixtureOrder)
    (hLinear : ∀ D : VNMConstructionData P S,
      ¬ P.Indiff D.best D.worst →
        D.WeightMixLinear (mixtureClosed_of_vnmRational hVNM)) :
    ∃ u : Outcome → ℝ, ExpectedValueRepresentsOn P S u := by
  rcases exists_constructionData_of_vnmRational_generated
      hVNM hDegenerate hGenerated with
    ⟨D, _⟩
  exact
    ⟨D.generalOutcomeUtility hDegenerate,
      D.expectedValueRepresentsOn_of_generalOutcomeUtility_of_mixOrder_and_weightMixLinear
        hDegenerate
        (rationalOn_of_vnmRational hVNM)
        (mixtureClosed_of_vnmRational hVNM)
        hGenerated
        (hOrder D)
        (hLinear D)⟩

theorem exists_expectedValueRepresentsOn_of_vnmRational_generatedLotteries_of_mixOrder
    [Fintype Outcome] [Nonempty Outcome]
    {P : Preference (Lottery Outcome)}
    (hVNM : VNMRational P (GeneratedLotteries (Set.univ : Set Outcome)))
    (hOrder : ∀ D : VNMConstructionData P (GeneratedLotteries (Set.univ : Set Outcome)),
      ¬ P.Indiff D.best D.worst → D.BestWorstMixtureOrder)
    (hLinear : ∀ D : VNMConstructionData P (GeneratedLotteries (Set.univ : Set Outcome)),
      ¬ P.Indiff D.best D.worst →
        D.WeightMixLinear (mixtureClosed_of_vnmRational hVNM)) :
    ∃ u : Outcome → ℝ,
      ExpectedValueRepresentsOn P (GeneratedLotteries (Set.univ : Set Outcome)) u :=
  exists_expectedValueRepresentsOn_of_vnmRational_generated_of_mixOrder
    hVNM
    (fun x => MixtureGenerated.ofOutcome (Set.mem_univ x))
    (fun _ hp => hp)
    hOrder
    hLinear

end ExpectedUtility
end GameTheory
end EcoLean
