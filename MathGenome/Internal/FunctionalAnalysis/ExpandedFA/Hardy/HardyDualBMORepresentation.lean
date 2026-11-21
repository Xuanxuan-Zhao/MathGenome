import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.HardyDualBMORepresentation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hardy.HardyPAtoms
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hardy.BMOQuotient
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.RieszRepresentation
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace

namespace ExpandedFA.Hardy.HardyDualBMORepresentation
open HardyDualBMORepresentationSpec
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜]

lemma ballTests_supported {c : Point d} {r : ℝ} (f : ballTests d 𝕜 c r) :
    ∀ᵐ x ∂volume, x ∉ Metric.ball c r → f.val x = 0 := by
  have h := f.property.1
  change LpToLpRestrictCLM (Point d) 𝕜 𝕜 volume 2 (Metric.ball c r)ᶜ f.val = 0 at h
  have he : f.val =ᵐ[volume.restrict (Metric.ball c r)ᶜ] (0 : Point d → 𝕜) := by
    exact (LpToLpRestrictCLM_coeFn 𝕜 _ f.val).symm.trans
      (h ▸ Lp.coeFn_zero 𝕜 2 (volume.restrict (Metric.ball c r)ᶜ))
  exact (ae_restrict_iff' Metric.isOpen_ball.measurableSet.compl).mp he

lemma ballTests_integrable {c : Point d} {r : ℝ} (f : ballTests d 𝕜 c r) :
    Integrable (f.val : Point d → 𝕜) volume := by
  have hi : IntegrableOn (f.val : Point d → 𝕜) (Metric.ball c r) volume :=
    integrableOn_Lp_of_measure_ne_top f.val (by norm_num) measure_ball_ne_top
  apply (hi.integrable_indicator Metric.isOpen_ball.measurableSet).congr
  filter_upwards [ballTests_supported f] with x hx
  by_cases h : x ∈ Metric.ball c r
  · exact Set.indicator_of_mem h _
  · simpa [Set.indicator_of_notMem h] using (hx h).symm

lemma ballTests_integral_zero {c : Point d} {r : ℝ} (f : ballTests d 𝕜 c r) :
    (∫ x, f.val x) = 0 := by
  have h := f.property.2
  change ⟪(indicatorConstLp (s := Metric.ball c r) 2 Metric.isOpen_ball.measurableSet
    measure_ball_ne_top (1 : 𝕜) : L2 d 𝕜), f.val⟫_𝕜 = 0 at h
  rw [L2.inner_indicatorConstLp_one] at h
  rw [← h]
  symm
  rw [← integral_indicator Metric.isOpen_ball.measurableSet]
  apply integral_congr_ae
  filter_upwards [ballTests_supported f] with x hx
  by_cases h : x ∈ Metric.ball c r
  · exact Set.indicator_of_mem h _
  · simpa [Set.indicator_of_notMem h] using (hx h).symm

instance ballTests_isClosed (c : Point d) (r : ℝ) :
    IsClosed (ballTests d 𝕜 c r : Set (L2 d 𝕜)) :=
  (LpToLpRestrictCLM (Point d) 𝕜 𝕜 volume 2 (Metric.ball c r)ᶜ).isClosed_ker.inter
    (innerSL 𝕜 (indicatorConstLp (s := Metric.ball c r) 2 Metric.isOpen_ball.measurableSet
      measure_ball_ne_top (1 : 𝕜) : L2 d 𝕜)).isClosed_ker


/-- Exact homogeneous normalization of a ball-supported L² function. In
particular, the Hardy bound has no additive slack at the zero function. -/
lemma ball_hardy_lift (d : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ {𝕜 : Type} [RCLike 𝕜] (f : L1 d 𝕜), MemLp f 2 volume →
      (∫ x, f x) = 0 → ∀ (c : Point d) (r : ℝ), 0 < r →
      (∀ᵐ x ∂volume, x ∉ Metric.ball c r → f x = 0) →
      ∃ h : H1 d 𝕜, AtomicHardySpaceSpec.EmbeddingValue volume h = f ∧
        ‖h‖ ≤ C * (volume.real (Metric.ball c r)) ^ (1 / 2 : ℝ) *
          (eLpNorm f 2 volume).toReal := by
  obtain ⟨C, hC, hA⟩ := HardyPAtoms.pAtom_hardy_bound d 2 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ f hf hz c r hr hs
  by_cases hzero : f = 0
  · refine ⟨0, by simpa using hzero.symm, ?_⟩
    simp only [norm_zero]
    positivity
  let V : ℝ := volume.real (Metric.ball c r)
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top
  let b : ℝ := V ^ (1 / 2 - 1 : ℝ)
  have hb : 0 < b := Real.rpow_pos_of_pos hV _
  let N : ℝ := (eLpNorm f 2 volume).toReal
  have hN : 0 < N := by
    apply ENNReal.toReal_pos _ hf.eLpNorm_ne_top
    intro he
    apply hzero
    exact Lp.ext (((eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp he).trans
      (Lp.coeFn_zero 𝕜 1 volume).symm)
  let A : ℝ := N / b
  have hApos : 0 < A := div_pos hN hb
  let k : 𝕜 := (A : 𝕜)
  have hk : k ≠ 0 := RCLike.ofReal_ne_zero.mpr hApos.ne'
  have hkn : ‖k‖ = A := by
    change ‖(A : 𝕜)‖ = A
    rw [RCLike.norm_ofReal, abs_of_pos hApos]
  have hsm : ⇑(k⁻¹ • f) =ᵐ[volume] k⁻¹ • ⇑f := Lp.coeFn_smul _ _
  have hm : MemLp (⇑(k⁻¹ • f)) 2 volume := (hf.const_smul k⁻¹).ae_eq hsm.symm
  have hn : (eLpNorm (⇑(k⁻¹ • f)) 2 volume).toReal ≤ b := by
    rw [eLpNorm_congr_ae hsm, eLpNorm_const_smul, ENNReal.toReal_mul,
      ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _), norm_inv, hkn]
    change A⁻¹ * N ≤ b
    apply (inv_mul_le_iff₀ hApos).mpr
    dsimp [A]
    rw [div_mul_cancel₀ _ hb.ne']
  have hi0 : (∫ x, (k⁻¹ • f) x) = 0 := by
    rw [integral_congr_ae hsm]
    change (∫ x, k⁻¹ • f x) = 0
    rw [integral_smul, hz, smul_zero]
  have hsup : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → (k⁻¹ • f) x = 0 := by
    filter_upwards [hsm, hs] with x hx hxs
    intro hxB
    simp [hx, hxs hxB]
  let a : HardyPAtomsSpec.PAtom d 2 𝕜 :=
    ⟨k⁻¹ • f, by
      refine ⟨?_, hi0, c, r, hr, hsup, ?_⟩
      · simpa using hm
      · simpa [b, V] using hn⟩
  obtain ⟨u, hu, hnu⟩ := hA a
  refine ⟨k • u, ?_, ?_⟩
  · rw [map_smul, hu]
    exact smul_inv_smul₀ hk f
  · calc
      ‖k • u‖ = A * ‖u‖ := by rw [norm_smul, hkn]
      _ ≤ A * C := mul_le_mul_of_nonneg_left hnu hApos.le
      _ = C * V ^ (1 / 2 : ℝ) * N := by
        have hv : b⁻¹ = V ^ (1 / 2 : ℝ) := by
          dsimp [b]
          rw [← Real.rpow_neg hV.le]
          norm_num
        dsimp [A]
        rw [div_eq_mul_inv, hv]
        ring


/-- The L¹ class underlying a local L² test. -/
def ballTestToL1 {c : Point d} {r : ℝ} (f : ballTests d 𝕜 c r) : L1 d 𝕜 :=
  (ballTests_integrable f).toL1 f.val

lemma ballTestToL1_coe {c : Point d} {r : ℝ} (f : ballTests d 𝕜 c r) :
    ballTestToL1 f =ᵐ[volume] f.val := Integrable.coeFn_toL1 _

/-- This uses the actual L¹ representative map, rather than an unrelated
linear identification of the local test space. -/
def ballTestToL1Linear {c : Point d} {r : ℝ} : ballTests d 𝕜 c r →ₗ[𝕜] L1 d 𝕜 where
  toFun := ballTestToL1
  map_add' f g := by
    apply Lp.ext
    filter_upwards [ballTestToL1_coe (f + g), ballTestToL1_coe f, ballTestToL1_coe g,
      Lp.coeFn_add f.val g.val, Lp.coeFn_add (ballTestToL1 f) (ballTestToL1 g)] with x h h₁ h₂ h₃ h₄
    change (ballTestToL1 (f + g)) x = (ballTestToL1 f + ballTestToL1 g) x
    rw [h]
    change (f.val + g.val) x = (ballTestToL1 f + ballTestToL1 g) x
    rw [h₃, h₄]
    simp only [Pi.add_apply, h₁, h₂]
  map_smul' k f := by
    apply Lp.ext
    filter_upwards [ballTestToL1_coe (k • f), ballTestToL1_coe f,
      Lp.coeFn_smul k f.val, Lp.coeFn_smul k (ballTestToL1 f)] with x h h₁ h₂ h₃
    change (ballTestToL1 (k • f)) x = (k • ballTestToL1 f) x
    rw [h]
    change (k • f.val) x = (k • ballTestToL1 f) x
    rw [h₂, h₃]
    simp only [Pi.smul_apply, h₁]

/-- A bounded, canonical-by-injectivity Hardy lift of every local test.
Existence comes from p = 2 atoms; linearity comes from the accepted injective
L¹ embedding, without choosing a linear atomic decomposition. -/
lemma ballTest_hardy_map (d : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (𝕜 : Type) [RCLike 𝕜] (c : Point d) (r : ℝ), 0 < r →
      ∃ T : ballTests d 𝕜 c r →L[𝕜] H1 d 𝕜,
        (∀ f, AtomicHardySpaceSpec.EmbeddingValue volume (T f) = ballTestToL1 f) ∧
        ‖T‖ ≤ C * (volume.real (Metric.ball c r)) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, h⟩ := ball_hardy_lift d
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ c r hr
  have hf (f : ballTests d 𝕜 c r) : MemLp (ballTestToL1 f) 2 volume :=
    (Lp.memLp f.val).ae_eq (ballTestToL1_coe f).symm
  have hz (f : ballTests d 𝕜 c r) : (∫ x, ballTestToL1 f x) = 0 :=
    (integral_congr_ae (ballTestToL1_coe f)).trans (ballTests_integral_zero f)
  have hs (f : ballTests d 𝕜 c r) :
      ∀ᵐ x ∂volume, x ∉ Metric.ball c r → ballTestToL1 f x = 0 := by
    filter_upwards [ballTestToL1_coe f, ballTests_supported f] with x hx hxB
    simpa only [hx] using hxB
  have hn (f : ballTests d 𝕜 c r) :
      (eLpNorm (ballTestToL1 f) 2 volume).toReal = ‖f‖ := by
    rw [eLpNorm_congr_ae (ballTestToL1_coe f)]
    rfl
  have hex (f : ballTests d 𝕜 c r) : ∃ u : H1 d 𝕜,
      AtomicHardySpaceSpec.EmbeddingValue volume u = ballTestToL1 f ∧
      ‖u‖ ≤ (C * (volume.real (Metric.ball c r)) ^ (1 / 2 : ℝ)) * ‖f‖ := by
    simpa only [hn f] using h (ballTestToL1 f) (hf f) (hz f) c r hr (hs f)
  choose u hu hnu using hex
  have hinj := (AtomicHardySpace.embedding_properties (𝕜 := 𝕜)
    (volume : Measure (Point d))).1
  let U : ballTests d 𝕜 c r →ₗ[𝕜] H1 d 𝕜 := {
    toFun := u
    map_add' := by
      intro f g
      apply hinj
      rw [map_add, hu, hu, hu]
      exact (ballTestToL1Linear (c := c) (r := r)).map_add f g
    map_smul' := by
      intro k f
      apply hinj
      rw [map_smul, hu, hu]
      exact (ballTestToL1Linear (c := c) (r := r)).map_smul k f }
  let T := U.mkContinuous (C * (volume.real (Metric.ball c r)) ^ (1 / 2 : ℝ)) hnu
  refine ⟨T, hu, ?_⟩
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- Build an actual element of the local Hilbert subspace from an L¹
class with the asserted support, cancellation, and L² membership. -/
lemma exists_ballTest (f : L1 d 𝕜) (hf : MemLp f 2 volume)
    (hz : (∫ x, f x) = 0) (c : Point d) (r : ℝ)
    (hs : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → f x = 0) :
    ∃ t : ballTests d 𝕜 c r, t.val =ᵐ[volume] f := by
  let t := hf.toLp f
  have he : t =ᵐ[volume] f := MemLp.coeFn_toLp hf
  refine ⟨⟨t, ?_⟩, he⟩
  constructor
  · change LpToLpRestrictCLM (Point d) 𝕜 𝕜 volume 2 (Metric.ball c r)ᶜ t = 0
    apply Lp.ext
    apply (LpToLpRestrictCLM_coeFn 𝕜 _ t).trans
    apply EventuallyEq.trans _ (Lp.coeFn_zero 𝕜 2 _).symm
    apply (ae_restrict_iff' Metric.isOpen_ball.measurableSet.compl).mpr
    filter_upwards [he, hs] with x hx hxs hxB
    exact hx.trans (hxs hxB)
  · change ⟪(indicatorConstLp (s := Metric.ball c r) 2 Metric.isOpen_ball.measurableSet
      measure_ball_ne_top (1 : 𝕜) : L2 d 𝕜), t⟫_𝕜 = 0
    rw [L2.inner_indicatorConstLp_one, ← integral_indicator Metric.isOpen_ball.measurableSet]
    apply (integral_congr_ae ?_).trans hz
    filter_upwards [he, hs] with x hx hxs
    by_cases hxB : x ∈ Metric.ball c r
    · simpa only [Set.indicator_of_mem hxB] using hx
    · simpa only [Set.indicator_of_notMem hxB] using (hxs hxB).symm

/-- Riesz on the closed local test subspace gives the mean-zero local
representatives with a uniform, homogeneous, dimension-only bound. -/
theorem local_representation : LocalRepresentation := by
  intro d
  obtain ⟨C, hC, h⟩ := ballTest_hardy_map d
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ L c r hr
  obtain ⟨T, hT, hnT⟩ := h 𝕜 c r hr
  obtain ⟨v, hv, hnv, _⟩ := Hilbert.RieszRepresentation.functional_representation
    𝕜 (ballTests d 𝕜 c r) (L.comp T)
  refine ⟨v, ?_, ?_⟩
  · change ‖v‖ ≤ _
    rw [← hnv]
    calc
      ‖L.comp T‖ ≤ ‖L‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖L‖ * (C * (volume.real (Metric.ball c r)) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hnT (norm_nonneg L)
      _ = _ := by ring
  · intro u f huf
    have he : u = T f := by
      apply (AtomicHardySpace.embedding_properties (𝕜 := 𝕜) volume).1
      rw [hT]
      exact Lp.ext (huf.trans (ballTestToL1_coe f).symm)
    rw [he]
    calc
      L (T f) = ⟪v, f⟫_𝕜 := hv f
      _ = ∫ x, f.val x * star (v.val x) := by
        change (∫ x, ⟪v.val x, f.val x⟫_𝕜) = _
        apply integral_congr_ae
        filter_upwards with x
        simp only [RCLike.inner_apply, starRingEnd_apply, mul_comm]


/-- Products with individual infinity-atoms really are Lebesgue integrable
for every locally integrable representative, even when it is unbounded. -/
lemma integrable_atom_mul (g : Point d → 𝕜) (hg : LocallyIntegrable g volume)
    (a : Atom d 𝕜) : Integrable (fun x => a.val x * g x) volume := by
  obtain ⟨c, r, hr, _, _, hb⟩ := a.property.2
  have hi := (integrableOn_ball_of_locallyIntegrable hg c r).integrable_indicator
    Metric.isOpen_ball.measurableSet
  have hip := hi.bdd_mul (Lp.aestronglyMeasurable a.val) (hb.mono fun _ hx => hx.2)
  apply hip.congr
  filter_upwards [hb] with x hx
  by_cases h : x ∈ Metric.ball c r
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h, hx.1 h]

/-- Atom pairings suffice for the exact finite-sum statement in the Spec.
This is purely linear assembly; no assertion about products for infinite
atomic sums is used. -/
lemma represents_of_atom_pairings (L : H1 d 𝕜 →L[𝕜] 𝕜)
    (g : Point d → 𝕜) (hg : LocallyIntegrable g volume)
    (ha : ∀ a : Atom d 𝕜,
      L (AtomicHardySpace.atomElement volume a) = ∫ x, a.val x * g x) :
    Represents L g := by
  classical
  let E : H1 d 𝕜 →L[𝕜] L1 d 𝕜 := AtomicHardySpaceSpec.EmbeddingValue volume
  let P (h : H1 d 𝕜) : Prop :=
    Integrable (fun x => E h x * g x) volume ∧ L h = ∫ x, E h x * g x
  have hzero : P 0 := by
    have he : (fun x => E 0 x * g x) =ᵐ[volume] 0 := by
      rw [map_zero]
      exact (Lp.coeFn_zero 𝕜 1 volume).mono fun x _ => by simp
    exact ⟨(integrable_zero (Point d) 𝕜 volume).congr he.symm,
      (map_zero L).trans (integral_eq_zero_of_ae he).symm⟩
  have hadd (u v : H1 d 𝕜) (hu : P u) (hv : P v) : P (u + v) := by
    have he : (fun x => E (u + v) x * g x) =ᵐ[volume]
        (fun x => E u x * g x + E v x * g x) := by
      rw [map_add]
      exact (Lp.coeFn_add (E u) (E v)).mono fun x hx =>
        (congrArg (fun z : 𝕜 => z * g x) hx).trans (add_mul _ _ _)
    refine ⟨(hu.1.add hv.1).congr he.symm, ?_⟩
    rw [map_add, hu.2, hv.2, integral_congr_ae he, integral_add hu.1 hv.1]
  have hsmul (k : 𝕜) (u : H1 d 𝕜) (hu : P u) : P (k • u) := by
    have he : (fun x => E (k • u) x * g x) =ᵐ[volume]
        (fun x => k * (E u x * g x)) := by
      rw [map_smul]
      exact (Lp.coeFn_smul k (E u)).mono fun x hx => by
        simp only [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
    refine ⟨(hu.1.const_mul k).congr he.symm, ?_⟩
    rw [map_smul, smul_eq_mul, hu.2, integral_congr_ae he, integral_const_mul]
  have hatom (a : Atom d 𝕜) : P (AtomicHardySpace.atomElement volume a) := by
    change Integrable (fun x => E (AtomicHardySpace.atomElement volume a) x * g x) volume ∧ _
    have he : E (AtomicHardySpace.atomElement volume a) = a.val :=
      AtomicHardySpace.embedding_atomElement volume a
    rw [he]
    exact ⟨integrable_atom_mul g hg a, ha a⟩
  intro s a h he
  let v : H1 d 𝕜 := ∑ b ∈ s, a b • AtomicHardySpace.atomElement volume b
  have hp : P v := by
    clear he h
    dsimp [v]
    clear v
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | @insert b s hb ih =>
      rw [Finset.sum_insert hb]
      exact hadd _ _ (hsmul _ _ (hatom b)) ih
  have hv : h = v := by
    apply (AtomicHardySpace.embedding_properties (𝕜 := 𝕜)
      (volume : Measure (Point d))).1
    change E h = E v
    rw [he]
    simp only [v, map_sum, map_smul, E, AtomicHardySpace.embedding_atomElement]
  exact hv ▸ hp

/-- Any bounded ball-supported zero-mean test is a scalar multiple of an
infinity-atom. Thus annihilating atoms annihilates all these tests. -/
lemma integral_test_mul_zero (w : Point d → 𝕜) (c : Point d) (r : ℝ)
    (ha : ∀ a : Atom d 𝕜,
      (∀ᵐ x ∂volume, x ∉ Metric.ball c r → a.val x = 0) →
      (∫ x, a.val x * w x) = 0)
    (f : Point d → 𝕜) (hf : AEStronglyMeasurable f volume)
    (hz : (∫ x, f x) = 0) (K : ℝ) (hr : 0 < r) (hK : 0 < K)
    (hs : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → f x = 0)
    (hb : ∀ᵐ x ∂volume, ‖f x‖ ≤ K) : (∫ x, f x * w x) = 0 := by
  let V := volume.real (Metric.ball c r)
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top
  let k : 𝕜 := ((K * V)⁻¹ : ℝ)
  have hk : k ≠ 0 := RCLike.ofReal_ne_zero.mpr (inv_ne_zero (mul_pos hK hV).ne')
  have hkn : ‖k‖ = (K * V)⁻¹ := by
    simp only [k, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr (mul_pos hK hV))]
  obtain ⟨a, he⟩ := AtomicHardySpace.euclidean_atom_realization d (fun x => k * f x)
    (hf.const_mul k) (by simp only [integral_const_mul, hz, mul_zero])
    ⟨c, r, hr, by
      filter_upwards [hs, hb] with x hx hxb
      refine ⟨fun h => by simp [hx h], ?_⟩
      rw [norm_mul, hkn]
      calc
        (K * V)⁻¹ * ‖f x‖ ≤ (K * V)⁻¹ * K :=
          mul_le_mul_of_nonneg_left hxb (by positivity)
        _ = V⁻¹ := by field_simp⟩
  have h := ha a (by
    filter_upwards [he, hs] with x hx hxs hxB
    simp [hx, hxs hxB])
  rw [integral_congr_ae (he.mono fun x hx => congrArg (fun z => z * w x) hx)] at h
  simp only [mul_assoc, integral_const_mul] at h
  exact (mul_eq_zero.mp h).resolve_left hk

/-- Atom annihilation forces a locally integrable function to be constant on
each ball. The measurable-set tests are centered indicators, normalized by
the preceding lemma into genuine atoms. -/
lemma ae_eq_ballMean_of_atom_annihilation (w : Point d → 𝕜)
    (hw : LocallyIntegrable w volume)
    (c : Point d) {r : ℝ} (hr : 0 < r)
    (ha : ∀ a : Atom d 𝕜,
      (∀ᵐ x ∂volume, x ∉ Metric.ball c r → a.val x = 0) →
      (∫ x, a.val x * w x) = 0) :
    ∀ᵐ x ∂volume, x ∈ Metric.ball c r → w x = ballMean w c r := by
  let B := Metric.ball c r
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hBt : volume B ≠ ∞ := measure_ball_ne_top
  let V := volume.real B
  have hV : 0 < V := ENNReal.toReal_pos (Metric.measure_ball_pos volume c hr).ne' hBt
  have hiB : IntegrableOn w B volume := integrableOn_ball_of_locallyIntegrable hw c r
  have htest (S : Set (Point d)) (hS : MeasurableSet S) (hSB : S ⊆ B) :
      (∫ x in S, w x) = ((volume.real S / V : ℝ) : 𝕜) * ∫ x in B, w x := by
    have hSt : volume S ≠ ∞ := ne_top_of_le_ne_top hBt (measure_mono hSB)
    let α := volume.real S / V
    have hα : 0 ≤ α := div_nonneg (measureReal_nonneg) hV.le
    have hα1 : α ≤ 1 := (div_le_one hV).mpr (measureReal_mono hSB hBt)
    let f : Point d → 𝕜 := fun x =>
      S.indicator (fun _ => (1 : 𝕜)) x - (α : 𝕜) * B.indicator (fun _ => 1) x
    have hiS1 : Integrable (S.indicator (fun _ => (1 : 𝕜))) volume :=
      (integrableOn_const hSt).integrable_indicator hS
    have hiB1 : Integrable (B.indicator (fun _ => (1 : 𝕜))) volume :=
      (integrableOn_const hBt).integrable_indicator hB
    have hfm : AEStronglyMeasurable f volume :=
      hiS1.aestronglyMeasurable.sub (hiB1.aestronglyMeasurable.const_mul _)
    have hfz : (∫ x, f x) = 0 := by
      dsimp [f]
      rw [integral_sub hiS1 (hiB1.const_mul _), integral_const_mul,
        integral_indicator_const _ hS, integral_indicator_const _ hB]
      simp only [RCLike.real_smul_eq_coe_mul, mul_one]
      have hv : α * V = volume.real S := div_mul_cancel₀ _ hV.ne'
      exact sub_eq_zero.mpr (by exact_mod_cast hv.symm)
    have hfs : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → f x = 0 := by
      filter_upwards with x hx
      have hxS : x ∉ S := fun h => hx (hSB h)
      simp [f, Set.indicator_of_notMem hxS, Set.indicator_of_notMem hx, B] at *
    have hfb : ∀ᵐ x ∂volume, ‖f x‖ ≤ 2 := by
      filter_upwards with x
      have hnS : ‖S.indicator (fun _ => (1 : 𝕜)) x‖ ≤ 1 := by
        by_cases hx : x ∈ S <;> simp [hx]
      have hnB : ‖B.indicator (fun _ => (1 : 𝕜)) x‖ ≤ 1 := by
        by_cases hx : x ∈ B <;> simp [hx]
      calc
        ‖f x‖ ≤ ‖S.indicator (fun _ => (1 : 𝕜)) x‖ +
          ‖(α : 𝕜) * B.indicator (fun _ => 1) x‖ := norm_sub_le _ _
        _ ≤ 1 + α := by
          rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg hα]
          exact add_le_add hnS (mul_le_of_le_one_right hα hnB)
        _ ≤ 2 := by linarith
    have hz := integral_test_mul_zero w c r ha f hfm hfz 2 hr (by norm_num) hfs hfb
    have hipS := (hiB.mono_set hSB).integrable_indicator hS
    have hipB := hiB.integrable_indicator hB
    have he : (fun x => f x * w x) = fun x =>
        S.indicator w x - (α : 𝕜) * B.indicator w x := by
      funext x
      dsimp [f]
      rw [sub_mul, mul_assoc]
      congr 1 <;> by_cases hx : x ∈ S <;> by_cases hy : x ∈ B <;> simp [hx, hy]
    rw [he, integral_sub hipS (hipB.const_mul _), integral_const_mul,
      integral_indicator hS, integral_indicator hB] at hz
    exact sub_eq_zero.mp hz
  have he : w =ᵐ[volume.restrict B] fun _ => ballMean w c r := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hiB
      (integrableOn_const hBt)
    intro S hS _
    simp only [Measure.restrict_restrict hS]
    rw [setIntegral_const]
    rw [htest (S ∩ B) (hS.inter hB) Set.inter_subset_right]
    change ((volume.real (S ∩ B) / V : ℝ) : 𝕜) * _ =
      volume.real (S ∩ B) • (V⁻¹ • ∫ x in B, w x)
    simp only [div_eq_mul_inv, RCLike.real_smul_eq_coe_mul, map_mul, mul_assoc]
  exact (ae_restrict_iff' hB).mp he

/-- Locally integrable functions are separated by the actual infinity-atoms,
up to one global almost-everywhere constant. -/
theorem atom_separation : AtomSeparation := by
  intro d 𝕜 _ g g' hg hg' he
  let w : Point d → 𝕜 := fun x => g' x - g x
  have hw : LocallyIntegrable w volume := hg'.sub hg
  have ha (a : Atom d 𝕜) : (∫ x, a.val x * w x) = 0 := by
    simp only [w, mul_sub]
    rw [integral_sub (integrable_atom_mul g' hg' a) (integrable_atom_mul g hg a), he a,
      sub_self]
  have hz : bmoENorm w = 0 := by
    apply le_antisymm _ zero_le
    apply iSup_le fun c => iSup_le fun r => iSup_le fun hr => ?_
    change (volume (Metric.ball c r))⁻¹ *
      (∫⁻ x in Metric.ball c r, ‖w x - ballMean w c r‖ₑ) ≤ 0
    have hloc := ae_eq_ballMean_of_atom_annihilation w hw c hr (fun a _ => ha a)
    have hi : (∫⁻ x in Metric.ball c r, ‖w x - ballMean w c r‖ₑ) = 0 := by
      apply (setLIntegral_eq_zero_iff' measurableSet_ball
        (hw.aestronglyMeasurable.restrict.sub aestronglyMeasurable_const).enorm).mpr
      filter_upwards [hloc] with x hx hmem
      simp [hx hmem]
    simp [hi]
  obtain ⟨k, hk⟩ := (bmoENorm_eq_zero_iff w hw).mp hz
  refine ⟨k, hk.mono fun x hx => ?_⟩
  change g' x - g x = k at hx
  simpa only [add_comm] using sub_eq_iff_eq_add.mp hx

/-- The local Riesz formula applies to every atom supported in the ball,
regardless of which supporting ball was originally stored with that atom. -/
lemma local_atom_pairing (L : H1 d 𝕜 →L[𝕜] 𝕜)
    {c : Point d} {r : ℝ} (v : ballTests d 𝕜 c r)
    (hv : ∀ (h : H1 d 𝕜) (f : ballTests d 𝕜 c r),
      AtomicHardySpaceSpec.EmbeddingValue volume h =ᵐ[volume] f.val →
      L h = ∫ x, f.val x * star (v.val x))
    (a : Atom d 𝕜) (hs : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → a.val x = 0) :
    L (AtomicHardySpace.atomElement volume a) = ∫ x, a.val x * star (v.val x) := by
  have hm : MemLp a.val 2 volume := by
    simpa using (HardyPAtoms.infinityAtoms_are_pAtoms d 2 (by norm_num) a).1
  obtain ⟨t, ht⟩ := exists_ballTest a.val hm a.property.1 c r hs
  exact (hv (AtomicHardySpace.atomElement volume a) t
    ((AtomicHardySpace.embedding_atomElement volume a) ▸ ht.symm)).trans
    (integral_congr_ae (ht.mono fun x hx => congrArg (fun z => z * star (v.val x)) hx))

/-- Local Riesz representatives on nested balls differ by a constant on the
smaller ball. This uses the proved separation argument locally. -/
lemma local_representatives_compatible (L : H1 d 𝕜 →L[𝕜] 𝕜)
    {c e : Point d} {r s : ℝ} (hr : 0 < r)
    (v : ballTests d 𝕜 c r) (u : ballTests d 𝕜 e s)
    (hv : ∀ (h : H1 d 𝕜) (f : ballTests d 𝕜 c r),
      AtomicHardySpaceSpec.EmbeddingValue volume h =ᵐ[volume] f.val →
      L h = ∫ x, f.val x * star (v.val x))
    (hu : ∀ (h : H1 d 𝕜) (f : ballTests d 𝕜 e s),
      AtomicHardySpaceSpec.EmbeddingValue volume h =ᵐ[volume] f.val →
      L h = ∫ x, f.val x * star (u.val x))
    (hsub : Metric.ball c r ⊆ Metric.ball e s) :
    ∃ k : 𝕜, ∀ᵐ x ∂volume, x ∈ Metric.ball c r →
      star (u.val x) = star (v.val x) + k := by
  let w : Point d → 𝕜 := fun x => star (u.val x) - star (v.val x)
  have hiu : LocallyIntegrable (fun x => star (u.val x)) volume :=
    (RCLike.conjCLE (K := 𝕜)).toContinuousLinearMap.integrable_comp
      (ballTests_integrable u) |>.locallyIntegrable
  have hiv : LocallyIntegrable (fun x => star (v.val x)) volume :=
    (RCLike.conjCLE (K := 𝕜)).toContinuousLinearMap.integrable_comp
      (ballTests_integrable v) |>.locallyIntegrable
  have hw : LocallyIntegrable w volume := hiu.sub hiv
  have ha (a : Atom d 𝕜) (hs : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → a.val x = 0) :
      (∫ x, a.val x * w x) = 0 := by
    have hs' : ∀ᵐ x ∂volume, x ∉ Metric.ball e s → a.val x = 0 :=
      hs.mono fun x hx hxs => hx (fun hxr => hxs (hsub hxr))
    have hp := (local_atom_pairing L v hv a hs).symm.trans
      (local_atom_pairing L u hu a hs')
    simp only [w, mul_sub]
    rw [integral_sub (integrable_atom_mul _ hiu a) (integrable_atom_mul _ hiv a),
      ← hp, sub_self]
  refine ⟨ballMean w c r, ?_⟩
  filter_upwards [ae_eq_ballMean_of_atom_annihilation w hw c hr ha] with x hx hmem
  have he := hx hmem
  change star (u.val x) - star (v.val x) = _ at he
  simpa only [add_comm] using sub_eq_iff_eq_add.mp he

/-- Glue an a.e. compatible sequence along the concentric ball exhaustion.
Choosing a representative pointwise is harmless: compatibility proves its
local a.e. equalities, from which local integrability follows. -/
lemma glue_compatible_sequence (u : ℕ → Point d → 𝕜)
    (hu : ∀ n, LocallyIntegrable (u n) volume)
    (hc : ∀ n m : ℕ, n ≤ m → ∀ᵐ x ∂volume,
      x ∈ Metric.ball (0 : Point d) ((n : ℝ) + 1) → u m x = u n x) :
    ∃ g : Point d → 𝕜, LocallyIntegrable g volume ∧ ∀ n : ℕ, ∀ᵐ x ∂volume,
      x ∈ Metric.ball (0 : Point d) ((n : ℝ) + 1) → g x = u n x := by
  classical
  have hex (x : Point d) : ∃ n : ℕ, x ∈ Metric.ball (0 : Point d) ((n : ℝ) + 1) := by
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    refine ⟨n, ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  let g (x : Point d) : 𝕜 := u (Nat.find (hex x)) x
  have he (n : ℕ) : ∀ᵐ x ∂volume,
      x ∈ Metric.ball (0 : Point d) ((n : ℝ) + 1) → g x = u n x := by
    have hall : ∀ᵐ x ∂volume, ∀ i j : ℕ, i ≤ j →
        x ∈ Metric.ball (0 : Point d) ((i : ℝ) + 1) → u j x = u i x := by
      apply ae_all_iff.mpr
      intro i
      apply ae_all_iff.mpr
      intro j
      by_cases h : i ≤ j
      · exact (hc i j h).mono fun x hx _ => hx
      · exact Eventually.of_forall fun _ hij => (h hij).elim
    filter_upwards [hall] with x hx hxn
    exact (hx (Nat.find (hex x)) n (Nat.find_min' (hex x) hxn)
      (Nat.find_spec (hex x))).symm
  refine ⟨g, ?_, he⟩
  intro x
  obtain ⟨n, hn⟩ := hex x
  refine ⟨Metric.ball 0 ((n : ℝ) + 1), Metric.isOpen_ball.mem_nhds hn, ?_⟩
  exact (integrableOn_ball_of_locallyIntegrable (hu n) 0 ((n : ℝ) + 1)).congr
    (EventuallyEq.symm ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr (he n)))

/-- Local equality on a ball is enough to compare its means. -/
lemma ballMean_congr_on_ball {f g : Point d → 𝕜} (c : Point d) (r : ℝ)
    (he : ∀ᵐ x ∂volume, x ∈ Metric.ball c r → f x = g x) :
    ballMean f c r = ballMean g c r := by
  change _ • (∫ x in Metric.ball c r, f x) = _ • (∫ x in Metric.ball c r, g x)
  congr 1
  exact setIntegral_congr_ae measurableSet_ball he

/-- A family on all positive balls, compatible up to constants on nested
balls, has a global locally integrable representative with the same local
classes. Constants are fixed by subtracting the mean on the unit ball. -/
lemma glue_mod_constants
    (u : (c : Point d) → (r : ℝ) → 0 < r → Point d → 𝕜)
    (hu : ∀ c r hr, LocallyIntegrable (u c r hr) volume)
    (hc : ∀ c r hr e s hs, Metric.ball c r ⊆ Metric.ball e s →
      ∃ k : 𝕜, ∀ᵐ x ∂volume, x ∈ Metric.ball c r →
        u e s hs x = u c r hr x + k) :
    ∃ g : Point d → 𝕜, LocallyIntegrable g volume ∧
      ∀ c r hr, ∃ k : 𝕜, ∀ᵐ x ∂volume, x ∈ Metric.ball c r →
        g x = u c r hr x + k := by
  let p (n : ℕ) := u 0 ((n : ℝ) + 1) (by positivity)
  let q (n : ℕ) (x : Point d) := p n x - ballMean (p n) 0 1
  have hq (n : ℕ) : LocallyIntegrable (q n) volume :=
    (hu 0 _ _).sub (locallyIntegrable_const _)
  have hqc (n m : ℕ) (hnm : n ≤ m) : ∀ᵐ x ∂volume,
      x ∈ Metric.ball (0 : Point d) ((n : ℝ) + 1) → q m x = q n x := by
    have hsub : Metric.ball (0 : Point d) ((n : ℝ) + 1) ⊆
        Metric.ball 0 ((m : ℝ) + 1) :=
      Metric.ball_subset_ball (by exact_mod_cast Nat.add_le_add_right hnm 1)
    obtain ⟨k, hk⟩ := hc 0 _ (by positivity) 0 _ (by positivity) hsub
    have hk' : ∀ᵐ x ∂volume, x ∈ Metric.ball (0 : Point d) ((n : ℝ) + 1) →
        p m x = p n x + k := hk
    have hmean : ballMean (p m) 0 1 = ballMean (p n) 0 1 + k := by
      rw [← ballMean_add_const (hu 0 _ _) k 0 zero_lt_one]
      apply ballMean_congr_on_ball
      have hsub0 : Metric.ball (0 : Point d) 1 ⊆ Metric.ball 0 ((n : ℝ) + 1) :=
        Metric.ball_subset_ball (by linarith [Nat.cast_nonneg (α := ℝ) n])
      exact hk'.mono fun x hx hmem => hx (hsub0 hmem)
    filter_upwards [hk'] with x hx hmem
    dsimp [q]
    rw [hx hmem, hmean]
    abel
  obtain ⟨g, hg, he⟩ := glue_compatible_sequence q hq hqc
  refine ⟨g, hg, ?_⟩
  intro c r hr
  obtain ⟨n, hn⟩ := exists_nat_gt (r + ‖c‖)
  have hsub : Metric.ball c r ⊆ Metric.ball (0 : Point d) ((n : ℝ) + 1) :=
    Metric.ball_subset_ball' (by rw [dist_zero_right]; linarith)
  obtain ⟨k, hk⟩ := hc c r hr 0 _ (by positivity) hsub
  refine ⟨k - ballMean (p n) 0 1, ?_⟩
  filter_upwards [he n, hk] with x hx hxx hmem
  rw [hx (hsub hmem)]
  change p n x - ballMean (p n) 0 1 = _
  have hp : p n x = u c r hr x + k := hxx hmem
  rw [hp]
  abel

/-- The local Riesz vector has zero mean on its own ball. -/
lemma ballTest_setIntegral_zero {c : Point d} {r : ℝ} (v : ballTests d 𝕜 c r) :
    (∫ x in Metric.ball c r, v.val x) = 0 := by
  have h := v.property.2
  change ⟪(indicatorConstLp (s := Metric.ball c r) 2 Metric.isOpen_ball.measurableSet
    measure_ball_ne_top (1 : 𝕜) : L2 d 𝕜), v.val⟫_𝕜 = 0 at h
  rwa [L2.inner_indicatorConstLp_one] at h

/-- Hölder on the supporting ball in the precise L² normalization needed
for the mean-oscillation bound. -/
lemma ballTest_integral_norm_le {c : Point d} {r : ℝ} (hr : 0 < r)
    (v : ballTests d 𝕜 c r) :
    (∫ x in Metric.ball c r, ‖v.val x‖) ≤
      ‖v.val‖ * (volume.real (Metric.ball c r)) ^ (1 / 2 : ℝ) := by
  have hm : MemLp (ballTestToL1 v) 2 volume :=
    (Lp.memLp v.val).ae_eq (ballTestToL1_coe v).symm
  have hs : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → ballTestToL1 v x = 0 := by
    filter_upwards [ballTestToL1_coe v, ballTests_supported v] with x hx hxs hmem
    exact hx.trans (hxs hmem)
  have hh := HardyPAtoms.ball_holder (p := 2) (by norm_num)
    (ballTestToL1 v) (by simpa using hm) c r hr hs
  have hn : (eLpNorm (ballTestToL1 v) 2 volume).toReal = ‖v.val‖ := by
    rw [eLpNorm_congr_ae (ballTestToL1_coe v)]
    rfl
  have he : ‖ballTestToL1 v‖ = ∫ x in Metric.ball c r, ‖v.val x‖ := by
    rw [MeasureTheory.L1.norm_eq_integral_norm,
      integral_congr_ae ((ballTestToL1_coe v).mono fun x hx => congrArg norm hx),
      ← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [ballTests_supported v] with x hx
    by_cases hmem : x ∈ Metric.ball c r
    · simp [hmem]
    · simp [hmem, hx hmem]
  norm_num at hh
  rwa [he, hn] at hh

/-- A locally glued representative inherits the dimension-only BMO estimate
from the homogeneous L² bound. -/
lemma meanOscillation_le_of_local_vector (g : Point d → 𝕜)
    (hg : LocallyIntegrable g volume) {c : Point d} {r : ℝ} (hr : 0 < r)
    (v : ballTests d 𝕜 c r) (k : 𝕜)
    (he : ∀ᵐ x ∂volume, x ∈ Metric.ball c r → g x = star (v.val x) + k)
    (A : ℝ) (hn : ‖v.val‖ ≤ A * (volume.real (Metric.ball c r)) ^ (1 / 2 : ℝ)) :
    meanOscillation g c r ≤ ENNReal.ofReal A := by
  have hi : LocallyIntegrable (fun x => star (v.val x)) volume :=
    (RCLike.conjCLE (K := 𝕜)).toContinuousLinearMap.integrable_comp
      (ballTests_integrable v) |>.locallyIntegrable
  have hz : ballMean (fun x => star (v.val x)) c r = 0 := by
    change _ • (∫ x in Metric.ball c r, star (v.val x)) = 0
    rw [show (∫ x in Metric.ball c r, star (v.val x)) = star (∫ x in Metric.ball c r, v.val x)
      from integral_conj, ballTest_setIntegral_zero, star_zero, smul_zero]
  have hmean : ballMean g c r = k := by
    rw [ballMean_congr_on_ball c r he, ballMean_add_const hi k c hr, hz, zero_add]
  change BMOQuotientSpec.MeanOscillationValue g c r ≤ ENNReal.ofReal A
  rw [meanOscillation_formula g hg c r hr]
  apply ENNReal.ofReal_le_ofReal
  change (volume.real (Metric.ball c r))⁻¹ * (∫ x in Metric.ball c r, ‖g x - ballMean g c r‖) ≤ A
  rw [hmean]
  have he' : (∫ x in Metric.ball c r, ‖g x - k‖) =
      ∫ x in Metric.ball c r, ‖v.val x‖ := by
    apply setIntegral_congr_ae measurableSet_ball
    filter_upwards [he] with x hx hmem
    rw [hx hmem, add_sub_cancel_right, norm_star]
  rw [he']
  let V := volume.real (Metric.ball c r)
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top
  have hp : V ^ (1 / 2 : ℝ) * V ^ (1 / 2 : ℝ) = V := by
    rw [← Real.rpow_add hV, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
  calc
    V⁻¹ * (∫ x in Metric.ball c r, ‖v.val x‖) ≤
        V⁻¹ * (‖v.val‖ * V ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (ballTest_integral_norm_le hr v) (inv_nonneg.mpr hV.le)
    _ ≤ V⁻¹ * ((A * V ^ (1 / 2 : ℝ)) * V ^ (1 / 2 : ℝ)) := by
      gcongr
    _ = A := by rw [mul_assoc A, hp]; field_simp

/-- Adding a constant on the support of an atom preserves its pairing. -/
lemma atom_pairing_eq_of_local_constant (a : Atom d 𝕜)
    (f g : Point d → 𝕜) (hf : LocallyIntegrable f volume) (_hg : LocallyIntegrable g volume)
    (c : Point d) (r : ℝ) (k : 𝕜)
    (hs : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → a.val x = 0)
    (he : ∀ᵐ x ∂volume, x ∈ Metric.ball c r → g x = f x + k) :
    (∫ x, a.val x * g x) = ∫ x, a.val x * f x := by
  have he' : (fun x => a.val x * g x) =ᵐ[volume]
      fun x => a.val x * f x + a.val x * k := by
    filter_upwards [hs, he] with x hx hxx
    by_cases hmem : x ∈ Metric.ball c r
    · rw [hxx hmem, mul_add]
    · simp [hx hmem]
  rw [integral_congr_ae he', integral_add (integrable_atom_mul f hf a)
    ((MeasureTheory.L1.integrable_coeFn a.val).mul_const k), integral_mul_const,
    a.property.1, zero_mul, add_zero]

/-- Global existence with the quantitative estimate. This constructs the
representative, rather than assuming a compatible family or a BMO certificate. -/
theorem atomic_existence : AtomicExistence := by
  intro d
  obtain ⟨C, hC, hl⟩ := local_representation d
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ L
  choose v hvn hv using fun c r hr => hl 𝕜 L c r hr
  let u (c : Point d) (r : ℝ) (hr : 0 < r) (x : Point d) : 𝕜 := star ((v c r hr).val x)
  have hu (c : Point d) (r : ℝ) (hr : 0 < r) : LocallyIntegrable (u c r hr) volume :=
    (RCLike.conjCLE (K := 𝕜)).toContinuousLinearMap.integrable_comp
      (ballTests_integrable (v c r hr)) |>.locallyIntegrable
  have hc (c : Point d) (r : ℝ) (hr : 0 < r) (e : Point d) (s : ℝ) (hs : 0 < s)
      (hsub : Metric.ball c r ⊆ Metric.ball e s) :
      ∃ k : 𝕜, ∀ᵐ x ∂volume, x ∈ Metric.ball c r → u e s hs x = u c r hr x + k :=
    local_representatives_compatible L hr (v c r hr) (v e s hs) (hv c r hr) (hv e s hs) hsub
  obtain ⟨g, hg, he⟩ := glue_mod_constants u hu hc
  have hgn : bmoENorm g ≤ ENNReal.ofReal (C * ‖L‖) := by
    apply iSup_le fun c => iSup_le fun r => iSup_le fun hr => ?_
    obtain ⟨k, hk⟩ := he c r hr
    apply meanOscillation_le_of_local_vector g hg hr (v c r hr) k hk (C * ‖L‖)
    calc
      ‖(v c r hr).val‖ ≤ C * (volume.real (Metric.ball c r)) ^ (1 / 2 : ℝ) * ‖L‖ := hvn c r hr
      _ = _ := by ring
  refine ⟨⟨g, hg, lt_of_le_of_lt hgn ENNReal.ofReal_lt_top⟩, hgn, ?_⟩
  intro a h hah
  obtain ⟨c, r, hr, _, _, hb⟩ := a.property.2
  have hs : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → a.val x = 0 := hb.mono fun x hx => hx.1
  obtain ⟨k, hk⟩ := he c r hr
  have hh : h = AtomicHardySpace.atomElement volume a := by
    apply (AtomicHardySpace.embedding_properties (𝕜 := 𝕜) volume).1
    rw [hah, AtomicHardySpace.embedding_atomElement]
  rw [hh, local_atom_pairing L (v c r hr) (hv c r hr) a hs]
  exact (atom_pairing_eq_of_local_constant a (u c r hr) g (hu c r hr) hg c r k hs hk).symm

/-- Assemble global existence and atom separation into the full representation
statement. The unconditional theorem below supplies both proved premises. -/
theorem assemble_representation : Assembly := by
  intro hex hsep d
  obtain ⟨C, hC, h⟩ := hex d
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ L
  obtain ⟨g, hgn, ha⟩ := h 𝕜 L
  have hrep : Represents L g.val :=
    represents_of_atom_pairings L g.val g.property.1 (fun a =>
      ha a (AtomicHardySpace.atomElement volume a)
        (AtomicHardySpace.embedding_atomElement volume a))
  refine ⟨g, hrep, hgn, ?_⟩
  intro g' hrep'
  apply hsep d 𝕜 g.val g'.val g.property.1 g'.property.1
  intro a
  have he : AtomicHardySpaceSpec.EmbeddingValue volume
      (AtomicHardySpace.atomElement volume a) =
        ∑ b ∈ ({a} : Finset (Atom d 𝕜)), (1 : 𝕜) • b.val := by
    simp only [Finset.sum_singleton, one_smul,
      AtomicHardySpace.embedding_atomElement]
  have hp := (hrep {a} (fun _ => 1) (AtomicHardySpace.atomElement volume a) he).2
  have hp' := (hrep' {a} (fun _ => 1) (AtomicHardySpace.atomElement volume a) he).2
  simpa only [AtomicHardySpace.embedding_atomElement] using hp.symm.trans hp'

/-- Every bounded scalar-linear functional on atomic H¹ is represented by a
BMO function with the stated dimension bound, uniquely modulo constants. -/
theorem representation : Representation :=
  assemble_representation atomic_existence atom_separation

end ExpandedFA.Hardy.HardyDualBMORepresentation
