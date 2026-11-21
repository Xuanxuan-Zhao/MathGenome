import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.SmoothApproximationInC1
import MathGenome.Internal.MultivariableAnalysis.D04.C14.EuclideanSmoothCutoffs
import MathGenome.Internal.MultivariableAnalysis.D04.C08.FiniteRepeated
import MathGenome.Internal.MultivariableAnalysis.D04.C07.AffineComposition
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace D04.SmoothApproximationInC1
open Specs.D04.C14.SmoothApproximationInC1

def C1ApproximationOn : C1ApproximationOnType := C1ApproximationOnValue
def kernelAverage : kernelAverageType := kernelAverageValue
def translatedAverage : translatedAverageType := translatedAverageValue

/-- Multiplication by a cutoff gives a globally C¹ map, even though f has
no regularity assumption outside O. The equality holds on an open set,
so it also identifies the ambient derivatives there. -/
theorem compactly_supported_extension : compactly_supported_extensionType := by
  intro n m K O f hK hO hKO hf
  obtain ⟨χ, hχ⟩ := EuclideanSmoothCutoffs.exists_smooth_cutoff K O hK hO hKO
  obtain ⟨V, hV, hKV, hχV⟩ := hχ.2.2.2.1
  let g : E n → E m := fun x => χ x • f x
  have hg : ContDiff ℝ 1 g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport χ
    · exact (hχ.1.of_le (by simp)).contDiffAt.smul
        (hf.contDiffAt (hO.mem_nhds (hχ.2.2.2.2.2 hx)))
    · have he : g =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hx)] with y hy
        simp [g, hy]
      exact contDiffAt_const.congr_of_eventuallyEq he
  have he : EqOn g f V := by
    intro x hx
    simp [g, hχV hx]
  refine ⟨g, hg, ?_, V, hV, hKV, he, ?_⟩
  · exact hχ.2.2.2.2.1.of_isClosed_subset (isClosed_tsupport g)
      (tsupport_smul_subset_left χ f)
  · intro x hx
    have he' : g =ᶠ[𝓝 x] f := by
      filter_upwards [hV.mem_nhds hx] with y hy
      exact he hy
    exact he'.fderiv_eq

/-- Every finite derivative is obtained from the corresponding derivative of
the smooth kernel. Only continuity, not differentiability, of g is used. -/
theorem kernelAverage_smooth : kernelAverage_smoothType := by
  intro n m S η g hS hη hg
  let T : (j : ℕ) → closure S → E n → Differential (E n) (E m) j :=
    fun j y x => (iteratedFDeriv ℝ j η (x - y)).smulRight (g y)
  have hjet (j : ℕ) (y x : E n) :
      iteratedFDeriv ℝ j (fun z => η (z - y) • g y) x =
        (iteratedFDeriv ℝ j η (x - y)).smulRight (g y) := by
    have hs : ContDiff ℝ (j : ℕ∞ω) (fun z : E n => η (z - y)) :=
      contDiff_infty.mp (hη.comp (contDiff_id.sub contDiff_const)) j
    rw [iteratedFDeriv_smul_const_apply hs.contDiffAt,
      iteratedFDeriv_comp_sub]
    rfl
  have hcont (j : ℕ) : Continuous (fun z : closure S × (univ : Set (E n)) =>
      T j z.1 z.2) := by
    have hd : Continuous (fun z : closure S × (univ : Set (E n)) =>
        iteratedFDeriv ℝ j η ((z.2 : E n) - z.1)) :=
      (hη.continuous_iteratedFDeriv (by simp)).comp
        ((continuous_subtype_val.comp continuous_snd).sub
          (continuous_subtype_val.comp continuous_fst))
    exact ((ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin j => E n) (E m)).continuous.comp
      hd).clm_apply (hg.comp (continuous_subtype_val.comp continuous_fst))
  apply contDiff_infty.mpr
  intro r
  have hex : ∀ (y : S) (x : E n), x ∈ (univ : Set (E n)) →
      TimesDifferentiableAt r univ (fun z : E n => η (z - (y : E n)) • g y) x := by
    intro y x _
    apply crOn_timesDifferentiableAt r univ _ isOpen_univ _ x (mem_univ x)
    apply (crOn_iff_contDiffOn r univ _ isOpen_univ).mpr
    exact (contDiff_infty.mp
      ((hη.comp (contDiff_id.sub contDiff_const)).smul contDiff_const) r).contDiffOn
  have H := FiniteRepeated.finite_repeated hS isOpen_univ r
    (fun y : S => fun x : E n => η (x - (y : E n)) • g y) T hex
    (fun j _ => hcont j) (fun j _ y x _ => (hjet j y x).symm)
  exact contDiffOn_univ.mp ((crOn_iff_contDiffOn r univ _ isOpen_univ).mp H.2.1)

open JordanRegions ProperContinuity

lemma weighted_constant_integral {n m : ℕ} {S : Set (E n)}
    (hS : Jordan S) (η : E n → ℝ) (hη : Continuous η) (v : E m) :
    vectorRegionIntegral (fun z : S => η z • v) =
      regionIntegral (fun z : S => η z) • v := by
  have hi : RegionIntegrable (fun z : S => η z) := by
    have hv := continuous_closure_integrable hS
      (fun z : closure S => Darboux.scalarPoint (η z))
      ((PiLp.continuous_toLp 2 _).comp (continuous_pi (fun _ => hη.comp continuous_subtype_val)))
    exact hv.2 0
  ext i
  change regionIntegral (fun z : S => η z * v i) = regionIntegral (fun z : S => η z) * v i
  simpa only [mul_comm] using
    (SlicingAndMoments.region_smul (jordan_bounded hS) (fun z : S => η z) hi (v i)).2

/-- The translated-input integral is C¹, with the derivative obtained by
integrating Dg. No higher derivative of g is used in this presentation. -/
theorem translatedAverage_hasFDerivAt : translatedAverage_hasFDerivAtType := by
  intro n m S η g hS hη hg ε x
  let f : closure S → E n → E m := fun z p => η z • g (p - ε • (z : E n))
  let A : closure S → E n → E n →L[ℝ] E m :=
    fun z p => η z • fderiv ℝ g (p - ε • (z : E n))
  have hc : Continuous (fun z : closure S × (univ : Set (E n)) =>
      (z.2 : E n) - ε • (z.1 : E n)) :=
    (continuous_subtype_val.comp continuous_snd).sub
      ((continuous_subtype_val.comp continuous_fst).const_smul ε)
  have hf : Continuous (fun z : closure S × (univ : Set (E n)) => f z.1 z.2) :=
    (hη.comp (continuous_subtype_val.comp continuous_fst)).smul (hg.continuous.comp hc)
  have hA : Continuous (fun z : closure S × (univ : Set (E n)) => A z.1 z.2) :=
    (hη.comp (continuous_subtype_val.comp continuous_fst)).smul
      ((hg.continuous_fderiv (by norm_num)).comp hc)
  have hd : ∀ (z : S) (p : E n), p ∈ (univ : Set (E n)) →
      HasFDerivAt (f ⟨z, subset_closure z.property⟩)
        (A ⟨z, subset_closure z.property⟩ p) p := by
    intro z p _
    have h := (((hg.differentiable (by norm_num)) (p - ε • (z : E n))).hasFDerivAt.comp p
      ((hasFDerivAt_id p).sub_const (ε • (z : E n)))).const_smul (η z)
    exact h.congr_fderiv (by ext v; simp [A])
  exact (ProperDerivative.continuous_parameter_derivative hS isOpen_univ f A hf hA hd).2.2.2
    x (mem_univ x) |>.1

/-- Uniform continuity controls all translated samples simultaneously in x.
The estimate uses only bounded-region Riemann integral bounds. -/
theorem translatedAverage_tendsto : translatedAverage_tendstoType := by
  intro n m S η g hS hη hg hmass ε hε
  change regionIntegral (fun z : S => η z) = 1 at hmass
  obtain ⟨R, hR, hRS⟩ := (jordan_bounded hS).exists_pos_norm_lt
  obtain ⟨M, hM, hMS⟩ :=
    (((jordan_bounded hS).isCompact_closure.image hη).isBounded).exists_pos_norm_lt
  have hMb (z : S) : ‖η z‖ ≤ M :=
    (hMS _ ⟨z, subset_closure z.property, rfl⟩).le
  have hvol : 0 ≤ volume S := volume_nonneg hS
  apply Metric.tendstoUniformly_iff.mpr
  intro e he
  let t := e / (volume S * M + 1)
  have ht : 0 < t := div_pos he (by positivity)
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.mp hg t ht
  have hsmall := Metric.tendsto_nhds.mp hε (δ / (R + 1)) (div_pos hδ (by linarith))
  filter_upwards [hsmall] with j hj x
  have hdist (z : S) : dist (x - ε j • (z : E n)) x < δ := by
    have hz : ‖(z : E n)‖ < R := hRS _ z.property
    have heps : ‖ε j‖ < δ / (R + 1) := by simpa [dist_eq_norm] using hj
    rw [dist_eq_norm, show x - ε j • (z : E n) - x = -(ε j • (z : E n)) by abel,
      norm_neg, norm_smul]
    have hh := (lt_div_iff₀ (show 0 < R + 1 by linarith)).mp heps
    nlinarith [norm_nonneg (ε j)]
  have hint (a : ℝ) : VectorRegionIntegrable
      (fun z : S => η z • g (x - a • (z : E n))) :=
    continuous_closure_integrable hS _
      ((hη.comp continuous_subtype_val).smul
        (hg.continuous.comp (continuous_const.sub (continuous_subtype_val.const_smul a))))
  have hconst : VectorRegionIntegrable (fun z : S => η z • g x) :=
    continuous_closure_integrable hS _ ((hη.comp continuous_subtype_val).smul continuous_const)
  have hb (z : S) : ‖η z • g (x - ε j • (z : E n)) - η z • g x‖ ≤ M * t := by
    rw [← smul_sub, norm_smul]
    exact mul_le_mul (hMb z) (by simpa [dist_eq_norm] using (hδg (hdist z)).le)
      (norm_nonneg _) hM.le
  have hbound := integral_sub_le hS (hint (ε j)) hconst (mul_nonneg hM.le ht.le) hb
  rw [weighted_constant_integral hS η hη (g x), hmass, one_smul] at hbound
  have hlt : volume S * (M * t) < e := by
    have ht' : t * (volume S * M + 1) = e := div_mul_cancel₀ e (by positivity)
    nlinarith
  have hbound' : dist (g x) (Model.translatedAverage S η g (ε j) x) ≤ volume S * (M * t) := by
    simpa only [Model.translatedAverage, dist_eq_norm, norm_sub_rev] using hbound
  exact hbound'.trans_lt hlt

lemma box_isCompact {n : ℕ} (Q : Darboux.Box n) : IsCompact (Darboux.carrier Q) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨?_, Darboux.carrier_isBounded Q⟩
  exact NullCovers.isClosed_carrier Q

/-- A normalized compactly supported smooth kernel. Its normalization is an
ordinary Riemann integral, proved positive by a central Darboux cell. -/
lemma exists_normalized_kernel (n : ℕ) :
    ∃ (S : Set (E n)) (η : E n → ℝ), Jordan S ∧ ContDiff ℝ ∞ η ∧
      HasCompactSupport η ∧ tsupport η ⊆ S ∧
      regionIntegral (fun z : S => η z) = 1 := by
  classical
  let B : Darboux.Box n := ⟨0, WithLp.toLp 2 (fun _ => 1), fun _ => by norm_num⟩
  let C : Darboux.Box n := ⟨WithLp.toLp 2 (fun _ => -1), WithLp.toLp 2 (fun _ => 2),
    fun _ => by norm_num⟩
  have hBC : Darboux.carrier B ⊆ NullCovers.openCarrier C := by
    intro x hx i
    have hi := hx i
    change 0 ≤ x i ∧ x i ≤ 1 at hi
    change -1 < x i ∧ x i < 2
    constructor <;> linarith
  obtain ⟨χ, hχ⟩ := EuclideanSmoothCutoffs.exists_smooth_cutoff
    (Darboux.carrier B) (NullCovers.openCarrier C) (box_isCompact B)
    (NullCovers.isOpen_openCarrier C) hBC
  let S := Darboux.carrier C
  have hS : Jordan S := OneCoordinate.Boxes.jordan_carrier C
  have hsχ : tsupport χ ⊆ S := hχ.2.2.2.2.2.trans (NullCovers.openCarrier_subset C)
  have hzero : ∀ x, x ∉ S → χ x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hsχ h))
  have hext : zeroExtension (fun z : S => χ z) = χ := by
    funext x
    by_cases hx : x ∈ S
    · exact zeroExtension_apply _ ⟨x, hx⟩
    · rw [zeroExtension_of_not_mem _ hx, hzero x hx]
  let Q := enclosingBox S
  have hQ : Encloses S Q := enclosingBox_encloses (jordan_bounded hS)
  have h0 : (0 : E n) ∈ S := by intro i; change -1 ≤ (0 : ℝ) ∧ 0 ≤ 2; norm_num
  have h1 : WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ)) ∈ S := by
    intro i; change -1 ≤ (1 : ℝ) ∧ 1 ≤ 2; norm_num
  have hl (i : Fin n) : Q.lower i < 0 := by
    simpa using (encloses_open hQ (subset_closure h0) i).1
  have hu (i : Fin n) : 1 < Q.upper i := by
    exact (encloses_open hQ (subset_closure h1) i).2
  let P : Darboux.Grid Q := fun i => threePartition (Q.lower i) 0 1 (Q.upper i)
    (hl i) (by norm_num) (hu i)
  let c₀ : Darboux.CellIndex P := fun _ => (1 : Fin 3)
  have hcell : Darboux.cellBox P c₀ = B := by
    apply Darboux.Subdivision.box_ext <;> ext i <;> rfl
  have hχB : EqOn χ (fun _ => 1) (Darboux.carrier B) := by
    obtain ⟨V, _, hBV, he⟩ := hχ.2.2.2.1
    exact he.mono hBV
  have himage : χ '' Darboux.cell P c₀ = {1} := by
    change χ '' Darboux.carrier (Darboux.cellBox P c₀) = {1}
    rw [hcell, hχB.image_eq]
    exact (Darboux.carrier_nonempty B).image_const 1
  have hterm : Darboux.cellInfimum χ P c₀ * Darboux.cellContent P c₀ = 1 := by
    change sInf (χ '' Darboux.cell P c₀) * Darboux.content (Darboux.cellBox P c₀) = 1
    rw [himage, csInf_singleton, hcell]
    simp [Darboux.content, Specs.D04.C06.DarbouxIntegral.Model.content, B]
  have hsum : 1 ≤ Darboux.lowerSum χ P := by
    rw [← hterm]
    change _ ≤ ∑ c, Darboux.cellInfimum χ P c * Darboux.cellContent P c
    apply Finset.single_le_sum (f := fun c : Darboux.CellIndex P =>
      Darboux.cellInfimum χ P c * Darboux.cellContent P c) (fun c _ => ?_) (Finset.mem_univ c₀)
    exact mul_nonneg (le_csInf (Darboux.cell_nonempty P c |>.image χ)
      (fun _ ⟨x, _, he⟩ => he ▸ (hχ.2.2.1 x).1)) (Darboux.cellContent_nonneg P c)
  have hi := SlicingAndMoments.continuous_box_integrable χ hχ.1.continuous Q
  have hpos : 0 < regionIntegral (fun z : S => χ z) := by
    change 0 < Darboux.lowerIntegral (zeroExtension (fun z : S => χ z)) Q
    rw [hext]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (hsum.trans ((Darboux.lowerIntegral_isLUB χ Q hi.1).1 ⟨P, rfl⟩))
  let a := regionIntegral (fun z : S => χ z)
  refine ⟨S, fun x => a⁻¹ * χ x, hS, contDiff_const.mul hχ.1,
    (show HasCompactSupport χ from hχ.2.2.2.2.1).mul_left, ?_, ?_⟩
  · exact tsupport_mul_subset_right.trans hsχ
  · rw [(SlicingAndMoments.region_smul (jordan_bounded hS) (fun z : S => χ z)
        ((continuous_closure_integrable hS
          (fun z : closure S => Darboux.scalarPoint (χ z))
          ((PiLp.continuous_toLp 2 _).comp
            (continuous_pi (fun _ => hχ.1.continuous.comp continuous_subtype_val)))).2 0) a⁻¹).2]
    exact inv_mul_cancel₀ hpos.ne'

lemma wholeIntegral_eq_region {n : ℕ} (S : Set (E n)) (hS : Jordan S)
    (f : E n → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hs : Function.support f ⊆ S) :
    AffineComposition.wholeIntegral f = regionIntegral (fun z : S => f z) := by
  have hfU := Localization.compact_support_integrable
    (fun z : (univ : Set (E n)) => f z) isOpen_univ
    (hf.comp continuous_subtype_val) (hfc.comp_isClosedEmbedding
      (isClosed_univ.isClosedEmbedding_subtypeVal))
  have hfS : RegionIntegrable (fun z : S => f z) := by
    have hv := continuous_closure_integrable hS
      (fun z : closure S => Darboux.scalarPoint (f z))
      ((PiLp.continuous_toLp 2 _).comp
        (continuous_pi (fun _ => hf.comp continuous_subtype_val)))
    exact hv.2 0
  apply OneCoordinate.open_eq_region _ _ hfU.2 hfS
  rw [AffineComposition.zeroExtension_univ]
  ext x
  by_cases hx : x ∈ S
  · exact (zeroExtension_apply (fun z : S => f z) ⟨x, hx⟩).symm
  · rw [zeroExtension_of_not_mem _ hx]
    exact Function.notMem_support.mp (fun h => hx (hs h))

set_option maxHeartbeats 1000000 in
/-- Affine Riemann substitution identifies the translated-input average with
a smooth kernel average over a fixed box containing the support of g.
No manifold integration or Stokes theorem is involved. -/
lemma translatedAverage_smooth {n m : ℕ} (S : Set (E n)) (η : E n → ℝ)
    (g : E n → E m) (hS : Jordan S) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hsη : tsupport η ⊆ S)
    (hg : Continuous g) (hgc : HasCompactSupport g) (ε : ℝ) (hε : ε ≠ 0) :
    ContDiff ℝ ∞ (translatedAverage S η g ε) := by
  classical
  let A : Matrix (Fin n) (Fin n) ℝ := (-ε) • 1
  have hA : A.det ≠ 0 := by
    change ((-ε) • (1 : Matrix (Fin n) (Fin n) ℝ)).det ≠ 0
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (neg_ne_zero.mpr hε)
  let J := |A.det|
  have hJ : J ≠ 0 := abs_ne_zero.mpr hA
  let κ : E n → ℝ := fun w => J⁻¹ * η (ε⁻¹ • w)
  have hκ : ContDiff ℝ ∞ κ := contDiff_const.mul (hη.comp (contDiff_id.const_smul _))
  let Y := Darboux.carrier (enclosingBox (tsupport g))
  have hY : Jordan Y := OneCoordinate.Boxes.jordan_carrier _
  have hsY : tsupport g ⊆ Y := encloses_subset (enclosingBox_encloses hgc.isBounded)
  have hlin (z : E n) : matrixLinearEquiv n n A z = -ε • z := by
    ext i
    simp [A, matrix_apply, Matrix.one_apply, PiLp.smul_apply]
  have heq : translatedAverage S η g ε = kernelAverage Y κ g := by
    funext x
    ext i
    let H := (AffineComposition.matrixEquiv A hA).toHomeomorph.trans (Homeomorph.addRight x)
    have hH (z : E n) : H z = x - ε • z := by
      change matrixLinearEquiv n n A z + x = _
      rw [hlin]
      simp only [neg_smul, sub_eq_add_neg, add_comm]
    let f : E n → ℝ := fun y => κ (x - y) * g y i
    have hgic : HasCompactSupport (fun y : E n => g y i) :=
      hgc.comp_left (g := fun v : E m => v i) rfl
    have hfc : HasCompactSupport f := hgic.mul_left (f := fun y => κ (x - y))
    have hfc' : Continuous f :=
      (hκ.continuous.comp (continuous_const.sub continuous_id)).mul
        ((PiLp.continuous_apply 2 _ i).comp hg)
    have hsF : Function.support f ⊆ Y := by
      intro y hy
      by_contra hyY
      have hyG : y ∉ tsupport g := fun h => hyY (hsY h)
      exact hy (by simp [f, image_eq_zero_of_notMem_tsupport hyG])
    have hsub := AffineComposition.global_comp
      (AffineComposition.global_linear A hA) (AffineComposition.global_translation x)
      f hfc' hfc
    change AffineComposition.wholeIntegral f =
      AffineComposition.wholeIntegral (fun z => f (H z) * (1 * |A.det|)) at hsub
    have hfg (z : E n) : f (H z) * (1 * |A.det|) = η z * g (x - ε • z) i := by
      rw [hH]
      dsimp [f, κ]
      rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hε, one_smul]
      change J⁻¹ * η z * g (x - ε • z) i * (1 * J) = _
      field_simp [hJ]
    have ht : Continuous (fun z : E n => η z * g (x - ε • z) i) :=
      hη.continuous.mul ((PiLp.continuous_apply 2 _ i).comp
        (hg.comp (continuous_const.sub (continuous_id.const_smul ε))))
    have htc : HasCompactSupport (fun z : E n => η z * g (x - ε • z) i) := hηc.mul_right
    have hts : Function.support (fun z : E n => η z * g (x - ε • z) i) ⊆ S := by
      intro z hz
      apply hsη
      apply subset_tsupport η
      intro he
      exact hz (by simp [he])
    rw [funext hfg, wholeIntegral_eq_region Y hY f hfc' hfc hsF,
      wholeIntegral_eq_region S hS _ ht htc hts] at hsub
    exact hsub.symm
  rw [heq]
  exact kernelAverage_smooth Y κ g hY hκ hg

lemma translatedAverage_fderiv_error {n m : ℕ} {S : Set (E n)}
    (hS : Jordan S) (η : E n → ℝ) (hη : Continuous η) (g : E n → E m)
    (hg : ContDiff ℝ 1 g) (hmass : regionIntegral (fun z : S => η z) = 1)
    (ε : ℝ) (x : E n) (M t : ℝ) (hM : 0 ≤ M) (ht : 0 ≤ t)
    (hηM : ∀ z : S, ‖η z‖ ≤ M)
    (hmod : ∀ z : S, ‖fderiv ℝ g (x - ε • (z : E n)) - fderiv ℝ g x‖ ≤ t) :
    ‖fderiv ℝ (translatedAverage S η g ε) x - fderiv ℝ g x‖ ≤ volume S * (M * t) := by
  let A : S → E n →L[ℝ] E m := fun z => η z • fderiv ℝ g (x - ε • (z : E n))
  have hDc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hi (v : E n) : VectorRegionIntegrable (fun z : S => A z v) := by
    apply continuous_closure_integrable hS
      (fun z : closure S => (η z • fderiv ℝ g (x - ε • (z : E n))) v)
    exact ((hη.comp continuous_subtype_val).smul
      (hDc.comp (continuous_const.sub (continuous_subtype_val.const_smul ε)))).clm_apply
        continuous_const
  have hAi : ProperDerivative.OperatorRegionIntegrable A :=
    ⟨jordan_bounded hS, fun i => hi (standardBasis n i)⟩
  have hd := (translatedAverage_hasFDerivAt S η g hS hη hg ε x).fderiv
  change fderiv ℝ (translatedAverage S η g ε) x = ProperDerivative.operatorRegionIntegral A at hd
  rw [hd]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (volume_nonneg hS) (mul_nonneg hM ht))
  intro v
  have hci : VectorRegionIntegrable (fun z : S => η z • fderiv ℝ g x v) :=
    continuous_closure_integrable hS _ ((hη.comp continuous_subtype_val).smul continuous_const)
  have hb (z : S) : ‖A z v - η z • fderiv ℝ g x v‖ ≤ M * t * ‖v‖ := by
    change ‖η z • (fderiv ℝ g (x - ε • (z : E n))) v - η z • fderiv ℝ g x v‖ ≤ _
    rw [← smul_sub, norm_smul]
    have hgv : ‖fderiv ℝ g (x - ε • (z : E n)) v - fderiv ℝ g x v‖ ≤ t * ‖v‖ :=
      (fderiv ℝ g (x - ε • (z : E n)) - fderiv ℝ g x).le_opNorm v |>.trans
        (mul_le_mul_of_nonneg_right (hmod z) (norm_nonneg v))
    exact (mul_le_mul (hηM z) hgv (norm_nonneg _) hM).trans_eq (mul_assoc _ _ _).symm
  have hbnd := integral_sub_le hS (hi v) hci (mul_nonneg (mul_nonneg hM ht) (norm_nonneg v)) hb
  rw [weighted_constant_integral hS η hη (fderiv ℝ g x v), hmass, one_smul] at hbnd
  rw [sub_apply, (ProperDerivative.integral_apply A hAi v).2]
  exact hbnd.trans_eq (mul_assoc _ _ _).symm

/-- Compact support makes the continuous derivative uniformly continuous.
The preceding operator estimate then yields uniform derivative convergence. -/
theorem translatedAverage_fderiv_tendsto : translatedAverage_fderiv_tendstoType := by
  intro n m S η g hS hη hg hgc hmass ε hε
  change regionIntegral (fun z : S => η z) = 1 at hmass
  have hDuc : UniformContinuous (fderiv ℝ g) :=
    (hgc.fderiv ℝ).uniformContinuous_of_continuous (hg.continuous_fderiv (by norm_num))
  obtain ⟨R, hR, hRS⟩ := (jordan_bounded hS).exists_pos_norm_lt
  obtain ⟨M, hM, hMS⟩ :=
    (((jordan_bounded hS).isCompact_closure.image hη).isBounded).exists_pos_norm_lt
  have hMb (z : S) : ‖η z‖ ≤ M :=
    (hMS _ ⟨z, subset_closure z.property, rfl⟩).le
  have hvol : 0 ≤ volume S := volume_nonneg hS
  apply Metric.tendstoUniformly_iff.mpr
  intro e he
  let t := e / (volume S * M + 1)
  have ht : 0 < t := div_pos he (by positivity)
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.mp hDuc t ht
  have hsmall := Metric.tendsto_nhds.mp hε (δ / (R + 1)) (div_pos hδ (by linarith))
  filter_upwards [hsmall] with j hj x
  have hdist (z : S) : dist (x - ε j • (z : E n)) x < δ := by
    have hz : ‖(z : E n)‖ < R := hRS _ z.property
    have heps : ‖ε j‖ < δ / (R + 1) := by simpa [dist_eq_norm] using hj
    rw [dist_eq_norm, show x - ε j • (z : E n) - x = -(ε j • (z : E n)) by abel,
      norm_neg, norm_smul]
    have hh := (lt_div_iff₀ (show 0 < R + 1 by linarith)).mp heps
    nlinarith [norm_nonneg (ε j)]
  have hbound := translatedAverage_fderiv_error hS η hη g hg hmass (ε j) x M t hM.le ht.le hMb
    (fun z => by simpa only [dist_eq_norm] using (hδg (hdist z)).le)
  have hlt : volume S * (M * t) < e := by
    have ht' : t * (volume S * M + 1) = e := div_mul_cancel₀ e (by positivity)
    nlinarith
  have hbound' : dist (fderiv ℝ g x)
      (fderiv ℝ (Model.translatedAverage S η g (ε j)) x) ≤ volume S * (M * t) := by
    simpa only [translatedAverage, translatedAverageValue, dist_eq_norm, norm_sub_rev] using hbound
  exact hbound'.trans_lt hlt

lemma uniformOn_sup_norm_tendsto {X Y : Type} [NormedAddCommGroup Y]
    {K : Set X} {F : ℕ → X → Y} {f : X → Y} (hne : K.Nonempty)
    (hb : ∀ j, BddAbove ((fun x => ‖F j x - f x‖) '' K))
    (hF : TendstoUniformlyOn F f atTop K) :
    Tendsto (fun j => sSup ((fun x => ‖F j x - f x‖) '' K)) atTop (𝓝 0) := by
  obtain ⟨x₀, hx₀⟩ := hne
  apply Metric.tendsto_nhds.mpr
  intro e he
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hF) (e / 2) (half_pos he)] with j hj
  have hnonneg : 0 ≤ sSup ((fun x => ‖F j x - f x‖) '' K) :=
    (norm_nonneg _).trans (le_csSup (hb j) ⟨x₀, hx₀, rfl⟩)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  have himg : ((fun x => ‖F j x - f x‖) '' K).Nonempty :=
    ⟨‖F j x₀ - f x₀‖, x₀, hx₀, rfl⟩
  have hupper : sSup ((fun x => ‖F j x - f x‖) '' K) ≤ e / 2 := by
    apply csSup_le himg
    rintro _ ⟨x, hx, rfl⟩
    simpa only [dist_eq_norm, norm_sub_rev] using (hj x hx).le
  exact hupper.trans_lt (half_lt_self he)

theorem smooth_approximation_in_C1 : smooth_approximation_in_C1Type := by
  intro n m Q O f hO hQ hf
  have hfc : ContDiffOn ℝ 1 f O := (crOn_iff_contDiffOn 1 O f hO).mp hf
  obtain ⟨g, hg, hgc, V, hV, hQV, hgf, hDgf⟩ :=
    compactly_supported_extension (Darboux.carrier Q) O f (box_isCompact Q) hO hQ hfc
  obtain ⟨S, η, hS, hη, hηc, hsη, hmass⟩ := exists_normalized_kernel n
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεne (j : ℕ) : ε j ≠ 0 := by dsimp [ε]; positivity
  let F : ℕ → E n → E m := fun j => translatedAverage S η g (ε j)
  have hFs (j : ℕ) : ContDiff ℝ ∞ (F j) :=
    translatedAverage_smooth S η g hS hη hηc hsη hg.continuous hgc (ε j) (hεne j)
  have hG := translatedAverage_tendsto S η g hS hη.continuous
    (hgc.uniformContinuous_of_continuous hg.continuous) hmass ε hε
  have hDG := translatedAverage_fderiv_tendsto S η g hS hη.continuous hg hgc hmass ε hε
  have hval : TendstoUniformlyOn F f atTop (Darboux.carrier Q) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro e he
    filter_upwards [(Metric.tendstoUniformly_iff.mp hG) e he] with j hj x hx
    rw [← hgf (hQV hx)]
    exact hj x
  have hder : TendstoUniformlyOn (fun j => fderiv ℝ (F j)) (fderiv ℝ f)
      atTop (Darboux.carrier Q) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro e he
    filter_upwards [(Metric.tendstoUniformly_iff.mp hDG) e he] with j hj x hx
    rw [← hDgf (hQV hx)]
    exact hj x
  refine ⟨F, ?_, hval, hder, ?_, ?_⟩
  · intro j
    exact ⟨univ, isOpen_univ, subset_univ _,
      (hFs j).contDiffOn⟩
  · apply uniformOn_sup_norm_tendsto (Darboux.carrier_nonempty Q) _ hval
    intro j
    exact ((box_isCompact Q).image_of_continuousOn
      (((hFs j).continuous.continuousOn.sub (hfc.continuousOn.mono hQ)).norm)).bddAbove
  · apply uniformOn_sup_norm_tendsto (Darboux.carrier_nonempty Q) _ hder
    intro j
    exact ((box_isCompact Q).image_of_continuousOn
      ((((hFs j).continuous_fderiv (by simp)).continuousOn.sub
        ((hfc.continuousOn_fderiv_of_isOpen hO le_rfl).mono hQ)).norm)).bddAbove

end D04.SmoothApproximationInC1
