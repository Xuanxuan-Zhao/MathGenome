import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.TraceEndpointOne
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevTraceAndKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevCompleteness
import Mathlib.Analysis.Normed.Group.ControlledClosure
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal

namespace ExpandedFA.PartIV.TraceEndpointOne
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Lines ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Trace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (i : Fin d)

/-- Smooth restriction determines the existing continuous half-space trace. -/
theorem flat_trace_unique (T S : HalfSpaceW11 𝕜 i →L[𝕜] FlatL1 𝕜 i)
    (hT : IsFlatTrace i T) (hS : IsFlatTrace i S) : T = S := by
  have heq : EqOn T S (C1Extension.SmoothUpToBoundary (𝕜 := 𝕜) (upper i) 1) := by
    rintro u ⟨f, hf, hu⟩
    exact Lp.ext ((hT u f hf hu).trans (hS u f hf hu).symm)
  apply ContinuousLinearMap.ext
  intro u
  exact heq.closure T.continuous S.continuous
    (coordinate_upper_smooth_density (𝕜 := 𝕜) i (by norm_num) u)

/-- This uses the accepted trace construction, not an assumed certificate. -/
theorem flat_trace_exists :
    ∃! T : HalfSpaceW11 𝕜 i →L[𝕜] FlatL1 𝕜 i, IsFlatTrace i T := by
  obtain ⟨T, hT, _⟩ := coordinate_upper_trace_exists (𝕜 := 𝕜) i (p := 1) (by norm_num)
  have ht : IsFlatTrace i T := fun u f hf hu => hT u f (hf.of_le (by simp)) hu
  exact ⟨T, ht, fun S hS => flat_trace_unique i S T hS ht⟩

/-- Zero is extended by the zero Sobolev class. -/
theorem zero_datum_extension (T : HalfSpaceW11 𝕜 i →L[𝕜] FlatL1 𝕜 i) :
    ∃ u : HalfSpaceW11 𝕜 i, T u = 0 := ⟨0, map_zero T⟩

/-- Compactly supported smooth boundary classes form a dense subspace. -/
def compactSmoothBoundary : Submodule 𝕜 (FlatL1 𝕜 i) where
  carrier := {g | ∃ f : Transverse i → 𝕜,
    g =ᵐ[volume] f ∧ HasCompactSupport f ∧ ContDiff ℝ (⊤ : ℕ∞) f}
  zero_mem' := ⟨0, Lp.coeFn_zero _ _ _, HasCompactSupport.zero, contDiff_const⟩
  add_mem' := by
    rintro u v ⟨f, huf, hfc, hfd⟩ ⟨g, hvg, hgc, hgd⟩
    refine ⟨f + g, ?_, hfc.add hgc, hfd.add hgd⟩
    filter_upwards [Lp.coeFn_add u v, huf, hvg] with x hx hfx hgx
    simp only [hx, Pi.add_apply, hfx, hgx]
  smul_mem' := by
    rintro c u ⟨f, huf, hfc, hfd⟩
    refine ⟨c • f, ?_, hfc.smul_left (f := fun _ => c), contDiff_const.smul hfd⟩
    filter_upwards [Lp.coeFn_smul c u, huf] with x hx hfx
    simp only [hx, Pi.smul_apply, hfx]

theorem compactSmoothBoundary_dense :
    Dense (compactSmoothBoundary (𝕜 := 𝕜) i : Set (FlatL1 𝕜 i)) := by
  exact Lp.dense_hasCompactSupport_contDiff (by norm_num)

/-- A uniformly bounded, possibly nonlinear lifting on smooth boundary
classes extends to every L1 datum by a convergent series. Only the source
space must be complete. This does not construct a linear right inverse. -/
theorem surjective_of_smooth_lifts
    (T : HalfSpaceW11 𝕜 i →L[𝕜] FlatL1 𝕜 i) {C : ℝ} (hC : 0 < C)
    (hlift : ∀ g ∈ compactSmoothBoundary (𝕜 := 𝕜) i,
      ∃ u : HalfSpaceW11 𝕜 i, T u = g ∧ ‖u‖ ≤ C * ‖g‖) :
    Function.Surjective T := by
  let : CompleteSpace (HalfSpaceW11 𝕜 i) := sobolev_complete 𝕜 d (upper i) 1 1
  let f : NormedAddGroupHom (HalfSpaceW11 𝕜 i) (FlatL1 𝕜 i) :=
    T.toLinearMap.toAddMonoidHom.mkNormedAddGroupHom ‖T‖ T.le_opNorm
  let K : AddSubgroup (FlatL1 𝕜 i) := (compactSmoothBoundary (𝕜 := 𝕜) i).toAddSubgroup
  have hclosure : (K.topologicalClosure : Set (FlatL1 𝕜 i)) = univ := by
    change closure (compactSmoothBoundary (𝕜 := 𝕜) i : Set (FlatL1 𝕜 i)) = univ
    exact (compactSmoothBoundary_dense (𝕜 := 𝕜) i).closure_eq
  have h := controlled_closure_of_complete (f := f) (K := K) hC (show (0 : ℝ) < 1 by norm_num) hlift
  intro g
  obtain ⟨u, hu, _⟩ := h g (by change g ∈ (K.topologicalClosure : Set _); rw [hclosure]; trivial)
  exact ⟨u, hu⟩

/-- Once the quantitative smooth lifting is supplied, uniqueness ties the
surjectivity assertion to the trace already constructed upstream. -/
theorem onto_trace_exists_of_surjectivity
    (honto : Specs.ExpandedFA.PartIV.TraceEndpointOne.Surjectivity) :
    Specs.ExpandedFA.PartIV.TraceEndpointOne.OntoTraceExists := by
  intro 𝕜 _ d i
  obtain ⟨T, hT, huniq⟩ := flat_trace_exists (𝕜 := 𝕜) i
  exact ⟨T, ⟨hT, honto 𝕜 d i T hT⟩, fun S hS => huniq S hS.1⟩



/-- Normal compression reduces mass without increasing total variation. -/
theorem thin_profiles : ∃ B ≥ (0 : ℝ), ∀ ε > (0 : ℝ), ∃ b : ℝ → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧ b 0 = 1 ∧
    (∫ t, ‖b t‖) ≤ ε ∧ (∫ t, ‖deriv b t‖) ≤ B := by
  let η : ContDiffBump (0 : ℝ) := default
  have hηSmooth : ContDiff ℝ (⊤ : ℕ∞) (η : ℝ → ℝ) := η.contDiff
  let A : ℝ := ∫ t, ‖η t‖
  let B : ℝ := ∫ t, ‖deriv η t‖
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  refine ⟨B, hB, fun ε hε => ?_⟩
  let δ := ε / (A + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  let b : ℝ → ℝ := fun t => η (δ⁻¹ * t)
  have hb : ContDiff ℝ (⊤ : ℕ∞) b :=
    η.contDiff.comp (contDiff_const.mul contDiff_id)
  have hbc : HasCompactSupport b := by
    exact η.hasCompactSupport.comp_homeomorph
      (Homeomorph.smul (Units.mk0 δ⁻¹ (inv_ne_zero hδ.ne')))
  have hderiv : ∀ t, deriv b t = δ⁻¹ * deriv η (δ⁻¹ * t) := by
    intro t
    have hη : HasDerivAt (η : ℝ → ℝ) (deriv η (δ⁻¹ * t)) (δ⁻¹ * t) :=
      (hηSmooth.differentiable (by simp) _).hasDerivAt
    have hh := hη.comp t
      ((hasDerivAt_id t).const_mul δ⁻¹)
    simpa only [b, Function.comp_def, mul_one, one_mul, mul_comm] using hh.deriv
  have hInt : (∫ t, ‖b t‖) = δ * A := by
    have hh := Measure.integral_comp_smul volume (fun t : ℝ => ‖η t‖) δ⁻¹
    simpa [b, A, Module.finrank_self, abs_of_pos hδ, smul_eq_mul] using hh
  have hdInt : (∫ t, ‖deriv b t‖) = B := by
    simp_rw [hderiv, norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hδ]
    rw [integral_const_mul]
    have hh := Measure.integral_comp_smul volume (fun t : ℝ => |deriv η t|) δ⁻¹
    simp only [Module.finrank_self, pow_one, inv_inv, abs_of_pos hδ, smul_eq_mul] at hh
    rw [hh, ← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]
    rfl
  refine ⟨b, hb, hbc, ?_, ?_, hdInt.le⟩
  · exact η.one_of_mem_closedBall (by simp [Metric.mem_closedBall, η.rIn_pos.le])
  · rw [hInt]
    dsimp [δ]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < A + 1)]
    nlinarith

/-- The transverse coordinate projection has norm at most one. -/
def transverseProjection : Domain d →L[ℝ] Transverse i :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj j.val

lemma transverseProjection_norm_le (x : Domain d) :
    ‖transverseProjection i x‖ ≤ ‖x‖ := by
  exact pi_norm_le_iff_of_nonneg (norm_nonneg x) |>.mpr
    fun j => norm_le_pi_norm x j.val

lemma transverseProjection_coordinateLine (y : Transverse i) (t : ℝ) :
    transverseProjection i (coordinateLine i y t) = y := by
  ext j
  exact coordinateLine_transverse i y t j

lemma tensor_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ → ℝ) (f : Transverse i → E)
    (ha : Integrable a) (hf : Integrable f) :
    Integrable (fun x : Domain d => a (x i) • f (transverseProjection i x)) := by
  have h := ha.smul_prod hf
  have hm : MeasurePreserving (coordinateEquiv i) volume
      ((volume : Measure ℝ).prod (volume : Measure (Transverse i))) :=
    coordinateEquiv_measurePreserving i
  exact hm.integrable_comp_of_integrable h

lemma tensor_norm_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ → ℝ) (f : Transverse i → E) :
    (∫ x : Domain d, ‖a (x i) • f (transverseProjection i x)‖) =
      (∫ t, ‖a t‖) * ∫ y, ‖f y‖ := by
  simp_rw [norm_smul]
  have hm : MeasurePreserving (coordinateEquiv i) volume
      ((volume : Measure ℝ).prod (volume : Measure (Transverse i))) :=
    coordinateEquiv_measurePreserving i
  exact (hm.integral_comp' (fun z : ℝ × Transverse i => ‖a z.1‖ * ‖f z.2‖)).trans
    (integral_prod_mul (fun t : ℝ => ‖a t‖) (fun y : Transverse i => ‖f y‖))

/-- The derivative estimate deliberately bounds every direction by the same
sum; no dimension-dependent anisotropic norm identification is required. -/
lemma tensor_derivative_bound (a : ℝ → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (f : Transverse i → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x : Domain d) (j : Fin d) :
    ‖fderiv ℝ (fun x : Domain d => a (x i) • f (transverseProjection i x)) x
      (coordinateVector j)‖ ≤
      ‖a (x i)‖ * ‖fderiv ℝ f (transverseProjection i x)‖ +
        ‖deriv a (x i)‖ * ‖f (transverseProjection i x)‖ := by
  let P := transverseProjection i
  let q : Domain d →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hq := (ha.differentiable (by simp) (x i)).hasDerivAt.comp_hasFDerivAt x q.hasFDerivAt
  have hP := (hf.differentiable (by simp) (P x)).hasFDerivAt.comp x P.hasFDerivAt
  have hF := hq.smul hP
  change ‖fderiv ℝ ((a ∘ q) • (f ∘ P)) x (coordinateVector j)‖ ≤ _
  rw [hF.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply]
  apply (norm_add_le _ _).trans
  have hv : ‖coordinateVector j‖ ≤ (1 : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro k
    classical
    by_cases h : k = j <;> simp [coordinateVector, h]
  have hPv : ‖P (coordinateVector j)‖ ≤ 1 :=
    (transverseProjection_norm_le i _).trans hv
  have hqv : ‖q (coordinateVector j)‖ ≤ 1 := (norm_le_pi_norm _ i).trans hv
  rw [norm_smul, norm_smul]
  apply add_le_add
  · have hh := (fderiv ℝ f (P x)).le_opNorm (P (coordinateVector j))
    have hh2 : ‖fderiv ℝ f (P x)‖ * ‖P (coordinateVector j)‖ ≤ ‖fderiv ℝ f (P x)‖ :=
      mul_le_of_le_one_right (norm_nonneg _) hPv
    exact mul_le_mul_of_nonneg_left (hh.trans hh2) (norm_nonneg _)
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (norm_nonneg _) hqv) (norm_nonneg _)

lemma lp_one_norm {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] (u : Lp E 1 μ) : ‖u‖ = ∫ x, ‖u x‖ ∂μ := by
  rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable u)]
  exact (integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable u)).symm

/-- Smooth tensor functions define genuine Sobolev graph elements, with an
L1 estimate that keeps the normal and tangential costs separate. -/
lemma smooth_tensor_lift (a : ℝ → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hac : HasCompactSupport a)
    (f : Transverse i → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    ∃ u : SpaceValue 𝕜 d (upper i) 1 1,
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
        (fun x => a (x i) • f (transverseProjection i x)) ∧
      ‖u‖ ≤ (Fintype.card (DerivativeIndex d 1) : ℝ) *
        ((∫ t, ‖a t‖) * ((∫ y, ‖f y‖) + ∫ y, ‖fderiv ℝ f y‖) +
          (∫ t, ‖deriv a t‖) * ∫ y, ‖f y‖) := by
  let F : Domain d → 𝕜 := fun x => a (x i) • f (transverseProjection i x)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (ha.comp (ContinuousLinearMap.proj i : Domain d →L[ℝ] ℝ).contDiff).smul (hf.comp (transverseProjection i).contDiff)
  have hai : Integrable a := ha.continuous.integrable_of_hasCompactSupport hac
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfc
  have hadi : Integrable (deriv a) :=
    (ha.continuous_deriv (by simp)).integrable_of_hasCompactSupport hac.deriv
  have hfdi : Integrable (fderiv ℝ f) :=
    (hf.continuous_fderiv (by simp)).integrable_of_hasCompactSupport (hfc.fderiv ℝ)
  have hFi : Integrable F := tensor_integrable i a f hai hfi
  let M : Domain d → ℝ := fun x =>
    ‖a (x i)‖ * ‖fderiv ℝ f (transverseProjection i x)‖ +
      ‖deriv a (x i)‖ * ‖f (transverseProjection i x)‖
  have hM1 := tensor_integrable i (fun t => ‖a t‖) (fun y => ‖fderiv ℝ f y‖) hai.norm hfdi.norm
  have hM2 := tensor_integrable i (fun t => ‖deriv a t‖) (fun y => ‖f y‖) hadi.norm hfi.norm
  have hMi : Integrable M := hM1.add hM2
  have hDi : ∀ j, Integrable (fun x => fderiv ℝ F x (coordinateVector j)) := by
    intro j
    apply hMi.mono' ((hF.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
    exact ae_of_all _ (fun x => tensor_derivative_bound i a ha f hf x j)
  obtain ⟨u, hu, hdu⟩ := C1Extension.Classical.c1_mem_sobolev F
    (hF.of_le (by simp)).contDiffOn (memLp_one_iff_integrable.mpr hFi.restrict) (fun j => (memLp_one_iff_integrable.mpr (hDi j).restrict))
  refine ⟨u, hu, ?_⟩
  let A := ∫ t, ‖a t‖
  let B := ∫ t, ‖deriv a t‖
  let G := ∫ y, ‖f y‖
  let D := ∫ y, ‖fderiv ℝ f y‖
  have hMInt : (∫ x, M x) = A * D + B * G := by
    change (∫ x : Domain d, ‖a (x i)‖ • ‖fderiv ℝ f (transverseProjection i x)‖ +
      ‖deriv a (x i)‖ • ‖f (transverseProjection i x)‖) = _
    rw [integral_add hM1 hM2]
    have h1 := tensor_norm_integral i a (fderiv ℝ f)
    have h2 := tensor_norm_integral i (deriv a) f
    simpa only [norm_smul, smul_eq_mul, A, B, G, D] using congrArg₂ (· + ·) h1 h2
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  have hG : 0 ≤ G := integral_nonneg fun _ => norm_nonneg _
  have hD : 0 ≤ D := integral_nonneg fun _ => norm_nonneg _
  have hzero : ‖u.val (zeroIndex d 1)‖ ≤ A * (G + D) + B * G := by
    rw [lp_one_norm, integral_congr_ae (hu.mono fun x hx => congrArg norm hx)]
    apply le_trans (integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ fun _ => norm_nonneg _) hFi.norm)
    change (∫ x : Domain d, ‖a (x i) • f (transverseProjection i x)‖) ≤ _
    rw [tensor_norm_integral]
    dsimp [A, B, G, D] at *
    nlinarith
  have hcoord : ∀ j, ‖u.val (coordinateIndex j)‖ ≤ A * (G + D) + B * G := by
    intro j
    rw [lp_one_norm, integral_congr_ae ((hdu j).mono fun x hx => congrArg norm hx)]
    apply le_trans (integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ fun _ => norm_nonneg _) (hDi j).norm)
    apply le_trans (integral_mono (hDi j).norm hMi (fun x => tensor_derivative_bound i a ha f hf x j))
    rw [hMInt]
    nlinarith
  rw [sobolev_norm_formula]
  calc
    (∑ α : DerivativeIndex d 1, ‖u.val α‖) ≤
        ∑ _α : DerivativeIndex d 1, (A * (G + D) + B * G) := by
      apply Finset.sum_le_sum
      intro α _
      rcases multiIndex_order_one_cases (natIndex α) α.property with hz | ⟨j, hj⟩
      · have heq : α = zeroIndex d 1 := derivativeIndex_ext hz
        simpa only [heq] using hzero
      · have heq : α = coordinateIndex j := derivativeIndex_ext (by simpa [coordinateIndex] using hj)
        simpa only [heq] using hcoord j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; rfl


/-- Uniformly bounded lifts of smooth boundary classes. The width of the
normal profile depends on the datum's tangential derivatives. -/
theorem smooth_lifts (T : HalfSpaceW11 𝕜 i →L[𝕜] FlatL1 𝕜 i)
    (hT : IsFlatTrace i T) :
    ∃ C > (0 : ℝ), ∀ g ∈ compactSmoothBoundary (𝕜 := 𝕜) i,
      ∃ u : HalfSpaceW11 𝕜 i, T u = g ∧ ‖u‖ ≤ C * ‖g‖ := by
  obtain ⟨B, hB, hprofiles⟩ := thin_profiles
  let N : ℝ := Fintype.card (DerivativeIndex d 1)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨zeroIndex d 1⟩
  refine ⟨N * (B + 1), mul_pos hN (by positivity), ?_⟩
  intro g hg
  by_cases hgz : g = 0
  · subst g
    exact ⟨0, map_zero T, by simp⟩
  obtain ⟨f, hgf, hfc, hfd⟩ := hg
  have hgn : 0 < ‖g‖ := norm_pos_iff.mpr hgz
  let D := ∫ y, ‖fderiv ℝ f y‖
  have hD : 0 ≤ D := integral_nonneg fun _ => norm_nonneg _
  have hG : (∫ y, ‖f y‖) = ‖g‖ := by
    rw [lp_one_norm]
    exact integral_congr_ae (hgf.mono fun x hx => congrArg norm hx.symm)
  let ε := ‖g‖ / (‖g‖ + D + 1)
  have hden : 0 < ‖g‖ + D + 1 := by positivity
  have hε : 0 < ε := div_pos hgn hden
  obtain ⟨a, ha, hac, ha0, haI, hadI⟩ := hprofiles ε hε
  obtain ⟨u, hu, hnorm⟩ := smooth_tensor_lift i a ha hac f hfd hfc
  have hTu : T u = g := by
    apply Lp.ext
    have hF : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Domain d => a (x i) • f (transverseProjection i x)) :=
      (ha.comp (ContinuousLinearMap.proj i : Domain d →L[ℝ] ℝ).contDiff).smul
        (hfd.comp (transverseProjection i).contDiff)
    have ht := hT u _ hF hu
    filter_upwards [ht, hgf] with y hy hgy
    rw [hy, coordinateLine_self, transverseProjection_coordinateLine, ha0, one_smul, hgy]
  refine ⟨u, hTu, hnorm.trans ?_⟩
  rw [hG]
  change N * ((∫ t, ‖a t‖) * (‖g‖ + D) + (∫ t, ‖deriv a t‖) * ‖g‖) ≤
    (N * (B + 1)) * ‖g‖
  have hεbound : ε * (‖g‖ + D) ≤ ‖g‖ := by
    calc
      ε * (‖g‖ + D) ≤ ε * (‖g‖ + D + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ = ‖g‖ := div_mul_cancel₀ _ hden.ne'
  have hsmall : (∫ t, ‖a t‖) * (‖g‖ + D) ≤ ‖g‖ :=
    (mul_le_mul_of_nonneg_right haI (by positivity)).trans hεbound
  have hnormal : (∫ t, ‖deriv a t‖) * ‖g‖ ≤ B * ‖g‖ :=
    mul_le_mul_of_nonneg_right hadI (norm_nonneg _)
  calc
    _ ≤ N * (‖g‖ + B * ‖g‖) := mul_le_mul_of_nonneg_left (add_le_add hsmall hnormal) hN.le
    _ = _ := by ring

/-- Every L1 boundary datum has an extension in the genuine W^{1,1}
space. The convergent-series choice imposes no linearity on the extension. -/
theorem halfSpace_trace_surjective : Specs.ExpandedFA.PartIV.TraceEndpointOne.Surjectivity := by
  intro 𝕜 _ d i T hT
  obtain ⟨C, hC, hlift⟩ := smooth_lifts i T hT
  exact surjective_of_smooth_lifts i T hC hlift

theorem halfSpace_onto_trace_exists : Specs.ExpandedFA.PartIV.TraceEndpointOne.OntoTraceExists :=
  onto_trace_exists_of_surjectivity halfSpace_trace_surjective

end ExpandedFA.PartIV.TraceEndpointOne
