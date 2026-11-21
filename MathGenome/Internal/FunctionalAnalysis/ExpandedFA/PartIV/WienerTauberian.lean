import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.WienerTauberian
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.WienerDensity
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Topology.Bornology.BoundedOperation
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace ExpandedFA.PartIV.WienerTauberian
open ExpandedFA.Fourier ExpandedFA.PartIV.WienerLocalIdeal
variable {d : ℕ}

lemma bounded_representative {φ : Euclidean d → ℂ} (hφ : MemLp φ ∞ volume) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂volume, ‖φ x‖ ≤ C := by
  have h := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp
    (by simpa only [eLpNorm_exponent_top hφ.aestronglyMeasurable] using hφ.eLpNorm_lt_top)
  obtain ⟨C, hC⟩ := h
  refine ⟨(C : ℝ) + 1, by positivity, ?_⟩
  filter_upwards [hC] with x hx
  exact (show ‖φ x‖ ≤ (C : ℝ) from hx).trans (by linarith)

lemma integrable_product {φ : Euclidean d → ℂ}
    (hφ : AEStronglyMeasurable φ volume) {C : ℝ}
    (hC : ∀ᵐ y ∂volume, ‖φ y‖ ≤ C)
    {f : Euclidean d → ℂ} (hf : Integrable f) (x : Euclidean d) :
    Integrable (fun y => f y * φ (x-y)) := by
  have hp := (volume : Measure (Euclidean d)).measurePreserving_sub_left x
  apply (hf.norm.mul_const C).mono'
    (hf.aestronglyMeasurable.mul (hφ.comp_measurePreserving hp))
  filter_upwards [hp.quasiMeasurePreserving.ae hC] with y hy
  simpa only [Pi.mul_apply, Function.comp_def, norm_mul] using mul_le_mul_of_nonneg_left hy (norm_nonneg (f y))

lemma convolution_bound {φ : Euclidean d → ℂ} {C : ℝ}
    (hC : ∀ᵐ y ∂volume, ‖φ y‖ ≤ C) (f : L1 d) (x : Euclidean d) :
    ‖convolutionValue f φ x‖ ≤ ‖f‖ * C := by
  have hp := (volume : Measure (Euclidean d)).measurePreserving_sub_left x
  calc
    ‖convolutionValue f φ x‖ ≤ ∫ y, ‖f y‖ * C := by
      apply norm_integral_le_of_norm_le ((L1.integrable_coeFn f).norm.mul_const C)
      filter_upwards [hp.quasiMeasurePreserving.ae hC] with y hy
      simpa only [Pi.mul_apply, Function.comp_def, norm_mul] using mul_le_mul_of_nonneg_left hy (norm_nonneg (f y))
    _ = ‖f‖ * C := by rw [integral_mul_const, L1.norm_eq_integral_norm]

/-- At each point, convolution against an essentially bounded representative
is a bounded functional on the actual L¹ quotient. -/
def convolutionCLM {φ : Euclidean d → ℂ}
    (hφ : AEStronglyMeasurable φ volume) {C : ℝ}
    (hC : ∀ᵐ y ∂volume, ‖φ y‖ ≤ C) (x : Euclidean d) : L1 d →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => convolutionValue f φ x
      map_add' := by
        intro f g
        unfold convolutionValue
        calc
          _ = ∫ y, f y * φ (x-y) + g y * φ (x-y) := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_add f g] with y hy
            simp only [Pi.add_apply] at hy
            rw [hy, add_mul]
          _ = _ := integral_add (integrable_product hφ hC (L1.integrable_coeFn f) x)
            (integrable_product hφ hC (L1.integrable_coeFn g) x)
      map_smul' := by
        intro c f
        unfold convolutionValue
        calc
          _ = ∫ y, c • (f y * φ (x-y)) := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_smul c f] with y hy
            simp only [Pi.smul_apply] at hy
            rw [hy, smul_eq_mul, mul_assoc]
            rfl
          _ = _ := integral_smul c _ }
    C (fun f => by
      change ‖convolutionValue f φ x‖ ≤ C * ‖f‖
      simpa only [mul_comm C] using convolution_bound hC f x)

lemma convolution_translate (φ : Euclidean d → ℂ) (f : L1 d) (y x : Euclidean d) :
    convolutionValue (translate y f) φ x = convolutionValue f φ (x-y) := by
  unfold convolutionValue
  calc
    _ = ∫ z, f (z-y) * φ (x-z) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_compMeasurePreserving f
        (measurePreserving_sub_right volume y)] with z hz
      change (translate y f) z = f (z-y) at hz
      rw [hz]
    _ = _ := by
      have h := integral_add_right_eq_self (fun z => f (z-y) * φ (x-z)) y
        (μ := (volume : Measure (Euclidean d)))
      simpa only [add_sub_cancel_right, sub_add_eq_sub_sub, sub_right_comm] using h.symm

/-- The zero-limit kernels form a closed subspace; the bound is uniform in x. -/
def vanishingSubmodule {φ : Euclidean d → ℂ}
    (hφ : AEStronglyMeasurable φ volume) {C : ℝ}
    (hC : ∀ᵐ y ∂volume, ‖φ y‖ ≤ C) (l : Filter (Euclidean d)) : Submodule ℂ (L1 d) where
  carrier := {f | Tendsto (fun x => convolutionCLM hφ hC x f) l (𝓝 0)}
  zero_mem' := by simpa using (tendsto_const_nhds (x := (0 : ℂ)) (f := l))
  add_mem' := by
    intro f g hf hg
    change Tendsto (fun x => convolutionCLM hφ hC x (f+g)) l (𝓝 0)
    simpa only [map_add, add_zero] using hf.add hg
  smul_mem' := by
    intro c f hf
    change Tendsto (fun x => convolutionCLM hφ hC x (c • f)) l (𝓝 0)
    simpa only [map_smul, smul_zero] using hf.const_smul c

lemma vanishingSubmodule_closed {φ : Euclidean d → ℂ}
    (hφ : AEStronglyMeasurable φ volume) {C : ℝ} (hpos : 0 < C)
    (hC : ∀ᵐ y ∂volume, ‖φ y‖ ≤ C) (l : Filter (Euclidean d)) :
    IsClosed (vanishingSubmodule hφ hC l : Set (L1 d)) := by
  apply isClosed_of_closure_subset
  intro f hf
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf (ε / (2*C)) (by positivity)
  have hg' : Tendsto (fun x => convolutionCLM hφ hC x g) l (𝓝 0) := hg
  filter_upwards [Metric.tendsto_nhds.mp hg' (ε/2) (by positivity)] with x hx
  simp only [dist_zero_right] at hx ⊢
  calc
    ‖convolutionCLM hφ hC x f‖ ≤
        ‖convolutionCLM hφ hC x (f-g)‖ + ‖convolutionCLM hφ hC x g‖ := by
      rw [map_sub]
      exact norm_le_norm_sub_add _ _
    _ ≤ ‖f-g‖ * C + ‖convolutionCLM hφ hC x g‖ :=
      add_le_add (convolution_bound hC (f-g) x) le_rfl
    _ < ε := by
      rw [dist_eq_norm] at hfg
      have hb : ‖f-g‖ * C < ε/2 := by
        have hh := (lt_div_iff₀ (by positivity : 0 < 2*C)).mp hfg
        nlinarith
      linarith

lemma zero_tauberian {φ : Euclidean d → ℂ}
    (hφ : AEStronglyMeasurable φ volume) {C : ℝ} (hpos : 0 < C)
    (hC : ∀ᵐ y ∂volume, ‖φ y‖ ≤ C) (l : Filter (Euclidean d))
    (hshift : ∀ y : Euclidean d, Tendsto (fun x => x-y) l l)
    (K : L1 d) (hK : ∀ ξ, integralFourier K ξ ≠ 0)
    (hlim : Tendsto (convolutionValue K φ) l (𝓝 0)) :
    ∀ f : L1 d, Tendsto (convolutionValue f φ) l (𝓝 0) := by
  let Y := vanishingSubmodule hφ hC l
  have htrans : TranslationInvariant Y := by
    intro y f hf
    change Tendsto (convolutionValue (translate y f) φ) l (𝓝 0)
    have hh : Tendsto (convolutionValue f φ) l (𝓝 0) := hf
    have heq : convolutionValue (translate y f) φ = fun x => convolutionValue f φ (x-y) :=
      funext (convolution_translate φ f y)
    rw [heq]
    exact hh.comp (hshift y)
  have htop : Y = ⊤ :=
    (ExpandedFA.PartIV.WienerDensity.subspace_criterion d Y
      (vanishingSubmodule_closed hφ hpos hC l) htrans).mpr
      (fun ξ => ⟨K, hlim, hK ξ⟩)
  intro f
  exact (show f ∈ Y from htop ▸ Submodule.mem_top)

lemma convolution_congr_left {𝕜 : Type*} [RCLike 𝕜]
    {f g : Euclidean d → 𝕜} (hfg : f =ᵐ[volume] g) (φ : Euclidean d → 𝕜) :
    convolutionValue f φ = convolutionValue g φ := by
  funext x
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

lemma convolution_center {f φ : Euclidean d → ℂ} (hf : Integrable f)
    (hφ : AEStronglyMeasurable φ volume) {C : ℝ}
    (hC : ∀ᵐ y ∂volume, ‖φ y‖ ≤ C) (a : ℂ) :
    convolutionValue f (fun y => φ y - a) =
      fun x => convolutionValue f φ x - a * ∫ y, f y := by
  funext x
  unfold convolutionValue
  simp_rw [mul_sub]
  rw [integral_sub (integrable_product hφ hC hf x) (hf.mul_const a),
    integral_mul_const, mul_comm a]

/-- A filter version handles both kinds of escape without repeating the density proof. -/
lemma tauberian_filter {K φ : Euclidean d → ℂ} {a : ℂ}
    (hKint : Integrable K) (hφ : MemLp φ ∞ volume)
    (hK : ∀ ξ, integralFourier K ξ ≠ 0)
    (l : Filter (Euclidean d))
    (hshift : ∀ y : Euclidean d, Tendsto (fun x => x-y) l l)
    (hlim : Tendsto (convolutionValue K φ) l (𝓝 (a * ∫ y, K y))) :
    ∀ f : Euclidean d → ℂ, Integrable f →
      Tendsto (convolutionValue f φ) l (𝓝 (a * ∫ y, f y)) := by
  obtain ⟨C, hpos, hC⟩ := bounded_representative hφ
  let ψ := fun y => φ y - a
  have hm : AEStronglyMeasurable ψ volume := hφ.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hbound : ∀ᵐ y ∂volume, ‖ψ y‖ ≤ C + ‖a‖ := by
    filter_upwards [hC] with y hy
    exact (norm_sub_le _ _).trans (add_le_add hy le_rfl)
  let k : L1 d := (memLp_one_iff_integrable.mpr hKint).toLp K
  have hk : (k : Euclidean d → ℂ) =ᵐ[volume] K := MemLp.coeFn_toLp _
  have hkF : ∀ ξ, integralFourier k ξ ≠ 0 := by
    intro ξ
    have heq : integralFourier k ξ = integralFourier K ξ := by
      apply integral_congr_ae
      filter_upwards [hk] with y hy
      rw [hy]
    rw [heq]
    exact hK ξ
  have hk0 : Tendsto (convolutionValue k ψ) l (𝓝 0) := by
    rw [convolution_congr_left hk, convolution_center hKint hφ.aestronglyMeasurable hC a]
    simpa using hlim.sub_const (a * ∫ y, K y)
  have hall := zero_tauberian hm (by positivity : 0 < C + ‖a‖) hbound l hshift k hkF hk0
  intro f hf
  let g : L1 d := (memLp_one_iff_integrable.mpr hf).toLp f
  have hg : (g : Euclidean d → ℂ) =ᵐ[volume] f := MemLp.coeFn_toLp _
  have h := hall g
  rw [convolution_congr_left hg, convolution_center hf hφ.aestronglyMeasurable hC a] at h
  have hh := h.add_const (a * ∫ y, f y)
  simpa only [sub_add_cancel, zero_add] using hh

lemma infinity_shift (y : Euclidean d) :
    Tendsto (fun x => x-y) (infinity d) (infinity d) := by
  simpa only [infinity, comap_norm_atTop] using tendsto_sub_const_cobounded y

lemma positiveInfinity_shift (y : Euclidean 1) :
    Tendsto (fun x => x-y) positiveInfinity positiveInfinity := by
  apply tendsto_comap_iff.mpr
  change Tendsto (fun x : Euclidean 1 => x 0 - y 0) positiveInfinity atTop
  apply tendsto_atTop.mpr
  intro b
  have h := (tendsto_comap : Tendsto (fun x : Euclidean 1 => x 0)
    positiveInfinity atTop).eventually_ge_atTop (b + y 0)
  exact h.mono fun x hx => by linarith

/-- Slow oscillation makes a sufficiently small normalized local average close
to the chosen pointwise representative, even if it is only essentially bounded. -/
lemma slow_limit_filter {φ : Euclidean d → ℂ} {a : ℂ}
    (hφ : MemLp φ ∞ volume) (l : Filter (Euclidean d))
    (hall : ∀ f : Euclidean d → ℂ, Integrable f →
      Tendsto (convolutionValue f φ) l (𝓝 (a * ∫ y, f y)))
    (hslow : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ x in l, ∀ h : Euclidean d, ‖h‖ < δ → ‖φ (x-h) - φ x‖ < ε) :
    Tendsto φ l (𝓝 a) := by
  obtain ⟨C, _, hC⟩ := bounded_representative hφ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hosc⟩ := hslow (ε/2) (by positivity)
  let b : ContDiffBump (0 : Euclidean d) :=
    { rIn := δ/2, rOut := δ, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let g := b.normed (volume : Measure (Euclidean d))
  let f : Euclidean d → ℂ := fun y => (g y : ℂ)
  have hgint : Integrable g := b.integrable_normed
  have hfint : Integrable f := Complex.ofRealCLM.integrable_comp hgint
  have hmass : ∫ y, f y = 1 := by
    change (∫ y, Complex.ofRealCLM (g y)) = 1
    rw [Complex.ofRealCLM.integral_comp_comm hgint]
    have hh : ∫ y, g y = 1 := b.integral_normed
    rw [hh]
    rfl
  have hlim := hall f hfint
  rw [hmass, mul_one] at hlim
  filter_upwards [hosc, Metric.tendsto_nhds.mp hlim (ε/2) (by positivity)] with x hx hlimx
  have herr : ‖convolutionValue f φ x - φ x‖ ≤ ε/2 := by
    have hc := congrFun (convolution_center hfint hφ.aestronglyMeasurable hC (φ x)) x
    rw [hmass, mul_one] at hc
    rw [← hc]
    change ‖∫ y, f y * (φ (x-y) - φ x)‖ ≤ ε/2
    calc
      _ ≤ ∫ y, g y * (ε/2) := by
        apply norm_integral_le_of_norm_le (hgint.mul_const (ε/2))
        apply Eventually.of_forall
        intro y
        have hgn : 0 ≤ g y := b.nonneg_normed y
        by_cases hy : g y = 0
        · simp [f, hy]
        · have hys : y ∈ Function.support g := hy
          rw [b.support_normed_eq] at hys
          have hnorm : ‖y‖ < δ := by simpa [b, Metric.mem_ball, dist_zero_right] using hys
          simpa only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgn] using
            mul_le_mul_of_nonneg_left (hx y hnorm).le hgn
      _ = ε/2 := by
        rw [integral_mul_const]
        have hh : ∫ y, g y = 1 := b.integral_normed
        rw [hh, one_mul]
  calc
    dist (φ x) a ≤ dist (φ x) (convolutionValue f φ x) + dist (convolutionValue f φ x) a :=
      dist_triangle _ _ _
    _ < ε := by
      have herr' : dist (φ x) (convolutionValue f φ x) ≤ ε/2 := by
        simpa only [dist_eq_norm, norm_sub_rev] using herr
      linarith

lemma slowOscillation_eventually {φ : Euclidean d → ℂ} (h : SlowOscillation φ)
    (ε : ℝ) (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ x in infinity d, ∀ y : Euclidean d, ‖y‖ < δ → ‖φ (x-y) - φ x‖ < ε := by
  obtain ⟨δ, R, hδ, _, hosc⟩ := h ε hε
  refine ⟨δ, hδ, ?_⟩
  have hR : ∀ᶠ x : Euclidean d in infinity d, R < ‖x‖ :=
    (tendsto_comap : Tendsto norm (infinity d) atTop).eventually_gt_atTop R
  exact hR.mono fun x hx y hy => hosc x y hy hx

lemma slowOscillationRight_eventually {φ : Euclidean 1 → ℂ} (h : SlowOscillationRight φ)
    (ε : ℝ) (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ x in positiveInfinity, ∀ y : Euclidean 1, ‖y‖ < δ → ‖φ (x-y) - φ x‖ < ε := by
  obtain ⟨δ, R, hδ, _, hosc⟩ := h ε hε
  refine ⟨δ, hδ, ?_⟩
  have hR : ∀ᶠ x : Euclidean 1 in positiveInfinity, R < x 0 :=
    (tendsto_comap : Tendsto (fun x : Euclidean 1 => x 0) positiveInfinity atTop).eventually_gt_atTop R
  exact hR.mono fun x hx y hy => hosc x y hy hx

theorem complex_tauberian : Specs.ExpandedFA.PartIV.WienerTauberian.ComplexTauberian := by
  intro d K φ a hKint hφ hK hlim
  have hall := tauberian_filter hKint hφ hK (infinity d) infinity_shift hlim
  exact ⟨hall, fun hslow => slow_limit_filter hφ _ hall (slowOscillation_eventually hslow)⟩

theorem complex_tauberian_right : Specs.ExpandedFA.PartIV.WienerTauberian.ComplexTauberianRight := by
  intro K φ a hKint hφ hK hlim
  have hall := tauberian_filter hKint hφ hK positiveInfinity positiveInfinity_shift hlim
  exact ⟨hall, fun hslow => slow_limit_filter hφ _ hall (slowOscillationRight_eventually hslow)⟩

lemma convolution_ofReal (f φ : Euclidean d → ℝ) :
    convolutionValue (fun y => (f y : ℂ)) (fun y => (φ y : ℂ)) =
      fun x => ((convolutionValue f φ x : ℝ) : ℂ) := by
  funext x
  simp only [convolutionValue, ← Complex.ofReal_mul, integral_complex_ofReal]

lemma slowOscillation_ofReal {φ : Euclidean d → ℝ} (h : SlowOscillation φ) :
    SlowOscillation (fun y => (φ y : ℂ)) := by
  intro ε hε
  obtain ⟨δ, R, hδ, hR, hh⟩ := h ε hε
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro x y hy hx
  simpa only [← Complex.ofReal_sub, Complex.norm_real] using hh x y hy hx

lemma slowOscillationRight_ofReal {φ : Euclidean 1 → ℝ} (h : SlowOscillationRight φ) :
    SlowOscillationRight (fun y => (φ y : ℂ)) := by
  intro ε hε
  obtain ⟨δ, R, hδ, hR, hh⟩ := h ε hε
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro x y hy hx
  simpa only [← Complex.ofReal_sub, Complex.norm_real] using hh x y hy hx

theorem real_tauberian : Specs.ExpandedFA.PartIV.WienerTauberian.RealTauberian := by
  intro d K φ a hKint hφ hK hlim
  have hlimC : Tendsto (convolutionValue (fun y => (K y : ℂ)) (fun y => (φ y : ℂ)))
      (infinity d) (𝓝 ((a : ℂ) * ∫ y, (K y : ℂ))) := by
    simpa only [convolution_ofReal, integral_complex_ofReal, ← Complex.ofReal_mul] using
      (tendsto_ofReal_iff.mpr hlim)
  have hc := complex_tauberian d (fun y => (K y : ℂ)) (fun y => (φ y : ℂ)) (a : ℂ)
    (Complex.ofRealCLM.integrable_comp hKint) (Complex.ofRealCLM.comp_memLp' hφ) hK hlimC
  constructor
  · intro f hf
    apply tendsto_ofReal_iff.mp
    have hh := hc.1 (fun y => (f y : ℂ)) (Complex.ofRealCLM.integrable_comp hf)
    simpa only [convolution_ofReal, integral_complex_ofReal, ← Complex.ofReal_mul] using hh
  · intro hslow
    exact tendsto_ofReal_iff.mp (hc.2 (slowOscillation_ofReal hslow))

theorem real_tauberian_right : Specs.ExpandedFA.PartIV.WienerTauberian.RealTauberianRight := by
  intro K φ a hKint hφ hK hlim
  have hlimC : Tendsto (convolutionValue (fun y => (K y : ℂ)) (fun y => (φ y : ℂ)))
      positiveInfinity (𝓝 ((a : ℂ) * ∫ y, (K y : ℂ))) := by
    simpa only [convolution_ofReal, integral_complex_ofReal, ← Complex.ofReal_mul] using
      (tendsto_ofReal_iff.mpr hlim)
  have hc := complex_tauberian_right (fun y => (K y : ℂ)) (fun y => (φ y : ℂ)) (a : ℂ)
    (Complex.ofRealCLM.integrable_comp hKint) (Complex.ofRealCLM.comp_memLp' hφ) hK hlimC
  constructor
  · intro f hf
    apply tendsto_ofReal_iff.mp
    have hh := hc.1 (fun y => (f y : ℂ)) (Complex.ofRealCLM.integrable_comp hf)
    simpa only [convolution_ofReal, integral_complex_ofReal, ← Complex.ofReal_mul] using hh
  · intro hslow
    exact tendsto_ofReal_iff.mp (hc.2 (slowOscillationRight_ofReal hslow))

/-- The single Euclidean coordinate is isometric to the real line, with its
Lebesgue measure. This transports the one-sided result without a change of scale. -/
def realLineEquiv : Euclidean 1 ≃ₗᵢ[ℝ] ℝ where
  __ := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toLinearEquiv
  norm_map' x := by simp [EuclideanSpace.norm_eq, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

@[simp] lemma realLineEquiv_apply (x : Euclidean 1) : realLineEquiv x = x 0 := rfl

lemma integral_realLine {𝕜 : Type*} [RCLike 𝕜] (f : ℝ → 𝕜) :
    (∫ y : Euclidean 1, f (realLineEquiv y)) = ∫ y, f y :=
  realLineEquiv.measurePreserving.integral_comp realLineEquiv.toHomeomorph.measurableEmbedding f

lemma convolution_realLine {𝕜 : Type*} [RCLike 𝕜] (f φ : ℝ → 𝕜) (x : Euclidean 1) :
    convolutionValue (fun y => f (realLineEquiv y)) (fun y => φ (realLineEquiv y)) x =
      convolutionValue f φ (realLineEquiv x) := by
  unfold convolutionValue
  simp_rw [map_sub]
  exact integral_realLine (fun y => f y * φ (realLineEquiv x - y))

lemma fourier_realLine (f : ℝ → ℂ) (ξ : Euclidean 1) :
    integralFourier (fun y => f (realLineEquiv y)) ξ = lineFourier f (realLineEquiv ξ) := by
  unfold integralFourier lineFourier
  have hi (x : Euclidean 1) : inner ℝ x ξ = realLineEquiv x * realLineEquiv ξ := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  simp_rw [hi]
  exact integral_realLine (𝕜 := ℂ) (fun y =>
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((y * realLineEquiv ξ : ℝ) : ℂ)) * f y)

lemma realLine_tendsto_iff {β : Type*} {f : ℝ → β} {l : Filter β} :
    Tendsto (fun x : Euclidean 1 => f (realLineEquiv x)) positiveInfinity l ↔
      Tendsto f atTop l := by
  have hmap : map realLineEquiv positiveInfinity = atTop := by
    exact map_comap_of_surjective realLineEquiv.surjective atTop
  rw [← hmap, tendsto_map'_iff]
  rfl

lemma line_tauberian_transfer {𝕜 : Type*} [RCLike 𝕜]
    (hcoord : ∀ (K φ : Euclidean 1 → 𝕜) (a : 𝕜),
      Integrable K → MemLp φ ∞ volume →
      (∀ ξ, integralFourier
        (fun x => (RCLike.re (K x) : ℂ) + Complex.I * (RCLike.im (K x) : ℂ)) ξ ≠ 0) →
      Tendsto (convolutionValue K φ) positiveInfinity (𝓝 (a * ∫ y, K y)) →
      (∀ f : Euclidean 1 → 𝕜, Integrable f →
        Tendsto (convolutionValue f φ) positiveInfinity (𝓝 (a * ∫ y, f y))) ∧
      (SlowOscillationRight φ → Tendsto φ positiveInfinity (𝓝 a)))
    (K φ : ℝ → 𝕜) (a : 𝕜) (hKint : Integrable K) (hφ : MemLp φ ∞ volume)
    (hK : ∀ ξ, lineFourier
      (fun x => (RCLike.re (K x) : ℂ) + Complex.I * (RCLike.im (K x) : ℂ)) ξ ≠ 0)
    (hlim : Tendsto (convolutionValue K φ) atTop (𝓝 (a * ∫ y, K y))) :
    (∀ f : ℝ → 𝕜, Integrable f →
      Tendsto (convolutionValue f φ) atTop (𝓝 (a * ∫ y, f y))) ∧
    (SlowOscillationAtTop φ → Tendsto φ atTop (𝓝 a)) := by
  have hKl : Integrable (fun x : Euclidean 1 => K (realLineEquiv x)) :=
    realLineEquiv.measurePreserving.integrable_comp_of_integrable hKint
  have hφl : MemLp (fun x : Euclidean 1 => φ (realLineEquiv x)) ∞ volume :=
    hφ.comp_measurePreserving realLineEquiv.measurePreserving
  have hKF : ∀ ξ : Euclidean 1, integralFourier
      (fun x => (RCLike.re (K (realLineEquiv x)) : ℂ) +
        Complex.I * (RCLike.im (K (realLineEquiv x)) : ℂ)) ξ ≠ 0 := by
    intro ξ
    rw [fourier_realLine (fun x => (RCLike.re (K x) : ℂ) +
      Complex.I * (RCLike.im (K x) : ℂ)) ξ]
    exact hK _
  have hliml : Tendsto
      (convolutionValue (fun x : Euclidean 1 => K (realLineEquiv x))
        (fun x : Euclidean 1 => φ (realLineEquiv x))) positiveInfinity
        (𝓝 (a * ∫ y : Euclidean 1, K (realLineEquiv y))) := by
    have heq := funext (convolution_realLine K φ)
    rw [heq, integral_realLine]
    exact realLine_tendsto_iff.mpr hlim
  have hc := hcoord _ _ a hKl hφl hKF hliml
  constructor
  · intro f hf
    have hh := hc.1 (fun x => f (realLineEquiv x))
      (realLineEquiv.measurePreserving.integrable_comp_of_integrable hf)
    have heq := funext (convolution_realLine f φ)
    rw [heq, integral_realLine] at hh
    exact realLine_tendsto_iff.mp hh
  · intro hslow
    apply realLine_tendsto_iff.mp
    apply hc.2
    intro ε hε
    obtain ⟨δ, R, hδ, hR, hosc⟩ := hslow ε hε
    refine ⟨δ, R, hδ, hR, ?_⟩
    intro x y hy hx
    have hy' : ‖realLineEquiv y‖ < δ := by simpa only [realLineEquiv.norm_map] using hy
    simpa only [map_sub] using hosc (realLineEquiv x) (realLineEquiv y) hy' hx

lemma complex_reconstruction {α : Type*} (f : α → ℂ) :
    (fun x => (RCLike.re (f x) : ℂ) + Complex.I * (RCLike.im (f x) : ℂ)) = f := by
  funext x
  change ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ) = f x
  rw [mul_comm, Complex.re_add_im]

theorem complex_line_tauberian : Specs.ExpandedFA.PartIV.WienerTauberian.ComplexLineTauberian := by
  intro K φ a hKint hφ hK hlim
  apply line_tauberian_transfer (𝕜 := ℂ) ?_ K φ a hKint hφ ?_ hlim
  · intro K φ a hKint hφ hK hlim
    apply complex_tauberian_right K φ a hKint hφ ?_ hlim
    simpa only [complex_reconstruction]
      using hK
  · simpa only [complex_reconstruction]
      using hK

theorem real_line_tauberian : Specs.ExpandedFA.PartIV.WienerTauberian.RealLineTauberian := by
  intro K φ a hKint hφ hK hlim
  apply line_tauberian_transfer (𝕜 := ℝ) ?_ K φ a hKint hφ ?_ hlim
  · intro K φ a hKint hφ hK hlim
    apply real_tauberian_right K φ a hKint hφ ?_ hlim
    simpa only [RCLike.re_to_real, RCLike.im_to_real, Complex.ofReal_zero, mul_zero, add_zero]
      using hK
  · simpa only [RCLike.re_to_real, RCLike.im_to_real, Complex.ofReal_zero, mul_zero, add_zero]
      using hK

end ExpandedFA.PartIV.WienerTauberian
