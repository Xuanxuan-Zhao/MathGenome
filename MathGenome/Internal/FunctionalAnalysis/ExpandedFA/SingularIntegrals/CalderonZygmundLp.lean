import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.CalderonZygmundLp
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SingularIntegrals.CalderonZygmundWeak11
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Interpolation.Marcinkiewicz
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpDuality
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.ProperSupportConvolution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Basic.Real.ConjExponents
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective

set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal NNReal Topology Distributions

namespace ExpandedFA.SingularIntegrals.CZLp
open StandardConvolution ExpandedFA.FunctionSpaces
open ExpandedFA.Interpolation ExpandedFA.Interpolation.MarcinkiewiczSpec

/-- A linear choice of a.e. measurable representatives. This is only an
algebraic section; no pointwise property of Mathlib's default choice is used. -/
theorem exists_linear_representatives {X : Type} [MeasurableSpace X]
    (𝕜 : Type) [RCLike 𝕜] (μ : Measure X) :
    ∃ R : (X →ₘ[μ] 𝕜) →ₗ[𝕜] (X → 𝕜),
      (∀ f, AEStronglyMeasurable (R f) μ) ∧
      ∀ f, R f =ᵐ[μ] (f : X → 𝕜) := by
  let M : Submodule 𝕜 (X → 𝕜) :=
    { carrier := {f | AEStronglyMeasurable f μ}
      zero_mem' := aestronglyMeasurable_zero
      add_mem' := fun hf hg => hf.add hg
      smul_mem' := fun c f hf => hf.const_smul c }
  let Q : M →ₗ[𝕜] (X →ₘ[μ] 𝕜) :=
    { toFun := fun f => AEEqFun.mk f.val f.property
      map_add' := by intro f g; exact (AEEqFun.mk_add_mk _ _ _ _).symm
      map_smul' := by intro c f; exact (AEEqFun.smul_mk _ _ _).symm }
  have hQ : Function.Surjective Q := by
    intro f
    exact ⟨⟨f, f.aestronglyMeasurable⟩, AEEqFun.mk_coeFn f⟩
  obtain ⟨R, hR⟩ := Q.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hQ)
  refine ⟨M.subtype.comp R, fun f => (R f).property, ?_⟩
  intro f
  have he : Q (R f) = f := LinearMap.congr_fun hR f
  exact (AEEqFun.coeFn_mk (R f).val (R f).property).symm.trans
    (Filter.Eventually.of_forall (fun x => congrArg (fun g : X →ₘ[μ] 𝕜 => g x) he))

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

/-- Change exponent on the intersection by retaining the same a.e. class. -/
def intersectionToL2 (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    intersectionCore (𝕜 := 𝕜) (volume : Measure (Space d)) 1 2 p →ₗ[𝕜] L2 𝕜 d where
  toFun f := f.property.2.toLp (f.val : Space d → 𝕜)
  map_add' f g := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans ((Lp.coeFn_add f.val g.val).trans
      (((Lp.coeFn_add _ _).trans ((MemLp.coeFn_toLp _).add (MemLp.coeFn_toLp _))).symm))
  map_smul' a f := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans ((Lp.coeFn_smul a f.val).trans
      (((Lp.coeFn_smul a _).trans ((MemLp.coeFn_toLp _).const_smul a)).symm))

/-- Weak (1,1) in the normalization used by the interpolation interface. -/
theorem endpoint_one_of_weak {X : Type} [MeasurableSpace X]
    (μ : Measure X) (f g : X → 𝕜) (C : ℝ≥0)
    (h : ∀ t : ℝ, 0 < t → μ {x | t < ‖g x‖} ≤
      ENNReal.ofReal ((C : ℝ) / t) * eLpNorm f 1 μ) :
    endpointEstimate μ μ 1 C f g := by
  simp only [endpointEstimate, ENNReal.one_ne_top, ↓reduceIte, ENNReal.toReal_one,
    div_one, ENNReal.rpow_one]
  intro t ht
  calc
    ENNReal.ofReal t * distribution μ g t ≤
        ENNReal.ofReal t * (ENNReal.ofReal ((C : ℝ) / t) * eLpNorm f 1 μ) :=
      by gcongr; exact h t ht
    _ = (C : ℝ≥0∞) * eLpNorm f 1 μ := by
      rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr ht.le),
        ENNReal.ofReal_inv_of_pos ht, ← mul_assoc, ← mul_assoc,
        ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr ht)
          ENNReal.ofReal_ne_top, one_mul]
      simp only [ENNReal.ofReal_coe_nnreal]

/-- Strong L² boundedness implies the weak endpoint used for interpolation. -/
theorem endpoint_two {X : Type} [MeasurableSpace X] (μ : Measure X)
    (f g : X → 𝕜) (hf : MemLp f 2 μ) (_hg : MemLp g 2 μ)
    (C : ℝ≥0) (hbound : eLpNorm g 2 μ ≤ (C : ℝ≥0∞) * eLpNorm f 2 μ) :
    endpointEstimate μ μ 2 C f g := by
  have he := endpointEstimate_finite_iff (g := g) (ν := μ) hf.aestronglyMeasurable
    (by norm_num : (0 : ℝ) < 2) C
  norm_num only [ENNReal.ofReal_ofNat] at he
  apply he.mpr
  intro t ht
  have hs : {x | t < ‖g x‖} ⊆ {x | ENNReal.ofReal t ≤ ‖g x‖ₑ} := by
    intro x hx
    change ENNReal.ofReal t ≤ ‖g x‖ₑ
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hx.le
  have hm := mul_meas_ge_le_pow_eLpNorm' (p := 2) (f := g) μ
    (by norm_num) (by norm_num) (ENNReal.ofReal t)
  have hb := ENNReal.rpow_le_rpow hbound (by norm_num : (0 : ℝ) ≤ 2)
  calc
    ENNReal.ofReal t ^ (2 : ℝ) * distribution μ g t ≤
      ENNReal.ofReal t ^ (2 : ℝ) * μ {x | ENNReal.ofReal t ≤ ‖g x‖ₑ} :=
        by gcongr; exact measure_mono hs
    _ ≤ eLpNorm g 2 μ ^ (2 : ℝ) := by simpa using hm
    _ ≤ ((C : ℝ≥0∞) * eLpNorm f 2 μ) ^ (2 : ℝ) := hb
    _ = (C : ℝ≥0∞) ^ (2 : ℝ) * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
      have hmom := eLpNorm_ofReal_rpow hf.aestronglyMeasurable
        (by norm_num : (0 : ℝ) < 2)
      norm_num only [ENNReal.ofReal_ofNat] at hmom
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hmom]

/-- Output on the endpoint intersection, still as an a.e. class. -/
def intersectionOutput (T : StandardConvolutionOperator 𝕜 d)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    intersectionCore (𝕜 := 𝕜) (volume : Measure (Space d)) 1 2 p →ₗ[𝕜]
      CZWeak.MeasurableClasses 𝕜 d where
  toFun f := (T.operator (intersectionToL2 p f) : CZWeak.MeasurableClasses 𝕜 d)
  map_add' f g := by simp only [map_add]; rfl
  map_smul' a f := by simp only [map_smul]; rfl

/-- Interpolation gives a bounded extension for each 1 < p < 2, with
agreement on all L¹ ∩ L² ∩ Lᵖ data. -/
theorem low_extensions : LowExtensions := by
  intro 𝕜 _ d T p hp2
  obtain ⟨C, hC, hweak⟩ := CZWeak.weak_core 𝕜 d T
  obtain ⟨R, hRm, hRae⟩ := exists_linear_representatives 𝕜
    (volume : Measure (Space d))
  let U := R.comp (intersectionOutput T p.val)
  have hae (f : intersectionCore (volume : Measure (Space d)) 1 2 p.val) :
      U f =ᵐ[volume] (T.operator (intersectionToL2 p.val f) : Space d → 𝕜) :=
    hRae (intersectionOutput T p.val f)
  have hm (f : intersectionCore (volume : Measure (Space d)) 1 2 p.val) :
      AEStronglyMeasurable (U f) volume := hRm _
  have hw1 (f : intersectionCore (volume : Measure (Space d)) 1 2 p.val) :
      endpointEstimate volume volume 1 ⟨C, hC⟩ (f.val : Space d → 𝕜) (U f) := by
    apply endpoint_one_of_weak _ _ _ ⟨C, hC⟩
    intro t ht
    rw [← distribution, distribution_congr_ae (hae f)]
    exact hweak f.val ((memLp_one_iff_integrable).mp f.property.1) f.property.2 t ht
  have hw2 (f : intersectionCore (volume : Measure (Space d)) 1 2 p.val) :
      endpointEstimate volume volume 2 ‖T.operator‖₊ (f.val : Space d → 𝕜) (U f) := by
    apply endpoint_two _ _ _ f.property.2
      ((memLp_congr_ae (hae f)).mpr (Lp.memLp _))
    rw [eLpNorm_congr_ae (hae f), ← Lp.enorm_def, ← ofReal_norm]
    apply (ENNReal.ofReal_le_ofReal (T.operator.le_opNorm _)).trans_eq
    rw [ENNReal.ofReal_mul (norm_nonneg T.operator)]
    change ENNReal.ofReal ‖T.operator‖ * ENNReal.ofReal ‖f.property.2.toLp _‖ = _
    rw [Lp.norm_toLp, ENNReal.ofReal_toReal f.property.2.ne, ofReal_norm]
    rfl
  obtain ⟨K, hK⟩ := marcinkiewicz_linear_extension 1 2 p.val
    (by rfl) p.one_lt hp2 ⟨C, hC⟩ ‖T.operator‖₊
  obtain ⟨S, hS, _⟩ := hK volume volume U hm hw1 hw2
  refine ⟨S, ?_⟩
  intro f h1 h2 hf
  let a : intersectionCore (volume : Measure (Space d)) 1 2 p.val :=
    ⟨hf.toLp f, (memLp_congr_ae hf.coeFn_toLp).mpr h1,
      (memLp_congr_ae hf.coeFn_toLp).mpr h2⟩
  have he : intersectionToL2 p.val a = h2.toLp f :=
    a.property.2.toLp_congr h2 hf.coeFn_toLp
  exact (hS.2 a).trans ((hae a).trans (by rw [he]))

/-- One fixed simple approximation works in every finite Lᵖ space to which
its input belongs. Its nonzero level sets have finite measure. -/
theorem simultaneous_simple_approx {X : Type} [MeasurableSpace X]
    (μ : Measure X) (f : X → 𝕜) (hm : Measurable f)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hf : MemLp f p μ) :
    ∃ u : ℕ → X → 𝕜,
      ∃ hu : ∀ n r, MemLp (u n) r μ,
      ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ∞ → ∀ hr : MemLp f r μ,
        Tendsto (fun n => (hu n r).toLp (u n))
          atTop (𝓝 (hr.toLp f)) := by
  let v := fun n => SimpleFunc.approxOn f hm (range f ∪ {0}) 0 (by simp) n
  have hmem (n : ℕ) (r : ℝ≥0∞) : MemLp (v n : X → 𝕜) r μ := by
    have hv : MemLp (v n : X → 𝕜) p μ := SimpleFunc.memLp_approxOn_range hm hf n
    exact SimpleFunc.memLp_of_finite_measure_preimage r
      ((SimpleFunc.memLp_iff hp0 hpTop).mp hv)
  refine ⟨fun n => v n, hmem, ?_⟩
  intro r _ hrTop hr
  exact SimpleFunc.tendsto_approxOn_range_Lp hrTop hm hr

/-- Bounded extensions agreeing with the original operator on the full
endpoint intersection agree on every pairwise finite-exponent intersection. -/
theorem compatible_of_core (T : StandardConvolutionOperator 𝕜 d)
    (p q : ℝ≥0∞) [hp : Fact (1 ≤ p)] [hq : Fact (1 ≤ q)]
    (hpTop : p ≠ ∞) (hqTop : q ≠ ∞)
    (S : LpSpace 𝕜 d p →L[𝕜] LpSpace 𝕜 d p)
    (R : LpSpace 𝕜 d q →L[𝕜] LpSpace 𝕜 d q)
    (hS : ∀ (f : Space d → 𝕜) (_h1 : MemLp f 1 volume) (h2 : MemLp f 2 volume)
      (h : MemLp f p volume), (S (h.toLp f) : Space d → 𝕜) =ᵐ[volume]
        (T.operator (h2.toLp f) : Space d → 𝕜))
    (hR : ∀ (f : Space d → 𝕜) (_h1 : MemLp f 1 volume) (h2 : MemLp f 2 volume)
      (h : MemLp f q volume), (R (h.toLp f) : Space d → 𝕜) =ᵐ[volume]
        (T.operator (h2.toLp f) : Space d → 𝕜))
    (f : Space d → 𝕜) (hfp : MemLp f p volume) (hfq : MemLp f q volume) :
    (S (hfp.toLp f) : Space d → 𝕜) =ᵐ[volume] (R (hfq.toLp f) : Space d → 𝕜) := by
  let g : Space d → 𝕜 := hfp.toLp f
  have hgp : MemLp g p volume := Lp.memLp _
  have hgq : MemLp g q volume := (memLp_congr_ae hfp.coeFn_toLp).mpr hfq
  obtain ⟨u, hu, hconv⟩ := simultaneous_simple_approx volume g
    (Lp.stronglyMeasurable (hfp.toLp f)).measurable
    (zero_lt_one.trans_le hp.out).ne' hpTop hgp
  have hep : hgp.toLp g = hfp.toLp f := hgp.toLp_congr hfp hfp.coeFn_toLp
  have heq : hgq.toLp g = hfq.toLp f := hgq.toLp_congr hfq hfp.coeFn_toLp
  have hup := S.continuous.tendsto (hgp.toLp g) |>.comp (hconv p hpTop hgp)
  have huq := R.continuous.tendsto (hgq.toLp g) |>.comp (hconv q hqTop hgq)
  rw [hep] at hup
  rw [heq] at huq
  have he (n : ℕ) :
      (S ((hu n p).toLp (u n)) : Space d → 𝕜) =ᵐ[volume]
        (R ((hu n q).toLp (u n)) : Space d → 𝕜) :=
    (hS (u n) (hu n 1) (hu n 2) (hu n p)).trans
      (hR (u n) (hu n 1) (hu n 2) (hu n q)).symm
  exact tendstoInMeasure_ae_unique
    ((tendstoInMeasure_of_tendsto_Lp hup).congr_left he)
    (tendstoInMeasure_of_tendsto_Lp huq)

/-- Agreement on the dense endpoint core also gives compatibility with the
weak extension on all L¹ ∩ Lᵖ inputs, rather than only on L² inputs. -/
theorem compatible_weak_of_core (T : StandardConvolutionOperator 𝕜 d)
    (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (hpTop : p ≠ ∞)
    (S : LpSpace 𝕜 d p →L[𝕜] LpSpace 𝕜 d p)
    (hS : ∀ (f : Space d → 𝕜) (_h1 : MemLp f 1 volume) (h2 : MemLp f 2 volume)
      (h : MemLp f p volume), (S (h.toLp f) : Space d → 𝕜) =ᵐ[volume]
        (T.operator (h2.toLp f) : Space d → 𝕜))
    (W : CZWeak.L1 𝕜 d →ₗ[𝕜] CZWeak.MeasurableClasses 𝕜 d)
    (hW : CZWeak.IsCompatibleExtension T W)
    (f : Space d → 𝕜) (hfp : MemLp f p volume) (hf1 : MemLp f 1 volume) :
    (S (hfp.toLp f) : Space d → 𝕜) =ᵐ[volume] (W (hf1.toLp f) : Space d → 𝕜) := by
  let g : Space d → 𝕜 := hfp.toLp f
  have hgp : MemLp g p volume := Lp.memLp _
  have hg1 : MemLp g 1 volume := (memLp_congr_ae hfp.coeFn_toLp).mpr hf1
  obtain ⟨u, hu, hconv⟩ := simultaneous_simple_approx volume g
    (Lp.stronglyMeasurable (hfp.toLp f)).measurable
    (zero_lt_one.trans_le hp.out).ne' hpTop hgp
  have hep : hgp.toLp g = hfp.toLp f := hgp.toLp_congr hfp hfp.coeFn_toLp
  have he1 : hg1.toLp g = hf1.toLp f := hg1.toLp_congr hf1 hfp.coeFn_toLp
  have hup := S.continuous.tendsto (hgp.toLp g) |>.comp (hconv p hpTop hgp)
  have huw := CZWeak.extension_tendstoInMeasure T W hW
    (fun n => (hu n 1).toLp (u n)) (hg1.toLp g) (hconv 1 (by simp) hg1)
  rw [hep] at hup
  rw [he1] at huw
  have he (n : ℕ) :
      (S ((hu n p).toLp (u n)) : Space d → 𝕜) =ᵐ[volume]
        (W ((hu n 1).toLp (u n)) : Space d → 𝕜) :=
    (hS (u n) (hu n 1) (hu n 2) (hu n p)).trans
      (hW.1 (u n) (hu n 1) (hu n 2)).symm
  exact tendstoInMeasure_ae_unique
    ((tendstoInMeasure_of_tendsto_Lp hup).congr_left he) huw

/-- The complete low-exponent result: agreement on the entire L²
intersection and on the entire intersection with the weak L¹ extension. -/
theorem low_strong_extensions : LowStrongExtensions := by
  intro 𝕜 _ d T p hp2
  obtain ⟨S, hS⟩ := low_extensions 𝕜 d T p hp2
  refine ⟨S, ?_, ?_⟩
  · intro f hf h2
    exact compatible_of_core T p.val 2 p.lt_top.ne (by simp) S T.operator hS
      (fun f _ h2 h => by have he : h.toLp f = h2.toLp f := rfl; rw [he]) f hf h2
  · intro W hW f h1 hp
    exact compatible_weak_of_core T p.val p.lt_top.ne S hS W hW f hp h1

theorem reflected_conjugate_gradient (k : StandardKernel 𝕜 d)
    (x : Space d) (hx : x ≠ 0) :
    kernelGradientNorm (fun y => star (k.function (-y))) x =
      kernelGradientNorm k.function (-x) := by
  have hk : DifferentiableAt ℝ k.function (-x) :=
    (k.contDiff.differentiableOn (by norm_num)).differentiableAt
      (isOpen_compl_singleton.mem_nhds (neg_ne_zero.mpr hx))
  have hf := (hk.hasFDerivAt.comp x (hasFDerivAt_id x).neg).star
  unfold kernelGradientNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change ‖(fderiv ℝ (fun y => star ((k.function ∘ Neg.neg) y)) x)
    (ExpandedFA.Fourier.basisVector i)‖ ^ 2 = _
  rw [hf.fderiv]
  simp

/-- Reflection and scalar conjugation preserve the exact size and gradient
constant; the value at the origin remains unrestricted. -/
def reflectedConjugateKernel (k : StandardKernel 𝕜 d) : StandardKernel 𝕜 d where
  function x := star (k.function (-x))
  contDiff := (starL' ℝ : 𝕜 ≃L[ℝ] 𝕜).contDiff.comp_contDiffOn
    (k.contDiff.comp contDiff_neg.contDiffOn (fun x hx => neg_ne_zero.mpr hx))
  constant := k.constant
  constant_nonneg := k.constant_nonneg
  size x hx := by simpa only [norm_star, norm_neg] using k.size (-x) (neg_ne_zero.mpr hx)
  gradient x hx := by
    rw [reflected_conjugate_gradient k x hx]
    simpa only [norm_neg] using k.gradient (-x) (neg_ne_zero.mpr hx)


/-- Translation as a unitary operator on native Euclidean L² classes. -/
def translationL2 (a : Space d) : L2 𝕜 d ≃ₗᵢ[𝕜] L2 𝕜 d :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ 𝕜 (fun x : Space d => x - a)
      (measurePreserving_sub_right volume a)) (by
    intro f
    refine ⟨Lp.compMeasurePreserving (fun x : Space d => x + a)
      (measurePreserving_add_right volume a) f, ?_⟩
    apply Lp.ext
    have h := (measurePreserving_sub_right (volume : Measure (Space d)) a).quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume a))
    filter_upwards [Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (fun x : Space d => x + a)
        (measurePreserving_add_right volume a) f)
      (measurePreserving_sub_right volume a), h] with x hx hy
    exact hx.trans (by simpa only [Function.comp_apply, sub_add_cancel] using hy))

theorem translationL2_coe (a : Space d) (f : L2 𝕜 d) :
    (translationL2 (𝕜 := 𝕜) a f : Space d → 𝕜) =ᵐ[volume] fun x => f (x - a) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume a)

/-- Commutation with translations passes to the Hilbert adjoint. -/
theorem adjoint_translation_invariant (T : StandardConvolutionOperator 𝕜 d) :
    TranslationInvariant T.operator.adjoint := by
  have hc (a : Space d) :
      T.operator.comp (translationL2 (𝕜 := 𝕜) a : L2 𝕜 d →L[𝕜] L2 𝕜 d) =
        (translationL2 (𝕜 := 𝕜) a : L2 𝕜 d →L[𝕜] L2 𝕜 d).comp T.operator := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    exact (T.translation_invariant a f (translationL2 (𝕜 := 𝕜) a f)
      (translationL2_coe a f)).trans (translationL2_coe a (T.operator f)).symm
  intro a f g hg
  have hgi : g = translationL2 (𝕜 := 𝕜) a f := Lp.ext (hg.trans (translationL2_coe a f).symm)
  rw [hgi]
  have hh : T.operator.adjoint.comp (translationL2 (𝕜 := 𝕜) a : L2 𝕜 d →L[𝕜] L2 𝕜 d) =
      (translationL2 (𝕜 := 𝕜) a : L2 𝕜 d →L[𝕜] L2 𝕜 d).comp T.operator.adjoint := by
    have he : T.operator.comp ((translationL2 (𝕜 := 𝕜) a).symm : L2 𝕜 d →L[𝕜] L2 𝕜 d) =
        ((translationL2 (𝕜 := 𝕜) a).symm : L2 𝕜 d →L[𝕜] L2 𝕜 d).comp T.operator := by
      apply ContinuousLinearMap.ext
      intro v
      apply (translationL2 (𝕜 := 𝕜) a).injective
      have ht := DFunLike.congr_fun (hc a) ((translationL2 (𝕜 := 𝕜) a).symm v)
      change T.operator ((translationL2 (𝕜 := 𝕜) a) ((translationL2 (𝕜 := 𝕜) a).symm v)) =
        (translationL2 (𝕜 := 𝕜) a) (T.operator ((translationL2 (𝕜 := 𝕜) a).symm v)) at ht
      rw [LinearIsometryEquiv.apply_symm_apply] at ht
      change (translationL2 (𝕜 := 𝕜) a) (T.operator ((translationL2 (𝕜 := 𝕜) a).symm v)) =
        (translationL2 (𝕜 := 𝕜) a) ((translationL2 (𝕜 := 𝕜) a).symm (T.operator v))
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact ht.symm
    have ha := congrArg ContinuousLinearMap.adjoint he
    simpa only [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm,
      LinearIsometryEquiv.symm_symm] using ha.symm
  have heq := DFunLike.congr_fun hh f
  change T.operator.adjoint (translationL2 (𝕜 := 𝕜) a f) =
    translationL2 (𝕜 := 𝕜) a (T.operator.adjoint f) at heq
  rw [heq]
  exact translationL2_coe a (T.operator.adjoint f)

theorem reflected_conjugate_bounds : ReflectedConjugateBounds := by
  intro 𝕜 _ d k
  exact ⟨reflectedConjugateKernel k, fun _ => rfl, rfl⟩

theorem adjoint_translation : AdjointTranslationInvariant := by
  intro 𝕜 _ d T
  exact adjoint_translation_invariant T

def conjugateReflectedTest (φ : Tests 𝕜 d) : Tests 𝕜 d :=
  TestFunction.postcompCLM (RCLike.conjCLE (K := 𝕜)).toContinuousLinearMap
    (ExpandedFA.Distributions.ProperSupportConvolution.pullbackCLM
      (ContinuousLinearEquiv.neg ℝ : Space d ≃L[ℝ] Space d) φ)

@[simp] theorem conjugateReflectedTest_apply (φ : Tests 𝕜 d) (x : Space d) :
    conjugateReflectedTest φ x = star (φ (-x)) := rfl

def adjointDistribution (D : KernelDistribution 𝕜 d) : KernelDistribution 𝕜 d where
  toFun φ := star (D (conjugateReflectedTest φ))
  map_add' φ ψ := by
    have he : conjugateReflectedTest (φ + ψ) =
        conjugateReflectedTest φ + conjugateReflectedTest ψ := by
      ext x
      change star (φ (-x) + ψ (-x)) = star (φ (-x)) + star (ψ (-x))
      exact star_add _ _
    simp only [he, map_add, star_add]
  map_smul' c φ := by
    have he : conjugateReflectedTest (c • φ) = star c • conjugateReflectedTest φ := by
      ext x
      change star (c * φ (-x)) = star c * star (φ (-x))
      exact star_mul' _ _
    simp only [he, map_smul, smul_eq_mul, star_mul', star_star,
      RingHom.id_apply]
  cont := by
    exact RCLike.continuous_conj.comp (D.continuous.comp
      ((TestFunction.postcompCLM (RCLike.conjCLE (K := 𝕜)).toContinuousLinearMap).continuous.comp
        (ExpandedFA.Distributions.ProperSupportConvolution.pullbackCLM
          (ContinuousLinearEquiv.neg ℝ : Space d ≃L[ℝ] Space d)).continuous))

@[simp] theorem adjointDistribution_apply (D : KernelDistribution 𝕜 d) (φ : Tests 𝕜 d) :
    adjointDistribution D φ = star (D (conjugateReflectedTest φ)) := rfl

theorem conjugateReflectedTest_support (φ : Tests 𝕜 d) (hφ : (0 : Space d) ∉ tsupport φ) :
    (0 : Space d) ∉ tsupport (conjugateReflectedTest φ) := by
  have hs : tsupport (conjugateReflectedTest φ) ⊆
      (fun x : Space d => -x) ⁻¹' tsupport φ := by
    refine (tsupport_comp_subset (map_zero (starRingEnd 𝕜)) _).trans ?_
    exact tsupport_comp_subset_preimage φ continuous_neg
  intro h
  exact hφ (by simpa using hs h)

theorem adjointDistribution_off_zero (T : StandardConvolutionOperator 𝕜 d)
    (φ : Tests 𝕜 d) (hφ : (0 : Space d) ∉ tsupport φ) :
    adjointDistribution T.distribution φ =
      ∫ x, star (T.kernel.function (-x)) * φ x := by
  rw [adjointDistribution_apply,
    T.agrees_off_zero _ (conjugateReflectedTest_support φ hφ)]
  simp only [conjugateReflectedTest_apply]
  change (starRingEnd 𝕜) (∫ x, T.kernel.function x * star (φ (-x))) = _
  rw [← integral_conj]
  change (∫ x, star (T.kernel.function x * star (φ (-x)))) = _
  simp only [star_mul', star_star]
  simpa using (integral_neg_eq_self
    (fun x : Space d => star (T.kernel.function x) * φ (-x)) volume).symm


theorem adjointDistribution_pairing_of_transpose
    (htrans : ∀ (u : KernelDistribution 𝕜 d) (φ ψ : Tests 𝕜 d),
      (∫ x, u (reflectedTest φ x) * ψ x) =
        ∫ x, u (reflectedTest (reflectedTest ψ 0) x) * reflectedTest φ 0 x)
    (T : StandardConvolutionOperator 𝕜 d) (φ ψ : Tests 𝕜 d) :
    (∫ x, star (ψ x) * adjointDistribution T.distribution (reflectedTest φ x)) =
      inner 𝕜 (T.operator (testL2 ψ)) (testL2 φ) := by
  let a := conjugateReflectedTest φ
  let b := reflectedTest ψ 0
  have ha (x : Space d) : conjugateReflectedTest (reflectedTest φ x) =
      reflectedTest a (-x) := by
    ext y
    simp [a, conjugateReflectedTest_apply, reflectedTest, sub_eq_add_neg,
      add_comm]
  have hb : reflectedTest b 0 = ψ := by
    ext y
    simp [b, reflectedTest]
  have hc (x : Space d) : reflectedTest a 0 x = star (φ x) := by
    simp [a, reflectedTest]
  calc
    (∫ x, star (ψ x) * adjointDistribution T.distribution (reflectedTest φ x)) =
        ∫ x, star (T.distribution (reflectedTest a (-x)) * ψ x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [adjointDistribution_apply, ha, star_mul']
      exact mul_comm _ _
    _ = star (∫ x, T.distribution (reflectedTest a (-x)) * ψ x) := by
      exact integral_conj
    _ = star (∫ x, T.distribution (reflectedTest a x) * b x) := by
      congr 1
      simpa [b, reflectedTest] using (integral_neg_eq_self
        (fun x : Space d => T.distribution (reflectedTest a x) * ψ (-x)) volume)
    _ = star (∫ x, T.distribution (reflectedTest ψ x) * star (φ x)) := by
      rw [htrans, hb]
      simp only [hc]
    _ = inner 𝕜 (T.operator (testL2 ψ)) (testL2 φ) := by
      change (starRingEnd 𝕜) (∫ x, T.distribution (reflectedTest ψ x) * star (φ x)) = _
      rw [← integral_conj, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [T.kernel_action ψ, testL2_coe φ] with x hψ hφ
      simp only [RCLike.inner_apply', starRingEnd_apply, star_mul', star_star]
      rw [hψ, hφ]


namespace AdjointKernel
open ExpandedFA.Distributions
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

abbrev CoordinateTests (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  ExpandedFA.Distributions.Tests 𝕜 (⊤ : Opens (Domain d))

def reflectDomain (φ : CoordinateTests 𝕜 d) : CoordinateTests 𝕜 d := reflectedTranslate φ 0

@[simp] lemma reflectDomain_apply (φ : CoordinateTests 𝕜 d) (x : Domain d) :
    reflectDomain φ x = φ (-x) := by simp [reflectDomain]

lemma reflectedCoordinateFunction_reflect (φ : CoordinateTests 𝕜 d) {k : ℕ}
    (a : Fin k → Fin d) (x : Domain d) :
    reflectedCoordinateFunction (reflectDomain φ) a x =
      iteratedFDeriv ℝ k φ (-x) (fun j => coordinateVector (a j)) := by
  unfold reflectedCoordinateFunction reflectDomain
  let N : Domain d →L[ℝ] Domain d := -ContinuousLinearMap.id ℝ _
  have heq : ⇑(reflectedTranslate φ 0) = φ ∘ N := by
    funext z
    simp [N]
  rw [heq, N.iteratedFDeriv_comp_right φ.contDiff x (i := k) (by simp)]
  simp [N]


lemma integratedReflectedJet_reflect (φ ψ : CoordinateTests 𝕜 d) (m : ℕ) :
    integratedReflectedJet φ ψ m =
      integratedReflectedJet (reflectDomain ψ) (reflectDomain φ) m := by
  ext a y
  rw [integratedReflectedJet_apply_by_parts, integratedReflectedJet_apply]
  simp_rw [reflectDomain_apply, reflectedCoordinateFunction_reflect]
  have he := integral_neg_eq_self (fun z : Domain d =>
    φ z * iteratedFDeriv ℝ a.1.val ψ (z+y) (fun j => coordinateVector (a.2 j))) volume
  simpa only [neg_neg, neg_sub, neg_add_rev, sub_eq_add_neg, add_comm] using he.symm

lemma distributionConvolution_transpose_reflect
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (φ ψ : CoordinateTests 𝕜 d) :
    (∫ x, distributionConvolution u φ x * ψ x) =
      ∫ x, distributionConvolution u (reflectDomain ψ) x * reflectDomain φ x := by
  obtain ⟨K, hK⟩ := reflectedTranslate_common_support φ (tsupport ψ) ψ.hasCompactSupport
  obtain ⟨K', hK'⟩ := reflectedTranslate_common_support (reflectDomain ψ)
    (tsupport (reflectDomain φ)) (reflectDomain φ).hasCompactSupport
  obtain ⟨m,L,hL⟩ := distribution_finiteJet_factorization u (K ⊔ K')
  rw [distributionConvolution_transpose_finiteJet u φ ψ (K ⊔ K')
    (fun x hx => (hK x hx).trans (by exact le_sup_left)) m L hL,
    distributionConvolution_transpose_finiteJet u (reflectDomain ψ) (reflectDomain φ)
    (K ⊔ K') (fun x hx => (hK' x hx).trans (by exact le_sup_right)) m L hL,
    integratedReflectedJet_reflect]

open StandardConvolution
open ExpandedFA.Distributions.ProperSupportConvolution

def toCoordinatesTest (φ : StandardConvolution.Tests 𝕜 d) : CoordinateTests 𝕜 d :=
  pullbackCLM (EuclideanSpace.equiv (Fin d) ℝ).symm φ

def toCoordinatesDistribution (u : KernelDistribution 𝕜 d) :
    ScalarDistribution 𝕜 (⊤ : Opens (Domain d)) :=
  u.comp (pullbackCLM (EuclideanSpace.equiv (Fin d) ℝ))

lemma toCoordinates_convolution (u : KernelDistribution 𝕜 d)
    (φ : StandardConvolution.Tests 𝕜 d) (x : Domain d) :
    distributionConvolution (toCoordinatesDistribution u) (toCoordinatesTest φ) x =
      u (reflectedTest φ ((EuclideanSpace.equiv (Fin d) ℝ).symm x)) := by
  change u (pullbackCLM (EuclideanSpace.equiv (Fin d) ℝ)
    (reflectedTranslate (toCoordinatesTest φ) x)) = _
  congr 1

lemma toCoordinates_reflect (φ : StandardConvolution.Tests 𝕜 d) :
    reflectDomain (toCoordinatesTest φ) = toCoordinatesTest (reflectedTest φ 0) := by
  ext x
  simp [toCoordinatesTest, reflectedTest]

lemma convolution_transpose_euclidean
    (u : KernelDistribution 𝕜 d) (φ ψ : StandardConvolution.Tests 𝕜 d) :
    (∫ x, u (reflectedTest φ x) * ψ x) =
      ∫ x, u (reflectedTest (reflectedTest ψ 0) x) * reflectedTest φ 0 x := by
  have he := distributionConvolution_transpose_reflect (toCoordinatesDistribution u)
    (toCoordinatesTest φ) (toCoordinatesTest ψ)
  simp_rw [toCoordinates_reflect, toCoordinates_convolution] at he
  simp only [toCoordinatesTest, pullbackCLM_apply] at he
  change (∫ x : Domain d,
    (fun z : Space d => u (reflectedTest φ z) * ψ z) (WithLp.toLp 2 x)) =
      ∫ x : Domain d,
    (fun z : Space d => u (reflectedTest (reflectedTest ψ 0) z) * reflectedTest φ 0 z)
      (WithLp.toLp 2 x) at he
  calc
    _ = ∫ x : Domain d, u (reflectedTest φ (WithLp.toLp 2 x)) * ψ (WithLp.toLp 2 x) :=
      ((PiLp.volume_preserving_toLp (Fin d)).integral_comp
        (MeasurableEquiv.toLp 2 (Domain d)).measurableEmbedding
        (fun z : Space d => u (reflectedTest φ z) * ψ z)).symm
    _ = _ := he
    _ = _ := (PiLp.volume_preserving_toLp (Fin d)).integral_comp
        (MeasurableEquiv.toLp 2 (Domain d)).measurableEmbedding
        (fun z : Space d => u (reflectedTest (reflectedTest ψ 0) z) * reflectedTest φ 0 z)

end AdjointKernel

namespace AdjointKernel

open ExpandedFA.Distributions.ProperSupportConvolution

theorem kernelConvolution_smooth (K : KernelDistribution 𝕜 d) (φ : Tests 𝕜 d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => K (reflectedTest φ x)) := by
  let e : Space d ≃L[ℝ] ExpandedFA.Distributions.Domain d := EuclideanSpace.equiv (Fin d) ℝ
  let u : ExpandedFA.Distributions.ScalarDistribution 𝕜
      (⊤ : Opens (ExpandedFA.Distributions.Domain d)) := K.comp (pullbackCLM e)
  let φ' : ExpandedFA.Distributions.Tests 𝕜
      (⊤ : Opens (ExpandedFA.Distributions.Domain d)) := pullbackCLM e.symm φ
  have he (x : Space d) :
      pullbackCLM e (ExpandedFA.Distributions.reflectedTranslate φ' (e x)) =
        reflectedTest φ x := by
    ext y
    simp only [pullbackCLM_apply, ExpandedFA.Distributions.reflectedTranslate,
      TestFunction.coe_mk, φ', map_sub, ContinuousLinearEquiv.symm_apply_apply,
      reflectedTest]
  have h := (ExpandedFA.Distributions.distributionConvolution_smooth u φ').comp e.contDiff
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : Space d => u (ExpandedFA.Distributions.reflectedTranslate φ' (e x))) at h
  simpa only [u, ContinuousLinearMap.comp_apply, he] using h

theorem kernelConvolution_locallyIntegrable (K : KernelDistribution 𝕜 d) (φ : Tests 𝕜 d) :
    LocallyIntegrable (fun x => K (reflectedTest φ x)) (volume : Measure (Space d)) :=
  (kernelConvolution_smooth K φ).continuous.locallyIntegrable

end AdjointKernel

/-- Smooth test pairings identify the actual Hilbert adjoint output without
assuming in advance that the distributional convolution belongs to L². -/
theorem adjoint_kernel_action_of_pairing
    (T : StandardConvolutionOperator 𝕜 d) (D : KernelDistribution 𝕜 d)
    (hcont : ∀ φ : Tests 𝕜 d, Continuous (fun x => D (reflectedTest φ x)))
    (hpair : ∀ φ ψ : Tests 𝕜 d,
      (∫ x, star (ψ x) * D (reflectedTest φ x)) =
        inner 𝕜 (T.operator (testL2 ψ)) (testL2 φ)) :
    ∀ φ : Tests 𝕜 d,
      (T.operator.adjoint (testL2 φ) : Space d → 𝕜) =ᵐ[volume]
        fun x => D (reflectedTest φ x) := by
  intro φ
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp _).locallyIntegrable (by norm_num))
    (hcont φ).locallyIntegrable
  intro g hg hgs
  let ψ : Tests 𝕜 d :=
    { toFun := fun x => (g x : 𝕜)
      contDiff' := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp hg
      hasCompactSupport' := hgs.comp_left (by simp)
      tsupport_subset' := subset_univ _ }
  calc
    (∫ x, g x • (T.operator.adjoint (testL2 φ)) x) =
        inner 𝕜 (testL2 ψ) (T.operator.adjoint (testL2 φ)) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(ψ.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport).coeFn_toLp]
        with x hx
      simp only [RCLike.inner_apply', starRingEnd_apply, testL2] at *
      rw [hx]
      change g x • _ = star (g x : 𝕜) * _
      simp [Algebra.smul_def]
    _ = inner 𝕜 (T.operator (testL2 ψ)) (testL2 φ) :=
      T.operator.adjoint_inner_right _ _
    _ = ∫ x, star (ψ x) * D (reflectedTest φ x) := (hpair φ ψ).symm
    _ = ∫ x, g x • D (reflectedTest φ x) := by
      apply integral_congr_ae
      filter_upwards with x
      change star (g x : 𝕜) * _ = g x • _
      simp [Algebra.smul_def]

/-- The actual Hilbert adjoint, with its full distribution-kernel data. -/
def adjointConvolutionOperator (T : StandardConvolutionOperator 𝕜 d) :
    StandardConvolutionOperator 𝕜 d where
  operator := T.operator.adjoint
  translation_invariant := adjoint_translation_invariant T
  distribution := adjointDistribution T.distribution
  kernel := reflectedConjugateKernel T.kernel
  agrees_off_zero := adjointDistribution_off_zero T
  kernel_action := adjoint_kernel_action_of_pairing T (adjointDistribution T.distribution)
    (fun φ => (AdjointKernel.kernelConvolution_smooth _ φ).continuous)
    (adjointDistribution_pairing_of_transpose AdjointKernel.convolution_transpose_euclidean T)

/-- Adjoint closure in the original standard convolution setting. -/
theorem adjoint_setting : AdjointSetting := by
  intro 𝕜 _ d T
  exact ⟨adjointConvolutionOperator T, rfl, fun _ _ => rfl⟩

section Duality

variable {X : Type} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]

/-- Pointwise scalar conjugation, lifted to ordinary a.e. Lp classes. -/
def conjugationLp (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp 𝕜 p μ →L⋆[𝕜] Lp 𝕜 p μ :=
  (starL 𝕜 : 𝕜 ≃L⋆[𝕜] 𝕜).toContinuousLinearMap.compLpL p μ

theorem conjugationLp_coe (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp 𝕜 p μ) :
    (conjugationLp μ p f : X → 𝕜) =ᵐ[μ] fun x => star (f x) :=
  ContinuousLinearMap.coeFn_compLpL _ _

theorem conjugationLp_norm (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp 𝕜 p μ) : ‖conjugationLp μ p f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (conjugationLp_coe μ p f)]
  exact congrArg ENNReal.toReal (eLpNorm_star (f := (f : X → 𝕜)))

/-- Conjugating twice makes a scalar-linear operator, also over complex scalars. -/
def conjugateOperator (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (R : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ) : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ :=
  (conjugationLp μ p).comp (R.comp (conjugationLp μ p))

/-- The accepted integral duality packaged with its scalar-linear inverse. -/
def pairingEquiv (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate q p]
    (hq : q ≠ ∞) : Lp 𝕜 p μ ≃ₗᵢ[𝕜] (Lp 𝕜 q μ →L[𝕜] 𝕜) :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (lpIntegralPairing μ q p).toLinearMap
      norm_map' := fun f => lp_pairing_exact_norm μ q p hq (Or.inl inferInstance) f }
    (lp_pairing_sigmaFinite_isometric_bijective μ q p hq).2.2

/-- Transpose the conjugated realization of the Hilbert adjoint, and return
from the scalar-linear dual to Lp by the accepted integral pairing. -/
def dualityTransfer (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate q p]
    (hq : q ≠ ∞) (R : Lp 𝕜 q μ →L[𝕜] Lp 𝕜 q μ) :
    Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ :=
  (pairingEquiv μ p q hq).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((ContinuousLinearMap.compL 𝕜 (Lp 𝕜 q μ) (Lp 𝕜 q μ) 𝕜).flip
      (conjugateOperator μ q R)).comp (lpIntegralPairing μ q p))

theorem dualityTransfer_pairing (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate q p]
    (hq : q ≠ ∞) (R : Lp 𝕜 q μ →L[𝕜] Lp 𝕜 q μ)
    (f : Lp 𝕜 p μ) (g : Lp 𝕜 q μ) :
    (∫ x, g x * dualityTransfer μ p q hq R f x ∂μ) =
      ∫ x, conjugateOperator μ q R g x * f x ∂μ := by
  have he := (pairingEquiv (𝕜 := 𝕜) μ p q hq).apply_symm_apply
    ((lpIntegralPairing μ q p f).comp (conjugateOperator μ q R))
  have h := congrArg (fun L : Lp 𝕜 q μ →L[𝕜] 𝕜 => L g) he
  change lpIntegralPairing μ q p (dualityTransfer μ p q hq R f) g =
    lpIntegralPairing μ q p f (conjugateOperator μ q R g) at h
  exact (lp_pairing_integral μ q p _ _).2.symm.trans
    (h.trans (lp_pairing_integral μ q p _ _).2)

/-- Duality preserves the norm bound of the adjoint realization. -/
theorem dualityTransfer_bound (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate q p]
    (hq : q ≠ ∞) (R : Lp 𝕜 q μ →L[𝕜] Lp 𝕜 q μ)
    (f : Lp 𝕜 p μ) : ‖dualityTransfer μ p q hq R f‖ ≤ ‖R‖ * ‖f‖ := by
  have hB : ‖conjugateOperator μ q R‖ ≤ ‖R‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R)
    intro g
    change ‖conjugationLp μ q (R (conjugationLp μ q g))‖ ≤ _
    rw [conjugationLp_norm]
    simpa only [conjugationLp_norm] using R.le_opNorm (conjugationLp μ q g)
  change ‖(pairingEquiv μ p q hq).symm
    ((lpIntegralPairing μ q p f).comp (conjugateOperator μ q R))‖ ≤ _
  rw [(pairingEquiv μ p q hq).symm.norm_map]
  calc
    _ ≤ ‖lpIntegralPairing μ q p f‖ * ‖conjugateOperator μ q R‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖f‖ * ‖R‖ := mul_le_mul
      (lp_pairing_norm_bound μ q p f) hB (norm_nonneg _) (norm_nonneg _)
    _ = _ := mul_comm _ _

/-- The transfer agrees on the entire Lp ∩ L² intersection. This proof
uses finite-measure indicators to identify densities of different exponents. -/
theorem dualityTransfer_agrees (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
    [hp : Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate q p]
    (hq : q ≠ ∞) (B : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ)
    (R : Lp 𝕜 q μ →L[𝕜] Lp 𝕜 q μ)
    (hR : ∀ (g : X → 𝕜) (hgq : MemLp g q μ) (hg2 : MemLp g 2 μ),
      (R (hgq.toLp g) : X → 𝕜) =ᵐ[μ] (B.adjoint (hg2.toLp g) : X → 𝕜))
    (f : X → 𝕜) (hfp : MemLp f p μ) (hf2 : MemLp f 2 μ) :
    (dualityTransfer μ p q hq R (hfp.toLp f) : X → 𝕜) =ᵐ[μ]
      (B (hf2.toLp f) : X → 𝕜) := by
  have htest (g : X → 𝕜) (hgq : MemLp g q μ) (hg2 : MemLp g 2 μ) :
      (∫ x, g x * dualityTransfer μ p q hq R (hfp.toLp f) x ∂μ) =
        ∫ x, g x * B (hf2.toLp f) x ∂μ := by
    let v : Lp 𝕜 2 μ := hg2.star.toLp (star g)
    have hc : conjugationLp μ q (hgq.toLp g) = hgq.star.toLp (star g) := by
      apply Lp.ext
      filter_upwards [conjugationLp_coe μ q (hgq.toLp g), hgq.coeFn_toLp,
        hgq.star.coeFn_toLp] with x hx hy hz
      exact hx.trans ((congrArg star hy).trans hz.symm)
    have hae : (conjugateOperator μ q R (hgq.toLp g) : X → 𝕜) =ᵐ[μ]
        fun x => star (B.adjoint v x) := by
      have ht := conjugationLp_coe μ q (R (conjugationLp μ q (hgq.toLp g)))
      rw [hc] at ht
      exact ht.trans ((hR (star g) hgq.star hg2.star).fun_comp star)
    calc
      (∫ x, g x * dualityTransfer μ p q hq R (hfp.toLp f) x ∂μ) =
          ∫ x, (hgq.toLp g) x * dualityTransfer μ p q hq R (hfp.toLp f) x ∂μ :=
        integral_congr_ae (hgq.coeFn_toLp.symm.mul EventuallyEq.rfl)
      _ = ∫ x, conjugateOperator μ q R (hgq.toLp g) x * (hfp.toLp f) x ∂μ :=
        dualityTransfer_pairing μ p q hq R _ _
      _ = inner 𝕜 (B.adjoint v) (hf2.toLp f) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hae, hfp.coeFn_toLp, hf2.coeFn_toLp] with x hx hy hz
        simp only [hx, hy, hz, RCLike.inner_apply', starRingEnd_apply]
      _ = inner 𝕜 v (B (hf2.toLp f)) := B.adjoint_inner_left _ _
      _ = ∫ x, g x * B (hf2.toLp f) x ∂μ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hg2.star.coeFn_toLp] with x hx
        simp only [RCLike.inner_apply', starRingEnd_apply, v, hx, Pi.star_apply, star_star]
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ hs => integrableOn_Lp_of_measure_ne_top _ hp.out hs.ne)
    (fun s _ hs => integrableOn_Lp_of_measure_ne_top _ (by norm_num) hs.ne)
  intro s hs hμs
  let g : X → 𝕜 := s.indicator (fun _ => 1)
  have hm (r : ℝ≥0∞) : MemLp g r μ :=
    memLp_indicator_const r hs.nullMeasurableSet 1 (Or.inr hμs.ne)
  have ht := htest g (hm q) (hm 2)
  simpa only [g, ← indicator_mul_left, one_mul, integral_indicator hs] using ht


theorem adjoint_duality_transfer : AdjointDualityTransfer := by
  intro X _ 𝕜 _ μ _ p q _ _ _ hq B R hR
  exact ⟨dualityTransfer μ p q hq R, dualityTransfer_bound μ p q hq R,
    dualityTransfer_agrees μ p q hq B R hR⟩

end Duality

/-- Assemble all exponents from the lower and upper halves, then use common
simple approximation to obtain every whole-intersection compatibility. -/
theorem compatible_family_of_high_extensions
    (hhigh : ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
      (T : StandardConvolutionOperator 𝕜 d) (p : InteriorExponent), 2 < p.val →
      ∃ S : LpSpace 𝕜 d p.val →L[𝕜] LpSpace 𝕜 d p.val, AgreesWithL2 T p S) :
    CompatibleFamily := by
  classical
  intro 𝕜 _ d T
  have hex (p : InteriorExponent) :
      ∃ S : LpSpace 𝕜 d p.val →L[𝕜] LpSpace 𝕜 d p.val, AgreesWithL2 T p S := by
    rcases lt_trichotomy p.val 2 with hp | hp | hp
    · obtain ⟨S, hS, _⟩ := low_strong_extensions 𝕜 d T p hp
      exact ⟨S, hS⟩
    · rcases p with ⟨v, hv, hvTop⟩
      dsimp at hp
      subst v
      exact ⟨T.operator, fun f _ _ => EventuallyEq.rfl⟩
    · exact hhigh 𝕜 d T p hp
  choose S hS using hex
  refine ⟨S, hS, ?_, ?_⟩
  · intro p q f hp hq
    exact compatible_of_core T p.val q.val p.lt_top.ne q.lt_top.ne (S p) (S q)
      (fun f _ h2 hp => hS p f hp h2) (fun f _ h2 hq => hS q f hq h2) f hp hq
  · intro W hW p f h1 hp
    exact compatible_weak_of_core T p.val p.lt_top.ne (S p)
      (fun f _ h2 hp => hS p f hp h2) W hW f hp h1

/-- The upper half follows from a standard convolution realization of T*.
No regularity, support or boundedness premise is added to the Lp input. -/
theorem high_extension_of_adjoint
    (T A : StandardConvolutionOperator 𝕜 d) (hA : A.operator = T.operator.adjoint)
    (p : InteriorExponent) (hp2 : 2 < p.val) :
    ∃ S : LpSpace 𝕜 d p.val →L[𝕜] LpSpace 𝕜 d p.val, AgreesWithL2 T p S := by
  let q := ENNReal.conjExponent p.val
  have hq1 : 1 < q :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p.val q).mp p.lt_top
  have hqTop : q < ∞ :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt q p.val).mpr p.one_lt
  have hq2 : q < 2 := by
    have hs : 1 < p.val - 1 := by
      exact (lt_tsub_iff_right).mpr (by norm_num only [one_add_one_eq_two]; exact hp2)
    change 1 + (p.val - 1)⁻¹ < 2
    have hi : (p.val - 1)⁻¹ < 1 := ENNReal.inv_lt_one.mpr hs
    calc
      1 + (p.val - 1)⁻¹ < 1 + 1 := ENNReal.add_lt_add_left (by norm_num) hi
      _ = 2 := by norm_num
  have : Fact (1 ≤ q) := ⟨hq1.le⟩
  let r : InteriorExponent := ⟨q, hq1, hqTop⟩
  obtain ⟨R, hR, _⟩ := low_strong_extensions 𝕜 d A r hq2
  refine ⟨dualityTransfer volume p.val q hqTop.ne R, ?_⟩
  intro f hfp hf2
  apply dualityTransfer_agrees volume p.val q hqTop.ne T.operator R ?_ f hfp hf2
  intro g hgq hg2
  simpa only [hA] using hR g hgq hg2

/-- Adjoint closure supplies the upper half through scalar-linear duality. -/
theorem compatible_family_of_adjoint_setting (h : AdjointSetting) : CompatibleFamily := by
  apply compatible_family_of_high_extensions
  intro 𝕜 _ d T p hp2
  obtain ⟨A, hA, _⟩ := h 𝕜 d T
  exact high_extension_of_adjoint T A hA p hp2

/-- The complete standard convolution Calderón–Zygmund strong theorem, with
compatibility on every pairwise intersection and with the weak L¹ extension. -/
theorem compatible_family : CompatibleFamily :=
  compatible_family_of_adjoint_setting adjoint_setting

end ExpandedFA.SingularIntegrals.CZLp
