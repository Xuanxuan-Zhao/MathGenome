import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.SobolevFormBridge
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.GalerkinExistence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevCompleteness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.NegativeSobolevRepresentation
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped NNReal ENNReal InnerProductSpace ComplexConjugate
namespace ExpandedFA.PartV.SobolevFormBridge
open ExpandedFA.Sobolev ExpandedFA.Sobolev.NegativeSobolev ExpandedFA.Distributions
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}

@[simp] theorem gradientMap_coe (u : W 𝕜 Ω) :
    gradientMap u =ᵐ[volume.restrict (Ω : Set (Domain d))] gradientFunction u.val :=
  (gradientMemLp u).coeFn_toLp

theorem gradient_inner (u v : W 𝕜 Ω) :
    ⟪gradientMap u, gradientMap v⟫_𝕜 =
      ∑ i : Fin d, ⟪u.val.val (coordinateIndex i), v.val.val (coordinateIndex i)⟫_𝕜 := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, ∑ i : Fin d, ⟪u.val.val (coordinateIndex i) x,
        v.val.val (coordinateIndex i) x⟫_𝕜
        ∂(volume.restrict (Ω : Set (Domain d))) := by
      apply integral_congr_ae
      filter_upwards [gradientMap_coe u, gradientMap_coe v] with x hu hv
      rw [hu, hv, PiLp.inner_apply]
      rfl
    _ = _ := by
      rw [integral_finsetSum]
      · rfl
      · intro i _
        exact L2.integrable_inner _ _

theorem gradient_norm_sq (u : W 𝕜 Ω) :
    ‖gradientMap u‖ ^ 2 = ∑ i : Fin d, ‖u.val.val (coordinateIndex i)‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), gradient_inner, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (norm_sq_eq_re_inner (𝕜 := 𝕜) _).symm

theorem gradient_norm : Spec.GradientNorm := by
  intro 𝕜 _ d Ω u
  refine ⟨?_, gradient_norm_sq u⟩
  change ‖(gradientMemLp u).toLp _‖ = _
  rw [Lp.norm_toLp]
  rfl

theorem coordinate_norm_le_gradient (u : W 𝕜 Ω) (i : Fin d) :
    ‖u.val.val (coordinateIndex i)‖ ≤ ‖gradientMap u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [gradientMap_coe u] with x hx
  rw [hx]
  exact PiLp.norm_apply_le (gradientFunction u.val x) i

theorem gradient_norm_le_full (u : W 𝕜 Ω) : ‖gradientMap u‖ ≤ ‖u‖ := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i : Fin d => ‖u.val.val (coordinateIndex i)‖)
    (fun i _ => norm_nonneg _)
  have hn : 0 ≤ ∑ i : Fin d, ‖u.val.val (coordinateIndex i)‖ :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  have hle : ‖gradientMap u‖ ≤ ∑ i : Fin d, ‖u.val.val (coordinateIndex i)‖ := by
    rw [← gradient_norm_sq] at hs
    nlinarith [norm_nonneg (gradientMap u)]
  exact hle.trans (by
    rw [full_norm 𝕜 d Ω 2 (by norm_num) u]
    exact le_add_of_nonneg_left (norm_nonneg _))

def gradientCLM : W 𝕜 Ω →L[𝕜] VectorL2 𝕜 Ω :=
  @LinearMap.mkContinuous 𝕜 𝕜 (W 𝕜 Ω) (VectorL2 𝕜 Ω)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id 𝕜) gradientMap 1
    (fun u => by simpa only [one_mul] using gradient_norm_le_full u)

/-- Poincaré and the elementary finite-dimensional ℓ¹/ℓ² comparison. -/
theorem full_norm_le_gradientL2 (hΩ : EnergyScope Ω) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : W 𝕜 Ω, ‖u‖ ≤ K * ‖gradientMap u‖ := by
  obtain ⟨K, hK, hb⟩ := full_norm_le_gradient (𝕜 := 𝕜) hΩ.1 hΩ.2
  refine ⟨K * (d + 1), by positivity, fun u => ?_⟩
  have hs : ‖gradientJet u‖ ≤ (d : ℝ) * ‖gradientMap u‖ := by
    rw [gradientJet_norm]
    calc
      _ ≤ ∑ _i : Fin d, ‖gradientMap u‖ :=
        Finset.sum_le_sum fun i _ => coordinate_norm_le_gradient u i
      _ = _ := by simp
  calc
    ‖u‖ ≤ K * ‖gradientJet u‖ := hb 2 (by norm_num) u
    _ ≤ K * ((d : ℝ) * ‖gradientMap u‖) :=
      mul_le_mul_of_nonneg_left hs (by linarith)
    _ ≤ (K * (d + 1)) * ‖gradientMap u‖ := by
      nlinarith [norm_nonneg (gradientMap u)]

theorem gradient_antilipschitz (hΩ : EnergyScope Ω) :
    ∃ K : ℝ≥0, AntilipschitzWith K (gradientCLM (𝕜 := 𝕜) (Ω := Ω)) := by
  obtain ⟨K, hK, hb⟩ := full_norm_le_gradientL2 (𝕜 := 𝕜) hΩ
  refine ⟨⟨K, hK.le⟩, ?_⟩
  apply AddMonoidHomClass.antilipschitz_of_bound
  exact hb

theorem energy_complete (hΩ : EnergyScope Ω) : CompleteSpace (Energy 𝕜 Ω) := by
  haveI := sobolev_complete 𝕜 d Ω 1 2
  haveI : CompleteSpace (W 𝕜 Ω) :=
    (Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.smoothSubmodule
      𝕜 d Ω 1 2).isClosed_topologicalClosure.completeSpace_coe
  obtain ⟨K, hK⟩ := gradient_antilipschitz (𝕜 := 𝕜) hΩ
  exact (hK.isClosed_range gradientCLM.uniformContinuous).completeSpace_coe

/-- The inverse exists on precisely the original W₀, with continuity proved
from Poincaré; no completeness or injectivity certificate is assumed. -/
def energyEquiv (hΩ : EnergyScope Ω) : W 𝕜 Ω ≃L[𝕜] Energy 𝕜 Ω := by
  let hK := (gradient_antilipschitz (𝕜 := 𝕜) hΩ).choose_spec
  let e := LinearEquiv.ofInjective gradientMap hK.injective
  refine { e with continuous_toFun := ?_, continuous_invFun := ?_ }
  · exact gradientCLM.continuous.subtype_mk _
  · apply (hK.isEmbedding gradientCLM.continuous).continuous_iff.mpr
    change Continuous (fun v : Energy 𝕜 Ω => gradientMap (e.symm v))
    have heq : (fun v : Energy 𝕜 Ω => gradientMap (e.symm v)) = Subtype.val := by
      funext v
      exact congrArg Subtype.val (e.apply_symm_apply v)
    rw [heq]
    exact continuous_subtype_val

@[simp] theorem energyEquiv_coe (hΩ : EnergyScope Ω) (u : W 𝕜 Ω) :
    (energyEquiv (𝕜 := 𝕜) hΩ u).val = gradientMap u := by
  rfl

theorem hilbert_realization : Spec.HilbertRealization := by
  intro 𝕜 _ d Ω hΩ
  refine ⟨energy_complete hΩ, energyEquiv hΩ, energyEquiv_coe hΩ, ?_, ?_⟩
  · intro u
    change ‖(energyEquiv hΩ u).val‖ = _
    rw [energyEquiv_coe]
    exact (gradient_norm 𝕜 d Ω u).1
  · intro u v
    change ⟪(energyEquiv hΩ u).val, (energyEquiv hΩ v).val⟫_𝕜 = _
    rw [energyEquiv_coe, energyEquiv_coe, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [gradientMap_coe u, gradientMap_coe v] with x hu hv
    rw [hu, hv]

theorem empty_space : Spec.EmptySpace := by
  intro 𝕜 _ d Ω he
  have hμ : volume.restrict (Ω : Set (Domain d)) = 0 := by rw [he, Measure.restrict_empty]
  have hw : Subsingleton (W 𝕜 Ω) := by
    constructor
    intro u v
    apply Subtype.ext
    apply sobolev_underlying_injective 𝕜 d Ω 1 2
    apply Lp.ext
    simp only [Filter.EventuallyEq, hμ, ae_zero, Filter.eventually_bot]
  haveI : Subsingleton (VectorL2 𝕜 Ω) := by
    constructor
    intro u v
    apply Lp.ext
    simp only [Filter.EventuallyEq, hμ, ae_zero, Filter.eventually_bot]
  exact ⟨hw, inferInstance⟩

theorem solvability : Spec.Solvability := by
  intro 𝕜 _ d Ω hΩ a c hc F
  haveI := energy_complete (𝕜 := 𝕜) hΩ
  exact GalerkinExistence.existence_uniqueness a c hc F

theorem coercive_isomorphism : Spec.CoerciveIsomorphism := by
  intro 𝕜 _ d Ω hΩ a c hc
  haveI := energy_complete (𝕜 := 𝕜) hΩ
  have hbij : Function.Bijective a.flip := by
    apply (Function.bijective_iff_existsUnique a.flip).mpr
    intro F
    obtain ⟨u, hu, hunique⟩ := solvability 𝕜 d Ω hΩ a c hc F
    refine ⟨u, ContinuousLinearMap.ext hu, fun z hz => hunique z ?_⟩
    intro v
    exact congrArg (fun L : Energy 𝕜 Ω →L⋆[𝕜] 𝕜 => L v) hz
  exact ⟨ContinuousLinearEquiv.ofBijective a.flip
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2), fun _ _ => rfl⟩

/-- Value conjugation, as opposed to precomposition by a Hilbert adjoint. -/
def dualToAnti {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (G : E →L[𝕜] 𝕜) : E →L⋆[𝕜] 𝕜 :=
  (starL 𝕜).toContinuousLinearMap.comp G

def antiToDual {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : E →L⋆[𝕜] 𝕜) : E →L[𝕜] 𝕜 :=
  (starL 𝕜).toContinuousLinearMap.comp F

theorem datum_conjugation : Spec.DatumConjugation := by
  intro 𝕜 _ E _ _
  constructor
  · intro G
    refine ⟨dualToAnti G, fun _ => rfl, ?_⟩
    apply ContinuousLinearMap.opNorm_ext
    intro x
    exact RCLike.norm_conj (G x)
  · intro F
    refine ⟨antiToDual F, fun _ => rfl, ?_⟩
    apply ContinuousLinearMap.opNorm_ext
    intro x
    exact RCLike.norm_conj (F x)

theorem negative_sobolev_bridge : Spec.NegativeSobolevBridge := by
  intro 𝕜 _ d Ω hΩ
  let e : W 𝕜 Ω ≃L[𝕜] Energy 𝕜 Ω := energyEquiv hΩ
  refine ⟨e, energyEquiv_coe hΩ, fun F => ?_⟩
  let G : W 𝕜 Ω →L[𝕜] 𝕜 := antiToDual (𝕜 := 𝕜) (E := W 𝕜 Ω) (F.comp e.toContinuousLinearMap)
  obtain ⟨f, _, hf, hn⟩ := full_representation 𝕜 d Ω 2 2 (by norm_num) G
  have hFG (u : W 𝕜 Ω) : F (e u) = conj (G u) := by
    change F (e u) = conj (conj (F (e u)))
    exact (star_star _).symm
  refine ⟨G, f, hFG, hf, hn, ?_⟩
  intro φ u hu
  rw [hFG]
  congr 1
  apply distribution_interpretation 𝕜 d Ω 2 2 (by norm_num) G f _ φ u hu
  intro v
  simpa only [Fintype.sum_option, firstIndex] using hf v

theorem derivative_data : Spec.DerivativeData := by
  intro 𝕜 _ d Ω hΩ
  let e : W 𝕜 Ω ≃L[𝕜] Energy 𝕜 Ω := energyEquiv hΩ
  refine ⟨e, energyEquiv_coe hΩ, fun F => ?_⟩
  let G : W 𝕜 Ω →L[𝕜] 𝕜 := antiToDual (𝕜 := 𝕜) (E := W 𝕜 Ω) (F.comp e.toContinuousLinearMap)
  obtain ⟨K, _, hb⟩ := derivative_representation 𝕜 d Ω hΩ.1 hΩ.2
  obtain ⟨_, f, _, _, hf, _⟩ := hb 2 2 (by norm_num) G
  refine ⟨f, fun u => ?_⟩
  rw [← hf u]
  change F (e u) = conj (conj (F (e u)))
  exact (star_star _).symm

section Matrix
variable (A : Domain d → Vector 𝕜 d →L[𝕜] Vector 𝕜 d) (M : ℝ)
  (hA : AEStronglyMeasurable A (volume.restrict (Ω : Set (Domain d))))
  (hM : ∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))), ‖A x‖ ≤ M)

include hA hM

/-- Bounded measurable coefficients act on actual vector-valued L² classes. -/
theorem matrixProduct_memLp (u : VectorL2 𝕜 Ω) :
    MemLp (fun x => A x (u x)) 2 (volume.restrict (Ω : Set (Domain d))) := by
  apply (Lp.memLp u).of_le_mul
  · exact (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
      hA (Lp.aestronglyMeasurable u))
  · filter_upwards [hM] with x hx
    exact (A x).le_opNorm (u x) |>.trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

def matrixProduct (u : VectorL2 𝕜 Ω) : VectorL2 𝕜 Ω :=
  (matrixProduct_memLp A M hA hM u).toLp (fun x => A x (u x))

@[simp] theorem matrixProduct_coe (u : VectorL2 𝕜 Ω) :
    matrixProduct A M hA hM u =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => A x (u x) :=
  (matrixProduct_memLp A M hA hM u).coeFn_toLp

def matrixMultiplier : VectorL2 𝕜 Ω →L[𝕜] VectorL2 𝕜 Ω :=
  LinearMap.mkContinuous
    { toFun := matrixProduct A M hA hM
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [matrixProduct_coe A M hA hM (u + v),
          matrixProduct_coe A M hA hM u, matrixProduct_coe A M hA hM v,
          Lp.coeFn_add u v, Lp.coeFn_add (matrixProduct A M hA hM u)
            (matrixProduct A M hA hM v)] with x huv hu hv hadd hsum
        rw [huv, hsum, Pi.add_apply, hu, hv, hadd, Pi.add_apply, map_add]
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [matrixProduct_coe A M hA hM (c • u),
          matrixProduct_coe A M hA hM u, Lp.coeFn_smul c u,
          Lp.coeFn_smul c (matrixProduct A M hA hM u)] with x hcu hu hsmul hprod
        simp only [RingHom.id_apply]
        rw [hcu, hprod, Pi.smul_apply, hu, hsmul, Pi.smul_apply, map_smul] }
    M (by
      intro u
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [matrixProduct_coe A M hA hM u, hM] with x hu hx
      change ‖matrixProduct A M hA hM u x‖ ≤ M * ‖u x‖
      rw [hu]
      exact ((A x).le_opNorm (u x)).trans
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _)))

@[simp] theorem matrixMultiplier_coe (u : VectorL2 𝕜 Ω) :
    matrixMultiplier A M hA hM u =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => A x (u x) := matrixProduct_coe A M hA hM u

def matrixForm : Hilbert.Conventions.Spec.BoundedSesquilinearFormValue
    𝕜 (Energy 𝕜 Ω) (Energy 𝕜 Ω) :=
  ((ContinuousLinearMap.compL 𝕜 (Energy 𝕜 Ω) (VectorL2 𝕜 Ω) 𝕜).flip
    ((matrixMultiplier A M hA hM).comp (Energy 𝕜 Ω).subtypeL)).comp
      ((innerSL 𝕜).comp (Energy 𝕜 Ω).subtypeL)

theorem matrixForm_apply (v u : Energy 𝕜 Ω) :
    matrixForm A M hA hM v u =
      ∫ x, ⟪v.val x, A x (u.val x)⟫_𝕜
        ∂(volume.restrict (Ω : Set (Domain d))) := by
  change ⟪v.val, matrixMultiplier A M hA hM u.val⟫_𝕜 = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [matrixMultiplier_coe A M hA hM u.val] with x hx
  rw [hx]

set_option maxHeartbeats 800000 in
theorem matrixForm_bound (hM0 : 0 ≤ M) : ‖matrixForm A M hA hM‖ ≤ M := by
  apply (matrixForm A M hA hM).opNorm_le_bound₂ hM0
  intro v u
  change ‖⟪v.val, matrixMultiplier A M hA hM u.val⟫_𝕜‖ ≤ _
  have hn : ‖matrixMultiplier A M hA hM‖ ≤ M :=
    LinearMap.mkContinuous_norm_le _ hM0 _
  calc
    _ ≤ ‖v.val‖ * ‖matrixMultiplier A M hA hM u.val‖ := norm_inner_le_norm _ _
    _ ≤ ‖v.val‖ * (M * ‖u.val‖) :=
      mul_le_mul_of_nonneg_left
        (((matrixMultiplier A M hA hM).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hn (norm_nonneg _))) (norm_nonneg _)
    _ = M * ‖v‖ * ‖u‖ := by change ‖v.val‖ * (M * ‖u.val‖) = M * ‖v.val‖ * ‖u.val‖; ring

theorem matrixForm_coercive (c : ℝ) (hc : 0 < c)
    (hell : ∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))),
      ∀ ξ, c * ‖ξ‖ ^ 2 ≤ RCLike.re ⟪ξ, A x ξ⟫_𝕜) :
    Hilbert.Conventions.Spec.FormCoerciveValue 𝕜 (Energy 𝕜 Ω)
      (matrixForm A M hA hM) c := by
  refine ⟨hc, fun u => ?_⟩
  have hi : Integrable (fun x => ⟪u.val x, A x (u.val x)⟫_𝕜)
      (volume.restrict (Ω : Set (Domain d))) := by
    apply (L2.integrable_inner u.val (matrixMultiplier A M hA hM u.val)).congr
    filter_upwards [matrixMultiplier_coe A M hA hM u.val] with x hx
    rw [hx]
  have hsq : Integrable (fun x => ‖u.val x‖ ^ 2)
      (volume.restrict (Ω : Set (Domain d))) := (Lp.memLp u.val).integrable_norm_pow (by norm_num)
  have heq : ∫ x, ‖u.val x‖ ^ 2 ∂(volume.restrict (Ω : Set (Domain d))) = ‖u.val‖ ^ 2 := by
    have h := norm_sq_eq_re_inner (𝕜 := 𝕜) u.val
    rw [L2.inner_def, ← integral_re (L2.integrable_inner u.val u.val)] at h
    simpa only [← norm_sq_eq_re_inner] using h.symm
  rw [matrixForm_apply, ← integral_re hi]
  change c * ‖u.val‖ ^ 2 ≤ _
  rw [← heq, ← integral_const_mul]
  apply integral_mono_ae (hsq.const_mul c) hi.re
  filter_upwards [hell] with x hx
  exact hx (u.val x)
end Matrix

theorem matrix_solvability : Spec.MatrixSolvability := by
  intro 𝕜 _ d Ω hΩ A M c hA hM0 hM hc hell
  let a := matrixForm A M hA hM
  have ha := matrixForm_coercive A M hA hM c hc hell
  exact ⟨a, matrixForm_apply A M hA hM, matrixForm_bound A M hA hM hM0,
    ha, solvability 𝕜 d Ω hΩ a c ha⟩

theorem matrixOperator_inner (A : Matrix (Fin d) (Fin d) 𝕜) (ξ η : Vector 𝕜 d) :
    ⟪ξ, matrixOperatorEquiv 𝕜 d A η⟫_𝕜 =
      ∑ i, conj (ξ i) * ∑ j, A i j * η j := by
  simp only [PiLp.inner_apply, RCLike.inner_apply']
  rfl

open scoped Matrix.Norms.Elementwise in
/-- The operator formulation applies to matrices bounded in the elementwise
supremum norm as well, with a fixed dimension-dependent constant. -/
theorem matrixOperator_norm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ B : Matrix (Fin d) (Fin d) 𝕜,
      ‖matrixOperatorEquiv 𝕜 d B‖ ≤ C * ‖B‖ :=
  SemilinearMapClass.bound_of_continuous (matrixOperatorEquiv 𝕜 d)
    (matrixOperatorEquiv 𝕜 d).toContinuousLinearEquiv.continuous

theorem matrix_entries : Spec.MatrixEntries := by
  intro 𝕜 _ d Ω hΩ A M c hA hM0 hM hc hell
  have hAc : AEStronglyMeasurable (fun x => matrixOperatorEquiv 𝕜 d (A x))
      (volume.restrict (Ω : Set (Domain d))) :=
    (matrixOperatorEquiv 𝕜 d).toContinuousLinearEquiv.continuous.comp_aestronglyMeasurable hA
  have he : ∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))),
      ∀ ξ, c * ‖ξ‖ ^ 2 ≤ RCLike.re ⟪ξ, matrixOperatorEquiv 𝕜 d (A x) ξ⟫_𝕜 := by
    filter_upwards [hell] with x hx
    intro ξ
    rw [matrixOperator_inner]
    exact hx ξ
  obtain ⟨a, ha, hb, hco, hs⟩ := matrix_solvability 𝕜 d Ω hΩ
    (fun x => matrixOperatorEquiv 𝕜 d (A x)) M c hAc hM0 hM hc he
  refine ⟨a, ?_, hb, hco, hs⟩
  intro v u
  rw [ha]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => matrixOperator_inner (A x) (v.val x) (u.val x)

theorem antidual_banach : Spec.AntidualBanach := by
  intro 𝕜 _ d Ω
  exact ⟨inferInstance, fun F G c v => ⟨rfl, rfl⟩⟩

end ExpandedFA.PartV.SobolevFormBridge
