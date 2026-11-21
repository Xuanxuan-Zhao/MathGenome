import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.PreHilbertCompactSpectral
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.PreHilbertCompletion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.CompactNormalClassification
import Mathlib.Topology.Algebra.InfiniteSum.GroupCompletion

/-!
Extend T to the Hilbert completion. Compact closure in E makes embedded
compact bounded images closed in the completion; density in open balls
therefore puts the whole extended range in E. Nonzero eigenvectors pull
back by dividing an extended image by its eigenvalue. The completion
isometry reflects the spectral HasSum statement with its specified limit Tx.

The real-complexification bridge below is constructed explicitly on pairs,
with its complex inner-product norm rather than the product supremum norm.
The coordinate equivalence is used only to prove compactness and completeness.
-/
noncomputable section
open scoped InnerProductSpace Topology
open Set
namespace ExpandedFA.Hilbert.PreHilbertCompactSpectral
universe u v
variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A compact image in E stays closed after embedding into its completion.
Using open balls with a little slack avoids any boundary approximation issue. -/
lemma completion_apply_mem_compact_image (T : E →L[𝕜] E)
    (hc : IsCompactOperator T) (r : ℝ) (x : UniformSpace.Completion E)
    (hx : ‖x‖ < r) :
    ∃ y ∈ closure (T '' Metric.ball (0 : E) r),
      T.completion x = (y : UniformSpace.Completion E) := by
  let i : E →ₗᵢ[𝕜] UniformSpace.Completion E := UniformSpace.Completion.toComplₗᵢ
  let K := closure (T '' Metric.ball (0 : E) r)
  have hK : IsCompact K := hc.isCompact_closure_image_ball r
  have hclosed : IsClosed (i '' K) := (hK.image i.continuous).isClosed
  have happrox : x ∈ closure (i '' Metric.ball (0 : E) r) := by
    have hd := UniformSpace.Completion.denseRange_coe (α := E)
    have h := hd.subset_closure_image_preimage_of_isOpen
      (Metric.isOpen_ball : IsOpen (Metric.ball (0 : UniformSpace.Completion E) r))
    have hx' : x ∈ Metric.ball (0 : UniformSpace.Completion E) r := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    have hp : (fun y : E => (y : UniformSpace.Completion E)) ⁻¹'
        Metric.ball (0 : UniformSpace.Completion E) r = Metric.ball (0 : E) r := by
      ext y
      simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right,
        UniformSpace.Completion.norm_coe]
    rw [hp] at h
    exact h hx'
  have hm : T.completion x ∈ i '' K := by
    apply closure_minimal ?_ hclosed
      (image_closure_subset_closure_image T.completion.continuous ⟨x, happrox, rfl⟩)
    rintro _ ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨T y, subset_closure ⟨y, hy, rfl⟩, (T.completion_apply_coe y).symm⟩
  obtain ⟨y, hy, he⟩ := hm
  exact ⟨y, hy, he.symm⟩

theorem completion_extension : Spec.CompletionExtension.{u,v} := by
  intro 𝕜 E _ _ _ T hT hcompact
  have hc : IsCompactOperator T :=
    (ExpandedFA.Compactness.compact_iff_isCompactOperator T.toLinearMap).mp hcompact
  have hsym : T.completion.IsSymmetric := by
    intro x y
    induction x, y using UniformSpace.Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y =>
      change inner 𝕜 (T.completion (x : UniformSpace.Completion E)) (y : UniformSpace.Completion E) =
        inner 𝕜 (x : UniformSpace.Completion E) (T.completion (y : UniformSpace.Completion E))
      rw [T.completion_apply_coe, T.completion_apply_coe,
        UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe]
      exact hT x y
  refine ⟨hsym, ?_, ?_⟩
  · apply (ExpandedFA.Compactness.compact_iff_isCompactOperator T.completion.toLinearMap).mpr
    apply (isCompactOperator_iff_image_ball_subset_compact T.completion.toLinearMap (by norm_num : (0:ℝ) < 1)).mpr
    refine ⟨(fun y : E => (y : UniformSpace.Completion E)) ''
      closure (T '' Metric.ball (0 : E) 2),
      (hc.isCompact_closure_image_ball 2).image (UniformSpace.Completion.continuous_coe E), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hx' : ‖x‖ < (2:ℝ) := lt_trans (by simpa using hx) (by norm_num)
    obtain ⟨y, hy, he⟩ := completion_apply_mem_compact_image T hc 2 x hx'
    exact ⟨y, hy, he.symm⟩
  · intro x
    obtain ⟨y, _, he⟩ := completion_apply_mem_compact_image T hc (‖x‖ + 1) x (by linarith)
    exact ⟨y, he⟩

/-- Nonzero eigenvectors of the extension already belong to the original space. -/
lemma eigenvector_in_original (T : E →L[𝕜] E)
    (hrange : ∀ x : UniformSpace.Completion E,
      ∃ y : E, T.completion x = (y : UniformSpace.Completion E))
    (a : 𝕜) (ha : a ≠ 0) (z : UniformSpace.Completion E)
    (hz : T.completion z = a • z) : ∃ y : E, (y : UniformSpace.Completion E) = z := by
  obtain ⟨y, hy⟩ := hrange z
  refine ⟨a⁻¹ • y, ?_⟩
  rw [UniformSpace.Completion.coe_smul, ← hy, hz, inv_smul_smul₀ ha]

/-- Finiteness above every threshold gives decay along every enumeration
without repetitions, so the statement does not depend on an ordering. -/
lemma eigenvalues_tendsto_zero {ι : Type*} (a : ι → ℝ)
    (hf : ∀ ε : ℝ, 0 < ε → {j | ε ≤ |a j|}.Finite)
    (b : ℕ → ι) (hb : Function.Injective b) :
    Filter.Tendsto (fun n => a (b n)) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hp : {n : ℕ | ε ≤ |a (b n)|}.Finite :=
    (hf ε hε).preimage (f := b) hb.injOn
  obtain ⟨N, hN⟩ := hp.bddAbove
  refine ⟨N+1, fun n hn => ?_⟩
  have hsmall : |a (b n)| < ε := lt_of_not_ge (fun hc => by
    have hnN : n ≤ N := hN hc
    omega)
  simpa [Real.dist_eq] using hsmall

/-- Pulling the Hilbert expansion back through the isometric embedding proves
convergence in E, without imposing completeness on E or on its kernel. -/
theorem spectral_expansion : Spec.SpectralExpansion.{u,v} := by
  intro 𝕜 E _ _ _ T hT hcompact
  let i : E →ₗᵢ[𝕜] UniformSpace.Completion E := UniformSpace.Completion.toComplₗᵢ
  let S := T.completion
  obtain ⟨hsym, hcS, hrange⟩ := completion_extension 𝕜 E T hT hcompact
  obtain ⟨ι, hι, f, a, hf, heig, _, _, hs, hfin, htail⟩ :=
    ExpandedFA.CompactSpectral.CompactNormalClassification.selfAdjoint_expansion
      𝕜 (UniformSpace.Completion E) S hsym.isSelfAdjoint hcS
  have hpre (j : ι) : ∃ y : E, i y = f j :=
    eigenvector_in_original T hrange (a j : 𝕜)
      (by exact_mod_cast (heig j).1) (f j) (heig j).2
  choose e he using hpre
  have heorth : Orthonormal 𝕜 e := (i.orthonormal_comp_iff).mp (by
    simpa only [Function.comp_def, he] using hf)
  have heigE (j : ι) : T (e j) = (a j : 𝕜) • e j := by
    apply i.injective
    change (T (e j) : UniformSpace.Completion E) = _
    rw [← T.completion_apply_coe, show (e j : UniformSpace.Completion E) = f j from he j,
      (heig j).2, ← he j, map_smul]
  refine ⟨ι, hι, e, a, heorth, (fun j => ⟨(heig j).1, heigE j⟩), ?_, ?_, htail,
    eigenvalues_tendsto_zero a htail, ?_⟩
  · intro x
    apply (hasSum_iff_hasSum_compl _ _).mp
    have hh := (hs (i x)).2
    convert hh using 1
    · ext j
      change i (((a j : 𝕜) * inner 𝕜 (e j) x) • e j) = _
      rw [map_smul, ← he j, i.inner_map_map]
    · exact (T.completion_apply_coe x).symm
  · intro μ hμ
    let := hfin μ hμ
    let F : Module.End.eigenspace T.toLinearMap μ →ₗ[𝕜]
        Module.End.eigenspace S.toLinearMap μ :=
      { toFun := fun x => ⟨i x, by
          rw [Module.End.mem_eigenspace_iff]
          change T.completion (x.val : UniformSpace.Completion E) = μ • (x.val : UniformSpace.Completion E)
          rw [T.completion_apply_coe]
          change i (T x) = μ • i x
          have hx : T (x : E) = μ • (x : E) := Module.End.mem_eigenspace_iff.mp x.property
          rw [hx, map_smul]⟩
        map_add' := fun x y => Subtype.ext (i.map_add x y)
        map_smul' := fun c x => Subtype.ext (i.map_smul c x) }
    exact FiniteDimensional.of_injective F (fun x y h =>
      Subtype.ext (i.injective (congrArg Subtype.val h)))
  · intro hzero
    refine ⟨fun j => ?_⟩
    have hz := heigE j
    rw [hzero, zero_apply] at hz
    have he0 : e j = 0 := (smul_eq_zero.mp hz.symm).resolve_left
      (by exact_mod_cast (heig j).1)
    have hn := heorth.norm_eq_one j
    rw [he0, norm_zero] at hn
    exact zero_ne_one hn

namespace Complexification
open Spec.Complexification
variable (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma norm_sq (p : Space E) : ‖p‖ ^ 2 = ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change inner ℝ p.1 p.1 + inner ℝ p.2 p.2 = _
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
lemma norm_fst_le (p : Space E) : ‖p.1‖ ≤ ‖p‖ := by
  have := norm_sq E p
  nlinarith [norm_nonneg p, norm_nonneg p.1, sq_nonneg ‖p.2‖]
lemma norm_snd_le (p : Space E) : ‖p.2‖ ≤ ‖p‖ := by
  have := norm_sq E p
  nlinarith [norm_nonneg p, norm_nonneg p.2, sq_nonneg ‖p.1‖]
lemma norm_le_add (p : Space E) : ‖p‖ ≤ ‖p.1‖ + ‖p.2‖ := by
  have := norm_sq E p
  nlinarith [norm_nonneg p, norm_nonneg p.1, norm_nonneg p.2]
def toPair : Space E ≃ₗ[ℝ] E × E := LinearEquiv.refl ℝ (E × E)
def pairEquiv : Space E ≃L[ℝ] E × E :=
  (toPair E).toContinuousLinearEquivOfBounds 1 2
    (fun p => by
      rw [one_mul]
      exact max_le (norm_fst_le E p) (norm_snd_le E p))
    (fun p => by
      have hn := norm_le_add E p
      exact hn.trans (by
        change ‖p.1‖ + ‖p.2‖ ≤ 2 * max ‖p.1‖ ‖p.2‖
        linarith [le_max_left ‖p.1‖ ‖p.2‖, le_max_right ‖p.1‖ ‖p.2‖]))
instance [CompleteSpace E] : CompleteSpace (Space E) :=
  (pairEquiv E).isUniformEmbedding.isUniformInducing.completeSpace_congr
    (pairEquiv E).surjective |>.mpr inferInstance

def opLinear (T : E →L[ℝ] E) : Space E →ₗ[ℂ] Space E where
  toFun p := complexPair E (T p.1) (T p.2)
  map_add' p q := by
    change (T (p.1 + q.1), T (p.2 + q.2)) = _
    simp only [map_add]; rfl
  map_smul' a p := by
    change complexPair E (T (a • p).1) (T (a • p).2) = a • complexPair E (T p.1) (T p.2)
    rw [csmul, csmul]
    change complexPair E (T (a.re • p.1 - a.im • p.2)) (T (a.im • p.1 + a.re • p.2)) = _
    simp only [map_sub, map_smul, map_add, complexPair]
    rfl
def op (T : E →L[ℝ] E) : Space E →L[ℂ] Space E :=
  (opLinear E T).mkContinuous (2 * ‖T‖) (fun p => by
      have h := norm_le_add E (complexPair E (T p.1) (T p.2))
      change ‖(complexPair E (T p.1) (T p.2))‖ ≤ _
      calc ‖(complexPair E (T p.1) (T p.2))‖ ≤ ‖T p.1‖ + ‖T p.2‖ := h
           _ ≤ ‖T‖ * ‖p‖ + ‖T‖ * ‖p‖ := add_le_add
             ((T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_fst_le E p) (norm_nonneg T)))
             ((T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_snd_le E p) (norm_nonneg T)))
           _ = (2 * ‖T‖) * ‖p‖ := by ring)
lemma op_symmetric (T : E →L[ℝ] E) (hT : T.IsSymmetric) : (op E T).IsSymmetric := by
  intro p q
  change ip E (T p.1, T p.2) q = ip E p (T q.1, T q.2)
  have ht (x y : E) : inner ℝ (T x) y = inner ℝ x (T y) := hT x y
  apply Complex.ext <;> simp only [ip, ht]
def realEmbedding : E →ₗᵢ[ℝ] Space E where
  toFun x := complexPair E x 0
  map_add' x y := by change (x + y, (0:E)) = (x + y, 0 + 0); simp
  map_smul' a x := by change (a • x, (0:E)) = (a • x, a • 0); simp
  norm_map' x := by
    change ‖complexPair E x 0‖ = ‖x‖
    have h := norm_sq E (complexPair E x 0)
    change ‖complexPair E x 0‖ ^ 2 = ‖x‖ ^ 2 + ‖(0:E)‖ ^ 2 at h
    rw [norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0), add_zero] at h
    nlinarith [norm_nonneg (complexPair E x 0), norm_nonneg x]
lemma op_compact (T : E →L[ℝ] E) (hc : IsCompactOperator T) :
    IsCompactOperator (op E T) := by
  obtain ⟨K, hK, hTK⟩ := hc.image_closedBall_subset_compact (f := T.toLinearMap) 1
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    (op E T).toLinearMap (by norm_num : (0:ℝ) < 1)).mpr
  refine ⟨(pairEquiv E).symm '' (K ×ˢ K), (hK.prod hK).image (pairEquiv E).symm.continuous, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have hp' : ‖p‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hp
  refine ⟨(T p.1, T p.2), ⟨?_, ?_⟩, rfl⟩
  · exact hTK ⟨p.1, by simpa only [Metric.mem_closedBall, dist_zero_right] using (norm_fst_le E p).trans hp', rfl⟩
  · exact hTK ⟨p.2, by simpa only [Metric.mem_closedBall, dist_zero_right] using (norm_snd_le E p).trans hp', rfl⟩
lemma op_eigen_iff (T : E →L[ℝ] E) (r : ℝ) (p : Space E) :
    op E T p = (r : ℂ) • p ↔ T p.1 = r • p.1 ∧ T p.2 = r • p.2 := by
  change complexPair E (T p.1) (T p.2) = (r : ℂ) • p ↔ _
  rw [csmul]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero, zero_add]
  change ((T p.1, T p.2) : E × E) = (r • p.1, r • p.2) ↔ _
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext h1 h2
lemma op_eigen_real (T : E →L[ℝ] E) (hT : T.IsSymmetric)
    (a : ℂ) (p : Space E) (hp : p ≠ 0) (he : op E T p = a • p) : a.im = 0 := by
  have h := (op_symmetric E T hT).conj_eigenvalue_eq_self
    (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr he, hp⟩)
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith
end Complexification

theorem complexification_geometry : Spec.ComplexificationGeometry.{v} := by
  intro E _ _
  refine ⟨Complexification.norm_sq E, ⟨Complexification.realEmbedding E, (fun _ => rfl), ?_, ?_⟩, ?_⟩
  · intro x y
    change Spec.Complexification.ip E
      (Spec.Complexification.complexPair E x 0) (Spec.Complexification.complexPair E y 0) = _
    apply Complex.ext <;> simp [Spec.Complexification.ip, Spec.Complexification.complexPair]
  · intro p
    rw [Spec.Complexification.csmul]
    change (p.1, p.2) =
      (p.1 + (Complex.I.re • p.2 - Complex.I.im • (0:E)),
        (0:E) + (Complex.I.im • p.2 + Complex.I.re • (0:E)))
    simp
  · intro hE
    let := hE
    infer_instance

theorem real_complexification : Spec.RealComplexification.{v} := by
  intro E _ _ T hT hc
  refine ⟨Complexification.op E T, (fun _ => rfl),
    Complexification.op_symmetric E T hT, ?_,
    Complexification.op_eigen_iff E T, Complexification.op_eigen_real E T hT⟩
  apply (ExpandedFA.Compactness.compact_iff_isCompactOperator _).mpr
  exact Complexification.op_compact E T
    ((ExpandedFA.Compactness.compact_iff_isCompactOperator T.toLinearMap).mp hc)

end ExpandedFA.Hilbert.PreHilbertCompactSpectral
