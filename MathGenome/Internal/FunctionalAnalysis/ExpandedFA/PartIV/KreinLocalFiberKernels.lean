import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinLocalFiberKernels
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.L2HilbertSchmidt
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace ExpandedFA.PartIV.KreinLocalFiberKernels
open KreinSpectralKernel

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma continuous_memLp_interval (v : ℝ → H) (hv : Continuous v) (R : ℝ) :
    MemLp v 2 (intervalMeasure R) := by
  apply (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mpr
  exact (hv.norm.pow 2).integrableOn_Icc

omit [CompleteSpace H] in
/-- The local integral is genuine Bochner integration, obtained using the
L²–L² Hölder product. -/
lemma synthesis_integrable {X : Type} [MeasurableSpace X] (μ : Measure X)
    (v : X → H) (hv : MemLp v 2 μ) (f : Lp ℂ 2 μ) :
    Integrable (fun t => f t • v t) μ := by
  exact memLp_one_iff_integrable.mp ((Lp.memLp f).smul hv)

/-- The canonical synthesis operator, built from the continuous Hölder pairing.
Its value is identified with the actual integral below. -/
def synthesisOperator {X : Type} [MeasurableSpace X] (μ : Measure X)
    (v : X → H) (hv : MemLp v 2 μ) : Lp ℂ 2 μ →L[ℂ] H :=
  ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] H →L[ℂ] H).lpPairing μ 2 2).flip
    (hv.toLp v)

lemma synthesisOperator_apply {X : Type} [MeasurableSpace X] (μ : Measure X)
    (v : X → H) (hv : MemLp v 2 μ) (f : Lp ℂ 2 μ) :
    synthesisOperator μ v hv f = ∫ t, f t • v t ∂μ := by
  rw [synthesisOperator, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hv.coeFn_toLp] with t ht
  simp [ht]

/-- The adjoint has the concrete scalar coefficient representative. -/
lemma synthesisOperator_adjoint {X : Type} [MeasurableSpace X] (μ : Measure X)
    (v : X → H) (hv : MemLp v 2 μ) (w : H) :
    ContinuousLinearMap.adjoint (synthesisOperator μ v hv) w =
      (hv.inner_const (𝕜 := ℂ) w).toLp (fun t => ⟪v t, w⟫_ℂ) := by
  apply ext_inner_right ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left, synthesisOperator_apply,
    ← integral_inner (synthesis_integrable μ v hv f), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hv.inner_const (𝕜 := ℂ) w).coeFn_toLp] with t ht
  simp [ht, inner_smul_right, inner_conj_symm, mul_comm]

omit [CompleteSpace H] in
lemma integral_sq_norm {X : Type} [MeasurableSpace X] (μ : Measure X)
    (v : X → H) (hv : MemLp v 2 μ) :
    (∫ t, ‖v t‖ ^ 2 ∂μ) = ‖hv.toLp v‖ ^ 2 := by
  have h := congrArg (RCLike.re : ℂ → ℝ) (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (hv.toLp v))
  rw [L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := ℂ) (hv.toLp v) (hv.toLp v))] at h
  simp only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [hv.coeFn_toLp] with t ht
  rw [ht]

omit [CompleteSpace H] in
/-- Separability makes every orthonormal family countable, also in the zero
space. The proof uses coefficient supports on an actual countable dense set. -/
lemma countable_orthonormal [TopologicalSpace.SeparableSpace H]
    {ι : Type} (e : ι → H) (he : Orthonormal ℂ e) : Countable ι := by
  classical
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense H
  have hcover : (⋃ d ∈ D, {i | ⟪e i, d⟫_ℂ ≠ 0}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    by_contra hi
    have hz : ∀ d ∈ D, ⟪e i, d⟫_ℂ = 0 := by
      intro d hd
      by_contra h
      exact hi (Set.mem_iUnion.mpr ⟨d, Set.mem_iUnion.mpr ⟨hd, h⟩⟩)
    have hfun : (fun x : H => ⟪e i, x⟫_ℂ) = fun _ => 0 :=
      Continuous.ext_on hdense (continuous_const.inner continuous_id) continuous_const hz
    have hei : e i = 0 := inner_self_eq_zero.mp (congrFun hfun (e i))
    have hnorm := he.norm_eq_one i
    simp [hei] at hnorm
  have hc : (⋃ d ∈ D, {i | ⟪e i, d⟫_ℂ ≠ 0}).Countable :=
    hD.biUnion fun d _ => ExpandedFA.Hilbert.OrthonormalExpansion.countable_coefficient_support
      ℂ H ι e he d
  rw [hcover] at hc
  exact Set.countable_univ_iff.mp hc

omit [CompleteSpace H] in
lemma lintegral_sq_norm {X : Type} [MeasurableSpace X] (μ : Measure X)
    (v : X → H) (hv : MemLp v 2 μ) :
    (∫⁻ t, ENNReal.ofReal (‖v t‖ ^ 2) ∂μ) =
      ENNReal.ofReal (‖hv.toLp v‖ ^ 2) := by
  rw [← integral_sq_norm μ v hv]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv)
    (ae_of_all _ fun t => sq_nonneg _)).symm

set_option maxHeartbeats 1000000 in
/-- Parseval in the target followed by Tonelli gives the exact square, with
no positivity-of-radius or nonzero-space assumption. -/
lemma synthesisOperator_square [TopologicalSpace.SeparableSpace H]
    {X : Type} [MeasurableSpace X] (μ : Measure X)
    (v : X → H) (hv : MemLp v 2 μ) :
    TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue
      (synthesisOperator μ v hv) = ENNReal.ofReal (∫ t, ‖v t‖ ^ 2 ∂μ) := by
  classical
  let J := synthesisOperator μ v hv
  obtain ⟨E, hE⟩ := Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset
    ℂ (Lp ℂ 2 μ)
  obtain ⟨D, hD⟩ := Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset ℂ H
  let : Countable D := countable_orthonormal (Subtype.val : D → H) hD.1
  rw [TraceIdeals.HilbertSchmidtDefinitions.squareSum_in_basis J _ hE,
    TraceIdeals.HilbertSchmidtDefinitions.adjoint_basis_identity J _ _ hE hD]
  change (∑' d : D, ENNReal.ofReal (‖ContinuousLinearMap.adjoint J d.val‖ ^ 2)) = _
  have hj (d : D) : ENNReal.ofReal (‖ContinuousLinearMap.adjoint J d.val‖ ^ 2) =
      ∫⁻ t : X, ENNReal.ofReal (‖⟪v t, d.val⟫_ℂ‖ ^ 2) ∂μ := by
    rw [show J = synthesisOperator μ v hv from rfl, synthesisOperator_adjoint]
    exact (lintegral_sq_norm (H := ℂ) μ _ (hv.inner_const (𝕜 := ℂ) d.val)).symm
  have hton := lintegral_tsum (μ := μ)
    (f := fun (d : D) (t : X) => ENNReal.ofReal (‖⟪v t, d.val⟫_ℂ‖ ^ 2))
    (fun d => ((hv.inner_const (𝕜 := ℂ) d.val).aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal)
  calc
    _ = ∑' d : D, ∫⁻ t : X, ENNReal.ofReal (‖⟪v t, d.val⟫_ℂ‖ ^ 2) ∂μ :=
      tsum_congr hj
    _ = ∫⁻ t : X, ∑' d : D, ENNReal.ofReal (‖⟪v t, d.val⟫_ℂ‖ ^ 2) ∂μ := hton.symm
    _ = ∫⁻ t : X, ENNReal.ofReal (‖v t‖ ^ 2) ∂μ := by
      apply lintegral_congr
      intro t
      simp_rw [norm_inner_symm (𝕜 := ℂ) (v t)]
      exact (TraceIdeals.HilbertSchmidtDefinitions.parseval_ennreal _ hD (v t)).symm
    _ = _ := (lintegral_sq_norm μ v hv).trans
      (congrArg ENNReal.ofReal (integral_sq_norm μ v hv).symm)

theorem local_synthesis_energy : Spec.LocalSynthesisEnergy := by
  intro H _ _ _ _ v hv R
  have hmem := continuous_memLp_interval v hv R
  exact ⟨synthesisOperator (intervalMeasure R) v hmem,
    synthesisOperator_apply _ v hmem, synthesisOperator_square _ v hmem⟩

set_option maxHeartbeats 1000000 in
/-- Reconstruct the product-L² kernel from all matrix coefficients in the
product basis. No compactness, nonzero-measure or countability is assumed. -/
theorem reverse_scalar_kernel : Spec.ReverseScalarKernel := by
  intro μ ν _ _ T hT
  classical
  obtain ⟨E, hE⟩ := Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset ℂ (Lp ℂ 2 ν)
  obtain ⟨D, hD⟩ := Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset ℂ (Lp ℂ 2 μ)
  let e : E → Lp ℂ 2 ν := Subtype.val
  let d : D → Lp ℂ 2 μ := Subtype.val
  have hprod := PartV.L2HilbertSchmidt.product_basis μ ν e d hE hD
  let b : HilbertBasis (E × D) ℂ (Lp ℂ 2 (μ.prod ν)) :=
    HilbertBasis.mk hprod.1
      ((Hilbert.OrthonormalExpansion.maximal_iff_total ℂ _ _ _ hprod.1).mp hprod).ge
  have hb : ⇑b = fun p : E × D => PartV.L2HilbertSchmidt.productVector μ ν (d p.2) (e p.1) :=
    HilbertBasis.coe_mk _ _
  have hmatrix : (∑' p : E × D, ENNReal.ofReal (‖⟪d p.2, T (e p.1)⟫_ℂ‖ ^ 2)) < ∞ := by
    rw [ENNReal.tsum_prod (f := fun (i : E) (j : D) => ENNReal.ofReal (‖⟪d j, T (e i)⟫_ℂ‖ ^ 2))]
    change TraceIdeals.HilbertSchmidtDefinitions.Spec.MatrixSquareSumValue T e d < ∞
    have heq := (TraceIdeals.HilbertSchmidtDefinitions.squareSum_in_basis T e hE).trans
      (TraceIdeals.HilbertSchmidtDefinitions.matrix_identity T e d hD)
    change TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue T < ∞ at hT
    exact heq ▸ hT
  have hs : Summable (fun p : E × D => ‖⟪d p.2, T (e p.1)⟫_ℂ‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hmatrix.ne
  have hc : Memℓp (fun p : E × D => ⟪d p.2, T (e p.1)⟫_ℂ) 2 := by
    apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    simpa using hs
  let c : lp (fun _ : E × D => ℂ) 2 := ⟨_, hc⟩
  let k : Lp ℂ 2 (μ.prod ν) := b.repr.symm c
  have hcoeff (p : E × D) :
      ⟪PartV.L2HilbertSchmidt.productVector μ ν (d p.2) (e p.1), k⟫_ℂ =
        ⟪d p.2, T (e p.1)⟫_ℂ := by
    rw [← congrFun hb p, ← b.repr_apply_apply]
    change b.repr (b.repr.symm c) p = _
    rw [b.repr.apply_symm_apply]
  have hTe (i : E) : PartV.L2Kernel.kernelOperator μ ν k (e i) = T (e i) := by
    apply sub_eq_zero.mp
    apply PartV.L2HilbertSchmidt.eq_zero_of_basis_coefficients d hD
    intro j
    rw [inner_sub_right, ← PartV.L2HilbertSchmidt.productVector_coefficient]
    exact sub_eq_zero.mpr (hcoeff (i, j))
  have hk : PartV.L2Kernel.kernelOperator μ ν k = T := by
    ext1 u
    have hu := (Hilbert.OrthonormalExpansion.expansion ℂ _ E e hE u).1
    have ht := (PartV.L2Kernel.kernelOperator μ ν k).hasSum hu
    have ht' := T.hasSum hu
    simp only [map_smul, hTe] at ht
    simp only [map_smul] at ht'
    exact ht.unique ht'
  refine ⟨k, hk, ?_⟩
  intro k' hk'
  change PartV.L2Kernel.kernelOperator μ ν k' = T at hk'
  apply sub_eq_zero.mp
  apply PartV.L2HilbertSchmidt.eq_zero_of_basis_coefficients _ hprod
  intro p
  rw [inner_sub_right, PartV.L2HilbertSchmidt.productVector_coefficient,
    PartV.L2HilbertSchmidt.productVector_coefficient]
  change ⟪d p.2, PartV.L2Kernel.kernelOperator μ ν k' (e p.1)⟫_ℂ -
    ⟪d p.2, PartV.L2Kernel.kernelOperator μ ν k (e p.1)⟫_ℂ = 0
  rw [hk', hk, sub_self]



/-- Vector-valued Fubini sections, without a fiber condition. -/
lemma vector_sections (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν]
    (h : ℝ → ℝ → FiberSpace) (hh : MemLp (Function.uncurry h) 2 (μ.prod ν)) :
    ∀ᵐ ξ ∂μ, MemLp (h ξ) 2 ν := by
  have hi := (memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable).mp hh
  filter_upwards [hh.aestronglyMeasurable.prodMk_left, hi.prod_right_ae] with ξ hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hi

/-- The actual coordinate functional on the canonical ℓ². -/
def fiberCoordinate (n : ℕ) : FiberSpace →L[ℂ] ℂ :=
  lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n

lemma integral_coordinate (ν : Measure ℝ) (n : ℕ) (f : Lp ℂ 2 ν)
    (h : ℝ → FiberSpace) (hh : MemLp h 2 ν) :
    (∫ t, f t • h t ∂ν) n = ∫ t, h t n * f t ∂ν := by
  have hi : Integrable (fun t => f t • h t) ν :=
    memLp_one_iff_integrable.mp ((Lp.memLp f).smul hh)
  have he := (fiberCoordinate n).integral_comp_comm hi
  change (∫ t, f t * h t n ∂ν) = (∫ t, f t • h t ∂ν) n at he
  simpa only [mul_comm] using he.symm

/-- Scalar integral kernels are injective on arbitrary σ-finite factors. -/
lemma scalar_kernel_ext (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν]
    (h k : ℝ × ℝ → ℂ) (hh : MemLp h 2 (μ.prod ν)) (hk : MemLp k 2 (μ.prod ν))
    (heq : ∀ f : Lp ℂ 2 ν,
      (fun ξ => ∫ t, h (ξ,t) * f t ∂ν) =ᵐ[μ]
        fun ξ => ∫ t, k (ξ,t) * f t ∂ν) : h =ᵐ[μ.prod ν] k := by
  have hop : PartV.L2Kernel.kernelOperator μ ν (hh.toLp h) =
      PartV.L2Kernel.kernelOperator μ ν (hk.toLp k) := by
    ext1 f
    apply Lp.ext
    have h₁ := PartV.L2Kernel.kernel_representative_formula μ ν h f hh (Lp.memLp f)
    have h₂ := PartV.L2Kernel.kernel_representative_formula μ ν k f hk (Lp.memLp f)
    simp only [Lp.toLp_coeFn] at h₁ h₂
    exact h₁.trans ((heq f).trans h₂.symm)
  have hz : PartV.L2Kernel.kernelOperator μ ν ((hh.toLp h) - (hk.toLp k)) = 0 := by
    change PartV.L2KernelCompact.kernelAssignment μ ν ((hh.toLp h) - (hk.toLp k)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hop
  have hclass := sub_eq_zero.mp (PartV.L2HilbertSchmidt.kernel_eq_zero μ ν _ hz)
  exact hh.coeFn_toLp.symm.trans ((show hh.toLp h =ᵐ[μ.prod ν] hk.toLp k by
    rw [hclass]).trans hk.coeFn_toLp)

/-- Equality on every scalar L² input determines a vector kernel, with no
active-coordinate or positivity assumption. -/
theorem kernel_unique : Spec.KernelUniqueness := by
  intro μ ν _ _ h k hh hk heq
  have hcoord (n : ℕ) :
      (fun p : ℝ × ℝ => h p.1 p.2 n) =ᵐ[μ.prod ν] fun p => k p.1 p.2 n := by
    apply scalar_kernel_ext μ ν
      _ _ ((fiberCoordinate n).comp_memLp' hh) ((fiberCoordinate n).comp_memLp' hk)
    intro f
    filter_upwards [heq f, vector_sections μ ν h hh, vector_sections μ ν k hk]
      with ξ hξ hrow krow
    change (∫ t, h ξ t n * f t ∂ν) = ∫ t, k ξ t n * f t ∂ν
    rw [← integral_coordinate ν n f (h ξ) hrow,
      ← integral_coordinate ν n f (k ξ) krow, hξ]
  filter_upwards [ae_all_iff.mpr hcoord] with p hp
  exact lp.ext (funext hp)

namespace CoordinatePacking
variable {X : Type} [MeasurableSpace X] (μ : Measure X)

/-- Taking a canonical fiber coordinate as a map of L² spaces. -/
def coord (n : ℕ) : Lp FiberSpace 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (fiberCoordinate n).compLpL 2 μ

lemma coord_ae (n : ℕ) (f : Lp FiberSpace 2 μ) :
    coord μ n f =ᵐ[μ] fun x => f x n := (fiberCoordinate n).coeFn_compLp f

private def insertMap (n : ℕ) : Lp ℂ 2 μ →L[ℂ] Lp FiberSpace 2 μ :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 n).compLpL 2 μ

private lemma insertMap_ae (n : ℕ) (f : Lp ℂ 2 μ) :
    insertMap μ n f =ᵐ[μ] fun x => lp.single 2 n (f x) :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 n).coeFn_compLp f

/-- Insert scalar L² into one coordinate; the norm is checked by its
integral, before the orthogonal summation is formed. -/
private def insert (n : ℕ) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp FiberSpace 2 μ where
  toLinearMap := (insertMap μ n).toLinearMap
  norm_map' f := by
    change ‖insertMap μ n f‖ = ‖f‖
    have hnorm : ‖insertMap μ n f‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [← show (∫ x, ‖insertMap μ n f x‖ ^ 2 ∂μ) = ‖insertMap μ n f‖ ^ 2 from by
        simpa only [Lp.toLp_coeFn] using integral_sq_norm μ _ (Lp.memLp (insertMap μ n f)),
        ← show (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖f‖ ^ 2 from by
          simpa only [Lp.toLp_coeFn] using integral_sq_norm μ f (Lp.memLp f)]
      apply integral_congr_ae
      filter_upwards [insertMap_ae μ n f] with x hx
      simp only [hx, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    nlinarith [norm_nonneg (insertMap μ n f), norm_nonneg f]

private lemma coord_insert (i j : ℕ) (f : Lp ℂ 2 μ) :
    coord μ i (insert μ j f) = if i = j then f else 0 := by
  classical
  by_cases he : i = j
  · subst i
    simp only [ite_true]
    apply Lp.ext
    filter_upwards [coord_ae μ j (insert μ j f), insertMap_ae μ j f] with x hc hi
    rw [hc]
    change insertMap μ j f x j = f x
    rw [hi]
    simp
  · rw [ite_eq_right he]
    apply Lp.ext
    filter_upwards [coord_ae μ i (insert μ j f), insertMap_ae μ j f,
      Lp.coeFn_zero ℂ 2 μ] with x hc hi hz
    rw [hc]
    change insertMap μ j f x i = (0 : Lp ℂ 2 μ) x
    rw [hi, hz]
    simp [lp.single_apply, he]

private lemma insert_orthogonal :
    OrthogonalFamily ℂ (fun _ : ℕ => Lp ℂ 2 μ) (insert μ) := by
  intro i j hij f g
  rw [L2.inner_def]
  calc
    _ = ∫ x, ⟪(lp.single 2 i (f x) : FiberSpace), (lp.single 2 j (g x) : FiberSpace)⟫_ℂ ∂μ := by
      apply integral_congr_ae
      filter_upwards [insertMap_ae μ i f, insertMap_ae μ j g] with x hf hg
      change ⟪insertMap μ i f x, insertMap μ j g x⟫_ℂ = _
      rw [hf, hg]
    _ = 0 := by simp [lp.inner_single_left, lp.single_apply, Ne.symm hij]

/-- Only the orthogonal summation is needed; there is no asserted inverse
Fubini map or assumed surjectivity of a vector-kernel construction. -/
def pack : lp (fun _ : ℕ => Lp ℂ 2 μ) 2 →ₗᵢ[ℂ] Lp FiberSpace 2 μ :=
  (insert_orthogonal μ).linearIsometry

lemma coord_pack (n : ℕ) (c : lp (fun _ : ℕ => Lp ℂ 2 μ) 2) :
    coord μ n (pack μ c) = c n := by
  classical
  have h := (coord μ n).hasSum ((insert_orthogonal μ).hasSum_linearIsometry c)
  simp only [coord_insert] at h
  apply h.unique
  convert hasSum_ite_eq n (c n) using 1
  ext j
  by_cases hj : j = n
  · subst j; simp
  · simp [hj, Ne.symm hj]

/-- Parseval in the fixed coordinate fiber, then Tonelli. -/
lemma enorm_square (f : Lp FiberSpace 2 μ) :
    ENNReal.ofReal (‖f‖ ^ 2) =
      ∑' n : ℕ, ENNReal.ofReal (‖coord μ n f‖ ^ 2) := by
  have hpoint (x : X) : ENNReal.ofReal (‖f x‖ ^ 2) =
      ∑' n : ℕ, ENNReal.ofReal (‖f x n‖ ^ 2) := by
    have hn := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (f x)
    have hs := (lp.memℓp (f x)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn hs
    rw [hn, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs]
  have hc (n : ℕ) : AEStronglyMeasurable (fun x => f x n) μ :=
    (fiberCoordinate n).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)
  have hcoord (n : ℕ) : (∫⁻ x, ENNReal.ofReal (‖f x n‖ ^ 2) ∂μ) =
      ENNReal.ofReal (‖coord μ n f‖ ^ 2) := by
    have hnorm := lintegral_sq_norm μ (coord μ n f) (Lp.memLp (coord μ n f))
    simp only [Lp.toLp_coeFn] at hnorm
    rw [← hnorm]
    exact lintegral_congr_ae ((coord_ae μ n f).fun_comp
      (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2))).symm
  calc
    _ = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
      simpa only [Lp.toLp_coeFn] using (lintegral_sq_norm μ f (Lp.memLp f)).symm
    _ = ∫⁻ x, ∑' n : ℕ, ENNReal.ofReal (‖f x n‖ ^ 2) ∂μ := lintegral_congr hpoint
    _ = ∑' n : ℕ, ∫⁻ x, ENNReal.ofReal (‖f x n‖ ^ 2) ∂μ :=
      lintegral_tsum fun n => ((hc n).norm.pow 2).aemeasurable.ennreal_ofReal
    _ = _ := tsum_congr hcoord
end CoordinatePacking


open TraceIdeals.HilbertSchmidtDefinitions

/-- Coordinate energies sum to the full Hilbert–Schmidt energy. -/
lemma coordinate_square_sum (μ ν : Measure ℝ)
    (T : Lp ℂ 2 ν →L[ℂ] Lp FiberSpace 2 μ) :
    (∑' n : ℕ, TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue ((CoordinatePacking.coord μ n).comp T)) =
      TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue T := by
  classical
  obtain ⟨E, hE⟩ := Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset ℂ (Lp ℂ 2 ν)
  simp_rw [squareSum_in_basis _ (Subtype.val : E → Lp ℂ 2 ν) hE]
  change (∑' n : ℕ, ∑' e : E, ENNReal.ofReal (‖CoordinatePacking.coord μ n (T e.val)‖ ^ 2)) =
    ∑' e : E, ENNReal.ofReal (‖T e.val‖ ^ 2)
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun e => (CoordinatePacking.enorm_square μ (T e.val)).symm

/-- Composition with the given isometry preserves the actual HS energy. -/
lemma isometry_comp_square (μ ν : Measure ℝ)
    (U : H →ₗᵢ[ℂ] Lp FiberSpace 2 μ) (J : Lp ℂ 2 ν →L[ℂ] H) :
    TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue (U.toContinuousLinearMap.comp J) =
      TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue J := by
  classical
  obtain ⟨E, hE⟩ := Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset ℂ (Lp ℂ 2 ν)
  simp_rw [squareSum_in_basis _ (Subtype.val : E → Lp ℂ 2 ν) hE]
  change (∑' e : E, ENNReal.ofReal (‖U (J e.val)‖ ^ 2)) = _
  simp only [U.norm_map, TraceIdeals.HilbertSchmidtDefinitions.Spec.BasisSquareSumValue]

set_option maxHeartbeats 1500000 in
/-- Reconstruct an ℓ²-valued kernel by assembling its scalar coordinate
kernels in L². Tonelli is encoded by the two Hilbert sums; no reverse
representation is an input hypothesis. -/
lemma reverse_vector_kernel (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν]
    (T : Lp ℂ 2 ν →L[ℂ] Lp FiberSpace 2 μ)
    (hT : TraceIdeals.HilbertSchmidtDefinitions.Spec.IsHilbertSchmidtValue T) :
    ∃ h : Lp FiberSpace 2 (μ.prod ν),
      (∀ f : Lp ℂ 2 ν, (T f : ℝ → FiberSpace) =ᵐ[μ]
        fun ξ => ∫ t, f t • h (ξ,t) ∂ν) ∧
      ENNReal.ofReal (‖h‖ ^ 2) =
        TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue T := by
  classical
  let Tn (n : ℕ) := (CoordinatePacking.coord μ n).comp T
  have hsum : (∑' n : ℕ,
      TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue (Tn n)) =
      TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue T :=
    coordinate_square_sum μ ν T
  have hn (n : ℕ) : TraceIdeals.HilbertSchmidtDefinitions.Spec.IsHilbertSchmidtValue (Tn n) := by
    apply lt_of_le_of_lt (ENNReal.le_tsum n)
    rw [hsum]
    exact hT
  choose k hk using fun n => (reverse_scalar_kernel μ ν (Tn n) (hn n)).exists
  have hkn (n : ℕ) : ENNReal.ofReal (‖k n‖ ^ 2) =
      TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue (Tn n) := by
    rw [← hk n]
    exact (PartV.L2HilbertSchmidt.kernel_square_norm μ ν (k n)).symm
  have hfinite : (∑' n : ℕ, ENNReal.ofReal (‖k n‖ ^ 2)) < ∞ := by
    simp_rw [hkn]
    rw [hsum]
    exact hT
  have hs : Summable (fun n : ℕ => ‖k n‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hfinite.ne
  have hc : Memℓp k 2 := by
    apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    simpa using hs
  let c : lp (fun _ : ℕ => Lp ℂ 2 (μ.prod ν)) 2 := ⟨k, hc⟩
  let h : Lp FiberSpace 2 (μ.prod ν) := CoordinatePacking.pack (μ.prod ν) c
  have hcoords (n : ℕ) :
      (k n : ℝ × ℝ → ℂ) =ᵐ[μ.prod ν] fun q => h q n := by
    have h' := CoordinatePacking.coord_ae (μ.prod ν) n h
    have he : CoordinatePacking.coord (μ.prod ν) n h = k n :=
      CoordinatePacking.coord_pack (μ.prod ν) n c
    rw [he] at h'
    exact h'
  refine ⟨h, ?_, ?_⟩
  · intro f
    have hout (n : ℕ) : ∀ᵐ ξ ∂μ,
        T f ξ n = (∫ t, f t • h (ξ,t) ∂ν) n := by
      have hf := PartV.L2KernelCompact.kernelOperator_coe μ ν (k n) f
      change (PartV.L2KernelSpec.OperatorValue μ ν (k n) f : ℝ → ℂ) =ᵐ[μ] _ at hf
      rw [hk n] at hf
      filter_upwards [hf, CoordinatePacking.coord_ae μ n (T f),
        Measure.ae_ae_of_ae_prod (hcoords n),
        vector_sections μ ν (fun ξ t => h (ξ,t)) (Lp.memLp h)] with ξ hf he hc hr
      change CoordinatePacking.coord μ n (T f) ξ = _ at hf
      rw [he] at hf
      rw [integral_coordinate ν n f (fun t => h (ξ,t)) hr]
      apply hf.trans
      apply integral_congr_ae
      filter_upwards [hc] with t ht
      rw [ht]
    filter_upwards [ae_all_iff.mpr hout] with ξ hξ
    exact lp.ext (funext hξ)
  · calc
      ENNReal.ofReal (‖h‖ ^ 2) =
          ∑' n : ℕ, ENNReal.ofReal (‖CoordinatePacking.coord (μ.prod ν) n h‖ ^ 2) :=
        CoordinatePacking.enorm_square (μ.prod ν) h
      _ = ∑' n : ℕ, ENNReal.ofReal (‖k n‖ ^ 2) := by
        congr 1
        funext n
        rw [show CoordinatePacking.coord (μ.prod ν) n h = k n from
          CoordinatePacking.coord_pack (μ.prod ν) n c]
      _ = _ := (tsum_congr hkn).trans hsum

/-- Inactive coordinate kernels vanish by scalar kernel injectivity. The
range condition holds separately for each input; uniqueness supplies the
common product null set. -/
lemma kernel_active_fibers (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν]
    (m : ℝ → ℕ∞) (hm : Measurable m)
    (T : Lp ℂ 2 ν →L[ℂ] Lp FiberSpace 2 μ)
    (hT : ∀ f : Lp ℂ 2 ν, ∀ᵐ ξ ∂μ, T f ξ ∈ coordinateFiber (m ξ))
    (h : ℝ → ℝ → FiberSpace) (hh : MemLp (Function.uncurry h) 2 (μ.prod ν))
    (hrep : ∀ f : Lp ℂ 2 ν, (T f : ℝ → FiberSpace) =ᵐ[μ]
      fun ξ => ∫ t, f t • h ξ t ∂ν) :
    ∀ᵐ ξ ∂μ, ∀ᵐ t ∂ν, h ξ t ∈ coordinateFiber (m ξ) := by
  classical
  have hcoords (n : ℕ) : ∀ᵐ q : ℝ × ℝ ∂μ.prod ν,
      ¬ (n : ℕ∞) < m q.1 → h q.1 q.2 n = 0 := by
    let A : Set (ℝ × ℝ) := {q | m q.1 ≤ (n : ℕ∞)}
    have hA : MeasurableSet A := (Set.to_countable {d : ℕ∞ | d ≤ (n : ℕ∞)}).measurableSet.preimage
      (hm.comp measurable_fst)
    let k : ℝ × ℝ → ℂ := A.indicator (fun q => h q.1 q.2 n)
    have hk : MemLp k 2 (μ.prod ν) :=
      ((fiberCoordinate n).comp_memLp' hh).indicator hA.nullMeasurableSet
    have he : k =ᵐ[μ.prod ν] (fun _ => (0 : ℂ)) := by
      apply scalar_kernel_ext μ ν _ _ hk MemLp.zero
      intro f
      filter_upwards [hT f, hrep f, vector_sections μ ν h hh] with ξ hactive hr hrow
      by_cases hξ : m ξ ≤ (n : ℕ∞)
      · have hind : (fun t => k (ξ,t) * f t) = fun t => h ξ t n * f t := by
          funext t
          simp [k, A, hξ]
        rw [hind, ← integral_coordinate ν n f (h ξ) hrow, ← hr]
        have hz : T f ξ n = 0 := hactive n (not_lt_of_ge hξ)
        simpa using hz
      · simp [k, A, hξ]
    filter_upwards [he] with q hq hn
    have hle : m q.1 ≤ (n : ℕ∞) := le_of_not_gt hn
    simpa [k, A, hle] using hq
  have hall : ∀ᵐ q : ℝ × ℝ ∂μ.prod ν,
      ∀ n : ℕ, ¬ (n : ℕ∞) < m q.1 → h q.1 q.2 n = 0 :=
    ae_all_iff.mpr hcoords
  exact Measure.ae_ae_of_ae_prod hall

/-- Tonelli in the same canonical product measure, including zero measures. -/
lemma vector_kernel_energy (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν]
    (h : Lp FiberSpace 2 (μ.prod ν)) :
    (∫⁻ ξ, ∫⁻ t, ‖h (ξ,t)‖ₑ ^ 2 ∂ν ∂μ) = ENNReal.ofReal (‖h‖ ^ 2) := by
  rw [← lintegral_prod (fun q : ℝ × ℝ => ‖h q‖ₑ ^ 2)
    ((Lp.aestronglyMeasurable h).enorm.pow_const 2)]
  have he (q : ℝ × ℝ) : ‖h q‖ₑ ^ 2 = ENNReal.ofReal (‖h q‖ ^ 2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simp_rw [he]
  simpa only [Lp.toLp_coeFn] using lintegral_sq_norm (μ.prod ν) h (Lp.memLp h)

/-- Local kernels for every positive real radius. The operator is constructed
from the Bochner synthesis, and its energy is preserved by U. -/
theorem local_kernel_exists : Spec.LocalKernelExistence := by
  intro H _ _ _ _ v hv μ _ m hm U hU R hR
  let : IsFiniteMeasure (intervalMeasure R) := by
    dsimp [intervalMeasure]
    infer_instance
  let J := synthesisOperator (intervalMeasure R) v (continuous_memLp_interval v hv R)
  let T := U.toContinuousLinearMap.comp J
  have hsquare : TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue T =
      ENNReal.ofReal (∫ t, ‖v t‖ ^ 2 ∂intervalMeasure R) := by
    rw [isometry_comp_square]
    exact synthesisOperator_square _ v (continuous_memLp_interval v hv R)
  have hfinite : TraceIdeals.HilbertSchmidtDefinitions.Spec.IsHilbertSchmidtValue T := by
    change TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue T < ∞
    rw [hsquare]
    exact ENNReal.ofReal_lt_top
  obtain ⟨h, hrep, he⟩ := reverse_vector_kernel μ (intervalMeasure R) T hfinite
  have hactive : ∀ f : Lp ℂ 2 (intervalMeasure R),
      ∀ᵐ ξ ∂μ, T f ξ ∈ coordinateFiber (m ξ) := fun f => hU (J f)
  refine ⟨{
    h := fun ξ t => h (ξ,t)
    measurable := (Lp.aestronglyMeasurable h)
    square := Lp.memLp h
    rows := vector_sections μ (intervalMeasure R) _ (Lp.memLp h)
    fibers := kernel_active_fibers μ (intervalMeasure R) m hm T hactive _ (Lp.memLp h) hrep
    represents := ?_
    energy := (vector_kernel_energy μ (intervalMeasure R) h).trans (he.trans hsquare) }⟩
  intro f
  have hJ := synthesisOperator_apply (intervalMeasure R) v (continuous_memLp_interval v hv R) f
  simpa only [T, J, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    hJ] using hrep f

end ExpandedFA.PartIV.KreinLocalFiberKernels
