import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.L2HilbertSchmidt
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.L2KernelCompact
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter RCLike
open scoped ENNReal InnerProductSpace ComplexConjugate Topology
universe u v a b
namespace ExpandedFA.PartV.L2HilbertSchmidt
open L2Kernel (kernelOperator)
open L2KernelCompact
open ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions

variable {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]

/-- The product vector with representative v(x) conj(u(y)). -/
def productVector (v : Lp 𝕜 2 μ) (u : Lp 𝕜 2 ν) : Lp 𝕜 2 (μ.prod ν) :=
  star ((memLp_tensor μ ν v u).choose.toLp (fun p : X × Y => conj (v p.1) * u p.2))

lemma productVector_coe (v : Lp 𝕜 2 μ) (u : Lp 𝕜 2 ν) :
    (productVector μ ν v u : X × Y → 𝕜) =ᵐ[μ.prod ν]
      fun p => v p.1 * conj (u p.2) := by
  filter_upwards [Lp.coeFn_star ((memLp_tensor μ ν v u).choose.toLp _),
    (memLp_tensor μ ν v u).choose.coeFn_toLp] with p hs ht
  rw [show productVector μ ν v u = star ((memLp_tensor μ ν v u).choose.toLp _) from rfl,
    hs, Pi.star_apply, ht]
  simp

lemma productVector_inner (v v' : Lp 𝕜 2 μ) (u u' : Lp 𝕜 2 ν) :
    ⟪productVector μ ν v u, productVector μ ν v' u'⟫_𝕜 =
      ⟪v, v'⟫_𝕜 * ⟪u', u⟫_𝕜 := by
  rw [L2.inner_def]
  calc
    _ = ∫ p : X × Y, (conj (v p.1) * v' p.1) *
        (conj (u' p.2) * u p.2) ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards [productVector_coe μ ν v u, productVector_coe μ ν v' u'] with p hp hp'
      simp only [RCLike.inner_apply', hp, hp', map_mul, conj_conj]
      ring
    _ = _ := by
      rw [integral_prod_mul (fun x => conj (v x) * v' x) (fun y => conj (u' y) * u y)]
      simp only [L2.inner_def, RCLike.inner_apply']

/-- Matrix entries of the original integral operator are product coefficients. -/
lemma productVector_coefficient (k : Lp 𝕜 2 (μ.prod ν))
    (v : Lp 𝕜 2 μ) (u : Lp 𝕜 2 ν) :
    ⟪productVector μ ν v u, k⟫_𝕜 = ⟪v, kernelOperator μ ν k u⟫_𝕜 := by
  have hprod : ⟪productVector μ ν v u, k⟫_𝕜 =
      ∫ p : X × Y, conj (v p.1) * k p * u p.2 ∂μ.prod ν := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [productVector_coe μ ν v u] with p hp
    simp only [RCLike.inner_apply', hp, map_mul, conj_conj]
    ring
  rw [hprod, integral_prod _ (l2_kernel_triple_bound μ ν k v u).1, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [kernelOperator_coe μ ν k u] with x hx
  simp only [RCLike.inner_apply', hx]
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

lemma productVector_indicator (B : Set X) (C : Set Y)
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hμB : μ B ≠ ∞) (hνC : ν C ≠ ∞) :
    productVector μ ν (indicatorConstLp 2 hB hμB (1 : 𝕜))
      (indicatorConstLp 2 hC hνC (1 : 𝕜)) =
      indicatorConstLp 2 (hB.prod hC)
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hμB hνC) (1 : 𝕜) := by
  apply Lp.ext
  filter_upwards [productVector_coe μ ν (indicatorConstLp 2 hB hμB (1 : 𝕜))
      (indicatorConstLp 2 hC hνC (1 : 𝕜)),
    (quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp
      (indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hB) (hμs := hμB) (c := (1 : 𝕜))),
    (quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp
      (indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hC) (hμs := hνC) (c := (1 : 𝕜))),
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hB.prod hC)
      (hμs := by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hμB hνC) (c := (1 : 𝕜))]
    with p hp hbp hcp hrect
  simp only [Function.comp_apply] at hbp hcp
  rw [hp, hbp, hcp, hrect]
  by_cases hb : p.1 ∈ B <;> by_cases hc : p.2 ∈ C <;> simp [hb, hc]

/-- The kernel assignment is injective on arbitrary sigma-finite factors. -/
lemma kernel_eq_zero (k : Lp 𝕜 2 (μ.prod ν))
    (hk : kernelOperator μ ν k = 0) : k = 0 := by
  apply eq_zero_of_rectangle_integrals k
  intro B C hB hC hμB hνC
  rw [← L2.inner_indicatorConstLp_one (𝕜 := 𝕜) (hB.prod hC)
    (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hμB hνC),
    ← productVector_indicator μ ν B C hB hC hμB hνC,
    productVector_coefficient, hk]
  simp

lemma product_orthonormal {ι : Type a} {κ : Type b}
    (e : ι → Lp 𝕜 2 ν) (f : κ → Lp 𝕜 2 μ)
    (he : Orthonormal 𝕜 e) (hf : Orthonormal 𝕜 f) :
    Orthonormal 𝕜 (fun p : ι × κ => productVector μ ν (f p.2) (e p.1)) := by
  classical
  rw [orthonormal_iff_ite] at he hf ⊢
  intro p q
  rw [productVector_inner, hf, he]
  by_cases h₁ : p.1 = q.1 <;> by_cases h₂ : p.2 = q.2 <;>
    simp [h₁, h₂, eq_comm, Prod.ext_iff]

omit μ ν in
lemma eq_zero_of_basis_coefficients {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] {ι : Type*} (e : ι → H)
    (he : Spec.IsBasis (𝕜 := 𝕜) e) (x : H) (hx : ∀ i, ⟪e i, x⟫_𝕜 = 0) : x = 0 := by
  have hp := (ExpandedFA.Hilbert.OrthonormalExpansion.parseval 𝕜 H ι e he x).2
  simp only [hx, norm_zero, zero_pow (by decide : 2 ≠ 0), tsum_zero] at hp
  exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero hp)

/-- Products of arbitrary bases form a basis of the ordinary product L².
Completeness follows from injectivity of the original integral operator. -/
lemma product_basis {ι : Type a} {κ : Type b}
    (e : ι → Lp 𝕜 2 ν) (f : κ → Lp 𝕜 2 μ)
    (he : Spec.IsBasis (𝕜 := 𝕜) e) (hf : Spec.IsBasis (𝕜 := 𝕜) f) :
    Spec.IsBasis (𝕜 := 𝕜) (fun p : ι × κ => productVector μ ν (f p.2) (e p.1)) := by
  apply (ExpandedFA.Hilbert.OrthonormalExpansion.maximal_iff_total 𝕜 _ _ _
    (product_orthonormal μ ν e f he.1 hf.1)).mpr
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro k hk
  apply kernel_eq_zero μ ν k
  have hke (i : ι) : kernelOperator μ ν k (e i) = 0 := by
    apply eq_zero_of_basis_coefficients f hf
    intro j
    rw [← productVector_coefficient]
    exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self (i,j))) hk
  ext1 u
  have hs := (ExpandedFA.Hilbert.OrthonormalExpansion.expansion 𝕜 _ ι e he u).1
  have ht := (kernelOperator μ ν k).hasSum hs
  simpa only [map_smul, hke, smul_zero, tsum_zero, zero_apply] using ht.tsum_eq.symm

lemma kernel_square_norm (k : Lp 𝕜 2 (μ.prod ν)) :
    hilbertSchmidtSquare (kernelOperator μ ν k) = ENNReal.ofReal (‖k‖ ^ 2) := by
  let T : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ := kernelOperator μ ν k
  change Spec.HilbertSchmidtSquareValue T = _
  obtain ⟨E, hE⟩ := ExpandedFA.Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset
    𝕜 (Lp 𝕜 2 ν)
  obtain ⟨F, hF⟩ := ExpandedFA.Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset
    𝕜 (Lp 𝕜 2 μ)
  calc
    Spec.HilbertSchmidtSquareValue T = basisSquareSum T (Subtype.val : E → _) :=
      squareSum_in_basis T _ hE
    _ = matrixSquareSum T (Subtype.val : E → _) (Subtype.val : F → _) :=
      matrix_identity T _ _ hF
    _ = ∑' p : E × F, ENNReal.ofReal (‖⟪p.2.val, T p.1.val⟫_𝕜‖ ^ 2) :=
      ENNReal.tsum_prod.symm
    _ = ∑' p : E × F,
        ENNReal.ofReal (‖⟪productVector μ ν p.2.val p.1.val, k⟫_𝕜‖ ^ 2) := by
      apply tsum_congr
      intro p
      exact congrArg (fun c : 𝕜 => ENNReal.ofReal (‖c‖ ^ 2))
        (productVector_coefficient μ ν k p.2.val p.1.val).symm
    _ = ENNReal.ofReal (‖k‖ ^ 2) :=
      (parseval_ennreal _ (product_basis μ ν (Subtype.val : E → _)
        (Subtype.val : F → _) hE hF) k).symm

omit [SigmaFinite μ] [SigmaFinite ν] in
lemma kernel_integral_square (k : Lp 𝕜 2 (μ.prod ν)) :
    (∫ p, ‖k p‖ ^ 2 ∂μ.prod ν) = ‖k‖ ^ 2 := by
  simpa only [Lp.toLp_coeFn] using L2Kernel.integral_sq_norm k (Lp.memLp k)

theorem kernel_square_identity : L2HilbertSchmidtSpec.SquareIdentity.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ k
  rw [kernel_integral_square]
  exact kernel_square_norm μ ν k

theorem kernel_hilbertSchmidt : L2HilbertSchmidtSpec.Finiteness.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ k
  change hilbertSchmidtSquare (kernelOperator μ ν k) < ∞
  rw [kernel_square_norm]
  exact ENNReal.ofReal_lt_top

theorem kernel_norm_identity : L2HilbertSchmidtSpec.NormIdentity.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ k h
  change Real.sqrt (hilbertSchmidtSquare (kernelOperator μ ν k)).toReal ^ 2 = _
  rw [Real.sq_sqrt ENNReal.toReal_nonneg, kernel_square_norm,
    ENNReal.toReal_ofReal (sq_nonneg _), kernel_integral_square]

theorem kernel_every_basis_identity : L2HilbertSchmidtSpec.EveryBasisIdentity.{u,v,a} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ k ι e he
  have hs := (finiteness_in_basis (kernelOperator μ ν k) e he).mp (kernel_hilbertSchmidt μ ν k)
  refine ⟨hs, ?_⟩
  let T : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ := kernelOperator μ ν k
  have h : Spec.HilbertSchmidtSquareValue T = ENNReal.ofReal (‖k‖ ^ 2) :=
    kernel_square_norm μ ν k
  rw [squareSum_in_basis T e he] at h
  change (∑' i, ENNReal.ofReal (‖T (e i)‖ ^ 2)) = _ at h
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hs] at h
  have heq := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal (tsum_nonneg fun i => sq_nonneg _),
    ENNReal.toReal_ofReal (sq_nonneg _)] at heq
  exact heq.trans (kernel_integral_square μ ν k).symm

end ExpandedFA.PartV.L2HilbertSchmidt
