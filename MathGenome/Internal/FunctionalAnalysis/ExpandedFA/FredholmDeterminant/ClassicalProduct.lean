import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.ClassicalProduct
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.ClassicalEntireSeries
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Approximation.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Data.Fintype.CardEmbedding

open MeasureTheory Filter
open scoped Topology
universe u
namespace ExpandedFA.FredholmDeterminant.ClassicalProduct
open ClassicalDefinitions.Spec ClassicalEntireSeries.Spec.Data Spec.Data

lemma continuous_determinantIntegral {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ] (n : ℕ) :
    Continuous (fun k : C(Q × Q, ℂ) => DeterminantIntegralValue μ k n) := by
  have : IsFiniteMeasure (MeasurePowerValue μ n) :=
    inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Fin n => μ)))
  apply continuous_iff_continuousAt.mpr
  intro k
  apply continuousAt_of_dominated (bound := fun _ => hadamardBound (‖k‖ + 1) n)
  · exact Eventually.of_forall fun l =>
      (ClassicalDefinitions.integrable_determinants μ l n).1.aestronglyMeasurable
  · have hn : ∀ᶠ l : C(Q × Q, ℂ) in 𝓝 k, ‖l‖ < ‖k‖ + 1 :=
      (continuous_norm.tendsto k).eventually (gt_mem_nhds (by linarith))
    filter_upwards [hn] with l hl
    exact Eventually.of_forall fun t =>
      ClassicalEntireSeries.norm_det_le_hadamard n _ (‖k‖ + 1) (by positivity)
        (fun i j => (l.norm_coe_le_norm (t i, t j)).trans hl.le)
  · exact integrable_const _
  · apply Eventually.of_forall
    intro t
    apply Continuous.continuousAt
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (ContinuousMap.evalCLM ℂ (t i, t j)).continuous

lemma determinant_term_bound {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ]
    (k : C(Q × Q, ℂ)) (M R : ℝ) (hM : ‖k‖ ≤ M) (hR : 0 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖DeterminantTermValue μ k z n‖ ≤ determinantMajorant (MeasureMassValue μ) M R n := by
  have h := (ClassicalEntireSeries.uniform_term_bounds μ k R hR z hz n).1
  apply h.trans
  unfold determinantMajorant hadamardBound
  gcongr
  exact pow_nonneg (show 0 ≤ MeasureMassValue μ from measureReal_nonneg) n

lemma continuous_determinantTerm {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ] (n : ℕ) :
    Continuous (fun p : C(Q × Q, ℂ) × ℂ => DeterminantTermValue μ p.1 p.2 n) := by
  exact ((continuous_snd.neg.pow n).div_const (n.factorial : ℂ)).mul
    ((continuous_determinantIntegral μ n).comp continuous_fst)

lemma continuous_determinant_joint {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ] :
    Continuous (fun p : C(Q × Q, ℂ) × ℂ => FredholmDeterminantValue μ p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let S : Set (C(Q × Q, ℂ) × ℂ) := {q | ‖q.1‖ < ‖p.1‖ + 1 ∧ ‖q.2‖ < ‖p.2‖ + 1}
  have hs := (ClassicalEntireSeries.majorants_summable (MeasureMassValue μ)
    (‖p.1‖ + 1) (‖p.2‖ + 1) measureReal_nonneg (by positivity) (by positivity)).1
  have hc : ContinuousOn (fun q : C(Q × Q, ℂ) × ℂ =>
      FredholmDeterminantValue μ q.1 q.2) S :=
    continuousOn_tsum (fun n => (continuous_determinantTerm μ n).continuousOn) hs
      (fun n q hq => determinant_term_bound μ q.1 _ _ hq.1.le (by positivity) q.2 hq.2.le n)
  have hS : S ∈ 𝓝 p := by
    apply IsOpen.mem_nhds
    · exact (isOpen_lt (continuous_fst.norm) continuous_const).inter
        (isOpen_lt (continuous_snd.norm) continuous_const)
    · constructor <;> linarith
  exact hc.continuousAt hS

lemma continuous_determinant_on_disk {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ] (R : ℝ) :
    Continuous (fun k : C(Q × Q, ℂ) => determinantOnDisk μ k R
      (ClassicalEntireSeries.entire_functions μ k).1.continuous) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_determinant_joint μ).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))


theorem uniform_kernel_continuity : Spec.UniformKernelContinuity.{u} := by
  intro Q _ _ _ _ μ _ k R ε hR hε
  let F := fun l : C(Q × Q, ℂ) => determinantOnDisk μ l R
    (ClassicalEntireSeries.entire_functions μ l).1.continuous
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp
    (continuous_determinant_on_disk μ R).continuousAt ε hε
  refine ⟨δ, hδ, fun l hl z hz => ?_⟩
  have hb : ‖F l - F k‖ < ε := by
    simpa only [dist_eq_norm] using h (show dist l k < δ by simpa [dist_eq_norm] using hl)
  exact ((F l - F k).norm_coe_le_norm ⟨z, by simpa using hz⟩).trans_lt hb

theorem locally_uniform_kernel_limit : Spec.LocallyUniformKernelLimit.{u} := by
  intro Q _ _ _ _ μ _ k l hk R hR
  have ht := ((continuous_determinant_on_disk μ R).tendsto l).comp hk
  have hu := ContinuousMap.tendsto_iff_tendstoUniformly.mp ht
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr hu

lemma continuous_compositionIntegrand {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    (k l : C(Q × Q, ℂ)) : Continuous (compositionIntegrand k l) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (k.continuous.comp ((continuous_fst.comp continuous_snd).prodMk continuous_fst)).mul
    (l.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

theorem composition_formula : Spec.CompositionFormula.{u} := by
  intro Q _ _ _ _ μ _ k l x y
  exact ContinuousMap.integral_apply
    ((continuous_compositionIntegrand k l).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (x, y)

lemma norm_compositionIntegrand_le {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    (k l : C(Q × Q, ℂ)) (t : Q) : ‖compositionIntegrand k l t‖ ≤ ‖k‖ * ‖l‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro p
  exact (norm_mul _ _).trans_le
    (mul_le_mul (k.norm_coe_le_norm _) (l.norm_coe_le_norm _) (norm_nonneg _)
      (norm_nonneg _))

lemma continuous_compositionKernel {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ] :
    Continuous (fun p : C(Q × Q, ℂ) × C(Q × Q, ℂ) => compositionKernel μ p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply continuousAt_of_dominated (bound := fun _ => (‖p.1‖ + 1) * (‖p.2‖ + 1))
  · exact Eventually.of_forall fun q =>
      ((continuous_compositionIntegrand q.1 q.2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).aestronglyMeasurable
  · have h₁ : ∀ᶠ q : C(Q × Q, ℂ) × C(Q × Q, ℂ) in 𝓝 p, ‖q.1‖ < ‖p.1‖ + 1 :=
      ((continuous_fst.norm).tendsto p).eventually (gt_mem_nhds (by linarith))
    have h₂ : ∀ᶠ q : C(Q × Q, ℂ) × C(Q × Q, ℂ) in 𝓝 p, ‖q.2‖ < ‖p.2‖ + 1 :=
      ((continuous_snd.norm).tendsto p).eventually (gt_mem_nhds (by linarith))
    filter_upwards [h₁, h₂] with q hq₁ hq₂
    exact Eventually.of_forall fun t => (norm_compositionIntegrand_le q.1 q.2 t).trans
      (mul_le_mul hq₁.le hq₂.le (norm_nonneg _) (by positivity))
  · exact integrable_const _
  · apply Eventually.of_forall
    intro t
    apply Continuous.continuousAt
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_fst.fst.eval
      ((continuous_fst.comp continuous_snd).prodMk continuous_const)).mul
      (continuous_fst.snd.eval (continuous_const.prodMk (continuous_snd.comp continuous_snd)))

lemma continuous_productKernel {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ] :
    Continuous (fun p : C(Q × Q, ℂ) × C(Q × Q, ℂ) => productKernel μ p.1 p.2) :=
  (continuous_fst.add continuous_snd).sub (continuous_compositionKernel μ)


set_option maxHeartbeats 4000000 in
/-- Passage to the limit only uses density and the multiplication identity on
finite separable kernels. No invertibility hypothesis is needed. -/
lemma multiplication_of_dense_finite_rank
    {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ]
    (hd : Dense {k : C(Q × Q, ℂ) | ∃ (N : ℕ) (a b : Fin N → C(Q, ℂ)),
      k = separableKernel N a b})
    (hf : ∀ (k l : C(Q × Q, ℂ)),
      (∃ (N : ℕ) (a b : Fin N → C(Q, ℂ)), k = separableKernel N a b) →
      (∃ (N : ℕ) (a b : Fin N → C(Q, ℂ)), l = separableKernel N a b) →
      FredholmDeterminantValue μ (productKernel μ k l) 1 =
        FredholmDeterminantValue μ k 1 * FredholmDeterminantValue μ l 1)
    (k l : C(Q × Q, ℂ)) :
    FredholmDeterminantValue μ (productKernel μ k l) 1 =
      FredholmDeterminantValue μ k 1 * FredholmDeterminantValue μ l 1 := by
  let S : Set C(Q × Q, ℂ) := {k | ∃ (N : ℕ) (a b : Fin N → C(Q, ℂ)),
    k = separableKernel N a b}
  have hD : Continuous (fun k : C(Q × Q, ℂ) => FredholmDeterminantValue μ k 1) :=
    (continuous_determinant_joint μ).comp (continuous_id.prodMk continuous_const)
  have hclosed : IsClosed {p : C(Q × Q, ℂ) × C(Q × Q, ℂ) |
      FredholmDeterminantValue μ (productKernel μ p.1 p.2) 1 =
        FredholmDeterminantValue μ p.1 1 * FredholmDeterminantValue μ p.2 1} :=
    isClosed_eq (hD.comp (continuous_productKernel μ))
      ((hD.comp continuous_fst).mul (hD.comp continuous_snd))
  have hsub : S ×ˢ S ⊆ {p | FredholmDeterminantValue μ (productKernel μ p.1 p.2) 1 =
      FredholmDeterminantValue μ p.1 1 * FredholmDeterminantValue μ p.2 1} :=
    fun p hp => hf p.1 p.2 hp.1 hp.2
  have hdp : Dense (S ×ˢ S) := Dense.prod hd hd
  have hc := closure_minimal hsub hclosed
  exact hc (hdp (k, l))

lemma scalar_multiplication_of_multiplication (h : Spec.Multiplication.{u}) :
    Spec.ScalarMultiplication.{u} := by
  intro Q _ _ _ _ μ _ k l a b
  exact h μ (a • k) (b • l)


lemma determinant_integral_smul {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] (μ : Measure Q) (k : C(Q × Q, ℂ)) (a : ℂ) (n : ℕ) :
    DeterminantIntegralValue μ (a • k) n = a ^ n * DeterminantIntegralValue μ k n := by
  unfold DeterminantIntegralValue
  have he : ∀ t : Fin n → Q,
      KernelMatrixValue (a • k) n t = a • KernelMatrixValue k n t := fun _ => rfl
  simp_rw [he, Matrix.det_smul, Fintype.card_fin]
  exact integral_const_mul _ _

theorem scalar_parameter : Spec.ScalarParameter.{u} := by
  intro Q _ _ _ _ μ _ k a z
  apply tsum_congr
  intro n
  change (-z) ^ n / (n.factorial : ℂ) * DeterminantIntegralValue μ (a • k) n =
    (-(a * z)) ^ n / (n.factorial : ℂ) * DeterminantIntegralValue μ k n
  rw [determinant_integral_smul]
  have hp : (-(a * z)) ^ n = a ^ n * (-z) ^ n := by rw [← mul_pow]; congr 1; ring
  rw [hp]
  ring

section FiniteSeparable
variable {Q : Type u} [MetricSpace Q] [CompactSpace Q]

@[simp] lemma separableKernel_apply (N : ℕ) (a b : Fin N → C(Q, ℂ)) (x y : Q) :
    separableKernel N a b (x, y) = ∑ i, a i x * b i y := by
  simp [separableKernel]

/-- A finite index type can always be replaced by the canonical `Fin N` index. -/
lemma exists_separableKernel_of_fintype {I : Type*} [Fintype I]
    (a b : I → C(Q, ℂ)) :
    ∃ (N : ℕ) (a' b' : Fin N → C(Q, ℂ)),
      (∑ i, (a i).comp ⟨Prod.fst, continuous_fst⟩ *
        (b i).comp ⟨Prod.snd, continuous_snd⟩) = separableKernel N a' b' := by
  classical
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, a ∘ e.symm, b ∘ e.symm, ?_⟩
  unfold separableKernel
  exact Fintype.sum_equiv e _ _ (fun i => by simp)

lemma separableKernel_add (N M : ℕ) (a b : Fin N → C(Q, ℂ))
    (c d : Fin M → C(Q, ℂ)) :
    separableKernel N a b + separableKernel M c d =
      separableKernel (N + M) (Fin.append a c) (Fin.append b d) := by
  ext ⟨x, y⟩
  simp [Fin.sum_univ_add]

/-- Finite separable kernels form an algebra. This includes constants and rank zero. -/
noncomputable def separableAlgebra : Subalgebra ℂ C(Q × Q, ℂ) where
  carrier := {k | ∃ (N : ℕ) (a b : Fin N → C(Q, ℂ)), k = separableKernel N a b}
  zero_mem' := ⟨0, Fin.elim0, Fin.elim0, by simp [separableKernel]⟩
  one_mem' := ⟨1, fun _ => 1, fun _ => 1, by ext p; simp [separableKernel]⟩
  add_mem' := by
    rintro k l ⟨N, a, b, rfl⟩ ⟨M, c, d, rfl⟩
    exact ⟨N + M, Fin.append a c, Fin.append b d, separableKernel_add N M a b c d⟩
  mul_mem' := by
    rintro k l ⟨N, a, b, rfl⟩ ⟨M, c, d, rfl⟩
    obtain ⟨P, e, f, hf⟩ := exists_separableKernel_of_fintype
      (fun i : Fin N × Fin M => a i.1 * c i.2)
      (fun i : Fin N × Fin M => b i.1 * d i.2)
    refine ⟨P, e, f, ?_⟩
    rw [← hf]
    ext ⟨x, y⟩
    simp only [ContinuousMap.mul_apply, separableKernel_apply, ContinuousMap.sum_apply,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk, Fintype.sum_prod_type,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  algebraMap_mem' := by
    intro z
    refine ⟨1, fun _ => ContinuousMap.const Q z, fun _ => 1, ?_⟩
    ext p
    simp [separableKernel]

lemma star_mem_separableAlgebra (k : C(Q × Q, ℂ)) (hk : k ∈ separableAlgebra (Q := Q)) :
    star k ∈ separableAlgebra (Q := Q) := by
  classical
  obtain ⟨N, a, b, rfl⟩ := hk
  refine ⟨N, fun i => star (a i), fun i => star (b i), ?_⟩
  ext ⟨x, y⟩
  simp [star_mul, mul_comm]

lemma separableAlgebra_separatesPoints : (separableAlgebra (Q := Q)).SeparatesPoints := by
  classical
  intro p q hpq
  by_cases h : p.1 = q.1
  · have h' : p.2 ≠ q.2 := fun he => hpq (Prod.ext h he)
    let b : C(Q, ℂ) := ⟨fun y => (dist y p.2 : ℂ),
      Complex.continuous_ofReal.comp (continuous_id.dist continuous_const)⟩
    let f := separableKernel 1 (fun _ => (1 : C(Q, ℂ))) (fun _ => b)
    refine ⟨f, ⟨f, ⟨1, _, _, rfl⟩, rfl⟩, ?_⟩
    change f p ≠ f q
    simpa [f, separableKernel, b] using
      (show (0 : ℂ) ≠ (dist q.2 p.2 : ℂ) by
        exact_mod_cast (dist_ne_zero.mpr (Ne.symm h')).symm)
  · let a : C(Q, ℂ) := ⟨fun x => (dist x p.1 : ℂ),
      Complex.continuous_ofReal.comp (continuous_id.dist continuous_const)⟩
    let f := separableKernel 1 (fun _ => a) (fun _ => (1 : C(Q, ℂ)))
    refine ⟨f, ⟨f, ⟨1, _, _, rfl⟩, rfl⟩, ?_⟩
    change f p ≠ f q
    simpa [f, separableKernel, a] using
      (show (0 : ℂ) ≠ (dist q.1 p.1 : ℂ) by
        exact_mod_cast (dist_ne_zero.mpr (Ne.symm h)).symm)

/-- Stone--Weierstrass gives approximation by finite sums `a(x)b(y)`. -/
lemma dense_separableKernel :
    Dense {k : C(Q × Q, ℂ) | ∃ (N : ℕ) (a b : Fin N → C(Q, ℂ)),
      k = separableKernel N a b} :=
  ExpandedFA.Approximation.StoneWeierstrass.complex_dense (Q × Q) separableAlgebra
    separableAlgebra_separatesPoints star_mem_separableAlgebra

end FiniteSeparable

/-! Finite-rank kernels: permutation expansion, independent integrals, and principal minors. -/

lemma integral_permuted_prod {Q : Type u} [MeasurableSpace Q]
    (μ : Measure Q) [SigmaFinite μ] {n : ℕ} (a b : Fin n → Q → ℂ)
    (σ : Equiv.Perm (Fin n)) :
    (∫ t : Fin n → Q, ∏ i, a i (t (σ i)) * b i (t i)
      ∂Measure.pi (fun _ : Fin n => μ)) =
      ∏ i, ∫ x, b (σ i) x * a i x ∂μ := by
  have hp (t : Fin n → Q) :
      (∏ i, a i (t (σ i)) * b i (t i)) =
      ∏ j, a (σ.symm j) (t j) * b j (t j) := by
    simp only [Finset.prod_mul_distrib]
    congr 1
    simpa using (σ.symm.prod_comp (fun i => a i (t (σ i)))).symm
  simp_rw [hp]
  rw [show (∫ t : Fin n → Q, ∏ j, a (σ.symm j) (t j) * b j (t j)
      ∂Measure.pi (fun _ : Fin n => μ)) =
      ∏ j, ∫ x, a (σ.symm j) x * b j x ∂μ from
    integral_fintype_prod_eq_prod (fun j x => a (σ.symm j) x * b j x)]
  simpa [mul_comm] using (Equiv.prod_comp σ
    (fun j => ∫ x, a (σ.symm j) x * b j x ∂μ)).symm

lemma determinantIntegral_separableKernel {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ]
    (N n : ℕ) (a b : Fin N → C(Q, ℂ)) :
    DeterminantIntegralValue μ (separableKernel N a b) n =
      ∑ f : Fin n → Fin N, (pairingMatrix μ N a b |>.submatrix f f).det := by
  classical
  let F := fun (f : Fin n → Fin N) (σ : Equiv.Perm (Fin n)) (t : Fin n → Q) =>
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, a (f i) (t (σ i)) * b (f i) (t i)
  have hc (f : Fin n → Fin N) (σ : Equiv.Perm (Fin n)) : Continuous (F f σ) := by
    dsimp [F]
    fun_prop
  have hi (f : Fin n → Fin N) (σ : Equiv.Perm (Fin n)) :
      Integrable (F f σ) (MeasurePowerValue μ n) := by
    change Integrable _ (Measure.pi (fun _ : Fin n => μ))
    exact (hc f σ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpoint (t : Fin n → Q) :
      (KernelMatrixValue (separableKernel N a b) n t).det =
      ∑ f : Fin n → Fin N, ∑ σ : Equiv.Perm (Fin n), F f σ t := by
    simp only [Matrix.det_apply', KernelMatrixValue, separableKernel_apply,
      Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
    exact Finset.sum_comm
  unfold DeterminantIntegralValue
  simp_rw [hpoint]
  rw [integral_finsetSum _ (fun f _ => integrable_finsetSum _ (fun σ _ => hi f σ))]
  apply Finset.sum_congr rfl
  intro f hf
  rw [integral_finsetSum _ (fun σ _ => hi f σ)]
  simp only [F, integral_const_mul, MeasurePowerValue, integral_permuted_prod]
  simpa only [pairingMatrix, Matrix.submatrix_apply] using
    (Matrix.det_apply' ((pairingMatrix μ N a b).submatrix f f)).symm


open Finset Matrix
open scoped Polynomial


noncomputable def embeddingFiberEquiv {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (s : Finset β) :
    {p : α ↪ β // Finset.univ.map p = s} ≃ (α ≃ s) where
  toFun p := Equiv.ofBijective (fun i => ⟨p.val i, by simpa only [p.property] using (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩ : p.val i ∈ Finset.univ.map p.val)⟩)
    ⟨fun i j h => p.val.injective (congrArg Subtype.val h), by
      rintro ⟨j,hj⟩
      have : j ∈ Finset.univ.map p.val := by rwa [p.property]
      rcases Finset.mem_map.mp this with ⟨i,_,hi⟩
      exact ⟨i, Subtype.ext hi⟩⟩
  invFun e := ⟨⟨fun i => (e i).val, fun i j h => e.injective (Subtype.ext h)⟩, by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨i,_,rfl⟩
      exact (e i).property
    · intro hj
      obtain ⟨i,hi⟩ := e.surjective ⟨j,hj⟩
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, congrArg Subtype.val hi⟩⟩
  left_inv p := by apply Subtype.ext; apply Function.Embedding.ext; intro i; rfl
  right_inv e := by apply Equiv.ext; intro i; rfl


theorem sum_det_submatrix_embedding {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommRing R] (M : Matrix β β R) :
    (∑ p : α ↪ β, (M.submatrix p p).det) =
    ∑ s : Finset β, (Fintype.card (α ≃ s) : R) *
      (M.submatrix (Subtype.val : s → β) (Subtype.val : s → β)).det := by
  classical
  rw [← Fintype.sum_fiberwise (fun p : α ↪ β => Finset.univ.map p)]
  apply Fintype.sum_congr
  intro s
  calc
    (∑ p : {p : α ↪ β // Finset.univ.map p = s},
        (M.submatrix p.val p.val).det) =
      ∑ _ : α ≃ s, (M.submatrix (Subtype.val : s → β) (Subtype.val : s → β)).det := by
        apply Fintype.sum_equiv (embeddingFiberEquiv s)
        intro p
        change ((M.submatrix (Subtype.val : s → β) (Subtype.val : s → β)).submatrix
          (embeddingFiberEquiv s p) (embeddingFiberEquiv s p)).det = _
        exact Matrix.det_submatrix_equiv_self _ _
    _ = _ := by simp

theorem card_equiv_finset {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (s : Finset β) :
    Fintype.card (α ≃ s) = if s.card = Fintype.card α then (Fintype.card α).factorial else 0 := by
  classical
  by_cases h : s.card = Fintype.card α
  · rw [ite_eq_left h]
    exact Fintype.card_equiv (Fintype.equivOfCardEq (by simpa using h.symm))
  · rw [ite_eq_right h]
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun e => h (by simpa using (Fintype.card_congr e).symm)⟩

theorem sum_det_submatrix_embedding_eq_factorial {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommRing R] (M : Matrix β β R) :
    (∑ p : α ↪ β, (M.submatrix p p).det) =
    ((Fintype.card α).factorial : R) *
      ∑ s ∈ Finset.univ.powersetCard (Fintype.card α),
        (M.submatrix (Subtype.val : s → β) (Subtype.val : s → β)).det := by
  classical
  rw [sum_det_submatrix_embedding]
  simp_rw [card_equiv_finset, Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hs : Finset.univ.filter (fun s : Finset β => s.card = Fintype.card α) =
      Finset.univ.powersetCard (Fintype.card α) := by
    ext s
    simp
  rw [hs, Finset.mul_sum]

theorem sum_det_submatrix_eq_embedding {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommRing R] (M : Matrix β β R) :
    (∑ p : α → β, (M.submatrix p p).det) =
    ∑ p : α ↪ β, (M.submatrix p p).det := by
  classical
  calc
    _ = ∑ p : α → β with Function.Injective p, (M.submatrix p p).det := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p hp hp'
      have hn : ¬ Function.Injective p := by simpa using hp'
      obtain ⟨i, j, hij, hne⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
        simpa only [Function.Injective, not_forall, exists_prop] using hn
      apply Matrix.det_zero_of_row_eq hne
      funext l
      exact congrArg (fun q => M q (p l)) hij
    _ = ∑ p : {p : α → β // Function.Injective p}, (M.submatrix p.val p.val).det := by
      exact Finset.sum_subtype _ (by simp) _
    _ = _ := by
      exact Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding α β) _ _ (by intro p; rfl)

theorem sum_det_submatrix_eq_factorial_coeff {β R : Type*} [Fintype β]
    [DecidableEq β] [CommRing R] (M : Matrix β β R) (n : ℕ) :
    (∑ p : Fin n → β, (M.submatrix p p).det) =
    (n.factorial : R) *
      (Matrix.det (1 + (Polynomial.X : R[X]) • M.map Polynomial.C)).coeff n := by
  rw [sum_det_submatrix_eq_embedding, sum_det_submatrix_embedding_eq_factorial,
    Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  simp

theorem determinant_polynomial_eval_generic {β : Type*} [Fintype β] [DecidableEq β]
    (M : Matrix β β ℂ) (c : ℂ) :
    (Matrix.det (1 + (Polynomial.X : ℂ[X]) • M.map Polynomial.C)).eval c =
      (1 + c • M).det := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply]
  split_ifs <;> simp [mul_comm]

theorem determinant_series_eq_det {β : Type*} [Fintype β] [DecidableEq β]
    (M : Matrix β β ℂ) (c : ℂ) :
    (∑' n : ℕ, c ^ n / (n.factorial : ℂ) *
      ∑ p : Fin n → β, (M.submatrix p p).det) = (1 + c • M).det := by
  classical
  let p : ℂ[X] := Matrix.det (1 + (Polynomial.X : ℂ[X]) • M.map Polynomial.C)
  calc
    _ = ∑' n : ℕ, p.coeff n * c ^ n := by
      apply tsum_congr
      intro n
      rw [sum_det_submatrix_eq_factorial_coeff]
      change c ^ n / (n.factorial : ℂ) * ((n.factorial : ℂ) * p.coeff n) = _
      have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
      field_simp
    _ = p.eval c := by
      rw [tsum_eq_sum (s := Finset.range (p.natDegree + 1))]
      · exact (p.eval_eq_sum_range c).symm
      · intro n hn
        rw [p.coeff_eq_zero_of_natDegree_lt (by simpa using hn), zero_mul]
    _ = _ := determinant_polynomial_eval_generic M c


theorem finite_rank_formula : Spec.FiniteRankFormula.{u} := by
  classical
  intro Q _ _ _ _ μ _ N a b z
  unfold FredholmDeterminantValue DeterminantTermValue
  simp_rw [determinantIntegral_separableKernel]
  simpa only [neg_smul, sub_eq_add_neg] using
    determinant_series_eq_det (pairingMatrix μ N a b) (-z)


section FiniteMultiplication
variable {Q : Type u} [MetricSpace Q] [CompactSpace Q]
  [MeasurableSpace Q] [BorelSpace Q]
  (μ : Measure Q) [IsFiniteMeasure μ]

private lemma continuous_scalar_integrable (f : Q → ℂ) (hf : Continuous f) :
    Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private lemma integral_product_separable (N : ℕ) (a b c : Fin N → C(Q, ℂ)) (x y : Q) :
    (∫ t, separableKernel N a b (x,t) * separableKernel N a c (t,y) ∂μ) =
      ∑ i, a i x * ∑ j, pairingMatrix μ N a b i j * c j y := by
  classical
  simp_rw [separableKernel_apply, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      change (∫ t, a i x * b i t * (a j t * c j y) ∂μ) =
        a i x * ((∫ t, b i t * a j t ∂μ) * c j y)
      simp_rw [show ∀ t, a i x * b i t * (a j t * c j y) =
          a i x * ((b i t * a j t) * c j y) from fun t => by ring]
      rw [integral_const_mul, integral_mul_const]
    · intro j hj
      apply continuous_scalar_integrable
      fun_prop
  · intro i hi
    apply continuous_scalar_integrable
    fun_prop

noncomputable def compositionCoefficients (N : ℕ) (a b c : Fin N → C(Q, ℂ)) :
    Fin N → C(Q, ℂ) :=
  fun i => ∑ j, pairingMatrix μ N a b i j • c j

lemma compositionKernel_same_range (N : ℕ) (a b c : Fin N → C(Q, ℂ)) :
    compositionKernel μ (separableKernel N a b) (separableKernel N a c) =
      separableKernel N a (compositionCoefficients μ N a b c) := by
  ext ⟨x,y⟩
  rw [composition_formula, integral_product_separable]
  simp [compositionCoefficients, separableKernel_apply]

lemma pairingMatrix_compositionCoefficients (N : ℕ) (a b c : Fin N → C(Q, ℂ)) :
    pairingMatrix μ N a (compositionCoefficients μ N a b c) =
      pairingMatrix μ N a b * pairingMatrix μ N a c := by
  classical
  ext i j
  simp only [pairingMatrix, compositionCoefficients, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, Finset.sum_mul, Matrix.mul_apply]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r hr
    simp_rw [mul_assoc]
    rw [integral_const_mul]
  · intro r hr
    apply continuous_scalar_integrable
    fun_prop

omit [MeasurableSpace Q] [BorelSpace Q] in
lemma separableKernel_add_sub_coefficients (N : ℕ) (a b c d : Fin N → C(Q, ℂ)) :
    separableKernel N a (b + c - d) =
      separableKernel N a b + separableKernel N a c - separableKernel N a d := by
  ext ⟨x,y⟩
  simp [separableKernel_apply, mul_sub, mul_add, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

lemma pairingMatrix_add_sub_coefficients (N : ℕ) (a b c d : Fin N → C(Q, ℂ)) :
    pairingMatrix μ N a (b + c - d) =
      pairingMatrix μ N a b + pairingMatrix μ N a c - pairingMatrix μ N a d := by
  ext i j
  simp only [pairingMatrix, Pi.sub_apply, Pi.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.add_apply, sub_mul, add_mul, Matrix.sub_apply, Matrix.add_apply]
  rw [integral_sub, integral_add]
  all_goals first
    | apply Integrable.add <;> apply continuous_scalar_integrable <;> fun_prop
    | apply continuous_scalar_integrable; fun_prop

lemma finite_rank_multiplication_same_range (hF : Spec.FiniteRankFormula.{u})
    (N : ℕ) (a b c : Fin N → C(Q, ℂ)) :
    FredholmDeterminantValue μ
      (productKernel μ (separableKernel N a b) (separableKernel N a c)) 1 =
      FredholmDeterminantValue μ (separableKernel N a b) 1 *
        FredholmDeterminantValue μ (separableKernel N a c) 1 := by
  classical
  have hp : productKernel μ (separableKernel N a b) (separableKernel N a c) =
      separableKernel N a (b + c - compositionCoefficients μ N a b c) := by
    rw [separableKernel_add_sub_coefficients, ← compositionKernel_same_range]
    rfl
  rw [hp, hF, hF, hF, one_smul, one_smul, one_smul,
    pairingMatrix_add_sub_coefficients, pairingMatrix_compositionCoefficients]
  rw [← Matrix.det_mul]
  congr 1
  noncomm_ring

omit [MeasurableSpace Q] [BorelSpace Q] in
lemma separableKernel_append_zero_right (N M : ℕ) (a b : Fin N → C(Q, ℂ))
    (c : Fin M → C(Q, ℂ)) :
    separableKernel (N + M) (Fin.append a c) (Fin.append b 0) =
      separableKernel N a b := by
  rw [← separableKernel_add]
  simp [separableKernel]

omit [MeasurableSpace Q] [BorelSpace Q] in
lemma separableKernel_append_zero_left (N M : ℕ) (a : Fin N → C(Q, ℂ))
    (c d : Fin M → C(Q, ℂ)) :
    separableKernel (N + M) (Fin.append a c) (Fin.append 0 d) =
      separableKernel M c d := by
  rw [← separableKernel_add]
  simp [separableKernel]

lemma finite_rank_multiplication (hF : Spec.FiniteRankFormula.{u})
    (k l : C(Q × Q, ℂ))
    (hk : ∃ (N : ℕ) (a b : Fin N → C(Q, ℂ)), k = separableKernel N a b)
    (hl : ∃ (N : ℕ) (a b : Fin N → C(Q, ℂ)), l = separableKernel N a b) :
    FredholmDeterminantValue μ (productKernel μ k l) 1 =
      FredholmDeterminantValue μ k 1 * FredholmDeterminantValue μ l 1 := by
  obtain ⟨N,a,b,rfl⟩ := hk
  obtain ⟨M,c,d,rfl⟩ := hl
  have h := finite_rank_multiplication_same_range μ hF (N+M)
    (Fin.append a c) (Fin.append b 0) (Fin.append 0 d)
  simpa only [separableKernel_append_zero_right, separableKernel_append_zero_left] using h

lemma multiplication_of_finite_rank_formula (hF : Spec.FiniteRankFormula.{u}) :
    Spec.Multiplication.{u} := by
  intro Q _ _ _ _ μ _ k l
  exact multiplication_of_dense_finite_rank μ dense_separableKernel
    (finite_rank_multiplication μ hF) k l

end FiniteMultiplication

theorem multiplication : Spec.Multiplication.{u} :=
  multiplication_of_finite_rank_formula finite_rank_formula

theorem scalar_multiplication : Spec.ScalarMultiplication.{u} :=
  scalar_multiplication_of_multiplication multiplication

end ExpandedFA.FredholmDeterminant.ClassicalProduct
