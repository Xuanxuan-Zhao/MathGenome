import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.TraceDeterminantContinuity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.TraceClassDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.TraceNormIdeal
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement

noncomputable section
universe v w
namespace ExpandedFA.FredholmDeterminant.TraceDeterminantContinuity
open TraceClassDefinitions
open TraceIdeals.TraceClassDefinitions
open Filter
open scoped Topology Classical

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Uniform factorial majorant for the actual exterior coefficients. -/
lemma exterior_term_bound (T : H →L[ℂ] H) (hT : IsTraceClass T)
    {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖z ^ n * exteriorTrace T n‖ ≤ (R * traceNorm T) ^ n / (n.factorial : ℝ) := by
  calc
    _ = ‖z‖ ^ n * ‖exteriorTrace T n‖ := by rw [norm_mul, norm_pow]
    _ ≤ R ^ n * (traceNorm T ^ n / (n.factorial : ℝ)) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz n)
        (TraceClassDefinitions.exterior_trace_factorial_bound T hT n)
        (norm_nonneg _) (pow_nonneg hR n)
    _ = _ := by rw [← mul_div_assoc, ← mul_pow]

lemma determinant_differentiable (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    Differentiable ℂ (fredholmDeterminant T) := by
  intro z
  let R : ℝ := ‖z‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hd : DifferentiableOn ℂ (fredholmDeterminant T) (Metric.ball 0 R) := by
    apply Complex.differentiableOn_tsum_of_summable_norm
      (Real.summable_pow_div_factorial (R * traceNorm T))
    · intro n
      exact ((differentiable_id.pow n).mul_const (exteriorTrace T n)).differentiableOn
    · exact Metric.isOpen_ball
    · intro n w hw
      exact exterior_term_bound T hT hR (by simpa using (mem_ball_zero_iff.mp hw).le) n
  apply hd.differentiableAt
  exact Metric.isOpen_ball.mem_nhds (by simp [R])

theorem entire_exterior_series : Spec.EntireExteriorSeries.{v} := by
  intro H _ _ _ T hT
  exact ⟨fun z => (fredholm_series_bound T hT z).1, determinant_differentiable T hT⟩

theorem uniform_exterior_series : Spec.UniformExteriorSeries.{v} := by
  intro H _ _ _ T hT R hR
  exact tendstoUniformlyOn_tsum_nat
    (Real.summable_pow_div_factorial (R * traceNorm T))
    (fun n z hz => exterior_term_bound T hT hR (mem_closedBall_zero_iff.mp hz) n)

theorem exterior_traceNorm_bound : Spec.ExteriorTraceNormBound.{v} := by
  intro H _ _ _ T hT n
  exact ⟨(exterior_construction T hT n).2.1, (exterior_construction T hT n).2.2.1⟩

omit [CompleteSpace H] in
/-- Homogeneity holds directly for the shared principal-minor definition. -/
lemma principalMinor_smul {ι : Type w} (b : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (c : ℂ) (s : Finset ι) :
    principalMinor b (c • T) s = c ^ s.card * principalMinor b T s := by
  classical
  let M : Matrix s s ℂ := fun i j => inner ℂ (b i.val) (T (b j.val))
  let N : Matrix s s ℂ := fun i j => inner ℂ (b i.val) ((c • T) (b j.val))
  change N.det = c ^ s.card * M.det
  have hm : N = c • M := by
    ext i j
    rw [Matrix.smul_apply]
    change inner ℂ (b i.val) ((c • T) (b j.val)) =
      c * inner ℂ (b i.val) (T (b j.val))
    simp only [smul_apply, inner_smul_right]
  rw [hm, Matrix.det_smul, Fintype.card_coe]

lemma exteriorTrace_smul (T : H →L[ℂ] H) (c : ℂ) (n : ℕ) :
    exteriorTrace (c • T) n = c ^ n * exteriorTrace T n := by
  classical
  unfold exteriorTrace TraceClassDefinitions.Spec.ExteriorTraceValue
  simp_rw [principalMinor_smul, Set.powersetCard.card_eq]
  exact tsum_mul_left

lemma determinant_smul (T : H →L[ℂ] H) (c z : ℂ) :
    fredholmDeterminant (c • T) z = fredholmDeterminant T (z * c) := by
  unfold fredholmDeterminant TraceClassDefinitions.Spec.FredholmDeterminantValue
  simp_rw [exteriorTrace_smul, mul_pow, mul_assoc]

/-- Homogeneity turns the estimate at one into its parameter-dependent form. -/
lemma parameter_bound_of_bound_at_one (hb : Spec.DeterminantPerturbationBound.{v}) :
    Spec.ParameterPerturbationBound.{v} := by
  intro H _ _ _ S T hS hT z
  have hdiff := TraceIdeals.TraceNormIdeal.traceClass_sub T S hT hS
  have h := hb (z • S) (z • T)
    (TraceIdeals.TraceNormIdeal.traceClass_smul z S hS).1
    (TraceIdeals.TraceNormIdeal.traceClass_smul z T hT).1
  simpa only [← smul_sub, (TraceIdeals.TraceNormIdeal.traceClass_smul z (T - S) hdiff).2,
    (TraceIdeals.TraceNormIdeal.traceClass_smul z T hT).2,
    (TraceIdeals.TraceNormIdeal.traceClass_smul z S hS).2,
    determinant_smul, one_mul, mul_max_of_nonneg _ _ (norm_nonneg z)] using h

/-- Trace norms of a trace-norm-convergent net are eventually bounded. -/
lemma eventually_traceNorm_le {I : Type w} {l : Filter I} (T : I → H →L[ℂ] H) (L : H →L[ℂ] H)
    (hT : ∀ n, IsTraceClass (T n)) (hL : IsTraceClass L)
    (hconv : Tendsto (fun n => traceNorm (T n - L)) l (𝓝 0)) :
    ∀ᶠ n in l, traceNorm (T n) ≤ traceNorm L + 1 := by
  filter_upwards [hconv.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
  have h := (TraceIdeals.TraceNormIdeal.traceClass_add (T n - L) L
    (TraceIdeals.TraceNormIdeal.traceClass_sub _ _ (hT n) hL) hL).2
  rw [sub_add_cancel] at h
  linarith

/-- The sharp bound implies locally uniform trace-norm continuity. -/
lemma locally_uniform_of_parameter_bound (hb : Spec.ParameterPerturbationBound.{v}) :
    Spec.TraceNormLocallyUniform.{v,w} := by
  intro H _ _ _ I l T L hT hL hconv R hR
  let C := traceNorm L + 1
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith [TraceIdeals.TraceNormIdeal.traceNorm_nonneg L hL]
  have hδ (n : I) : 0 ≤ traceNorm (T n - L) :=
    TraceIdeals.TraceNormIdeal.traceNorm_nonneg _
      (TraceIdeals.TraceNormIdeal.traceClass_sub _ _ (hT n) hL)
  have hlim : Tendsto (fun n => (R * Real.exp (R * C)) * traceNorm (T n - L))
      l (𝓝 0) := by
    simpa using hconv.const_mul (R * Real.exp (R * C))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [eventually_traceNorm_le T L hT hL hconv,
    hlim.eventually (gt_mem_nhds hε)] with n hn hsmall z hz
  have hzR : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
  have hmax : max (traceNorm (T n)) (traceNorm L) ≤ C :=
    max_le hn (by dsimp [C]; linarith)
  have hle := hb L (T n) hL (hT n) z
  have he : Real.exp (‖z‖ * max (traceNorm (T n)) (traceNorm L)) ≤ Real.exp (R * C) :=
    Real.exp_le_exp.mpr (mul_le_mul hzR hmax
      ((TraceIdeals.TraceNormIdeal.traceNorm_nonneg L hL).trans (le_max_right _ _)) hR)
  have hmajor : ‖z‖ * traceNorm (T n - L) *
      Real.exp (‖z‖ * max (traceNorm (T n)) (traceNorm L)) ≤
      (R * Real.exp (R * C)) * traceNorm (T n - L) := by
    calc
      _ ≤ (R * traceNorm (T n - L)) * Real.exp (R * C) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hzR (hδ n)) he
          (Real.exp_pos _).le (mul_nonneg hR (hδ n))
      _ = _ := by ring
  rw [dist_comm, dist_eq_norm]
  exact (hle.trans hmajor).trans_lt hsmall

open TraceIdeals.TraceNormIdeal

/-- Right multiplication is bounded for the canonical trace norm, including
the zero Hilbert space (so only `norm_id_le`, not `norm_id = 1`, is used). -/
lemma traceNorm_comp_right_le (A B : H →L[ℂ] H) (hA : IsTraceClass A) :
    IsTraceClass (A.comp B) ∧ traceNorm (A.comp B) ≤ traceNorm A * ‖B‖ := by
  have h := two_sided_ideal ℂ H H H H A (ContinuousLinearMap.id ℂ H) B hA
  simp only [ContinuousLinearMap.id_comp] at h
  refine ⟨h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (traceNorm_nonneg A hA) ContinuousLinearMap.norm_id_le)
    (norm_nonneg B)

lemma traceNorm_comp_left_le (A B : H →L[ℂ] H) (hB : IsTraceClass B) :
    IsTraceClass (A.comp B) ∧ traceNorm (A.comp B) ≤ ‖A‖ * traceNorm B := by
  have h := two_sided_ideal ℂ H H H H B A (ContinuousLinearMap.id ℂ H) hB
  simp only [ContinuousLinearMap.comp_id] at h
  refine ⟨h.1, h.2.trans ?_⟩
  exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg A) (traceNorm_nonneg B hB))
    ContinuousLinearMap.norm_id_le

lemma tendsto_traceNorm_add {I : Type w} {l : Filter I}
    (S T : I → H →L[ℂ] H) (A B : H →L[ℂ] H)
    (hS : ∀ i, IsTraceClass (S i)) (hT : ∀ i, IsTraceClass (T i))
    (hA : IsTraceClass A) (hB : IsTraceClass B)
    (hs : Tendsto (fun i => traceNorm (S i - A)) l (𝓝 0))
    (ht : Tendsto (fun i => traceNorm (T i - B)) l (𝓝 0)) :
    Tendsto (fun i => traceNorm ((S i + T i) - (A + B))) l (𝓝 0) := by
  have hlim : Tendsto (fun i => traceNorm (S i - A) + traceNorm (T i - B)) l (𝓝 0) :=
    by simpa using hs.add ht
  apply squeeze_zero (fun i => traceNorm_nonneg _
    (traceClass_sub _ _ (traceClass_add _ _ (hS i) (hT i)).1
      (traceClass_add _ _ hA hB).1)) _ hlim
  intro i
  convert (traceClass_add (S i - A) (T i - B)
    (traceClass_sub _ _ (hS i) hA) (traceClass_sub _ _ (hT i) hB)).2 using 1
  congr 1
  abel

lemma tendsto_traceNorm_comp {I : Type w} {l : Filter I}
    (S T : I → H →L[ℂ] H) (A B : H →L[ℂ] H)
    (hS : ∀ i, IsTraceClass (S i)) (hT : ∀ i, IsTraceClass (T i))
    (hA : IsTraceClass A) (hB : IsTraceClass B)
    (hs : Tendsto (fun i => traceNorm (S i - A)) l (𝓝 0))
    (ht : Tendsto (fun i => traceNorm (T i - B)) l (𝓝 0)) :
    Tendsto (fun i => traceNorm ((S i).comp (T i) - A.comp B)) l (𝓝 0) := by
  have hlim : Tendsto
      (fun i => traceNorm (S i - A) * (traceNorm B + 1) + ‖A‖ * traceNorm (T i - B))
      l (𝓝 0) := by
    simpa using (hs.mul_const (traceNorm B + 1)).add (ht.const_mul ‖A‖)
  apply squeeze_zero' (Eventually.of_forall (fun i => traceNorm_nonneg _
    (traceClass_sub _ _ (traceNorm_comp_right_le _ _ (hS i)).1
      (traceNorm_comp_right_le _ _ hA).1))) _ hlim
  filter_upwards [eventually_traceNorm_le T B hT hB ht] with i hi
  have hD := traceClass_sub _ _ (hS i) hA
  have hE := traceClass_sub _ _ (hT i) hB
  have hdecomp : (S i).comp (T i) - A.comp B =
      (S i - A).comp (T i) + A.comp (T i - B) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, sub_apply, add_apply, map_sub]
    abel
  rw [hdecomp]
  calc
    _ ≤ traceNorm ((S i - A).comp (T i)) + traceNorm (A.comp (T i - B)) :=
      (traceClass_add _ _ (traceNorm_comp_right_le _ _ hD).1
        (traceNorm_comp_left_le _ _ hE).1).2
    _ ≤ traceNorm (S i - A) * ‖T i‖ + ‖A‖ * traceNorm (T i - B) :=
      add_le_add (traceNorm_comp_right_le _ _ hD).2 (traceNorm_comp_left_le _ _ hE).2
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
      ((opNorm_le_traceNorm _ (hT i)).trans hi) (traceNorm_nonneg _ hD)) le_rfl

/-- Finite-rank density gives a sequence in the exact shared trace norm. -/
lemma exists_finiteRank_approximation (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    ∃ F : ℕ → H →L[ℂ] H,
      (∀ n, FiniteDimensional ℂ (F n).range) ∧ (∀ n, IsTraceClass (F n)) ∧
      Tendsto (fun n => traceNorm (F n - T)) atTop (𝓝 0) := by
  have he (n : ℕ) := finite_rank_dense ℂ H H T hT (1 / ((n : ℝ) + 1)) (by positivity)
  choose F hfin hf hdiff herr using he
  refine ⟨F, hfin, hf, ?_⟩
  apply squeeze_zero (fun n => traceNorm_nonneg _ (traceClass_sub _ _ (hf n) hT)) _
    tendsto_one_div_add_atTop_nhds_zero_nat
  intro n
  have hn := (traceClass_neg (T - F n) (hdiff n)).2
  rw [neg_sub] at hn
  rw [hn]
  exact (herr n).le

/-- The final limit passage needs only the perturbation bound and the finite-rank
multiplicative identity. Neither input is silently postulated as a theorem. -/
lemma multiplicative_of_finiteRank
    (hb : Spec.DeterminantPerturbationBound.{v})
    (hfinite : ∀ (S T : H →L[ℂ] H), FiniteDimensional ℂ S.range →
      FiniteDimensional ℂ T.range →
      fredholmDeterminant (S + T + S.comp T) 1 =
        fredholmDeterminant S 1 * fredholmDeterminant T 1)
    (S T : H →L[ℂ] H) (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S + T + S.comp T) ∧
      fredholmDeterminant (S + T + S.comp T) 1 =
        fredholmDeterminant S 1 * fredholmDeterminant T 1 := by
  obtain ⟨F, hFfin, hF, hf⟩ := exists_finiteRank_approximation S hS
  obtain ⟨G, hGfin, hG, hg⟩ := exists_finiteRank_approximation T hT
  have hP : IsTraceClass (S + T + S.comp T) :=
    (traceClass_add _ _ (traceClass_add _ _ hS hT).1 (traceNorm_comp_right_le _ _ hS).1).1
  have hPn (n : ℕ) : IsTraceClass (F n + G n + (F n).comp (G n)) :=
    (traceClass_add _ _ (traceClass_add _ _ (hF n) (hG n)).1
      (traceNorm_comp_right_le _ _ (hF n)).1).1
  have hp := tendsto_traceNorm_add (fun n => F n + G n) (fun n => (F n).comp (G n))
    (S + T) (S.comp T) (fun n => (traceClass_add _ _ (hF n) (hG n)).1)
    (fun n => (traceNorm_comp_right_le _ _ (hF n)).1)
    (traceClass_add _ _ hS hT).1 (traceNorm_comp_right_le _ _ hS).1
    (tendsto_traceNorm_add F G S T hF hG hS hT hf hg)
    (tendsto_traceNorm_comp F G S T hF hG hS hT hf hg)
  have hu : Spec.TraceNormLocallyUniform.{v,0} := locally_uniform_of_parameter_bound (parameter_bound_of_bound_at_one hb)
  have h1 : (1 : ℂ) ∈ Metric.closedBall 0 1 := by simp
  have hpdet := (hu (H := H) atTop _ _ hPn hP hp 1 zero_le_one).tendsto_at h1
  have hfdet := (hu atTop F S hF hS hf 1 zero_le_one).tendsto_at h1
  have hgdet := (hu atTop G T hG hT hg 1 zero_le_one).tendsto_at h1
  refine ⟨hP, tendsto_nhds_unique hpdet ?_⟩
  convert hfdet.mul hgdet using 1
  funext n
  exact hfinite (F n) (G n) (hFfin n) (hGfin n)

/-- Uniform convergence on disks implies the usual topology-based notion of
locally uniform convergence, for arbitrary index filters. -/
lemma locallyUniform_of_disks {I : Type w} {l : Filter I}
    {F : I → ℂ → ℂ} {f : ℂ → ℂ}
    (h : ∀ R : ℝ, 0 ≤ R → TendstoUniformlyOn F f l (Metric.closedBall 0 R)) :
    TendstoLocallyUniformly F f l := by
  apply tendstoLocallyUniformly_of_forall_exists_nhds
  intro z
  refine ⟨Metric.closedBall 0 (‖z‖ + 1), ?_, h _ (by positivity)⟩
  exact Metric.closedBall_mem_nhds_of_mem (by simp)

/-! Polynomial dependence on an affine line is established from the actual
principal minors. In particular, it does not presuppose continuity of the
exterior functor in trace norm. -/

omit [CompleteSpace H] in
lemma principalMinor_affine_polynomial {ι : Type w} (b : HilbertBasis ι ℂ H)
    (S D : H →L[ℂ] H) (s : Finset ι) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ s.card ∧
      ∀ z : ℂ, p.eval z = principalMinor b (S + z • D) s := by
  classical
  let A : Matrix s s ℂ := fun i j => inner ℂ (b i.val) (D (b j.val))
  let B : Matrix s s ℂ := fun i j => inner ℂ (b i.val) (S (b j.val))
  let M : Matrix s s (Polynomial ℂ) := (Polynomial.X : Polynomial ℂ) • A.map Polynomial.C + B.map Polynomial.C
  refine ⟨M.det, ?_, ?_⟩
  · simpa [M] using Polynomial.natDegree_det_X_add_C_le A B
  · intro z
    change (Polynomial.evalRingHom z) M.det = _
    rw [RingHom.map_det]
    unfold principalMinor TraceClassDefinitions.Spec.PrincipalMinorValue
    congr 1
    ext i j
    change Polynomial.eval z (Polynomial.X * Polynomial.C (inner ℂ (b i.val) (D (b j.val))) +
      Polynomial.C (inner ℂ (b i.val) (S (b j.val)))) = _
    simp [inner_add_right, inner_smul_right, add_comm]
    exact mul_comm _ _

/-- Interpolation at n+1 distinct scalar nodes represents a degree-n principal
minor by the same finite family of scalar polynomials, independent of the minor. -/
lemma principalMinor_affine_interpolate {ι : Type w} (b : HilbertBasis ι ℂ H)
    (S D : H →L[ℂ] H) (n : ℕ) (s : Set.powersetCard ι n) (z : ℂ) :
    principalMinor b (S + z • D) s.val =
      ∑ j : Fin (n + 1), principalMinor b (S + (j.val : ℂ) • D) s.val *
        (Lagrange.basis Finset.univ (fun k : Fin (n + 1) => (k.val : ℂ)) j).eval z := by
  classical
  obtain ⟨p, hp, he⟩ := principalMinor_affine_polynomial b S D s.val
  have hinj : Set.InjOn (fun k : Fin (n + 1) => (k.val : ℂ)) ((Finset.univ : Finset (Fin (n + 1))) : Set (Fin (n + 1))) := by
    intro i _ j _ hij
    exact Fin.ext (Nat.cast_injective hij)
  have hdeg : p.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    apply (Polynomial.degree_le_natDegree).trans_lt
    simp only [Finset.card_univ, Fintype.card_fin]
    exact_mod_cast (hp.trans_lt (by simpa using Nat.lt_succ_self n))
  have hi := congrArg (Polynomial.eval z) (Lagrange.eq_interpolate hinj hdeg)
  simpa only [he, Lagrange.interpolate_apply, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C] using hi

/-- Each exterior coefficient is polynomial along every trace-class affine
line. Absolute convergence at the interpolation nodes justifies summation. -/
lemma exteriorTrace_affine_interpolate (S D : H →L[ℂ] H)
    (hS : IsTraceClass S) (hD : IsTraceClass D) (n : ℕ) (z : ℂ) :
    exteriorTrace (S + z • D) n =
      ∑ j : Fin (n + 1), exteriorTrace (S + (j.val : ℂ) • D) n *
        (Lagrange.basis Finset.univ (fun k : Fin (n + 1) => (k.val : ℂ)) j).eval z := by
  classical
  let b := TraceIdeals.TraceClassDefinitions.Spec.chosenBasis (𝕜 := ℂ) (H := H)
  have hs (j : Fin (n + 1)) :
      Summable (fun s : Set.powersetCard _ n =>
        principalMinor b (S + (j.val : ℂ) • D) s.val) :=
    (TraceClassDefinitions.principal_minor_traceNorm_bound _
      (traceClass_add _ _ hS (traceClass_smul _ _ hD).1).1 b n).1.of_norm
  change (∑' s : Set.powersetCard _ n, principalMinor b (S + z • D) s.val) = _
  trans ∑' s : Set.powersetCard _ n, ∑ j : Fin (n + 1),
    principalMinor b (S + (j.val : ℂ) • D) s.val *
      (Lagrange.basis Finset.univ (fun k : Fin (n + 1) => (k.val : ℂ)) j).eval z
  · apply tsum_congr
    intro s
    exact principalMinor_affine_interpolate b S D n s z
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    exact tsum_mul_right
  · intro j _
    exact (hs j).mul_right _

lemma exteriorTrace_affine_differentiable (S D : H →L[ℂ] H)
    (hS : IsTraceClass S) (hD : IsTraceClass D) (n : ℕ) :
    Differentiable ℂ (fun z : ℂ => exteriorTrace (S + z • D) n) := by
  have heq := funext (exteriorTrace_affine_interpolate S D hS hD n)
  rw [heq]
  apply Differentiable.fun_sum
  intro j _
  exact (Lagrange.basis Finset.univ
    (fun k : Fin (n + 1) => (k.val : ℂ)) j).differentiable.const_mul _

lemma traceNorm_add_smul_le (S D : H →L[ℂ] H)
    (hS : IsTraceClass S) (hD : IsTraceClass D) (z : ℂ) :
    traceNorm (S + z • D) ≤ traceNorm S + ‖z‖ * traceNorm D := by
  simpa only [(traceClass_smul z D hD).2] using
    (traceClass_add S (z • D) hS (traceClass_smul z D hD).1).2

/-- Holomorphy along trace-class affine lines, obtained independently of any
trace-norm continuity claim. -/
lemma determinant_affine_differentiable (S D : H →L[ℂ] H)
    (hS : IsTraceClass S) (hD : IsTraceClass D) :
    Differentiable ℂ (fun z : ℂ => fredholmDeterminant (S + z • D) 1) := by
  have heq : (fun z : ℂ => fredholmDeterminant (S + z • D) 1) =
      (fun z : ℂ => ∑' n : ℕ, exteriorTrace (S + z • D) n) := by
    funext z
    simp [fredholmDeterminant, TraceClassDefinitions.Spec.FredholmDeterminantValue]
  rw [heq]
  intro z
  let R : ℝ := ‖z‖ + 1
  let C : ℝ := traceNorm S + R * traceNorm D
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hC : 0 ≤ C := add_nonneg (traceNorm_nonneg S hS)
    (mul_nonneg hR (traceNorm_nonneg D hD))
  have hd : DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℕ, exteriorTrace (S + z • D) n)
      (Metric.ball 0 R) := by
    apply Complex.differentiableOn_tsum_of_summable_norm (Real.summable_pow_div_factorial C)
    · intro n
      exact (exteriorTrace_affine_differentiable S D hS hD n).differentiableOn
    · exact Metric.isOpen_ball
    · intro n w hw
      have hF := (traceClass_add _ _ hS (traceClass_smul w D hD).1).1
      have hwR : ‖w‖ ≤ R := (mem_ball_zero_iff.mp hw).le
      have hnorm : traceNorm (S + w • D) ≤ C :=
        (traceNorm_add_smul_le S D hS hD w).trans
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right hwR (traceNorm_nonneg D hD)))
      exact (TraceClassDefinitions.exterior_trace_factorial_bound _ hF n).trans
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ (traceNorm_nonneg _ hF) hnorm n)
          (Nat.cast_nonneg _))
  exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp [R]))

/-- Cauchy's estimate supplies a bound with one extra factor `exp 1`.
This bound is sufficient for continuity, but does not replace the sharp
perturbation estimate in the independent specification. -/
lemma determinant_affine_deriv_bound (S D : H →L[ℂ] H)
    (hS : IsTraceClass S) (hD : IsTraceClass D) (c : ℂ) :
    ‖deriv (fun z : ℂ => fredholmDeterminant (S + z • D) 1) c‖ ≤
      traceNorm D * Real.exp (traceNorm (S + c • D) + 1) := by
  have hδ := traceNorm_nonneg D hD
  by_cases hzero : traceNorm D = 0
  · have hDzero := (traceNorm_eq_zero_iff D hD).mp hzero
    subst D
    simp [hzero]
  have hpos : 0 < traceNorm D := lt_of_le_of_ne hδ (Ne.symm hzero)
  have hf := determinant_affine_differentiable S D hS hD
  have hF := (traceClass_add _ _ hS (traceClass_smul c D hD).1).1
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (c := c) (R := (traceNorm D)⁻¹) (C := Real.exp (traceNorm (S + c • D) + 1))
    (inv_pos.mpr hpos) hf.diffContOnCl ?_
  · simpa only [div_inv_eq_mul, mul_comm] using hcauchy
  · intro z hz
    have hzdist : ‖z - c‖ = (traceNorm D)⁻¹ := by
      simpa only [Metric.mem_sphere, dist_eq_norm] using hz
    have hdecomp : S + z • D = (S + c • D) + (z - c) • D := by
      rw [sub_smul]
      abel
    have hnorm : traceNorm (S + z • D) ≤ traceNorm (S + c • D) + 1 := by
      rw [hdecomp]
      simpa only [hzdist, inv_mul_cancel₀ hzero] using
        traceNorm_add_smul_le (S + c • D) D hF hD (z - c)
    have htz := (traceClass_add _ _ hS (traceClass_smul z D hD).1).1
    exact ((fredholm_series_bound _ htz 1).2.trans_eq (by simp)).trans
      (Real.exp_le_exp.mpr hnorm)

lemma traceNorm_segment_le (S T : H →L[ℂ] H)
    (hS : IsTraceClass S) (hT : IsTraceClass T) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    traceNorm (S + (t : ℂ) • (T - S)) ≤ max (traceNorm T) (traceNorm S) := by
  have hdecomp : S + (t : ℂ) • (T - S) =
      ((1 - t : ℝ) : ℂ) • S + (t : ℂ) • T := by
    simp only [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, smul_sub, one_smul]
    abel
  rw [hdecomp]
  have h := (traceClass_add _ _ (traceClass_smul ((1 - t : ℝ) : ℂ) S hS).1
    (traceClass_smul (t : ℂ) T hT).1).2
  rw [(traceClass_smul _ S hS).2, (traceClass_smul _ T hT).2] at h
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1,
    abs_of_nonneg (sub_nonneg.mpr ht.2)] at h
  refine h.trans ?_
  calc
    (1 - t) * traceNorm S + t * traceNorm T ≤
        (1 - t) * max (traceNorm T) (traceNorm S) +
        t * max (traceNorm T) (traceNorm S) :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left (le_max_left _ _) ht.1)
    _ = _ := by ring

/-- A proved, non-sharp perturbation estimate used only to obtain continuity.
The sharp estimate remains a separate target. -/
lemma determinant_perturbation_bound_cauchy (S T : H →L[ℂ] H)
    (hS : IsTraceClass S) (hT : IsTraceClass T) :
    ‖fredholmDeterminant T 1 - fredholmDeterminant S 1‖ ≤
      traceNorm (T - S) * Real.exp (max (traceNorm T) (traceNorm S) + 1) := by
  let f : ℂ → ℂ := fun z => fredholmDeterminant (S + z • (T - S)) 1
  have hD := traceClass_sub T S hT hS
  have hf := determinant_affine_differentiable S (T - S) hS hD
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => f (t : ℂ)) (deriv f (t : ℂ)) t :=
    (hf (t : ℂ)).hasDerivAt.comp_ofReal
  have hb (t : ℝ) (ht : t ∈ Set.Icc 0 1) : ‖deriv f (t : ℂ)‖ ≤
      traceNorm (T - S) * Real.exp (max (traceNorm T) (traceNorm S) + 1) :=
    (determinant_affine_deriv_bound S (T - S) hS hD (t : ℂ)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (add_le_add (traceNorm_segment_le S T hS hT ht) le_rfl))
        (traceNorm_nonneg _ hD))
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ Set.Icc (0 : ℝ) 1) => (hd t).hasDerivWithinAt)
    hb (convex_Icc 0 1) (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
    (by simp : (1 : ℝ) ∈ Set.Icc 0 1)
  simpa [f] using h

lemma parameter_perturbation_bound_cauchy (S T : H →L[ℂ] H)
    (hS : IsTraceClass S) (hT : IsTraceClass T) (z : ℂ) :
    ‖fredholmDeterminant T z - fredholmDeterminant S z‖ ≤
      ‖z‖ * traceNorm (T - S) *
        Real.exp (‖z‖ * max (traceNorm T) (traceNorm S) + 1) := by
  have hdiff := traceClass_sub T S hT hS
  have h := determinant_perturbation_bound_cauchy (z • S) (z • T)
    (traceClass_smul z S hS).1 (traceClass_smul z T hT).1
  simpa only [← smul_sub, (traceClass_smul z (T - S) hdiff).2,
    (traceClass_smul z T hT).2, (traceClass_smul z S hS).2,
    determinant_smul, one_mul, mul_max_of_nonneg _ _ (norm_nonneg z)] using h

theorem traceNorm_locally_uniform : Spec.TraceNormLocallyUniform.{v,w} := by
  intro H _ _ _ I l T L hT hL hconv R hR
  let C := traceNorm L + 1
  have hC : 0 ≤ C := by dsimp [C]; linarith [traceNorm_nonneg L hL]
  have hδ (n : I) : 0 ≤ traceNorm (T n - L) :=
    traceNorm_nonneg _ (traceClass_sub _ _ (hT n) hL)
  have hlim : Tendsto (fun n => (R * Real.exp (R * C + 1)) * traceNorm (T n - L))
      l (𝓝 0) := by
    simpa using hconv.const_mul (R * Real.exp (R * C + 1))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [eventually_traceNorm_le T L hT hL hconv,
    hlim.eventually (gt_mem_nhds hε)] with n hn hsmall z hz
  have hzR : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
  have hmax : max (traceNorm (T n)) (traceNorm L) ≤ C :=
    max_le hn (by dsimp [C]; linarith)
  have hle := parameter_perturbation_bound_cauchy L (T n) hL (hT n) z
  have he : Real.exp (‖z‖ * max (traceNorm (T n)) (traceNorm L) + 1) ≤
      Real.exp (R * C + 1) :=
    Real.exp_le_exp.mpr (add_le_add (mul_le_mul hzR hmax
      ((traceNorm_nonneg L hL).trans (le_max_right _ _)) hR) le_rfl)
  have hmajor : ‖z‖ * traceNorm (T n - L) *
      Real.exp (‖z‖ * max (traceNorm (T n)) (traceNorm L) + 1) ≤
      (R * Real.exp (R * C + 1)) * traceNorm (T n - L) := by
    calc
      _ ≤ (R * traceNorm (T n - L)) * Real.exp (R * C + 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hzR (hδ n)) he
          (Real.exp_pos _).le (mul_nonneg hR (hδ n))
      _ = _ := by ring
  rw [dist_comm, dist_eq_norm]
  exact (hle.trans hmajor).trans_lt hsmall

/-- The chosen-basis coefficient agrees with the principal-minor sum in every
Hilbert basis. Both sums are traces of the same completed exterior operator. -/
lemma exteriorTrace_eq_tsum_principalMinor (T : H →L[ℂ] H) (hT : IsTraceClass T)
    {ι : Type w} (b : HilbertBasis ι ℂ H) (n : ℕ) :
    exteriorTrace T n = ∑' s : Set.powersetCard ι n, principalMinor b T s.val := by
  classical
  let a := TraceIdeals.TraceClassDefinitions.Spec.chosenBasis (𝕜 := ℂ) (H := H)
  let A := exteriorOperator T n
  let c := ExteriorCoordinates.inducedBasis (n := n) a b
  have hA := exterior_construction T hT n
  have hn (x : Fin n → H) : A (TraceClassDefinitions.Spec.ExteriorCoordinates.wedgeAlternating a x) =
      TraceClassDefinitions.Spec.ExteriorCoordinates.wedgeAlternating a (T ∘ x) := hA.1 x
  have hd := TraceIdeals.TraceClassDefinitions.diagonal_trace ℂ _ A hA.2.1 _ c
  have heq (s : Set.powersetCard ι n) :
      inner ℂ (c s) (A (c s)) = principalMinor b T s.val := by
    dsimp only [c]
    rw [ExteriorCoordinates.inducedBasis_apply, hn, ExteriorCoordinates.inner_wedge]
    let e : Fin n ≃ s.val := (Finset.equivFinOfCardEq s.property).symm
    let M : Matrix s.val s.val ℂ := fun i j => inner ℂ (b i.val) (T (b j.val))
    change Matrix.det (M.submatrix e e) = Matrix.det M
    exact Matrix.det_submatrix_equiv_self e M
  exact hA.2.2.2.symm.trans (by simpa only [heq] using hd.2.tsum_eq.symm)

/-- In a finite Hilbert basis the shared exterior series is the usual matrix
determinant, at every scalar parameter, including dimension zero. -/
lemma determinant_eq_matrix_det {ι : Type w} [Fintype ι] (b : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (hT : IsTraceClass T) (z : ℂ) :
    fredholmDeterminant T z =
      Matrix.det (1 + z • Matrix.of (fun i j : ι => inner ℂ (b i) (T (b j)))) := by
  classical
  let M : Matrix ι ι ℂ := fun i j => inner ℂ (b i) (T (b j))
  let p : Polynomial ℂ := Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)
  have hc (n : ℕ) : p.coeff n = exteriorTrace T n := by
    letI : Fintype (Set.powersetCard ι n) := Fintype.ofFinite _
    rw [exteriorTrace_eq_tsum_principalMinor T hT b n, tsum_fintype]
    change (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)).coeff n = _
    rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
    exact Finset.sum_subtype _ (by intro s; simp) (fun s => principalMinor b T s)
  have hp : p.eval z = Matrix.det (1 + z • M) := by
    change (Polynomial.evalRingHom z) (Matrix.det _) = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    change Polynomial.eval z ((if i = j then 1 else 0) + Polynomial.X * Polynomial.C (M i j)) =
      (if i = j then 1 else 0) + z * M i j
    split_ifs <;> simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_zero]
  calc
    fredholmDeterminant T z = ∑' n : ℕ, z ^ n * p.coeff n := by
      unfold fredholmDeterminant TraceClassDefinitions.Spec.FredholmDeterminantValue
      simp only [hc]
    _ = ∑ n ∈ p.support, p.coeff n * z ^ n := by
      rw [tsum_eq_sum (s := p.support) (fun n hn => by
        rw [Polynomial.notMem_support_iff.mp hn, mul_zero])]
      apply Finset.sum_congr rfl
      intro n _
      exact mul_comm _ _
    _ = p.eval z := by rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    _ = _ := hp


lemma matrix_comp_hilbertBasis {ι : Type w} [Fintype ι] (b : HilbertBasis ι ℂ H)
    (S T : H →L[ℂ] H) :
    (Matrix.of (fun i j : ι => inner ℂ (b i) ((S.comp T) (b j)))) =
      (Matrix.of (fun i j : ι => inner ℂ (b i) (S (b j)))) *
      (Matrix.of (fun i j : ι => inner ℂ (b i) (T (b j)))) := by
  classical
  ext i j
  change inner ℂ (b i) (S (T (b j))) = ∑ k, _
  have hsum : (∑ k, inner ℂ (b k) (T (b j)) • b k) = T (b j) := by
    simpa using b.toOrthonormalBasis.sum_repr' (T (b j))
  rw [← hsum, map_sum, inner_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [map_smul, inner_smul_right, mul_comm, Matrix.of_apply]

lemma determinant_multiplicative_finiteBasis {ι : Type w} [Fintype ι]
    (b : HilbertBasis ι ℂ H) (S T : H →L[ℂ] H)
    (hS : IsTraceClass S) (hT : IsTraceClass T) :
    fredholmDeterminant (S + T + S.comp T) 1 =
      fredholmDeterminant S 1 * fredholmDeterminant T 1 := by
  classical
  have hP : IsTraceClass (S + T + S.comp T) := (traceClass_add _ _ (traceClass_add _ _ hS hT).1
    (traceNorm_comp_right_le S T hS).1).1
  rw [determinant_eq_matrix_det b _ hP, determinant_eq_matrix_det b S hS,
    determinant_eq_matrix_det b T hT]
  simp only [one_smul]
  rw [← Matrix.det_mul]
  congr 1
  have hcomp := matrix_comp_hilbertBasis b S T
  have hadd : (Matrix.of (fun i j : ι => inner ℂ (b i) ((S + T + S.comp T) (b j)))) =
    (Matrix.of (fun i j : ι => inner ℂ (b i) (S (b j)))) +
    (Matrix.of (fun i j : ι => inner ℂ (b i) (T (b j)))) +
    (Matrix.of (fun i j : ι => inner ℂ (b i) ((S.comp T) (b j)))) := by
    ext i j
    simp only [ContinuousLinearMap.add_apply, inner_add_right, Matrix.add_apply, Matrix.of_apply]
  rw [hadd, hcomp]
  simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one]
  abel

lemma determinant_multiplicative_finiteDimensional [FiniteDimensional ℂ H]
    (S T : H →L[ℂ] H) :
    fredholmDeterminant (S + T + S.comp T) 1 =
      fredholmDeterminant S 1 * fredholmDeterminant T 1 := by
  let b := stdOrthonormalBasis ℂ H
  exact determinant_multiplicative_finiteBasis b.toHilbertBasis S T
    (finite_rank_traceClass S) (finite_rank_traceClass T)
lemma multiplicative_of_finiteRank_continuity
   
    (hfinite : ∀ (S T : H →L[ℂ] H), FiniteDimensional ℂ S.range →
      FiniteDimensional ℂ T.range →
      fredholmDeterminant (S + T + S.comp T) 1 =
        fredholmDeterminant S 1 * fredholmDeterminant T 1)
    (S T : H →L[ℂ] H) (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S + T + S.comp T) ∧
      fredholmDeterminant (S + T + S.comp T) 1 =
        fredholmDeterminant S 1 * fredholmDeterminant T 1 := by
  obtain ⟨F, hFfin, hF, hf⟩ := exists_finiteRank_approximation S hS
  obtain ⟨G, hGfin, hG, hg⟩ := exists_finiteRank_approximation T hT
  have hP : IsTraceClass (S + T + S.comp T) :=
    (traceClass_add _ _ (traceClass_add _ _ hS hT).1 (traceNorm_comp_right_le _ _ hS).1).1
  have hPn (n : ℕ) : IsTraceClass (F n + G n + (F n).comp (G n)) :=
    (traceClass_add _ _ (traceClass_add _ _ (hF n) (hG n)).1
      (traceNorm_comp_right_le _ _ (hF n)).1).1
  have hp := tendsto_traceNorm_add (fun n => F n + G n) (fun n => (F n).comp (G n))
    (S + T) (S.comp T) (fun n => (traceClass_add _ _ (hF n) (hG n)).1)
    (fun n => (traceNorm_comp_right_le _ _ (hF n)).1)
    (traceClass_add _ _ hS hT).1 (traceNorm_comp_right_le _ _ hS).1
    (tendsto_traceNorm_add F G S T hF hG hS hT hf hg)
    (tendsto_traceNorm_comp F G S T hF hG hS hT hf hg)
  have hu : Spec.TraceNormLocallyUniform.{v,0} := traceNorm_locally_uniform
  have h1 : (1 : ℂ) ∈ Metric.closedBall 0 1 := by simp
  have hpdet := (hu (H := H) atTop _ _ hPn hP hp 1 zero_le_one).tendsto_at h1
  have hfdet := (hu atTop F S hF hS hf 1 zero_le_one).tendsto_at h1
  have hgdet := (hu atTop G T hG hT hg 1 zero_le_one).tendsto_at h1
  refine ⟨hP, tendsto_nhds_unique hpdet ?_⟩
  convert hfdet.mul hgdet using 1
  funext n
  exact hfinite (F n) (G n) (hFfin n) (hGfin n)


lemma tendsto_traceNorm_of_sub {I : Type w} {l : Filter I}
    (T : I → H →L[ℂ] H) (L : H →L[ℂ] H)
    (hT : ∀ i, IsTraceClass (T i)) (hL : IsTraceClass L)
    (h : Tendsto (fun i => traceNorm (T i - L)) l (𝓝 0)) :
    Tendsto (fun i => traceNorm (T i)) l (𝓝 (traceNorm L)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun i => norm_nonneg _) _ h
  intro i
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have hneg := (traceClass_neg (T i - L) (traceClass_sub _ _ (hT i) hL)).2
    rw [neg_sub] at hneg
    have hb := (traceClass_add (L - T i) (T i)
      (traceClass_sub _ _ hL (hT i)) (hT i)).2
    rw [sub_add_cancel, hneg] at hb
    linarith
  · have hb := (traceClass_add (T i - L) L
      (traceClass_sub _ _ (hT i) hL) hL).2
    rw [sub_add_cancel] at hb
    linarith

lemma perturbation_of_finiteRank
    (hfinite : ∀ (S T : H →L[ℂ] H), FiniteDimensional ℂ S.range →
      FiniteDimensional ℂ T.range →
      ‖fredholmDeterminant T 1 - fredholmDeterminant S 1‖ ≤
        traceNorm (T - S) * Real.exp (max (traceNorm T) (traceNorm S)))
    (S T : H →L[ℂ] H) (hS : IsTraceClass S) (hT : IsTraceClass T) :
    ‖fredholmDeterminant T 1 - fredholmDeterminant S 1‖ ≤
      traceNorm (T - S) * Real.exp (max (traceNorm T) (traceNorm S)) := by
  obtain ⟨F, hFfin, hF, hf⟩ := exists_finiteRank_approximation S hS
  obtain ⟨G, hGfin, hG, hg⟩ := exists_finiteRank_approximation T hT
  have h1 : (1 : ℂ) ∈ Metric.closedBall 0 1 := by simp
  have hfdet := (traceNorm_locally_uniform atTop F S hF hS hf 1 zero_le_one).tendsto_at h1
  have hgdet := (traceNorm_locally_uniform atTop G T hG hT hg 1 zero_le_one).tendsto_at h1
  have hd : Tendsto (fun n => traceNorm ((G n - F n) - (T - S))) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => traceNorm (G n - T) + traceNorm (F n - S)) atTop (𝓝 0) :=
      by simpa using hg.add hf
    apply squeeze_zero (fun n => traceNorm_nonneg _
      (traceClass_sub _ _ (traceClass_sub _ _ (hG n) (hF n)) (traceClass_sub _ _ hT hS))) _ hlim
    intro n
    have hn := (traceClass_neg (F n - S) (traceClass_sub _ _ (hF n) hS)).2
    have hb := (traceClass_add (G n - T) (-(F n - S))
      (traceClass_sub _ _ (hG n) hT) (traceClass_neg _ (traceClass_sub _ _ (hF n) hS)).1).2
    rw [hn] at hb
    convert hb using 1
    congr 1
    abel
  have hnorm := tendsto_traceNorm_of_sub (fun n => G n - F n) (T - S)
    (fun n => traceClass_sub _ _ (hG n) (hF n)) (traceClass_sub _ _ hT hS) hd
  have hfnorm := tendsto_traceNorm_of_sub F S hF hS hf
  have hgnorm := tendsto_traceNorm_of_sub G T hG hT hg
  exact le_of_tendsto_of_tendsto (hgdet.sub hfdet).norm
    (hnorm.mul (Real.continuous_exp.tendsto _ |>.comp (hgnorm.max hfnorm)))
    (Eventually.of_forall (fun n => hfinite (F n) (G n) (hFfin n) (hGfin n)))


lemma subspace_basis_extension (M : Submodule ℂ H) {ι : Type w} [Fintype ι]
    (a : OrthonormalBasis ι ℂ M) :
    ∃ (W : Set H) (b : HilbertBasis W ℂ H) (e : ι ↪ W),
      (∀ i, b (e i) = (a i : H)) ∧
      ∀ k, k ∉ Set.range e → ∀ x : M, inner ℂ (b k) (x : H) = 0 := by
  classical
  let v : ι → H := fun i => (a i : H)
  have hv : Orthonormal ℂ v := a.orthonormal.comp_linearIsometry M.subtypeₗᵢ
  obtain ⟨W,b,hW,hb⟩ := hv.toSubtypeRange.exists_hilbertBasis_extension
  let e : ι ↪ W := {
    toFun := fun i => ⟨v i, hW ⟨i, rfl⟩⟩
    inj' := fun i j hij => hv.linearIndependent.injective
      (show v i = v j from congrArg (fun k : W => (k : H)) hij) }
  have he (i : ι) : b (e i) = (a i : H) := congrFun hb (e i)
  refine ⟨W,b,e,he,?_⟩
  intro k hk x
  have hx := congrArg M.subtype (a.sum_repr' x)
  simp only [map_sum, map_smul] at hx
  change inner ℂ (b k) (M.subtype x) = 0
  rw [← hx, inner_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [inner_smul_right]
  change inner ℂ (a i) x * inner ℂ (b k) (a i : H) = 0
  rw [← he]
  have hki : k ≠ e i := fun h => hk ⟨i,h.symm⟩
  rw [b.orthonormal.inner_eq_zero hki, mul_zero]

lemma powersetCard_map_injective {ι κ : Type*} (e : ι ↪ κ) (n : ℕ) :
    Function.Injective (Set.powersetCard.map n e) := by
  intro s t h
  apply Subtype.ext
  exact Finset.map_injective e (congrArg Subtype.val h)

lemma powersetCard_mem_range {ι κ : Type*} [Fintype ι] (e : ι ↪ κ) (n : ℕ)
    (s : Set.powersetCard κ n) :
    s ∈ Set.range (Set.powersetCard.map n e) ↔ ∀ k ∈ s.val, k ∈ Set.range e := by
  classical
  constructor
  · rintro ⟨t,rfl⟩ k hk
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hk
    exact ⟨i,rfl⟩
  · intro hs
    let t : Finset ι := Finset.univ.filter (fun i => e i ∈ s.val)
    have ht : t.map e = s.val := by
      ext k
      simp only [Finset.mem_map, t, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i,hi,rfl⟩
        exact hi
      · intro hk
        obtain ⟨i,rfl⟩ := hs k hk
        exact ⟨i,hk,rfl⟩
    have hcard : t.card = n := by rw [← Finset.card_map e, ht]; exact s.property
    refine ⟨⟨t,hcard⟩,?_⟩
    apply Subtype.ext
    exact ht

lemma tsum_principal_restrict {ι κ : Type*} [Fintype ι] (e : ι ↪ κ) (n : ℕ)
    (f : Set.powersetCard κ n → ℂ)
    (hf : ∀ s, (∃ k ∈ s.val, k ∉ Set.range e) → f s = 0) :
    (∑' s : Set.powersetCard κ n, f s) =
      ∑' s : Set.powersetCard ι n, f (Set.powersetCard.map n e s) := by
  classical
  symm
  apply (powersetCard_map_injective e n).tsum_eq
  intro s hs
  apply (powersetCard_mem_range e n s).mpr
  intro k hk
  by_contra h
  exact hs (hf s ⟨k,hk,h⟩)



lemma principalMinor_compression (M : Submodule ℂ H) [CompleteSpace M]
    {ι κ : Type*} (a : HilbertBasis ι ℂ M) (b : HilbertBasis κ ℂ H)
    (e : ι ↪ κ) (he : ∀ i, b (e i) = (a i : H))
    (T : H →L[ℂ] H) (hT : ∀ x, T x ∈ M) (s : Finset ι) :
    principalMinor b T (s.map e) =
      principalMinor a ((T.codRestrict M hT).comp M.subtypeL) s := by
  classical
  let q := Finset.equivMap e s
  let N : Matrix (s.map e) (s.map e) ℂ :=
    fun i j => inner ℂ (b i.val) (T (b j.val))
  change N.det = _
  rw [← Matrix.det_submatrix_equiv_self q N]
  congr 1
  ext i j
  change inner ℂ (b (e i.val)) (T (b (e j.val))) = _
  rw [he, he]
  rfl

lemma principalMinor_off_subspace (M : Submodule ℂ H) {ι κ : Type*}
    (b : HilbertBasis κ ℂ H) (e : ι ↪ κ)
    (hb : ∀ k, k ∉ Set.range e → ∀ x : M, inner ℂ (b k) (x : H) = 0)
    (T : H →L[ℂ] H) (hT : ∀ x, T x ∈ M) (s : Finset κ)
    (hs : ∃ k ∈ s, k ∉ Set.range e) : principalMinor b T s = 0 := by
  classical
  obtain ⟨k,hk,hke⟩ := hs
  apply Matrix.det_eq_zero_of_row_eq_zero ⟨k,hk⟩
  intro j
  exact hb k hke ⟨T (b j.val), hT _⟩




lemma determinant_compression (M : Submodule ℂ H) [FiniteDimensional ℂ M]
    (T : H →L[ℂ] H) (hT : ∀ x, T x ∈ M) (z : ℂ) :
    fredholmDeterminant T z =
      fredholmDeterminant ((T.codRestrict M hT).comp M.subtypeL) z := by
  classical
  haveI : FiniteDimensional ℂ T.range := Submodule.finiteDimensional_of_le
    (show T.range ≤ M from by rintro _ ⟨x,rfl⟩; exact hT x)
  have ht : IsTraceClass T := finite_rank_traceClass T
  let U := (T.codRestrict M hT).comp M.subtypeL
  have hu : IsTraceClass U := finite_rank_traceClass U
  let a := stdOrthonormalBasis ℂ M
  obtain ⟨W,b,e,he,hb⟩ := subspace_basis_extension M a
  have he' (i) : b (e i) = (a.toHilbertBasis i : H) := by
    simpa only [OrthonormalBasis.coe_toHilbertBasis] using he i
  have hc (n : ℕ) : exteriorTrace T n = exteriorTrace U n := by
    rw [exteriorTrace_eq_tsum_principalMinor T ht b n,
      exteriorTrace_eq_tsum_principalMinor U hu a.toHilbertBasis n]
    rw [tsum_principal_restrict e n (fun s => principalMinor b T s.val)
      (fun s hs => principalMinor_off_subspace M b e hb T hT s.val hs)]
    apply tsum_congr
    intro s
    exact principalMinor_compression M a.toHilbertBasis b e he' T hT s.val
  unfold fredholmDeterminant ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.FredholmDeterminantValue
  exact tsum_congr (fun n => congrArg (fun x : ℂ => z ^ n * x) (hc n))


lemma finiteRank_multiplicative_of_finiteDimensional
    (hfd : ∀ (M : Submodule ℂ H) [FiniteDimensional ℂ M]
      (U V : M →L[ℂ] M),
      fredholmDeterminant (U + V + U.comp V) 1 =
        fredholmDeterminant U 1 * fredholmDeterminant V 1)
    (S T : H →L[ℂ] H) (hS : FiniteDimensional ℂ S.range)
    (hT : FiniteDimensional ℂ T.range) :
    fredholmDeterminant (S + T + S.comp T) 1 =
      fredholmDeterminant S 1 * fredholmDeterminant T 1 := by
  classical
  letI := hS
  letI := hT
  let M : Submodule ℂ H := S.range ⊔ T.range
  have hSM (x : H) : S x ∈ M :=
    (show S.range ≤ M from le_sup_left) ⟨x,rfl⟩
  have hTM (x : H) : T x ∈ M :=
    (show T.range ≤ M from le_sup_right) ⟨x,rfl⟩
  have hPM (x : H) : (S + T + S.comp T) x ∈ M :=
    M.add_mem (M.add_mem (hSM x) (hTM x)) (hSM (T x))
  let U := (S.codRestrict M hSM).comp M.subtypeL
  let V := (T.codRestrict M hTM).comp M.subtypeL
  have hcomp : (((S + T + S.comp T).codRestrict M hPM).comp M.subtypeL) =
      U + V + U.comp V := by
    ext x
    rfl
  rw [determinant_compression M _ hPM, determinant_compression M S hSM,
    determinant_compression M T hTM, hcomp]
  exact hfd M U V



/-- Finite-dimensional determinant multiplicativity passes to arbitrary
trace-class operators through the proved trace-norm continuity. -/
theorem determinant_multiplicative : Spec.DeterminantMultiplicative.{v} := by
  intro H _ _ _ S T hS hT
  have hfd (M : Submodule ℂ H) [FiniteDimensional ℂ M] (U V : M →L[ℂ] M) :
      fredholmDeterminant (U + V + U.comp V) 1 =
        fredholmDeterminant U 1 * fredholmDeterminant V 1 :=
    determinant_multiplicative_finiteDimensional U V
  have hfin (A B : H →L[ℂ] H) (hA : FiniteDimensional ℂ A.range)
      (hB : FiniteDimensional ℂ B.range) :
      fredholmDeterminant (A + B + A.comp B) 1 =
        fredholmDeterminant A 1 * fredholmDeterminant B 1 :=
    finiteRank_multiplicative_of_finiteDimensional hfd A B hA hB
  exact multiplicative_of_finiteRank_continuity hfin S T hS hT


/-! Finite nuclear expansions and the sharp derivative estimate. -/

lemma det_one_add_eq_sum_principalMinors {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (M : Matrix ι ι R) :
    (1 + M).det = ∑ s : Finset ι, (M.submatrix (fun i : s => i.val) (fun i : s => i.val)).det := by
  rw [add_comm]
  let D : (ι → R) [⋀^ι]→ₗ[R] R := Matrix.detRowAlternating
  change D ((fun i => M i) + (fun i => (1 : Matrix ι ι R) i)) = _
  rw [D.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  exact Matrix.det_piecewise_one_eq_submatrix_det M s

lemma weighted_gram_det_expansion {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [Fintype ι] [DecidableEq ι]
    (u v : ι → H) (c : ι → ℂ) :
    (1 + Matrix.of (fun i j => c i * inner ℂ (v i) (u j))).det =
      ∑ s : Finset ι, (∏ i ∈ s, c i) *
        (Matrix.of (fun i j : s => inner ℂ (v i.val) (u j.val))).det := by
  rw [det_one_add_eq_sum_principalMinors]
  apply Finset.sum_congr rfl
  intro s _
  change (Matrix.of (fun i j : s => c i.val * inner ℂ (v i.val) (u j.val))).det = _
  simpa only [Finset.prod_coe_sort, Matrix.of_apply] using Matrix.det_mul_column
    (fun i : s => c i.val) (Matrix.of (fun i j : s => inner ℂ (v i.val) (u j.val)))

lemma finite_nuclear_matrix_expansion {H ι β : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (b : HilbertBasis β ℂ H) (u v : ι → H) (c : ι → ℂ) :
    (1 + Matrix.of (fun i j => inner ℂ (b i)
      (∑ k, (c k * inner ℂ (v k) (b j)) • u k))).det =
      ∑ s : Finset ι, (∏ i ∈ s, c i) *
        (Matrix.of (fun i j : s => inner ℂ (v i.val) (u j.val))).det := by
  let A : Matrix β ι ℂ := fun i k => inner ℂ (b i) (u k)
  let B : Matrix ι β ℂ := fun k j => c k * inner ℂ (v k) (b j)
  have hAB : Matrix.of (fun i j => inner ℂ (b i)
      (∑ k, (c k * inner ℂ (v k) (b j)) • u k)) = A * B := by
    ext i j
    simp only [Matrix.of_apply, inner_sum, inner_smul_right, Matrix.mul_apply, A, B]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hBA : B * A = Matrix.of (fun i j => c i * inner ℂ (v i) (u j)) := by
    ext i j
    change (∑ k : β, (c i * inner ℂ (v i) (b k)) * inner ℂ (b k) (u j)) = _
    rw [show (∑ k : β, (c i * inner ℂ (v i) (b k)) * inner ℂ (b k) (u j)) =
      c i * ∑ k : β, inner ℂ (v i) (b k) * inner ℂ (b k) (u j) by rw [Finset.mul_sum]; congr 1; ext k; ring]
    have hs : (∑ k : β, inner ℂ (v i) (b k) * inner ℂ (b k) (u j)) = inner ℂ (v i) (u j) := by
      simpa only [tsum_fintype] using b.tsum_inner_mul_inner (v i) (u j)
    exact congrArg (fun w : ℂ => c i * w) hs
  rw [hAB, Matrix.det_one_add_mul_comm, hBA, weighted_gram_det_expansion]




lemma finite_nuclear_determinant_expansion {ι : Type*} [Fintype ι]
    (u v : ι → H) (c : ι → ℂ) (T : H →L[ℂ] H)
    (hexp : ∀ x, T x = ∑ k, (c k * inner ℂ (v k) x) • u k) :
    fredholmDeterminant T 1 = ∑ s : Finset ι, (∏ i ∈ s, c i) *
      (Matrix.of (fun i j : s => inner ℂ (v i.val) (u j.val))).det := by
  classical
  let M : Submodule ℂ H := Submodule.span ℂ (Set.range u)
  haveI : FiniteDimensional ℂ M := FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  have hu (i : ι) : u i ∈ M := Submodule.subset_span ⟨i,rfl⟩
  have hT (x : H) : T x ∈ M := by
    rw [hexp]
    exact M.sum_mem (fun i _ => M.smul_mem _ (hu i))
  let U := (T.codRestrict M hT).comp M.subtypeL
  let uM : ι → M := fun i => ⟨u i,hu i⟩
  let vM : ι → M := fun i => M.orthogonalProjectionOnto (v i)
  have heU (x : M) : U x = ∑ k, (c k * inner ℂ (vM k) x) • uM k := by
    apply Subtype.val_injective
    change T (x : H) = _
    simp only [Submodule.coe_sum, Submodule.coe_smul, uM, vM,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
    exact hexp x
  have hgram (i j : ι) : inner ℂ (vM i) (uM j) = inner ℂ (v i) (u j) := by
    simp only [vM, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right, uM]
  let b := (stdOrthonormalBasis ℂ M).toHilbertBasis
  rw [determinant_compression M T hT,
    determinant_eq_matrix_det b U (finite_rank_traceClass U) 1]
  simp only [one_smul]
  simp_rw [heU]
  convert (finite_nuclear_matrix_expansion b uM vM c) using 1
  · congr 1
    ext i j
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
    split_ifs <;> rfl
  · simp_rw [hgram]



lemma subset_product_hasDeriv {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c d : ι → ℝ) :
    HasDerivAt (fun z : ℂ => ∏ i ∈ s, ((c i : ℂ) + z * (d i : ℂ)))
      ((∑ i ∈ s, (∏ j ∈ s.erase i, c j) * d i : ℝ) : ℂ) 0 := by
  have h (i : ι) : HasDerivAt (fun z : ℂ => (c i : ℂ) + z * (d i : ℂ)) (d i : ℂ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (d i : ℂ)).const_add (c i : ℂ)
  convert HasDerivAt.fun_finsetProd (u := s) (fun i _ => h i) using 1
  · simp [Complex.ofReal_sum, Complex.ofReal_prod, smul_eq_mul]

lemma subset_polynomial_hasDeriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Finset ι → ℂ) (c d : ι → ℝ) :
    HasDerivAt (fun z : ℂ => ∑ s : Finset ι,
      a s * ∏ i ∈ s, ((c i : ℂ) + z * (d i : ℂ)))
      (∑ s : Finset ι, a s *
        ((∑ i ∈ s, (∏ j ∈ s.erase i, c j) * d i : ℝ) : ℂ)) 0 := by
  exact HasDerivAt.fun_sum (fun s _ => (subset_product_hasDeriv s c d).const_mul (a s))

lemma sum_subset_deriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c d : ι → ℝ) :
    (∑ s : Finset ι, ∑ i ∈ s, (∏ j ∈ s.erase i, c j) * d i) =
      ∑ i : ι, (∏ j ∈ Finset.univ.erase i, (1 + c j)) * d i := by
  have h1 := subset_polynomial_hasDeriv (fun _ : Finset ι => (1 : ℂ)) c d
  have h2 := subset_product_hasDeriv (Finset.univ : Finset ι) (fun i => 1 + c i) d
  have heq : (fun z : ℂ => ∑ s : Finset ι,
      (1 : ℂ) * ∏ i ∈ s, ((c i : ℂ) + z * (d i : ℂ))) =
      (fun z : ℂ => ∏ i : ι, (((1 + c i : ℝ) : ℂ) + z * (d i : ℂ))) := by
    funext z
    simp only [one_mul, Complex.ofReal_add, Complex.ofReal_one]
    simpa only [Finset.powerset_univ, add_assoc] using
      (Finset.prod_one_add (f := fun i => (c i : ℂ) + z * (d i : ℂ)) (Finset.univ : Finset ι)).symm
  rw [heq] at h1
  have hh := h1.unique h2
  norm_cast at hh
  simpa using hh

lemma subset_polynomial_deriv_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Finset ι → ℂ) (ha : ∀ s, ‖a s‖ ≤ 1)
    (c d : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i) :
    ‖deriv (fun z : ℂ => ∑ s : Finset ι,
      a s * ∏ i ∈ s, ((c i : ℂ) + z * (d i : ℂ))) 0‖ ≤
        (∑ i : ι, d i) * ∏ i : ι, (1 + c i) := by
  rw [(subset_polynomial_hasDeriv a c d).deriv]
  have hp (s : Finset ι) : 0 ≤ ∑ i ∈ s, (∏ j ∈ s.erase i, c j) * d i := by
    exact Finset.sum_nonneg (fun i _ => mul_nonneg
      (Finset.prod_nonneg (fun j _ => hc j)) (hd i))
  calc
    _ ≤ ∑ s : Finset ι, ‖a s *
        ((∑ i ∈ s, (∏ j ∈ s.erase i, c j) * d i : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ s : Finset ι, ∑ i ∈ s, (∏ j ∈ s.erase i, c j) * d i := by
      apply Finset.sum_le_sum
      intro s _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp s)]
      exact mul_le_of_le_one_left (hp s) (ha s)
    _ = ∑ i : ι, (∏ j ∈ Finset.univ.erase i, (1 + c j)) * d i := sum_subset_deriv c d
    _ ≤ ∑ i : ι, (∏ j : ι, (1 + c j)) * d i := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (hd i)
      have hp' : 0 ≤ ∏ j ∈ Finset.univ.erase i, (1 + c j) :=
        Finset.prod_nonneg (fun j _ => by linarith [hc j])
      calc
        _ ≤ (1 + c i) * (∏ j ∈ Finset.univ.erase i, (1 + c j)) := by
          nlinarith [hc i]
        _ = _ := Finset.mul_prod_erase (Finset.univ : Finset ι) (fun j => (1 + c j)) (Finset.mem_univ i)
    _ = _ := by rw [← Finset.mul_sum]; ring


lemma finiteRank_deriv_bound (S D : H →L[ℂ] H) (hS : IsTraceClass S) (hD : IsTraceClass D)
    (hSF : FiniteDimensional ℂ S.range) (hDF : FiniteDimensional ℂ D.range) :
    ‖deriv (fun z : ℂ => fredholmDeterminant (S + z • D) 1) 0‖ ≤
      traceNorm D * Real.exp (traceNorm S) := by
  classical
  obtain ⟨A⟩ := CompactSpectral.SingularExpansion.compact_singular_system ℂ H H S hS.1
  obtain ⟨B⟩ := CompactSpectral.SingularExpansion.compact_singular_system ℂ H H D hD.1
  letI : Finite A.Index := A.finite_rank hSF
  letI : Finite B.Index := B.finite_rank hDF
  letI : Fintype A.Index := Fintype.ofFinite _
  letI : Fintype B.Index := Fintype.ofFinite _
  letI : DecidableEq (A.Index ⊕ B.Index) := Classical.decEq _
  let u : A.Index ⊕ B.Index → H := Sum.elim A.leftVector B.leftVector
  let v : A.Index ⊕ B.Index → H := Sum.elim A.rightVector B.rightVector
  let c : A.Index ⊕ B.Index → ℝ := Sum.elim A.sigma (fun _ => 0)
  let d : A.Index ⊕ B.Index → ℝ := Sum.elim (fun _ => 0) B.sigma
  let a : Finset (A.Index ⊕ B.Index) → ℂ := fun s =>
    (Matrix.of (fun i j : s => inner ℂ (v i.val) (u j.val))).det
  have hu (i) : ‖u i‖ = 1 := by
    cases i with
    | inl i => exact A.left_orthonormal.norm_eq_one i
    | inr i => exact B.left_orthonormal.norm_eq_one i
  have hv (i) : ‖v i‖ = 1 := by
    cases i with
    | inl i => exact A.right_orthonormal.norm_eq_one i
    | inr i => exact B.right_orthonormal.norm_eq_one i
  have ha (s) : ‖a s‖ ≤ 1 := by
    change ‖Matrix.det (fun i j : s => inner ℂ (v i.val) (u j.val))‖ ≤ 1
    have hh := GramDeterminant.norm_det_mixedGram_le' (𝕜 := ℂ)
      (fun i : s => v i.val) (fun i : s => u i.val)
    simpa only [hv, hu, one_mul, Finset.prod_const_one] using hh
  have hc (i) : 0 ≤ c i := by
    cases i with
    | inl i => exact (A.positive i).le
    | inr i => exact le_rfl
  have hd (i) : 0 ≤ d i := by
    cases i with
    | inl i => exact le_rfl
    | inr i => exact (B.positive i).le
  have hsa : (∑ i : A.Index, A.sigma i) = traceNorm S := by
    simpa only [tsum_fintype] using (singularSystem_sum ℂ H H S hS A).2
  have hsb : (∑ i : B.Index, B.sigma i) = traceNorm D := by
    simpa only [tsum_fintype] using (singularSystem_sum ℂ H H D hD B).2
  have hcs : (∑ i, c i) = traceNorm S := by
    simpa only [Fintype.sum_sum_type, c, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, add_zero] using hsa
  have hds : (∑ i, d i) = traceNorm D := by
    simpa only [Fintype.sum_sum_type, d, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, zero_add] using hsb
  have hexp (z : ℂ) (x : H) :
      (S + z • D) x = ∑ k, (((c k : ℂ) + z * (d k : ℂ)) * inner ℂ (v k) x) • u k := by
    have heA : S x = ∑ k : A.Index, ((A.sigma k : ℂ) * inner ℂ (A.rightVector k) x) • A.leftVector k := by
      exact (A.expansion x).unique (hasSum_fintype _)
    have heB : D x = ∑ k : B.Index, ((B.sigma k : ℂ) * inner ℂ (B.rightVector k) x) • B.leftVector k := by
      exact (B.expansion x).unique (hasSum_fintype _)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, heA, heB,
      Fintype.sum_sum_type, c, d, u, v, Sum.elim_inl, Sum.elim_inr, Complex.ofReal_zero,
      mul_zero, add_zero, zero_add, Finset.smul_sum, smul_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  have heq : (fun z : ℂ => fredholmDeterminant (S + z • D) 1) =
      (fun z : ℂ => ∑ s, a s * ∏ i ∈ s, ((c i : ℂ) + z * (d i : ℂ))) := by
    funext z
    rw [finite_nuclear_determinant_expansion u v
      (fun k => (c k : ℂ) + z * (d k : ℂ)) (S + z • D) (hexp z)]
    apply Finset.sum_congr rfl
    intro s _
    change _ = (Matrix.of (fun i j : s => inner ℂ (v i.val) (u j.val))).det * _
    exact mul_comm (∏ i ∈ s, ((c i : ℂ) + z * (d i : ℂ)))
      (Matrix.of (fun i j : s => inner ℂ (v i.val) (u j.val))).det
  rw [heq]
  have hb := subset_polynomial_deriv_bound a ha c d hc hd
  refine hb.trans ?_
  rw [hds]
  apply mul_le_mul_of_nonneg_left _ (traceNorm_nonneg D hD)
  calc
    _ ≤ ∏ i, Real.exp (c i) := Finset.prod_le_prod₀
      (fun i _ => by linarith [hc i]) (fun i _ => by simpa [add_comm] using Real.add_one_le_exp (c i))
    _ = Real.exp (∑ i, c i) := (Real.exp_sum _ _).symm
    _ = _ := by rw [hcs]


lemma finiteDimensional_range_add_smul (S D : H →L[ℂ] H)
    (hS : FiniteDimensional ℂ S.range) (hD : FiniteDimensional ℂ D.range) (c : ℂ) :
    FiniteDimensional ℂ (S + c • D).range := by
  letI := hS
  letI := hD
  apply Submodule.finiteDimensional_of_le (S₂ := S.range ⊔ D.range)
  rintro _ ⟨x, rfl⟩
  exact (S.range ⊔ D.range).add_mem
    ((show S.range ≤ S.range ⊔ D.range from le_sup_left) ⟨x, rfl⟩)
    ((S.range ⊔ D.range).smul_mem c
      ((show D.range ≤ S.range ⊔ D.range from le_sup_right) ⟨x, rfl⟩))

lemma finiteRank_affine_deriv_bound_of_zero
    (hb : ∀ (A B : H →L[ℂ] H), FiniteDimensional ℂ A.range →
      FiniteDimensional ℂ B.range →
      ‖deriv (fun z : ℂ => fredholmDeterminant (A + z • B) 1) 0‖ ≤
        traceNorm B * Real.exp (traceNorm A))
    (S D : H →L[ℂ] H) (hS : FiniteDimensional ℂ S.range)
    (hD : FiniteDimensional ℂ D.range) (c : ℂ) :
    ‖deriv (fun z : ℂ => fredholmDeterminant (S + z • D) 1) c‖ ≤
      traceNorm D * Real.exp (traceNorm (S + c • D)) := by
  have hF := finiteDimensional_range_add_smul S D hS hD c
  have heq : (fun z : ℂ => fredholmDeterminant ((S + c • D) + z • D) 1) =
      (fun z : ℂ => fredholmDeterminant (S + (c + z) • D) 1) := by
    funext z
    congr 1
    rw [add_smul]
    abel
  have h := hb (S + c • D) D hF hD
  rw [heq] at h
  rw [deriv_comp_const_add (fun z => fredholmDeterminant (S + z • D) 1) c 0] at h
  simpa only [add_zero] using h

lemma finiteRank_perturbation_of_derivative_bound
    (hb : ∀ (A B : H →L[ℂ] H), FiniteDimensional ℂ A.range →
      FiniteDimensional ℂ B.range →
      ‖deriv (fun z : ℂ => fredholmDeterminant (A + z • B) 1) 0‖ ≤
        traceNorm B * Real.exp (traceNorm A))
    (S T : H →L[ℂ] H) (hSF : FiniteDimensional ℂ S.range)
    (hTF : FiniteDimensional ℂ T.range) :
    ‖fredholmDeterminant T 1 - fredholmDeterminant S 1‖ ≤
      traceNorm (T - S) * Real.exp (max (traceNorm T) (traceNorm S)) := by
  letI := hSF
  letI := hTF
  have hS : IsTraceClass S := finite_rank_traceClass S
  have hT : IsTraceClass T := finite_rank_traceClass T
  have hDF : FiniteDimensional ℂ (T - S).range := by
    have h := finiteDimensional_range_add_smul T S hTF hSF (-1)
    have heq : T + (-1 : ℂ) • S = T - S := by simp only [neg_one_smul, sub_eq_add_neg]
    rw [heq] at h
    exact h
  let f : ℂ → ℂ := fun z => fredholmDeterminant (S + z • (T - S)) 1
  have hD := traceClass_sub T S hT hS
  have hf := determinant_affine_differentiable S (T - S) hS hD
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => f (t : ℂ)) (deriv f (t : ℂ)) t :=
    (hf (t : ℂ)).hasDerivAt.comp_ofReal
  have hb' (t : ℝ) (ht : t ∈ Set.Icc 0 1) : ‖deriv f (t : ℂ)‖ ≤
      traceNorm (T - S) * Real.exp (max (traceNorm T) (traceNorm S)) :=
    (finiteRank_affine_deriv_bound_of_zero hb S (T - S) hSF hDF (t : ℂ)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (traceNorm_segment_le S T hS hT ht)) (traceNorm_nonneg _ hD))
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ Set.Icc (0 : ℝ) 1) => (hd t).hasDerivWithinAt)
    hb' (convex_Icc 0 1) (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
    (by simp : (1 : ℝ) ∈ Set.Icc 0 1)
  simpa [f] using h


/-- The sharp perturbation estimate follows from the finite singular
expansions and passage to the limit in the canonical trace norm. -/
theorem determinant_perturbation_bound : Spec.DeterminantPerturbationBound.{v} := by
  intro H _ _ _ S T hS hT
  have hb (A B : H →L[ℂ] H) (hA : FiniteDimensional ℂ A.range)
      (hB : FiniteDimensional ℂ B.range) :
      ‖deriv (fun z : ℂ => fredholmDeterminant (A + z • B) 1) 0‖ ≤
        traceNorm B * Real.exp (traceNorm A) := by
    letI := hA
    letI := hB
    exact finiteRank_deriv_bound A B (finite_rank_traceClass A) (finite_rank_traceClass B) hA hB
  have hfin (A B : H →L[ℂ] H) (hA : FiniteDimensional ℂ A.range)
      (hB : FiniteDimensional ℂ B.range) :
      ‖fredholmDeterminant B 1 - fredholmDeterminant A 1‖ ≤
        traceNorm (B - A) * Real.exp (max (traceNorm B) (traceNorm A)) :=
    finiteRank_perturbation_of_derivative_bound hb A B hA hB
  exact perturbation_of_finiteRank hfin S T hS hT

theorem parameter_perturbation_bound : Spec.ParameterPerturbationBound.{v} :=
  parameter_bound_of_bound_at_one determinant_perturbation_bound

/-- Diskwise uniform convergence gives the usual locally uniform convergence
on the whole parameter plane, for arbitrary index filters. -/
theorem determinant_tendstoLocallyUniformly {I : Type w} {l : Filter I}
    (T : I → H →L[ℂ] H) (L : H →L[ℂ] H)
    (hT : ∀ i, IsTraceClass (T i)) (hL : IsTraceClass L)
    (hconv : Tendsto (fun i => traceNorm (T i - L)) l (𝓝 0)) :
    TendstoLocallyUniformly (fun i => fredholmDeterminant (T i))
      (fredholmDeterminant L) l :=
  locallyUniform_of_disks (traceNorm_locally_uniform l T L hT hL hconv)

end ExpandedFA.FredholmDeterminant.TraceDeterminantContinuity
