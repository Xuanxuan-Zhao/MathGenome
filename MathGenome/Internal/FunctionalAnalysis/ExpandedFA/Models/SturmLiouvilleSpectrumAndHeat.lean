import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.SturmLiouvilleSpectrumAndHeat
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.SturmLiouvillePeriodic
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.CompactNormalClassification
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.SemigroupGrowthAndGenerator

set_option maxHeartbeats 1500000
noncomputable section
open Set Filter Topology
open scoped InnerProductSpace NNReal
namespace ExpandedFA.Models.SturmLiouvilleSpectrumAndHeat
open Unbounded Semigroups SturmLiouvilleDirichlet

section Abstract
variable {𝕜 H : Type} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- An everywhere defined positive shifted inverse. These are proof inputs
only for the abstract lemma; the model theorem constructs them upstream. -/
theorem spectrum_of_shifted_inverse (A : Operator 𝕜 H H) (σ : ℝ)
    (S : H →L[𝕜] H) (hc : IsCompactOperator S) (hs : IsSelfAdjoint S)
    (hpos : ∀ x, 0 ≤ RCLike.re (inner 𝕜 x (S x)))
    (hm : ∀ x, S x ∈ A.domain)
    (hr : ∀ x, A ⟨S x, hm x⟩ + (σ : 𝕜) • S x = x)
    (hl : ∀ x : A.domain, S (A x + (σ : 𝕜) • (x : H)) = (x : H))
    (ha : A.IsFormalAdjoint A) : Nonempty (SpectralResolution A) := by
  have hinj : Function.Injective S := by
    apply (injective_iff_map_eq_zero S).mpr
    intro x hx
    have hz : (⟨S x, hm x⟩ : A.domain) = 0 := Subtype.ext hx
    have hh := hr x
    rw [hz, A.map_zero, hx, smul_zero, add_zero] at hh
    exact hh.symm
  have hker : S.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  obtain ⟨I, hI, e, μ, he, heig, hspan, _, _, hfinite, haway⟩ :=
    CompactSpectral.CompactNormalClassification.selfAdjoint_expansion 𝕜 H S hs
      ((Compactness.compact_iff_isCompactOperator S.toLinearMap).mpr hc)
  have hμ (i : I) : 0 < μ i := by
    have hp := hpos (e i)
    rw [(heig i).2, inner_smul_right] at hp
    simp only [inner_self_eq_norm_sq_to_K, he.1 i, RCLike.ofReal_one, one_pow,
      mul_one, RCLike.ofReal_re] at hp
    exact lt_of_le_of_ne hp (Ne.symm (heig i).1)
  have hdense : (Submodule.span 𝕜 (range e)).topologicalClosure = ⊤ := by
    simpa [hker] using hspan
  let B : HilbertBasis I 𝕜 H := HilbertBasis.mk he (by rw [hdense])
  have hB : (B : I → H) = e := HilbertBasis.coe_mk he _
  have hmB (i : I) : B i ∈ A.domain := by
    have hh := A.domain.smul_mem ((μ i : 𝕜)⁻¹) (hm (e i))
    rw [(heig i).2, smul_smul, inv_mul_cancel₀ (RCLike.ofReal_ne_zero.mpr (hμ i).ne'), one_smul] at hh
    simpa only [hB] using hh
  have haction (i : I) : A ⟨B i, hmB i⟩ = (((μ i)⁻¹ - σ : ℝ) : 𝕜) • B i := by
    have hh := hr (B i)
    have hSe : S (B i) = (μ i : 𝕜) • B i := by simpa only [hB] using (heig i).2
    have hsub : (⟨S (B i), hm (B i)⟩ : A.domain) = (μ i : 𝕜) • ⟨B i, hmB i⟩ := Subtype.ext hSe
    rw [hsub, A.map_smul, hSe, smul_smul] at hh
    have hh' : (μ i : 𝕜) • (A ⟨B i, hmB i⟩ + (σ : 𝕜) • B i) = B i := by
      simpa only [smul_add, smul_smul, mul_comm] using hh
    have heq := congrArg (fun x : H => (μ i : 𝕜)⁻¹ • x) hh'
    rw [smul_smul, inv_mul_cancel₀ (RCLike.ofReal_ne_zero.mpr (hμ i).ne'), one_smul] at heq
    have hval : A ⟨B i, hmB i⟩ = ((μ i : 𝕜)⁻¹ - (σ : 𝕜)) • B i := by
      rw [sub_smul, eq_sub_iff_add_eq]
      exact heq
    simpa only [RCLike.ofReal_sub, RCLike.ofReal_inv] using hval
  have hfiniteBelow (R : ℝ) : {i | (μ i)⁻¹ - σ ≤ R}.Finite := by
    by_cases hR : 0 < R + σ
    · apply (haway (R + σ)⁻¹ (inv_pos.mpr hR)).subset
      intro i hi
      change (μ i)⁻¹ - σ ≤ R at hi
      change (R + σ)⁻¹ ≤ |μ i|
      rw [abs_of_pos (hμ i)]
      exact (inv_le_comm₀ hR (hμ i)).mpr (by linarith [hi])
    · have hempty : {i | (μ i)⁻¹ - σ ≤ R} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hp := inv_pos.mpr (hμ i)
        change (μ i)⁻¹ - σ ≤ R at hi
        linarith
      rw [hempty]; exact finite_empty
  have hreal (z : 𝕜) (u : A.domain) (hu : (u : H) ≠ 0)
      (hz : A u = z • (u : H)) : ∃ r : ℝ, z = (r : 𝕜) := by
    have hh := ha u u
    rw [hz, inner_smul_left, inner_smul_right] at hh
    have hn : inner 𝕜 (u : H) (u : H) ≠ 0 := inner_self_ne_zero.mpr hu
    have hconj : starRingEnd 𝕜 z = z := mul_right_cancel₀ hn hh
    exact ⟨RCLike.re z, (RCLike.conj_eq_iff_re.mp hconj).symm⟩
  have hmult (z : 𝕜) : FiniteDimensional 𝕜 (eigenspace A z) := by
    by_cases hz : z + (σ : 𝕜) = 0
    · have hbot : eigenspace A z = ⊥ := by
        apply bot_unique
        intro u hu
        change A u - z • (u : H) = 0 at hu
        have hh := hl u
        rw [sub_eq_zero.mp hu, ← add_smul, hz, zero_smul, map_zero] at hh
        exact Subtype.ext hh.symm
      rw [hbot]; infer_instance
    · let f : eigenspace A z →ₗ[𝕜] Module.End.eigenspace S.toLinearMap (z + (σ : 𝕜))⁻¹ :=
        { toFun := fun u => ⟨(u.val : H), by
            rw [Module.End.mem_eigenspace_iff]
            change S (u.val : H) = _
            have hu := u.property
            change A u.val - z • (u.val : H) = 0 at hu
            have hh := hl u.val
            rw [sub_eq_zero.mp hu, ← add_smul, map_smul] at hh
            have heq := congrArg (fun x : H => (z + (σ : 𝕜))⁻¹ • x) hh
            simpa only [smul_smul, inv_mul_cancel₀ hz, one_smul] using heq⟩
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      letI := hfinite (z + (σ : 𝕜))⁻¹ (inv_ne_zero hz)
      exact FiniteDimensional.of_injective f (by
        intro x y h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun v : Module.End.eigenspace S.toLinearMap (z + (σ : 𝕜))⁻¹ => (v : H)) h)
  refine ⟨⟨I, hI, B, (fun i => (μ i)⁻¹ - σ), hmB, ?_, ?_, hfiniteBelow, hreal, hmult⟩⟩
  · intro i
    exact haction i
  · exact ⟨-σ, fun i => by have hp := inv_pos.mpr (hμ i); linarith⟩

/-- Finiteness of lower spectral sections is precisely escape to +∞,
with each basis vector counted separately. -/
theorem SpectralResolution.eigenvalues_tendsto (A : Operator 𝕜 H H) (D : SpectralResolution A) :
    Tendsto D.eigenvalue cofinite atTop := by
  apply tendsto_atTop.mpr
  intro R
  filter_upwards [(D.finite_below R).compl_mem_cofinite] with i hi
  change ¬ D.eigenvalue i ≤ R at hi
  exact (lt_of_not_ge hi).le

end Abstract

theorem spectrum : Spec.Spectrum := by
  intro 𝕜 _ a b c A hA
  rcases hA with hA | hA
  · have heq := SturmLiouvilleDirichlet.formRealization_unique c hA
      (dirichletOperator_formRealization c)
    subst A
    refine spectrum_of_shifted_inverse (𝕜 := 𝕜) (H := L2 𝕜 a b) (dirichletOperator (𝕜 := 𝕜) c) (formShift (𝕜 := 𝕜) c)
      (shiftedSolution c) (shiftedSolution_compact c) ?_ ?_
      (shiftedSolution_mem (𝕜 := 𝕜) c) (shiftedSolution_solve (𝕜 := 𝕜) c) ?_
      (dirichletOperator_formalAdjoint (𝕜 := 𝕜) c)
    · simpa only [shiftedSolution, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp] using
        (IsSelfAdjoint.one _ : IsSelfAdjoint (ContinuousLinearMap.id 𝕜 (DirichletEnergy 𝕜 c))).conj_adjoint
          (DirichletEnergy.inclusion c)
    · intro x
      change 0 ≤ RCLike.re (inner 𝕜 x (DirichletEnergy.inclusion c ((DirichletEnergy.inclusion c).adjoint x)))
      rw [← ContinuousLinearMap.adjoint_inner_left]
      exact inner_self_nonneg
    · intro u
      have hh := (dirichletResolvent c).left_inverse u
      change -shiftedSolution c (-(formShift (𝕜 := 𝕜) c : 𝕜) • (u : L2 𝕜 a b) - dirichletOperator c u) = _ at hh
      simpa only [neg_smul, sub_eq_add_neg, ← neg_add, map_neg, neg_neg, add_comm] using hh
  · have heq := SturmLiouvillePeriodic.formRealization_unique c hA
      (SturmLiouvillePeriodic.periodicOperator_formRealization c)
    subst A
    open SturmLiouvillePeriodic in
      refine spectrum_of_shifted_inverse (𝕜 := 𝕜) (H := L2 𝕜 a b) (periodicOperator (𝕜 := 𝕜) c) (formShift (𝕜 := 𝕜) c)
        (periodicShiftedSolution c) (periodicShiftedSolution_compact c) ?_ ?_
        (periodicShiftedSolution_mem (𝕜 := 𝕜) c) (periodicShiftedSolution_solve (𝕜 := 𝕜) c) ?_
        (periodicOperator_formalAdjoint (𝕜 := 𝕜) c)
    · simpa only [SturmLiouvillePeriodic.periodicShiftedSolution, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp] using
        (IsSelfAdjoint.one _ : IsSelfAdjoint (ContinuousLinearMap.id 𝕜 (SturmLiouvillePeriodic.PeriodicEnergy 𝕜 c))).conj_adjoint
          (SturmLiouvillePeriodic.PeriodicEnergy.inclusion c)
    · intro x
      change 0 ≤ RCLike.re (inner 𝕜 x (SturmLiouvillePeriodic.PeriodicEnergy.inclusion c
        ((SturmLiouvillePeriodic.PeriodicEnergy.inclusion c).adjoint x)))
      rw [← ContinuousLinearMap.adjoint_inner_left]
      exact inner_self_nonneg
    · intro u
      have hh := (SturmLiouvillePeriodic.periodicResolvent c).left_inverse u
      change -SturmLiouvillePeriodic.periodicShiftedSolution c (-(formShift (𝕜 := 𝕜) c : 𝕜) • (u : L2 𝕜 a b) - SturmLiouvillePeriodic.periodicOperator c u) = _ at hh
      simpa only [neg_smul, sub_eq_add_neg, ← neg_add, map_neg, neg_neg, add_comm] using hh


namespace DiagonalHeat
variable {I 𝕜 H : Type} [RCLike 𝕜] [NormedAddCommGroup H]
 [InnerProductSpace 𝕜 H] [CompleteSpace H]
/-- A bounded diagonal multiplier transported from ℓ² by the given basis. -/
def diag (B : HilbertBasis I 𝕜 H) (m : I → 𝕜) (K : ℝ) (hK : 0 ≤ K)
 (hm : ∀ i, ‖m i‖ ≤ K) : H →L[𝕜] H :=
 B.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
 ((lp.mapCLM 2 (fun i => m i • ContinuousLinearMap.id 𝕜 𝕜) hK
   (fun i => by simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using hm i)).comp B.repr.toContinuousLinearEquiv.toContinuousLinearMap)

lemma diag_repr (B : HilbertBasis I 𝕜 H) (m : I → 𝕜) (K : ℝ) (hK : 0 ≤ K)
 (hm : ∀ i, ‖m i‖ ≤ K) (x : H) (i : I) :
 B.repr (diag B m K hK hm x) i = m i * B.repr x i := by
 simp [diag, lp.mapCLM]

lemma diag_bound (B : HilbertBasis I 𝕜 H) (m : I → 𝕜) (K : ℝ) (hK : 0 ≤ K)
 (hm : ∀ i, ‖m i‖ ≤ K) : ‖diag B m K hK hm‖ ≤ K := by
 apply ContinuousLinearMap.opNorm_le_bound _ hK
 intro x
 rw [← B.repr.norm_map]
 simp only [diag, ContinuousLinearMap.comp_apply,
   ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
   LinearIsometryEquiv.apply_symm_apply]
 have hh := (lp.mapCLM 2 (fun i => m i • ContinuousLinearMap.id 𝕜 𝕜) hK
   (fun i => by simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using hm i)).le_of_opNorm_le
   (lp.norm_mapCLM_le 2 _ hK _) (B.repr x)
 simpa using hh

lemma norm_sq_lp (x : lp (fun _ : I => 𝕜) 2) :
 ‖x‖ ^ 2 = ∑' i, ‖x i‖ ^ 2 := by
 simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x

/-- Dominated convergence of square-summable coordinates gives norm convergence. -/
lemma lp_dominated {J : Type} {l : Filter J}
 (f : J → lp (fun _ : I => 𝕜) 2) (g : lp (fun _ : I => 𝕜) 2)
 (b : lp (fun _ : I => 𝕜) 2)
 (hc : ∀ i, Tendsto (fun j => f j i) l (𝓝 (g i)))
 (hb : ∀ᶠ j in l, ∀ i, ‖f j i - g i‖ ≤ ‖b i‖) :
 Tendsto f l (𝓝 g) := by
 have hs : Summable (fun i => ‖b i‖ ^ 2) := by
   simpa using (lp.hasSum_norm (p := 2) (by norm_num) b).summable
 have ht := tendsto_tsum_of_dominated_convergence hs
   (g := fun _ : I => (0 : ℝ))
   (fun i => by simpa using ((hc i).sub_const (g i)).norm.pow 2)
   (hb.mono (fun j hj i => by
     rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _) ]
     exact
       (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (hj i))))
 have hh : Tendsto (fun j => ‖f j - g‖ ^ 2) l (𝓝 0) := by
   simpa only [norm_sq_lp, lp.coeFn_sub, Pi.sub_apply, tsum_zero] using ht
 have ht' := hh.sqrt
 rw [Real.sqrt_zero] at ht'
 have he : (fun j => Real.sqrt (‖f j - g‖ ^ 2)) = (fun j => ‖f j - g‖) := by
   funext j; exact Real.sqrt_sq (norm_nonneg _)
 rw [he] at ht'
 exact tendsto_iff_norm_sub_tendsto_zero.mpr ht'

lemma diag_single (B : HilbertBasis I 𝕜 H) (m : I → 𝕜) (K : ℝ) (hK : 0 ≤ K)
 (hm : ∀ i, ‖m i‖ ≤ K) (i : I) : diag B m K hK hm (B i) = m i • B i := by
 classical
 apply B.repr.injective
 ext j
 rw [diag_repr, map_smul]
 simp only [B.repr_self, lp.single_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
 by_cases h : i = j <;> simp [h]

lemma diag_norm_le (B : HilbertBasis I 𝕜 H) (T : H →L[𝕜] H)
 (m : I → 𝕜) (C : ℝ) (hC : 0 ≤ C)
 (hm : ∀ i, ‖m i‖ ≤ C)
 (ht : ∀ x i, B.repr (T x) i = m i * B.repr x i) : ‖T‖ ≤ C := by
 have he : T = diag B m C hC hm := by
   ext x
   apply B.repr.injective
   ext i
   rw [ht, diag_repr]
 rw [he]
 exact diag_bound _ _ _ _ _

/-- A diagonal multiplier vanishing at infinity is a norm limit of finite-rank maps. -/
lemma diag_compact (B : HilbertBasis I 𝕜 H) (T : H →L[𝕜] H)
 (m : I → 𝕜) (ht : ∀ x i, B.repr (T x) i = m i * B.repr x i)
 (hm : ∀ ε : ℝ, 0 < ε → {i | ε ≤ ‖m i‖}.Finite) : IsCompactOperator T := by
 classical
 have hclosed : IsClosed {T : H →L[𝕜] H | IsCompactOperator T} := isClosed_setOfPred_isCompactOperator
 change T ∈ {T : H →L[𝕜] H | IsCompactOperator T}
 rw [← hclosed.closure_eq, mem_closure_iff_nhds]
 intro U hU
 obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
 let s := (hm (ε / 2) (by positivity)).toFinset
 let P : H →L[𝕜] H := ∑ i ∈ s, m i • (innerSL 𝕜 (B i)).smulRight (B i)
 have hP : IsCompactOperator P := by
   have hi (i : I) : IsCompactOperator (m i • (innerSL 𝕜 (B i)).smulRight (B i)) := by
     have hh := (isCompactOperator_of_locallyCompactSpace_dom (innerSL 𝕜 (B i))).clm_comp
       (ContinuousLinearMap.smulRight (ContinuousLinearMap.id 𝕜 𝕜) (m i • B i))
     convert hh using 1
     funext x
     dsimp
     exact smul_comm _ _ _
   apply (compactOperator (RingHom.id 𝕜) H H).sum_mem
   intro i hi'
   exact hi i
 have hrepr (x : H) (j : I) :
     B.repr (P x) j = (if j ∈ s then m j else 0) * B.repr x j := by
   simp only [P, sum_apply, smul_apply,
     ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_sum, map_smul,
     B.repr_self, lp.coeFn_sum, lp.coeFn_smul, Pi.smul_apply, lp.single_apply, smul_eq_mul]
   simp [Pi.single_apply, mul_comm, B.repr_apply_apply]
 have hnorm : ‖T - P‖ ≤ ε / 2 := by
   apply diag_norm_le B (T - P) (fun i => if i ∈ s then 0 else m i) (ε / 2) (by positivity)
   · intro i
     split_ifs with hi
     · simp; positivity
     · have hh : ¬ ε / 2 ≤ ‖m i‖ := by
         simpa only [s, Finite.mem_toFinset, mem_ofPred_eq] using hi
       exact (lt_of_not_ge hh).le
   · intro x i
     rw [sub_apply, map_sub]
     change B.repr (T x) i - B.repr (P x) i = _
     rw [ht, hrepr]
     split_ifs <;> simp
 have hdist : dist P T < ε := by
   rw [dist_eq_norm, norm_sub_rev]
   linarith
 exact ⟨P, hball hdist, hP⟩

lemma exp_bound {lam γ t : ℝ} (hlam : γ ≤ lam) (ht : 0 ≤ t) :
 Real.exp (-t * lam) ≤ Real.exp (-t * γ) := by
 apply Real.exp_le_exp.mpr
 nlinarith

lemma exp_local_bound {lam γ t : ℝ} (hlam : γ ≤ lam) (ht : t ∈ Icc 0 1) :
 Real.exp (-t * lam) ≤ Real.exp |γ| := by
 apply Real.exp_le_exp.mpr
 have hh := mul_le_mul_of_nonneg_left (neg_le_neg hlam) ht.1
 have hγ : -γ ≤ |γ| := neg_le_abs γ
 have hp := mul_le_mul_of_nonneg_left hγ ht.1
 have hq := mul_le_mul_of_nonneg_right ht.2 (abs_nonneg γ)
 nlinarith

def thermal (B : HilbertBasis I 𝕜 H) (lam : I → ℝ) (γ : ℝ) (hl : ∀ i, γ ≤ lam i)
 (t : ℝ≥0) : H →L[𝕜] H :=
 diag B (fun i => (Real.exp (-(t : ℝ) * lam i) : 𝕜))
   (Real.exp (-(t : ℝ) * γ)) (Real.exp_pos _).le
   (fun i => by simpa only [RCLike.norm_ofReal, Real.abs_exp] using exp_bound (hl i) t.coe_nonneg)

lemma thermal_repr (B : HilbertBasis I 𝕜 H) (lam : I → ℝ) (γ : ℝ) (hl : ∀ i, γ ≤ lam i)
 (t : ℝ≥0) (x : H) (i : I) :
 B.repr (thermal B lam γ hl t x) i = (Real.exp (-(t : ℝ) * lam i) : 𝕜) * B.repr x i :=
 diag_repr ..

lemma thermal_zero (B : HilbertBasis I 𝕜 H) (lam : I → ℝ) (γ : ℝ) (hl : ∀ i, γ ≤ lam i) :
 thermal B lam γ hl 0 = ContinuousLinearMap.id 𝕜 H := by
 ext x
 apply B.repr.injective
 ext i
 simp [thermal_repr]

lemma thermal_add (B : HilbertBasis I 𝕜 H) (lam : I → ℝ) (γ : ℝ) (hl : ∀ i, γ ≤ lam i)
 (t s : ℝ≥0) : thermal B lam γ hl (t+s) = (thermal B lam γ hl t).comp (thermal B lam γ hl s) := by
 ext x
 apply B.repr.injective
 ext i
 simp only [ContinuousLinearMap.comp_apply, thermal_repr, NNReal.coe_add,
   neg_add, add_mul, Real.exp_add, RCLike.ofReal_mul, mul_assoc]

lemma thermal_strong_zero (B : HilbertBasis I 𝕜 H) (lam : I → ℝ) (γ : ℝ) (hl : ∀ i, γ ≤ lam i)
 (x : H) : Tendsto (fun h : ℝ => thermal B lam γ hl h.toNNReal x) (𝓝[>] 0) (𝓝 x) := by
 have hc (i : I) : Tendsto (fun h : ℝ => B.repr (thermal B lam γ hl h.toNNReal x) i)
     (𝓝[>] 0) (𝓝 (B.repr x i)) := by
   simp only [thermal_repr]
   have hh : Tendsto (fun h : ℝ => Real.exp (-(h.toNNReal : ℝ) * lam i)) (𝓝[>] 0) (𝓝 1) := by
     have ht : Tendsto (fun h : ℝ => -(h.toNNReal : ℝ) * lam i) (𝓝 0) (𝓝 0) := by
       have hcont : Continuous (fun h : ℝ => -(h.toNNReal : ℝ) * lam i) := by fun_prop
       simpa using hcont.tendsto 0
     simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.continuousAt.tendsto.comp ht).mono_left nhdsWithin_le_nhds
   simpa using (RCLike.continuous_ofReal.tendsto 1 |>.comp hh).mul_const (B.repr x i)
 have hb : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ i,
     ‖B.repr (thermal B lam γ hl h.toNNReal x) i - B.repr x i‖ ≤
       ‖((Real.exp |γ| + 1 : ℝ) : 𝕜) • B.repr x i‖ := by
   filter_upwards [self_mem_nhdsWithin, (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)))] with h hpos hone i
   rw [thermal_repr, ← sub_one_mul, norm_mul, norm_smul, RCLike.norm_ofReal,
     abs_of_nonneg (by positivity : 0 ≤ Real.exp |γ| + 1)]
   apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
   calc
     _ ≤ ‖(Real.exp (-(h.toNNReal : ℝ) * lam i) : 𝕜)‖ + ‖(1 : 𝕜)‖ := norm_sub_le _ _
     _ ≤ Real.exp |γ| + 1 := by
       rw [RCLike.norm_ofReal, Real.abs_exp, norm_one]
       exact add_le_add (exp_local_bound (hl i) ⟨h.toNNReal.coe_nonneg,
         by rw [Real.coe_toNNReal h hpos.le]; exact hone.le⟩) le_rfl
 have ht := lp_dominated (fun h : ℝ => B.repr (thermal B lam γ hl h.toNNReal x)) (B.repr x)
   ((((Real.exp |γ| + 1 : ℝ) : 𝕜)) • B.repr x) hc hb
 have hh := B.repr.symm.continuous.continuousAt.tendsto.comp ht
 simpa only [Function.comp_def, LinearIsometryEquiv.symm_apply_apply] using hh

lemma thermal_compact (B : HilbertBasis I 𝕜 H) (lam : I → ℝ) (γ : ℝ) (hl : ∀ i, γ ≤ lam i)
 (hfin : ∀ R : ℝ, {i | lam i ≤ R}.Finite)
 (t : ℝ≥0) (ht : 0 < t) : IsCompactOperator (thermal B lam γ hl t) := by
 apply diag_compact B _ _ (thermal_repr B lam γ hl t)
 intro ε hε
 apply (hfin (-Real.log ε / (t : ℝ))).subset
 intro i hi
 simp only [RCLike.norm_ofReal, Real.abs_exp, mem_ofPred_eq] at hi ⊢
 have hlog : Real.log ε ≤ -(t : ℝ) * lam i := (Real.log_le_iff_le_exp hε).mpr hi
 apply (le_div_iff₀ (show (0 : ℝ) < (t : ℝ) from ht)).mpr
 nlinarith


lemma exp_slope (r : ℝ) : Tendsto (fun h : ℝ =>
    (h : 𝕜)⁻¹ * ((Real.exp (-h*r) : 𝕜) - 1)) (𝓝[>] 0) (𝓝 (-(r : 𝕜))) := by
 have hd : HasDerivAt (fun h : ℝ => Real.exp (-h*r)) (-r) 0 := by
   simpa using (((hasDerivAt_id (0 : ℝ)).neg.mul_const r).exp)
 have ht := hd.tendsto_slope_zero_right
 have ht' : Tendsto (fun h : ℝ => (Real.exp (-h*r)-1)/h) (𝓝[>] 0) (𝓝 (-r)) := by
   simpa [div_eq_mul_inv, mul_comm] using ht
 have hh := ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).continuous.tendsto (-r)).comp ht'
 change Tendsto (fun h : ℝ => (((Real.exp (-h*r)-1)/h : ℝ) : 𝕜)) (𝓝[>] 0) (𝓝 ((-r : ℝ) : 𝕜)) at hh
 simpa only [Function.comp_def, RCLike.ofReal_div, RCLike.ofReal_sub, RCLike.ofReal_one,
   RCLike.ofReal_neg, RCLike.ofReal_mul, RCLike.ofReal_inv, div_eq_mul_inv, mul_comm] using hh


end DiagonalHeat
section SpectralHeat
variable {𝕜 H : Type} [RCLike 𝕜] [NormedAddCommGroup H]
 [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (A : Operator 𝕜 H H) (D : SpectralResolution A)
lemma coefficient_action (ha : A.IsFormalAdjoint A) (u : A.domain) (i : D.Index) :
 D.basis.repr (A u) i = (D.eigenvalue i : 𝕜) * D.basis.repr (u : H) i := by
 simp only [D.basis.repr_apply_apply]
 have hh := ha ⟨D.basis i, D.mem_domain i⟩ u
 rw [D.action, inner_smul_left, RCLike.conj_ofReal] at hh
 exact hh.symm

/-- Finite spectral sums converge in both graph coordinates. Closedness
therefore recovers the full domain from the coefficient relation. -/
lemma graph_of_eigenbasis {I : Type} (B : HilbertBasis I 𝕜 H) (d : I → 𝕜)
 (hc : A.IsClosed) (ha : ∀ i, (B i, d i • B i) ∈ A.graph) (x y : H)
 (he : ∀ i, B.repr y i = d i * B.repr x i) : (x,y) ∈ A.graph := by
 classical
 have ht : Tendsto (fun s : Finset I =>
     (∑ i ∈ s, B.repr x i • B i, ∑ i ∈ s, B.repr y i • B i))
     atTop (𝓝 (x,y)) := (B.hasSum_repr x).prodMk_nhds (B.hasSum_repr y)
 apply hc.mem_of_tendsto ht
 apply Eventually.of_forall
 intro s
 have heq : (∑ i ∈ s, B.repr x i • B i, ∑ i ∈ s, B.repr y i • B i) =
     ∑ i ∈ s, (B.repr x i • B i, B.repr y i • B i) := by
   apply Prod.ext <;> simp only [Prod.fst_sum, Prod.snd_sum]
 rw [heq]
 apply A.graph.sum_mem
 intro i hi
 have hh := A.graph.smul_mem (B.repr x i) (ha i)
 convert hh using 1
 ext
 · rfl
 · simp only [he i, smul_smul, Prod.smul_snd]
   rw [mul_comm]

namespace DiagonalHeat
variable {I : Type}

def semigroup (B : HilbertBasis I 𝕜 H) (lam : I → ℝ) (γ : ℝ) (hl : ∀ i, γ ≤ lam i) :
 C0Semigroup 𝕜 H where
 operators := thermal B lam γ hl
 at_zero := thermal_zero B lam γ hl
 add_time := thermal_add B lam γ hl
 strong_zero := thermal_strong_zero B lam γ hl

lemma quotient_repr (B : HilbertBasis I 𝕜 H) (lam : I → ℝ) (γ : ℝ) (hl : ∀ i, γ ≤ lam i)
 (h : ℝ) (x : H) (i : I) :
 B.repr (C0SemigroupSpec.differenceQuotientValue (semigroup B lam γ hl) h x) i =
 (h : 𝕜)⁻¹ * ((Real.exp (-(h.toNNReal : ℝ)*lam i) : 𝕜)-1) * B.repr x i := by
 simp only [C0SemigroupSpec.differenceQuotientValue, smul_apply, sub_apply,
   ContinuousLinearMap.id_apply, map_smul, map_sub, lp.coeFn_smul, lp.coeFn_sub,
   Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
 change (h : 𝕜)⁻¹ * (B.repr (thermal B lam γ hl h.toNNReal x) i - B.repr x i) = _
 rw [thermal_repr]
 ring

lemma quotient_coefficient_limit (B : HilbertBasis I 𝕜 H) (lam : I → ℝ) (γ : ℝ) (hl : ∀ i, γ ≤ lam i)
 (x : H) (i : I) : Tendsto
 (fun h => B.repr (C0SemigroupSpec.differenceQuotientValue (semigroup B lam γ hl) h x) i)
 (𝓝[>] 0) (𝓝 (-(lam i : 𝕜) * B.repr x i)) := by
 have hh := (exp_slope (𝕜 := 𝕜) (lam i)).mul_const (B.repr x i)
 apply hh.congr'
 filter_upwards [self_mem_nhdsWithin] with h hpos
 rw [quotient_repr, Real.coe_toNNReal h hpos.le]

lemma eigenvector_limit (B : HilbertBasis I 𝕜 H) (lam : I → ℝ) (γ : ℝ) (hl : ∀ i, γ ≤ lam i)
 (i : I) : C0SemigroupSpec.hasGeneratorLimitValue (semigroup B lam γ hl)
     (B i) (-(lam i : 𝕜) • B i) := by
 have ht := (exp_slope (𝕜 := 𝕜) (lam i)).smul_const (B i)
 apply ht.congr'
 filter_upwards [self_mem_nhdsWithin] with h hpos
 change _ = (h : 𝕜)⁻¹ • (thermal B lam γ hl h.toNNReal (B i) - B i)
 rw [thermal, diag_single, Real.coe_toNNReal h hpos.le]
 rw [mul_smul, sub_smul, one_smul, smul_sub]

end DiagonalHeat

/-- Both graph inclusions are proved: differentiation gives the coefficients
of every generator vector, and closedness extends the eigenvector identities
to the entire original operator domain. -/
lemma heat_generator (hc : A.IsClosed) (ha : A.IsFormalAdjoint A)
 (γ : ℝ) (hl : ∀ i, γ ≤ D.eigenvalue i) :
 C0SemigroupSpec.generatorValue (DiagonalHeat.semigroup D.basis D.eigenvalue γ hl) = -A := by
 let T := DiagonalHeat.semigroup D.basis D.eigenvalue γ hl
 let G := C0SemigroupSpec.generatorValue T
 have hclosed : G.IsClosed := C0Semigroup.generator_graph_closed T
 have heigen (i : D.Index) : (D.basis i, -(D.eigenvalue i : 𝕜) • D.basis i) ∈ G.graph :=
   (Semigroups.mem_generator_graph_iff T _ _).mpr
     (DiagonalHeat.eigenvector_limit D.basis D.eigenvalue γ hl i)
 apply LinearPMap.eq_of_eq_graph
 apply le_antisymm
 · intro p hp
   obtain ⟨u, hu, hGu⟩ := G.mem_graph_iff.mp hp
   have hlim := (Semigroups.mem_generator_graph_iff T p.1 p.2).mp hp
   have hcoeff (i : D.Index) : D.basis.repr p.2 i = -(D.eigenvalue i : 𝕜) * D.basis.repr p.1 i := by
     have hy := ((innerSL 𝕜 (D.basis i)).continuous.tendsto p.2).comp hlim
     have hy' : Tendsto (fun h => D.basis.repr
         (C0SemigroupSpec.differenceQuotientValue T h p.1) i) (𝓝[>] 0) (𝓝 (D.basis.repr p.2 i)) := by
       simpa only [Function.comp_def, D.basis.repr_apply_apply, innerSL_apply_apply] using hy
     exact tendsto_nhds_unique hy' (DiagonalHeat.quotient_coefficient_limit D.basis D.eigenvalue γ hl p.1 i)
   have hA : (p.1, -p.2) ∈ A.graph := by
     apply graph_of_eigenbasis A D.basis (fun i => (D.eigenvalue i : 𝕜)) hc
     · intro i
       simpa only [D.action] using A.mem_graph ⟨D.basis i, D.mem_domain i⟩
     · intro i
       rw [map_neg]
       change -D.basis.repr p.2 i = _
       rw [hcoeff]
       ring
   obtain ⟨v, hv, hAv⟩ := A.mem_graph_iff.mp hA
   apply (-A).mem_graph_iff.mpr
   refine ⟨v, hv, ?_⟩
   change -A v = p.2
   rw [hAv, neg_neg]
 · intro p hp
   obtain ⟨u, hu, hAu⟩ := (-A).mem_graph_iff.mp hp
   apply graph_of_eigenbasis G D.basis (fun i => -(D.eigenvalue i : 𝕜)) hclosed heigen
   intro i
   have heq : p.2 = -A u := hAu.symm
   rw [heq, map_neg]
   change -D.basis.repr (A u) i = _
   rw [coefficient_action A D ha, ← hu]
   ring


theorem heat : Spec.Heat := by
 intro 𝕜 _ a b c A hA
 obtain ⟨D⟩ := spectrum 𝕜 a b c A hA
 obtain ⟨γ, hl⟩ := D.lower_bound
 have hprop : A.IsClosed ∧ A.IsFormalAdjoint A := by
   rcases hA with hA | hA
   · have heq := SturmLiouvilleDirichlet.formRealization_unique c hA
       (SturmLiouvilleDirichlet.dirichletOperator_formRealization c)
     subst A
     have hs : IsSelfAdjoint (SturmLiouvilleDirichlet.dirichletOperator (𝕜 := 𝕜) c) := by
       change (SturmLiouvilleDirichlet.dirichletOperator (𝕜 := 𝕜) c).adjoint = _
       exact (SturmLiouvilleDirichlet.dirichletOperator_selfAdjoint c).symm
     exact ⟨hs.isClosed, SturmLiouvilleDirichlet.dirichletOperator_formalAdjoint c⟩
   · have heq := SturmLiouvillePeriodic.formRealization_unique c hA
       (SturmLiouvillePeriodic.periodicOperator_formRealization c)
     subst A
     have hs : IsSelfAdjoint (SturmLiouvillePeriodic.periodicOperator (𝕜 := 𝕜) c) := by
       change (SturmLiouvillePeriodic.periodicOperator (𝕜 := 𝕜) c).adjoint = _
       exact (SturmLiouvillePeriodic.periodicOperator_selfAdjoint c).symm
     exact ⟨hs.isClosed, SturmLiouvillePeriodic.periodicOperator_formalAdjoint c⟩
 refine ⟨D, DiagonalHeat.semigroup D.basis D.eigenvalue γ hl,
   heat_generator A D hprop.1 hprop.2 γ hl, ?_, ?_⟩
 · intro t i
   apply DiagonalHeat.diag_single
   intro j
   simpa only [RCLike.norm_ofReal, Real.abs_exp] using DiagonalHeat.exp_bound (hl j) t.coe_nonneg
 · intro t ht
   exact DiagonalHeat.thermal_compact D.basis D.eigenvalue γ hl D.finite_below t ht


end SpectralHeat
end ExpandedFA.Models.SturmLiouvilleSpectrumAndHeat
