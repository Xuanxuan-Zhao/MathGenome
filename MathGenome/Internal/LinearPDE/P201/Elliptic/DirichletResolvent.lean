import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.DirichletResolvent
import MathGenome.Internal.LinearPDE.P201.Elliptic.WeakDirichlet
import MathGenome.Internal.LinearPDE.P201.Elliptic.ClosedForm
import MathGenome.Internal.FourierSobolev.P102.Sobolev.Rellich

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace P201.DirichletResolvent
open P201Specs.Dirichlet

theorem inclusion_injective {n : ℕ} (Ω : Domain n) :
    Function.Injective (hZeroUnderlying (𝕜 := ℝ) Ω) := by
  intro u v h
  apply Subtype.ext
  exact hilbertUnderlyingInjective Ω 1 h

/-- Each test is in the actual H¹ closure, with its original L² class. -/
theorem test_in_range {n : ℕ} (Ω : Domain n) (φ : Test ℝ Ω) :
    ∃ u : H10 ℝ Ω, hZeroUnderlying Ω u = P102.U4.testToDomainLp Ω 2 φ := by
  obtain ⟨v, hv⟩ := P102.U4.zeroExtension_smoothInclusion Ω 1 2 φ
  let u : H ℝ Ω 1 := (hToW ℝ Ω 1).symm v
  have hu : u ∈ P201Specs.hZeroSubmodule ℝ Ω := by
    apply Submodule.le_topologicalClosure
    change ∃ ψ, P102.U4.testToDomainLp Ω 2 ψ =
      P102.U4.sobolevUnderlying (hToW ℝ Ω 1 u)
    exact ⟨φ, by simpa [u] using hv.symm⟩
  refine ⟨⟨u, hu⟩, ?_⟩
  change P102.U4.sobolevUnderlying (hToW ℝ Ω 1 u) = _
  simpa [u] using hv

theorem inclusion_dense {n : ℕ} (Ω : Domain n) :
    DenseRange (hZeroUnderlying (𝕜 := ℝ) Ω) := by
  change Dense ((hZeroUnderlying (𝕜 := ℝ) Ω).range : Set (Lp ℝ Ω 2))
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm _ bot_le
  intro f hf
  have hdist : regularDistribution Ω f = regularDistribution Ω (0 : Lp ℝ Ω 2) := by
    ext φ
    obtain ⟨u, hu⟩ := test_in_range Ω φ
    have hz : inner ℝ (P102.U4.testToDomainLp Ω 2 φ) f = 0 :=
      hu ▸ hf (hZeroUnderlying Ω u) ⟨u, rfl⟩
    rw [P102.U4.regularLp_pairing Ω 2, P102.U4.regularLp_pairing Ω 2,
      P102.U4.lpTestPairing_eq_integral, P102.U4.lpTestPairing_eq_integral]
    change (∫ x in Ω, f x * φ x) = (∫ x in Ω, (0 : Lp ℝ Ω 2) x * φ x)
    rw [show (∫ x in Ω, (0 : Lp ℝ Ω 2) x * φ x) = 0 by
      apply integral_eq_zero_of_ae
      filter_upwards [Lp.coeFn_zero (E := ℝ) (p := (2 : ℝ≥0∞)) (μ := domainMeasure Ω)] with x hx
      change (0 : Lp ℝ Ω 2) x * φ x = 0
      rw [show (0 : Lp ℝ Ω 2) x = 0 from hx]
      exact zero_mul _]
    rw [L2.inner_def] at hz
    calc
      (∫ x in Ω, f x * φ x) =
          ∫ x in Ω, inner ℝ (P102.U4.testToDomainLp Ω 2 φ x) (f x) := by
        apply integral_congr_ae
        filter_upwards [P102.U4.testToDomainLp_ae Ω 2 φ] with x hx
        simp [hx, RCLike.inner_apply]
      _ = 0 := hz
  exact P102.U4.regularLp_injective Ω 2 hdist

theorem inclusion_compact (m : ℕ) (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) :
    IsCompactOperator (hZeroUnderlying (𝕜 := ℝ) Ω) := by
  obtain ⟨I, _, hI, hc⟩ := P102.Sobolev.Rellich.same_exponent
    m (graphFrame m) Ω hΩ ℝ 2 (by norm_num)
  have he : I = P102.U4.sobolevUnderlyingCLM (𝕜 := ℝ) Ω 1 2 := by
    apply ContinuousLinearMap.ext
    intro u
    exact Lp.ext (hI u)
  subst I
  have hcompact : IsCompactOperator (P102.U4.sobolevUnderlyingCLM (𝕜 := ℝ) Ω 1 2) := by
    apply (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image _).mpr
    exact ⟨Metric.ball 0 1, Metric.ball_mem_nhds _ zero_lt_one,
      hc _ Metric.isBounded_ball⟩
  exact hcompact.comp_clm
    ((hToW ℝ Ω 1).toContinuousLinearMap.comp (P201Specs.hZeroSubmodule ℝ Ω).subtypeL)

theorem embedding : P201Specs.DirichletResolvent.EmbeddingStatement := by
  intro m Ω hΩ
  exact ⟨inclusion_injective Ω, inclusion_dense Ω, inclusion_compact m Ω hΩ⟩

/-- The solution map is constructed from the coercive variational problem;
linearity follows from uniqueness, and its bound uses the full H¹ norm. -/
theorem variational_inverse {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n)))
    (A : MatrixField n) (hA : MemLp A ∞ (domainMeasure Ω))
    (lam : ℝ) (hlam : 0 < lam) (hEll : Elliptic Ω A lam) :
    ∃ T : Lp ℝ Ω 2 →L[ℝ] H10 ℝ Ω,
      (∀ (f : Lp ℝ Ω 2) (v : H10 ℝ Ω),
        ellipticEnergyForm Ω A (T f).val v.val = pivot Ω f v) ∧
      (∀ (f : Lp ℝ Ω 2) (u : H10 ℝ Ω),
        Solves Ω A (pivot Ω f) u.val ↔ u = T f) := by
  letI : NormedAddCommGroup (H ℝ Ω 1) := inferInstance
  letI : NormedSpace ℝ (H ℝ Ω 1) := inferInstance
  letI : NormedAddCommGroup (H10 ℝ Ω) := inferInstance
  letI : NormedSpace ℝ (H10 ℝ Ω) := inferInstance
  letI : NormedAddCommGroup (Hminus1 ℝ Ω) := inferInstance
  letI : NormedSpace ℝ (Hminus1 ℝ Ω) := inferInstance
  obtain ⟨C, hC, hsolve⟩ := Dirichlet.homogeneous hn Ω hb
  choose t ht hnorm huniq using hsolve A hA lam hlam hEll
  let F : Hminus1 ℝ Ω →ₗ[ℝ] H10 ℝ Ω :=
    { toFun := t
      map_add' := by
        intro f g
        symm
        apply huniq
        intro v
        change ellipticEnergyForm Ω A (t f + t g).val v.val = _
        rw [← Dirichlet.form_apply Ω A hA]
        simp only [Submodule.coe_add, map_add, add_apply]
        rw [Dirichlet.form_apply, Dirichlet.form_apply]
        exact congrArg₂ (· + ·) (ht _ v) (ht _ v)
      map_smul' := by
        intro c f
        symm
        apply huniq
        intro v
        change ellipticEnergyForm Ω A (c • t f).val v.val = _
        rw [← Dirichlet.form_apply Ω A hA]
        simp only [Submodule.coe_smul, map_smul, smul_apply]
        rw [Dirichlet.form_apply]
        exact congrArg (c • ·) (ht _ v) }
  let U : Hminus1 ℝ Ω →L[ℝ] H10 ℝ Ω :=
    by
      change (H10 ℝ Ω →L[ℝ] ℝ) →L[ℝ] H10 ℝ Ω
      exact F.mkContinuous (C * lam⁻¹) hnorm
  let T : Lp ℝ Ω 2 →L[ℝ] H10 ℝ Ω := U.comp (pivot Ω)
  exact ⟨T, fun f => ht _, fun f u => ⟨fun hu => huniq _ u hu,
    by rintro rfl; exact ht _⟩⟩

/-- Symmetry, positivity and density are deduced for the concrete PDE inverse. -/
theorem inverse : P201Specs.DirichletResolvent.InverseStatement := by
  intro m Ω hΩ A hA lam hlam hEll hsym
  obtain ⟨T, hT, huniq⟩ := variational_inverse (by omega) Ω
    (Dirichlet.lipschitz_isBounded Ω hΩ) A hA lam hlam hEll
  let S := (hZeroUnderlying Ω).comp T
  have hpair (f : Lp ℝ Ω 2) (v : H10 ℝ Ω) :
      ellipticEnergyForm Ω A (T f).val v.val =
        inner ℝ f (hZeroUnderlying Ω v) := hT f v
  have hs : S.toLinearMap.IsSymmetric := by
    intro f g
    change inner ℝ (S f) g = inner ℝ f (S g)
    rw [real_inner_comm g (S f)]
    change inner ℝ g (hZeroUnderlying Ω (T f)) =
      inner ℝ f (hZeroUnderlying Ω (T g))
    rw [← hpair, ← hpair, ← Dirichlet.form_apply Ω A hA,
      ← Dirichlet.form_apply Ω A hA]
    exact Dirichlet.form_symmetric Ω A hA hsym _ _
  have hinj : Function.Injective S := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm _ bot_le
    intro f hf
    have hz : T f = 0 := inclusion_injective Ω (by
      change S f = hZeroUnderlying Ω 0
      simpa using hf)
    apply Dense.eq_of_inner_left (𝕜 := ℝ) (inclusion_dense Ω)
    intro w hw
    obtain ⟨v, rfl⟩ := hw
    rw [← hpair, hz]
    rw [← Dirichlet.form_apply Ω A hA]
    simp
  have hdense : DenseRange S := by
    change Dense (S.range : Set (Lp ℝ Ω 2))
    rw [Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff, hs.orthogonal_range]
    exact LinearMap.ker_eq_bot.mpr hinj
  refine ⟨T, hT, huniq, (inclusion_compact m Ω hΩ).comp_clm T,
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hs.isSelfAdjoint, ?_, hinj, hdense⟩
  intro f
  change 0 ≤ inner ℝ f (hZeroUnderlying Ω (T f))
  rw [← hpair, ← Dirichlet.form_apply Ω A hA]
  have hco := Dirichlet.form_gradient_coercive Ω A hA lam hEll (T f).val
  exact (mul_nonneg hlam.le (sq_nonneg _)).trans hco

/-- Recover the H¹₀ vector from its L² class. This equivalence is algebraic;
the range carries the ambient L² norm, not the Sobolev norm. -/
def rangeEquiv {n : ℕ} (Ω : Domain n) :
    H10 ℝ Ω ≃ₗ[ℝ] (hZeroUnderlying (𝕜 := ℝ) Ω).range :=
  LinearEquiv.ofInjective (hZeroUnderlying Ω).toLinearMap (inclusion_injective Ω)

@[simp] theorem rangeEquiv_coe {n : ℕ} (Ω : Domain n) (u : H10 ℝ Ω) :
    (rangeEquiv Ω u : Lp ℝ Ω 2) = hZeroUnderlying Ω u := rfl

/-- The concrete coefficient form on its dense L² form domain. -/
def coefficientForm {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) :
    P201.Elliptic.DenseForm ℝ (Lp ℝ Ω 2) where
  domain := (hZeroUnderlying (𝕜 := ℝ) Ω).range
  dense := inclusion_dense Ω
  form := ((Dirichlet.form Ω A hA).bilinearComp
    (zeroInclusion Ω) (zeroInclusion Ω)).toLinearMap₁₂.compl₁₂
      (rangeEquiv Ω).symm.toLinearMap (rangeEquiv Ω).symm.toLinearMap

@[simp] theorem coefficientForm_apply {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (u v : H10 ℝ Ω)
    (hu : hZeroUnderlying Ω u ∈ (coefficientForm Ω A hA).domain)
    (hv : hZeroUnderlying Ω v ∈ (coefficientForm Ω A hA).domain) :
    (coefficientForm Ω A hA).form ⟨hZeroUnderlying Ω u, hu⟩
      ⟨hZeroUnderlying Ω v, hv⟩ = ellipticEnergyForm Ω A u.val v.val := by
  have he (w : H10 ℝ Ω) (hw : hZeroUnderlying Ω w ∈ (coefficientForm Ω A hA).domain) :
      (rangeEquiv Ω).symm ⟨hZeroUnderlying Ω w, hw⟩ = w := by
    apply (rangeEquiv Ω).injective
    simp only [LinearEquiv.apply_symm_apply]
    rfl
  change Dirichlet.form Ω A hA
    ((rangeEquiv Ω).symm ⟨hZeroUnderlying Ω u, hu⟩).val
    ((rangeEquiv Ω).symm ⟨hZeroUnderlying Ω v, hv⟩).val = _
  rw [he, he, Dirichlet.form_apply]

theorem coefficient_graph {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (u f : Lp ℝ Ω 2) :
    (u, f) ∈ (coefficientForm Ω A hA).associatedOperator.graph ↔
      ∃ v : H10 ℝ Ω, hZeroUnderlying Ω v = u ∧ Solves Ω A (pivot Ω f) v.val := by
  rw [P201.Elliptic.DenseForm.mem_associated_graph]
  constructor
  · rintro ⟨hu, huf⟩
    obtain ⟨v, rfl⟩ := hu
    refine ⟨v, rfl, fun w => ?_⟩
    have he := huf ⟨hZeroUnderlying Ω w, ⟨w, rfl⟩⟩
    change ellipticEnergyForm Ω A v.val w.val = inner ℝ f (hZeroUnderlying Ω w)
    calc
      ellipticEnergyForm Ω A v.val w.val =
          (coefficientForm Ω A hA).form ⟨hZeroUnderlying Ω v, ⟨v, rfl⟩⟩
            ⟨hZeroUnderlying Ω w, ⟨w, rfl⟩⟩ :=
        (coefficientForm_apply Ω A hA v w _ _).symm
      _ = inner ℝ (hZeroUnderlying Ω w) f := he
      _ = inner ℝ f (hZeroUnderlying Ω w) := real_inner_comm _ _
  · rintro ⟨v, rfl, hv⟩
    refine ⟨⟨v, rfl⟩, fun w => ?_⟩
    obtain ⟨z, hz⟩ := w.property
    have he : w = ⟨hZeroUnderlying Ω z, ⟨z, rfl⟩⟩ := Subtype.ext hz.symm
    rw [he, coefficientForm_apply]
    change ellipticEnergyForm Ω A v.val z.val = inner ℝ (hZeroUnderlying Ω z) f
    have hvz := hv z
    change ellipticEnergyForm Ω A v.val z.val = inner ℝ f (hZeroUnderlying Ω z) at hvz
    exact hvz.trans (real_inner_comm _ _)

/-- A canonical associated operator whose graph is the inverse of a bounded
self-adjoint injection is self-adjoint on exactly that inverse range. -/
theorem selfAdjoint_of_inverse {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (a : P201.Elliptic.DenseForm ℝ H) (S : H →L[ℝ] H)
    (hS : S.adjoint = S) (hd : DenseRange S)
    (hg : ∀ u f : H, (u, f) ∈ a.associatedOperator.graph ↔ S f = u) :
    a.associatedOperator = a.associatedOperator.adjoint := by
  let L := a.associatedOperator
  have hdom : (L.domain : Set H) = Set.range S := by
    ext u
    change u ∈ L.domain ↔ ∃ f, S f = u
    rw [LinearPMap.mem_domain_iff]
    exact exists_congr (fun f => hg u f)
  have hdL : Dense (L.domain : Set H) := hdom ▸ hd
  have hleft (u : L.domain) : S (L u) = (u : H) := (hg _ _).mp (L.mem_graph u)
  have hs : L.IsFormalAdjoint L := by
    intro u v
    rw [← hleft u, ← hleft v]
    change inner ℝ (L u) (S (L v)) = inner ℝ (S (L u)) (L v)
    simpa only [hS] using S.adjoint_inner_right (L u) (L v)
  apply le_antisymm (LinearPMap.IsFormalAdjoint.le_adjoint hdL hs)
  apply LinearPMap.le_of_le_graph
  rintro ⟨y, w⟩ hp
  obtain ⟨v, hv, hvw⟩ := L.adjoint.mem_graph_iff.mp hp
  apply (hg y w).mpr
  apply ext_inner_left ℝ
  intro f
  have hf := (hg (S f) f).mpr rfl
  obtain ⟨u, hu, huf⟩ := L.mem_graph_iff.mp hf
  have he := (LinearPMap.adjoint_isFormalAdjoint hdL).symm u v
  rw [huf, hu, hvw, hv] at he
  change inner ℝ f y = inner ℝ (S f) w at he
  calc
    inner ℝ f (S w) = inner ℝ (S f) w := by
      simpa only [hS] using S.adjoint_inner_right f w
    _ = inner ℝ f y := he.symm

/-- The H¹₀ class of a compact smooth test, fixed by its L² representative. -/
def testClass {n : ℕ} (Ω : Domain n) (φ : Test ℝ Ω) : H10 ℝ Ω :=
  (test_in_range Ω φ).choose

theorem testClass_underlying {n : ℕ} (Ω : Domain n) (φ : Test ℝ Ω) :
    hZeroUnderlying Ω (testClass Ω φ) = P102.U4.testToDomainLp Ω 2 φ :=
  (test_in_range Ω φ).choose_spec

theorem testClass_derivative {n : ℕ} (Ω : Domain n) (φ : Test ℝ Ω) (i : Fin n) :
    hFirstDerivative (testClass Ω φ).val i =
      P102.U4.testToDomainLp Ω 2 (P102.U4.testPartialWord Ω [i] φ) := by
  apply P102.U4.SlabPoincareProof.smooth_sobolev_firstDerivative
  exact testClass_underlying Ω φ

/-- Each component of the actual flux is an L² function. -/
theorem flux_component_memLp {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (u : H ℝ Ω 1) (i : Fin n) :
    MemLp (fun x => ∑ j, A x i j * hFirstDerivative u j x) 2 (domainMeasure Ω) := by
  apply memLp_finsetSum
  intro j _
  exact (Lp.memLp (Dirichlet.weightedDerivative Ω A hA i j u)).ae_eq
    (Dirichlet.weightedDerivative_ae Ω A hA i j u)

/-- Transposition yields the coefficient energy on compact tests. -/
theorem divergence_test {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (u : H ℝ Ω 1) (φ : Test ℝ Ω) :
    negativeDivergenceDistribution Ω
      (fun x => WithLp.toLp 2 (fun i => ∑ j, A x i j * hFirstDerivative u j x)) φ =
      ellipticEnergyForm Ω A u (testClass Ω φ).val := by
  have hreg (i : Fin n) :
      regularDistribution Ω (fun x => ∑ j, A x i j * hFirstDerivative u j x)
        (P102.U4.testPartialWord Ω [i] φ) =
        ∑ j, inner ℝ (Dirichlet.weightedDerivative Ω A hA i j u)
          (hFirstDerivative (testClass Ω φ).val i) := by
    rw [P102.U4.regular_pairing n ℝ Ω _
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((flux_component_memLp Ω A hA u i).locallyIntegrable (by norm_num)))]
    simp_rw [mul_comm (∑ j, A _ i j * _) _, Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [testClass_derivative, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Dirichlet.weightedDerivative_ae Ω A hA i j u,
        P102.U4.testToDomainLp_ae Ω 2 (P102.U4.testPartialWord Ω [i] φ)] with x hx hφ
      simp [hx, hφ, RCLike.inner_apply]
    · intro j _
      have h := Dirichlet.summand_integrable Ω A hA u (testClass Ω φ).val i j
      apply h.congr
      filter_upwards [P102.U4.testToDomainLp_ae Ω 2 (P102.U4.testPartialWord Ω [i] φ)] with x hx
      have hd : hFirstDerivative (testClass Ω φ).val i x =
          P102.U4.testPartialWord Ω [i] φ x := by
        rw [testClass_derivative]
        exact hx
      rw [hd]
      ring
  rw [← Dirichlet.form_apply Ω A hA]
  change (-(∑ i : Fin n, P102.U4.distributionPartial ({i} : MultiIndex n)
    (regularDistribution Ω (fun x => ∑ j, A x i j * hFirstDerivative u j x)))) φ = _
  simp only [neg_apply, sum_apply, P102.U4.distributionPartial,
    Multiset.card_singleton, pow_one, Multiset.sort_singleton, smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, neg_one_mul, Finset.sum_neg_distrib, neg_neg]
  rw [Dirichlet.form]
  simp only [sum_apply, ContinuousLinearMap.bilinearComp_apply, Dirichlet.derivativeCLM_apply]
  exact Finset.sum_congr rfl (fun i _ => hreg i)

/-- Equality of distributions extends from tests to the full H¹₀ closure. -/
theorem distribution_iff_solves {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (u : H10 ℝ Ω) (f : Lp ℝ Ω 2) :
    negativeDivergenceDistribution Ω
      (fun x => WithLp.toLp 2 (fun i => ∑ j, A x i j * hFirstDerivative u.val j x)) =
      regularDistribution Ω f ↔ Solves Ω A (pivot Ω f) u.val := by
  have hpair (φ : Test ℝ Ω) : regularDistribution Ω f φ =
      pivot Ω f (testClass Ω φ) := by
    rw [P102.U4.regularLp_pairing Ω 2, P102.U4.lpTestPairing_eq_integral]
    change _ = inner ℝ f (hZeroUnderlying Ω (testClass Ω φ))
    rw [testClass_underlying, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [P102.U4.testToDomainLp_ae Ω 2 φ] with x hx
    simp [hx, RCLike.inner_apply, mul_comm]
  constructor
  · intro h
    have ht (φ : Test ℝ Ω) : ellipticEnergyForm Ω A u.val (testClass Ω φ).val =
        pivot Ω f (testClass Ω φ) := by
      rw [← divergence_test Ω A hA u.val φ, h, hpair]
    let C : Set (H ℝ Ω 1) := {v | Dirichlet.form Ω A hA u.val v =
      inner ℝ f (hUnderlying Ω 1 v)}
    have hc : IsClosed C := isClosed_eq (Dirichlet.form Ω A hA u.val).continuous
      ((innerSL ℝ f).continuous.comp (hUnderlying Ω 1).continuous)
    have hs : (((P102.U4.smoothSobolevSubmodule ℝ Ω 1 2).comap
        (hToW ℝ Ω 1).toLinearMap) : Set (H ℝ Ω 1)) ⊆ C := by
      rintro v ⟨φ, hφ⟩
      have he : v = (testClass Ω φ).val := hilbertUnderlyingInjective Ω 1
        (hφ.symm.trans (testClass_underlying Ω φ).symm)
      change Dirichlet.form Ω A hA u.val v = inner ℝ f (hUnderlying Ω 1 v)
      rw [he, Dirichlet.form_apply]
      exact ht φ
    intro v
    exact (Dirichlet.form_apply Ω A hA u.val v.val).symm.trans
      ((closure_minimal hs hc) v.property)
  · intro hu
    ext φ
    rw [divergence_test Ω A hA u.val φ, hpair]
    exact hu (testClass Ω φ)

/-- The exact real Dirichlet realization, including its distributional action
and its compact positive self-adjoint two-sided inverse. -/
theorem realization : P201Specs.DirichletResolvent.RealizationStatement := by
  intro m Ω hΩ _hne A hA lam hlam hEll hsym
  obtain ⟨T, hT, huniq, hcompact, hself, hpos, hinj, hdense⟩ :=
    inverse m Ω hΩ A hA lam hlam hEll hsym
  let a := coefficientForm Ω A hA
  let L := a.associatedOperator
  let S := (hZeroUnderlying Ω).comp T
  have hgraph := coefficient_graph Ω A hA
  have hg (u f : Lp ℝ Ω 2) : (u, f) ∈ L.graph ↔ S f = u := by
    rw [hgraph]
    constructor
    · rintro ⟨v, hv, hsol⟩
      rw [(huniq f v).mp hsol] at hv
      exact hv
    · intro hu
      exact ⟨T f, hu, (huniq f (T f)).mpr rfl⟩
  have hdom : (L.domain : Set (Lp ℝ Ω 2)) = Set.range S := by
    ext u
    change u ∈ L.domain ↔ ∃ f, S f = u
    rw [LinearPMap.mem_domain_iff]
    exact exists_congr (fun f => hg u f)
  have hdL : Dense (L.domain : Set (Lp ℝ Ω 2)) := hdom ▸ hdense
  refine ⟨a, T, rfl, coefficientForm_apply Ω A hA, hgraph, ?_,
    fun u => LinearPMap.mem_domain_iff, hdL,
    selfAdjoint_of_inverse a S hself hdense hg, ?_,
    fun f => (hg _ _).mpr rfl, fun u => (hg _ _).mp (L.mem_graph u),
    hdom, hcompact, hself, hpos, hinj, hdense⟩
  · intro u f
    rw [hgraph]
    exact exists_congr fun v => and_congr_right fun _ =>
      (distribution_iff_solves Ω A hA v f).symm
  · intro u
    obtain ⟨v, hv, hsol⟩ := (hgraph _ _).mp (L.mem_graph u)
    have he := hsol v
    change ellipticEnergyForm Ω A v.val v.val = inner ℝ (L u) (hZeroUnderlying Ω v) at he
    rw [hv] at he
    have hco := Dirichlet.form_gradient_coercive Ω A hA lam hEll v.val
    rw [Dirichlet.form_apply] at hco
    calc
      0 ≤ ellipticEnergyForm Ω A v.val v.val :=
        (mul_nonneg hlam.le (sq_nonneg _)).trans hco
      _ = inner ℝ (u : Lp ℝ Ω 2) (L u) := he.trans (real_inner_comm _ _)

end P201.DirichletResolvent
