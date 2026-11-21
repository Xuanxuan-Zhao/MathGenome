import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.ConfiningSchrodingerRealization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.WeightedConfiningEnergySpace

noncomputable section
open MeasureTheory Set TopologicalSpace Filter
open scoped InnerProductSpace ComplexConjugate Topology ENNReal

attribute [local instance 2000] NormedAddCommGroup.toSeminormedAddCommGroup

namespace ExpandedFA.Models.ConfiningSchrodingerRealization
open ExpandedFA.Models.WeightedConfiningEnergySpace
open ExpandedFA.Sobolev ExpandedFA.Distributions

variable {𝕜 : Type} [RCLike 𝕜]

lemma value_norm_le {p : Potential} (u : Space 𝕜 p) : ‖value u‖ ≤ ‖u‖ := by
  have h := weighted_norm_formula 𝕜 p u
  nlinarith [sq_nonneg ‖derivative u‖, sq_nonneg ‖weighted u‖,
    norm_nonneg u, norm_nonneg (value u)]

lemma energyForm_symm {p : Potential} (v u : Space 𝕜 p) :
    conj (energyForm v u) = energyForm u v := by
  simp only [energyForm, map_add, inner_conj_symm]

/-- The coercivity estimate gives bounded dependence on the L² datum. -/
lemma solution_bound (p : Potential) {α : ℝ} (hα : 0 < α)
    (hc : ∀ u : Space 𝕜 p, α * ‖u‖ ^ 2 ≤ RCLike.re (energyForm u u))
    (f : L2 𝕜) (u : Space 𝕜 p)
    (hu : ∀ v : Space 𝕜 p, energyForm v u = ⟪value v, f⟫_𝕜) :
    ‖u‖ ≤ α⁻¹ * ‖f‖ := by
  have h := hc u
  rw [hu] at h
  have he := (re_inner_le_norm (𝕜 := 𝕜) (value u) f).trans
    (mul_le_mul_of_nonneg_right (value_norm_le u) (norm_nonneg f))
  have hprod : α * ‖u‖ ^ 2 ≤ ‖u‖ * ‖f‖ := h.trans he
  by_cases hz : ‖u‖ = 0
  · rw [hz]; positivity
  · have hu0 : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hb : α * ‖u‖ ≤ ‖f‖ := by nlinarith
    exact (le_inv_mul_iff₀ hα).mpr hb

/-- Unique variational solutions assemble to a bounded linear map into V. -/
lemma exists_solution_map (p : Potential) (hp : PositiveAtInfinity p) :
    ∃ S : L2 𝕜 →L[𝕜] Space 𝕜 p,
      ∀ f v, energyForm v (S f) = ⟪value v, f⟫_𝕜 := by
  choose s hs huniq using (weighted_variational_solvability 𝕜 p hp)
  let L : L2 𝕜 →ₗ[𝕜] Space 𝕜 p :=
    { toFun := s
      map_add' := by
        intro f g
        apply (huniq (f + g) _ ?_).symm
        intro v
        change energyFormL p v (s f + s g) = _
        rw [map_add]
        simp only [energyFormL_apply, hs, inner_add_right]
      map_smul' := by
        intro c f
        apply (huniq (c • f) _ ?_).symm
        intro v
        change energyFormL p v (c • s f) = _
        rw [map_smul]
        simp only [energyFormL_apply, hs, inner_smul_right,
          smul_eq_mul] }
  obtain ⟨α, hα, hc⟩ := weighted_coercivity 𝕜 p hp
  exact ⟨L.mkContinuous (α⁻¹) (fun f => solution_bound p hα hc f (s f) (hs f)), hs⟩

/-- The energy inclusion has dense range in the original L² space. -/
lemma value_denseRange (p : Potential) : DenseRange (valueL (𝕜 := 𝕜) p) := by
  intro f
  apply closure_mono ?_ ((Lp.dense_hasCompactSupport_contDiff
    (E := Line) (F := 𝕜) (μ := lineMeasure) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)) f)
  rintro g ⟨φ, hg, hcomp, hdiff⟩
  let ψ : Tests 𝕜 (⊤ : Opens Line) := ⟨φ, hdiff, hcomp, by simp⟩
  obtain ⟨u, hu⟩ := weighted_smooth_inclusion 𝕜 p ψ
  exact ⟨u, Lp.ext (hu.trans hg.symm)⟩

lemma solution_operator_properties (p : Potential) (S : L2 𝕜 →L[𝕜] Space 𝕜 p)
    (hS : ∀ f v, energyForm v (S f) = ⟪value v, f⟫_𝕜) :
    let T := (valueL p).comp S
    IsSelfAdjoint T ∧ (∀ f, 0 ≤ RCLike.re ⟪f, T f⟫_𝕜) ∧
      Function.Injective T ∧ DenseRange T := by
  let T := (valueL p).comp S
  have hsym : ∀ f g, ⟪T f, g⟫_𝕜 = ⟪f, T g⟫_𝕜 := by
    intro f g
    change ⟪value (S f), g⟫_𝕜 = ⟪f, value (S g)⟫_𝕜
    rw [← hS g (S f), ← inner_conj_symm f, ← hS f (S g), energyForm_symm]
  have hself : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hsym
  have hinj : Function.Injective T := by
    intro f g hfg
    have hsfg : S f = S g := weighted_underlying_injective 𝕜 p hfg
    apply (value_denseRange (𝕜 := 𝕜) p).eq_of_inner_right 𝕜
    intro v
    change ⟪value v, f⟫_𝕜 = ⟪value v, g⟫_𝕜
    rw [← hS f v, ← hS g v, hsfg]
  refine ⟨hself, ?_, hinj, ?_⟩
  · intro f
    have hdiag := energyForm_diagonal p (S f)
    have he : ⟪f, T f⟫_𝕜 = energyForm (S f) (S f) := by
      exact (hsym f f).symm.trans (hS f (S f)).symm
    rw [he, hdiag]
    positivity
  · change Dense (T.range : Set (L2 𝕜))
    rw [Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff, T.orthogonal_range,
      (ContinuousLinearMap.isSelfAdjoint_iff'.mp hself)]
    exact LinearMap.ker_eq_bot.mpr hinj

section Inverse
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The inverse is defined on the actual range, with no completed or enlarged domain. -/
def rangeInverse (T : H →L[𝕜] H) (hT : Function.Injective T) : H →ₗ.[𝕜] H where
  domain := T.range
  toFun := (LinearEquiv.ofInjective T.toLinearMap hT).symm.toLinearMap

omit [CompleteSpace H] in
lemma rangeInverse_right (T : H →L[𝕜] H) (hT : Function.Injective T)
    (u : (rangeInverse T hT).domain) : T (rangeInverse T hT u) = u := by
  exact congrArg Subtype.val ((LinearEquiv.ofInjective T.toLinearMap hT).apply_symm_apply u)

lemma rangeInverse_graph (T : H →L[𝕜] H) (hT : Function.Injective T) (u f : H) :
    (u, f) ∈ (rangeInverse T hT).graph ↔ T f = u := by
  constructor
  · rintro h
    obtain ⟨v, hv, hf⟩ := (rangeInverse T hT).mem_graph_iff.mp h
    change (v : H) = u at hv
    change rangeInverse T hT v = f at hf
    rw [← hf, rangeInverse_right, hv]
  · intro h
    have hu : u ∈ (rangeInverse T hT).domain := ⟨f, h⟩
    refine (rangeInverse T hT).mem_graph_iff.mpr ⟨⟨u, hu⟩, rfl, ?_⟩
    apply hT
    exact (rangeInverse_right T hT _).trans h.symm

/-- A bounded injective self-adjoint operator has a self-adjoint inverse on its dense range.
This proof uses the defining adjoint identity, so it works over both scalar fields. -/
lemma rangeInverse_selfAdjoint (T : H →L[𝕜] H) (hi : Function.Injective T)
    (hd : DenseRange T) (hs : ∀ f g, ⟪T f, g⟫_𝕜 = ⟪f, T g⟫_𝕜) :
    (rangeInverse T hi).adjoint = rangeInverse T hi := by
  let A := rangeInverse T hi
  have hAd : Dense (A.domain : Set H) := hd
  have hformal : A.IsFormalAdjoint A := by
    intro x y
    rw [← rangeInverse_right T hi y, ← hs, rangeInverse_right]
  have hle : A ≤ A.adjoint := hformal.le_adjoint hAd
  apply LinearPMap.ext_iff.mpr
  refine ⟨le_antisymm ?_ hle.1, ?_⟩
  · intro y hy
    have he : T (A.adjoint ⟨y, hy⟩) = y := by
      apply ext_inner_right 𝕜
      intro f
      have hx : T f ∈ A.domain := ⟨f, rfl⟩
      have hf : A ⟨T f, hx⟩ = f := by
        apply hi
        exact rangeInverse_right T hi _
      calc
        ⟪T (A.adjoint ⟨y, hy⟩), f⟫_𝕜 = ⟪A.adjoint ⟨y, hy⟩, T f⟫_𝕜 := hs _ _
        _ = ⟪y, A ⟨T f, hx⟩⟫_𝕜 := LinearPMap.adjoint_isFormalAdjoint hAd ⟨y, hy⟩ ⟨T f, hx⟩
        _ = ⟪y, f⟫_𝕜 := by rw [hf]
    exact ⟨A.adjoint ⟨y, hy⟩, he⟩
  · intro x hx hy
    exact (hle.2 (x := ⟨x, hy⟩) (y := ⟨x, hx⟩) rfl).symm

end Inverse

/-- Conjugation preserves compact support and smoothness, also over ℝ. -/
def conjugateTest (φ : Tests 𝕜 (⊤ : Opens Line)) : Tests 𝕜 (⊤ : Opens Line) :=
  ⟨conj ∘ φ, (RCLike.conjCLE : 𝕜 ≃L[ℝ] 𝕜).contDiff.comp φ.contDiff,
    φ.hasCompactSupport.comp_left (map_zero _), by simp⟩

@[simp] lemma conjugateTest_apply (φ : Tests 𝕜 (⊤ : Opens Line)) (x : Line) :
    conjugateTest φ x = conj (φ x) := rfl

@[simp] lemma conjugateTest_involutive (φ : Tests 𝕜 (⊤ : Opens Line)) :
    conjugateTest (conjugateTest φ) = φ := by
  ext x
  exact RCLike.conj_conj _

lemma conjugateTest_partial (φ : Tests 𝕜 (⊤ : Opens Line)) :
    testPartialCLM [0] (conjugateTest φ) = conjugateTest (testPartialCLM [0] φ) := by
  ext x
  rw [testPartial_single_apply, conjugateTest_apply, testPartial_single_apply]
  change fderiv ℝ ((RCLike.conjCLE : 𝕜 ≃L[ℝ] 𝕜) ∘ φ) x (coordinateVector 0) = _
  rw [ContinuousLinearEquiv.comp_fderiv]
  rfl

/-- The defining first weak derivative identity for an arbitrary energy member. -/
lemma derivative_testing {p : Potential} (u : Space 𝕜 p)
    (ψ : Tests 𝕜 (⊤ : Opens Line)) :
    lpDistribution (derivative u) ψ = -lpDistribution (value u) (testPartialCLM [0] ψ) := by
  have h := congrArg (fun D : ScalarDistribution 𝕜 (⊤ : Opens Line) => D ψ)
    (u.val.fst.property firstIndex)
  change lpDistribution (derivative u) ψ =
    Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
      𝕜 1 (⊤ : Opens Line) (natIndex firstIndex) (lpDistribution (value u)) ψ at h
  simpa only [Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue,
    firstIndex_word, Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue,
    List.length_singleton, pow_one, smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, neg_one_mul] using h

/-- Every potential term in the distributional equation is a genuine integral.
Only boundedness on the support of the test is used; pu need not be globally L². -/
lemma potential_test_integrable (p : Potential) (u : Space 𝕜 p)
    (φ : Tests 𝕜 (⊤ : Opens Line)) :
    Integrable (fun x => (p.toContinuousMap (x 0) : 𝕜) * φ x * value u x) lineMeasure := by
  have hc : Continuous (fun x : Line => (p.toContinuousMap (x 0) : 𝕜) * φ x) :=
    (RCLike.continuous_ofReal.comp
      (p.toContinuousMap.continuous.comp (continuous_apply 0))).mul φ.continuous
  have hs : HasCompactSupport (fun x : Line => (p.toContinuousMap (x 0) : 𝕜) * φ x) :=
    φ.hasCompactSupport.mul_left
  exact (hc.memLp_of_hasCompactSupport (p := 2) hs).integrable_mul (Lp.memLp (value u))

/-- Integration by parts on compact tests relates the energy form to −u″+pu. -/
lemma smooth_form_testing {p : Potential} (u v : Space 𝕜 p)
    (φ : Tests 𝕜 (⊤ : Opens Line)) (hv : value v =ᵐ[lineMeasure] φ) :
    energyForm v u =
      -lpDistribution (value u) (testPartialCLM [0, 0] (conjugateTest φ)) +
        (∫ x, (p.toContinuousMap (x 0) : 𝕜) * conjugateTest φ x * value u x ∂lineMeasure) := by
  have hd := smooth_derivative_ae v φ hv
  have hder : ⟪derivative v, derivative u⟫_𝕜 =
      lpDistribution (derivative u) (testPartialCLM [0] (conjugateTest φ)) := by
    rw [scalar_inner_integral, lpDistribution_apply]
    apply integral_congr_ae
    filter_upwards [hd] with x hx
    rw [hx, conjugateTest_partial, conjugateTest_apply]
  have hw : ⟪weighted v, weighted u⟫_𝕜 =
      ∫ x, (p.toContinuousMap (x 0) : 𝕜) * conjugateTest φ x * value u x ∂lineMeasure := by
    rw [scalar_inner_integral]
    apply integral_congr_ae
    filter_upwards [potential_product_ae p v u, hv] with x hx hvx
    rw [hx, hvx, conjugateTest_apply]
  rw [energyForm, hder, hw, derivative_testing]
  rfl

lemma smooth_inner_testing {p : Potential} (v : Space 𝕜 p)
    (φ : Tests 𝕜 (⊤ : Opens Line)) (hv : value v =ᵐ[lineMeasure] φ) (f : L2 𝕜) :
    ⟪value v, f⟫_𝕜 = lpDistribution f (conjugateTest φ) := by
  rw [scalar_inner_integral, lpDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  rw [hx, conjugateTest_apply]

/-- Compact tests suffice because both sides of the variational identity are
continuous in the full weighted energy norm. -/
theorem form_distribution_equivalence :
    Specs.ExpandedFA.Models.ConfiningSchrodingerRealization.FormDistributionEquivalence := by
  intro 𝕜 _ p u f
  constructor
  · intro hu
    have hc : IsClosed {v : Space 𝕜 p | energyForm v u = ⟪value v, f⟫_𝕜} :=
      isClosed_eq ((ContinuousLinearMap.apply 𝕜 𝕜 u).continuous.comp (energyFormL p).continuous)
        ((innerSLFlip 𝕜 f).continuous.comp (valueL p).continuous)
    have he : closure (SmoothMembers 𝕜 p) ⊆
        {v : Space 𝕜 p | energyForm v u = ⟪value v, f⟫_𝕜} := by
      apply closure_minimal ?_ hc
      rintro v ⟨φ, hv⟩
      change energyForm v u = ⟪value v, f⟫_𝕜
      rw [smooth_form_testing u v φ hv, smooth_inner_testing v φ hv f]
      exact hu (conjugateTest φ)
    intro v
    exact he (weighted_smooth_density 𝕜 p v)
  · intro hu φ
    obtain ⟨v, hv⟩ := weighted_smooth_inclusion 𝕜 p (conjugateTest φ)
    have h := hu v
    rw [smooth_form_testing u v (conjugateTest φ) hv,
      smooth_inner_testing v (conjugateTest φ) hv f, conjugateTest_involutive] at h
    exact h

/-- The positive self-adjoint realization, including the exact distributional
operator domain, under only the exterior positive lower bound on p. -/
theorem confining_realization :
    Specs.ExpandedFA.Models.ConfiningSchrodingerRealization.Realization := by
  intro 𝕜 _ p hp
  obtain ⟨S, hS⟩ := exists_solution_map (𝕜 := 𝕜) p hp
  let T := (valueL p).comp S
  obtain ⟨hself, hpos, hinj, hdense⟩ := solution_operator_properties p S hS
  have hs : ∀ f g, ⟪T f, g⟫_𝕜 = ⟪f, T g⟫_𝕜 :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself
  let A := rangeInverse T hinj
  have hg : ∀ u f, (u, f) ∈ A.graph ↔ T f = u := rangeInverse_graph T hinj
  have huq (f : L2 𝕜) (v : Space 𝕜 p)
      (hv : ∀ w : Space 𝕜 p, energyForm w v = ⟪value w, f⟫_𝕜) : v = S f :=
    (weighted_variational_solvability 𝕜 p hp f).unique hv (hS f)
  have hdifferential : ∀ u f : L2 𝕜, (u, f) ∈ A.graph ↔
      ∃ v : Space 𝕜 p, value v = u ∧ DistributionEquation v f := by
    intro u f
    constructor
    · intro h
      exact ⟨S f, (hg u f).mp h,
        (form_distribution_equivalence 𝕜 p (S f) f).mpr (hS f)⟩
    · rintro ⟨v, hv, he⟩
      apply (hg u f).mpr
      have hvS := huq f v ((form_distribution_equivalence 𝕜 p v f).mp he)
      change value (S f) = u
      rw [← hvS, hv]
  refine ⟨T, (fun f => ⟨S f, rfl, hS f⟩), hself, hpos, hinj, hdense,
    A, hg, hdense, rangeInverse_selfAdjoint T hinj hdense hs, ?_, hdifferential, ?_⟩
  · intro x
    have he : value (S (A x)) = (x : L2 𝕜) := rangeInverse_right T hinj x
    rw [← he, ← hS (A x) (S (A x)), energyForm_diagonal]
    positivity
  · intro u
    change u ∈ T.range ↔ _
    constructor
    · rintro ⟨f, hf⟩
      exact ⟨S f, hf, f, (form_distribution_equivalence 𝕜 p (S f) f).mpr (hS f)⟩
    · rintro ⟨v, hv, f, he⟩
      refine ⟨f, ?_⟩
      change value (S f) = u
      rw [← huq f v ((form_distribution_equivalence 𝕜 p v f).mp he), hv]

end ExpandedFA.Models.ConfiningSchrodingerRealization
