import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.ContinuousFunctionCharacters
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.Characters
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.SpecificLimits.Basic
import MathGenome.ODEDynamics.Topics.D13Unified.Ch06

noncomputable section
namespace ExpandedFA.BanachAlgebra.ContinuousFunctionCharacters
open Specs.ExpandedFA.BanachAlgebra.ContinuousFunctionCharacters
universe u

local instance (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A] :
    TopologicalSpace (Character ℂ A) := Characters.characterTopology A

/-- The native compact-space evaluation homeomorphism, transported to the
manuscript's algebraic characters with their evaluation topology. -/
def compactEvaluationHomeomorph (K : Type u) [TopologicalSpace K]
    [CompactSpace K] [T2Space K] :
    K ≃ₜ Character ℂ C(K, ℂ) :=
  (WeakDual.CharacterSpace.homeoEval K ℂ).trans
    (Characters.characterHomeomorph C(K, ℂ)).symm

@[simp] theorem compactEvaluationHomeomorph_apply (K : Type u) [TopologicalSpace K]
    [CompactSpace K] [T2Space K] (x : K) (f : C(K, ℂ)) :
    (compactEvaluationHomeomorph K x).val f = f x := rfl

theorem compact_evaluation_homeomorphism : CompactEvaluationHomeomorphism.{u} := by
  intro K _ _ _
  exact ⟨compactEvaluationHomeomorph K, fun _ _ => rfl⟩

theorem compact_characters_are_evaluations : CompactCharactersAreEvaluations.{u} := by
  intro K _ _ _ χ
  let e := compactEvaluationHomeomorph K
  refine ⟨e.symm χ, ?_, ?_⟩
  · intro f
    have h := congrArg (fun ψ : Character ℂ C(K, ℂ) => ψ.val f) (e.apply_symm_apply χ)
    exact h.symm
  · intro x hx
    apply e.injective
    apply Subtype.ext
    apply LinearMap.ext
    intro f
    calc
      (e x).val f = f x := rfl
      _ = χ.val f := (hx f).symm
      _ = (e (e.symm χ)).val f :=
        (congrArg (fun ψ : Character ℂ C(K, ℂ) => ψ.val f)
          (e.apply_symm_apply χ)).symm

theorem empty_compact_case : EmptyCompactCase.{u} := by
  intro K _ _ _ _
  refine ⟨inferInstance, ⟨fun χ => ?_⟩⟩
  exact isEmptyElim ((compactEvaluationHomeomorph K).symm χ)

/-- Evaluation restricted to the uniform polynomial algebra. -/
def polydiskEvalAlgHom (n : ℕ) (z : ClosedPolydisk n) :
    polynomialUniformAlgebra n →ₐ[ℂ] ℂ :=
  (ContinuousMap.evalAlgHom ℂ ℂ z).comp (polynomialUniformAlgebra n).val

def polydiskEvaluationCharacter (n : ℕ) (z : ClosedPolydisk n) :
    Character ℂ (polynomialUniformAlgebra n) :=
  ⟨(polydiskEvalAlgHom n z).toLinearMap, by
    refine ⟨?_, fun f g => map_mul (polydiskEvalAlgHom n z) f g⟩
    intro h
    have hh := LinearMap.congr_fun h 1
    simp at hh⟩

/-- The coordinate values of any algebraic character lie in the closed polydisk. -/
def polydiskCharacterPoint (n : ℕ) (χ : Character ℂ (polynomialUniformAlgebra n)) :
    ClosedPolydisk n :=
  ⟨fun j => χ.val (polynomialCoordinate n j), by
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    refine (AlgHom.norm_apply_le_self (Characters.characterAlgHom χ) _).trans ?_
    change ‖polydiskCoordinate n j‖ ≤ 1
    apply (ContinuousMap.norm_le _ zero_le_one).mpr
    intro z
    exact (norm_le_pi_norm z.val j).trans (mem_closedBall_zero_iff.mp z.property)⟩

/-- Agreement on coordinates extends first to polynomials and then, by automatic
continuity, to their uniform closure. -/
theorem polydisk_character_apply (n : ℕ)
    (χ : Character ℂ (polynomialUniformAlgebra n)) (f : polynomialUniformAlgebra n) :
    χ.val f = f.val (polydiskCharacterPoint n χ) := by
  let i : polydiskPolynomialFunctions n →ₐ[ℂ] polynomialUniformAlgebra n :=
    Subalgebra.inclusion (polydiskPolynomialFunctions n).le_topologicalClosure
  let φ := Characters.characterAlgHom χ
  let ψ := polydiskEvalAlgHom n (polydiskCharacterPoint n χ)
  have hpoly : φ.comp i = ψ.comp i := by
    apply AlgHom.adjoin_ext
    rintro g ⟨j, rfl⟩
    rfl
  have hdense : DenseRange i :=
    (denseRange_inclusion_iff (polydiskPolynomialFunctions n).le_topologicalClosure).mpr
      (by intro g hg; exact hg)
  have heq : (φ : polynomialUniformAlgebra n → ℂ) = ψ :=
    hdense.equalizer φ.toContinuousLinearMap.continuous
      ψ.toContinuousLinearMap.continuous (funext fun g => DFunLike.congr_fun hpoly g)
  exact congrFun heq f

/-- An explicit homeomorphism: the inverse reads the coordinate values. -/
def uniformPolydiskHomeomorph (n : ℕ) :
    ClosedPolydisk n ≃ₜ Character ℂ (polynomialUniformAlgebra n) where
  toFun := polydiskEvaluationCharacter n
  invFun := polydiskCharacterPoint n
  left_inv z := by apply Subtype.ext; funext j; rfl
  right_inv χ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro f
    exact (polydisk_character_apply n χ f).symm
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro f
    exact f.val.continuous
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    exact (continuous_apply (polynomialCoordinate n j)).comp continuous_induced_dom

theorem uniform_polydisk_homeomorphism : UniformPolydiskHomeomorphism := by
  intro n
  exact ⟨uniformPolydiskHomeomorph n, fun _ _ => rfl⟩

theorem uniform_polydisk_characters : UniformPolydiskCharacters := by
  intro n χ
  refine ⟨polydiskCharacterPoint n χ, fun f => polydisk_character_apply n χ f, ?_⟩
  intro z hz
  apply Subtype.ext
  funext j
  exact (hz (polynomialCoordinate n j)).symm

/-- Membership in the auxiliary algebra is precisely uniform polynomial
approximation. This does not assert density for holomorphic functions. -/
theorem polynomial_approximation_iff (n : ℕ) (f : C(ClosedPolydisk n, ℂ)) :
    f ∈ polynomialUniformAlgebra n ↔
      ∀ ε : ℝ, 0 < ε → ∃ p : MvPolynomial (Fin n) ℂ,
        ‖f - MvPolynomial.aeval (polydiskCoordinate n) p‖ < ε := by
  change f ∈ closure (polydiskPolynomialFunctions n : Set C(ClosedPolydisk n, ℂ)) ↔ _
  rw [Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨g, hg, hd⟩ := h ε hε
    rw [polydiskPolynomialFunctions, ← MvPolynomial.aeval_range] at hg
    obtain ⟨p, rfl⟩ := hg
    refine ⟨p, ?_⟩
    rw [dist_eq_norm] at hd
    exact hd
  · intro h ε hε
    obtain ⟨p, hp⟩ := h ε hε
    refine ⟨MvPolynomial.aeval (polydiskCoordinate n) p, ?_, ?_⟩
    · rw [polydiskPolynomialFunctions, ← MvPolynomial.aeval_range]
      exact ⟨p, rfl⟩
    · simpa only [dist_eq_norm] using hp

@[simp] theorem polynomial_restriction_apply (n : ℕ)
    (p : MvPolynomial (Fin n) ℂ) (z : ClosedPolydisk n) :
    MvPolynomial.aeval (polydiskCoordinate n) p z = MvPolynomial.eval z.val p := by
  change (ContinuousMap.evalAlgHom ℂ ℂ z)
    (MvPolynomial.aeval (polydiskCoordinate n) p) = _
  rw [MvPolynomial.comp_aeval_apply]
  rfl

/-- An unrestricted extension does not add any continuity hypothesis beyond
continuity of the function on the closed polydisk. -/
theorem continuousOn_of_polydisk_restriction (n : ℕ)
    (f : C(ClosedPolydisk n, ℂ)) (F : (Fin n → ℂ) → ℂ)
    (hF : ∀ z : ClosedPolydisk n, F z.val = f z) :
    ContinuousOn F (Metric.closedBall 0 1) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun z : ClosedPolydisk n => F z.val)
  have heq : (fun z : ClosedPolydisk n => F z.val) = f := funext hF
  rw [heq]
  exact f.continuous

/-- A uniform limit on a closed unit ball of entire maps is holomorphic in
its interior. The Schwarz estimate controls the Fréchet derivatives on a
smaller ball; completeness then gives their uniform limit. -/
theorem differentiableOn_uniform_limit_entire
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℕ → E → ℂ} {F : E → ℂ}
    (hf : ∀ m, Differentiable ℂ (f m))
    (hlim : TendstoUniformlyOn f F Filter.atTop (Metric.closedBall 0 1)) :
    DifferentiableOn ℂ F (Metric.ball 0 1) := by
  intro x hx
  have hxnorm : ‖x‖ < 1 := by simpa using hx
  let r : ℝ := (1 - ‖x‖) / 4
  have hr : 0 < r := by dsimp [r]; linarith
  have hsmall : ∀ y ∈ Metric.ball x r, y ∈ Metric.closedBall (0 : E) 1 := by
    intro y hy
    have hy' : ‖y - x‖ < r := by simpa [dist_eq_norm] using hy
    have hn := norm_add_le (y - x) x
    rw [sub_add_cancel] at hn
    simp only [Metric.mem_closedBall, dist_zero_right]
    dsimp [r] at hy'
    linarith
  have hlarge : ∀ y ∈ Metric.ball x r, ∀ z ∈ Metric.ball y r,
      z ∈ Metric.closedBall (0 : E) 1 := by
    intro y hy z hz
    have hy' : ‖y - x‖ < r := by simpa [dist_eq_norm] using hy
    have hz' : ‖z - y‖ < r := by simpa [dist_eq_norm] using hz
    have hn := norm_add_le (y - x) x
    have hn' := norm_add_le (z - y) y
    rw [sub_add_cancel] at hn hn'
    simp only [Metric.mem_closedBall, dist_zero_right]
    dsimp [r] at hy' hz'
    linarith
  have hc : UniformCauchySeqOn (fun m => fderiv ℂ (f m)) Filter.atTop
      (Metric.ball x r) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    let δ : ℝ := ε * r / 4
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hlim.uniformCauchySeqOn δ hδ
    refine ⟨N, fun m hm k hk y hy => ?_⟩
    have hnorm : ∀ z ∈ Metric.closedBall (0 : E) 1, ‖f m z - f k z‖ ≤ δ := by
      intro z hz
      exact le_of_lt (by simpa only [dist_eq_norm] using hN m hm k hk z hz)
    have hd := Complex.norm_fderiv_le_div_of_mapsTo_ball
      ((hf m).sub (hf k)).differentiableOn
      (R₂ := 2 * δ) (c := y) (R₁ := r) ?_ hr
    · have heq : fderiv ℂ (f m - f k) y =
          fderiv ℂ (f m) y - fderiv ℂ (f k) y :=
        ((hf m y).hasFDerivAt.sub (hf k y).hasFDerivAt).fderiv
      rw [heq] at hd
      rw [dist_eq_norm]
      apply hd.trans_lt
      dsimp [δ]
      field_simp
      nlinarith
    · intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact (norm_sub_le _ _).trans (by
        have h₁ := hnorm z (hlarge y hy z hz)
        have h₂ := hnorm y (hsmall y hy)
        change ‖f m z - f k z‖ + ‖f m y - f k y‖ ≤ _
        linarith)
  let G : E → E →L[ℂ] ℂ := fun y => Filter.limUnder Filter.atTop
    (fun m => fderiv ℂ (f m) y)
  have hG : TendstoUniformlyOn (fun m => fderiv ℂ (f m)) G Filter.atTop
      (Metric.ball x r) :=
    hc.tendstoUniformlyOn_of_tendsto (fun y hy =>
      (show CauchySeq (fun m => fderiv ℂ (f m) y) from hc.cauchy_map hy).tendsto_limUnder)
  exact (hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hG
    (fun m y _ => (hf m y).hasFDerivAt)
    (fun y hy => hlim.tendsto_at (hsmall y hy))
    (Metric.mem_ball_self hr)).differentiableAt.differentiableWithinAt

/-- Multivariate Cauchy expansion on a larger polydisk gives polynomial
approximation on each strictly smaller closed polydisk. -/
theorem polynomial_approximation_on_smaller_polydisk (n : ℕ)
    (F : (Fin n → ℂ) → ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hF : DifferentiableOn ℂ F (Metric.ball 0 R))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℂ,
      ∀ z ∈ Metric.closedBall (0 : Fin n → ℂ) r,
        ‖F z - MvPolynomial.eval z p‖ < ε := by
  let S := (r + R) / 2
  have hS : 0 < S := by dsimp [S]; linarith
  have hSr : r < S := by dsimp [S]; linarith
  have hSR : S < R := by dsimp [S]; linarith
  let T := (S + R) / 2
  have hST : S < T := by dsimp [T]; linarith
  have hTR : T < R := by dsimp [T]; linarith
  have hT : 0 < T := hS.trans hST
  have hclosed : Metric.closedBall (0 : Fin n → ℂ) T ⊆ Metric.ball 0 R :=
    Metric.closedBall_subset_ball hTR
  have hline : ∀ a v : Fin n → ℂ,
      AnalyticOnNhd ℂ (F ∘ D13Unified.Ch06.HolomorphicLimits.affineLine a v)
        (D13Unified.Ch06.HolomorphicLimits.affineLine a v ⁻¹' Metric.ball 0 R) := by
    intro a v
    apply DifferentiableOn.analyticOnNhd _
      (Metric.isOpen_ball.preimage (D13Unified.Ch06.HolomorphicLimits.continuous_affineLine a v))
    exact hF.comp (fun z _ =>
      (differentiable_const a |>.add (differentiable_id.smul_const v)) z |>.differentiableWithinAt)
      (fun _ hz => hz)
  obtain ⟨c, hc⟩ := D13Unified.Ch06.HolomorphicLimits.coordinate_series_of_torus_cauchy
    (0 : Fin n → ℂ) hT (hF.continuousOn.mono hclosed)
    (fun z hz => D13Unified.Ch06.HolomorphicLimits.torus_cauchy_of_lineAnalytic n
      Metric.isOpen_ball hF.continuousOn hline 0 hT hclosed z hz)
  let q : Fin n → ℂ := fun _ => (S : ℂ)
  have hq : q ∈ Metric.ball (0 : Fin n → ℂ) T := by
    rw [Metric.mem_ball, dist_zero_right]
    apply lt_of_le_of_lt _ hST
    apply (pi_norm_le_iff_of_nonneg hS.le).mpr
    intro j
    simp [q, abs_of_pos hS]
  let u : (Fin n → ℕ) → ℝ := fun α => ‖c α * ∏ j, (q j - 0) ^ α j‖
  have hu : Summable u := (hc q hq).1
  have hub : ∀ α z, z ∈ Metric.closedBall (0 : Fin n → ℂ) r →
      ‖c α * ∏ j, (z j - 0) ^ α j‖ ≤ u α := by
    intro α z hz
    dsimp [u]
    simp only [norm_mul, norm_prod, norm_pow]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
    intro j _
    have hj : ‖z j‖ ≤ S := (norm_le_pi_norm z j).trans
      ((by simpa using hz : ‖z‖ ≤ r).trans hSr.le)
    simpa [q, abs_of_pos hS] using pow_le_pow_left₀ (norm_nonneg _) hj (α j)
  have ht := tendstoUniformlyOn_tsum hu hub
  have htF : TendstoUniformlyOn
      (fun s : Finset (Fin n → ℕ) => fun z : Fin n → ℂ =>
        ∑ α ∈ s, c α * ∏ j, (z j - 0) ^ α j) F Filter.atTop
      (Metric.closedBall 0 r) := by
    apply ht.congr_right
    intro z hz
    exact (hc z (Metric.closedBall_subset_ball (hSr.trans hST) hz)).2.tsum_eq
  obtain ⟨s, hs⟩ := (Metric.tendstoUniformlyOn_iff.mp htF ε hε).exists
  refine ⟨∑ α ∈ s, MvPolynomial.C (c α) *
    ∏ j : Fin n, MvPolynomial.X j ^ α j, ?_⟩
  intro z hz
  simpa only [dist_eq_norm, map_sum, map_mul, map_prod, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, sub_zero] using hs z hz

/-- Polynomial uniform limits satisfy the actual Fréchet holomorphy
condition in every finite dimension, including zero. -/
theorem ambient_polynomial_uniform_limit : AmbientPolynomialUniformLimit := by
  intro n F _hF happ
  have hpos : ∀ m : ℕ, 0 < 1 / ((m : ℝ) + 1) := fun m => by positivity
  choose p hp using fun m : ℕ => happ (1 / ((m : ℝ) + 1)) (hpos m)
  apply differentiableOn_uniform_limit_entire
    (f := fun m z => MvPolynomial.eval z (p m))
  · intro m z
    exact (AnalyticOnNhd.eval_mvPolynomial (p m) z (Set.mem_univ z)).differentiableAt
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (gt_mem_nhds hε)] with m hm
    intro z hz
    rw [dist_eq_norm]
    exact (hp m z hz).trans hm

/-- Dilation approaches the identity uniformly on the closed polydisk;
the Cauchy expansion then gives polynomial approximation with no boundary
smoothness assumption. -/
theorem ambient_polynomial_approximation : AmbientPolynomialApproximation := by
  intro n F hcont hdiff ε hε
  have hu := (isCompact_closedBall (0 : Fin n → ℂ) 1).uniformContinuousOn_of_continuous hcont
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / 2) (half_pos hε)
  let η : ℝ := min (δ / 2) (1 / 2)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηδ : η < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hηhalf : η ≤ 1 / 2 := min_le_right _ _
  let r : ℝ := 1 - η
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  obtain ⟨p, hp⟩ := polynomial_approximation_on_smaller_polydisk n F hr.le hr1
    hdiff (ε / 2) (half_pos hε)
  refine ⟨MvPolynomial.eval₂ MvPolynomial.C
    (fun j => MvPolynomial.C (r : ℂ) * MvPolynomial.X j) p, ?_⟩
  intro z hz
  have hznorm : ‖z‖ ≤ 1 := by simpa using hz
  have hrs : ‖(r : ℂ) • z‖ ≤ r := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_of_le_one_right hr.le hznorm
  have hscaled : (r : ℂ) • z ∈ Metric.closedBall (0 : Fin n → ℂ) r := by
    simpa using hrs
  have hscaled1 : (r : ℂ) • z ∈ Metric.closedBall (0 : Fin n → ℂ) 1 :=
    Metric.closedBall_subset_closedBall hr1.le hscaled
  have hdist : dist z ((r : ℂ) • z) < δ := by
    rw [dist_eq_norm]
    nth_rw 1 [← one_smul ℂ z]
    rw [← sub_smul, norm_smul]
    have heq : (1 : ℂ) - (r : ℂ) = (η : ℂ) := by
      dsimp [r]
      push_cast
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
    exact (mul_le_of_le_one_right hη.le hznorm).trans_lt hηδ
  have hclose : ‖F z - F ((r : ℂ) • z)‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hδF z hz ((r : ℂ) • z) hscaled1 hdist
  have heval : MvPolynomial.eval z
      (MvPolynomial.eval₂ MvPolynomial.C
        (fun j => MvPolynomial.C (r : ℂ) * MvPolynomial.X j) p) =
      MvPolynomial.eval ((r : ℂ) • z) p := by
    rw [← MvPolynomial.eval_assoc]
    congr 2
    funext j
    simp
  rw [heval]
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans_lt
    (by have h := hp ((r : ℂ) • z) hscaled; linarith)

/-- Assembly of the two independent analytic directions, with the exact
continuous-on-the-closure, holomorphic-in-the-interior definition. -/
theorem holomorphic_density_of_analytic_results
    (ha : AmbientPolynomialApproximation) (hl : AmbientPolynomialUniformLimit) :
    HolomorphicPolynomialDensity := by
  intro n
  apply le_antisymm
  · intro f hf
    obtain ⟨F, hF, eF⟩ := hf
    apply (polynomial_approximation_iff n f).mpr
    intro ε hε
    obtain ⟨p, hp⟩ := ha n F (continuousOn_of_polydisk_restriction n f F eF)
      hF (ε / 2) (half_pos hε)
    refine ⟨p, lt_of_le_of_lt ?_ (half_lt_self hε)⟩
    apply (ContinuousMap.norm_le _ (half_pos hε).le).mpr
    intro z
    change ‖f z - MvPolynomial.aeval (polydiskCoordinate n) p z‖ ≤ ε / 2
    rw [polynomial_restriction_apply, ← eF z]
    exact (hp z.val z.property).le
  · intro f hf
    let F : (Fin n → ℂ) → ℂ :=
      Function.extend Subtype.val f (fun _ => 0)
    have eF : ∀ z : ClosedPolydisk n, F z.val = f z :=
      fun z => Function.Injective.extend_apply Subtype.val_injective f (fun _ => 0) z
    refine ⟨F, hl n F (continuousOn_of_polydisk_restriction n f F eF) ?_, eF⟩
    intro ε hε
    obtain ⟨p, hp⟩ := (polynomial_approximation_iff n f).mp hf ε hε
    refine ⟨p, ?_⟩
    intro z hz
    have hb := (f - MvPolynomial.aeval (polydiskCoordinate n) p).norm_coe_le_norm ⟨z, hz⟩
    have e := eF ⟨z, hz⟩
    simpa only [ContinuousMap.sub_apply, polynomial_restriction_apply, e] using hb.trans_lt hp

/-- Character identification transported along the analytic bridge. -/
theorem holomorphic_characters_of_density (h : HolomorphicPolynomialDensity) :
    HolomorphicPolydiskCharacters := by
  unfold HolomorphicPolydiskCharacters
  intro n
  rw [h n]
  exact uniform_polydisk_characters n

theorem holomorphic_homeomorphism_of_density (h : HolomorphicPolynomialDensity) :
    HolomorphicPolydiskHomeomorphism := by
  unfold HolomorphicPolydiskHomeomorphism
  intro n
  rw [h n]
  exact uniform_polydisk_homeomorphism n

theorem holomorphic_approximation_of_density (h : HolomorphicPolynomialDensity) :
    HolomorphicPolynomialApproximation := by
  intro n f
  apply (polynomial_approximation_iff n f.val).mp
  rw [← h n]
  exact f.property

theorem disk_characters_of_density (h : HolomorphicPolynomialDensity) : DiskCharacters :=
  holomorphic_characters_of_density h 1

/-- The one-coordinate closed polydisk is the usual scalar closed unit disk,
with the identification given by its unique coordinate. -/
def closedDiskHomeomorph : ClosedPolydisk 1 ≃ₜ ↥(Metric.closedBall (0 : ℂ) 1) where
  toFun z := ⟨z.val 0, by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_pi_norm z.val 0).trans (mem_closedBall_zero_iff.mp z.property)⟩
  invFun z := ⟨fun _ => z.val, by
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    exact mem_closedBall_zero_iff.mp z.property⟩
  left_inv z := by
    apply Subtype.ext
    funext j
    exact congrArg z.val (Subsingleton.elim (0 : Fin 1) j)
  right_inv z := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_apply (0 : Fin 1)).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun _ => continuous_subtype_val

/-- Under this disk identification, the holomorphy condition in the Specs
is exactly the ordinary one-complex-variable holomorphy condition. -/
theorem differentiableOn_one_polydisk_iff (F : (Fin 1 → ℂ) → ℂ) :
    DifferentiableOn ℂ F (Metric.ball 0 1) ↔
      DifferentiableOn ℂ (fun z : ℂ => F (fun _ => z)) (Metric.ball 0 1) := by
  constructor
  · intro h
    apply h.comp (ContinuousLinearMap.pi
      (fun _ : Fin 1 => ContinuousLinearMap.id ℂ ℂ)).differentiable.differentiableOn
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    have hz' : ‖z‖ < 1 := by simpa using hz
    apply lt_of_le_of_lt _ hz'
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
    intro j
    exact le_rfl
  · intro h
    have hmap : Set.MapsTo (fun z : Fin 1 → ℂ => z 0)
        (Metric.ball 0 1) (Metric.ball (0 : ℂ) 1) := by
      intro z hz
      rw [Metric.mem_ball, dist_zero_right]
      exact (norm_le_pi_norm z 0).trans_lt (by simpa using hz)
    have hc := h.comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).differentiable.differentiableOn
      hmap
    have he : (fun z : Fin 1 → ℂ => F (fun _ => z 0)) = F := by
      funext z
      congr 1
      funext j
      exact congrArg z (Subsingleton.elim (0 : Fin 1) j)
    exact he ▸ hc

/-- The holomorphic polydisk algebra is exactly the uniform polynomial closure. -/
theorem holomorphic_polynomial_density : HolomorphicPolynomialDensity :=
  holomorphic_density_of_analytic_results ambient_polynomial_approximation
    ambient_polynomial_uniform_limit

theorem holomorphic_polynomial_approximation : HolomorphicPolynomialApproximation :=
  holomorphic_approximation_of_density holomorphic_polynomial_density

theorem holomorphic_polydisk_characters : HolomorphicPolydiskCharacters :=
  holomorphic_characters_of_density holomorphic_polynomial_density

theorem holomorphic_polydisk_homeomorphism : HolomorphicPolydiskHomeomorphism :=
  holomorphic_homeomorphism_of_density holomorphic_polynomial_density

theorem disk_characters : DiskCharacters :=
  disk_characters_of_density holomorphic_polynomial_density

end ExpandedFA.BanachAlgebra.ContinuousFunctionCharacters
