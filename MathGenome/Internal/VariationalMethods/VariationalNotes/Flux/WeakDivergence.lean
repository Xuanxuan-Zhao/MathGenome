import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.WeakDivergence
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.Spaces
import MathGenome.Internal.VariationalMethods.VariationalNotes.Flux.LpDuality

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory TopologicalSpace Set
open scoped ENNReal InnerProductSpace

namespace VariationalNotes.Flux.WeakDivergence
open VariationalNotes.Sobolev WeakDivergenceSpec

abbrev gradientOperator : Expected.GradientType := @gradientMap
abbrev adjointOperator : Expected.AdjointType := @adjointMap
abbrev fluxAdjointOperator : Expected.FluxAdjointType := @fluxAdjoint

theorem gradient_formula : Expected.GradientFormula := by
  intro d Ω p v
  have h := (rowIsometry d).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL
    (p := p.ennreal) (μ := domainMeasure Ω) (gradient Ω 1 p v.val)
  filter_upwards [h] with x hx
  intro j
  exact congrArg (fun a : Domain d => a j) hx

variable {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent)

theorem mem_smooth_iff (w : W1p Ω 1 p) :
    w ∈ smoothSubmodule Ω 1 p ↔
      ∃ φ : P102.U4.TestSpace ℝ Ω,
        coordinateLp Ω p (0 : Fin 1) (value Ω 1 p w) = P102.U4.testToDomainLp Ω p.ennreal φ := by
  simp only [smoothSubmodule, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.mem_range, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  constructor
  · intro h
    obtain ⟨φ,hφ⟩ := h 0
    exact ⟨φ,hφ.symm⟩
  · rintro ⟨φ,hφ⟩ i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact ⟨φ,hφ.symm⟩

theorem test_class_exists_unique (φ : P102.U4.TestSpace ℝ Ω) :
    ∃! v : X Ω p, IsTestClass Ω p φ v := by
  obtain ⟨w, hw⟩ := smooth_inclusion (m := 1) Ω p (fun _ => φ)
  have hs : w ∈ smoothSubmodule Ω 1 p := (mem_smooth_iff Ω p w).mpr ⟨φ,hw 0⟩
  refine ⟨⟨w, (smoothSubmodule Ω 1 p).le_topologicalClosure hs⟩, hw 0, ?_⟩
  intro v hv
  apply Subtype.ext
  apply value_injective Ω p
  apply coordinateLp_ext Ω p
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  exact hv.trans (hw 0).symm

theorem test_class_derivative (φ : P102.U4.TestSpace ℝ Ω) (v : X Ω p)
    (hv : IsTestClass Ω p φ v) (j : Fin d) :
    coordinateLp Ω p (0,j) (gradient Ω 1 p v.val) =
      P102.U4.testToDomainLp Ω p.ennreal (P102.U4.testPartialWord Ω [j] φ) := by
  apply P102.U4.regularLp_injective Ω p.ennreal
  dsimp only
  rw [← distribution_derivative Ω p v.val 0 j, hv,
    P102.U4.regular_testToDomainLp, P102.U4.regular_testToDomainLp]
  rw [P102.U4.derivative_classicalCompatibility d ℝ Ω {j} φ
    (φ.contDiff.of_le (by simp)).contDiffOn]
  congr 1
  simpa only [P102.U4.multiPartial, Multiset.sort_singleton] using
    (P102.U4.testPartialWord_coe Ω [j] φ).symm

theorem test_class_gradient (φ : P102.U4.TestSpace ℝ Ω) (v : X Ω p)
    (hv : IsTestClass Ω p φ v) :
    (gradientMap Ω p v : Domain d → Domain d) =ᵐ[domainMeasure Ω] testGradient Ω φ := by
  have hc := Filter.eventually_all.mpr (fun j : Fin d =>
    coordinateLp_ae Ω p (0,j) (gradient Ω 1 p v.val))
  have ht := Filter.eventually_all.mpr (fun j : Fin d =>
    P102.U4.testToDomainLp_ae Ω p.ennreal (P102.U4.testPartialWord Ω [j] φ))
  filter_upwards [gradient_formula Ω p v, hc, ht] with x hx hcx htx
  apply PiLp.ext
  intro j
  exact (hx j).trans ((hcx j).symm.trans
    ((congrArg (fun f : P102.U4.DomainLp ℝ Ω p.ennreal => f x)
      (test_class_derivative Ω p φ v hv j)).trans (htx j)))

theorem smooth_tests : Expected.SmoothTests := by
  intro d Ω p φ
  exact ⟨test_class_exists_unique Ω p φ, test_class_gradient Ω p φ⟩

theorem test_density : Expected.TestDensity := by
  intro d Ω p
  have himage : (Subtype.val '' {v : X Ω p | ∃ φ, IsTestClass Ω p φ v}) =
      (smoothSubmodule Ω 1 p : Set (W1p Ω 1 p)) := by
    ext w
    constructor
    · rintro ⟨v, ⟨φ,hφ⟩, rfl⟩
      exact (mem_smooth_iff Ω p v.val).mpr ⟨φ,hφ⟩
    · intro hw
      obtain ⟨φ,hφ⟩ := (mem_smooth_iff Ω p w).mp hw
      exact ⟨⟨w,(smoothSubmodule Ω 1 p).le_topologicalClosure hw⟩, ⟨φ,hφ⟩,rfl⟩
  apply Set.eq_univ_of_forall
  intro v
  apply closure_subtype.mpr
  rw [himage]
  exact v.property

theorem adjoint_formula : Expected.AdjointFormula := by
  intro d Ω p hp σ v
  have hint := (innerSL ℝ (E := Domain d)).memLp_of_bilin 1
    (Lp.memLp σ) (Lp.memLp (gradientMap Ω p v))
  refine ⟨memLp_one_iff_integrable.mp hint, ?_⟩
  exact (innerSL ℝ (E := Domain d)).lpPairing_eq_integral σ (gradientMap Ω p v)

theorem duality_adjoint : Expected.DualityAdjoint := by
  intro d hd Ω hΩ p hp
  obtain ⟨T,hT,-,-⟩ := LpDuality.isometric_duality d hd (Ω : Set (Domain d))
    Ω.isOpen.measurableSet hΩ.measure_lt_top p.real hp
  refine ⟨T, fun σ v => (hT σ v).2, ?_⟩
  intro σ
  have he : fluxPairing Ω p hp σ = T σ := by
    ext v
    exact ((innerSL ℝ (E := Domain d)).lpPairing_eq_integral σ v).trans (hT σ v).2.symm
  exact congrArg (adjointMap Ω p) he

variable (hp : 1 < p.real) (σ : Flux Ω p hp)

/-- Each coordinate product is integrable by Hölder, without boundary assumptions. -/
theorem coordinate_test_integrable (φ : P102.U4.TestSpace ℝ Ω) (j : Fin d) :
    Integrable (fun x => σ x j * P102.U4.testPartialWord Ω [j] φ x) (domainMeasure Ω) := by
  have hσ := Lp.memLp (coordinateLp Ω (conjugate p hp) j σ)
  have hφ := (P102.U4.testPartialWord Ω [j] φ).continuous.memLp_of_hasCompactSupport
    (p := p.ennreal) (μ := domainMeasure Ω) (P102.U4.testPartialWord Ω [j] φ).hasCompactSupport
  have hi := memLp_one_iff_integrable.mp
    ((ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin 1 hσ hφ)
  apply hi.congr
  filter_upwards [coordinateLp_ae Ω (conjugate p hp) j σ] with x hx
  exact congrArg (fun z : ℝ => z * P102.U4.testPartialWord Ω [j] φ x) hx

theorem divergence_formula : Expected.DivergenceFormula := by
  intro d Ω p hp σ φ
  have hj (j : Fin d) :
      P102.U4.distributionPartial {j}
        (P102.U4.regularDistribution Ω (coordinateLp Ω (conjugate p hp) j σ)) φ =
      -(∫ x, σ x j * P102.U4.testPartialWord Ω [j] φ x ∂domainMeasure Ω) := by
    simp only [P102.U4.distributionPartial, Multiset.card_singleton, pow_one,
      Multiset.sort_singleton, neg_smul, one_smul]
    change -(P102.U4.regularDistribution Ω (coordinateLp Ω (conjugate p hp) j σ)
      (P102.U4.testPartialWord Ω [j] φ)) = _
    rw [P102.U4.regularLp_pairing, P102.U4.lpTestPairing_eq_integral]
    congr 1
    apply integral_congr_ae
    filter_upwards [coordinateLp_ae Ω (conjugate p hp) j σ] with x hx
    rw [hx]
  simp only [divergence, sum_apply, hj, Finset.sum_neg_distrib, neg_neg]
  rw [← integral_finsetSum Finset.univ (fun j _ => coordinate_test_integrable Ω p hp σ φ j)]
  congr 1
  funext x
  simp [testGradient, PiLp.inner_apply, mul_comm]

/-- Equality on smooth tests extends to W₀ by its defining norm closure. -/
theorem allVariations_iff_tests (ℓ : X Ω p →L[ℝ] ℝ) :
    AllVariations Ω p hp σ ℓ ↔ TestVariations Ω p hp σ ℓ := by
  constructor
  · intro h φ v hv
    rw [← h v]
    exact integral_congr_ae ((test_class_gradient Ω p φ v hv).mono
      (fun x hx => congrArg (fun z : Domain d => inner ℝ (σ x) z) hx.symm))
  · intro h
    have he : Set.EqOn (fluxAdjoint Ω p hp σ) ℓ
        {v : X Ω p | ∃ φ, IsTestClass Ω p φ v} := by
      rintro v ⟨φ,hφ⟩
      rw [(adjoint_formula Ω p hp σ v).2, ← h φ v hφ]
      exact integral_congr_ae ((test_class_gradient Ω p φ v hφ).mono
        (fun x hx => congrArg (fun z : Domain d => inner ℝ (σ x) z) hx))
    intro v
    rw [← (adjoint_formula Ω p hp σ v).2]
    apply he.closure (fluxAdjoint Ω p hp σ).continuous ℓ.continuous
    rw [test_density Ω p]
    trivial

theorem constraint_equivalences : Expected.ConstraintEquivalences := by
  intro d hd Ω hΩ p hp ℓ σ
  refine ⟨?_, allVariations_iff_tests Ω p hp σ ℓ, ?_⟩
  · constructor
    · intro h v
      rw [← (adjoint_formula Ω p hp σ v).2, h]
    · intro h
      ext v
      exact (adjoint_formula Ω p hp σ v).2.trans (h v)
  · simp only [TestVariations, DistributionConstraint, divergence_formula Ω p hp σ]

end VariationalNotes.Flux.WeakDivergence
