import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.PowerWeakEquation
import MathGenome.Internal.VariationalMethods.VariationalNotes.Flux.PowerEnergy
import MathGenome.Internal.VariationalMethods.VariationalNotes.Flux.ConstitutiveRelation
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.DifferentiabilityMonotonicity
import Mathlib.Analysis.InnerProductSpace.NormPow

noncomputable section
open MeasureTheory TopologicalSpace Set Filter
open scoped Topology InnerProductSpace
namespace VariationalNotes.Flux.PowerWeakEquation
open Sobolev WeakDivergenceSpec PowerEnergySpecs PowerWeakEquationSpecs

def B : {d : ℕ} → ℝ → Vector d → Vector d := @PowerWeakEquationSpecs.B

lemma B_eq_smul {d : ℕ} (p : ℝ) (z : Vector d) :
    B p z = ‖z‖ ^ (p - 2) • z := by
  by_cases hz : z = 0 <;> simp [B, PowerWeakEquationSpecs.B, hz]

lemma hasFDerivAt_energy {d : ℕ} (p : ℝ) (hp : 1 < p) (z : Vector d) :
    HasFDerivAt (energy p) (innerSL ℝ (B p z)) z := by
  have h := (hasFDerivAt_norm_rpow z hp).const_smul p⁻¹
  convert h using 1
  · ext v
    simp [PowerEnergySpecs.energy, div_eq_mul_inv, mul_comm]
  · ext v
    simp only [B_eq_smul, innerSL_apply_apply, real_inner_smul_left,
      smul_apply, smul_eq_mul]
    field_simp

/-- Differentiability at zero is supplied by the norm-power derivative theorem,
whose hypothesis is p > 1, with no p ≥ 2 restriction. -/
theorem power_subdifferential : PowerSubdifferential := by
  intro d p hp z
  have hc : ConvexAnalysis.IsConvex (fun y : Vector d => (energy p y : WithTop ℝ)) := by
    apply (ConvexAnalysis.convex_iff_twoPoint _).mpr
    intro x y r s hx hy a b ha hb hab
    have hr : energy p x = r := WithTop.coe_inj.mp hx
    have hs : energy p y = s := WithTop.coe_inj.mp hy
    apply WithTop.coe_le_coe.mpr
    rw [← hr, ← hs]
    exact (PowerEnergy.strictConvex_power d p hp).convexOn.2
      (mem_univ _) (mem_univ _) ha hb hab
  have hlocal : ∀ᶠ y in 𝓝 z,
      (energy p y : WithTop ℝ) = (energy p y : WithTop ℝ) := Eventually.of_forall fun _ => rfl
  ext w
  rw [ConstitutiveRelation.mem_fiberSubdifferential_iff]
  constructor
  · intro hw
    exact innerSL_inj.mp
      (ConvexAnalysis.subgradient_eq_of_hasFDerivAt hlocal (hasFDerivAt_energy p hp z) hw)
  · intro hw
    have hw' : w = B p z := hw
    rw [hw']
    exact ConvexAnalysis.derivative_mem_subdifferential hc hlocal (hasFDerivAt_energy p hp z)

lemma norm_B {d : ℕ} (p : ℝ) (hp : 1 < p) (z : Vector d) :
    ‖B p z‖ = ‖z‖ ^ (p - 1) := by
  by_cases hz : z = 0
  · simp [B, PowerWeakEquationSpecs.B, hz, Real.zero_rpow (by linarith : p - 1 ≠ 0)]
  · rw [B_eq_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      ← Real.rpow_add_one (norm_ne_zero_iff.mpr hz)]
    congr 1
    ring

lemma memLp_B {d : ℕ} {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : Exponent) (hp : 1 < p.real) {f : α → Vector d}
    (hf : MemLp f p.ennreal μ) :
    MemLp (fun x => B p.real (f x)) (conjugate p hp).ennreal μ := by
  have hm : AEStronglyMeasurable (fun x => B p.real (f x)) μ := by
    simp_rw [B_eq_smul]
    exact (hf.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable.smul
      hf.aestronglyMeasurable
  have h := hf.norm_rpow_div (ENNReal.ofReal (p.real - 1))
  have he : p.ennreal / ENNReal.ofReal (p.real - 1) = (conjugate p hp).ennreal := by
    exact (ENNReal.ofReal_div_of_pos (by linarith : 0 < p.real - 1)).symm
  rw [he, ENNReal.toReal_ofReal (by linarith : 0 ≤ p.real - 1)] at h
  apply h.congr_norm hm
  exact Eventually.of_forall fun x => by
    rw [norm_B p.real hp, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

theorem power_flux_integrability : PowerFluxIntegrability := by
  intro d Ω p hp u
  exact memLp_B (domainMeasure Ω) p hp (Lp.memLp _)

/-- The pointwise Fenchel gap vanishes precisely at the power constitutive law. -/
lemma pointwise_power_gap {d : ℕ} (p : ℝ) (hp : 1 < p) (z w : Vector d) :
    0 ≤ energy p z + energy (p / (p - 1)) w - inner ℝ w z ∧
    (energy p z + energy (p / (p - 1)) w - inner ℝ w z = 0 ↔ w = B p z) := by
  have hc := PowerEnergy.power_conjugate d p hp w
  have h := ConstitutiveRelation.pointwise_gap (energy p) z w
    (by rw [hc]; exact EReal.coe_ne_top _) (by rw [hc]; exact EReal.coe_ne_bot _)
  rw [hc, EReal.toReal_coe] at h
  simpa only [power_subdifferential d p hp z, mem_singleton_iff, B] using h

/-- Feasibility identifies the integrated gap with the primal minus dual value. -/
lemma integrated_gap {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (hp : 1 < p.real)
    (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ) (u : W1pZero Ω 1 p) (σ : Flux Ω p hp)
    (hσ : AllVariations Ω p hp σ ℓ) :
    let g := fun x => energy p.real (Primal.gradientMap Ω p u x) +
      energy (p.real / (p.real - 1)) (σ x) -
      inner ℝ (σ x) (Primal.gradientMap Ω p u x)
    Integrable g (domainMeasure Ω) ∧
    (∀ᵐ x ∂domainMeasure Ω, 0 ≤ g x) ∧
    (∫ x, g x ∂domainMeasure Ω) = primalObjective Ω p ℓ u - dualObjective Ω p hp σ ∧
    ((∫ x, g x ∂domainMeasure Ω) = 0 ↔ Constitutive Ω p hp u σ) := by
  dsimp only
  have hiu := PowerEnergy.integrable_energy Ω p (Primal.gradientMap Ω p u)
  have his := PowerEnergy.integrable_energy Ω (conjugate p hp) σ
  change Integrable (fun x => energy (p.real / (p.real - 1)) (σ x)) (domainMeasure Ω) at his
  have hip := (WeakDivergence.adjoint_formula Ω p hp σ u).1
  rw [← DirichletDuality.gradientMap_eq] at hip
  have hpair : (∫ x, inner ℝ (σ x) (Primal.gradientMap Ω p u x) ∂domainMeasure Ω) = ℓ u := by
    simpa only [DirichletDuality.gradientMap_eq] using hσ u
  have hi := (hiu.add his).sub hip
  have hn : ∀ᵐ x ∂domainMeasure Ω,
      0 ≤ energy p.real (Primal.gradientMap Ω p u x) +
      energy (p.real / (p.real - 1)) (σ x) -
      inner ℝ (σ x) (Primal.gradientMap Ω p u x) :=
    Eventually.of_forall fun x => (pointwise_power_gap p.real hp _ _).1
  refine ⟨hi, hn, ?_, ?_⟩
  · have hsub := integral_sub (hiu.add his) hip
    have hadd := integral_add hiu his
    simp only [Pi.add_apply] at hsub hadd
    rw [hsub, hadd, hpair]
    unfold primalObjective dualObjective
    ring
  · rw [integral_eq_zero_iff_of_nonneg_ae hn hi]
    apply Filter.eventually_congr
    exact Eventually.of_forall fun x => (pointwise_power_gap p.real hp _ _).2

/-- The representative form of the weak equation is equivalent to the original
Lp flux constraint whenever the constitutive identity holds a.e. -/
lemma feasible_iff_weak {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (hp : 1 < p.real)
    (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ) (u : W1pZero Ω 1 p) (σ : Flux Ω p hp)
    (hc : Constitutive Ω p hp u σ) :
    AllVariations Ω p hp σ ℓ ↔ WeakSolution Ω p ℓ u := by
  have he (v : W1pZero Ω 1 p) :
      (∫ x, inner ℝ (σ x) (WeakDivergenceSpec.gradientMap Ω p v x) ∂domainMeasure Ω) =
      ∫ x, inner ℝ (B p.real (Primal.gradientMap Ω p u x))
        (Primal.gradientMap Ω p v x) ∂domainMeasure Ω := by
    rw [← DirichletDuality.gradientMap_eq]
    apply integral_congr_ae
    filter_upwards [hc] with x hx
    rw [hx]
    rfl
  simp only [AllVariations, WeakSolution, he, B]

/-- Simultaneous power optimality, feasibility, and the weak p-Laplace equation. -/
theorem power_optimality : PowerOptimality := by
  intro d hd Ω hΩ p hp ℓ u σ
  have hfirst : OptimalPair Ω p hp ℓ u σ ↔
      AllVariations Ω p hp σ ℓ ∧ Constitutive Ω p hp u σ := by
    constructor
    · rintro ⟨hu, hσ, hs⟩
      refine ⟨hσ, ?_⟩
      obtain ⟨_, _, _, m, u₀, σ₀, hu₀, hmin, hσ₀, hval, hmax, _⟩ :=
        PowerEnergy.power_flux hd Ω hΩ p hp ℓ
      have h₁ := hu u₀
      have h₂ := hs σ₀ hσ₀
      have h₃ := hmin u
      have h₄ := hmax σ hσ
      have hg := integrated_gap Ω p hp ℓ u σ hσ
      apply hg.2.2.2.mp
      rw [hg.2.2.1]
      linarith
    · rintro ⟨hσ, hc⟩
      have hg := integrated_gap Ω p hp ℓ u σ hσ
      have he := hg.2.2.2.mpr hc
      rw [hg.2.2.1] at he
      refine ⟨?_, hσ, ?_⟩
      · intro v
        have hv := integrated_gap Ω p hp ℓ v σ hσ
        have hn := integral_nonneg_of_ae hv.2.1
        rw [hv.2.2.1] at hn
        linarith
      · intro τ hτ
        have ht := integrated_gap Ω p hp ℓ u τ hτ
        have hn := integral_nonneg_of_ae ht.2.1
        rw [ht.2.2.1] at hn
        linarith
  refine ⟨hfirst, hfirst.trans ?_⟩
  constructor
  · rintro ⟨hf, hc⟩
    exact ⟨(feasible_iff_weak Ω p hp ℓ u σ hc).mp hf, hc⟩
  · rintro ⟨hw, hc⟩
    exact ⟨(feasible_iff_weak Ω p hp ℓ u σ hc).mpr hw, hc⟩

/-- A genuine Lp class representing the nonlinear gradient exists before
any feasibility or optimality hypothesis is imposed. -/
lemma exists_constitutive_flux {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (hp : 1 < p.real) (u : W1pZero Ω 1 p) :
    ∃ σ : Flux Ω p hp, Constitutive Ω p hp u σ := by
  let h := power_flux_integrability Ω p hp u
  exact ⟨h.toLp _, h.coeFn_toLp⟩

/-- Existence, the converse from weak solutions, and uniqueness for every load. -/
theorem power_weak_solutions : PowerWeakSolutions := by
  intro d hd Ω hΩ p hp ℓ
  have hopt := power_optimality hd Ω hΩ p hp ℓ
  obtain ⟨_, _, _, m, u₀, σ₀, hu₀, hmin, hσ₀, hval, hmax, _⟩ :=
    PowerEnergy.power_flux hd Ω hΩ p hp ℓ
  have hu₀min : ∀ v, primalObjective Ω p ℓ u₀ ≤ primalObjective Ω p ℓ v := by
    rw [hu₀]
    exact hmin
  have h₀pair : OptimalPair Ω p hp ℓ u₀ σ₀ := ⟨hu₀min, hσ₀, by simpa [hval] using hmax⟩
  have h₀weak : WeakSolution Ω p ℓ u₀ := ((hopt u₀ σ₀).2.mp h₀pair).1
  have hweak_min (u : W1pZero Ω 1 p) (hu : WeakSolution Ω p ℓ u) :
      ∀ v, primalObjective Ω p ℓ u ≤ primalObjective Ω p ℓ v := by
    obtain ⟨σ, hc⟩ := exists_constitutive_flux Ω p hp u
    exact ((hopt u σ).2.mpr ⟨hu, hc⟩).1
  refine ⟨⟨u₀, h₀weak, ?_⟩, ?_⟩
  · intro u hu
    exact PowerEnergy.power_minimizer_unique hd Ω hΩ p hp ℓ (hweak_min u hu) hu₀min
  · intro u
    refine ⟨⟨hweak_min u, ?_⟩, ?_⟩
    · intro hu
      have he := PowerEnergy.power_minimizer_unique hd Ω hΩ p hp ℓ hu hu₀min
      simpa [he] using h₀weak
    · intro hu
      refine ⟨?_, ?_⟩
      · intro v hv
        exact PowerEnergy.power_minimizer_unique hd Ω hΩ p hp ℓ hv (hweak_min u hu)
      · obtain ⟨σ, hc⟩ := exists_constitutive_flux Ω p hp u
        exact ⟨σ, (hopt u σ).2.mpr ⟨hu, hc⟩, hc⟩

end VariationalNotes.Flux.PowerWeakEquation
