import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.PowerEnergy
import MathGenome.Internal.VariationalMethods.VariationalNotes.Flux.DirichletDuality
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.SlabPoincare
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.InnerProductSpace.Convex

noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped InnerProductSpace
namespace VariationalNotes.Flux.PowerEnergy
open Sobolev PowerEnergySpecs

/-- Young's upper bound, with a maximizing vector in the direction of w. -/
theorem power_conjugate : PowerConjugate := by
  intro d p hp w
  let q := p / (p - 1)
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hupper (z : Vector d) : inner ℝ w z - PowerEnergySpecs.energy p z ≤ PowerEnergySpecs.energy q w := by
    have hi := real_inner_le_norm w z
    have hy := Real.young_inequality_of_nonneg (norm_nonneg z) (norm_nonneg w) hpq
    dsimp [PowerEnergySpecs.energy]
    nlinarith
  apply le_antisymm
  · exact iSup_le fun z => EReal.coe_le_coe_iff.mpr (hupper z)
  · have hex : ∃ z : Vector d, inner ℝ w z - PowerEnergySpecs.energy p z = PowerEnergySpecs.energy q w := by
      by_cases hw : w = 0
      · refine ⟨0, ?_⟩
        simp [hw, PowerEnergySpecs.energy, Real.zero_rpow hpq.pos.ne', Real.zero_rpow hpq.symm.pos.ne']
      · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
        let a := ‖w‖ ^ (1 / (p - 1))
        have ha : 0 ≤ a := Real.rpow_nonneg (norm_nonneg w) _
        let z := (a / ‖w‖) • w
        have hn : ‖z‖ = a := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha hwpos.le)]
          exact div_mul_cancel₀ a hwpos.ne'
        have hi : inner ℝ w z = a * ‖w‖ := by
          dsimp [z]
          rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
          field_simp
        have he : ‖z‖ ^ p = ‖w‖ ^ q := by
          rw [hn, ← Real.rpow_mul (norm_nonneg w)]
          congr 1
          dsimp [q]
          ring
        have hy := (Real.young_inequality_eq_iff_of_nonneg
          (norm_nonneg z) (norm_nonneg w) hpq).mpr he
        refine ⟨z, ?_⟩
        dsimp [PowerEnergySpecs.energy] at *
        rw [hi, hn] at *
        linarith
    obtain ⟨z, hz⟩ := hex
    rw [← hz]
    exact le_iSup (fun z : Vector d => ((inner ℝ w z - PowerEnergySpecs.energy p z : ℝ) : EReal)) z

/-- Equal-length vectors use strict convexity of Euclidean balls; unequal
lengths use strict convexity of the scalar power. This covers every p > 1. -/
theorem strictConvex_power : StrictConvexPower := by
  intro d p hp
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  have hn : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb] using
      norm_add_le (a • x) (b • y)
  have hpow : ‖a • x + b • y‖ ^ p < a * ‖x‖ ^ p + b * ‖y‖ ^ p := by
    by_cases he : ‖x‖ = ‖y‖
    · have ht : ‖a • x + b • y‖ < ‖x‖ :=
        norm_combo_lt_of_ne le_rfl he.symm.le hxy ha hb hab
      have ht' := Real.rpow_lt_rpow (norm_nonneg _) ht (by linarith : 0 < p)
      calc
        _ < ‖x‖ ^ p := ht'
        _ = a * ‖x‖ ^ p + b * ‖y‖ ^ p := by rw [← he, ← add_mul, hab, one_mul]
    · exact (Real.rpow_le_rpow (norm_nonneg _) hn (by linarith : 0 ≤ p)).trans_lt
        ((strictConvexOn_rpow hp).2 (norm_nonneg x) (norm_nonneg y) he ha hb hab)
  dsimp only [PowerEnergySpecs.energy]
  simp only [smul_eq_mul]
  calc
    _ < (a * ‖x‖ ^ p + b * ‖y‖ ^ p) / p :=
      div_lt_div_of_pos_right hpow (by linarith : 0 < p)
    _ = _ := by ring

/-- Power densities of genuine Lp classes are integrable. -/
lemma integrable_energy {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (f : Lp (Vector d) p.ennreal (domainMeasure Ω)) :
    Integrable (fun x => PowerEnergySpecs.energy p.real (f x)) (domainMeasure Ω) := by
  have h := (Lp.memLp f).integrable_norm_rpow
    (ne_of_gt (ENNReal.ofReal_pos.mpr p.pos)) ENNReal.ofReal_ne_top
  simpa only [Exponent.toReal, PowerEnergySpecs.energy] using h.div_const p.real

/-- Injectivity follows from the quantitative Poincaré estimate, even on an
empty or disconnected bounded open set. -/
lemma gradient_injective {d : ℕ} (hd : 0 < d) (Ω : Opens (Domain d))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent) :
    Function.Injective (Primal.gradientMap Ω p) := by
  intro u v huv
  obtain ⟨K, _, hK⟩ := bounded_gradient_control hd Ω hΩ p
  have hz : Primal.gradientMap Ω p (u - v) = 0 := by simp [huv]
  have h := hK (u - v)
  rw [hz, norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

/-- Equality in the integrated strict Jensen inequality forces the gradients
to agree a.e.; Poincaré then identifies the Sobolev classes. -/
theorem power_minimizer_unique {d : ℕ} (hd : 0 < d) (Ω : Opens (Domain d))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent) (hp : 1 < p.real)
    (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ) {u v : W1pZero Ω 1 p}
    (hu : ∀ w, primalObjective Ω p ℓ u ≤ primalObjective Ω p ℓ w)
    (hv : ∀ w, primalObjective Ω p ℓ v ≤ primalObjective Ω p ℓ w) : u = v := by
  let D := Primal.gradientMap Ω p
  let t : ℝ := 1 / 2
  let m := t • u + t • v
  have ht : 0 < t := by norm_num [t]
  have htt : t + t = 1 := by norm_num [t]
  have hrep : ∀ᵐ x ∂domainMeasure Ω, D m x = t • D u x + t • D v x := by
    have hm : D m = t • D u + t • D v := by simp [m]
    rw [hm]
    filter_upwards [Lp.coeFn_add (t • D u) (t • D v),
      Lp.coeFn_smul t (D u), Lp.coeFn_smul t (D v)] with x hx hu hv
    exact hx.trans (congrArg₂ (· + ·) hu hv)
  have hi (w : W1pZero Ω 1 p) := integrable_energy Ω p (D w)
  have hig := ((hi u).const_mul t).add ((hi v).const_mul t)
  have hle : (fun x => PowerEnergySpecs.energy p.real (D m x)) ≤ᵐ[domainMeasure Ω]
      (fun x => t * PowerEnergySpecs.energy p.real (D u x) + t * PowerEnergySpecs.energy p.real (D v x)) := by
    filter_upwards [hrep] with x hx
    rw [hx]
    exact (strictConvex_power d p.real hp).convexOn.2 (mem_univ _) (mem_univ _)
      ht.le ht.le htt
  have hload : ℓ m = t * ℓ u + t * ℓ v := by simp [m, smul_eq_mul]
  have hobj : primalObjective Ω p ℓ u = primalObjective Ω p ℓ v :=
    (hu v).antisymm (hv u)
  have hlower := hu m
  change (∫ x, PowerEnergySpecs.energy p.real (D u x) ∂domainMeasure Ω) - ℓ u ≤
    (∫ x, PowerEnergySpecs.energy p.real (D m x) ∂domainMeasure Ω) - ℓ m at hlower
  change (∫ x, PowerEnergySpecs.energy p.real (D u x) ∂domainMeasure Ω) - ℓ u =
    (∫ x, PowerEnergySpecs.energy p.real (D v x) ∂domainMeasure Ω) - ℓ v at hobj
  have heint : (∫ x, PowerEnergySpecs.energy p.real (D m x) ∂domainMeasure Ω) =
      ∫ x, t * PowerEnergySpecs.energy p.real (D u x) + t * PowerEnergySpecs.energy p.real (D v x) ∂domainMeasure Ω := by
    apply le_antisymm (integral_mono_ae (hi m) hig hle)
    simp only [Pi.add_apply]
    rw [integral_add ((hi u).const_mul t) ((hi v).const_mul t),
      integral_const_mul, integral_const_mul]
    rw [hload] at hlower
    dsimp [t] at *
    linarith
  have heae := (integral_eq_iff_of_ae_le (hi m) hig hle).mp heint
  apply gradient_injective hd Ω hΩ p
  apply Lp.ext
  filter_upwards [hrep, heae] with x hx he
  by_contra hne
  have hstrict := (strictConvex_power d p.real hp).2 (mem_univ (D u x))
    (mem_univ (D v x)) hne ht ht htt
  rw [← hx] at hstrict
  exact (ne_of_lt hstrict) he

/-- Specialize the attained flux duality theorem to the power integrand. -/
theorem power_flux : PowerFlux := by
  intro d hd Ω hΩ p hp ℓ
  let F : Domain d → Vector d → ℝ := fun _ => PowerEnergySpecs.energy p.real
  have hcont : Continuous (PowerEnergySpecs.energy (d := d) p.real) :=
    (continuous_norm.rpow_const (fun _ => Or.inr p.pos.le)).div_const p.real
  have hF : Sobolev.Caratheodory (domainMeasure Ω) F :=
    ⟨fun _ => measurable_const, Filter.Eventually.of_forall (fun _ => hcont)⟩
  have hg : IntegralRegularitySpecs.TwoSidedPGrowth (domainMeasure Ω) p.ennreal F := by
    refine ⟨1 / p.real, 1 / p.real, 0, one_div_pos.mpr p.pos,
      (one_div_pos.mpr p.pos).le, integrable_zero _ _ _,
      Filter.Eventually.of_forall (fun _ => le_rfl), ?_⟩
    apply Filter.Eventually.of_forall
    intro x z
    simp [F, PowerEnergySpecs.energy, div_eq_mul_inv, mul_comm]
  have hc : ∀ᵐ x ∂domainMeasure Ω, ConvexOn ℝ univ (F x) :=
    Filter.Eventually.of_forall (fun _ => (strictConvex_power d p.real hp).convexOn)
  have hconj (x : Domain d) (w : Vector d) :
      IntegralConjugacySpecs.pointwiseConjugate F x w =
      (PowerEnergySpecs.energy (p.real / (p.real - 1)) w : EReal) := by
    exact power_conjugate d p.real hp w
  obtain ⟨_, u, σ, hu, hσ, hval, hbound⟩ :=
    DirichletDuality.ambient_duality hd Ω hΩ p hp F ℓ hF hg hc
  have hJ : Primal.objective Ω p F ℓ = primalObjective Ω p ℓ := rfl
  have hH (τ : WeakDivergenceSpec.Flux Ω p hp) :
      -(∫ x, (IntegralConjugacySpecs.pointwiseConjugate F x (τ x)).toReal
        ∂domainMeasure Ω) = dualObjective Ω p hp τ := by
    simp only [hconj, EReal.toReal_coe]
    rfl
  rw [hJ] at hu hval hbound
  simp only [hH] at hval hbound
  refine ⟨fun v => integrable_energy Ω p _, ?_, ?_,
    primalObjective Ω p ℓ u, u, σ, rfl, ?_, hσ, hval, hbound, ?_, hu, ?_⟩
  · intro τ
    exact integrable_energy Ω (WeakDivergenceSpec.conjugate p hp) τ
  · intro τ
    obtain ⟨_, h₁, h₂⟩ := WeakDivergence.constraint_equivalences d hd Ω hΩ p hp ℓ τ
    exact h₁.trans h₂
  · intro v
    exact hu.1 ⟨v, rfl⟩
  · intro v hv
    exact power_minimizer_unique hd Ω hΩ p hp ℓ hv (fun w => hu.1 ⟨w, rfl⟩)
  · constructor
    · rintro b ⟨τ, hτ, rfl⟩
      exact hbound τ hτ
    · intro b hb
      rw [← hval]
      exact hb ⟨σ, hσ, rfl⟩

end VariationalNotes.Flux.PowerEnergy
