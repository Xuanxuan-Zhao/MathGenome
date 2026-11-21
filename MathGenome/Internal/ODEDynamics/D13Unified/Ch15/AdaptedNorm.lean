import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.AdaptedNorm
import MathGenome.Internal.ODEDynamics.D13Unified.Ch08.MatrixPowerCriteria
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Module
open scoped Matrix.Norms.Operator ENNReal NNReal
open D13Unified.Ch08.MatrixPowerCriteria
namespace D13Unified.Ch15.AdaptedNorm

section Construction
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma inducedNorm_le (p : Seminorm 𝕜 E) (A : Module.End 𝕜 E) (a : ℝ)
    (ha : 0 ≤ a) (h : ∀ v, p (A v) ≤ a * p v) : inducedNorm p A ≤ a := by
  apply csSup_le
  · exact ⟨0, 0, by simp, by simp⟩
  · rintro r ⟨v, hv, rfl⟩
    exact (h v).trans ((mul_le_mul_of_nonneg_left hv ha).trans_eq (mul_one a))

/-- The supremum of the rescaled forward orbit gives an adapted norm. -/
lemma adapted_of_power_bound (A : Module.End 𝕜 E) (a C : ℝ) (ha : 0 < a) (hC : 0 < C)
    (hpow : ∀ n : ℕ, ∀ v : E, ‖(A ^ n) v‖ ≤ C * a ^ n * ‖v‖) :
    ∃ p : Seminorm 𝕜 E, Equivalent p ∧ ∀ v, p (A v) ≤ a * p v := by
  let f (v : E) (n : ℕ) : ℝ := ‖(A ^ n) v‖ / a ^ n
  have hbound (v : E) : BddAbove (Set.range (f v)) := by
    refine ⟨C * ‖v‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (div_le_iff₀ (pow_pos ha n)).mpr (by simpa [mul_assoc, mul_comm, mul_left_comm] using hpow n v)
  let q (v : E) : ℝ := ⨆ n, f v n
  have hle (v : E) (n : ℕ) : f v n ≤ q v := le_ciSup (hbound v) n
  have hnorm (v : E) : ‖v‖ ≤ q v := by simpa [f] using hle v 0
  have hupper (v : E) : q v ≤ C * ‖v‖ := by
    apply ciSup_le
    intro n
    exact (div_le_iff₀ (pow_pos ha n)).mpr (by simpa [mul_assoc, mul_comm, mul_left_comm] using hpow n v)
  have hzero : q 0 = 0 := by simp [q, f]
  have hadd (v w : E) : q (v + w) ≤ q v + q w := by
    apply ciSup_le
    intro n
    calc
      f (v + w) n ≤ f v n + f w n := by
        dsimp [f]
        rw [map_add, ← add_div]
        exact div_le_div_of_nonneg_right (norm_add_le _ _) (pow_pos ha n).le
      _ ≤ q v + q w := add_le_add (hle v n) (hle w n)
  have hsmul (c : 𝕜) (v : E) : q (c • v) ≤ ‖c‖ * q v := by
    apply ciSup_le
    intro n
    calc
      f (c • v) n = ‖c‖ * f v n := by simp [f, norm_smul, mul_div_assoc]
      _ ≤ ‖c‖ * q v := mul_le_mul_of_nonneg_left (hle v n) (norm_nonneg _)
  let p : Seminorm 𝕜 E := Seminorm.ofSMulLE q hzero hadd hsmul
  refine ⟨p, ⟨1, zero_lt_one, C, hC, fun v => ?_⟩, ?_⟩
  · exact ⟨by change ‖v‖ ≤ 1 * q v; simpa using hnorm v, hupper v⟩
  · intro v
    change q (A v) ≤ a * q v
    apply ciSup_le
    intro n
    calc
      f (A v) n = a * f v (n + 1) := by
        dsimp [f]
        rw [pow_succ, Module.End.mul_apply]
        field_simp
        rw [pow_succ]
        ring
      _ ≤ a * q v := mul_le_mul_of_nonneg_left (hle v (n + 1)) ha.le

/-- Pull back an equivalent norm along a continuous linear coordinate map. -/
lemma equivalent_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] F) (p : Seminorm 𝕜 F) (hp : Equivalent p) :
    Equivalent (p.comp e.toLinearMap) := by
  obtain ⟨C, hC, D, hD, h⟩ := hp
  refine ⟨(‖e.symm.toContinuousLinearMap‖ + 1) * C, by positivity,
    D * (‖e.toContinuousLinearMap‖ + 1), by positivity, fun v => ?_⟩
  change ‖v‖ ≤ (‖e.symm.toContinuousLinearMap‖ + 1) * C * p (e v) ∧
    p (e v) ≤ D * (‖e.toContinuousLinearMap‖ + 1) * ‖v‖
  constructor
  · calc
      ‖v‖ = ‖e.symm (e v)‖ := by rw [e.symm_apply_apply]
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e v‖ := ContinuousLinearMap.le_opNorm e.symm.toContinuousLinearMap (e v)
      _ ≤ (‖e.symm.toContinuousLinearMap‖ + 1) * (C * p (e v)) :=
        mul_le_mul (by linarith) (h (e v)).1 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · calc
      p (e v) ≤ D * ‖e v‖ := (h (e v)).2
      _ ≤ D * (‖e.toContinuousLinearMap‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm e.toContinuousLinearMap v) hD.le
      _ ≤ _ := by nlinarith [norm_nonneg e.toContinuousLinearMap, norm_nonneg v]

lemma matrix_adapted {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    (M : Matrix (Fin d) (Fin d) 𝕜) (a C : ℝ) (ha : 0 < a) (hC : 0 < C)
    (hpow : ∀ n : ℕ, ‖M ^ n‖ ≤ C * a ^ n) :
    ∃ p : Seminorm 𝕜 (Fin d → 𝕜), Equivalent p ∧ ∀ v, p (M.mulVec v) ≤ a * p v := by
  apply adapted_of_power_bound M.toLin' a C ha hC
  intro n v
  have h := (Matrix.linfty_opNorm_mulVec (M ^ n) v).trans
    (mul_le_mul_of_nonneg_right (hpow n) (norm_nonneg v))
  simpa only [← Matrix.toLin'_pow, Matrix.toLin'_apply] using h

lemma pullback_adapted [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] {d : ℕ}
    (b : Basis (Fin d) 𝕜 E) (A : Module.End 𝕜 E) (a : ℝ)
    (p : Seminorm 𝕜 (Fin d → 𝕜)) (hp : Equivalent p)
    (hA : ∀ v, p ((LinearMap.toMatrix b b A).mulVec v) ≤ a * p v) :
    ∃ q : Seminorm 𝕜 E, Equivalent q ∧ ∀ v, q (A v) ≤ a * q v := by
  refine ⟨p.comp b.equivFun.toLinearMap, equivalent_comp b.equivFunL p hp, ?_⟩
  intro v
  simpa only [Seminorm.comp_apply, LinearEquiv.coe_coe, Basis.equivFun_apply,
    LinearMap.toMatrix_mulVec_repr] using hA (b.equivFun v)

end Construction

theorem upperComplex : Specs.D13Unified.Ch15.AdaptedNorm.upperComplex := by
  intro E _ _ _ d b A a hρ
  have ha : 0 < a := ENNReal.ofReal_pos.mp (lt_of_le_of_lt (zero_le (α := ℝ≥0∞)) hρ)
  obtain ⟨C, hC, hpow⟩ := geometric_bound_of_spectralRadius_lt (LinearMap.toMatrix b b A) a ha hρ
  obtain ⟨p, hp, hA⟩ := matrix_adapted _ a C ha hC hpow
  obtain ⟨q, hq, hbound⟩ := pullback_adapted b A a p hp hA
  exact ⟨q, hq, hbound, inducedNorm_le q A a ha.le hbound⟩

theorem upperReal : Specs.D13Unified.Ch15.AdaptedNorm.upperReal := by
  intro E _ _ _ d b A a hρ
  have ha : 0 < a := ENNReal.ofReal_pos.mp (lt_of_le_of_lt (zero_le (α := ℝ≥0∞)) hρ)
  obtain ⟨C, hC, hpow⟩ := geometric_bound_of_spectralRadius_lt
    (complexify (LinearMap.toMatrix b b A)) a ha hρ
  have hreal : ∀ n : ℕ, ‖LinearMap.toMatrix b b A ^ n‖ ≤ C * a ^ n := by
    simpa only [norm_complexify_pow] using hpow
  obtain ⟨p, hp, hA⟩ := matrix_adapted _ a C ha hC hreal
  obtain ⟨q, hq, hbound⟩ := pullback_adapted b A a p hp hA
  exact ⟨q, hq, hbound, inducedNorm_le q A a ha.le hbound⟩

/-- Reciprocal spectral values of an invertible matrix lie strictly below
`a⁻¹` when all original spectral values lie above `a`. No nonzero-dimension
assumption is used. -/
lemma inverse_radius_lt {d : ℕ} (M : (CMatrix d)ˣ) (a : ℝ) (ha : 0 < a)
    (h : ∀ z ∈ spectrum ℂ (M : CMatrix d), a < ‖z‖) :
    spectralRadius ℂ (↑M⁻¹ : CMatrix d) < ENNReal.ofReal a⁻¹ := by
  let r : ℝ≥0 := NNReal.mk a⁻¹ (inv_pos.mpr ha).le
  have hr : spectralRadius ℂ (↑M⁻¹ : CMatrix d) < (r : ℝ≥0∞) := by
    apply spectralRadius_lt_of_forall_quasispectrum_lt
    intro z hz
    rw [quasispectrum_eq_spectrum_union_zero] at hz
    rcases hz with hz | hz
    · have hzorig : z⁻¹ ∈ spectrum ℂ (M : CMatrix d) := spectrum.inv₀_mem_iff.mpr hz
      have hnorm : a < ‖z‖⁻¹ := by simpa only [norm_inv] using h z⁻¹ hzorig
      have hzpos : 0 < ‖z‖ := by
        by_contra! hn
        have hz0 : ‖z‖ = 0 := le_antisymm hn (norm_nonneg _)
        simp only [hz0, inv_zero] at hnorm
        exact (not_lt_of_ge ha.le) hnorm
      have hlt : ‖z‖ < a⁻¹ := (lt_inv_comm₀ hzpos ha).mpr hnorm
      exact_mod_cast hlt
    · have hz0 : z = 0 := Set.mem_singleton_iff.mp hz
      simp only [hz0, nnnorm_zero]
      exact_mod_cast (inv_pos.mpr ha : 0 < a⁻¹)
  simpa only [r, ENNReal.ofReal, Real.toNNReal_of_nonneg (inv_pos.mpr ha).le] using hr

/-- An inverse upper bound yields the desired lower bound on the same norm. -/
lemma lower_of_inverse_upper {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (A : (Module.End 𝕜 E)ˣ) (p : Seminorm 𝕜 E)
    (a : ℝ) (ha : 0 < a)
    (h : ∀ v, p ((↑A⁻¹ : Module.End 𝕜 E) v) ≤ a⁻¹ * p v) :
    ∀ v, a * p v ≤ p ((A : Module.End 𝕜 E) v) := by
  intro v
  have hv := h ((A : Module.End 𝕜 E) v)
  have heq : (↑A⁻¹ : Module.End 𝕜 E) ((A : Module.End 𝕜 E) v) = v := by
    change ((↑A⁻¹ : Module.End 𝕜 E) * (A : Module.End 𝕜 E)) v = v
    rw [Units.inv_mul, Module.End.one_apply]
  rw [heq] at hv
  have := mul_le_mul_of_nonneg_left hv ha.le
  simpa only [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] using this

theorem lowerComplex : Specs.D13Unified.Ch15.AdaptedNorm.lowerComplex := by
  intro E _ _ _ d b A a ha hspec
  let M : (CMatrix d)ˣ := Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom A
  have hM : ∀ z ∈ spectrum ℂ (M : CMatrix d), a < ‖z‖ := hspec
  have hr := inverse_radius_lt M a ha hM
  have hmatrix : (↑M⁻¹ : CMatrix d) = LinearMap.toMatrix b b (↑A⁻¹ : Module.End ℂ E) := rfl
  rw [hmatrix] at hr
  obtain ⟨p, hp, hbound, _⟩ := upperComplex b (↑A⁻¹ : Module.End ℂ E) a⁻¹ hr
  exact ⟨p, hp, lower_of_inverse_upper A p a ha hbound⟩

theorem lowerReal : Specs.D13Unified.Ch15.AdaptedNorm.lowerReal := by
  intro E _ _ _ d b A a ha hspec
  let Mr : (RMatrix d)ˣ := Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom A
  let M : (CMatrix d)ˣ := Units.map (algebraMap ℝ ℂ).mapMatrix.toMonoidHom Mr
  have hM : ∀ z ∈ spectrum ℂ (M : CMatrix d), a < ‖z‖ := hspec
  have hr := inverse_radius_lt M a ha hM
  have hmatrix : (↑M⁻¹ : CMatrix d) =
      complexify (LinearMap.toMatrix b b (↑A⁻¹ : Module.End ℝ E)) := rfl
  rw [hmatrix] at hr
  obtain ⟨p, hp, hbound, _⟩ := upperReal b (↑A⁻¹ : Module.End ℝ E) a⁻¹ hr
  exact ⟨p, hp, lower_of_inverse_upper A p a ha hbound⟩

theorem normRepresentation : Specs.D13Unified.Ch15.AdaptedNorm.normRepresentation := by
  intro 𝕜 E _ _ _ p hp v
  constructor
  · intro hv
    obtain ⟨C, _, D, _, h⟩ := hp
    have hn := (h v).1
    rw [hv, mul_zero] at hn
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  · rintro rfl
    exact map_zero p

end D13Unified.Ch15.AdaptedNorm
