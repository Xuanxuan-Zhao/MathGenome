import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.PolyconvexExample
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.Minors
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import MathGenome.Internal.FourierSobolev.P102.Sobolev.MoserMembership
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.PolyconvexExistence
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory TopologicalSpace Set Filter
open scoped Topology ENNReal InnerProductSpace
namespace VariationalNotes.Sobolev.PolyconvexExample
open Minors

lemma convex_norm_rpow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ} (hp : 1 ≤ p) : ConvexOn ℝ univ (fun x : E => ‖x‖ ^ p) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hn := (convexOn_univ_norm (E := E)).2 hx hy ha hb hab
  have hr := Real.rpow_le_rpow (norm_nonneg (a • x + b • y)) hn
    (show 0 ≤ p by linarith)
  exact hr.trans ((convexOn_rpow hp).2 (norm_nonneg x) (norm_nonneg y) ha hb hab)

lemma convex_matrixRepresentation (p γ : ℝ) (hp : 1 ≤ p) :
    ConvexOn ℝ univ (matrixRepresentation p γ) := by
  constructor
  · exact convex_univ
  · intro x hx y hy a b ha hb hab
    have hn := (convex_norm_rpow (E := Gradient 2 2) hp).2
      (mem_univ x.1) (mem_univ y.1) ha hb hab
    have hs : (a * x.2 + b * y.2 - γ)^2 ≤ a * (x.2 - γ)^2 + b * (y.2 - γ)^2 := by
      have h := (Even.convexOn_pow (show Even 2 by decide) (𝕜 := ℝ)).2
        (mem_univ (x.2 - γ)) (mem_univ (y.2 - γ)) ha hb hab
      simp only [smul_eq_mul] at h
      have he : a * (x.2 - γ) + b * (y.2 - γ) = a * x.2 + b * y.2 - γ := by
        nlinarith [congrArg (fun c : ℝ => c * γ) hab]
      rwa [he] at h
    change ‖a • x.1 + b • y.1‖ ^ p + (a * x.2 + b * y.2 - γ)^2 ≤ _
    dsimp [matrixRepresentation]
    simp only [smul_eq_mul] at hn ⊢
    nlinarith

lemma determinant_coordinate (Z : Gradient 2 2) :
    allMinors Z determinantIndex = Polyconvex.determinant Z := rfl

lemma convex_minorRepresentation (p γ : ℝ) (hp : 1 ≤ p) (x : Domain 2) (s : Vector 2) :
    ConvexOn ℝ univ (minorRepresentation p γ x s) := by
  let L : Coordinates 2 2 →ₗ[ℝ] Gradient 2 2 × ℝ :=
    (firstMatrix (by decide) (by decide)).prod
      { toFun := fun z => z determinantIndex
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
  refine ⟨convex_univ, ?_⟩
  intro z hz w hw a b ha hb hab
  have h := (convex_matrixRepresentation p γ hp).2 (mem_univ (L z)) (mem_univ (L w))
    ha hb hab
  change matrixRepresentation p γ (L (a • z + b • w)) ≤ _
  rw [map_add, map_smul, map_smul]
  exact h

/-- Every conditional target retains both full upstream premises in order. -/
theorem representation_conditional
    (_existence : Polyconvex.Expected.Existence)
    (_matrixDetExistence : Polyconvex.Expected.MatrixDetExistence) :
    Expected.Representation := by
  intro p γ hp hγ
  refine ⟨fun _ => rfl, convex_matrixRepresentation p γ (by linarith), ?_, ?_⟩
  · intro x s Z
    change ‖Z‖ ^ p + (Polyconvex.determinant Z - γ)^2 =
      ‖firstMatrix (by decide) (by decide) (allMinors Z)‖ ^ p +
        (allMinors Z determinantIndex - γ)^2
    rw [matrix_recovery (by decide) (by decide) Z, determinant_coordinate]
  · exact convex_minorRepresentation p γ (by linarith)

theorem coercivity_conditional
    (_existence : Polyconvex.Expected.Existence)
    (_matrixDetExistence : Polyconvex.Expected.MatrixDetExistence) :
    Expected.Coercivity := by
  intro p γ
  refine ⟨fun Z => ?_, fun Z t => ?_, fun x s z => ?_⟩
  all_goals
    dsimp [integrand, matrixRepresentation, minorRepresentation]
    exact le_add_of_nonneg_right (sq_nonneg _)

@[simp] lemma determinant_scalarIdentity (t : ℝ) :
    Polyconvex.determinant (scalarIdentity t) = t ^ 2 := by
  simp [Polyconvex.determinant, scalarIdentity, Matrix.det_fin_two, pow_two]

@[simp] lemma determinant_zero : Polyconvex.determinant 0 = 0 := by
  simp [Polyconvex.determinant, Matrix.det_fin_two]

lemma norm_scalarIdentity (t : ℝ) : ‖scalarIdentity t‖ = Real.sqrt 2 * |t| := by
  rw [gradient_norm_eq]
  simp only [scalarIdentity, Fin.sum_univ_two, ite_true,
    Fin.zero_ne_one, ite_false, Ne.symm Fin.zero_ne_one, zero_pow (by decide : 2 ≠ 0), add_zero,
    zero_add]
  rw [show t ^ 2 + t ^ 2 = 2 * t ^ 2 by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq_eq_abs]

lemma norm_scalarIdentity_rpow (p t : ℝ) :
    ‖scalarIdentity t‖ ^ p = (2 : ℝ) ^ (p / 2) * |t| ^ p := by
  rw [norm_scalarIdentity, Real.mul_rpow (Real.sqrt_nonneg _) (abs_nonneg _),
    Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 2
  ring

@[simp] lemma integrand_zero (p γ : ℝ) (hp : p ≠ 0) :
    integrand p γ 0 = γ ^ 2 := by
  simp [integrand, Real.zero_rpow hp]

lemma scalar_increment (p γ : ℝ) (hp : 2 < p) (t : ℝ) :
    integrand p γ (scalarIdentity t) - integrand p γ 0 =
      (2 : ℝ) ^ (p / 2) * |t| ^ p - 2 * γ * t ^ 2 + t ^ 4 := by
  rw [integrand_zero p γ (by linarith)]
  dsimp [integrand]
  rw [norm_scalarIdentity_rpow, determinant_scalarIdentity]
  ring

lemma scalar_even (p γ t : ℝ) :
    integrand p γ (scalarIdentity (-t)) = integrand p γ (scalarIdentity t) := by
  simp [integrand, norm_scalarIdentity_rpow]

lemma scalar_decreases (p γ : ℝ) (hp : 2 < p) (hγ : 0 < γ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < |t| → |t| < δ →
      integrand p γ (scalarIdentity t) - integrand p γ 0 < 0 := by
  have hc : ContinuousAt (fun t : ℝ => (2 : ℝ) ^ (p / 2) * |t| ^ (p - 2) + t ^ 2) 0 :=
    (continuousAt_const.mul
      (continuous_abs.continuousAt.rpow_const (Or.inr (by linarith)))).add
        (continuousAt_id.pow 2)
  have hev : ∀ᶠ t : ℝ in 𝓝 0,
      (2 : ℝ) ^ (p / 2) * |t| ^ (p - 2) + t ^ 2 < 2 * γ := by
    have h0 : (2 : ℝ) ^ (p / 2) * |(0 : ℝ)| ^ (p - 2) + (0 : ℝ) ^ 2 < 2 * γ := by
      simp [Real.zero_rpow (by linarith : p - 2 ≠ 0)]
      linarith
    exact hc.eventually (gt_mem_nhds h0)
  obtain ⟨δ, hδ, hlt⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ
  have hsmall := hlt (by simpa [Real.dist_eq] using htδ)
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero (abs_pos.mp ht)
  have hpw : |t| ^ p = |t| ^ (p - 2) * t ^ 2 := by
    have hr := Real.rpow_add ht (p - 2) 2
    rw [sub_add_cancel, Real.rpow_two, sq_abs] at hr
    exact hr
  rw [scalar_increment p γ hp t, hpw]
  nlinarith [mul_pos ht2 (sub_pos.mpr hsmall)]

lemma not_convex_integrand (p γ : ℝ) (hp : 2 < p) (hγ : 0 < γ) :
    ¬ ConvexOn ℝ univ (integrand p γ) := by
  intro hc
  obtain ⟨δ, hδ, hdec⟩ := scalar_decreases p γ hp hγ
  have hd := hdec (δ / 2) (by rw [abs_of_pos (by linarith : 0 < δ / 2)]; linarith)
    (by rw [abs_of_pos (by linarith : 0 < δ / 2)]; linarith)
  have hj := hc.2 (mem_univ (scalarIdentity (δ / 2)))
    (mem_univ (scalarIdentity (-(δ / 2))))
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)
  have hz : (1 / 2 : ℝ) • scalarIdentity (δ / 2) +
      (1 / 2 : ℝ) • scalarIdentity (-(δ / 2)) = 0 := by
    ext ij
    simp only [scalarIdentity, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
    split_ifs <;> ring
  rw [hz, scalar_even] at hj
  simp only [smul_eq_mul] at hj
  linarith

theorem line_behavior_conditional
    (_existence : Polyconvex.Expected.Existence)
    (_matrixDetExistence : Polyconvex.Expected.MatrixDetExistence) :
    Expected.LineBehavior := by
  intro p γ hp hγ
  exact ⟨scalar_increment p γ hp, scalar_even p γ,
    scalar_decreases p γ hp hγ, not_convex_integrand p γ hp hγ⟩

lemma zero_energy (Ω : Opens (Domain 2)) (p : Exponent) (γ : ℝ)
    (hΩ : Bornology.IsBounded (Ω : Set (Domain 2))) :
    energy Ω 2 p (fun _ _ Z => integrand p.real γ Z) 0 =
      ((γ ^ 2 * (volume (Ω : Set (Domain 2))).toReal : ℝ) : EReal) := by
  have hu : (value Ω 2 p (0 : W1p Ω 2 p) : Domain 2 → Vector 2) =ᵐ[domainMeasure Ω]
      (fun _ => 0) := by
    rw [map_zero]
    filter_upwards [Lp.coeFn_zero (Vector 2) p.ennreal (domainMeasure Ω)] with x hx
    exact hx
  have hV : (gradient Ω 2 p (0 : W1p Ω 2 p) : Domain 2 → Gradient 2 2) =ᵐ[domainMeasure Ω]
      (fun _ => 0) := by
    rw [map_zero]
    filter_upwards [Lp.coeFn_zero (Gradient 2 2) p.ennreal (domainMeasure Ω)] with x hx
    exact hx
  rw [energy, energyOnFields_congr Ω _ hu hV]
  unfold energyOnFields
  simp only [integrand_zero p.real γ p.pos.ne',
    ENNReal.ofReal_of_nonpos (neg_nonpos.mpr (sq_nonneg γ)), lintegral_zero,
    ENNReal.toEReal_zero, sub_zero, lintegral_const, Measure.restrict_apply_univ]
  have hf : volume (Ω : Set (Domain 2)) ≠ ⊤ := hΩ.measure_lt_top.ne
  have he : ENNReal.ofReal (γ ^ 2) * volume (Ω : Set (Domain 2)) =
      ENNReal.ofReal (γ ^ 2 * (volume (Ω : Set (Domain 2))).toReal) := by
    nth_rw 1 [← ENNReal.ofReal_toReal hf]
    rw [ENNReal.ofReal_mul (sq_nonneg γ)]
  rw [he]
  rw [EReal.coe_ennreal_ofReal, max_eq_left (by positivity)]

theorem zero_competitor_conditional
    (_existence : Polyconvex.Expected.Existence)
    (_matrixDetExistence : Polyconvex.Expected.MatrixDetExistence) :
    Expected.ZeroCompetitor := by
  intro Ω p γ hΩ
  exact ⟨by simp [affineClass], zero_energy Ω p γ hΩ⟩

lemma continuous_matrixRepresentation (p γ : ℝ) (hp : 0 ≤ p) :
    Continuous (matrixRepresentation p γ) := by
  unfold matrixRepresentation
  exact ((continuous_fst.norm).rpow_const (fun _ => Or.inr hp)).add
    ((continuous_snd.sub continuous_const).pow 2)

theorem attainment_conditional
    (_existence : Polyconvex.Expected.Existence)
    (matrixDetExistence : Polyconvex.Expected.MatrixDetExistence) :
    Expected.Attainment := by
  intro Ω p γ hΩ hp hγ
  let q : Exponent := ⟨1, le_rfl⟩
  have hrep : CaratheodorySpecs.Caratheodory (domainMeasure Ω)
      (fun (_x : Domain 2) (y : Vector 2 × (Gradient 2 2 × ℝ)) =>
        matrixRepresentation p.real γ y.2) := by
    refine ⟨fun _ => measurable_const, Filter.Eventually.of_forall (fun _ => ?_)⟩
    exact (continuous_matrixRepresentation p.real γ (by linarith)).comp continuous_snd
  have hc : ∀ᵐ _x ∂domainMeasure Ω, ∀ _s : Vector 2,
      ConvexOn ℝ univ (matrixRepresentation p.real γ) :=
    Filter.Eventually.of_forall (fun _ _ => convex_matrixRepresentation p.real γ (by linarith))
  have hl : ∀ᵐ _x ∂domainMeasure Ω, ∀ (s : Vector 2) (Z : Gradient 2 2) (t : ℝ),
      (1 : ℝ) * ‖Z‖ ^ p.real - 0 * ‖s‖ ^ q.real - 0 ≤
        matrixRepresentation p.real γ (Z,t) := by
    filter_upwards [] with x s Z t
    simp only [one_mul, zero_mul, sub_zero]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hzero := zero_energy Ω p γ hΩ
  apply matrixDetExistence Ω p q 0 (fun _ _ => matrixRepresentation p.real γ)
    1 0 (fun _ => 0) hΩ hp (by dsimp [q]; linarith) hrep hc
    (by norm_num) le_rfl (integrable_zero _ _ _) hl
  exact ⟨0, by simp [affineClass], γ ^ 2 * (volume (Ω : Set (Domain 2))).toReal, hzero⟩

lemma continuous_determinant : Continuous (Polyconvex.determinant : Gradient 2 2 → ℝ) := by
  unfold Polyconvex.determinant
  simp only [Matrix.det_fin_two]
  fun_prop

/-- On a finite-measure domain, a determinant outside L² forces the actual
extended energy to be +∞. No everywhere-finiteness assumption is introduced. -/
lemma energy_top_of_determinant_not_memLp (Ω : Opens (Domain 2)) (p : Exponent)
    (γ : ℝ) (u : W1p Ω 2 p) (hΩ : Bornology.IsBounded (Ω : Set (Domain 2)))
    (hdet : ¬ MemLp (fun x => Polyconvex.determinant (gradient Ω 2 p u x)) 2
      (domainMeasure Ω)) :
    energy Ω 2 p (fun _ _ Z => integrand p.real γ Z) u = ⊤ := by
  let μ := domainMeasure Ω
  let D := fun x => Polyconvex.determinant (gradient Ω 2 p u x)
  have hfin : μ univ < ⊤ := by simpa [μ] using hΩ.measure_lt_top (μ := volume)
  haveI : IsFiniteMeasure μ := ⟨hfin⟩
  have hm : AEStronglyMeasurable D μ :=
    continuous_determinant.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)
  have hm' : AEStronglyMeasurable (fun x => D x - γ) μ := hm.sub aestronglyMeasurable_const
  have hnot : ¬ Integrable (fun x => (D x - γ)^2) μ := by
    intro hi
    have hh := (memLp_two_iff_integrable_sq hm').mpr hi
    have h := hh.add (memLp_const (p := (2 : ℝ≥0∞)) (μ := μ) γ)
    apply hdet
    have hh' : ((fun x => D x - γ) + (fun _ => γ)) = D := by
      funext x
      exact sub_add_cancel _ _
    rw [hh'] at h
    exact h
  have htop : ∫⁻ x, ENNReal.ofReal ((D x - γ)^2) ∂μ = ⊤ := by
    by_contra h
    exact hnot ((lintegral_ofReal_ne_top_iff_integrable (hm'.pow 2)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).mp h)
  have he : ∫⁻ x, ENNReal.ofReal (integrand p.real γ (gradient Ω 2 p u x)) ∂μ = ⊤ := by
    apply top_unique
    rw [← htop]
    apply lintegral_mono
    intro x
    apply ENNReal.ofReal_le_ofReal
    exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)
  have hn : ∀ x, ENNReal.ofReal (-integrand p.real γ (gradient Ω 2 p u x)) = 0 := by
    intro x
    apply ENNReal.ofReal_of_nonpos
    exact neg_nonpos.mpr (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg _))
  change (∫⁻ x, ENNReal.ofReal (integrand p.real γ (gradient Ω 2 p u x)) ∂μ).toEReal -
    (∫⁻ x, ENNReal.ofReal (-integrand p.real γ (gradient Ω 2 p u x)) ∂μ).toEReal = ⊤
  simp only [he, hn, lintegral_zero, ENNReal.toEReal_zero, sub_zero]
  rfl

/-! The infinite-energy witness. The radial core has derivative eigenvalues
(1/2)|x|^(-1/2) and |x|^(-1/2). Its determinant is 1/(2|x|).
We build its Sobolev representatives by the ACL converse, then use
support-controlled mollification for the zero-boundary closure. -/

def coreMap (x : Domain 2) : Vector 2 := ‖x‖ ^ (-(1/2:ℝ)) • x

def coreDerivative (x : Domain 2) : Domain 2 →L[ℝ] Vector 2 :=
  ‖x‖ ^ (-(1/2:ℝ)) • ContinuousLinearMap.id ℝ (Domain 2) +
    (((-(1/2:ℝ)) * ‖x‖ ^ (-(5/2:ℝ))) • innerSL ℝ x).smulRight x

lemma hasFDerivAt_coreMap {x : Domain 2} (hx : x ≠ 0) :
    HasFDerivAt coreMap (coreDerivative x) x := by
  have hs : HasFDerivAt (fun y : Domain 2 => ‖y‖ ^ (-(1/2:ℝ)))
      (((-(1/2:ℝ)) * ‖x‖ ^ (-(5/2:ℝ))) • innerSL ℝ x) x := by
    convert ((hasStrictFDerivAt_norm_sq x).rpow_const
      (p := (-(1/4:ℝ))) (by simp [hx])).hasFDerivAt using 0
    simp_rw [← Real.rpow_natCast_mul (norm_nonneg _),
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    ring_nf
  exact hs.smul (hasFDerivAt_id x)

lemma norm_coreMap (x : Domain 2) : ‖coreMap x‖ = ‖x‖ ^ (1/2:ℝ) := by
  by_cases hx : x = 0
  · simp [hx, coreMap, Real.zero_rpow]
  rw [coreMap, norm_smul, Real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm,
    ← Real.rpow_add_one (norm_ne_zero_iff.mpr hx)]
  norm_num

lemma continuous_coreMap : Continuous coreMap := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    change Tendsto coreMap (𝓝 0) (𝓝 (coreMap 0))
    have hz : coreMap 0 = 0 := by simp [coreMap]
    rw [hz, tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_coreMap]
    convert ((continuous_norm.rpow_const (p := (1/2:ℝ)) (fun _ => Or.inr (by norm_num))).tendsto
      (0 : Domain 2)) using 1; norm_num
  · exact (hasFDerivAt_coreMap hx).continuousAt

lemma contDiffAt_coreMap {x : Domain 2} (hx : x ≠ 0) : ContDiffAt ℝ 1 coreMap x := by
  have hpow : ContDiffAt ℝ 1 (fun y : Domain 2 => ‖y‖ ^ (-(1/2:ℝ))) x :=
    (Real.contDiffAt_rpow_const (n := 1) (p := (-(1/2:ℝ)))
      (Or.inl (norm_ne_zero_iff.mpr hx))).comp x (contDiffAt_norm ℝ hx)
  exact hpow.smul contDiffAt_id

lemma norm_coreDerivative {x : Domain 2} (hx : x ≠ 0) :
    ‖coreDerivative x‖ ≤ (3/2:ℝ) * ‖x‖ ^ (-(1/2:ℝ)) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have he : ‖x‖ ^ (-(5/2:ℝ)) * ‖x‖ * ‖x‖ = ‖x‖ ^ (-(1/2:ℝ)) := by
    rw [← Real.rpow_add_one hr.ne', ← Real.rpow_add_one hr.ne']
    norm_num
  unfold coreDerivative
  refine (norm_add_le _ _).trans_eq ?_
  simp only [norm_smul, ContinuousLinearMap.norm_id, mul_one,
    ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, norm_mul,
    Real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm]
  norm_num
  nlinarith [he]

lemma radialMap_eq (x : Domain 2) : radialMap x = radialCutoff x • coreMap x := by
  simp [radialMap, coreMap, smul_smul]

lemma radialMap_eq_smul : radialMap = (radialCutoff : Domain 2 → ℝ) • coreMap :=
  funext radialMap_eq

lemma continuous_radialMap : Continuous radialMap := by
  rw [radialMap_eq_smul]
  exact radialCutoff.continuous.smul continuous_coreMap

lemma compactSupport_radialMap : HasCompactSupport radialMap := by
  have h : HasCompactSupport ((radialCutoff : Domain 2 → ℝ) • coreMap) :=
    radialCutoff.hasCompactSupport.smul_right
  rwa [← radialMap_eq_smul] at h

lemma contDiffAt_radialMap {x : Domain 2} (hx : x ≠ 0) : ContDiffAt ℝ 1 radialMap x := by
  rw [radialMap_eq_smul]
  exact radialCutoff.contDiff.contDiffAt.smul (contDiffAt_coreMap hx)

def radialDerivative (x : Domain 2) : Domain 2 →L[ℝ] Vector 2 :=
  radialCutoff x • coreDerivative x + (fderiv ℝ radialCutoff x).smulRight (coreMap x)

lemma hasFDerivAt_radialMap {x : Domain 2} (hx : x ≠ 0) :
    HasFDerivAt radialMap (radialDerivative x) x := by
  rw [radialMap_eq_smul]
  exact (radialCutoff.contDiff.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0) x).hasFDerivAt.smul
      (hasFDerivAt_coreMap hx)

lemma norm_coreMap_product (x : Domain 2) :
    ‖coreMap x‖ = ‖x‖ ^ (-(1/2:ℝ)) * ‖x‖ := by
  rw [coreMap, norm_smul, Real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm]

lemma radialDerivative_bound : ∃ C : ℝ, 0 < C ∧ ∀ x : Domain 2,
    x ≠ 0 → ‖x‖ < 2 → ‖radialDerivative x‖ ≤ C * ‖x‖ ^ (-(1/2:ℝ)) := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    radialCutoff.hasCompactSupport (radialCutoff.contDiff (n := 1)) (by decide)
  refine ⟨2 * (K : ℝ) + 2, by positivity, ?_⟩
  intro x hx hr
  have hpow : 0 ≤ ‖x‖ ^ (-(1/2:ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  have hb : ‖radialCutoff x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg radialCutoff.nonneg]
    exact radialCutoff.le_one
  have hu : ‖coreMap x‖ ≤ 2 * ‖x‖ ^ (-(1/2:ℝ)) := by
    rw [norm_coreMap_product]
    nlinarith
  have hd := norm_fderiv_le_of_lipschitz ℝ hK (x₀ := x)
  unfold radialDerivative
  calc
    _ ≤ ‖radialCutoff x • coreDerivative x‖ +
        ‖(fderiv ℝ radialCutoff x).smulRight (coreMap x)‖ := norm_add_le _ _
    _ = ‖radialCutoff x‖ * ‖coreDerivative x‖ +
        ‖fderiv ℝ radialCutoff x‖ * ‖coreMap x‖ := by
      rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
    _ ≤ 1 * ((3/2:ℝ) * ‖x‖ ^ (-(1/2:ℝ))) +
        (K : ℝ) * (2 * ‖x‖ ^ (-(1/2:ℝ))) := by
      exact add_le_add (mul_le_mul hb (norm_coreDerivative hx) (norm_nonneg _) (by norm_num))
        (mul_le_mul hd hu (norm_nonneg _) K.coe_nonneg)
    _ ≤ _ := by nlinarith

lemma tsupport_radialMap : tsupport radialMap ⊆ Metric.closedBall 0 1 := by
  rw [radialMap_eq_smul]
  exact (tsupport_smul_subset_left (radialCutoff : Domain 2 → ℝ) coreMap).trans_eq (by
    simpa [radialCutoff] using radialCutoff.tsupport_eq)

/-- A compactly supported field with the radial half-power derivative bound
belongs to every finite Lp with p < 4 in dimension two. -/
lemma memLp_of_half_power_bound {E : Type*} [NormedAddCommGroup E]
    (p : Exponent) (hp : p.real < 4) (f : Domain 2 → E)
    (hm : AEStronglyMeasurable f volume)
    (hs : Function.support f ⊆ Metric.ball 0 2)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain 2) 2),
      ‖f x‖ ≤ C * ‖x‖ ^ (-(1/2:ℝ))) : MemLp f p.ennreal volume := by
  apply (integrable_norm_rpow_iff hm (by simp [Exponent.ennreal, p.pos])
    (by simp [Exponent.ennreal])).mp
  simp only [Exponent.toReal]
  have hdim : Module.finrank ℝ (Domain 2) = 2 := by simp [Domain, P102.U4.Space]
  have hi : IntegrableOn (fun x : Domain 2 => ‖f x‖ ^ p.real) (Metric.ball 0 2) volume := by
    apply integrableOn_ball_of_norm_le_rpow (C := C ^ p.real) (α := p.real / 2)
      (by rw [hdim]; norm_num) (by rw [hdim]; norm_cast; linarith)
    · filter_upwards [hb] with x hx
      rw [Real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm]
      calc
        ‖f x‖ ^ p.real ≤ (C * ‖x‖ ^ (-(1/2:ℝ))) ^ p.real :=
          Real.rpow_le_rpow (norm_nonneg _) hx p.pos.le
        _ = C ^ p.real * ‖x‖ ^ (-(p.real / 2)) := by
          rw [Real.mul_rpow hC (Real.rpow_nonneg (norm_nonneg _) _),
            ← Real.rpow_mul (norm_nonneg _)]
          congr 2
          ring
    · exact (hm.norm.aemeasurable.pow_const p.real).aestronglyMeasurable
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi
  intro x hx
  apply hs
  by_contra hn
  have hz : f x = 0 := not_not.mp hn
  exact hx (by simp [hz, Real.zero_rpow p.pos.ne'])

def scalarField (i : Fin 2) (x : Domain 2) : ℝ := radialMap x i

def scalarDerivative (i j : Fin 2) (x : Domain 2) : ℝ :=
  fderiv ℝ (scalarField i) x (P102.U4.coordinateVector 2 j)

lemma scalarField_tsupport (i : Fin 2) : tsupport (scalarField i) ⊆ tsupport radialMap :=
  tsupport_comp_subset (g := fun v : Vector 2 => v i) rfl radialMap

lemma scalarField_continuous (i : Fin 2) : Continuous (scalarField i) :=
  (EuclideanSpace.proj i).continuous.comp continuous_radialMap

lemma scalarField_compactSupport (i : Fin 2) : HasCompactSupport (scalarField i) :=
  compactSupport_radialMap.of_isClosed_subset (isClosed_tsupport _) (scalarField_tsupport i)

lemma contDiffAt_scalarField (i : Fin 2) {x : Domain 2} (hx : x ≠ 0) :
    ContDiffAt ℝ 1 (scalarField i) x := by
  have hp : ContDiff ℝ 1 (fun v : Vector 2 => v i) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i).contDiff
  exact hp.contDiffAt.comp x (contDiffAt_radialMap hx)

lemma scalarDerivative_eq (i j : Fin 2) {x : Domain 2} (hx : x ≠ 0) :
    scalarDerivative i j x = (radialDerivative x (P102.U4.coordinateVector 2 j)) i := by
  have h := (EuclideanSpace.proj i).hasFDerivAt.comp x (hasFDerivAt_radialMap hx)
  change fderiv ℝ (scalarField i) x _ = _
  rw [show fderiv ℝ (scalarField i) x = (EuclideanSpace.proj i).comp (radialDerivative x)
    from h.fderiv]
  rfl

lemma scalarDerivative_memLp (p : Exponent) (hp : p.real < 4) (i j : Fin 2) :
    MemLp (scalarDerivative i j) p.ennreal volume := by
  have hm : Measurable (scalarDerivative i j) :=
    measurable_fderiv_apply_const ℝ (scalarField i) _
  obtain ⟨C, hC, hb⟩ := radialDerivative_bound
  refine memLp_of_half_power_bound p hp (scalarDerivative i j) hm.aestronglyMeasurable ?_ C hC.le ?_
  · exact ((subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ _)).trans
      ((scalarField_tsupport i).trans (tsupport_radialMap.trans
        (Metric.closedBall_subset_ball (show (1:ℝ) < 2 by norm_num))))
  · filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0 : Domain 2))] with x hx hx0
    rw [scalarDerivative_eq i j hx0]
    have hnorm : ‖P102.U4.coordinateVector 2 j‖ = 1 := by
      simp [P102.U4.coordinateVector, EuclideanSpace.basisFun_apply, EuclideanSpace.single,
        PiLp.norm_single]
    calc
      _ ≤ ‖radialDerivative x (P102.U4.coordinateVector 2 j)‖ := PiLp.norm_apply_le _ _
      _ ≤ ‖radialDerivative x‖ * ‖P102.U4.coordinateVector 2 j‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * ‖x‖ ^ (-(1/2:ℝ)) := by
        rw [hnorm, mul_one]
        exact hb x hx0 (by simpa using hx)

lemma line_ne_zero (j : Fin 2) {z : P102.U4.ACL.Transverse j} (hz : z ≠ 0) (t : ℝ) :
    P102.U4.ACL.line j z t ≠ 0 := by
  intro h
  apply hz
  funext k
  have hk := congrArg (fun x : Domain 2 => x k.1) h
  simpa [P102.U4.ACL.line, ExpandedFA.Sobolev.Lines.coordinateLine, k.property] using hk

lemma transverse_ae_ne_zero (j : Fin 2) :
    ∀ᵐ z : P102.U4.ACL.Transverse j ∂volume, z ≠ 0 := by
  haveI : Nonempty {k : Fin 2 // k ≠ j} := by
    fin_cases j
    · exact ⟨⟨1, by decide⟩⟩
    · exact ⟨⟨0, by decide⟩⟩
  exact volume.ae_ne 0

lemma exists_scalar_sobolev (p : Exponent) (hp : p.real < 4) (i : Fin 2) :
    ∃ u : P102.U4.Sobolev (d := 2) ℝ ⊤ 1 p.ennreal,
      (P102.U4.sobolevUnderlying u : Domain 2 → ℝ) =ᵐ[volume] scalarField i ∧
      ∀ j : Fin 2, (P102.U4.Truncations.sobolevFirstDerivative u j : Domain 2 → ℝ)
        =ᵐ[volume] scalarDerivative i j := by
  let Ω : Opens (Domain 2) := ⊤
  have hfm : MemLp (scalarField i) p.ennreal (domainMeasure Ω) := by
    simpa [Ω] using (scalarField_continuous i).memLp_of_hasCompactSupport
      (p := p.ennreal) (scalarField_compactSupport i)
  have hgm (j : Fin 2) : MemLp (scalarDerivative i j) p.ennreal (domainMeasure Ω) := by
    simpa [Ω, domainMeasure] using scalarDerivative_memLp p hp i j
  let a : P102.U4.DomainLp ℝ Ω p.ennreal := hfm.toLp _
  let g (j : Fin 2) : P102.U4.DomainLp ℝ Ω p.ennreal := (hgm j).toLp _
  have hweak (j : Fin 2) :
      P102.U4.distributionPartial {j} (P102.U4.regularDistribution Ω a) =
        P102.U4.regularDistribution Ω (g j) := by
    apply P102.U4.acl_converse 2 (by decide) ℝ Ω j a (g j)
      (P102.U4.domainLp_locallyIntegrable Ω p.ennreal _)
      (P102.U4.domainLp_locallyIntegrable Ω p.ennreal _)
    refine ⟨scalarField i, hfm.coeFn_toLp, ?_⟩
    filter_upwards [transverse_ae_ne_zero j,
      P102.U4.ACL.ae_on_fibers j (hgm j).coeFn_toLp] with z hz hgz
    refine ⟨?_, ?_⟩
    · intro b c hbc
      have hc : ContDiffOn ℝ 1 (fun t => scalarField i (P102.U4.ACL.line j z t)) (uIcc b c) := by
        intro t ht
        exact ((contDiffAt_scalarField i (line_ne_zero j hz t)).comp t
          ((P102.U4.ACL.line_contDiff j z).of_le (by simp : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))).contDiffAt).contDiffWithinAt
      exact hc.absolutelyContinuousOnInterval
    · filter_upwards [hgz] with t ht
      change HasDerivAt (fun s => scalarField i (P102.U4.ACL.line j z s))
        (g j (P102.U4.ACL.line j z t)) t
      rw [show g j (P102.U4.ACL.line j z t) =
        scalarDerivative i j (P102.U4.ACL.line j z t) from ht]
      exact ((contDiffAt_scalarField i (line_ne_zero j hz t)).differentiableAt
        (by decide)).hasFDerivAt.comp_hasDerivAt t (P102.U4.ACL.line_hasDerivAt j z t)
  obtain ⟨u, hu, hdu⟩ := P102.U4.Truncations.exists_sobolev_of_coordinates a g hweak
  refine ⟨u, ?_, fun j => ?_⟩
  · simpa only [hu, a, Ω, domainMeasure, Opens.coe_top, Measure.restrict_univ] using hfm.coeFn_toLp
  · simpa only [hdu, g, Ω, domainMeasure, Opens.coe_top, Measure.restrict_univ] using (hgm j).coeFn_toLp

def coreMatrix (x : Domain 2) : Gradient 2 2 :=
  WithLp.toLp 2 (fun ij => ‖x‖ ^ (-(1/2:ℝ)) * (if ij.1 = ij.2 then 1 else 0) -
    (1/2:ℝ) * ‖x‖ ^ (-(5/2:ℝ)) * x ij.1 * x ij.2)

lemma determinant_coreMatrix (x : Domain 2) :
    Polyconvex.determinant (coreMatrix x) = 1 / (2 * ‖x‖) := by
  by_cases hx : x = 0
  · simp [hx, coreMatrix, Polyconvex.determinant, Matrix.det_fin_two, Real.zero_rpow]
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hnorm : x 0 ^ 2 + x 1 ^ 2 = ‖x‖ ^ 2 := by
    simpa [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] using (PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) x).symm
  have he : Polyconvex.determinant (coreMatrix x) =
      (‖x‖ ^ (-(1/2:ℝ))) ^ 2 -
        (1/2:ℝ) * (‖x‖ ^ (-(1/2:ℝ)) * ‖x‖ ^ (-(5/2:ℝ))) * ‖x‖^2 := by
    rw [← hnorm]
    simp [Polyconvex.determinant, coreMatrix, Matrix.det_fin_two]
    ring
  rw [he, ← Real.rpow_mul_natCast hr.le,
    ← Real.rpow_add hr, show (-(1/2:ℝ)) * (2:ℕ) = -1 by norm_num,
    show (-(1/2:ℝ)) + (-(5/2:ℝ)) = -3 by norm_num,
    ]
  rw [mul_assoc, ← Real.rpow_two ‖x‖, ← Real.rpow_add hr]
  norm_num
  rw [Real.rpow_neg_one]
  ring

lemma core_det_not_memLp :
    ¬ MemLp (fun x : Domain 2 => Polyconvex.determinant (coreMatrix x)) 2
      (volume.restrict (Metric.ball 0 (1/2))) := by
  intro hm
  have hi := hm.integrable_sq
  simp_rw [determinant_coreMatrix] at hi
  have hj := (integrableOn_fun_norm_addHaar (E := Domain 2) (f := fun r : ℝ => (1 / (2 * r)) ^ 2) (r := 1/2) volume).mp hi
  have hk := hj.const_mul (4 : ℝ)
  have he : IntegrableOn (fun r : ℝ => r ^ (-1 : ℝ)) (Ioo 0 (1/2)) volume := by
    apply IntegrableOn.congr_fun hk _ measurableSet_Ioo
    intro r hr
    have hdim : Module.finrank ℝ (Domain 2) = 2 := by simp [Domain, P102.U4.Space]
    simp only [hdim, Nat.add_one_sub_one,
      pow_one, smul_eq_mul, Real.rpow_neg_one]
    field_simp [ne_of_gt hr.1]
    ring
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ) < 1/2)] at he
  norm_num at he

lemma coreDerivative_entry (x : Domain 2) (i j : Fin 2) :
    (coreDerivative x (P102.U4.coordinateVector 2 j)) i = coreMatrix x (i,j) := by
  have hi : ⟪x, P102.U4.coordinateVector 2 j⟫_ℝ = x j :=
    EuclideanSpace.inner_basisFun_real (Fin 2) x j
  have he : P102.U4.coordinateVector 2 j i = if i = j then 1 else 0 := by
    simp [P102.U4.coordinateVector, EuclideanSpace.basisFun_apply, EuclideanSpace.single]
  simp only [coreDerivative, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hi,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, he]
  change _ = ‖x‖ ^ (-(1/2:ℝ)) * (if i = j then 1 else 0) -
    (1/2:ℝ) * ‖x‖ ^ (-(5/2:ℝ)) * x i * x j
  ring

lemma scalarDerivative_core (i j : Fin 2) {x : Domain 2} (hx : x ≠ 0)
    (hr : ‖x‖ < 1/2) : scalarDerivative i j x = coreMatrix x (i,j) := by
  have hb : (radialCutoff : Domain 2 → ℝ) =ᶠ[𝓝 x] 1 :=
    radialCutoff.eventuallyEq_one_of_mem_ball (by simpa [radialCutoff] using hr)
  have heq : radialMap =ᶠ[𝓝 x] coreMap := by
    filter_upwards [hb] with y hy
    rw [radialMap_eq, show radialCutoff y = 1 from hy, one_smul]
  have hd : radialDerivative x = coreDerivative x :=
    (hasFDerivAt_radialMap hx).unique ((hasFDerivAt_coreMap hx).congr_of_eventuallyEq heq)
  rw [scalarDerivative_eq i j hx, hd, coreDerivative_entry]

lemma exists_radial_sobolev (p : Exponent) (hp : p.real < 4) :
    ∃ u : W1p disk 2 p, u ∈ zeroSubmodule disk 2 p ∧
      (value disk 2 p u : Domain 2 → Vector 2) =ᵐ[domainMeasure disk] radialMap ∧
      ∀ i j : Fin 2, (fun x => gradient disk 2 p u x (i,j)) =ᵐ[domainMeasure disk]
        scalarDerivative i j := by
  choose U hU hDU using (fun i : Fin 2 => exists_scalar_sobolev p hp i)
  let v (i : Fin 2) := P102.U4.sobolevRestrict disk (U i)
  let u : W1p disk 2 p := (coordinateEquiv disk p).symm v
  have hcoord (i : Fin 2) : toCoordinates disk p u i = v i :=
    congrFun ((coordinateEquiv disk p).apply_symm_apply v) i
  have hz : u ∈ zeroSubmodule disk 2 p := by
    apply (zero_mem_iff_coordinates disk p u).mpr
    intro i
    change toCoordinates disk p u i ∈ _
    rw [hcoord]
    let K : Compacts (Domain 2) := ⟨Metric.closedBall 0 1, isCompact_closedBall _ _⟩
    apply P102.Sobolev.MoserMembership.sobolevRestrict_mem_zero
      (by simp [Exponent.ennreal]) disk (U i) K
    · exact Metric.closedBall_subset_ball (by norm_num : (1:ℝ) < 2)
    · filter_upwards [hU i] with x hx hnot
      rw [hx]
      exact image_eq_zero_of_notMem_tsupport (fun h => hnot
        ((scalarField_tsupport i).trans tsupport_radialMap h))
  have hval (i : Fin 2) :
      (coordinateLp disk p i (value disk 2 p u) : Domain 2 → ℝ) =ᵐ[domainMeasure disk]
        scalarField i := by
    rw [← toCoordinates_value disk p u i, hcoord]
    exact (P102.U4.domainLpRestrict_ae disk (P102.U4.sobolevUnderlying (U i))).trans
      (ae_restrict_of_ae (hU i))
  have hvalue : (value disk 2 p u : Domain 2 → Vector 2) =ᵐ[domainMeasure disk] radialMap := by
    have hv := Filter.eventually_all.mpr hval
    have hv' := Filter.eventually_all.mpr (fun i : Fin 2 => coordinateLp_ae disk p i
      (value disk 2 p u))
    filter_upwards [hv, hv'] with x hx hx'
    apply PiLp.ext
    intro i
    exact (hx' i).symm.trans (hx i)
  refine ⟨u, hz, hvalue, ?_⟩
  intro i j
  have hd :
      (coordinateLp disk p (i,j) (gradient disk 2 p u) : Domain 2 → ℝ) =ᵐ[domainMeasure disk]
        scalarDerivative i j := by
    rw [← toCoordinates_derivative disk p u i j, hcoord]
    exact (P102.U4.domainLpRestrict_ae disk (P102.U4.Truncations.sobolevFirstDerivative (U i) j)).trans
      (ae_restrict_of_ae (hDU i j))
  exact (coordinateLp_ae disk p (i,j) (gradient disk 2 p u)).symm.trans hd

theorem infinite_competitor_conditional
    (_existence : Polyconvex.Expected.Existence)
    (_matrixDetExistence : Polyconvex.Expected.MatrixDetExistence) :
    Expected.InfiniteCompetitor := by
  intro p γ hp hp4 hγ
  obtain ⟨u, hzero, hvalue, hgrad⟩ := exists_radial_sobolev p hp4
  have hsub : Metric.ball (0 : Domain 2) (1/2) ⊆ (disk : Set (Domain 2)) :=
    Metric.ball_subset_ball (by norm_num : (1/2:ℝ) ≤ 2)
  have hμ := Measure.restrict_mono hsub (le_refl volume)
  have hdet : ¬ MemLp (fun x => Polyconvex.determinant (gradient disk 2 p u x)) 2
      (domainMeasure disk) := by
    intro hd
    apply core_det_not_memLp
    refine (memLp_congr_ae ?_).mp (MemLp.mono_measure hμ hd)
    have hg := Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hgrad i))
    filter_upwards [ae_mono hμ hg, ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0 : Domain 2))] with x hx hxball hx0
    apply congrArg Polyconvex.determinant
    apply PiLp.ext
    rintro ⟨i,j⟩
    exact (hx i j).trans (scalarDerivative_core i j hx0 (by simpa using hxball))
  refine ⟨u, hzero, hvalue, hdet, ?_⟩
  exact energy_top_of_determinant_not_memLp disk p γ u Metric.isBounded_ball hdet

end VariationalNotes.Sobolev.PolyconvexExample

theorem _root_.«VariationalNotes».«Sobolev».«PolyconvexExample».«attainment» : _root_.«VariationalNotes».«Sobolev».«PolyconvexExample».«Expected».«Attainment» :=
  @_root_.«VariationalNotes».«Sobolev».«PolyconvexExample».«attainment_conditional» (@_root_.«VariationalNotes».«Sobolev».«Polyconvex».«existence») (@_root_.«VariationalNotes».«Sobolev».«Polyconvex».«matrixDet_existence»)
theorem _root_.«VariationalNotes».«Sobolev».«PolyconvexExample».«coercivity» : _root_.«VariationalNotes».«Sobolev».«PolyconvexExample».«Expected».«Coercivity» :=
  @_root_.«VariationalNotes».«Sobolev».«PolyconvexExample».«coercivity_conditional» (@_root_.«VariationalNotes».«Sobolev».«Polyconvex».«existence») (@_root_.«VariationalNotes».«Sobolev».«Polyconvex».«matrixDet_existence»)
theorem _root_.«VariationalNotes».«Sobolev».«PolyconvexExample».«infinite_competitor» : _root_.«VariationalNotes».«Sobolev».«PolyconvexExample».«Expected».«InfiniteCompetitor» :=
  @_root_.«VariationalNotes».«Sobolev».«PolyconvexExample».«infinite_competitor_conditional» (@_root_.«VariationalNotes».«Sobolev».«Polyconvex».«existence») (@_root_.«VariationalNotes».«Sobolev».«Polyconvex».«matrixDet_existence»)
theorem _root_.«VariationalNotes».«Sobolev».«PolyconvexExample».«line_behavior» : _root_.«VariationalNotes».«Sobolev».«PolyconvexExample».«Expected».«LineBehavior» :=
  @_root_.«VariationalNotes».«Sobolev».«PolyconvexExample».«line_behavior_conditional» (@_root_.«VariationalNotes».«Sobolev».«Polyconvex».«existence») (@_root_.«VariationalNotes».«Sobolev».«Polyconvex».«matrixDet_existence»)
theorem _root_.«VariationalNotes».«Sobolev».«PolyconvexExample».«representation» : _root_.«VariationalNotes».«Sobolev».«PolyconvexExample».«Expected».«Representation» :=
  @_root_.«VariationalNotes».«Sobolev».«PolyconvexExample».«representation_conditional» (@_root_.«VariationalNotes».«Sobolev».«Polyconvex».«existence») (@_root_.«VariationalNotes».«Sobolev».«Polyconvex».«matrixDet_existence»)
theorem _root_.«VariationalNotes».«Sobolev».«PolyconvexExample».«zero_competitor» : _root_.«VariationalNotes».«Sobolev».«PolyconvexExample».«Expected».«ZeroCompetitor» :=
  @_root_.«VariationalNotes».«Sobolev».«PolyconvexExample».«zero_competitor_conditional» (@_root_.«VariationalNotes».«Sobolev».«Polyconvex».«existence») (@_root_.«VariationalNotes».«Sobolev».«Polyconvex».«matrixDet_existence»)
