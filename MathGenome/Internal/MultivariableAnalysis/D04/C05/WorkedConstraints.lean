import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.WorkedConstraints
import MathGenome.Internal.MultivariableAnalysis.D04.C05.ExistenceFermat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Set
open scoped RealInnerProductSpace
namespace D04.WorkedConstraints
open Specs.D04.C05.WorkedConstraints.Model

private theorem unit_norm {n : ℕ} {v : E n} (hv : v ≠ 0) : ‖unit v‖ = 1 := by
  simp [unit, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

private theorem objective_unit {n : ℕ} {v : E n} (hv : v ≠ 0) :
    linearObjective v (unit v) = ‖v‖ := by
  dsimp [linearObjective, unit]
  rw [inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp

private theorem sphere_identities {n : ℕ} {v : E n} (hv : v ≠ 0)
    {x : E n} (hx : x ∈ sphere n) :
    linearObjective v x = -‖v‖ + (‖v‖/2) * ‖x - (-unit v)‖^2 ∧
    linearObjective v x = ‖v‖ - (‖v‖/2) * ‖x - unit v‖^2 := by
  have hu := unit_norm hv
  have hx' : ‖x‖ = 1 := hx
  have hinner : inner ℝ x (unit v) = ‖v‖⁻¹ * linearObjective v x := by
    dsimp [unit, linearObjective]
    rw [real_inner_smul_right, real_inner_comm]
  have hpos := norm_pos_iff.mpr hv
  have hminus := norm_sub_sq_real x (unit v)
  have hplus := norm_add_sq_real x (unit v)
  rw [hx', hu, hinner] at hminus hplus
  rw [sub_neg_eq_add]
  constructor <;> dsimp [linearObjective] at *
  · rw [hplus]; field_simp; ring
  · rw [hminus]; field_simp; ring

theorem sphere_compact_existence :
    Specs.D04.C05.WorkedConstraints.sphere_compact_existenceType := by
  intro n hn v
  have hS : IsCompact (sphere n) := by
    convert isCompact_sphere (0 : E n) 1 using 1
    ext x
    simp [sphere]
  have hn0 : 0 < n := by omega
  let i : Fin n := ⟨0, hn0⟩
  have hne : (sphere n).Nonempty := by
    refine ⟨standardBasis n i, ?_⟩
    change ‖standardBasis n i‖ = 1
    exact (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i
  exact ⟨hS, hne, compact_global_extrema _ _
    ((compact_iff_isCompact _).mpr hS) hne (by
      exact (continuous_const.inner continuous_id).continuousOn)⟩

theorem sphere_constraint_derivative :
    Specs.D04.C05.WorkedConstraints.sphere_constraint_derivativeType := by
  intro n x
  refine ⟨(hasStrictFDerivAt_norm_sq x).hasFDerivAt, ?_, ?_⟩
  · intro hx y
    refine ⟨(y/2) • x, ?_⟩
    have hn : ‖x‖ = 1 := hx
    simp [fderiv_norm_sq_apply, hn]
  · intro z
    simp [fderiv_norm_sq_apply, mul_eq_zero]

private theorem sphere_extrema_data {n : ℕ} {v : E n} (hv : v ≠ 0) :
    GlobalMinimumOn (sphere n) (linearObjective v) (-unit v) ∧
    GlobalMaximumOn (sphere n) (linearObjective v) (unit v) ∧
    ∀ x ∈ sphere n, -‖v‖ ≤ linearObjective v x ∧ linearObjective v x ≤ ‖v‖ ∧
      (linearObjective v x = -‖v‖ ↔ x = -unit v) ∧
      (linearObjective v x = ‖v‖ ↔ x = unit v) := by
  have hp := norm_pos_iff.mpr hv
  have hu : unit v ∈ sphere n := unit_norm hv
  have hnu : -unit v ∈ sphere n := by simpa [sphere] using unit_norm hv
  have hval := objective_unit hv
  have hnval : linearObjective v (-unit v) = -‖v‖ := by
    simpa [linearObjective] using congrArg Neg.neg hval
  have hall (x : E n) (hx : x ∈ sphere n) :
      -‖v‖ ≤ linearObjective v x ∧ linearObjective v x ≤ ‖v‖ ∧
      (linearObjective v x = -‖v‖ ↔ x = -unit v) ∧
      (linearObjective v x = ‖v‖ ↔ x = unit v) := by
    obtain ⟨hmin,hmax⟩ := sphere_identities hv hx
    refine ⟨by nlinarith [sq_nonneg ‖x-(-unit v)‖],
      by nlinarith [sq_nonneg ‖x-unit v‖], ?_, ?_⟩
    · constructor
      · intro he
        have hprod : (‖v‖/2) * ‖x-(-unit v)‖^2 = 0 := by linarith
        have hz : ‖x-(-unit v)‖ = 0 :=
          sq_eq_zero_iff.mp ((mul_eq_zero.mp hprod).resolve_left (by positivity))
        exact sub_eq_zero.mp (norm_eq_zero.mp hz)
      · rintro rfl; exact hnval
    · constructor
      · intro he
        have hprod : (‖v‖/2) * ‖x-unit v‖^2 = 0 := by linarith
        have hz : ‖x-unit v‖ = 0 :=
          sq_eq_zero_iff.mp ((mul_eq_zero.mp hprod).resolve_left (by positivity))
        exact sub_eq_zero.mp (norm_eq_zero.mp hz)
      · rintro rfl; exact hval
  exact ⟨⟨hnu, fun x hx => by rw [hnval]; exact (hall x hx).1⟩,
    ⟨hu, fun x hx => by rw [hval]; exact (hall x hx).2.1⟩, hall⟩

theorem sphere_extrema : Specs.D04.C05.WorkedConstraints.sphere_extremaType := by
  intro n v hv
  obtain ⟨hmin,hmax,hall⟩ := sphere_extrema_data hv
  refine ⟨hmin.1, hmax.1, ?_, objective_unit hv, hmin, hmax, hall, ?_, ?_⟩
  · simpa [linearObjective] using congrArg Neg.neg (objective_unit hv)
  · intro x
    constructor
    · intro hx
      apply (hall x hx.1).2.2.1.mp
      apply le_antisymm
      · have h := hx.2 _ hmin.1
        have he : linearObjective v (-unit v) = -‖v‖ := by
          simpa only [linearObjective, inner_neg_right] using congrArg Neg.neg (objective_unit hv)
        rwa [he] at h
      · exact (hall x hx.1).1
    · rintro rfl; exact hmin
  · intro x
    constructor
    · intro hx
      apply (hall x hx.1).2.2.2.mp
      apply le_antisymm (hall x hx.1).2.1
      have h := hx.2 _ hmax.1
      rwa [objective_unit hv] at h
    · rintro rfl; exact hmax

theorem sphere_growth : Specs.D04.C05.WorkedConstraints.sphere_growthType := by
  intro n v hv
  obtain ⟨hmin,hmax,hall⟩ := sphere_extrema_data hv
  refine ⟨⟨hmin.1, 1, zero_lt_one, ?_⟩, ⟨hmax.1, 1, zero_lt_one, ?_⟩,
    by positivity, fun x hx => sphere_identities hv hx⟩
  · intro x hx _ hne
    have hlt : -‖v‖ < linearObjective v x := lt_of_le_of_ne (hall x hx).1
      (fun he => hne ((hall x hx).2.2.1.mp he.symm))
    have he : linearObjective v (-unit v) = -‖v‖ := by
      simpa only [linearObjective, inner_neg_right] using congrArg Neg.neg (objective_unit hv)
    simpa only [he] using hlt
  · intro x hx _ hne
    have hlt : linearObjective v x < ‖v‖ := lt_of_le_of_ne (hall x hx).2.1
      (fun he => hne ((hall x hx).2.2.2.mp he))
    simpa [objective_unit hv] using hlt

private theorem objective_derivative {n : ℕ} (v x : E n) :
    HasFDerivAt (linearObjective v) (innerSL ℝ v) x :=
  (innerSL ℝ v).hasFDerivAt

theorem sphere_multipliers : Specs.D04.C05.WorkedConstraints.sphere_multipliersType := by
  intro n v hv x hx lam
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hn : ‖x‖ = 1 := hx
  constructor
  · constructor
    · intro he
      have heNorm : ‖v‖ = |2*lam| := by
        rw [he, norm_smul, hn, mul_one, Real.norm_eq_abs]
      have heUnit : unit v = (‖v‖⁻¹ * (2*lam)) • x := by
        rw [unit, he, smul_smul]
      by_cases hl : lam < 0
      · left
        have hl' : lam = -‖v‖/2 := by rw [abs_of_neg (by linarith)] at heNorm; linarith
        refine ⟨?_,hl'⟩
        rw [hl'] at heUnit
        have hc : ‖v‖⁻¹ * (2 * (-‖v‖/2)) = -1 := by field_simp
        rw [hc, neg_one_smul] at heUnit
        simpa only [neg_neg] using (congrArg Neg.neg heUnit).symm
      · right
        have hl' : lam = ‖v‖/2 := by rw [abs_of_nonneg (by linarith)] at heNorm; linarith
        refine ⟨?_,hl'⟩
        rw [hl'] at heUnit
        have hc : ‖v‖⁻¹ * (2 * (‖v‖/2)) = 1 := by field_simp
        simpa only [hc, one_smul] using heUnit.symm
    · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · dsimp [unit]
        rw [smul_neg, smul_smul, ← neg_smul]
        have hc : -(2 * (-‖v‖/2) * ‖v‖⁻¹) = 1 := by field_simp
        rw [hc, one_smul]
      · dsimp [unit]
        rw [smul_smul]
        convert (one_smul ℝ v).symm using 1
        congr 1
        field_simp
  · rw [(objective_derivative v x).fderiv, fderiv_norm_sq_apply]
    constructor
    · intro he
      apply ext_inner_right ℝ
      intro z
      have h := congrArg (fun A : E n →L[ℝ] ℝ => A z) he
      simpa [real_inner_smul_left, mul_assoc, mul_comm, mul_left_comm] using h
    · intro he
      ext z
      rw [he]
      simp [mul_assoc, mul_comm]

private theorem lagrangian_derivative {n : ℕ} (v x : E n) (lam : ℝ) :
    HasFDerivAt (sphereLagrangian v lam)
      (innerSL ℝ v - lam • (2 • innerSL ℝ x)) x := by
  exact (objective_derivative v x).sub ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul lam)

theorem sphere_lagrangian_hessian :
    Specs.D04.C05.WorkedConstraints.sphere_lagrangian_hessianType := by
  intro n v x lam z w
  rw [iteratedFDeriv_two_apply]
  let B : E n →L[ℝ] (E n →L[ℝ] ℝ) := innerSL ℝ
  have he : fderiv ℝ (sphereLagrangian v lam) =
      fun y => innerSL ℝ v - (lam * 2) • B y := by
    funext y
    simpa only [B, two_smul, smul_add, mul_two, add_smul] using (lagrangian_derivative v y lam).fderiv
  rw [he]
  have hdB : HasFDerivAt (fun y : E n => B y) B x := B.hasFDerivAt
  have hd := (hasFDerivAt_const (innerSL ℝ v) x).sub (hdB.const_smul (lam * 2))
  change HasFDerivAt (fun y : E n => innerSL ℝ v - (lam * 2) • B y) _ x at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_sub, ContinuousLinearMap.neg_apply, smul_eq_mul]
  change -(lam * 2 * inner ℝ z w) = (-2*lam) * inner ℝ z w
  ring

theorem sphere_hessian_classification :
    Specs.D04.C05.WorkedConstraints.sphere_hessian_classificationType := by
  intro n v hv z hz
  constructor <;> intro _ <;> rw [sphere_lagrangian_hessian]
  · have hp := real_inner_self_pos.mpr hz
    have hn := norm_pos_iff.mpr hv
    nlinarith
  · have hp := real_inner_self_pos.mpr hz
    have hn := norm_pos_iff.mpr hv
    nlinarith

private theorem norm_sq_two (x : E 2) : ‖x‖^2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

private theorem norm_sq_one (x : E 1) : ‖x‖^2 = x 0 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

private theorem coord_derivative (i : Fin 2) (a : E 2) :
    HasFDerivAt (fun x : E 2 => x i) (EuclideanSpace.proj (𝕜 := ℝ) i) a :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt

private theorem coord_derivative_ne (i : Fin 2) (a : E 2) :
    fderiv ℝ (fun x : E 2 => x i) a ≠ 0 := by
  rw [(coord_derivative i a).fderiv]
  intro he
  have h := congrArg (fun A : E 2 →L[ℝ] ℝ => A (standardBasis 2 i)) he
  simpa [standardBasis, Specs.D04.C01.EuclideanInterfaces.standardBasisValue,
    Specs.D04.C01.EuclideanInterfaces.Model.standardBasis] using h

theorem sphere_one_dimension : Specs.D04.C05.WorkedConstraints.sphere_one_dimensionType := by
  have hcoord (x : E 1) : x ∈ sphere 1 ↔ x 0 = -1 ∨ x 0 = 1 := by
    have hn := norm_sq_one x
    constructor
    · intro hx
      change ‖x‖ = 1 at hx
      rw [hx] at hn
      have he : (x 0 - 1) * (x 0 + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp he with h | h
      · right; linarith
      · left; linarith
    · intro hx
      change ‖x‖ = 1
      rcases hx with hx | hx <;> rw [hx] at hn <;> nlinarith [norm_nonneg x]
  refine ⟨Set.ext hcoord, ?_⟩
  intro a ha
  have hiso : ∀ x ∈ sphere 1, ‖x-a‖ < 1 → x = a := by
    intro x hx hb
    have hn := norm_sq_one (x-a)
    have hxa : x 0 = a 0 := by
      rcases (hcoord x).mp hx with hx | hx <;>
        rcases (hcoord a).mp ha with ha | ha <;>
        simp only [PiLp.sub_apply] at hn <;> rw [hx,ha] at hn <;>
        nlinarith [norm_nonneg (x-a)]
    ext i
    fin_cases i
    exact hxa
  refine ⟨⟨1,zero_lt_one,hiso⟩, fun f => ?_⟩
  constructor <;> exact ⟨ha,1,zero_lt_one, fun x hx hb hne => (hne (hiso x hx hb)).elim⟩

theorem sphere_zero_objective : Specs.D04.C05.WorkedConstraints.sphere_zero_objectiveType := by
  intro n a ha
  constructor <;> refine ⟨ha, ?_⟩ <;> intro x hx <;> simp [linearObjective]

theorem singular_origin : Specs.D04.C05.WorkedConstraints.singular_originType := by
  let S : Set (E 2) := {x | x 0 ^ 2 + x 1 ^ 2 = 0}
  have hS : S = {0} := by
    ext x
    constructor
    · intro hx
      have he : x 0 ^ 2 + x 1 ^ 2 = 0 := hx
      have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 1)]
      have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0)]
      apply Set.mem_singleton_iff.mpr
      ext i; fin_cases i <;> assumption
    · rintro rfl; simp [S]
  change S = {0} ∧ _
  refine ⟨hS, ?_, ?_⟩
  · intro f
    change GlobalMinimumOn S f 0 ∧ GlobalMaximumOn S f 0 ∧
      StrictLocalMinimumOn S f 0 ∧ StrictLocalMaximumOn S f 0
    rw [hS]
    refine ⟨⟨by simp, fun x hx => by simpa using le_of_eq (congrArg f (Set.mem_singleton_iff.mp hx).symm)⟩,
      ⟨by simp, fun x hx => by simpa using le_of_eq (congrArg f (Set.mem_singleton_iff.mp hx))⟩,
      ⟨by simp,1,zero_lt_one, ?_⟩,⟨by simp,1,zero_lt_one, ?_⟩⟩
    all_goals intro x hx _ hne; exact (hne (Set.mem_singleton_iff.mp hx)).elim
  · intro lam
    have hd := ((coord_derivative 0 0).pow 2).add ((coord_derivative 1 0).pow 2)
    change HasFDerivAt (fun x : E 2 => x 0^2 + x 1^2) _ 0 at hd
    have he : fderiv ℝ (fun x : E 2 => x 0^2 + x 1^2) 0 = 0 := by
      rw [hd.fderiv]; simp
    rw [he, smul_zero]
    exact coord_derivative_ne 0 0

theorem singular_axis : Specs.D04.C05.WorkedConstraints.singular_axisType := by
  have heq : {x : E 2 | x 1 ^ 2 = 0} = {x | x 1 = 0} := by
    ext x; simp only [Set.mem_ofPred_eq, sq_eq_zero_iff]
  refine ⟨heq, ?_⟩
  intro a ha
  have ha0 : a 1 = 0 := sq_eq_zero_iff.mp ha
  have hall (x : E 2) (hx : x 1 ^ 2 = 0) : x 1 = 0 := sq_eq_zero_iff.mp hx
  have hd := (coord_derivative 1 a).pow 2
  have hdz : fderiv ℝ (fun x : E 2 => x 1 ^ 2) a = 0 := by
    rw [hd.fderiv]; simp [ha0]
  refine ⟨hall, ⟨ha,fun x hx => by simpa only [ha0,hall x hx] using le_refl (0 : ℝ)⟩,
    ⟨ha,fun x hx => by simpa only [ha0,hall x hx] using le_refl (0 : ℝ)⟩, hdz, ?_⟩
  intro lam
  rw [hdz, smul_zero]
  exact coord_derivative_ne 1 a

private theorem disk_data :
    GlobalMinimumOn disk (fun x => x 0) (point (-1) 0) ∧
    GlobalMaximumOn disk (fun x => x 0) (point 1 0) ∧
    ∀ x ∈ disk, -1 ≤ x 0 ∧ x 0 ≤ 1 ∧
      (x 0 = -1 ↔ x = point (-1) 0) ∧ (x 0 = 1 ↔ x = point 1 0) := by
  have hall (x : E 2) (hx : x ∈ disk) : -1 ≤ x 0 ∧ x 0 ≤ 1 ∧
      (x 0 = -1 ↔ x = point (-1) 0) ∧ (x 0 = 1 ↔ x = point 1 0) := by
    change x 0 ^ 2 + x 1 ^ 2 ≤ 1 at hx
    refine ⟨by nlinarith [sq_nonneg (x 1)], by nlinarith [sq_nonneg (x 1)], ?_, ?_⟩
    · constructor
      · intro h0
        have h1 : x 1 = 0 := by rw [h0] at hx; nlinarith
        ext i; fin_cases i <;> assumption
      · rintro rfl; rfl
    · constructor
      · intro h0
        have h1 : x 1 = 0 := by rw [h0] at hx; nlinarith
        ext i; fin_cases i <;> assumption
      · rintro rfl; rfl
  refine ⟨⟨by norm_num [disk,point],fun x hx => (hall x hx).1⟩,
    ⟨by norm_num [disk,point], fun x hx => (hall x hx).2.1⟩,hall⟩

theorem disk_extrema : Specs.D04.C05.WorkedConstraints.disk_extremaType := by
  obtain ⟨hmin,hmax,hall⟩ := disk_data
  refine ⟨?_, ?_, hmin,hmax, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [disk, Set.mem_ofPred_eq]
    rw [← norm_sq_two]
    constructor <;> intro h <;> nlinarith [norm_nonneg x]
  · ext x
    simp only [disk,diskConstraint, Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  · intro x
    constructor
    · intro hx
      exact (hall x hx.1).2.2.1.mp (le_antisymm (by simpa [point] using hx.2 _ hmin.1)
        (hall x hx.1).1)
    · rintro rfl; exact hmin
  · intro x
    constructor
    · intro hx
      exact (hall x hx.1).2.2.2.mp (le_antisymm (hall x hx.1).2.1
        (by simpa [point] using hx.2 _ hmax.1))
    · rintro rfl; exact hmax
  all_goals
    intro hs
    exact coord_derivative_ne 0 _ ((stationaryPoint_iff _ _ _).mp hs).2.2.2

private theorem disk_constraint_derivative (a : E 2) :
    HasFDerivAt diskConstraint
      (0 - (2*a 0) • EuclideanSpace.proj (𝕜 := ℝ) 0 -
        (2*a 1) • EuclideanSpace.proj (𝕜 := ℝ) 1) a := by
  have hd := ((hasFDerivAt_const (1 : ℝ) a).sub ((coord_derivative 0 a).pow 2)).sub
    ((coord_derivative 1 a).pow 2)
  change HasFDerivAt diskConstraint _ a at hd
  convert hd using 1; norm_num

theorem disk_multipliers : Specs.D04.C05.WorkedConstraints.disk_multipliersType := by
  refine ⟨by norm_num, by norm_num [diskConstraint,point],
    by norm_num [diskConstraint,point], ?_, ?_⟩
  · rw [(coord_derivative 0 _).fderiv, (disk_constraint_derivative _).fderiv]
    ext z
    simp [point]
  · have hd := (coord_derivative 0 (point 1 0)).neg
    change HasFDerivAt (fun x : E 2 => -x 0) _ (point 1 0) at hd
    rw [hd.fderiv, (disk_constraint_derivative _).fderiv]
    ext z
    simp [point]

private theorem corner_derivative (a : E 2) :
    HasFDerivAt cornerObjective
      (EuclideanSpace.proj (𝕜 := ℝ) 0 + EuclideanSpace.proj (𝕜 := ℝ) 1) a :=
  (coord_derivative 0 a).add (coord_derivative 1 a)

private theorem box_derivative (i : Fin 4) (a : E 2) :
    fderiv ℝ (fun x : E 2 => boxConstraints x i) a =
      ![EuclideanSpace.proj (𝕜 := ℝ) 0, EuclideanSpace.proj (𝕜 := ℝ) 1,
        -EuclideanSpace.proj (𝕜 := ℝ) 0, -EuclideanSpace.proj (𝕜 := ℝ) 1] i := by
  fin_cases i
  · exact (coord_derivative 0 a).fderiv
  · exact (coord_derivative 1 a).fderiv
  · have hd := (hasFDerivAt_const (1 : ℝ) a).sub (coord_derivative 0 a)
    change HasFDerivAt (fun x : E 2 => boxConstraints x 2) _ a at hd
    simpa using hd.fderiv
  · have hd := (hasFDerivAt_const (1 : ℝ) a).sub (coord_derivative 1 a)
    change HasFDerivAt (fun x : E 2 => boxConstraints x 3) _ a at hd
    simpa using hd.fderiv

theorem corner_constraints : Specs.D04.C05.WorkedConstraints.corner_constraintsType := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx i
      fin_cases i
      · exact hx.1
      · exact hx.2.2.1
      · change 0 ≤ 1 - x 0; linarith [hx.2.1]
      · change 0 ≤ 1 - x 1; linarith [hx.2.2.2]
    · intro hx
      have h0 := hx 0
      have h1 := hx 1
      have h2 := hx 2
      have h3 := hx 3
      change 0 ≤ x 0 at h0
      change 0 ≤ x 1 at h1
      change 0 ≤ 1-x 0 at h2
      change 0 ≤ 1-x 1 at h3
      exact ⟨h0,by linarith,h1,by linarith⟩
  · intro i; fin_cases i <;> norm_num [boxConstraints]
  · intro i; fin_cases i <;> norm_num [boxMultipliers]
  · intro i; fin_cases i <;> norm_num [boxMultipliers,boxConstraints]
  · rw [(corner_derivative 0).fderiv]
    simp [Fin.sum_univ_succ, boxMultipliers, box_derivative]
  · ext z
    constructor
    · intro hz
      have h0 := hz.2.1 ⟨0,by rfl⟩
      have h1 := hz.2.1 ⟨1,by rfl⟩
      have hf := hz.2.2
      change fderiv ℝ cornerObjective 0 z = 0 at hf
      change 0 ≤ fderiv ℝ (fun x : E 2 => boxConstraints x 0) 0 z at h0
      change 0 ≤ fderiv ℝ (fun x : E 2 => boxConstraints x 1) 0 z at h1
      rw [box_derivative] at h0 h1
      rw [(corner_derivative 0).fderiv] at hf
      change 0 ≤ z 0 at h0
      change 0 ≤ z 1 at h1
      change z 0 + z 1 = 0 at hf
      have hz0 : z 0 = 0 := by linarith
      have hz1 : z 1 = 0 := by linarith
      apply Set.mem_singleton_iff.mpr
      ext i; fin_cases i <;> assumption
    · rintro rfl
      change fderiv ℝ noEqualities 0 0 = 0 ∧ _
      simp only [map_zero, true_and]
      refine ⟨fun i => ?_, by simp⟩
      exact le_refl 0

private theorem corner_norm_bound (x : E 2) (hx : x ∈ square) :
    ‖x‖ ≤ cornerObjective x := by
  have hn := norm_sq_two x
  have hnon : 0 ≤ x 0 + x 1 := add_nonneg hx.1 hx.2.2.1
  have hmul := mul_nonneg hx.1 hx.2.2.1
  dsimp [cornerObjective]
  nlinarith [norm_nonneg x]

theorem corner_growth : Specs.D04.C05.WorkedConstraints.corner_growthType := by
  have ha : (0 : E 2) ∈ square := by norm_num [square]
  refine ⟨⟨ha, fun x hx => ?_⟩, ⟨ha,1,zero_lt_one, ?_⟩, ?_, 1,zero_lt_one,1,zero_lt_one, ?_⟩
  · simpa [cornerObjective] using add_nonneg hx.1 hx.2.2.1
  · intro x hx _ hne
    have hp := norm_pos_iff.mpr (show x ≠ 0 from hne)
    have hb := corner_norm_bound x hx
    have hg : 0 < cornerObjective x := lt_of_lt_of_le hp hb
    simpa [cornerObjective] using hg
  · intro x hx
    rw [← norm_sq_two, Real.sqrt_sq (norm_nonneg x)]
    exact corner_norm_bound x hx
  · intro x hx hn
    have hb := corner_norm_bound x hx
    simp only [cornerObjective, PiLp.zero_apply, zero_add, sub_zero, one_mul]
    change ‖x‖^2 ≤ x 0 + x 1
    change ‖x‖ ≤ x 0 + x 1 at hb
    nlinarith [norm_nonneg x]

end D04.WorkedConstraints
