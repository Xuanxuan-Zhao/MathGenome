import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.AnnularOrientationsAndPeriods
import MathGenome.Internal.MultivariableAnalysis.D04.C12.GreenCirculationAndFlux
import MathGenome.Internal.MultivariableAnalysis.D04.C09.CircleMultiplicity
import Mathlib.Analysis.Normed.Module.RCLike.Real

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set Filter Topology
open scoped ContDiff BigOperators
open SingleVariableAnalysis.Riemann
namespace D04.Annulus
open Specs.D04.C12.AnnularOrientationsAndPeriods
open Specs.D04.C12.AnnularOrientationsAndPeriods.Model
open D04.C09 D04.C09.CircleMultiplicity
open Specs.D04.C12.ClassicalRegularDomains.Model

abbrev annulus : annulusType := Model.annulus
abbrev leftTurn : leftTurnType := Model.leftTurn
abbrev radiusCircle : radiusCircleType := Model.radiusCircle
abbrev radiusVelocity : radiusCircleType := Model.radiusVelocity
abbrev radiusPath : radiusPathType := Model.radiusPath

theorem annulus_coordinates : annulus_coordinatesType := by
  intro a b
  have hn (x : E 2) : ‖x‖ = Real.sqrt ((x 0)^2 + (x 1)^2) := by
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  ext x
  simp only [annulus, Model.annulus, mem_setOf_eq, hn]

lemma annulus_open (a b : ℝ) : IsOpen (annulus a b) :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

lemma annulus_bounded (a b : ℝ) : Bornology.IsBounded (annulus a b) :=
  (Metric.isBounded_ball (x := (0 : E 2)) (r := b)).subset (by
    intro x hx
    simpa only [Metric.mem_ball, dist_zero_right] using hx.2)

lemma closure_bounds (a b : ℝ) :
    closure (annulus a b) ⊆ {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} := by
  apply closure_minimal
  · intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)

private lemma open_inter_closure {X : Type*} [TopologicalSpace X]
    {S T : Set X} (hS : IsOpen S) {x : X} (hx : x ∈ S) (ht : x ∈ closure T) :
    x ∈ closure (S ∩ T) := by
  rw [mem_closure_iff] at ht ⊢
  intro O hO hxO
  obtain ⟨y, hy, hyt⟩ := ht (O ∩ S) (hO.inter hS) ⟨hxO, hx⟩
  exact ⟨y, hy.1, hy.2, hyt⟩

lemma outer_mem_closure {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {x : E 2} (hx : ‖x‖ = b) : x ∈ closure (annulus a b) := by
  have ht : x ∈ closure (Metric.ball (0 : E 2) b) := by
    rw [closure_ball _ (ha.trans hab).ne']
    simpa [Metric.mem_closedBall, hx] using (le_refl b)
  have hm : x ∈ closure ({y : E 2 | a < ‖y‖} ∩ Metric.ball 0 b) :=
    open_inter_closure (isOpen_lt continuous_const continuous_norm) (by simpa [hx]) ht
  have he : annulus a b = {y : E 2 | a < ‖y‖} ∩ Metric.ball 0 b := by
    ext y
    simp [annulus, Model.annulus, Metric.mem_ball]
  rwa [← he] at hm

lemma inner_mem_closure {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {x : E 2} (hx : ‖x‖ = a) : x ∈ closure (annulus a b) := by
  have ht : x ∈ closure (Metric.closedBall (0 : E 2) a)ᶜ := by
    rw [closure_compl, interior_closedBall _ ha.ne']
    simpa [Metric.mem_ball, hx]
  have hm := open_inter_closure (Metric.isOpen_ball (x := (0 : E 2)) (ε := b))
    (x := x) (by simpa [Metric.mem_ball, hx] using hab) ht
  have he : annulus a b = Metric.ball 0 b ∩ (Metric.closedBall 0 a)ᶜ := by
    ext y
    simp only [annulus, Model.annulus, mem_inter_iff, mem_setOf_eq, mem_compl_iff,
      Metric.mem_ball, Metric.mem_closedBall, dist_zero_right, not_le]
    exact and_comm
  rwa [← he] at hm

theorem annulus_closure : annulus_closureType := by
  intro a b ha hab
  apply Subset.antisymm (closure_bounds a b)
  intro x hx
  rcases hx.1.lt_or_eq with hax | hax
  · rcases hx.2.lt_or_eq with hxb | hxb
    · exact subset_closure ⟨hax, hxb⟩
    · exact outer_mem_closure ha hab hxb
  · exact inner_mem_closure ha hab hax.symm

theorem annulus_frontier : annulus_frontierType := by
  intro a b ha hab
  rw [(annulus_open a b).frontier_eq, annulus_closure ha hab]
  ext x
  simp only [Set.mem_sdiff, mem_setOf_eq, annulus, Model.annulus]
  constructor
  · rintro ⟨⟨hax, hxb⟩, hn⟩
    by_cases he : ‖x‖ = a
    · exact Or.inl he
    · exact Or.inr (le_antisymm hxb (not_lt.mp (fun h => hn ⟨lt_of_le_of_ne hax (Ne.symm he), h⟩)))
  · rintro (he | he)
    · subst a
      exact ⟨⟨le_rfl, hab.le⟩, fun h => (lt_irrefl _) h.1⟩
    · subst b
      exact ⟨⟨hab.le, le_rfl⟩, fun h => (lt_irrefl _) h.2⟩

/-- Squared radii avoid differentiating the norm at the origin. -/
lemma outer_differential (r : ℝ) (x : E 2) :
    fderiv ℝ (fun y : E 2 => ‖y‖^2 - r^2) x = 2 • innerSL ℝ x := by
  simpa using ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const (r^2)).fderiv

lemma inner_differential (r : ℝ) (x : E 2) :
    fderiv ℝ (fun y : E 2 => r^2 - ‖y‖^2) x = -(2 • innerSL ℝ x) := by
  simpa using ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_sub (r^2)).fderiv

lemma outer_gradient (r : ℝ) (x : E 2) :
    _root_.gradient (fun y : E 2 => ‖y‖^2 - r^2) x = (2 : ℝ) • x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, outer_differential]
  simp [real_inner_smul_left]

lemma inner_gradient (r : ℝ) (x : E 2) :
    _root_.gradient (fun y : E 2 => r^2 - ‖y‖^2) x = -(2 : ℝ) • x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, inner_differential]
  simp [real_inner_smul_left]

lemma square_lt_iff {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    r^2 < s^2 ↔ r < s := by
  constructor <;> intro h <;> nlinarith

lemma square_eq_iff {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    r^2 = s^2 ↔ r = s := by
  constructor <;> intro h <;> nlinarith

lemma outer_defining {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IsDefiningFunction (annulus a b) {x | a < ‖x‖}
      (fun x : E 2 => ‖x‖^2 - b^2) := by
  refine ⟨isOpen_lt continuous_const continuous_norm,
    ((contDiff_norm_sq ℝ).sub contDiff_const).contDiffOn, ?_, ?_, ?_⟩
  · intro x hx
    change (a < ‖x‖ ∧ ‖x‖ < b) ↔ ‖x‖^2 - b^2 < 0
    rw [sub_neg, square_lt_iff (norm_nonneg _) (ha.trans hab).le]
    exact and_iff_right hx
  · intro x hx
    rw [annulus_frontier ha hab]
    change (‖x‖ = a ∨ ‖x‖ = b) ↔ ‖x‖^2 - b^2 = 0
    rw [sub_eq_zero, square_eq_iff (norm_nonneg _) (ha.trans hab).le]
    exact or_iff_right (ne_of_gt hx)
  · intro x hx _ hz
    have he : _root_.gradient (fun y : E 2 => ‖y‖^2 - b^2) x = 0 := by
      unfold gradient
      rw [hz]
      simp
    rw [outer_gradient] at he
    have hzero : x = 0 := (smul_eq_zero.mp he).resolve_left (by norm_num)
    have hbad : a < 0 := by simpa [hzero] using hx
    linarith

lemma inner_defining {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IsDefiningFunction (annulus a b) {x | ‖x‖ < b}
      (fun x : E 2 => a^2 - ‖x‖^2) := by
  refine ⟨isOpen_lt continuous_norm continuous_const,
    (contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffOn, ?_, ?_, ?_⟩
  · intro x hx
    change (a < ‖x‖ ∧ ‖x‖ < b) ↔ a^2 - ‖x‖^2 < 0
    rw [sub_neg, square_lt_iff ha.le (norm_nonneg _)]
    exact and_iff_left hx
  · intro x hx
    rw [annulus_frontier ha hab]
    change (‖x‖ = a ∨ ‖x‖ = b) ↔ a^2 - ‖x‖^2 = 0
    rw [sub_eq_zero, square_eq_iff ha.le (norm_nonneg _), eq_comm]
    exact or_iff_left (ne_of_lt hx)
  · intro x _ hzero hz
    have he : _root_.gradient (fun y : E 2 => a^2 - ‖y‖^2) x = 0 := by
      unfold gradient
      rw [hz]
      simp
    rw [inner_gradient] at he
    have hzero' : x = 0 := (smul_eq_zero.mp he).resolve_left (by norm_num)
    simp only [hzero', norm_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero] at hzero
    exact (pow_ne_zero 2 ha.ne') hzero

theorem annulus_regular : annulus_regularType := by
  intro a b ha hab
  refine ⟨by norm_num, annulus_bounded a b, annulus_open a b, ?_⟩
  intro p hp
  rw [annulus_frontier ha hab] at hp
  rcases hp with hp | hp
  · exact ⟨{x | ‖x‖ < b}, (fun x => a^2 - ‖x‖^2), by simpa [hp] using hab,
      inner_defining ha hab⟩
  · exact ⟨{x | a < ‖x‖}, (fun x => ‖x‖^2 - b^2), by simpa [hp] using hab,
      outer_defining ha hab⟩

theorem outward_normals : outward_normalsType := by
  intro a b ha hab hD p
  have hb : 0 < b := ha.trans hab
  constructor
  · intro hp
    rw [ClassicalRegularDomains.outwardNormal_formula hD p (outer_defining ha hab)
      (by change a < ‖(p : E 2)‖; simpa [hp] using hab)]
    change ‖_root_.gradient _ _‖⁻¹ • _root_.gradient _ _ = _
    rw [outer_gradient, norm_smul, hp]
    norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : 0 < (2 : ℝ))]
    ext i
    simp only [PiLp.smul_apply, smul_eq_mul]
    field_simp
  · intro hp
    rw [ClassicalRegularDomains.outwardNormal_formula hD p (inner_defining ha hab)
      (by change ‖(p : E 2)‖ < b; simpa [hp] using hab)]
    change ‖_root_.gradient _ _‖⁻¹ • _root_.gradient _ _ = _
    rw [inner_gradient, norm_smul, hp]
    norm_num only [Real.norm_eq_abs, abs_neg, abs_of_pos (by norm_num : 0 < (2 : ℝ))]
    ext i
    simp only [PiLp.smul_apply, smul_eq_mul, PiLp.neg_apply]
    field_simp

@[simp] lemma leftTurn_twice (v : E 2) : leftTurn (leftTurn v) = -v := by
  ext i
  fin_cases i <;> simp [leftTurn, Model.leftTurn]

theorem region_left : region_leftType := by
  intro a b ha hab hD p
  refine ⟨b-a, sub_pos.mpr hab, ?_⟩
  intro ε hε hεsmall
  change (p : E 2) + ε • leftTurn (leftTurn (outwardNormal hD p)) ∈ annulus a b
  rw [leftTurn_twice]
  have hp : ‖(p : E 2)‖ = a ∨ ‖(p : E 2)‖ = b :=
    (Set.ext_iff.mp (annulus_frontier ha hab) (p : E 2)).mp p.property
  rcases hp with hp | hp
  · rw [(outward_normals ha hab hD p).2 hp, neg_neg]
    have he : (p : E 2) + ε • (a⁻¹ • (p : E 2)) = ((a+ε)/a) • (p : E 2) := by
      ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp <;> ring
    rw [he]
    have hn : ‖((a+ε)/a) • (p : E 2)‖ = a+ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by linarith) ha), hp]
      field_simp
    change a < _ ∧ _ < b
    rw [hn]
    constructor <;> linarith
  · rw [(outward_normals ha hab hD p).1 hp]
    have hb : 0 < b := ha.trans hab
    have he : (p : E 2) + ε • -(b⁻¹ • (p : E 2)) = ((b-ε)/b) • (p : E 2) := by
      ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      field_simp <;> ring
    rw [he]
    have hn : ‖((b-ε)/b) • (p : E 2)‖ = b-ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by linarith) hb), hp]
      field_simp
    change a < _ ∧ _ < b
    rw [hn]
    constructor <;> linarith

lemma radius_derivative (r : ℝ) (m : ℤ) (t : ℝ) :
    HasDerivAt (radiusCircle r m) (radiusVelocity r m t) t :=
  (circle_derivative m t).const_smul r

lemma radius_velocity_continuous (r : ℝ) (m : ℤ) : Continuous (radiusVelocity r m) :=
  (velocity_continuous m).const_smul r

lemma radius_norm {r : ℝ} (hr : 0 < r) (m : ℤ) (t : ℝ) :
    ‖radiusCircle r m t‖ = r := by
  rw [radiusCircle, Model.radiusCircle, norm_smul, Real.norm_eq_abs, abs_of_pos hr, circle_norm, mul_one]

lemma radius_piecewiseC1 (r : ℝ) (m : ℤ) : PiecewiseC1 (radiusPath r m) := by
  obtain ⟨P⟩ := partition_exists (radiusPath r m).ordered
  refine ⟨⟨P, fun _ => radiusVelocity r m, ?_⟩⟩
  intro i
  exact ⟨(radius_velocity_continuous r m).continuousOn,
    fun t _ => (radius_derivative r m t).hasDerivWithinAt⟩

lemma radius_velocity_agrees (r : ℝ) (m : ℤ) (d : PiecewiseC1Data (radiusPath r m))
    (i : Fin d.partition.n) {t : ℝ} (ht : t ∈ cell d.partition i) :
    d.velocity i t = radiusVelocity r m t := by
  have hu := uniqueDiffOn_Icc (d.partition.strictMono (Fin.castSucc_lt_succ (i := i))) t ht
  exact ((d.smooth i).2 t ht).derivWithin hu |>.symm.trans
    ((radius_derivative r m t).hasDerivWithinAt.derivWithin hu)

theorem radius_path_geometry : radius_path_geometryType := by
  intro r hr m hm
  refine ⟨?_, congrArg (fun x : E 2 => r • x) (circle_closed m), ?_⟩
  · ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact radius_norm hr m t
    · intro hx
      have hn : ‖r⁻¹ • x‖ = 1 := by
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr, hx, inv_mul_cancel₀ hr.ne']
      have hc : r⁻¹ • x ∈ trace (circlePath m) := by
        rw [circle_trace m hm]
        exact hn
      obtain ⟨t, ht, he⟩ := hc
      refine ⟨t, ht, ?_⟩
      change r • circle m t = x
      rw [show circle m t = r⁻¹ • x from he, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  · obtain ⟨d⟩ := radius_piecewiseC1 r m
    refine ⟨d, ?_⟩
    intro i t ht
    rw [radius_velocity_agrees r m d i ht]
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hn : ‖radiusVelocity r m t‖ = r * |(m : ℝ)| := by
      rw [radiusVelocity, Model.radiusVelocity, norm_smul, Real.norm_eq_abs, abs_of_pos hr, circle_speed]
    exact norm_ne_zero_iff.mp (hn ▸ mul_ne_zero hr.ne' (abs_ne_zero.mpr hm'))

lemma radius_angular_work {r : ℝ} (hr : 0 < r) (m : ℤ) (t : ℝ) :
    inner ℝ (angularField (radiusCircle r m t)) (radiusVelocity r m t) = (m : ℝ) := by
  have hs := Real.cos_sq_add_sin_sq ((m : ℝ)*t)
  rw [D04.inner_coordinates]
  simp only [Fin.sum_univ_two, angularField,
    Specs.D04.C09.CircleMultiplicity.Model.angularField, radiusCircle, Model.radiusCircle, radiusVelocity, Model.radiusVelocity,
    PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    circle_zero, circle_one, velocity_zero, velocity_one]
  have hden : (r * Real.cos ((m : ℝ)*t))^2 +
      (r * Real.sin ((m : ℝ)*t))^2 = r^2 := by nlinarith
  rw [hden]
  field_simp
  rw [Real.sin_sq_add_cos_sq, mul_one]

theorem radius_period : radius_periodType := by
  intro r hr m d
  obtain ⟨h, he⟩ := pieceIntegral_constant d (fun x v => inner ℝ (angularField x) v) (m : ℝ)
    (fun i t ht => by
      rw [radius_velocity_agrees r m d i ht]
      exact radius_angular_work hr m t)
  exact ⟨h, he.trans (by ring)⟩

theorem boundary_periods : boundary_periodsType := by
  intro a b ha hab outer inner
  obtain ⟨ho, hoval⟩ := radius_period (ha.trans hab) 1 outer
  obtain ⟨hi, hival⟩ := radius_period ha (-1) inner
  refine ⟨ho, hi, ?_, ?_, ?_⟩
  · simpa using hoval
  · simpa using hival
  · rw [hoval, hival]
    norm_num

@[simp] lemma leftTurn_smul (c : ℝ) (v : E 2) : leftTurn (c • v) = c • leftTurn v := by
  ext i
  fin_cases i <;> simp [leftTurn, Model.leftTurn, mul_neg]

@[simp] lemma leftTurn_neg (v : E 2) : leftTurn (-v) = -leftTurn v := by
  simpa only [neg_one_smul] using leftTurn_smul (-1) v

lemma velocity_turn (m : ℤ) (t : ℝ) :
    circleVelocity m t = (m : ℝ) • leftTurn (circle m t) := by
  ext i
  fin_cases i <;> simp [leftTurn, Model.leftTurn]

theorem boundary_traversals : boundary_traversalsType := by
  intro a b ha hab hD t
  have hb := ha.trans hab
  have hpo : radiusCircle b 1 t ∈ frontier (annulus a b) := by
    rw [annulus_frontier ha hab]
    exact Or.inr (radius_norm hb 1 t)
  have hpi : radiusCircle a (-1) t ∈ frontier (annulus a b) := by
    rw [annulus_frontier ha hab]
    exact Or.inl (radius_norm ha (-1) t)
  constructor
  · refine ⟨hpo, ?_⟩
    rw [(outward_normals ha hab hD ⟨_, hpo⟩).1 (radius_norm hb 1 t)]
    simp [Model.radiusVelocity, radiusCircle, Model.radiusCircle, smul_smul, hb.ne', velocity_turn]
  · refine ⟨hpi, ?_⟩
    rw [(outward_normals ha hab hD ⟨_, hpi⟩).2 (radius_norm ha (-1) t)]
    simp [Model.radiusVelocity, radiusCircle, Model.radiusCircle, smul_smul, ha.ne', velocity_turn]

theorem field_neighborhood : field_neighborhoodType := by
  intro a b ha hab
  refine ⟨puncturedPlane_open, ?_, angularField_C1, ?_⟩
  · intro x hx hz
    have hn := (closure_bounds a b hx).1
    rw [hz, norm_zero] at hn
    linarith
  · intro x hx
    exact sub_eq_zero.mpr (angularField_cross_partials x hx)

open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model

lemma angular_coordinate_C1 (i : Fin 2) : CrOn 1 puncturedPlane (fun x => angularField x i) := by
  apply (crOn_iff_contDiffOn 1 _ _ puncturedPlane_open).mpr
  exact (contDiff_piLp_apply 2 : ContDiff ℝ 1 (fun v : E 2 => v i)).comp_contDiffOn
    ((crOn_iff_contDiffOn 1 _ _ puncturedPlane_open).mp angularField_C1)

theorem green_zero : green_zeroType := by
  intro a b ha hab
  have hfield := field_neighborhood ha hab
  obtain ⟨hb, o, bO, ho, hOb, _, _, hc, _, _⟩ := Green.green (annulus_regular ha hab)
    puncturedPlane (fun x => angularField x 0) (fun x => angularField x 1)
    hfield.1 hfield.2.1 (angular_coordinate_C1 0) (angular_coordinate_C1 1)
  have hz : (fun x : annulus a b => circulationDensity
      (fun y => angularField y 0) (fun y => angularField y 1) x) = fun _ => 0 := by
    funext x
    exact hfield.2.2.2 x (hfield.2.1 (subset_closure x.property))
  have hi : regionIntegral (fun x : annulus a b => circulationDensity
      (fun y => angularField y 0) (fun y => angularField y 1) x) = 0 := by
    rw [hz]
    unfold regionIntegral
    have he : (zeroExtension (fun _ : annulus a b => (0 : ℝ))) = fun _ => 0 := by
      funext x
      simp [zeroExtension]
    rw [he]
    exact (D04.Darboux.constant_integrals _ 0).1.trans (zero_mul _)
  exact ⟨o, bO, ho, hOb, hi, hi ▸ hc⟩

theorem disk_excluded : disk_excludedType := by
  intro c r hzero hsub
  exact hsub (subset_closure hzero) rfl

theorem induced_tangent : induced_tangentType := by
  intro a b _ _ hD hb o ho bO hOb x e he
  have ht := Green.boundary_tangent_normal hD hb o ho bO hOb x e he
  ext i
  fin_cases i
  · exact ht.1
  · exact ht.2.1

theorem boundary_trace : boundary_traceType := by
  intro a b ha hab
  rw [(radius_path_geometry (ha.trans hab) 1 (by norm_num)).1,
    (radius_path_geometry ha (-1) (by norm_num)).1, annulus_frontier ha hab]
  constructor
  · ext x
    exact or_comm
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact (ne_of_lt hab) (hy.symm.trans hx)

theorem green_boundary_sum : green_boundary_sumType := by
  intro a b ha hab outer inner
  obtain ⟨ho, hi, hoval, hival, hsum⟩ := boundary_periods ha hab outer inner
  obtain ⟨o, bO, hO, hbO, hbulk, hboundary⟩ := green_zero ha hab
  exact ⟨ho, hi, o, bO, hO, hbO, hoval, hival, hbulk.trans hsum.symm, hsum.symm ▸ hboundary⟩

end D04.Annulus
