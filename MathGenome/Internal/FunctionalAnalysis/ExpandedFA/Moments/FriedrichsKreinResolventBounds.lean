import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.FriedrichsKreinResolventBounds
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Moments.KreinNonnegativeExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.FriedrichsExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.LaxMilgramSolvability
import Mathlib.Tactic.FunProp

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProductSpace ComplexConjugate Topology
open UniformSpace Filter
universe u v
namespace ExpandedFA.Moments.FriedrichsKreinResolventBounds
open ExpandedFA.Unbounded ExpandedFA.Unbounded.FriedrichsExtension
open ExpandedFA.Unbounded.ClosedNonnegativeForms
open ExpandedFA.Moments.KreinNonnegativeExtension
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem re_mul_real (a : ℝ) (z : ℂ) : ((a : ℂ) * z).re = a * z.re := by simp
private theorem re_inner_self (x : H) : (inner ℂ x x).re = ‖x‖ ^ 2 :=
  (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
private theorem re_inner_swap (x y : H) : (inner ℂ x y).re = (inner ℂ y x).re :=
  inner_re_symm (𝕜 := ℂ) x y

/-- The a-shifted form is represented in the original form Hilbert space. -/
def formShift (q : NonnegativeForm ℂ H) [CompleteSpace q.EnergySpace] (a : ℝ) :
    q.EnergySpace →L[ℂ] q.EnergySpace :=
  ContinuousLinearMap.id ℂ _ + ((a - 1 : ℝ) : ℂ) • (q.inclusion.adjoint ∘L q.inclusion)

@[simp] theorem formShift_inner (q : NonnegativeForm ℂ H)
    [CompleteSpace q.EnergySpace] (a : ℝ) (x y : q.EnergySpace) :
    inner ℂ x (formShift q a y) =
      q.form (q.toDomain x) (q.toDomain y) + (a : ℂ) *
        inner ℂ (q.toDomain x : H) (q.toDomain y : H) := by
  simp only [formShift, _root_.add_apply, ContinuousLinearMap.id_apply,
    smul_apply, ContinuousLinearMap.comp_apply, inner_add_right,
    inner_smul_right, q.inclusion.adjoint_inner_right]
  rw [q.energy_inner]
  change _ + _ * inner ℂ (q.toDomain x : H) (q.toDomain y : H) = _
  push_cast
  ring

theorem formShift_coercive (q : NonnegativeForm ℂ H)
    [CompleteSpace q.EnergySpace] (a : ℝ) (x : q.EnergySpace) :
    min 1 a * ‖x‖ ^ 2 ≤ (inner ℂ x (formShift q a x)).re := by
  rw [formShift_inner, Complex.add_re, re_mul_real, re_inner_self]
  have hn : 0 ≤ (q.form (q.toDomain x) (q.toDomain x)).re := q.nonneg (q.toDomain x)
  have h1 := min_le_left (1 : ℝ) a
  have h2 := min_le_right (1 : ℝ) a
  have he : ‖x‖ ^ 2 = (q.form (q.toDomain x) (q.toDomain x)).re + ‖(q.toDomain x : H)‖ ^ 2 := q.energy_norm x
  rw [he]
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) hn,
    mul_nonneg (sub_nonneg.mpr h2) (sq_nonneg ‖(q.toDomain x : H)‖)]

theorem form_solution (q : NonnegativeForm ℂ H) (hc : q.IsClosed)
    (a : ℝ) (ha : 0 < a) (f : H) :
    ∃ x : q.domain, ∀ y : q.domain,
      q.form y x + (a : ℂ) * inner ℂ (y : H) (x : H) = inner ℂ (y : H) f := by
  let : CompleteSpace q.EnergySpace := hc
  obtain ⟨x, hx⟩ := (ExpandedFA.Hilbert.LaxMilgramSolvability.operator_bijective
    (formShift q a) (lt_min zero_lt_one ha) (formShift_coercive q a)).2 (q.inclusion.adjoint f)
  refine ⟨q.toDomain x, fun y => ?_⟩
  exact (formShift_inner q a (show q.EnergySpace from y) x).symm.trans
    ((congrArg (inner ℂ (show q.EnergySpace from y)) hx).trans
      (q.inclusion.adjoint_inner_right _ f))

/-- Coercivity in the ambient norm, without dividing by a possibly zero vector. -/
theorem shift_lower (A : Operator ℂ H H)
    (hn : ∀ x : A.domain, 0 ≤ (inner ℂ (x : H) (A x)).re)
    (a : ℝ) (x : A.domain) :
    a * ‖(x : H)‖ ≤ ‖A x + (a : ℂ) • (x : H)‖ := by
  have he : a * ‖(x : H)‖ ^ 2 ≤
      (inner ℂ (x : H) (A x + (a : ℂ) • (x : H))).re := by
    rw [inner_add_right, inner_smul_right, Complex.add_re, re_mul_real,
      re_inner_self]
    linarith [hn x]
  have hb := he.trans (re_inner_le_norm (𝕜 := ℂ) (x : H) (A x + (a : ℂ) • (x : H)))
  by_cases hx : ‖(x : H)‖ = 0
  · simp [hx]
  · have hp : 0 < ‖(x : H)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    nlinarith

theorem positive_resolvent_of_surjective (A : Operator ℂ H H)
    (hs : A.IsFormalAdjoint A)
    (hn : ∀ x : A.domain, 0 ≤ (inner ℂ (x : H) (A x)).re)
    (a : ℝ) (ha : 0 < a)
    (hr : ∀ f : H, ∃ x : A.domain, A x + (a : ℂ) • (x : H) = f) :
    Nonempty (PositiveResolvent A a) := by
  let L : A.domain →ₗ[ℂ] H := A.toFun + (a : ℂ) • A.domain.subtype
  have hb : ∀ x : A.domain, a * ‖(x : H)‖ ≤ ‖L x‖ := shift_lower A hn a
  have hi : Function.Injective L := by
    intro x y hxy
    have hh := hb (x - y)
    rw [map_sub, hxy, sub_self, norm_zero] at hh
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have : ‖((x - y : A.domain) : H)‖ = 0 := by
      nlinarith [norm_nonneg (((x - y : A.domain) : H))]
    exact this
  let e := LinearEquiv.ofBijective L ⟨hi, hr⟩
  let M : H →ₗ[ℂ] H := A.domain.subtype.comp e.symm.toLinearMap
  have hm : ∀ f, ‖M f‖ ≤ a⁻¹ * ‖f‖ := by
    intro f
    have hh := hb (e.symm f)
    have he : L (e.symm f) = f := e.apply_symm_apply f
    rw [he] at hh
    change ‖(e.symm f : H)‖ ≤ _
    calc
      _ ≤ ‖f‖ / a := (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hh)
      _ = _ := by rw [div_eq_mul_inv, mul_comm]
  let B := M.mkContinuous a⁻¹ hm
  have hd : ∀ f, B f ∈ A.domain := fun f => (e.symm f).property
  have he : ∀ f, A ⟨B f, hd f⟩ + (a : ℂ) • B f = f := fun f => e.apply_symm_apply f
  refine ⟨{ inverse := B
            mem_domain := hd
            right_inverse := he
            left_inverse := ?_
            selfAdjoint := ?_
            nonnegative := ?_ }⟩
  · intro x
    exact congrArg (fun y : A.domain => (y : H)) (e.symm_apply_apply x)
  · intro f g
    let x : A.domain := ⟨B f, hd f⟩
    let y : A.domain := ⟨B g, hd g⟩
    have hh := hs x y
    have hf := he f
    have hg := he g
    calc
      inner ℂ (B f) g = inner ℂ (x : H) (A y + (a : ℂ) • (y : H)) := by rw [hg]
      _ = inner ℂ (A x + (a : ℂ) • (x : H)) (y : H) := by
        rw [inner_add_right, inner_add_left, inner_smul_right, inner_smul_left,
          Complex.conj_ofReal, hh]
      _ = inner ℂ f (B g) := by rw [hf]
  · intro f
    have hh := hn ⟨B f, hd f⟩
    rw [← (congrArg (fun v => inner ℂ v (B f)) (he f)), inner_add_left, inner_smul_left, Complex.conj_ofReal,
      Complex.add_re, re_mul_real, re_inner_self,
      re_inner_swap]
    nlinarith [sq_nonneg ‖B f‖]

theorem form_resolvent (q : NonnegativeForm ℂ H) (hc : q.IsClosed)
    (a : ℝ) (ha : 0 < a) : Nonempty (PositiveResolvent q.associatedOperator a) := by
  apply positive_resolvent_of_surjective q.associatedOperator q.associated_formalAdjoint
    q.associated_nonnegative a ha
  intro f
  obtain ⟨u, hu⟩ := form_solution q hc a ha f
  have hg : ((u : H), f - (a : ℂ) • (u : H)) ∈ q.associatedOperator.graph := by
    apply (q.associated _ _).mpr
    refine ⟨u.property, fun v => ?_⟩
    rw [inner_sub_right, inner_smul_right]
    exact eq_sub_iff_add_eq.mpr (hu v)
  obtain ⟨x, hx, hAx⟩ := q.associatedOperator.mem_graph_iff.mp hg
  refine ⟨x, ?_⟩
  rw [hAx, hx, sub_add_cancel]

/-- The associated Friedrichs operator extends the original nonnegative operator. -/
theorem friedrichs_le (S : Operator ℂ H H) (h : SemiboundedSymmetric S 0)
    (F : FormClosure (operatorForm S 0 h)) : S ≤ F.closedForm.associatedOperator := by
  apply LinearPMap.le_of_le_graph
  intro p hp
  obtain ⟨x, hx, hSx⟩ := S.mem_graph_iff.mp hp
  have hh := F.core_graph S 0 h x
  have he : realShift S (-0) x = S x := by simp
  rw [he] at hh
  simpa only [hx, hSx] using hh

/-- A self-adjoint operator has no proper symmetric operator extension. -/
theorem maximal_selfAdjoint (T A : Operator ℂ H H)
    (hd : Dense (T.domain : Set H)) (ht : T = HilbertAdjointSpec.adjointValue T)
    (hs : A.IsFormalAdjoint A) (hle : T ≤ A) : A = T := by
  apply le_antisymm _ hle
  rw [ht]
  apply LinearPMap.IsFormalAdjoint.le_adjoint hd
  intro x y
  let z : A.domain := ⟨x, hle.1 x.property⟩
  have hz : T x = A z := hle.2 rfl
  rw [hz]
  exact hs z y

/-- Positive resolvents of arbitrary nonnegative self-adjoint operators. -/
theorem selfAdjoint_resolvent (T : Operator ℂ H H) (h : SemiboundedSymmetric T 0)
    (ht : T = HilbertAdjointSpec.adjointValue T) (a : ℝ) (ha : 0 < a) :
    Nonempty (PositiveResolvent T a) := by
  let F := formClosure T 0 h
  have he : F.closedForm.associatedOperator = T :=
    maximal_selfAdjoint T _ h.dense ht F.closedForm.associated_formalAdjoint (friedrichs_le T h F)
  rw [← he]
  exact form_resolvent F.closedForm F.closed a ha

/-- The shifted variational equation on the full form domain. -/
theorem resolvent_form_equation (q : NonnegativeForm ℂ H) (A : Operator ℂ H H)
    (hq : q.Associated A) (a : ℝ) (R : PositiveResolvent A a) (f : H) :
    ∃ u : q.domain, (u : H) = R.inverse f ∧ ∀ v : q.domain,
      q.form v u + (a : ℂ) * inner ℂ (v : H) (u : H) = inner ℂ (v : H) f := by
  obtain ⟨hu, hf⟩ := (hq _ _).mp (A.mem_graph ⟨R.inverse f, R.mem_domain f⟩)
  refine ⟨⟨R.inverse f, hu⟩, rfl, fun v => ?_⟩
  rw [hf, ← inner_smul_right, ← inner_add_right, R.right_inverse]

/-- Completion of the square: every form-domain test is below the resolvent value. -/
theorem form_variational_bound (q : NonnegativeForm ℂ H) (A : Operator ℂ H H)
    (hq : q.Associated A) (a : ℝ) (ha : 0 < a) (R : PositiveResolvent A a)
    (f : H) (x : q.domain) :
    2 * (inner ℂ f (x : H)).re - (q.form x x).re - a * ‖(x : H)‖ ^ 2 ≤
      (inner ℂ f (R.inverse f)).re := by
  obtain ⟨u, hu, hsolve⟩ := resolvent_form_equation q A hq a R f
  have hxu := congrArg Complex.re (hsolve x)
  have huu := congrArg Complex.re (hsolve u)
  simp only [Complex.add_re, re_mul_real, re_inner_self] at hxu huu
  have hherm : (q.form u x).re = (q.form x u).re := by
    have hh := congrArg Complex.re (q.hermitian x u)
    simpa using hh
  have hp := q.nonneg (x - u)
  change 0 ≤ (q.form (x - u) (x - u)).re at hp
  simp only [map_sub, LinearMap.sub_apply, Complex.sub_re, hherm] at hp
  have hn := mul_nonneg (le_of_lt ha) (sq_nonneg ‖(x : H) - (u : H)‖)
  rw [norm_sub_sq (𝕜 := ℂ)] at hn
  simp only [RCLike.re_to_complex] at hn
  rw [← hu]
  rw [re_inner_swap f (x : H)]
  rw [re_inner_swap f (u : H)]
  nlinarith

/-- Diagonal value at the solution, used to identify the attained maximum. -/
theorem form_variational_value (q : NonnegativeForm ℂ H) (A : Operator ℂ H H)
    (hq : q.Associated A) (a : ℝ) (R : PositiveResolvent A a) (f : H)
    (u : q.domain) (hu : (u : H) = R.inverse f) :
    2 * (inner ℂ f (u : H)).re - (q.form u u).re - a * ‖(u : H)‖ ^ 2 =
      (inner ℂ f (R.inverse f)).re := by
  obtain ⟨v, hv, hsolve⟩ := resolvent_form_equation q A hq a R f
  have he : v = u := Subtype.ext (hv.trans hu.symm)
  subst v
  have hh := congrArg Complex.re (hsolve u)
  simp only [Complex.add_re, re_mul_real, re_inner_self] at hh
  rw [re_inner_swap (u : H) f, hu] at hh
  rw [hu]
  linarith

/-- Restricting the testing vectors to D(T) still specifies T itself, since
its output is determined by the density of that domain. -/
theorem operatorForm_associated (T : Operator ℂ H H) (h : SemiboundedSymmetric T 0) :
    (operatorForm T 0 h).Associated T := by
  intro u f
  constructor
  · intro hg
    obtain ⟨x, hx, hTx⟩ := T.mem_graph_iff.mp hg
    have hx' : (x : H) = u := hx
    have hu : u ∈ T.domain := hx' ▸ x.property
    refine ⟨hu, fun v => ?_⟩
    have he : (⟨u, hu⟩ : T.domain) = x := Subtype.ext hx'.symm
    simp only [operatorForm_apply, zero_mul, sub_zero, RCLike.ofReal_zero, he, hTx]
  · rintro ⟨hu, hf⟩
    have he : T ⟨u, hu⟩ = f := by
      apply h.dense.eq_of_inner_right (𝕜 := ℂ)
      intro v hv
      simpa only [operatorForm_apply, RCLike.ofReal_zero, zero_mul, sub_zero] using hf ⟨v, hv⟩
    exact T.mem_graph_iff.mpr ⟨⟨u, hu⟩, rfl, he⟩

section Enlargement
variable {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable (i : H →ₗᵢ[ℂ] G)

/-- The adjoint of an isometric inclusion is contractive. -/
theorem projection_norm (x : G) : ‖i.toContinuousLinearMap.adjoint x‖ ≤ ‖x‖ := by
  let p := i.toContinuousLinearMap.adjoint x
  have he : inner ℂ (i p) x = inner ℂ p p :=
    (i.toContinuousLinearMap.adjoint_inner_right p x).symm
  have hb := re_inner_le_norm (𝕜 := ℂ) (i p) x
  rw [he, ← norm_sq_eq_re_inner (𝕜 := ℂ), i.norm_map] at hb
  by_cases hz : ‖p‖ = 0
  · change ‖p‖ ≤ _
    rw [hz]
    exact norm_nonneg _
  · change ‖p‖ ≤ _
    have hp : 0 < ‖p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

@[simp] theorem compression_inner (B : G →L[ℂ] G) (f g : H) :
    inner ℂ f (compression i B g) = inner ℂ (i f) (B (i g)) := by
  exact i.toContinuousLinearMap.adjoint_inner_right f (B (i g))

theorem compression_symmetric (T : Operator ℂ G G) (a : ℝ) (R : PositiveResolvent T a)
    (f g : H) : inner ℂ (compression i R.inverse f) g =
      inner ℂ f (compression i R.inverse g) := by
  rw [← inner_conj_symm, compression_inner, inner_conj_symm, compression_inner]
  exact R.selfAdjoint (i f) (i g)

/-- The embedded core is a legitimate test in the enlarged operator domain. -/
theorem core_variational_bound (S : Operator ℂ H H) (T : Operator ℂ G G)
    (hT : SemiboundedSymmetric T 0) (he : ExtendsAlong i S T)
    (a : ℝ) (ha : 0 < a) (RT : PositiveResolvent T a) (f : H) (y : S.domain) :
    2 * (inner ℂ f (y : H)).re - (inner ℂ (y : H) (S y)).re - a * ‖(y : H)‖ ^ 2 ≤
      (inner ℂ f (compression i RT.inverse f)).re := by
  obtain ⟨hy, hTy⟩ := he y
  have hb := form_variational_bound (operatorForm T 0 hT) T (operatorForm_associated T hT)
    a ha RT (i f) ⟨i (y : H), hy⟩
  simpa only [operatorForm_apply, RCLike.ofReal_zero, zero_mul, sub_zero, hTy,
    i.inner_map_map, i.norm_map, compression_inner] using hb

/-- Density of the original form core upgrades its tests to the Friedrichs value. -/
theorem friedrichs_bound (S : Operator ℂ H H) (h : SemiboundedSymmetric S 0)
    (F : FormClosure (operatorForm S 0 h))
    (a : ℝ) (ha : 0 < a) (RF : PositiveResolvent F.closedForm.associatedOperator a)
    (T : Operator ℂ G G) (hT : SemiboundedSymmetric T 0) (he : ExtendsAlong i S T)
    (RT : PositiveResolvent T a) : FormLE RF.inverse (compression i RT.inverse) := by
  intro f
  let q := operatorForm S 0 h
  let J : Completion q.EnergySpace → ℝ := fun x =>
    2 * (inner ℂ f (F.embedding x)).re - ‖x‖ ^ 2 + (1 - a) * ‖F.embedding x‖ ^ 2
  have hc : ∀ x : Completion q.EnergySpace,
      J x ≤ (inner ℂ f (compression i RT.inverse f)).re := by
    intro x
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) continuous_const
    | ih y =>
      have hb := core_variational_bound i S T hT he a ha RT f (q.toDomain y)
      change 2 * (inner ℂ f (F.embedding (y : Completion q.EnergySpace))).re -
        ‖(y : Completion q.EnergySpace)‖ ^ 2 +
        (1 - a) * ‖F.embedding (y : Completion q.EnergySpace)‖ ^ 2 ≤ _
      have hn : ‖y‖ ^ 2 = (inner ℂ (q.toDomain y : H) (S (q.toDomain y))).re +
          ‖(q.toDomain y : H)‖ ^ 2 := by
        simpa only [q, operatorForm_apply, RCLike.ofReal_zero, zero_mul, sub_zero,
          RCLike.re_to_complex] using q.energy_norm y
      rw [F.on_core, Completion.norm_coe, hn]
      change 2 * (inner ℂ f (q.toDomain y : H)).re -
        ((inner ℂ (q.toDomain y : H) (S (q.toDomain y))).re + ‖(q.toDomain y : H)‖ ^ 2) +
        (1 - a) * ‖(q.toDomain y : H)‖ ^ 2 ≤ _
      nlinarith
  obtain ⟨u, hu, _⟩ := resolvent_form_equation F.closedForm _ F.closedForm.associated a RF f
  let x := F.equivalence.symm u
  have hx : F.embedding x = (u : H) := by rw [← F.inclusion, LinearEquiv.apply_symm_apply]
  have heq := F.energy_identity x x
  rw [LinearEquiv.apply_symm_apply, hx] at heq
  have hn := congrArg Complex.re heq
  simp only [Complex.add_re, re_inner_self] at hn
  have hb := hc x
  change 2 * (inner ℂ f (F.embedding x)).re - ‖x‖ ^ 2 + (1 - a) * ‖F.embedding x‖ ^ 2 ≤ _ at hb
  rw [hx] at hb
  have hv := form_variational_value F.closedForm _ F.closedForm.associated a RF f u hu
  nlinarith

/-- Cauchy--Schwarz on the unshifted energy completions shows that projection
lands in the exact Krein form domain, with no loss of energy. -/
theorem projection_energy_bound (S : Operator ℂ H H) (h : SemiboundedSymmetric S 0)
    (K : Construction S h) (T : Operator ℂ G G) (hT : SemiboundedSymmetric T 0)
    (he : ExtendsAlong i S T) (z : T.domain) :
    ∃ hp : i.toContinuousLinearMap.adjoint (z : G) ∈ K.R.domain,
      ‖K.R ⟨i.toContinuousLinearMap.adjoint (z : G), hp⟩‖ ^ 2 ≤
        (inner ℂ (z : G) (T z)).re := by
  let p := i.toContinuousLinearMap.adjoint (z : G)
  let C := ‖classMap T hT z‖
  have hb : ∀ y : S.domain, ‖inner ℂ p (S y)‖ ≤ C * ‖classMap S h y‖ := by
    intro y
    obtain ⟨hy, hTy⟩ := he y
    let v : T.domain := ⟨i (y : H), hy⟩
    have hn : ‖classMap T hT v‖ = ‖classMap S h y‖ := by
      have hh : ‖classMap T hT v‖ ^ 2 = ‖classMap S h y‖ ^ 2 := by
        rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
          classMap_inner, classMap_inner]
        change RCLike.re (inner ℂ (i (y : H)) (T ⟨i (y : H), hy⟩)) = _
        rw [hTy, i.inner_map_map]
      nlinarith [norm_nonneg (classMap T hT v), norm_nonneg (classMap S h y)]
    have ht : inner ℂ p (S y) = inner ℂ (classMap T hT z) (classMap T hT v) := by
      rw [classMap_inner]
      change inner ℂ (i.toContinuousLinearMap.adjoint (z : G)) (S y) =
        inner ℂ (z : G) (T ⟨i (y : H), hy⟩)
      rw [hTy]
      exact i.toContinuousLinearMap.adjoint_inner_left (S y) (z : G)
    rw [ht]
    exact (norm_inner_le_norm _ _).trans_eq (by rw [hn])
  have hp : p ∈ K.R.domain := (K.bounded_domain p).mpr ⟨C, norm_nonneg _, hb⟩
  let w := K.R ⟨p, hp⟩
  have hw : ∀ y : S.domain, inner ℂ w (classMap S h y) = inner ℂ p (S y) :=
    (K.graph_iff p w).mp (K.R.mem_graph ⟨p, hp⟩)
  have hwb : ∀ v : W S h, ‖inner ℂ w v‖ ≤ C * ‖v‖ := by
    intro v
    induction v using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih y =>
      change ‖inner ℂ w (classMap S h (show S.domain from y))‖ ≤
        C * ‖classMap S h (show S.domain from y)‖
      rw [hw]
      exact hb _
  have hnorm : ‖w‖ ≤ C := by
    have ht := hwb w
    rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_coe_norm] at ht
    by_cases hz : ‖w‖ = 0
    · rw [hz]; exact norm_nonneg _
    · have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  refine ⟨hp, ?_⟩
  have hC : C ^ 2 = (inner ℂ (z : G) (T z)).re := by
    dsimp only [C]
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), classMap_inner]
    rfl
  change ‖w‖ ^ 2 ≤ _
  rw [← hC]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- Projection decreases both the unshifted energy and the ambient norm. -/
theorem krein_bound (S : Operator ℂ H H) (h : SemiboundedSymmetric S 0)
    (K : Construction S h) (a : ℝ) (ha : 0 < a) (RK : PositiveResolvent K.extension a)
    (T : Operator ℂ G G) (hT : SemiboundedSymmetric T 0) (he : ExtendsAlong i S T)
    (RT : PositiveResolvent T a) : FormLE (compression i RT.inverse) RK.inverse := by
  intro f
  let z : T.domain := ⟨RT.inverse (i f), RT.mem_domain (i f)⟩
  obtain ⟨hp, hb⟩ := projection_energy_bound i S h K T hT he z
  let p : K.R.domain := ⟨i.toContinuousLinearMap.adjoint (z : G), hp⟩
  have hv := form_variational_bound (pullbackForm K.R K.dense) K.extension K.associated
    a ha RK f p
  change 2 * (inner ℂ f (p : H)).re - (inner ℂ (K.R p) (K.R p)).re - a * ‖(p : H)‖ ^ 2 ≤ _ at hv
  rw [re_inner_self] at hv
  have hn := projection_norm i (z : G)
  have heq := RT.right_inverse (i f)
  have heval : (inner ℂ (i f) (z : G)).re =
      (inner ℂ (z : G) (T z)).re + a * ‖(z : G)‖ ^ 2 := by
    have hh := congrArg (fun y : G => (inner ℂ y (z : G)).re) heq
    change (inner ℂ (T z + (a : ℂ) • (z : G)) (z : G)).re = (inner ℂ (i f) (z : G)).re at hh
    simp only [inner_add_left, inner_smul_left, Complex.conj_ofReal,
      Complex.add_re, re_mul_real, re_inner_self] at hh
    rw [re_inner_swap (T z) (z : G)] at hh
    exact hh.symm
  have hinner : inner ℂ f (p : H) = inner ℂ (i f) (z : G) :=
    i.toContinuousLinearMap.adjoint_inner_right f (z : G)
  rw [hinner] at hv
  rw [compression_inner]
  change (inner ℂ (i f) (z : G)).re ≤ _
  have hn2 : a * ‖(p : H)‖ ^ 2 ≤ a * ‖(z : G)‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) ha.le
  change ‖K.R p‖ ^ 2 ≤ _ at hb
  nlinarith

end Enlargement
/-- Friedrichs--Krein resolvent bounds, including every isometrically closed
Hilbert enlargement and the non-strict lower bound S≥0. -/
theorem resolvent_bounds : Spec.ResolventBounds.{u, v} := by
  intro H _ _ _ S h _hclosed
  let F := formClosure S 0 h
  let K := construction S h
  let SF := F.closedForm.associatedOperator
  refine ⟨F, K, SF, F.closedForm.associated, friedrichs_le S h F,
    F.closedForm.associated_dense F.closed, F.closedForm.associated_selfAdjoint F.closed,
    F.closedForm.associated_nonnegative, ?_⟩
  intro a ha
  obtain ⟨RF⟩ := form_resolvent F.closedForm F.closed a ha
  have hk : (pullbackForm K.R K.dense).associatedOperator = K.extension :=
    (pullbackForm K.R K.dense).associated_unique
      (pullbackForm K.R K.dense).associated K.associated
  have hkr : Nonempty (PositiveResolvent K.extension a) := by
    rw [← hk]
    exact form_resolvent _ K.closed_form a ha
  obtain ⟨RK⟩ := hkr
  refine ⟨RF, RK, ?_⟩
  intro G _ _ _ i T hT ht he
  obtain ⟨RT⟩ := selfAdjoint_resolvent T hT ht a ha
  exact ⟨RT, compression_symmetric i T a RT,
    friedrichs_bound i S h F a ha RF T hT he RT,
    krein_bound i S h K a ha RK T hT he RT⟩

end ExpandedFA.Moments.FriedrichsKreinResolventBounds
