import Specs.LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy
import LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting
import LinearAlgebraicGroups.Composition.QuaternionNorm
import Batteries.Tactic.OpenPrivate
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
import Mathlib.Tactic.LinearCombination

namespace LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy

open LinearAlgebraicGroups.Specs.Arithmetic.LocalQuadraticIsotropy
open LinearAlgebraicGroups.Specs.Arithmetic.IsotropicSpinGeneration (reflection)
open CliffordAlgebra
open scoped TensorProduct
open _root_.Specs.RM03.CSA (degree isCentralDivision)
open LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting

universe u v

noncomputable section

open QuaternionAlgebra in
private theorem quaternion_norm_formula {F : Type u} [Field F] {a b : F}
    (x : QuaternionAlgebra F a 0 b) :
    (x * star x).re = x.re ^ 2 + pureNorm a b x.imI x.imJ x.imK := by
  simp [pureNorm]
  ring

private theorem quaternion_norm_mul {F : Type u} [Field F] {a b : F}
    (x y : QuaternionAlgebra F a 0 b) :
    ((x * y) * star (x * y)).re = (x * star x).re * (y * star y).re := by
  let A := QuaternionAlgebra F a 0 b
  let f := algebraMap F A
  have h (z : A) : f (z * star z).re = z * star z := z.mul_star_eq_coe.symm
  apply f.injective
  rw [map_mul, h, h, h, star_mul]
  calc
    x * y * (star y * star x) = x * (y * star y) * star x := by
      simp only [mul_assoc]
    _ = (y * star y) * x * star x := by
      rw [← h y, Algebra.commutes]
    _ = (x * star x) * (y * star y) := by
      rw [mul_assoc, ← h y, Algebra.commutes]

open private quaternion_isUnit_of_norm_ne_zero from
  LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting

private theorem quaternion_isUnit_or_zero {F : Type u} [Field F] {a b : F}
    (h : ∀ x y z, pureNorm a b x y z = 0 → x = 0 ∧ y = 0 ∧ z = 0)
    (x : QuaternionAlgebra F a 0 b) : IsUnit x ∨ x = 0 := by
  let A := QuaternionAlgebra F a 0 b
  have ha : a ≠ 0 := by
    intro ha
    exact one_ne_zero (h 1 0 0 (by simp [pureNorm, ha])).1
  have hb : b ≠ 0 := by
    intro hb
    exact one_ne_zero (h 0 1 0 (by simp [pureNorm, hb])).2.1
  have hpure {y : A} (hre : y.re = 0) (hn : (y * star y).re = 0) : y = 0 := by
    rw [quaternion_norm_formula, hre, zero_pow (by decide : 2 ≠ 0), zero_add] at hn
    obtain ⟨hi, hj, hk⟩ := h _ _ _ hn
    exact QuaternionAlgebra.ext hre hi hj hk
  by_cases hn : (x * star x).re = 0
  · right
    have hex : ∃ y : A, y.re = 0 ∧ y ≠ 0 ∧ (x * y).re = 0 := by
      by_cases hi : x.imI = 0
      · refine ⟨⟨0, 1, 0, 0⟩, rfl, ?_, ?_⟩
        · intro he
          exact one_ne_zero (congrArg QuaternionAlgebra.imI he)
        · change x.re * 0 + a * x.imI * 1 + b * x.imJ * 0 + 0 * b * x.imJ * 0 - a * b * x.imK * 0 = 0
          simp [hi]
      · refine ⟨⟨0, b * x.imJ, -(a * x.imI), 0⟩, rfl, ?_, ?_⟩
        · intro he
          exact neg_ne_zero.mpr (mul_ne_zero ha hi) (congrArg QuaternionAlgebra.imJ he)
        · change x.re * 0 + a * x.imI * (b * x.imJ) + b * x.imJ * (-(a * x.imI)) + 0 * b * x.imJ * 0 - a * b * x.imK * 0 = 0
          ring
    obtain ⟨y, hyr, hy, hxyr⟩ := hex
    have hyu : IsUnit y := quaternion_isUnit_of_norm_ne_zero (fun hz => hy (hpure hyr hz))
    have hz : x * y = 0 := hpure hxyr (by rw [quaternion_norm_mul, hn, zero_mul])
    exact hyu.mul_right_cancel (hz.trans (zero_mul y).symm)
  · exact Or.inl (quaternion_isUnit_of_norm_ne_zero hn)

private theorem quaternion_central {F : Type u} [Field F] {a b : F}
    (h₂ : (2 : F) ≠ 0) (ha : a ≠ 0) :
    Algebra.IsCentral F (QuaternionAlgebra F a 0 b) := by
  let A := QuaternionAlgebra F a 0 b
  constructor
  intro q hq
  rw [Algebra.mem_bot]
  let i : A := ⟨0, 1, 0, 0⟩
  let j : A := ⟨0, 0, 1, 0⟩
  have hq' := (Subalgebra.mem_center_iff (R := F)).mp hq
  have hI : 2 * q.imI = 0 := by
    have he := congrArg QuaternionAlgebra.imK (hq' j)
    simp [j] at he
    linear_combination -he
  have hJ : 2 * q.imJ = 0 := by
    have he := congrArg QuaternionAlgebra.imK (hq' i)
    simp [i] at he
    linear_combination he
  have hK : 2 * a * q.imK = 0 := by
    have he := congrArg QuaternionAlgebra.imJ (hq' i)
    simp [i] at he
    linear_combination he
  refine ⟨q.re, ?_⟩
  ext <;> simp [QuaternionAlgebra.algebraMap_eq, (mul_eq_zero.mp hI).resolve_left h₂,
    (mul_eq_zero.mp hJ).resolve_left h₂, (mul_eq_zero.mp hK).resolve_left (mul_ne_zero h₂ ha)]

open LinearAlgebraicGroups.Composition QuaternionSpecification in
open private quaternion_model_coordinates reduced_norm_transport scalar_double_involution_conjugate
  from LinearAlgebraicGroups.Composition.QuaternionNorm in
private theorem quaternion_reduced_norm {F : Type u} [Field F] {a b : F}
    (h₂ : (2 : F) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hD : RM03.CSA.IsCentralSimple F (QuaternionAlgebra F a 0 b))
    (p : QuaternionAlgebra F a 0 b) :
    RM03.CSA.reducedNorm hD p = (p * star p).re := by
  obtain ⟨hét, hd, hn, _, hcoords, _⟩ := scalar_double_model a h₂ ha
  let := hét
  obtain ⟨hQ, _, _, _, hnorm, _⟩ := quaternion_norm_and_splitting hn hd
    (scalarDoubleInvolution a) (scalarDoubleInvolution_involutive a)
    scalar_double_involution_conjugate b hb
  obtain ⟨e, he⟩ := quaternion_model_coordinates a b
  let x : scalarDouble a := ⟨p.re, p.imI⟩
  let y : scalarDouble a := ⟨p.imJ, p.imK⟩
  have hp : e (quaternionModelPair a b x y) = p := he x y
  rw [← hp, reduced_norm_transport hQ hD, hnorm, cyclic_norm_pair, he,
    quaternion_norm_formula, hcoords, hcoords]
  simp only [pureNorm]
  ring

private theorem separable_quadratic {F : Type u} [Field F] {d : F} [Fact (¬ IsSquare d)]
    (h₂ : (2 : F) ≠ 0) : Algebra.IsSeparable F (QuadraticAlgebra F d 0) := by
  classical
  let E := QuadraticAlgebra F d 0
  let w : E := ⟨0, 1⟩
  have hd : d ≠ 0 := fun he => Fact.out (p := ¬ IsSquare d) ⟨0, by simp [he]⟩
  have hw : w ^ 2 = algebraMap F E d := by ext <;> simp [E, w, pow_two]
  have hp : (Polynomial.X ^ 2 - Polynomial.C d : Polynomial F).Separable :=
    Polynomial.separable_X_pow_sub_C (n := 2) d (by simpa using h₂) hd
  have hwsep : IsSeparable F w := hp.of_dvd (minpoly.dvd F w (by simp [hw]))
  have hwmem : w ∈ separableClosure F E := hwsep
  constructor
  intro x
  change x ∈ separableClosure F E
  have he : x = algebraMap F E x.re + x.im • w := by
    ext <;> simp [E, w]
  rw [he]
  exact (separableClosure F E).add_mem (IntermediateField.algebraMap_mem _ _)
    ((separableClosure F E).toSubalgebra.smul_mem hwmem _)

/-- In the anisotropic case every nonsquare `-t` supplies the quadratic
field whose generator is a pure quaternion of norm `t`. -/
theorem pure_norm_values : PureNormValues.{u} := by
  intro F _ _ _ _ h₂ a b h t ht
  let A := QuaternionAlgebra F a 0 b
  let : DivisionRing A := DivisionRing.ofIsUnitOrEqZero (quaternion_isUnit_or_zero h)
  have ha : a ≠ 0 :=
    fun ha => one_ne_zero (h 1 0 0 (by simp [pureNorm, ha])).1
  have hA : isCentralDivision F A := ⟨quaternion_central h₂ ha, inferInstance⟩
  have hdeg : degree F A = 2 := by
    change Nat.sqrt (Module.finrank F (QuaternionAlgebra F a 0 b)) = 2
    rw [QuaternionAlgebra.finrank_eq_four]
    exact Nat.sqrt_eq' 2
  have pure_sq (p : A) (hp : p.re = 0) :
      p * p = algebraMap F A (-pureNorm a b p.imI p.imJ p.imK) := by
    have hstar : star p = -p := by ext <;> simp [A, hp]
    have he : p * star p = algebraMap F A (p * star p).re := p.mul_star_eq_coe
    rw [quaternion_norm_formula, hstar, mul_neg, hp, zero_pow (by decide : 2 ≠ 0), zero_add] at he
    rw [map_neg, ← he, neg_neg]
  constructor
  · rintro ⟨x, y, z, he⟩ ⟨s, hs⟩
    let p : A := ⟨0, x, y, z⟩
    have hsq : p * p = algebraMap F A (s * s) := by
      rw [← hs, ← he]
      exact pure_sq p rfl
    have hfact : (p - algebraMap F A s) * (p + algebraMap F A s) = 0 := by
      rw [sub_mul, mul_add, mul_add, hsq, map_mul, Algebra.commutes s p]
      abel
    rcases mul_eq_zero.mp hfact with hl | hr
    · have hzero : s = 0 := (congrArg QuaternionAlgebra.re (sub_eq_zero.mp hl)).symm
      exact ht (by simpa [hzero] using hs)
    · have hp' : p = -algebraMap F A s := eq_neg_of_add_eq_zero_left hr
      have hzero : s = 0 := by
        have hh := congrArg QuaternionAlgebra.re hp'
        simpa [A, p, QuaternionAlgebra.algebraMap_eq] using hh.symm
      exact ht (by simpa [hzero] using hs)
  · intro ht'
    let : Fact (¬ IsSquare (-t)) := ⟨ht'⟩
    let E := QuadraticAlgebra F (-t) 0
    let : Algebra.IsSeparable F E := separable_quadratic h₂
    obtain ⟨f⟩ := quadratic_embedding hA hdeg (QuadraticAlgebra.finrank_eq_two (-t) 0)
    let w : E := ⟨0, 1⟩
    let p : A := f w
    have hsq : p * p = algebraMap F A (-t) := by
      have hw : w * w = algebraMap F E (-t) := by ext <;> simp [E, w]
      exact (f.map_mul w w).symm.trans ((congrArg f hw).trans (f.commutes (-t)))
    have hns : ∀ s : F, p ≠ algebraMap F A s := by
      intro s hs
      have hw := f.injective (hs.trans (f.commutes s).symm)
      exact one_ne_zero (congrArg QuadraticAlgebra.im hw)
    have hr : p.re = 0 := by
      by_contra hne
      have e (z : F) (hz : 2 * p.re * z = 0) : z = 0 :=
        (mul_eq_zero.mp hz).resolve_left (mul_ne_zero h₂ hne)
      have hI := congrArg QuaternionAlgebra.imI hsq
      have hJ := congrArg QuaternionAlgebra.imJ hsq
      have hK := congrArg QuaternionAlgebra.imK hsq
      simp [A, QuaternionAlgebra.algebraMap_eq] at hI hJ hK
      apply hns p.re
      ext
      · rfl
      · exact e _ (by linear_combination hI)
      · exact e _ (by linear_combination hJ)
      · exact e _ (by linear_combination hK)
    have hvalue := (algebraMap F A).injective ((pure_sq p hr).symm.trans hsq)
    exact ⟨p.imI, p.imJ, p.imK, neg_injective hvalue⟩

private theorem ternary_scale {F : Type u} [Field F]
    {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (x y z : F) :
    let s := a * b / c
    s * pureNorm (-a / s) (-b / s) x y z = a * x ^ 2 + b * y ^ 2 + c * z ^ 2 := by
  dsimp
  unfold pureNorm
  field_simp
  ring

theorem ternary_values : TernaryValues.{u} := by
  intro F _ _ _ _ h₂ a b c ha hb hc h t ht
  let s := a * b / c
  have hs : s ≠ 0 := div_ne_zero (mul_ne_zero ha hb) hc
  have hnorm (x y z : F) :
      s * pureNorm (-a / s) (-b / s) x y z = a * x ^ 2 + b * y ^ 2 + c * z ^ 2 :=
    ternary_scale ha hb hc x y z
  have hani (x y z : F) (hz : pureNorm (-a / s) (-b / s) x y z = 0) :
      x = 0 ∧ y = 0 ∧ z = 0 := h x y z (by rw [← hnorm, hz, mul_zero])
  rw [← pure_norm_values h₂ (-a / s) (-b / s) hani (t / s) (div_ne_zero ht hs)]
  constructor
  · rintro ⟨x, y, z, he⟩
    exact ⟨x, y, z, (eq_div_iff hs).mpr (by rw [mul_comm, hnorm, he])⟩
  · rintro ⟨x, y, z, he⟩
    exact ⟨x, y, z, by rw [← hnorm, he, mul_div_cancel₀ t hs]⟩


/-- The anisotropic binary form is the field norm in the basis
consisting of one and the quadratic generator, scaled by its first coefficient. -/
theorem binary_extension_norm : BinaryExtensionNorm.{u} := by
  intro F _ h₂ a b ha h
  let d := -b / a
  have hd : ¬ IsSquare d := by
    rintro ⟨s, hs⟩
    have hd' : a * d = -b := by dsimp [d]; field_simp
    have he : a * s ^ 2 + b * (1 : F) ^ 2 = 0 := by
      rw [pow_two s, ← hs, hd']; simp
    exact one_ne_zero (h s 1 he).2
  let : Fact (¬ IsSquare d) := ⟨hd⟩
  let E := QuadraticAlgebra F d 0
  let e : (F × F) ≃ₗ[F] E :=
    { toFun := fun z => ⟨z.1, z.2⟩
      invFun := fun z => (z.re, z.im)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨E, inferInstance, inferInstance, separable_quadratic h₂,
    QuadraticAlgebra.finrank_eq_two d 0, e, ?_⟩
  intro x y
  have hn (z : E) : Algebra.norm F z = QuadraticAlgebra.norm z :=
    QuadraticAlgebra.det_toLinearMap_eq_norm z
  rw [hn, QuadraticAlgebra.norm_def]
  change _ = a * (x * x + 0 * x * y - d * y * y)
  dsimp [d]
  field_simp
  ring

open private liftSimpleRoot quadratic quadratic_monic quadratic_derivative quadratic_aeval from
  LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting

open ValuativeRel in
private theorem local_quadratic_root {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    ∃ p : ℕ, 0 < p ∧ ∃ x : F, x ^ 2 + x + (p : F) = 0 := by
  let R := (valuation F).valuationSubring
  let k := IsLocalRing.ResidueField R
  let : Finite k :=
    IsNonarchimedeanLocalField.instFiniteResidueFieldSubtypeMemSubringIntegerValueGroupWithZeroValuation F
  let p := ringChar k
  have hp : 0 < p := Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite k)
  have hp0 : (p : k) = 0 := CharP.cast_eq_zero k p
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have : IsAdicComplete (IsLocalRing.maximalIdeal R) R :=
    inferInstanceAs (IsAdicComplete (IsLocalRing.maximalIdeal (Valuation.integer (valuation F)))
      (Valuation.integer (valuation F)))
  have h₀ : Polynomial.aeval (0 : k) (quadratic (1 : R) (p : R)) = 0 := by
    rw [quadratic_aeval]
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, map_natCast] using hp0
  have h₁ : Polynomial.aeval (0 : k) (quadratic (1 : R) (p : R)).derivative ≠ 0 := by
    rw [quadratic_derivative]
    simp
  obtain ⟨x, hx, _⟩ := liftSimpleRoot _ (quadratic_monic 1 (p : R)) 0 h₀ h₁
  refine ⟨p, hp, (x : F), ?_⟩
  have hh : x ^ 2 + x + (p : R) = 0 := by simpa [Polynomial.IsRoot, quadratic] using hx
  let f := (valuation F).valuationSubring.subtype
  change f x ^ 2 + f x + (p : F) = 0
  simpa only [map_add, map_pow, map_natCast, map_zero] using congrArg f hh

private theorem local_not_pythagorean {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (h : ∀ x y : F, IsSquare (x ^ 2 + y ^ 2)) : IsSquare (-1 : F) := by
  obtain ⟨p, hp, x, hx'⟩ := local_quadratic_root (F := F)
  have hnat (n : ℕ) : IsSquare (n : F) := by
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨a, ha⟩ := ih
      simpa only [Nat.cast_succ, ha, pow_two, mul_one] using h a 1
  let n := 4 * p - 2
  have hn : n + 2 = 4 * p := by dsimp [n]; omega
  have hnf : (n : F) + 2 = 4 * (p : F) := by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using congrArg (fun n : ℕ => (n : F)) hn
  obtain ⟨a, ha⟩ := hnat n
  have hh : a ^ 2 + (2 * x + 1) ^ 2 = -1 := by
    rw [pow_two a, ← ha]
    linear_combination 4 * hx' + hnf
  exact hh ▸ h a (2 * x + 1)

/-- If the norm of the quadratic generator is already a square, the norm
form is equivalent to the sum of two squares. Closure of squares under
addition would make minus one a square by Hensel's lemma. -/
theorem binary_norm_classes : BinaryNormClasses.{u} := by
  intro F _ _ _ _ _ d hd
  by_cases hs : IsSquare (-d)
  · obtain ⟨s, hs⟩ := hs
    have hd0 : d ≠ 0 := fun he => hd ⟨0, by simp [he]⟩
    have hs0 : s ≠ 0 := by
      intro hz
      exact hd0 (neg_eq_zero.mp (by simpa [hz] using hs))
    by_contra! h
    have h' (x y : F) : IsSquare (x ^ 2 + y ^ 2) := by
      have he : x ^ 2 - d * (y / s) ^ 2 = x ^ 2 + y ^ 2 := by
        rw [sub_eq_add_neg, ← neg_mul, hs]
        field_simp
      exact he ▸ h x (y / s)
    obtain ⟨r, hr⟩ := local_not_pythagorean h'
    exact hd ⟨r * s, by linear_combination s ^ 2 * hr - hs⟩
  · exact ⟨0, 1, by simpa using hs⟩

/-- Transfer the value calculation from diagonal coordinates to the given form. -/
theorem ternary_form_values : TernaryFormValues.{u,v} := by
  classical
  intro F _ _ _ _ h₂ V _ _ _ q hdim hani
  let : Invertible (2 : F) := (isUnit_iff_ne_zero.mpr h₂).invertible
  obtain ⟨w, ⟨e⟩⟩ := q.equivalent_weightedSumSquares
  generalize heq : Module.finrank F V = n at w e
  have hn : n = 3 := heq.symm.trans hdim
  rcases hn with rfl
  let a := w 0
  let b := w 1
  let c := w 2
  have he (f : Fin 3 → F) : q (e.symm f) = a * f 0 ^ 2 + b * f 1 ^ 2 + c * f 2 ^ 2 := by
    rw [e.symm.map_app, QuadraticMap.weightedSumSquares_apply]
    simp [Fin.sum_univ_succ, a, b, c]
    ring
  have hcoords (x y z : F) (hz : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) :
      x = 0 ∧ y = 0 ∧ z = 0 := by
    let f : Fin 3 → F := ![x, y, z]
    have hfq : q (e.symm f) = 0 := (he f).trans hz
    have hf : e.symm f = 0 := by
      by_contra hne
      exact hani ⟨_, hne, hfq⟩
    have hzero : f = 0 := e.symm.toLinearEquiv.injective (by simpa using hf)
    exact ⟨congrFun hzero 0, congrFun hzero 1, congrFun hzero 2⟩
  have ha : a ≠ 0 := fun h => one_ne_zero (hcoords 1 0 0 (by simp [h])).1
  have hb : b ≠ 0 := fun h => one_ne_zero (hcoords 0 1 0 (by simp [h])).2.1
  have hc : c ≠ 0 := fun h => one_ne_zero (hcoords 0 0 1 (by simp [h])).2.2
  let s := a * b / c
  let α := -a / s
  let β := -b / s
  let D := QuaternionAlgebra F α 0 β
  have hs : s ≠ 0 := div_ne_zero (mul_ne_zero ha hb) hc
  have hα : α ≠ 0 := div_ne_zero (neg_ne_zero.mpr ha) hs
  have hβ : β ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb) hs
  have hscale (x y z : F) :
      s * pureNorm α β x y z = a * x ^ 2 + b * y ^ 2 + c * z ^ 2 :=
    ternary_scale ha hb hc x y z
  have hpure (x y z : F) (h : pureNorm α β x y z = 0) :
      x = 0 ∧ y = 0 ∧ z = 0 := hcoords x y z (by rw [← hscale, h, mul_zero])
  have hD : RM03.CSA.IsCentralSimple F D := by
    let : DivisionRing D := DivisionRing.ofIsUnitOrEqZero (quaternion_isUnit_or_zero hpure)
    exact RM03.CSA.isCentralSimple_of_isCentralDivision F D
      ⟨quaternion_central h₂ hα, inferInstance⟩
  refine ⟨s, α, β, hs, hD, fun p hp => (quaternion_isUnit_or_zero hpure p).resolve_right hp, ?_, ?_⟩
  · let f : (Fin 3 → F) ≃ₗ[F] (QuaternionAlgebra.reₗ α 0 β).ker :=
      { toFun := fun v => ⟨⟨0, v 0, v 1, v 2⟩, rfl⟩
        invFun := fun p => ![p.val.imI, p.val.imJ, p.val.imK]
        left_inv := fun v => by ext i; fin_cases i <;> rfl
        right_inv := fun p => by
          apply Subtype.ext
          exact QuaternionAlgebra.ext (LinearMap.mem_ker.mp p.prop).symm rfl rfl rfl
        map_add' := fun _ _ => Subtype.ext
          (QuaternionAlgebra.ext (zero_add (0 : F)).symm rfl rfl rfl)
        map_smul' := fun r v => Subtype.ext (by
          change QuaternionAlgebra.mk 0 (r • v 0) (r • v 1) (r • v 2) =
            r • (⟨0, v 0, v 1, v 2⟩ : D)
          rw [QuaternionAlgebra.smul_mk, smul_zero]) }
    refine ⟨e.toLinearEquiv.trans f, fun x => ?_⟩
    let p := (f (e x)).val
    change q x = s * _root_.Specs.RM03.CSA.reducedNorm hD p
    have hn : _root_.Specs.RM03.CSA.reducedNorm hD p = (p * star p).re :=
      quaternion_reduced_norm h₂ hα hβ hD p
    rw [hn, quaternion_norm_formula]
    change q x = s * (0 ^ 2 + pureNorm α β (e x 0) (e x 1) (e x 2))
    rw [zero_pow (by decide : 2 ≠ 0), zero_add, hscale]
    simpa only [QuadraticMap.IsometryEquiv.symm_apply_apply] using he (e x)
  · intro t ht
    rw [← ternary_values h₂ a b c ha hb hc hcoords t ht]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨e x 0, e x 1, e x 2, ?_⟩
      simpa only [QuadraticMap.IsometryEquiv.symm_apply_apply] using (he (e x)).symm
    · rintro ⟨x, y, z, ht⟩
      exact ⟨e.symm ![x, y, z], (he _).trans ht⟩

/-- The binary norm model and the distinct represented classes apply to
the original quadratic space through an isometry to diagonal coordinates. -/
theorem binary_form_norm_classes : BinaryFormNormClasses.{u,v} := by
  classical
  intro F _ _ _ _ h₂ V _ _ _ q hdim hani
  let : Invertible (2 : F) := (isUnit_iff_ne_zero.mpr h₂).invertible
  obtain ⟨w, ⟨e⟩⟩ := q.equivalent_weightedSumSquares
  generalize heq : Module.finrank F V = n at w e
  have hn : n = 2 := heq.symm.trans hdim
  rcases hn with rfl
  let f := e.toLinearEquiv.trans (LinearEquiv.finTwoArrow F F)
  let a := w 0
  let b := w 1
  have he (x y : F) : q (f.symm (x, y)) = a * x ^ 2 + b * y ^ 2 := by
    change q (e.symm ((LinearEquiv.finTwoArrow F F).symm (x, y))) = _
    rw [e.symm.map_app, QuadraticMap.weightedSumSquares_apply]
    simp [Fin.sum_univ_succ, a, b, LinearEquiv.finTwoArrow, pow_two]
  have hcoords (x y : F) (hz : a * x ^ 2 + b * y ^ 2 = 0) : x = 0 ∧ y = 0 := by
    have hz' : q (f.symm (x, y)) = 0 := (he x y).trans hz
    have hh : f.symm (x, y) = 0 := by
      by_contra hne
      exact hani ⟨_, hne, hz'⟩
    have hzero : (x, y) = 0 := f.symm.injective (by simpa using hh)
    exact ⟨congrArg Prod.fst hzero, congrArg Prod.snd hzero⟩
  have ha : a ≠ 0 := fun h => one_ne_zero (hcoords 1 0 (by simp [h])).1
  constructor
  · obtain ⟨E, _, _, hsep, hd, g, hg⟩ := binary_extension_norm h₂ a b ha hcoords
    refine ⟨E, inferInstance, inferInstance, hsep, hd, a, ha, f.trans g, ?_⟩
    intro x
    have h := (he (f x).1 (f x).2).trans (hg (f x).1 (f x).2)
    simpa using h
  · let d := -b / a
    have hscale (x y : F) : a * (x ^ 2 - d * y ^ 2) = a * x ^ 2 + b * y ^ 2 := by
      dsimp [d]
      field_simp
      ring
    have hd : ¬ IsSquare d := by
      rintro ⟨s, hs⟩
      have h : a * (s ^ 2 - d * (1 : F) ^ 2) = 0 := by
        rw [pow_two s, ← hs, one_pow, mul_one, sub_self, mul_zero]
      exact one_ne_zero (hcoords s 1 ((hscale s 1).symm.trans h)).2
    obtain ⟨x, y, hn⟩ := binary_norm_classes h₂ d hd
    let r := x ^ 2 - d * y ^ 2
    have hr : r ≠ 0 := fun h => hn ⟨0, by simp [r, h]⟩
    have hx : q (f.symm (1, 0)) = a := by simpa using he 1 0
    have hy : q (f.symm (x, y)) = a * r := (he x y).trans (hscale x y).symm
    refine ⟨f.symm (1, 0), f.symm (x, y), hx.symm ▸ ha, hy.symm ▸ mul_ne_zero ha hr, ?_⟩
    rw [hx, hy, mul_div_cancel_left₀ _ ha]
    exact hn

private theorem diagonal_five_isotropic {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (h₂ : (2 : F) ≠ 0)
    (a b c e f : F) :
    ∃ x y z m n : F, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ m ≠ 0 ∨ n ≠ 0) ∧
      a * x ^ 2 + b * y ^ 2 + c * z ^ 2 + (e * m ^ 2 + f * n ^ 2) = 0 := by
  by_contra! h
  have ha : a ≠ 0 := by intro h0; exact h 1 0 0 0 0 (Or.inl one_ne_zero) (by simp [h0])
  have hb : b ≠ 0 := by intro h0; exact h 0 1 0 0 0 (Or.inr (Or.inl one_ne_zero)) (by simp [h0])
  have hc : c ≠ 0 := by intro h0; exact h 0 0 1 0 0 (Or.inr (Or.inr (Or.inl one_ne_zero))) (by simp [h0])
  have he : e ≠ 0 := by
    intro h0
    exact h 0 0 0 1 0 (Or.inr (Or.inr (Or.inr (Or.inl one_ne_zero)))) (by simp [h0])
  let d := -f / e
  have hbinary (m n : F) : e * (m ^ 2 - d * n ^ 2) = e * m ^ 2 + f * n ^ 2 := by
    dsimp [d]
    field_simp
    ring
  have hd : ¬ IsSquare d := by
    rintro ⟨s, hs⟩
    apply h 0 0 0 s 1 (Or.inr (Or.inr (Or.inr (Or.inr one_ne_zero))))
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add]
    rw [← hbinary, pow_two, ← hs, one_pow, mul_one, sub_self, mul_zero]
  obtain ⟨m, n, hns⟩ := binary_norm_classes h₂ d hd
  let t := m ^ 2 - d * n ^ 2
  have ht : t ≠ 0 := fun hz => hns ⟨0, by simp [t, hz]⟩
  have hmn : m ≠ 0 ∨ n ≠ 0 := by
    by_contra! hh
    exact ht (by simp [t, hh.1, hh.2])
  have hternary (x y z : F) (hz : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) :
      x = 0 ∧ y = 0 ∧ z = 0 := by
    have hneg : ¬ (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) := by
      intro hh
      exact h x y z 0 0 (hh.imp_right (Or.imp_right Or.inl)) (by simpa using hz)
    simpa only [not_or, not_not] using hneg
  let s := a * b / c
  have he₀ : IsSquare (e / s) := by
    by_contra hs
    obtain ⟨x, y, z, hz⟩ := (ternary_values h₂ a b c ha hb hc hternary (-e) (neg_ne_zero.mpr he)).mpr
      (by simpa [s, neg_div] using hs)
    exact h x y z 1 0 (Or.inr (Or.inr (Or.inr (Or.inl one_ne_zero)))) (by simp [hz])
  have he₁ : IsSquare (e * t / s) := by
    by_contra hs
    obtain ⟨x, y, z, hz⟩ := (ternary_values h₂ a b c ha hb hc hternary (-(e * t))
      (neg_ne_zero.mpr (mul_ne_zero he ht))).mpr (by simpa [s, neg_div] using hs)
    exact h x y z m n (Or.inr (Or.inr (Or.inr hmn))) (by rw [hz, ← hbinary, neg_add_cancel])
  apply hns
  have hs : s ≠ 0 := div_ne_zero (mul_ne_zero ha hb) hc
  have hs' : e * t / s = t * (e / s) := by ring
  rw [hs'] at he₁
  simpa only [mul_div_cancel_right₀ _ (div_ne_zero he hs)] using he₁.div he₀

open LinearAlgebraicGroups.Specs.Arithmetic.IsotropicSpinGeneration (IsIsotropic) in
theorem local_isotropy : LocalIsotropy.{u,v} := by
  classical
  intro F _ _ _ _ h₂ V _ _ _ q _ hdim
  let : Invertible (2 : F) := (isUnit_iff_ne_zero.mpr h₂).invertible
  obtain ⟨w, ⟨e⟩⟩ := q.equivalent_weightedSumSquares
  generalize Module.finrank F V = j at w e hdim
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hdim
  let a (i : Fin 5) := w (Fin.castAdd k i)
  obtain ⟨x, y, z, m, n, hne, hz⟩ := diagonal_five_isotropic h₂ (a 0) (a 1) (a 2) (a 3) (a 4)
  let xs : Fin 5 → F := ![x, y, z, m, n]
  let v : Fin (5 + k) → F := Fin.addCases xs 0
  have hv : v ≠ 0 := by
    intro he
    have hh (i : Fin 5) : xs i = 0 := by
      simpa [v] using congrFun he (Fin.castAdd k i)
    rcases hne with h | h | h | h | h
    · exact h (hh 0)
    · exact h (hh 1)
    · exact h (hh 2)
    · exact h (hh 3)
    · exact h (hh 4)
  refine ⟨e.symm v, fun h => hv (e.symm.toLinearEquiv.injective (by simpa using h)), ?_⟩
  rw [e.symm.map_app, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_add]
  simp [v, Fin.sum_univ_succ, xs, a] at hz ⊢
  linear_combination hz

open private reflection_mul_vector from LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
open private scalar_injective from LinearAlgebraicGroups.Albert.SpinFunctor

section ReflectionWords

variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]

private def reflectionLinear (q : QuadraticForm F V) (w : V) : V →ₗ[F] V :=
  LinearMap.id - ((q w)⁻¹ • q.polarBilin w).smulRight w

private theorem reflectionLinear_apply (q : QuadraticForm F V) (w x : V) :
    reflectionLinear q w x = reflection q w x := by
  simp [reflectionLinear, reflection, div_eq_inv_mul]

private theorem polar_self_eq (q : QuadraticForm F V) (w : V) :
    q.polarBilin w w = 2 * q w := by
  simpa only [QuadraticMap.polarBilin_apply_apply, two_smul, two_mul] using
    QuadraticMap.polar_self q w

private theorem reflection_det [FiniteDimensional F V] (q : QuadraticForm F V)
    (w : ReflectionVector q) (h₂ : (2 : F) ≠ 0) :
    LinearMap.det (reflectionLinear q w.val) = -1 := by
  let L := F ∙ w.val
  let N := LinearMap.BilinForm.orthogonal q.polarBilin L
  have hdiag : q.polarBilin w.val w.val ≠ 0 := by
    rw [polar_self_eq]
    exact mul_ne_zero h₂ w.prop
  have hc : IsCompl L N := LinearMap.BilinForm.isCompl_span_singleton_orthogonal hdiag
  let e := L.prodEquivOfIsCompl N hc
  let j : L →ₗ[F] L := (-1 : F) • LinearMap.id
  let k : N →ₗ[F] N := LinearMap.id
  have hl (x : L) : reflectionLinear q w.val x.val = -x.val := by
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp x.prop
    rw [← ht, map_smul, reflectionLinear_apply, reflection, polar_self_eq, mul_div_cancel_right₀ _ w.prop]
    rw [two_smul, sub_add_eq_sub_sub, sub_self, zero_sub, smul_neg]
  have hn (y : N) : reflectionLinear q w.val y.val = y.val := by
    have hy := (LinearMap.BilinForm.mem_orthogonal_iff.mp y.prop) w.val
      (Submodule.mem_span_singleton_self w.val)
    simp [reflectionLinear_apply, reflection, hy]
  have hm : reflectionLinear q w.val = e.conj (j.prodMap k) := by
    ext x
    obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective x
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    change reflectionLinear q w.val (a.val + b.val) = (-1 : F) • a.val + b.val
    rw [map_add, hl, hn, neg_one_smul]
  have hw : w.val ≠ 0 := fun h => w.prop (h ▸ q.map_zero)
  rw [hm, show e.conj (j.prodMap k) = e.toLinearMap.comp ((j.prodMap k).comp e.symm.toLinearMap) from rfl,
    LinearMap.det_conj, LinearMap.det_prodMap]
  change LinearMap.det ((-1 : F) • (LinearMap.id : L →ₗ[F] L)) *
    LinearMap.det (LinearMap.id : N →ₗ[F] N) = -1
  rw [LinearMap.det_smul, finrank_span_singleton hw, pow_one, LinearMap.det_id, mul_one,
    LinearMap.det_id, mul_one]

private def reflectionWordLinear (q : QuadraticForm F V) (l : List (ReflectionVector q)) :
    V →ₗ[F] V :=
  l.foldr (fun w g => (reflectionLinear q w.val).comp g) LinearMap.id

private theorem reflectionWordLinear_apply (q : QuadraticForm F V)
    (l : List (ReflectionVector q)) (x : V) :
    reflectionWordLinear q l x = reflectionWord q l x := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change reflectionLinear q w.val (reflectionWordLinear q l x) =
      reflection q w.val (reflectionWord q l x)
    rw [reflectionLinear_apply, ih]

private theorem reflectionWord_det [FiniteDimensional F V] (q : QuadraticForm F V)
    (l : List (ReflectionVector q)) (h₂ : (2 : F) ≠ 0) :
    LinearMap.det (reflectionWordLinear q l) = (-1 : F) ^ l.length := by
  induction l with
  | nil => simp [reflectionWordLinear]
  | cons w l ih =>
    change LinearMap.det ((reflectionLinear q w.val).comp (reflectionWordLinear q l)) = _
    rw [LinearMap.det_comp, reflection_det q w h₂, ih, List.length_cons, pow_succ', mul_comm]

private theorem reflectionWord_even [FiniteDimensional F V] [CharZero F] (q : QuadraticForm F V)
    (g : specialOrthogonal q) (l : List (ReflectionVector q))
    (hl : ∀ x, g.val x = reflectionWord q l x) : Even l.length := by
  have hh : reflectionWordLinear q l = g.val.toLinearMap :=
    LinearMap.ext (f := reflectionWordLinear q l) (g := g.val.toLinearMap)
      fun x => (reflectionWordLinear_apply q l x).trans (hl x).symm
  have hd := reflectionWord_det q l (by norm_num)
  rw [hh, ← LinearEquiv.coe_det, g.prop.2, Units.val_one] at hd
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : F) ≠ 1)).mp hd.symm

private theorem reflectionWord_append (q : QuadraticForm F V) (l m : List (ReflectionVector q))
    (x : V) : reflectionWord q (l ++ m) x = reflectionWord q l (reflectionWord q m x) := by
  simp [reflectionWord, List.foldr_append]

private theorem reflectionNorm_append (q : QuadraticForm F V) (l m : List (ReflectionVector q)) :
    reflectionNorm q (l ++ m) = reflectionNorm q l * reflectionNorm q m := by
  simp [reflectionNorm]

private theorem exists_even_word [FiniteDimensional F V] [CharZero F] (q : QuadraticForm F V)
    (hq : LinearMap.ker q.polarBilin = ⊥) (g : specialOrthogonal q) :
    ∃ l : List (ReflectionVector q), Even l.length ∧ ∀ x, g.val x = reflectionWord q l x := by
  obtain ⟨l, hl, hword⟩ := SpinOrthogonalWords.orthogonalWords q (Or.inl hq) g.val g.prop.1
  let l' : List (ReflectionVector q) := l.attach.map fun w => ⟨w.val, hl w.val w.prop⟩
  have hh (x : V) : g.val x = reflectionWord q l' x := by
    rw [hword]
    simp [l', reflectionWord, List.foldr_map, reflection]
  exact ⟨l', reflectionWord_even q g l' hh, hh⟩

end ReflectionWords

section CliffordWords

variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]
variable (q : QuadraticForm F V)

private def cliffordWord (l : List (ReflectionVector q)) : (CliffordAlgebra q)ˣ :=
  (l.map fun w => (CliffordAlgebra.isUnit_ι_of_isUnit q (isUnit_iff_ne_zero.mpr w.prop)).unit).prod

private theorem cliffordWord_cons (w : ReflectionVector q) (l : List (ReflectionVector q)) :
    (cliffordWord q (w :: l)).val = ι q w.val * (cliffordWord q l).val := by
  simp [cliffordWord]

private theorem cliffordWord_grade (l : List (ReflectionVector q)) :
    (cliffordWord q l).val ∈ evenOdd q (l.length : ZMod 2) := by
  induction l with
  | nil => exact SetLike.one_mem_graded (evenOdd q)
  | cons w l ih =>
    rw [cliffordWord_cons, List.length_cons, Nat.cast_add, Nat.cast_one, add_comm]
    exact SetLike.mul_mem_graded (ι_mem_evenOdd_one q w.val) ih

private theorem cliffordWord_even (l : List (ReflectionVector q)) (hl : Even l.length) :
    (cliffordWord q l).val ∈ evenOdd q 0 := by
  have hlen : (l.length : ZMod 2) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (even_iff_two_dvd.mp hl)
  simpa only [hlen] using cliffordWord_grade q l

private theorem cliffordWord_action (l : List (ReflectionVector q)) (x : V) :
    (cliffordWord q l).val * ι q x =
      ι q (reflectionWord q l x) * involute (cliffordWord q l).val := by
  induction l with
  | nil => simp [cliffordWord, reflectionWord]
  | cons w l ih =>
    rw [cliffordWord_cons]
    change (ι q w.val * (cliffordWord q l).val) * ι q x =
      ι q (reflection q w.val (reflectionWord q l x)) * involute (ι q w.val * (cliffordWord q l).val)
    rw [mul_assoc, ih, ← mul_assoc, map_mul, involute_ι, ← mul_assoc, mul_neg,
      reflection_mul_vector q _ _ w.prop, neg_neg]

private theorem cliffordWord_norm (l : List (ReflectionVector q)) :
    reverse (cliffordWord q l).val * (cliffordWord q l).val =
      algebraMap F _ (reflectionNorm q l).val := by
  induction l with
  | nil => simp [cliffordWord, reflectionNorm]
  | cons w l ih =>
    let a := (cliffordWord q l).val
    have hcomm := Algebra.commutes (R := F) (q w.val) (reverse a)
    rw [cliffordWord_cons, CliffordAlgebra.reverse.map_mul, reverse_ι,
      mul_assoc, ← mul_assoc (ι q w.val), ι_sq_scalar]
    change reverse a * (algebraMap F _ (q w.val) * a) = _
    rw [← mul_assoc, ← hcomm, mul_assoc, show reverse a * a = _ from ih]
    simp [reflectionNorm, map_mul]

private theorem even_implementer_ratio [FiniteDimensional F V]
    (hq : LinearMap.ker q.polarBilin = ⊥) (g : V ≃ₗ[F] V)
    (a b : (CliffordAlgebra q)ˣ) (ha : a.val ∈ evenOdd q 0) (hb : b.val ∈ evenOdd q 0)
    (hacta : ∀ x, a.val * ι q x = ι q (g x) * a.val)
    (hactb : ∀ x, b.val * ι q x = ι q (g x) * b.val) :
    ∃ r : Fˣ, b.val = a.val * algebraMap F _ r.val := by
  classical
  let c := a⁻¹ * b
  have hai : involute a⁻¹.val = a⁻¹.val := by
    have h : Units.map (involute (Q := q)).toMonoidHom a = a :=
      Units.ext (involute_eq_of_mem_even ha)
    exact congrArg Units.val ((map_inv (Units.map (involute (Q := q)).toMonoidHom) a).trans
      (congrArg Inv.inv h))
  have hc (x : V) : ι q x * c.val = involute c.val * ι q x := by
    have hi : ι q x * a⁻¹.val = a⁻¹.val * ι q (g x) := by
      calc
        _ = a⁻¹.val * (a.val * ι q x) * a⁻¹.val := by
          rw [← mul_assoc a⁻¹.val, Units.inv_mul, one_mul]
        _ = _ := by rw [hacta, mul_assoc a⁻¹.val, mul_assoc (ι q (g x)), Units.mul_inv, mul_one]
    change ι q x * (a⁻¹.val * b.val) = involute (a⁻¹.val * b.val) * ι q x
    rw [map_mul, hai, involute_eq_of_mem_even hb, ← mul_assoc, hi, mul_assoc, ← hactb, mul_assoc]
  let B := Module.finBasis F V
  obtain ⟨r, hr⟩ := IsotropicSpinGeneration.gradedCentralizerCalculation q B hq c.val hc
  have hE : b.val = a.val * algebraMap F _ r := by
    rw [← hr]
    change _ = a.val * (a⁻¹.val * b.val)
    rw [← mul_assoc, Units.mul_inv, one_mul]
  let : Nontrivial (CliffordAlgebra q) := Function.Injective.nontrivial (scalar_injective q B)
  have hr₀ : r ≠ 0 := by
    intro h
    exact b.ne_zero (by simp [hE, h])
  exact ⟨Units.mk0 r hr₀, hE⟩

private theorem reverse_norm_scaled (a : CliffordAlgebra q) (r : F) :
    reverse (a * algebraMap F _ r) * (a * algebraMap F _ r) =
      (reverse a * a) * algebraMap F _ (r * r) := by
  rw [CliffordAlgebra.reverse.map_mul, reverse.commutes, map_mul]
  rw [Algebra.commutes (R := F) r (reverse a), mul_assoc (reverse a),
    ← mul_assoc (algebraMap F _ r) a, Algebra.commutes (R := F) r a]
  simp only [mul_assoc]

private theorem reflectionWord_same_class [FiniteDimensional F V]
    (hq : LinearMap.ker q.polarBilin = ⊥) (g : specialOrthogonal q)
    (l m : List (ReflectionVector q)) (hl : Even l.length) (hm : Even m.length)
    (hdl : ∀ x, g.val x = reflectionWord q l x) (hdm : ∀ x, g.val x = reflectionWord q m x) :
    QuotientGroup.mk' (Subgroup.square Fˣ) (reflectionNorm q l) =
      QuotientGroup.mk' (Subgroup.square Fˣ) (reflectionNorm q m) := by
  have ha := cliffordWord_even q l hl
  have hb := cliffordWord_even q m hm
  have hacta (x) := cliffordWord_action q l x
  have hactb (x) := cliffordWord_action q m x
  simp_rw [← hdl, involute_eq_of_mem_even ha] at hacta
  simp_rw [← hdm, involute_eq_of_mem_even hb] at hactb
  obtain ⟨r, hr⟩ := even_implementer_ratio q hq g.val _ _ ha hb hacta hactb
  have hn : reflectionNorm q m = reflectionNorm q l * (r * r) := by
    apply Units.ext
    apply scalar_injective q (Module.finBasis F V)
    change algebraMap F _ (reflectionNorm q m).val =
      algebraMap F _ ((reflectionNorm q l).val * (r.val * r.val))
    rw [← cliffordWord_norm, hr, reverse_norm_scaled, cliffordWord_norm]
    simp only [map_mul]
  rw [hn, map_mul]
  have hs : QuotientGroup.mk' (Subgroup.square Fˣ) (r * r) = 1 :=
    (QuotientGroup.eq_one_iff (N := Subgroup.square Fˣ) (r * r)).mpr ⟨r, rfl⟩
  rw [hs, mul_one]

open LinearAlgebraicGroups.Albert.SpinSpecification (ScalarClifford spinUnits evenPart reversion
  vectors conjugate IsVectorAction) in
open private conjugate_inverse from LinearAlgebraicGroups.Albert.SpinFunctor in
set_option maxHeartbeats 800000 in
private theorem hasSpinLift_iff_intrinsic (g : specialOrthogonal q) :
    HasSpinLift q g ↔ ∃ a : (CliffordAlgebra q)ˣ,
      a.val ∈ evenOdd q 0 ∧ reverse a.val * a.val = 1 ∧
      ∀ x : V, a.val * ι q x = ι q (g.val x) * a.val := by
  change (∃ a : (ScalarClifford q F)ˣ,
    a ∈ spinUnits q F ∧ IsVectorAction q F a (g.val.baseChange F F V V)) ↔ _
  let e := Algebra.TensorProduct.lid F (CliffordAlgebra q)
  let gF := g.val.baseChange F F V V
  have heven (z : ScalarClifford q F) : z ∈ evenPart q F ↔ e z ∈ evenOdd q 0 := by
    constructor
    · have hle : evenPart q F ≤ (evenOdd q 0).comap e.toLinearMap := by
        rw [show evenPart q F = (evenOdd q 0).baseChange F from rfl, Submodule.baseChange_eq_span]
        apply Submodule.span_le.mpr
        rintro _ ⟨w, hw, rfl⟩
        simpa [e] using hw
      exact fun h => hle h
    · intro h
      have hz : (1 ⊗ₜ[F] e z : ScalarClifford q F) = z := e.injective (by simp [e])
      exact hz ▸ Submodule.tmul_mem_baseChange_of_mem (1 : F) h
  have hev (x : V) : e (vectors q F (1 ⊗ₜ[F] x)) = ι q x := by
    simp [e, vectors, LinearMap.baseChange_tmul]
  have hnorm (a : ScalarClifford q F) : reversion q F a * a = 1 ↔
      reverse (e a) * e a = 1 := by
    have hr : e (reversion q F a) = reverse (e a) := by
      induction a using TensorProduct.inductionOn with
      | tmul r x => simp only [e, reversion, LinearMap.baseChange_tmul,
          Algebra.TensorProduct.lid_tmul, map_smul]
      | add x y hx hy => simp only [map_add, hx, hy]
    calc
      _ ↔ e (reversion q F a * a) = e 1 := e.injective.eq_iff.symm
      _ ↔ _ := by rw [map_mul, map_one, hr]
  have haction (a : (ScalarClifford q F)ˣ) :
      IsVectorAction q F a gF ↔
        ∀ x : V, e a.val * ι q x = ι q (g.val x) * e a.val := by
    have he (x : V) :
        vectors q F (gF (1 ⊗ₜ[F] x)) = conjugate q F a (vectors q F (1 ⊗ₜ[F] x)) ↔
        e a.val * ι q x = ι q (g.val x) * e a.val := by
      change vectors q F (1 ⊗ₜ[F] g.val x) = conjugate q F a (vectors q F (1 ⊗ₜ[F] x)) ↔ _
      rw [← e.injective.eq_iff, hev, conjugate, map_mul, map_mul, hev]
      have hcancel : e a⁻¹.val * e a.val = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      constructor
      · intro h
        rw [h, mul_assoc, hcancel, mul_one]
      · intro h
        rw [h, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
    constructor
    · exact fun h x => (he x).mp (h _)
    · intro h z
      obtain ⟨x, rfl⟩ := (TensorProduct.lid F V).symm.surjective z
      exact (he x).mpr (h x)
  constructor
  · rintro ⟨a, hs, hg⟩
    exact ⟨Units.map e.toMonoidHom a, (heven _).mp hs.1, (hnorm _).mp hs.2.1, (haction a).mp hg⟩
  · rintro ⟨b, hb, hn, hg⟩
    let a := Units.map e.symm.toMonoidHom b
    have hab : e a.val = b.val := e.apply_symm_apply _
    have hact : IsVectorAction q F a gF := (haction a).mpr (by simpa only [hab] using hg)
    refine ⟨a, ⟨(heven _).mpr (hab.symm ▸ hb), (hnorm _).mpr (hab.symm ▸ hn), ?_, ?_⟩, hact⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨gF x, hact x⟩
    · rintro _ ⟨x, rfl⟩
      refine ⟨gF.symm x, ?_⟩
      rw [← conjugate_inverse q F a⁻¹ (vectors q F (gF.symm x)), inv_inv, ← hact,
        LinearEquiv.apply_symm_apply]

private theorem reflectionWord_lift [FiniteDimensional F V]
    (hq : LinearMap.ker q.polarBilin = ⊥) (g : specialOrthogonal q)
    (l : List (ReflectionVector q)) (hl : Even l.length)
    (hdl : ∀ x, g.val x = reflectionWord q l x) :
    QuotientGroup.mk' (Subgroup.square Fˣ) (reflectionNorm q l) = 1 ↔ HasSpinLift q g := by
  let a := cliffordWord q l
  have ha : a.val ∈ evenOdd q 0 := cliffordWord_even q l hl
  have hact (x) : a.val * ι q x = ι q (g.val x) * a.val := by
    change (cliffordWord q l).val * ι q x = ι q (g.val x) * (cliffordWord q l).val
    have ha' : involute (cliffordWord q l).val = (cliffordWord q l).val := involute_eq_of_mem_even ha
    simpa only [← hdl, ha'] using cliffordWord_action q l x
  have hn : reverse a.val * a.val = algebraMap F _ (reflectionNorm q l).val :=
    cliffordWord_norm q l
  rw [hasSpinLift_iff_intrinsic q g]
  constructor
  · intro h
    obtain ⟨r, hr⟩ := (Subgroup.mem_square (G := Fˣ)).mp ((QuotientGroup.eq_one_iff (reflectionNorm q l)).mp h)
    let b := a * Units.map (algebraMap F (CliffordAlgebra q)).toMonoidHom r⁻¹
    have hb : b.val = a.val * algebraMap F _ r⁻¹.val := rfl
    refine ⟨b, ?_, ?_, ?_⟩
    · rw [hb, ← Algebra.commutes, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ ha
    · rw [hb, reverse_norm_scaled, hn, ← map_mul, ← Units.val_mul, ← Units.val_mul, hr]
      simp [mul_assoc]
    · intro x
      rw [hb, mul_assoc, Algebra.commutes, ← mul_assoc, hact, mul_assoc]
  · rintro ⟨b, hb, hbn, hba⟩
    obtain ⟨r, hr⟩ := even_implementer_ratio q hq g.val a b ha hb hact hba
    rw [hr, reverse_norm_scaled, hn, ← map_mul, ← map_one (algebraMap F (CliffordAlgebra q))] at hbn
    have hh := scalar_injective q (Module.finBasis F V) hbn
    have he : reflectionNorm q l * (r * r) = 1 := Units.ext hh
    exact (QuotientGroup.eq_one_iff (N := Subgroup.square Fˣ) (reflectionNorm q l)).mpr ⟨r⁻¹, by
      calc
        reflectionNorm q l = (r * r)⁻¹ := eq_inv_of_mul_eq_one_left he
        _ = r⁻¹ * r⁻¹ := mul_inv_rev _ _⟩

end CliffordWords

theorem spinor_norm : SpinorNorm.{u,v} := by
  classical
  intro F _ _ V _ _ _ q hq
  let word (g : specialOrthogonal q) := Classical.choose (exists_even_word q hq g)
  have hw (g) := Classical.choose_spec (exists_even_word q hq g)
  let ν (g : specialOrthogonal q) := QuotientGroup.mk' (Subgroup.square Fˣ) (reflectionNorm q (word g))
  have hagree (g : specialOrthogonal q) (l : List (ReflectionVector q))
      (hl : Even l.length) (hact : ∀ x, g.val x = reflectionWord q l x) :
      ν g = QuotientGroup.mk' (Subgroup.square Fˣ) (reflectionNorm q l) :=
    reflectionWord_same_class q hq g (word g) l (hw g).1 hl (hw g).2 hact
  let f : specialOrthogonal q →* SquareClasses F :=
    { toFun := ν
      map_one' := by simpa [reflectionNorm] using hagree 1 [] (by simp) (fun _ => rfl)
      map_mul' := fun g h => by
        rw [hagree (g * h) (word g ++ word h)
          (by simpa only [List.length_append] using (hw g).1.add (hw h).1) (fun x => by
            change g.val (h.val x) = _
            rw [reflectionWord_append, ← (hw h).2, ← (hw g).2]), reflectionNorm_append, map_mul] }
  refine ⟨f, exists_even_word q hq, hagree, ?_⟩
  intro g
  exact reflectionWord_lift q hq g (word g) (hw g).1 (hw g).2

section IntegralReflection

variable {R : Type u} [CommRing R] {L : Type v} [AddCommGroup L] [Module R L]

private theorem integral_norm_add (q : QuadraticForm R L) (x y : L) :
    q (x + y) = q x + q y + q.polarBilin x y := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  ring

private theorem integral_norm_sub (q : QuadraticForm R L) (x y : L) :
    q (x - y) = q x + q y - q.polarBilin x y := by
  rw [sub_eq_add_neg, integral_norm_add, q.map_neg, map_neg, sub_eq_add_neg]

private theorem integral_polar_self (q : QuadraticForm R L) (x : L) :
    q.polarBilin x x = 2 * q x := by
  simpa only [QuadraticMap.polarBilin_apply_apply, two_smul, two_mul] using
    QuadraticMap.polar_self q x

private theorem integral_polar_symm (q : QuadraticForm R L) (x y : L) :
    q.polarBilin x y = q.polarBilin y x := QuadraticMap.polar_comm q x y

private abbrev UnitVector (q : QuadraticForm R L) := {w : L // IsUnit (q w)}

private def integralReflect (q : QuadraticForm R L) (w : UnitVector q) : L →ₗ[R] L :=
  LinearMap.id - ((w.prop.unit⁻¹.val : R) • q.polarBilin w.val).smulRight w.val

private theorem integralReflect_apply (q : QuadraticForm R L) (w : UnitVector q) (x : L) :
    integralReflect q w x = x - (w.prop.unit⁻¹.val * q.polarBilin w.val x) • w.val := by
  simp [integralReflect]

private theorem integralReflect_norm (q : QuadraticForm R L) (w : UnitVector q) (x : L) :
    q (integralReflect q w x) = q x := by
  have h : w.prop.unit⁻¹.val * q w.val = 1 := by
    exact (congrArg (fun z : R => w.prop.unit⁻¹.val * z) w.prop.unit_spec).symm.trans (Units.inv_mul _)
  rw [integralReflect_apply, integral_norm_sub, q.map_smul, map_smul, integral_polar_symm q x w.val]
  simp only [smul_eq_mul]
  linear_combination (w.prop.unit⁻¹.val * q.polarBilin w.val x ^ 2) * h

private theorem integralReflect_twice (q : QuadraticForm R L) (w : UnitVector q) (x : L) :
    integralReflect q w (integralReflect q w x) = x := by
  have h : w.prop.unit⁻¹.val * q w.val = 1 := by
    exact (congrArg (fun z : R => w.prop.unit⁻¹.val * z) w.prop.unit_spec).symm.trans (Units.inv_mul _)
  let c := w.prop.unit⁻¹.val
  let p := q.polarBilin w.val x
  have hh : c * (p - c * p * (2 * q w.val)) = -(c * p) := by
    linear_combination (-2 * c * p) * h
  rw [integralReflect_apply q w (integralReflect q w x), integralReflect_apply q w x]
  simp only [map_sub, map_smul, smul_eq_mul, integral_polar_self]
  change x - (c * p) • w.val - (c * (p - c * p * (2 * q w.val))) • w.val = x
  rw [hh, neg_smul, sub_neg_eq_add, sub_add_cancel]

private theorem integralReflect_difference (q : QuadraticForm R L) (x y : L)
    (hxy : q x = q y) (h : IsUnit (q (x - y))) :
    integralReflect q ⟨x - y, h⟩ x = y := by
  have he : q.polarBilin (x - y) x = q (x - y) := by
    rw [map_sub, LinearMap.sub_apply, integral_polar_self, integral_polar_symm q y x,
      integral_norm_sub, hxy]
    ring
  rw [integralReflect_apply]
  change x - (h.unit⁻¹.val * q.polarBilin (x - y) x) • (x - y) = y
  have hi : h.unit⁻¹.val * q (x - y) = 1 :=
    (congrArg (fun z : R => h.unit⁻¹.val * z) h.unit_spec).symm.trans (Units.inv_mul _)
  rw [he, hi, one_smul, sub_sub_cancel]

private def integralWord (q : QuadraticForm R L) (l : List (UnitVector q)) : L →ₗ[R] L :=
  l.foldr (fun w g => (integralReflect q w).comp g) LinearMap.id

private theorem integralWord_append (q : QuadraticForm R L) (l m : List (UnitVector q)) (x : L) :
    integralWord q (l ++ m) x = integralWord q l (integralWord q m x) := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change integralReflect q w (integralWord q (l ++ m) x) =
      integralReflect q w (integralWord q l (integralWord q m x))
    rw [ih]

private theorem integralWord_reverse (q : QuadraticForm R L) (l : List (UnitVector q)) (x : L) :
    integralWord q l.reverse (integralWord q l x) = x := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    rw [List.reverse_cons, integralWord_append]
    change integralWord q l.reverse (integralReflect q w (integralReflect q w (integralWord q l x))) = x
    rw [integralReflect_twice, ih]

private theorem integralWord_norm (q : QuadraticForm R L) (l : List (UnitVector q)) (x : L) :
    q (integralWord q l x) = q x := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change q (integralReflect q w (integralWord q l x)) = q x
    rw [integralReflect_norm, ih]

private theorem integral_polar_preserve (q : QuadraticForm R L) (g : L →ₗ[R] L)
    (hg : ∀ x, q (g x) = q x) (x y : L) :
    q.polarBilin (g x) (g y) = q.polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hg]

private theorem integral_unit_vector [IsLocalRing R] [Module.Free R L] [Module.Finite R L]
    (q : QuadraticForm R L) (hQ : Function.Surjective q.polarBilin)
    (hL : Module.finrank R L ≠ 0) : ∃ v : L, IsUnit (q v) := by
  classical
  let b := Module.finBasis R L
  let i : Fin (Module.finrank R L) := ⟨0, Nat.pos_of_ne_zero hL⟩
  obtain ⟨w, hw⟩ := hQ (b.coord i)
  have hB : q.polarBilin w (b i) = 1 := by rw [hw, Module.Basis.coord_apply, b.repr_self]; simp
  by_cases h₁ : IsUnit (q w)
  · exact ⟨w, h₁⟩
  by_cases h₂ : IsUnit (q (b i))
  · exact ⟨b i, h₂⟩
  refine ⟨w + b i, (IsLocalRing.residue_ne_zero_iff_isUnit _).mp ?_⟩
  rw [integral_norm_add, hB, map_add, map_add, map_one]
  rw [not_ne_iff.mp (mt (IsLocalRing.residue_ne_zero_iff_isUnit _).mp h₁),
    not_ne_iff.mp (mt (IsLocalRing.residue_ne_zero_iff_isUnit _).mp h₂), zero_add, zero_add]
  exact one_ne_zero

private theorem integral_align [IsLocalRing R] (h₂ : IsUnit (2 : R)) (q : QuadraticForm R L)
    (x v : L) (h : q x = q v) (hv : IsUnit (q v)) :
    ∃ l : List (UnitVector q), integralWord q l x = v := by
  have hs : q (x - v) + q (x + v) = (2 : R) * 2 * q v := by
    rw [integral_norm_sub, integral_norm_add, h]
    ring
  have hu : IsUnit (q (x - v) + q (x + v)) := hs ▸ (h₂.mul h₂).mul hv
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with hd | hs
  · exact ⟨[⟨x - v, hd⟩], integralReflect_difference q x v h hd⟩
  · let w : UnitVector q := ⟨v, hv⟩
    have hv' : integralReflect q w (-v) = v := by
      have he : hv.unit⁻¹.val * q v = 1 := by exact (congrArg (fun z : R => hv.unit⁻¹.val * z) hv.unit_spec).symm.trans (Units.inv_mul _)
      rw [integralReflect_apply, map_neg, integral_polar_self]
      change -v - (hv.unit⁻¹.val * -(2 * q v)) • v = v
      have he' : hv.unit⁻¹.val * -(2 * q v) = -2 := by linear_combination -2 * he
      rw [he', neg_smul, sub_neg_eq_add, two_smul, ← add_assoc, neg_add_cancel, zero_add]
    have hs' : IsUnit (q (x - -v)) := by simpa using hs
    refine ⟨[w, ⟨x - -v, hs'⟩], ?_⟩
    change integralReflect q w (integralReflect q ⟨x - -v, hs'⟩ x) = v
    rw [integralReflect_difference q x (-v) (by simpa using h), hv']


private theorem integralWord_mem_fixed (q : QuadraticForm R L) (l : List (UnitVector q))
    (x : L) (h : ∀ w ∈ l, q.polarBilin w.val x = 0) : integralWord q l x = x := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change integralReflect q w (integralWord q l x) = x
    rw [ih fun u hu => h u (List.mem_cons_of_mem _ hu), integralReflect_apply]
    simp [h w (by simp)]

private def unitVectorInclusion (q : QuadraticForm R L) (N : Submodule R L) :
    UnitVector (q.comp N.subtype) → UnitVector q :=
  fun w => ⟨w.val.val, w.prop⟩

private theorem integralWord_restrict (q : QuadraticForm R L) (N : Submodule R L)
    (l : List (UnitVector (q.comp N.subtype))) (x : N) :
    (integralWord (q.comp N.subtype) l x).val = integralWord q (l.map (unitVectorInclusion q N)) x.val := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change (integralReflect (q.comp N.subtype) w (integralWord (q.comp N.subtype) l x)).val =
      integralReflect q (unitVectorInclusion q N w) (integralWord q (l.map (unitVectorInclusion q N)) x.val)
    rw [integralReflect_apply, integralReflect_apply, ← ih]
    rfl

private def linePerpEquiv (B : L →ₗ[R] R) (x : L) (hx : B x = 1) :
    (R × LinearMap.ker B) ≃ₗ[R] L where
  toFun p := p.1 • x + p.2.val
  invFun y := ⟨B y, ⟨y - B y • x, by rw [LinearMap.mem_ker, map_sub, map_smul, hx, smul_eq_mul,
    mul_one, sub_self]⟩⟩
  left_inv p := by
    have h : B (p.1 • x + p.2.val) = p.1 := by
      rw [map_add, map_smul, hx, LinearMap.mem_ker.mp p.2.prop, smul_eq_mul, mul_one, add_zero]
    apply Prod.ext h
    apply Subtype.ext
    change p.1 • x + p.2.val - (B (p.1 • x + p.2.val)) • x = p.2.val
    rw [h, add_sub_cancel_left]
  right_inv y := by simp
  map_add' p p' := by simp [add_smul]; abel
  map_smul' c p := by simp [smul_add, smul_smul]

private theorem integral_generate {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsPrincipalIdealRing R] (h₂ : IsUnit (2 : R)) :
    ∀ n : ℕ, ∀ {L : Type v} [AddCommGroup L] [Module R L] [Module.Free R L] [Module.Finite R L],
      Module.finrank R L = n → ∀ (q : QuadraticForm R L), Function.Bijective q.polarBilin →
        ∀ g : L →ₗ[R] L, (∀ x, q (g x) = q x) →
          ∃ l : List (UnitVector q), ∀ x, g x = integralWord q l x := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n IH =>
    intro L _ _ _ _ hdim q hq g hg
    by_cases h0 : Module.finrank R L = 0
    · have := (Module.finrank_eq_zero_iff_of_free R L).mp h0
      exact ⟨[], fun _ => Subsingleton.elim _ _⟩
    obtain ⟨v, hv⟩ := integral_unit_vector q hq.2 h0
    obtain ⟨l, hfix⟩ := integral_align h₂ q (g v) v (hg v) hv
    let j := (integralWord q l).comp g
    have hj (x : L) : q (j x) = q x := (integralWord_norm q l (g x)).trans (hg x)
    have hjv : j v = v := hfix
    have hu : IsUnit (q.polarBilin v v) := (integral_polar_self q v).symm ▸ h₂.mul hv
    let c : R := hu.unit⁻¹.val
    have hc : c * q.polarBilin v v = 1 :=
      (congrArg (fun z : R => c * z) hu.unit_spec).symm.trans (Units.inv_mul _)
    let B := c • q.polarBilin v
    have hB : B v = 1 := hc
    let N := LinearMap.ker B
    let e := linePerpEquiv B v hB
    have orthogonal (x : N) : q.polarBilin v x.val = 0 := by
      have hx := LinearMap.mem_ker.mp x.prop
      change c * q.polarBilin v x.val = 0 at hx
      exact (mul_eq_zero.mp hx).resolve_left hu.unit⁻¹.ne_zero
    have hN (x : L) (hx : q.polarBilin v x = 0) : x ∈ N := by
      change c * q.polarBilin v x = 0
      rw [hx, mul_zero]
    let Q := q.comp N.subtype
    have hQ : Function.Bijective Q.polarBilin := by
      constructor
      · intro x y hxy
        apply Subtype.ext
        apply hq.1
        ext z
        obtain ⟨⟨a, w⟩, rfl⟩ := e.surjective z
        change q.polarBilin x.val (a • v + w.val) = q.polarBilin y.val (a • v + w.val)
        have hw : q.polarBilin x.val w.val = q.polarBilin y.val w.val :=
          congrArg (fun f : N →ₗ[R] R => f w) hxy
        rw [map_add, map_add, map_smul, map_smul, integral_polar_symm q x.val v,
          integral_polar_symm q y.val v, orthogonal x, orthogonal y, hw]
      · intro f
        let p : L →ₗ[R] N := (LinearMap.snd R R N).comp e.symm.toLinearMap
        have hproj (w : N) : p w.val = w := by
          change (e.symm w.val).2 = w
          have H : w.val = e (0, w) := by change _ = (0 : R) • v + w.val; simp
          rw [H, LinearEquiv.symm_apply_apply]
        have hprojv : p v = 0 := by
          change (e.symm v).2 = 0
          have H : v = e (1, 0) := by change _ = (1 : R) • v + 0; simp
          rw [H, LinearEquiv.symm_apply_apply]
        obtain ⟨z, hz⟩ := hq.2 (f.comp p)
        have hzv : q.polarBilin v z = 0 := by
          rw [integral_polar_symm q v z, hz, LinearMap.comp_apply, hprojv, map_zero]
        refine ⟨⟨z, hN z hzv⟩, ?_⟩
        ext w
        change q.polarBilin z w.val = f w
        rw [hz, LinearMap.comp_apply, hproj]
    have hjN (x : N) : j x.val ∈ N := by
      apply hN
      calc
        q.polarBilin v (j x.val) = q.polarBilin (j v) (j x.val) := by rw [hjv]
        _ = q.polarBilin v x.val := integral_polar_preserve q j hj v x.val
        _ = 0 := orthogonal x
    let jN : N →ₗ[R] N := (j.comp N.subtype).codRestrict N hjN
    have hdimN : Module.finrank R N < n := by
      have hh := e.finrank_eq
      rw [Module.finrank_prod, Module.finrank_self, hdim] at hh
      change 1 + Module.finrank R N = n at hh
      omega
    obtain ⟨m, hm⟩ := IH _ hdimN rfl Q hQ jN (fun x => hj x.val)
    have hjword (x : L) : j x = integralWord q (m.map (unitVectorInclusion q N)) x := by
      obtain ⟨⟨a, y⟩, rfl⟩ := e.surjective x
      change j (a • v + y.val) = integralWord q (m.map (unitVectorInclusion q N)) (a • v + y.val)
      have hvword : integralWord q (m.map (unitVectorInclusion q N)) v = v := by
        apply integralWord_mem_fixed
        intro w hw
        obtain ⟨w', _, rfl⟩ := List.mem_map.mp hw
        rw [integral_polar_symm]
        exact orthogonal w'.val
      have hyword : j y.val = integralWord q (m.map (unitVectorInclusion q N)) y.val :=
        (congrArg Subtype.val (hm y)).trans (integralWord_restrict q N m y)
      simp only [map_add, map_smul, hjv, hvword, hyword]
    refine ⟨l.reverse ++ m.map (unitVectorInclusion q N), fun x => ?_⟩
    rw [integralWord_append, ← hjword]
    exact (integralWord_reverse q l (g x)).symm

end IntegralReflection


section IntegralBaseChange

variable {R F : Type u} [CommRing R] [Field F] [Algebra R F]
  {L : Type v} [AddCommGroup L] [Module R L]
  [Invertible (2 : R)] [Invertible (2 : F)]

omit [Invertible (2 : F)] in
private theorem integral_norm_baseChange (q : QuadraticForm R L) (x : L) :
    (q.baseChange F) (1 ⊗ₜ[R] x) = algebraMap R F (q x) := by
  simp [Algebra.smul_def]

private def unitVectorBaseChange (q : QuadraticForm R L) (w : UnitVector q) :
    ReflectionVector (q.baseChange F) :=
  ⟨1 ⊗ₜ[R] w.val, by
    rw [integral_norm_baseChange]
    exact (w.prop.map (algebraMap R F)).ne_zero⟩

private theorem integralReflect_baseChange (q : QuadraticForm R L) (w : UnitVector q) (x : L) :
    (1 ⊗ₜ[R] integralReflect q w x : F ⊗[R] L) =
      reflection (q.baseChange F) (unitVectorBaseChange q w).val (1 ⊗ₜ[R] x) := by
  have hp : (q.baseChange F).polarBilin (1 ⊗ₜ[R] w.val) (1 ⊗ₜ[R] x) =
      algebraMap R F (q.polarBilin w.val x) := by
    rw [QuadraticForm.polarBilin_baseChange]
    simp [LinearMap.BilinForm.baseChange, Algebra.smul_def]
  have hn := (w.prop.map (algebraMap R F)).ne_zero
  have hi : w.prop.unit⁻¹.val * q w.val = 1 :=
    (congrArg (fun z : R => w.prop.unit⁻¹.val * z) w.prop.unit_spec).symm.trans (Units.inv_mul _)
  have he : algebraMap R F (w.prop.unit⁻¹.val * q.polarBilin w.val x) =
      algebraMap R F (q.polarBilin w.val x) / algebraMap R F (q w.val) := by
    apply (eq_div_iff hn).mpr
    rw [← map_mul, mul_right_comm, hi, one_mul]
  rw [integralReflect_apply, reflection]
  change _ = (1 ⊗ₜ[R] x : F ⊗[R] L) -
    (((q.baseChange F).polarBilin (1 ⊗ₜ[R] w.val) (1 ⊗ₜ[R] x)) /
      (q.baseChange F) (1 ⊗ₜ[R] w.val)) • (1 ⊗ₜ[R] w.val)
  rw [hp, integral_norm_baseChange, TensorProduct.tmul_sub, ← he,
    algebraMap_smul F, TensorProduct.tmul_smul]

private theorem integralWord_baseChange (q : QuadraticForm R L) (l : List (UnitVector q)) (x : L) :
    (1 ⊗ₜ[R] integralWord q l x : F ⊗[R] L) =
      reflectionWord (q.baseChange F) (l.map (unitVectorBaseChange q)) (1 ⊗ₜ[R] x) := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change (1 ⊗ₜ[R] integralReflect q w (integralWord q l x) : F ⊗[R] L) =
      reflection (q.baseChange F) (unitVectorBaseChange q w).val
        (reflectionWord (q.baseChange F) (l.map (unitVectorBaseChange q)) (1 ⊗ₜ[R] x))
    rw [integralReflect_baseChange, ih]

omit [Invertible (2 : F)] in
private theorem integralWord_norm_baseChange (q : QuadraticForm R L) (l : List (UnitVector q)) :
    reflectionNorm (q.baseChange F) (l.map (unitVectorBaseChange q)) =
      Units.map (algebraMap R F).toMonoidHom ((l.map fun w => w.prop.unit).prod) := by
  induction l with
  | nil => simp [reflectionNorm]
  | cons w l ih =>
    change Units.mk0 (q.baseChange F (unitVectorBaseChange q w).val) (unitVectorBaseChange q w).prop *
        reflectionNorm (q.baseChange F) (l.map (unitVectorBaseChange q)) =
      Units.map (algebraMap R F).toMonoidHom (w.prop.unit * (l.map fun w => w.prop.unit).prod)
    rw [ih, map_mul]
    congr 1
    apply Units.ext
    change (q.baseChange F) (1 ⊗ₜ[R] w.val) = algebraMap R F w.prop.unit.val
    rw [integral_norm_baseChange, w.prop.unit_spec]

private theorem unimodular_baseChange [Module.Free R L] [Module.Finite R L]
    (q : QuadraticForm R L) (hq : Function.Bijective q.polarBilin) :
    LinearMap.ker (q.baseChange F).polarBilin = ⊥ := by
  let b := TensorProduct.isBaseChange R L F
  let e := (LinearEquiv.ofBijective q.polarBilin hq).baseChange R F L (Module.Dual R L)
  let f := e.trans b.toDualBaseChange
  have heq : f.toLinearMap = (q.baseChange F).polarBilin := by
    apply b.algHom_ext
    intro x
    apply b.algHom_ext
    intro y
    change (b.toDualBaseChange (1 ⊗ₜ[R] q.polarBilin x)) (1 ⊗ₜ[R] y) =
      (q.baseChange F).polarBilin (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)
    rw [show (b.toDualBaseChange (1 ⊗ₜ[R] q.polarBilin x)) (1 ⊗ₜ[R] y) =
      1 * algebraMap R F (q.polarBilin x y) from b.toDualBaseChange_tmul 1 (q.polarBilin x) y,
      one_mul, QuadraticForm.polarBilin_baseChange, LinearMap.BilinForm.baseChange_tmul,
      one_mul, Algebra.smul_def, mul_one]
  rw [← heq, LinearMap.ker_eq_bot]
  exact f.injective

private theorem integral_isometry_baseChange [Module.Free R L] [Module.Finite R L]
    (q : QuadraticForm R L) (g : specialOrthogonal q) (h₂ : IsUnit (2 : F)) :
    ∃ gF : specialOrthogonal (q.baseChange F),
      ∀ x : L, gF.val (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] g.val x := by
  let e := g.val.baseChange R F L L
  let Q := q.baseChange F
  have hq : Q.comp e.toLinearMap = Q := by
    apply QuadraticMap.polarBilin_injective h₂
    rw [QuadraticMap.polarBilin_comp, QuadraticForm.polarBilin_baseChange]
    let b := TensorProduct.isBaseChange R L F
    apply b.algHom_ext
    intro x
    apply b.algHom_ext
    intro y
    change (LinearMap.BilinForm.baseChange F q.polarBilin) (1 ⊗ₜ[R] g.val x) (1 ⊗ₜ[R] g.val y) =
      (LinearMap.BilinForm.baseChange F q.polarBilin) (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)
    have he : q.polarBilin (g.val x) (g.val y) = q.polarBilin x y :=
      integral_polar_preserve q g.val.toLinearMap g.prop.1 x y
    rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, he]
  have hd : LinearEquiv.det e = 1 := by
    rw [LinearEquiv.det_baseChange, g.prop.2, map_one]
  exact ⟨⟨e, fun x => congrArg (fun q' : QuadraticForm F (F ⊗[R] L) => q' x) hq, hd⟩,
    fun _ => rfl⟩

end IntegralBaseChange

open ValuativeRel in
theorem integral_unit_class : IntegralUnitClass.{u,v} := by
  classical
  intro F _ _ _ _ _
  let R := LinearAlgebraicGroups.Arithmetic.LocalDivisionRamification.Integers F
  change ∀ h₂ : IsUnit (2 : R), _
  intro h₂
  let : Invertible (2 : R) := h₂.invertible
  have h₂F : IsUnit (2 : F) := isUnit_iff_ne_zero.mpr (by norm_num)
  let : Invertible (2 : F) := h₂F.invertible
  let : IsDiscreteValuationRing R :=
    IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation F
  intro L _ _ _ _ q hq g
  obtain ⟨gF, hgF⟩ := integral_isometry_baseChange q g h₂F
  refine ⟨gF, hgF, spinor_norm (q.baseChange F) (unimodular_baseChange q hq), ?_⟩
  intro ν hν
  obtain ⟨l, hl⟩ := integral_generate h₂ (Module.finrank R L) rfl q hq g.val.toLinearMap g.prop.1
  let Q := q.baseChange F
  let m : List (ReflectionVector Q) := l.map (unitVectorBaseChange q)
  have ht (x : L) : gF.val (1 ⊗ₜ[R] x) = reflectionWord Q m (1 ⊗ₜ[R] x) := by
    rw [hgF, show g.val x = integralWord q l x from hl x]
    exact integralWord_baseChange q l x
  have hmap : gF.val.toLinearMap = reflectionWordLinear Q m := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    have he : a ⊗ₜ[R] x = a • (1 ⊗ₜ[R] x : F ⊗[R] L) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [he, map_smul, map_smul, reflectionWordLinear_apply, ← ht]
    rfl
  have hm (x : F ⊗[R] L) : gF.val x = reflectionWord Q m x := by
    rw [← reflectionWordLinear_apply, ← hmap]
    rfl
  have hpar : Even m.length := reflectionWord_even Q gF m hm
  refine ⟨(l.map fun w => w.prop.unit).prod, ?_⟩
  rw [hν.2.1 gF m hpar hm, integralWord_norm_baseChange]

end

end LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy
