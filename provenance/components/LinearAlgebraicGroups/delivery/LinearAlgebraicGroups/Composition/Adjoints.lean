import LinearAlgebraicGroups.Composition.Algebras
import LinearAlgebraicGroups.Composition.AlternativeIdentities
import Specs.LinearAlgebraicGroups.Composition.Adjoints
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Tactic.LinearCombination

namespace LinearAlgebraicGroups.Composition

open scoped TensorProduct

universe u v w

variable {R : Type u} {A : Type v}

/-- The scalar trace of a composition norm. -/
abbrev compositionTrace := @AdjointSpecification.trace

/-- The standard linear conjugation of a composition algebra. -/
abbrev conjugate := @AdjointSpecification.conjugate

/-- For a norm represented by a unit, rescale the conjugate by its inverse. -/
abbrev inverseByNorm := @AdjointSpecification.inverseByNorm

abbrev NormLaws := @AdjointSpecification.NormLaws

theorem IsFieldCompositionNorm.toNormLaws [Field R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A}
    (h : IsFieldCompositionNorm n) : NormLaws n :=
  ⟨field_norm_one h, h.multiplicative, h.nondegenerate⟩

section Trace

variable [CommRing R] [NonAssocRing A] [Module R A]
variable {n : QuadraticForm R A}

theorem compositionTrace_apply (n : QuadraticForm R A) (x : A) :
    compositionTrace n x = n.polarBilin x 1 := rfl

theorem conjugate_apply (n : QuadraticForm R A) (x : A) :
    conjugate n x = compositionTrace n x • (1 : A) - x := rfl

theorem compositionTrace_one (h : NormLaws n) : compositionTrace n 1 = 2 := by
  rw [compositionTrace_apply, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, h.map_one]
  simp

theorem compositionTrace_scalar (h : NormLaws n) (r : R) :
    compositionTrace n (r • (1 : A)) = 2 * r := by
  rw [map_smul, compositionTrace_one h, smul_eq_mul, mul_comm]

theorem norm_scalar (h : NormLaws n) (r : R) : n (r • (1 : A)) = r ^ 2 := by
  rw [n.map_smul, h.map_one, smul_eq_mul, mul_one, pow_two]

theorem compositionTrace_conjugate (h : NormLaws n) (x : A) :
    compositionTrace n (conjugate n x) = compositionTrace n x := by
  rw [conjugate_apply, map_sub, compositionTrace_scalar h]
  ring

theorem conjugate_one (h : NormLaws n) : conjugate n 1 = 1 := by
  rw [conjugate_apply, compositionTrace_one h, two_smul, add_sub_cancel_right]

theorem conjugate_involutive (h : NormLaws n) : Function.Involutive (conjugate n) := by
  intro x
  rw [conjugate_apply, compositionTrace_conjugate h, conjugate_apply]
  abel

private theorem norm_add (n : QuadraticForm R A) (x y : A) :
    n (x + y) = n x + n y + n.polarBilin x y :=
  QuadraticMap.map_add n x y

theorem norm_conjugate (h : NormLaws n) (x : A) : n (conjugate n x) = n x := by
  rw [conjugate_apply, sub_eq_add_neg, norm_add n, norm_scalar h,
    n.map_neg, map_neg, LinearMap.map_smul₂, smul_eq_mul,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm n (1 : A) x,
    ← QuadraticMap.polarBilin_apply_apply, ← compositionTrace_apply]
  ring

end Trace

section Ring

variable [CommRing R] [NonAssocRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable {n : QuadraticForm R A}

theorem IsOctonionNorm.toNormLaws (h : IsOctonionNorm n) : NormLaws n :=
  ⟨octonion_norm_one h, octonion_norm_mul h, h.perfect.nondegenerate⟩

theorem left_mul_adjoint (h : NormLaws n) (x : A) :
    LinearMap.IsAdjointPair n.polarBilin n.polarBilin
      (LinearMap.mul R A x) (LinearMap.mul R A (conjugate n x)) := by
  intro y z
  change n.polarBilin (x * y) z = n.polarBilin y (conjugate n x * z)
  have H := left_norm_similarity h.map_mul (x + 1) y z
  rw [add_mul, add_mul, one_mul, one_mul, LinearMap.map_add₂, map_add, map_add,
    left_norm_similarity h.map_mul, norm_add n, h.map_one, ← compositionTrace_apply] at H
  rw [conjugate_apply, sub_mul, smul_mul_assoc, one_mul, map_sub, map_smul, smul_eq_mul]
  linear_combination H

theorem right_mul_adjoint (h : NormLaws n) (x : A) :
    LinearMap.IsAdjointPair n.polarBilin n.polarBilin
      ((LinearMap.mul R A).flip x) ((LinearMap.mul R A).flip (conjugate n x)) := by
  intro y z
  change n.polarBilin (y * x) z = n.polarBilin y (z * conjugate n x)
  have H := right_norm_similarity h.map_mul (x + 1) y z
  rw [mul_add, mul_add, mul_one, mul_one, LinearMap.map_add₂, map_add, map_add,
    right_norm_similarity h.map_mul, norm_add n, h.map_one, ← compositionTrace_apply] at H
  rw [conjugate_apply, mul_sub, mul_smul_comm, mul_one, map_sub, map_smul, smul_eq_mul]
  linear_combination H

private theorem conjugate_left_mul (h : NormLaws n) (x y : A) :
    conjugate n x * (x * y) = n x • y := by
  apply LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp h.nondegenerate.1)
  apply LinearMap.ext
  intro z
  change n.polarBilin (conjugate n x * (x * y)) z = n.polarBilin (n x • y) z
  have H := left_mul_adjoint h (conjugate n x) (x * y) z
  change n.polarBilin (conjugate n x * (x * y)) z =
    n.polarBilin (x * y) (conjugate n (conjugate n x) * z) at H
  rw [H, conjugate_involutive h x, left_norm_similarity h.map_mul, LinearMap.map_smul₂, smul_eq_mul]

theorem conjugate_left_products (h : NormLaws n) (x y : A) :
    (conjugate n x * (x * y) = n x • y) ∧ (x * (conjugate n x * y) = n x • y) := by
  refine ⟨conjugate_left_mul h x y, ?_⟩
  simpa only [conjugate_involutive h x, norm_conjugate h x] using
    conjugate_left_mul h (conjugate n x) y

private theorem conjugate_right_mul (h : NormLaws n) (x y : A) :
    (y * x) * conjugate n x = n x • y := by
  apply LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp h.nondegenerate.1)
  apply LinearMap.ext
  intro z
  change n.polarBilin ((y * x) * conjugate n x) z = n.polarBilin (n x • y) z
  have H := right_mul_adjoint h (conjugate n x) (y * x) z
  change n.polarBilin ((y * x) * conjugate n x) z =
    n.polarBilin (y * x) (z * conjugate n (conjugate n x)) at H
  rw [H, conjugate_involutive h x, right_norm_similarity h.map_mul, LinearMap.map_smul₂, smul_eq_mul]

theorem conjugate_right_products (h : NormLaws n) (x y : A) :
    ((y * x) * conjugate n x = n x • y) ∧ ((y * conjugate n x) * x = n x • y) := by
  refine ⟨conjugate_right_mul h x y, ?_⟩
  simpa only [conjugate_involutive h x, norm_conjugate h x] using
    conjugate_right_mul h (conjugate n x) y

theorem mul_conjugate (h : NormLaws n) (x : A) :
    x * conjugate n x = n x • (1 : A) ∧ conjugate n x * x = n x • (1 : A) := by
  simpa only [mul_one, and_comm] using conjugate_left_products h x (1 : A)

theorem composition_quadratic_equation (h : NormLaws n) (x : A) :
    x * x - compositionTrace n x • x + n x • (1 : A) = 0 := by
  rw [← (mul_conjugate h x).1, conjugate_apply, mul_sub, mul_smul_comm, mul_one]
  abel

theorem polar_mul_conjugate (h : NormLaws n) (x y : A) :
    x * conjugate n y + y * conjugate n x = n.polarBilin x y • (1 : A) := by
  have H := (mul_conjugate h (x + y)).1
  rw [map_add, add_mul, mul_add, mul_add, (mul_conjugate h x).1, (mul_conjugate h y).1,
    norm_add n, add_smul, add_smul] at H
  calc
    _ = (n x • (1 : A) + x * conjugate n y + (y * conjugate n x + n y • (1 : A))) -
        (n x • (1 : A) + n y • (1 : A)) := by abel
    _ = _ := by rw [H]; abel

private theorem polar_quadratic_equation (h : NormLaws n) (x y : A) :
    x * y + y * x = compositionTrace n x • y + compositionTrace n y • x -
      n.polarBilin x y • (1 : A) := by
  have H := polar_mul_conjugate h x y
  simp only [conjugate_apply, mul_sub, mul_smul_comm, mul_one] at H
  rw [← H]
  abel

theorem compositionTrace_mul_formula (h : NormLaws n) (x y : A) :
    compositionTrace n (x * y) = compositionTrace n x * compositionTrace n y - n.polarBilin x y := by
  rw [compositionTrace_apply]
  have H := right_mul_adjoint h y x 1
  change n.polarBilin (x * y) 1 = n.polarBilin x (1 * conjugate n y) at H
  rw [H, one_mul, conjugate_apply, map_sub, map_smul, smul_eq_mul, ← compositionTrace_apply, mul_comm]

theorem conjugate_mul (h : NormLaws n) (x y : A) :
    conjugate n (x * y) = conjugate n y * conjugate n x := by
  simp only [conjugate_apply, compositionTrace_mul_formula h, sub_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub, smul_smul, sub_smul]
  have H := polar_quadratic_equation h x y
  rw [mul_comm (compositionTrace n x) (compositionTrace n y)]
  calc
    _ = (compositionTrace n y * compositionTrace n x) • (1 : A) +
        (x * y + y * x) - (compositionTrace n x • y + compositionTrace n y • x) - x * y := by
      rw [H]
      abel
    _ = _ := by abel

theorem compositionTrace_mul_comm (h : NormLaws n) (x y : A) :
    compositionTrace n (x * y) = compositionTrace n (y * x) := by
  rw [compositionTrace_mul_formula h, compositionTrace_mul_formula h, mul_comm,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm n x y]

theorem compositionTrace_mul_conjugate (h : NormLaws n) (x y : A) :
    compositionTrace n (x * conjugate n y) = n.polarBilin x y := by
  have H := right_mul_adjoint h (conjugate n y) x 1
  change n.polarBilin (x * conjugate n y) 1 = n.polarBilin x (1 * conjugate n (conjugate n y)) at H
  simpa only [compositionTrace_apply, one_mul, conjugate_involutive h y] using H

theorem compositionTrace_mul_as_polar (h : NormLaws n) (x y : A) :
    compositionTrace n (x * y) = n.polarBilin x (conjugate n y) := by
  simpa only [conjugate_involutive h y] using compositionTrace_mul_conjugate h x (conjugate n y)

theorem compositionTrace_mul_assoc (h : NormLaws n) (x y z : A) :
    compositionTrace n ((x * y) * z) = compositionTrace n (x * (y * z)) := by
  rw [compositionTrace_mul_as_polar h (x * y) z, compositionTrace_mul_as_polar h x (y * z),
    conjugate_mul h]
  exact right_mul_adjoint h y x (conjugate n z)

theorem compositionTrace_mul_cyclic (h : NormLaws n) (x y z : A) :
    compositionTrace n ((x * y) * z) = compositionTrace n ((y * z) * x) :=
  (compositionTrace_mul_assoc h x y z).trans (compositionTrace_mul_comm h x (y * z))

theorem composition_isAlternative (h : NormLaws n) : IsAlternative A := by
  intro x y
  have left := (conjugate_left_products h x y).1
  have right := (conjugate_right_products h x y).1
  have square : x * x = compositionTrace n x • x - n x • (1 : A) := by
    rw [← (mul_conjugate h x).1, conjugate_apply, mul_sub, mul_smul_comm, mul_one]
    abel
  constructor
  · rw [associator_apply, square, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
    simp only [conjugate_apply, sub_mul, smul_mul_assoc, one_mul] at left
    rw [← left]
    abel
  · rw [associator_apply, square, mul_sub, mul_smul_comm, mul_smul_comm, mul_one]
    simp only [conjugate_apply, mul_sub, mul_smul_comm, mul_one] at right
    rw [← right]
    abel

theorem composition_inverse_operators (h : NormLaws n) (x : A) (a : Rˣ)
    (ha : (a : R) = n x) :
    let L := LinearMap.mul R A
    let P := (LinearMap.mul R A).flip
    let y := inverseByNorm n x a
    (L x).comp (L y) = LinearMap.id ∧ (L y).comp (L x) = LinearMap.id ∧
      (P x).comp (P y) = LinearMap.id ∧ (P y).comp (P x) = LinearMap.id := by
  have scalar_cancel (z : A) : (↑(a⁻¹) : R) • (n x • z) = z := by
    rw [← ha, smul_smul, Units.inv_mul, one_smul]
  refine ⟨LinearMap.ext fun z => ?_, LinearMap.ext fun z => ?_, LinearMap.ext fun z => ?_,
    LinearMap.ext fun z => ?_⟩
  · change x * ((↑(a⁻¹) : R) • conjugate n x * z) = z
    rw [smul_mul_assoc, mul_smul_comm, (conjugate_left_products h x z).2, scalar_cancel]
  · change (↑(a⁻¹) : R) • conjugate n x * (x * z) = z
    rw [smul_mul_assoc, (conjugate_left_products h x z).1, scalar_cancel]
  · change (z * ((↑(a⁻¹) : R) • conjugate n x)) * x = z
    rw [mul_smul_comm, smul_mul_assoc, (conjugate_right_products h x z).2, scalar_cancel]
  · change (z * x) * ((↑(a⁻¹) : R) • conjugate n x) = z
    rw [mul_smul_comm, (conjugate_right_products h x z).1, scalar_cancel]

theorem composition_inverse (h : NormLaws n) (x : A) (a : Rˣ) (ha : (a : R) = n x) :
    x * inverseByNorm n x a = 1 ∧ inverseByNorm n x a * x = 1 := by
  have H := composition_inverse_operators h x a ha
  refine ⟨?_, ?_⟩
  · have H₁ := LinearMap.congr_fun H.1 1
    change x * (inverseByNorm n x a * 1) = 1 at H₁
    simpa only [mul_one] using H₁
  · have H₂ := LinearMap.congr_fun H.2.1 1
    change inverseByNorm n x a * (x * 1) = 1 at H₂
    simpa only [mul_one] using H₂

theorem composition_inverse_iff_norm_unit (h : NormLaws n) (x : A) :
    (∃ y, x * y = 1 ∧ y * x = 1) ↔ IsUnit (n x) := by
  constructor
  · rintro ⟨y, hy, _⟩
    apply IsUnit.of_mul_eq_one (n y)
    rw [← h.map_mul, hy, h.map_one]
  · rintro ⟨a, ha⟩
    exact ⟨inverseByNorm n x a, composition_inverse h x a ha⟩

theorem compositionTrace_baseChange_tmul [Module.Projective R A]
    (S : Type w) [CommRing S] [Algebra R S] (n : QuadraticForm R A) (s : S) (x : A) :
    compositionTrace (normBaseChange S n) (s ⊗ₜ[R] x) = s * algebraMap R S (compositionTrace n x) := by
  rw [compositionTrace_apply, polar_normBaseChange]
  change LinearMap.BilinForm.baseChange S n.polarBilin (s ⊗ₜ[R] x) (1 ⊗ₜ[R] (1 : A)) = _
  rw [LinearMap.BilinForm.baseChange_tmul]
  simp [compositionTrace_apply, Algebra.smul_def, mul_comm]

theorem conjugate_baseChange [Module.Projective R A]
    (S : Type w) [CommRing S] [Algebra R S] (n : QuadraticForm R A) :
    conjugate (normBaseChange S n) = (conjugate n).baseChange S := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s x
  rw [LinearMap.baseChange_tmul, conjugate_apply, conjugate_apply, compositionTrace_baseChange_tmul,
    TensorProduct.tmul_sub]
  change (s * algebraMap R S (compositionTrace n x)) • (1 ⊗ₜ[R] (1 : A)) - _ = _
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [mul_comm s, ← Algebra.smul_def, TensorProduct.smul_tmul]

end Ring

section Field

variable [Field R] [NonAssocRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable {n : QuadraticForm R A}

theorem field_composition_inverse (h : IsFieldCompositionNorm n) (x : A) (hx : n x ≠ 0) :
    let y := (n x)⁻¹ • conjugate n x
    x * y = 1 ∧ y * x = 1 ∧
    Function.LeftInverse (fun z => y * z) (fun z => x * z) ∧
    Function.RightInverse (fun z => y * z) (fun z => x * z) ∧
    Function.LeftInverse (fun z => z * y) (fun z => z * x) ∧
    Function.RightInverse (fun z => z * y) (fun z => z * x) := by
  let a := Units.mk0 (n x) hx
  have H := composition_inverse_operators h.toNormLaws x a rfl
  exact ⟨(composition_inverse h.toNormLaws x a rfl).1,
    (composition_inverse h.toNormLaws x a rfl).2,
    LinearMap.congr_fun H.2.1, LinearMap.congr_fun H.1,
    LinearMap.congr_fun H.2.2.2, LinearMap.congr_fun H.2.2.1⟩

theorem zero_norm_no_inverse (h : IsFieldCompositionNorm n) (x : A) (hx : n x = 0) (y : A) :
    x * y ≠ 1 ∧ y * x ≠ 1 := by
  constructor <;> intro H <;>
    have hn := congrArg n H <;>
    simp only [h.multiplicative, hx, zero_mul, mul_zero, field_norm_one h, zero_ne_one] at hn

theorem division_iff_anisotropic (h : IsFieldCompositionNorm n) :
    (∀ x : A, x ≠ 0 → Function.Bijective (fun y => x * y) ∧ Function.Bijective (fun y => y * x))
      ↔ ¬ IsIsotropic n := by
  constructor
  · rintro div ⟨x, hx, hn⟩
    obtain ⟨y, hy⟩ := (div x hx).1.surjective 1
    exact (zero_norm_no_inverse h x hn y).1 hy
  · intro anisotropic x hx
    have hn : n x ≠ 0 := fun hn => anisotropic ⟨x, hx, hn⟩
    obtain ⟨_, _, l, l', r, r'⟩ := field_composition_inverse h x hn
    exact ⟨⟨l.injective, l'.surjective⟩, ⟨r.injective, r'.surjective⟩⟩

end Field

section Uniqueness

variable {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
variable {n n' : QuadraticForm R A}

private theorem local_norm_unique [IsLocalRing R] [Module.Finite R A] [Module.Projective R A]
    (h : NormLaws n) (h' : NormLaws n') : n = n' ∧ compositionTrace n = compositionTrace n' := by
  classical
  let : Module.Free R A := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis R A
  let : LinearOrder (Module.Free.ChooseBasisIndex R A) :=
    IsWellOrder.linearOrder WellOrderingRel
  -- A bilinear representative of the norm gives a functional splitting the unit line.
  let B := n.toBilin b
  let s := B.flip 1
  have hs : s 1 = 1 := by
    change B 1 1 = 1
    rw [← LinearMap.BilinMap.toQuadraticMap_apply, QuadraticMap.toQuadraticMap_toBilin, h.map_one]
  let l := compositionTrace n - compositionTrace n'
  have diff (x : A) : l x • x = (n x - n' x) • (1 : A) := by
    change (compositionTrace n x - compositionTrace n' x) • x = _
    rw [sub_smul, sub_smul]
    calc
      _ = (x * x - compositionTrace n' x • x + n' x • (1 : A)) -
          (x * x - compositionTrace n x • x + n x • (1 : A)) +
          (n x • (1 : A) - n' x • (1 : A)) := by abel
      _ = _ := by rw [composition_quadratic_equation h, composition_quadratic_equation h']; simp
  -- Projecting the difference equation to this free complement kills its scalar side.
  let K := LinearMap.ker s
  let p : A →ₗ[R] K :=
    LinearMap.codRestrict K (LinearMap.id - s.smulRight 1) (fun x => by
      change s (x - s x • (1 : A)) = 0
      rw [map_sub, map_smul, hs, smul_eq_mul, mul_one, sub_self])
  have hp (x : K) : p x = x := by
    apply Subtype.ext
    change (x : A) - s x • (1 : A) = x
    rw [LinearMap.mem_ker.mp x.property, zero_smul, sub_zero]
  have hp_one : p 1 = 0 := by
    apply Subtype.ext
    change (1 : A) - s 1 • (1 : A) = 0
    rw [hs, one_smul, sub_self]
  let : Module.Finite R K := Module.Finite.of_surjective p fun x => ⟨x, hp x⟩
  let : Module.Projective R K := Module.Projective.of_split K.subtype p (LinearMap.ext hp)
  let : Module.Free R K := Module.free_of_flat_of_isLocalRing
  have vanishes (m : K) : l m • m = 0 := by
    simpa only [map_smul, hp, hp_one, smul_zero] using congrArg p (diff m)
  let c := Module.Free.chooseBasis R K
  have onKernel : l.comp K.subtype = 0 := by
    apply c.ext
    intro i
    have H := congrArg (c.coord i) (vanishes (c i))
    change l (c i : A) = 0
    simpa only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, smul_eq_mul, mul_one, map_zero] using H
  have onUnit : l 1 = 0 := by
    change compositionTrace n 1 - compositionTrace n' 1 = 0
    rw [compositionTrace_one h, compositionTrace_one h', sub_self]
  have onAll (x : A) : l x = 0 := by
    have H := LinearMap.congr_fun onKernel (p x)
    change l (x - s x • (1 : A)) = 0 at H
    simpa only [map_sub, map_smul, onUnit, smul_zero, sub_zero] using H
  constructor
  · ext x
    have H := diff x
    rw [onAll, zero_smul] at H
    have E := congrArg s H.symm
    simpa only [map_smul, hs, smul_eq_mul, mul_one, map_zero, sub_eq_zero] using E
  · exact LinearMap.ext fun x => sub_eq_zero.mp (onAll x)

/-- The norm and trace of an octonion algebra are determined by its product and unit. -/
theorem octonion_norm_unique (h : IsOctonionNorm n) (h' : IsOctonionNorm n') :
    n = n' ∧ compositionTrace n = compositionTrace n' := by
  let := h.finite
  let := h.projective
  have eqNorm : n = n' := by
    ext x
    apply sub_eq_zero.mp
    apply eq_zero_of_localization
    intro m hm
    let : m.IsPrime := hm.isPrime
    let S := Localization.AtPrime m
    have hS := octonion_norm_baseChange h S
    have hS' := octonion_norm_baseChange h' S
    have equiv := (local_norm_unique (IsOctonionNorm.toNormLaws hS) (IsOctonionNorm.toNormLaws hS')).1
    have E := congrArg (fun q : QuadraticForm S (S ⊗[R] A) => q (1 ⊗ₜ[R] x)) equiv
    simpa only [normBaseChange_tmul, one_mul, map_sub, sub_eq_zero] using E
  exact ⟨eqNorm, congrArg compositionTrace eqNorm⟩

private theorem octonion_norm_comp_equiv (h : IsOctonionNorm n) (f : A ≃ₗ[R] A)
    (hMul : ∀ x y, f (x * y) = f x * f y) : IsOctonionNorm (n.comp f.toLinearMap) := by
  let := h.projective
  refine ⟨h.finite, h.projective, h.rank_eight, ?_, ?_⟩
  · rw [QuadraticMap.polarBilin_comp]
    let := h.perfect
    infer_instance
  · apply norm_comp_after_baseChange
    intro x y
    change n (f (x * y)) = n (f x) * n (f y)
    rw [hMul, octonion_norm_mul h]

theorem octonion_automorphism_invariance (h : IsOctonionNorm n)
    (S : Type w) [CommRing S] [Algebra R S] :
    letI := h.projective
    let q := normBaseChange S n
    ∀ (f : (S ⊗[R] A) ≃ₗ[S] (S ⊗[R] A)),
      f 1 = 1 → (∀ x y, f (x * y) = f x * f y) →
        q.comp f.toLinearMap = q ∧ (compositionTrace q).comp f.toLinearMap = compositionTrace q ∧
          (conjugate q).comp f.toLinearMap = f.toLinearMap.comp (conjugate q) := by
  intro q f hOne hMul
  have hq : IsOctonionNorm q := octonion_norm_baseChange h S
  have H := octonion_norm_unique (octonion_norm_comp_equiv hq f hMul) hq
  have trace_preserved (x : S ⊗[R] A) : compositionTrace q (f x) = compositionTrace q x := by
    have E := LinearMap.congr_fun H.2 x
    simpa only [compositionTrace_apply, QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply,
      LinearEquiv.coe_coe, hOne] using E
  refine ⟨H.1, LinearMap.ext trace_preserved, LinearMap.ext fun x => ?_⟩
  change conjugate q (f x) = f (conjugate q x)
  simp only [conjugate_apply, map_sub, map_smul, hOne, trace_preserved]

theorem octonion_automorphism_coefficients : AdjointSpecification.octonionAutomorphismCoefficients := by
  intro R A _ _ _ _ _ n h S _ _ q f hOne hMul x y
  have H := octonion_automorphism_invariance h S f hOne hMul
  refine ⟨congrArg (fun Q : QuadraticForm S (S ⊗[R] A) => Q x) H.1, ?_,
    LinearMap.congr_fun H.2.1 x⟩
  have E := congrArg (fun Q : QuadraticForm S (S ⊗[R] A) => Q.polarBilin x y) H.1
  simpa only [QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe] using E

end Uniqueness

theorem field_composition_norm_unique {R : Type u} {A : Type v}
    [Field R] [NonAssocRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    {n n' : QuadraticForm R A} (h : IsFieldCompositionNorm n) (h' : IsFieldCompositionNorm n') :
    n = n' ∧ compositionTrace n = compositionTrace n' := by
  let := h.finite
  exact local_norm_unique h.toNormLaws h'.toNormLaws

end LinearAlgebraicGroups.Composition
