import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ObstructedFirstOrderExample
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FlatSquareZeroLifts
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

noncomputable section

open scoped TensorProduct
open Polynomial
open CommutativeAlgebraNotes

namespace CommutativeAlgebraNotes.ObstructedFirstOrderExample

universe u v

/-- Four coefficients ordered as `1,x,y,z`, with multiplication depending on `t`. -/
private def Coordinates (R : Type*) (_t : R) := Fin 4 → R

namespace Coordinates

variable {R : Type*} {t : R}

abbrev coeff (a : Coordinates R t) : Fin 4 → R := a

private def vec (a b c d : R) : Coordinates R t := ![a, b, c, d]

@[simp] theorem coeff_vec (a b c d : R) (i : Fin 4) :
    (vec (t := t) a b c d).coeff i = ![a,b,c,d] i := rfl

private theorem ext {a b : Coordinates R t} (h : ∀ i, a.coeff i = b.coeff i) : a = b :=
  funext h

variable [CommRing R]

instance : AddCommGroup (Coordinates R t) :=
  inferInstanceAs (AddCommGroup (Fin 4 → R))

@[simp] theorem coeff_add (a b : Coordinates R t) (i : Fin 4) :
    (a + b).coeff i = a.coeff i + b.coeff i := rfl

@[simp] theorem coeff_zero (i : Fin 4) : (0 : Coordinates R t).coeff i = 0 := rfl

instance : One (Coordinates R t) := ⟨vec 1 0 0 0⟩

instance : Mul (Coordinates R t) where
  mul a b :=
    vec
      (a.coeff 0 * b.coeff 0)
      (a.coeff 0 * b.coeff 1 + a.coeff 1 * b.coeff 0)
      (a.coeff 0 * b.coeff 2 + a.coeff 2 * b.coeff 0 + t * a.coeff 3 * b.coeff 3)
      (a.coeff 0 * b.coeff 3 + a.coeff 3 * b.coeff 0 +
        t * (a.coeff 1 * b.coeff 2 + a.coeff 2 * b.coeff 1))

@[simp] theorem one_coeff (i : Fin 4) :
    (1 : Coordinates R t).coeff i = ![(1 : R),0,0,0] i := rfl

@[simp] theorem mul_coeff (a b : Coordinates R t) (i : Fin 4) :
    (a * b).coeff i =
      ![a.coeff 0 * b.coeff 0,
        a.coeff 0 * b.coeff 1 + a.coeff 1 * b.coeff 0,
        a.coeff 0 * b.coeff 2 + a.coeff 2 * b.coeff 0 + t * a.coeff 3 * b.coeff 3,
        a.coeff 0 * b.coeff 3 + a.coeff 3 * b.coeff 0 +
          t * (a.coeff 1 * b.coeff 2 + a.coeff 2 * b.coeff 1)] i := rfl

instance [Fact (t ^ 2 = 0)] : CommRing (Coordinates R t) where
  __ := (inferInstance : AddCommGroup (Coordinates R t))
  __ := (inferInstance : One (Coordinates R t))
  __ := (inferInstance : Mul (Coordinates R t))
  zero_mul a := by apply ext; intro i; fin_cases i <;> simp
  mul_zero a := by apply ext; intro i; fin_cases i <;> simp
  one_mul a := by apply ext; intro i; fin_cases i <;> simp
  mul_one a := by apply ext; intro i; fin_cases i <;> simp
  mul_comm a b := by apply ext; intro i; fin_cases i <;> simp <;> ring
  left_distrib a b c := by apply ext; intro i; fin_cases i <;> simp <;> ring
  right_distrib a b c := by apply ext; intro i; fin_cases i <;> simp <;> ring
  mul_assoc a b c := by
    apply ext
    intro i
    fin_cases i <;> simp <;> ring_nf <;> simp [Fact.out (p := t ^ 2 = 0)]

variable [Fact (t ^ 2 = 0)]

private def const : R →+* Coordinates R t where
  toFun r := vec r 0 0 0
  map_one' := rfl
  map_zero' := by apply ext; intro i; fin_cases i <;> simp
  map_add' _ _ := by apply ext; intro i; fin_cases i <;> simp
  map_mul' _ _ := by apply ext; intro i; fin_cases i <;> simp

instance : Algebra R (Coordinates R t) := const.toAlgebra

@[simp] theorem coeff_algebraMap (r : R) (i : Fin 4) :
    (algebraMap R (Coordinates R t) r).coeff i = ![r,0,0,0] i := rfl

@[simp] theorem coeff_smul (r : R) (a : Coordinates R t) (i : Fin 4) :
    (r • a).coeff i = r * a.coeff i := by
  fin_cases i <;> simp [Algebra.smul_def]

private def linearEquiv : Coordinates R t ≃ₗ[R] (Fin 4 → R) where
  toEquiv := Equiv.refl _
  map_add' _ _ := rfl
  map_smul' r a := funext fun i => coeff_smul r a i

private def basis : Module.Basis (Fin 4) R (Coordinates R t) :=
  (Pi.basisFun R (Fin 4)).map linearEquiv.symm

@[simp] theorem coeff_basis (i j : Fin 4) :
    (basis (R := R) (t := t) i).coeff j = (Pi.single i (1 : R) : Fin 4 → R) j :=
  congrFun (Pi.basisFun_apply R (Fin 4) i) j

private theorem basis_products :
    let b := basis (t := t)
    b 1 * b 2 = t • b 3 ∧ b 3 * b 3 = t • b 2 ∧
    b 1 * b 1 = 0 ∧ b 1 * b 3 = 0 ∧ b 2 * b 2 = 0 ∧ b 2 * b 3 = 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply ext (t := t); intro i; fin_cases i <;> simp)

end Coordinates

section Bases

variable (k : Type u) [Field k]

local notation "R₃" => base k 2
local notation "R₂" => base k 1
local notation "t₃" => parameter k 2
local notation "t₂" => parameter k 1

private theorem reduction_mk (p : k[X]) :
    (reduction k).val (AdjoinRoot.mk _ p) = (AdjoinRoot.mk _ p : Truncated k 1) := by
  let f : Truncated k 2 →+* Truncated k 1 := (reduction k).val.toRingHom
  have h : f.comp (AdjoinRoot.mk _) = AdjoinRoot.mk _ := by
    apply Polynomial.ringHom_ext
    · intro a
      change f (AdjoinRoot.mk _ (C a)) = AdjoinRoot.mk _ (C a)
      rw [AdjoinRoot.mk_C, AdjoinRoot.mk_C]
      exact (show Truncated k 2 →ₐ[k] Truncated k 1 from (reduction k).val).commutes a
    · change f (AdjoinRoot.mk _ X) = AdjoinRoot.mk _ X
      rw [AdjoinRoot.mk_X, AdjoinRoot.mk_X]
      exact reduction_parameter k
  exact DFunLike.congr_fun h p

private theorem reduction_surjective : Function.Surjective (reduction k).val := by
  intro x
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  exact ⟨AdjoinRoot.mk _ p, reduction_mk k p⟩

private theorem ker_reduction :
    RingHom.ker (reduction k).val.toRingHom = Ideal.span {t₃ ^ 2} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    have h : (AdjoinRoot.mk _ p : Truncated k 1) = 0 :=
      (reduction_mk k p).symm.trans (RingHom.mem_ker.mp hx)
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_eq_zero.mp h
    apply Ideal.mem_span_singleton.mpr
    refine ⟨(show R₃ from AdjoinRoot.mk _ q), ?_⟩
    have hm := (AdjoinRoot.mk (X ^ 3 : k[X])).map_mul (X ^ 2) q
    rw [map_pow, AdjoinRoot.mk_X] at hm
    exact hm
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change (reduction k).val (t₃ ^ 2) = 0
    rw [map_pow, reduction_parameter, parameter_pow k 1]

private theorem parameter_sq_ne_zero : t₃ ^ 2 ≠ 0 := by
  suffices h : (root k 2) ^ 2 ≠ 0 by exact h
  have h : AdjoinRoot.mk (X ^ 3 : k[X]) (X ^ 2) ≠ 0 := by
    apply AdjoinRoot.mk_ne_zero_of_natDegree_lt ((monic_X (R := k)).pow _)
    · exact pow_ne_zero _ X_ne_zero
    · simp
  rw [map_pow, AdjoinRoot.mk_X] at h
  exact h

private theorem mul_root_sq (r : Truncated k 2) :
    r * (root k 2) ^ 2 = algebraMap k (Truncated k 2) (augmentation k 2 r) * (root k 2) ^ 2 := by
  let c := algebraMap k (Truncated k 2) (augmentation k 2 r)
  have hr : r - c ∈ RingHom.ker (augmentation k 2).toRingHom := by
    change augmentation k 2 (r - c) = 0
    rw [map_sub, show augmentation k 2 c = augmentation k 2 r from
      (augmentation k 2).commutes _, sub_self]
  rw [ker_augmentation, Ideal.mem_span_singleton] at hr
  obtain ⟨q, hq⟩ := hr
  have hpow : (root k 2) ^ 2 * (root k 2) = 0 := by
    rw [← pow_succ, root_pow k 2]
  calc
    r * (root k 2) ^ 2 = (r - c) * (root k 2) ^ 2 + c * (root k 2) ^ 2 := by ring
    _ = c * (root k 2) ^ 2 := by
      rw [hq, mul_comm (root k 2) q, mul_assoc, mul_comm (root k 2) ((root k 2) ^ 2), hpow, mul_zero, zero_add]

private theorem mul_parameter_sq (r : R₃) :
    r * t₃ ^ 2 = algebraMap k R₃ ((base k 2).residue r) * t₃ ^ 2 :=
  mul_root_sq k r

/-- Multiplication by `t²` embeds the residue field as an R₃-submodule. -/
private def embedResidue : k →ₗ[R₃] R₃ where
  toFun a := algebraMap k R₃ a * t₃ ^ 2
  map_add' a b := by
    change algebraMap k R₃ (a + b) * t₃ ^ 2 =
      algebraMap k R₃ a * t₃ ^ 2 + algebraMap k R₃ b * t₃ ^ 2
    rw [map_add, add_mul]
  map_smul' r a := by
    change algebraMap k R₃ ((base k 2).residue r * a) * t₃ ^ 2 =
      r * (algebraMap k R₃ a * t₃ ^ 2)
    rw [map_mul, mul_left_comm r, mul_parameter_sq k r]
    ring

private theorem embedResidue_injective : Function.Injective (embedResidue k) := by
  apply (injective_iff_map_eq_zero _).2
  intro a ha
  change algebraMap k (Truncated k 2) a * (root k 2) ^ 2 = 0 at ha
  by_contra hn
  have hu := (isUnit_iff_ne_zero.mpr hn).map (algebraMap k (Truncated k 2))
  exact parameter_sq_ne_zero k (hu.mul_right_eq_zero.mp ha)

private theorem residue_of_parameter_sq_smul_eq_zero
    {D : Type v} [CommRing D] [Algebra R₃ D] [Module.Flat R₃ D] {d : D}
    (h : (t₃ ^ 2 : R₃) • d = 0) : (1 : k) ⊗ₜ[R₃] d = 0 := by
  let m := (TensorProduct.lid R₃ D).toLinearMap.comp ((embedResidue k).rTensor D)
  have hm : Function.Injective m :=
    (TensorProduct.lid R₃ D).injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ (embedResidue_injective k))
  apply hm
  change (algebraMap k R₃ 1 * t₃ ^ 2) • d = m 0
  rw [map_one, one_mul, h, map_zero]

end Bases

section FirstOrder

variable (k : Type u) [Field k]

local notation "A" => base k 1
local notation "B" => residual k
local notation "ε" => parameter k 1
local notation "ρ" => LocalArtinAlgebra.residue (base k 1)
local notation "E" => Coordinates A ε

local instance : Fact ((ε : A) ^ 2 = 0) := ⟨parameter_pow k 1⟩

private def residualCoords : B ≃ₗ[k] (Fin 4 → k) where
  toFun a :=
    let b : TrivSqZeroExt k (Fin 3 → k) := a
    Fin.cons b.fst b.snd
  invFun f := (⟨f 0, fun j => f j.succ⟩ : TrivSqZeroExt k (Fin 3 → k))
  left_inv a := by
    change (⟨_, _⟩ : TrivSqZeroExt k (Fin 3 → k)) = a
    exact TrivSqZeroExt.ext rfl rfl
  right_inv f := funext (Fin.cases rfl fun _ => rfl)
  map_add' _ _ := funext (Fin.cases rfl fun _ => rfl)
  map_smul' _ _ := funext (Fin.cases rfl fun _ => rfl)

private def residualBasis : Module.Basis (Fin 4) k B :=
  (Pi.basisFun k (Fin 4)).map (residualCoords k).symm

private theorem residualBasis_apply (i : Fin 4) :
    residualBasis k i = residualVectors k i := by
  rw [residualBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  rfl

private abbrev residueAlgebra : Algebra A B :=
  ((algebraMap k B).comp (algebraMap A k)).toAlgebra

local instance : Algebra A B := residueAlgebra k
local instance : IsScalarTower A k B := IsScalarTower.of_algebraMap_eq fun _ => rfl

@[simp] private theorem residue_parameter : (base k 1).residue ε = 0 :=
  augmentation_root k 1

private def reduceCoordinates : E →ₐ[A] B where
  toFun a :=
    (⟨ρ (a.coeff 0), fun j => ρ (a.coeff j.succ)⟩ :
      TrivSqZeroExt k (Fin 3 → k))
  map_zero' := TrivSqZeroExt.ext (map_zero ρ)
    (funext fun _ => map_zero ρ)
  map_one' := by
    apply TrivSqZeroExt.ext
    · exact map_one ρ
    · funext i
      fin_cases i <;> exact map_zero ρ
  map_add' _ _ := TrivSqZeroExt.ext (map_add ρ _ _)
    (funext fun _ => map_add ρ _ _)
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · exact map_mul ρ _ _
    · funext i
      change ρ ((a * b).coeff i.succ) =
        ρ (a.coeff 0) * ρ (b.coeff i.succ) +
          ρ (b.coeff 0) * ρ (a.coeff i.succ)
      fin_cases i <;> simp <;> ring
  commutes' a := by
    apply TrivSqZeroExt.ext
    · rfl
    · funext i
      fin_cases i <;> exact map_zero ρ

private theorem reduceCoordinates_basis (i : Fin 4) :
    reduceCoordinates k (Coordinates.basis i) = residualVectors k i := by
  have hc (j : Fin 4) :
      ρ ((Coordinates.basis (R := A) (t := ε) i).coeff j) =
        (Pi.single i (1 : k) : Fin 4 → k) j := by
    rw [Coordinates.coeff_basis]
    by_cases h : j = i
    · subst j
      simp [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]
  exact TrivSqZeroExt.ext (hc 0) (funext fun j => hc j.succ)

private def markingHom : k ⊗[A] E →ₐ[k] B :=
  Algebra.TensorProduct.lift (Algebra.ofId k B) (reduceCoordinates k) (fun _ _ => Commute.all _ _)

@[simp] private theorem markingHom_basis (i : Fin 4) :
    markingHom k (1 ⊗ₜ[A] Coordinates.basis i) = residualVectors k i := by
  simp [markingHom, reduceCoordinates_basis]

private def marking : k ⊗[A] E ≃ₐ[k] B :=
  AlgEquiv.ofBijective (markingHom k) (by
    let source := Algebra.TensorProduct.basis k
      (Coordinates.basis : Module.Basis (Fin 4) A E)
    let e := source.equiv (residualBasis k) (Equiv.refl _)
    have h : (markingHom k).toLinearMap = e.toLinearMap := by
      apply source.ext
      intro i
      rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
      change markingHom k (Algebra.TensorProduct.basis k Coordinates.basis i) =
        residualBasis k i
      rw [Algebra.TensorProduct.basis_apply, markingHom_basis, residualBasis_apply]
    exact (show Function.Bijective (markingHom k).toLinearMap from h ▸ e.bijective))

private def deformation : MarkedDeformation.{u,u,u,u} A B where
  carrier := E
  flat :=
    letI : Module.Free A E := Module.Free.of_basis Coordinates.basis
    inferInstance
  marking := marking k

private def deformationBasis : Module.Basis (Fin 4) A (deformation k) :=
  Coordinates.basis (t := ε)

private theorem basis_one : (Coordinates.basis (R := A) (t := ε)) 0 = 1 := by
  apply Coordinates.ext
  intro i
  fin_cases i <;> simp

end FirstOrder

section Obstruction

open private baseChange_unit_ker from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FlatSquareZeroLifts

variable (k : Type u) [Field k]

local notation "R" => base k 2
local notation "A" => base k 1
local notation "B" => residual k
local notation "t₃" => parameter k 2
local notation "t₂" => parameter k 1

private theorem residual_y_coefficient (a b : B) :
    residualCoords k (residualVectors k 2 + a * residualVectors k 3 -
      residualVectors k 1 * b) 2 = 1 := by
  let a' : TrivSqZeroExt k (Fin 3 → k) := a
  let b' : TrivSqZeroExt k (Fin 3 → k) := b
  change (1 : k) + (a'.fst * 0 + 0 * a'.snd 1) -
    (0 * b'.snd 1 + b'.fst * 0) = 1
  simp

private theorem noFlatLift
    (E : MarkedDeformation.{u,u,u,u} A B) (x₀ y₀ z₀ : E)
    (hxy : x₀ * y₀ = t₂ • z₀) (hzz : z₀ * z₀ = t₂ • y₀) (hyz : y₀ * z₀ = 0)
    (hx₀ : E.marking (1 ⊗ₜ[A] x₀) = residualVectors k 1)
    (hy₀ : E.marking (1 ⊗ₜ[A] y₀) = residualVectors k 2)
    (hz₀ : E.marking (1 ⊗ₜ[A] z₀) = residualVectors k 3) :
    letI := (reduction k).toAlgebra
    ∀ (D : Type v) [CommRing D] [Algebra R D] [Module.Flat R D],
      IsEmpty (A ⊗[R] D ≃ₐ[A] E) := by
  let := (reduction k).toAlgebra
  let := (reduction k).residueScalarTower
  intro D _ _ _
  refine ⟨fun e => ?_⟩
  let p : D →+* E :=
    e.toRingHom.comp (Algebra.TensorProduct.includeRight : D →ₐ[R] A ⊗[R] D).toRingHom
  let τ := algebraMap R D t₃
  have hτ : τ ^ 3 = 0 := by
    change (algebraMap R D t₃) ^ 3 = 0
    rw [← map_pow, parameter_pow k 2, map_zero]
  have hpτ : p τ = algebraMap A E t₂ := by
    change e ((1 : A) ⊗ₜ[R] algebraMap R D t₃) = _
    rw [← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply R A,
      AlgEquiv.commutes]
    exact congrArg (algebraMap A E) (reduction_parameter k)
  have hsurj : Function.Surjective p :=
    e.surjective.comp (TensorProduct.mk_surjective R D A (reduction_surjective k))
  obtain ⟨x, hx⟩ := hsurj x₀
  obtain ⟨y, hy⟩ := hsurj y₀
  obtain ⟨z, hz⟩ := hsurj z₀
  -- Errors in the quadratic reduction are multiples of the cubic base's t².
  have hker (d : D) (hd : p d = 0) : ∃ a : D, d = τ ^ 2 * a := by
    have hl : d ∈ LinearMap.ker (TensorProduct.mk R A D 1) := by
      apply e.injective
      exact hd.trans e.map_zero.symm
    rw [baseChange_unit_ker (reduction_surjective k)] at hl
    change d ∈ RingHom.ker (reduction k).val.toRingHom • (⊤ : Submodule R D) at hl
    rw [ker_reduction, Submodule.ideal_span_singleton_smul] at hl
    obtain ⟨a, -, ha⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hl
    refine ⟨a, ha.symm.trans ?_⟩
    rw [Algebra.smul_def, map_pow]
  obtain ⟨a, ha⟩ := hker (x * y - τ * z) (by
    rw [map_sub, map_mul, map_mul, hx, hy, hz, hpτ, ← Algebra.smul_def, hxy, sub_self])
  obtain ⟨b, hb⟩ := hker (y * z) (by rw [map_mul, hy, hz, hyz])
  obtain ⟨c, hc⟩ := hker (z * z - τ * y) (by
    rw [map_sub, map_mul, map_mul, hz, hy, hpτ, ← Algebra.smul_def, hzz, sub_self])
  have hassoc : τ ^ 2 * (y + a * z - x * b) = 0 := by
    linear_combination x * hb - z * ha - τ * hc - c * hτ
  have hsmul : (t₃ ^ 2 : R) • (y + a * z - x * b) = 0 := by
    rw [Algebra.smul_def, map_pow]
    exact hassoc
  -- Flatness detects the coefficient of t² in the special fibre.
  have hzero := residue_of_parameter_sq_smul_eq_zero k hsmul
  let f : k ⊗[R] D ≃ₐ[k] B :=
    (Algebra.TensorProduct.cancelBaseChange R A k k D).symm.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) e).trans E.marking)
  let q : D →+* B :=
    f.toRingHom.comp (Algebra.TensorProduct.includeRight : D →ₐ[R] k ⊗[R] D).toRingHom
  have hq (d : D) : q d = E.marking (1 ⊗ₜ[A] p d) := by
    change f ((1 : k) ⊗ₜ[R] d) = _
    simp [f, p]
  have hqx : q x = residualVectors k 1 := (hq x).trans (by rw [hx]; exact hx₀)
  have hqy : q y = residualVectors k 2 := (hq y).trans (by rw [hy]; exact hy₀)
  have hqz : q z = residualVectors k 3 := (hq z).trans (by rw [hz]; exact hz₀)
  have hqzero : q (y + a * z - x * b) = 0 := by
    change f ((1 : k) ⊗ₜ[R] (y + a * z - x * b)) = 0
    rw [hzero, map_zero]
  rw [map_sub, map_add, map_mul, map_mul, hqx, hqy, hqz] at hqzero
  have hh := congrArg (fun d : B => residualCoords k d 2) hqzero
  exact one_ne_zero ((residual_y_coefficient k (q a) (q b)).symm.trans
    (hh.trans (by rw [map_zero]; rfl)))

end Obstruction

/-- The explicit first-order deformation of the split square-zero algebra
has no flat lift to the cubic truncated polynomial ring. -/
theorem obstruction : Specs.CommutativeAlgebraNotes.ObstructedFirstOrderExample.Obstruction := by
  intro k _
  let : Fact (parameter k 1 ^ 2 = 0) := ⟨parameter_pow k 1⟩
  let b := deformationBasis k
  have hmark (i : Fin 4) :
      (deformation k).marking (1 ⊗ₜ[base k 1] b i) = residualVectors k i :=
    markingHom_basis k i
  obtain ⟨hxy, hzz, hxx, hxz, hyy, hyz⟩ := Coordinates.basis_products (t := parameter k 1)
  exact ⟨deformation k, b, basis_one k, hmark, hxy, hzz, hxx, hxz, hyy, hyz,
    noFlatLift k (deformation k) (b 1) (b 2) (b 3) hxy hzz hyz
      (hmark 1) (hmark 2) (hmark 3)⟩

end CommutativeAlgebraNotes.ObstructedFirstOrderExample
