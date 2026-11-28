import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.SkewReduction
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.Abel

import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.ClassicalLimit
noncomputable section

open scoped TensorProduct

namespace LieNotes.Quantum.SkewReduction

open Specs.LieNotes.Quantum
open Specs.LieNotes.Quantum.ClassicalLimit (ClassicalLimitProp ClassicalReduction firstLevel modParameter)
open Specs.LieNotes.Quantum.Completion (CompletedSquare HopfMaps Square Uh project)
open Specs.LieNotes.Quantum.MatrixSpecialization (Classical)
open Specs.LieNotes.Quantum.SkewReduction
open scoped Specs.LieNotes.Quantum.ClassicalLimit

universe u

set_option synthInstance.maxHeartbeats 120000

variable {k : Type u} [Field k] [CharZero k] {D : HopfMaps k}

private theorem completedFlip_flip (z : CompletedSquare k) :
    completedFlip (completedFlip z) = z := by
  apply Subtype.ext
  funext N
  change project k .square N (completedFlip (completedFlip z)) = project k .square N z
  rw [project_completedFlip, project_completedFlip]
  exact TensorProduct.comm_comm (Completion.A k N) (Completion.U k N) (Completion.U k N) _

private theorem specialize_project (r : ClassicalReduction D) (X : Uh k) :
    specialize r X = r.comparison (project k .single firstLevel X) := by
  change r.comparison (r.levelEquiv .single (modParameter k .single X)) = _
  exact congrArg r.comparison (r.levelEquiv_mk .single X)

private theorem specializeSquare_project (r : ClassicalReduction D) (Z : CompletedSquare k) :
    specializeSquare r Z = r.tensorComparison (project k .square firstLevel Z) := by
  change r.tensorComparison (r.levelEquiv .square (modParameter k .square Z)) = _
  exact congrArg r.tensorComparison (r.levelEquiv_mk .square Z)

private theorem tensorComparison_flip (r : ClassicalReduction D) (z : Square k firstLevel) :
    r.tensorComparison (levelFlip firstLevel z) = classicalFlip (r.tensorComparison z) := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a b
    calc
      r.tensorComparison (levelFlip firstLevel (a ⊗ₜ[Completion.A k firstLevel] b)) =
          r.tensorComparison (b ⊗ₜ[Completion.A k firstLevel] a) :=
        congrArg r.tensorComparison (levelFlip_tmul firstLevel a b)
      _ = r.comparison b ⊗ₜ[k] r.comparison a := r.tensorComparison_tmul b a
      _ = classicalFlip (r.comparison a ⊗ₜ[k] r.comparison b) := rfl
      _ = classicalFlip (r.tensorComparison (a ⊗ₜ[Completion.A k firstLevel] b)) :=
        congrArg classicalFlip (r.tensorComparison_tmul a b).symm
  · intro a b ha hb
    calc
      r.tensorComparison (levelFlip firstLevel (a + b)) =
          r.tensorComparison (levelFlip firstLevel a) + r.tensorComparison (levelFlip firstLevel b) :=
        (congrArg r.tensorComparison ((levelFlip firstLevel).map_add a b)).trans
          (r.tensorComparison.map_add _ _)
      _ = classicalFlip (r.tensorComparison a) + classicalFlip (r.tensorComparison b) :=
        congrArg₂ (· + ·) ha hb
      _ = classicalFlip (r.tensorComparison (a + b)) :=
        ((congrArg classicalFlip (r.tensorComparison.map_add a b)).trans
          (classicalFlip.map_add _ _)).symm

private theorem specializeSquare_flip (r : ClassicalReduction D) (Z : CompletedSquare k) :
    specializeSquare r (completedFlip Z) = classicalFlip (specializeSquare r Z) := by
  rw [specializeSquare_project, project_completedFlip, specializeSquare_project]
  exact tensorComparison_flip r _

private theorem specialize_comul (r : ClassicalReduction D) (X : Uh k) :
    specializeSquare r (D.comul X) = r.hopf.comul (specialize r X) :=
  r.comul X

attribute [local instance 100] LieRing.ofAssociativeRing in
private theorem classical_cocommutative (r : ClassicalReduction D) (x : Classical k) :
    classicalFlip (r.hopf.comul x) = r.hopf.comul x := by
  have heq : classicalFlip.toAlgHom.comp r.hopf.comul = r.hopf.comul := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro v
    change classicalFlip (r.hopf.comul (UniversalEnvelopingAlgebra.ι k v)) =
      r.hopf.comul (UniversalEnvelopingAlgebra.ι k v)
    rw [r.hopf.comul_ι]
    simp only [map_add, Algebra.TensorProduct.comm_tmul, add_comm]
  exact DFunLike.congr_fun heq x

private theorem specialize_eq_zero (r : ClassicalReduction D) (X : Uh k) :
    specialize r X = 0 ↔ project k .single firstLevel X = 0 := by
  rw [specialize_project, ← r.comparison.map_zero]
  exact r.comparison.injective.eq_iff

private theorem specializeSquare_eq_zero (r : ClassicalReduction D) (Z : CompletedSquare k) :
    specializeSquare r Z = 0 ↔ project k .square firstLevel Z = 0 := by
  rw [specializeSquare_project, ← r.tensorComparison.map_zero]
  exact r.tensorComparison.injective.eq_iff

private theorem project_first_eq_zero {p : Completion.TensorPower}
    (red : Completion.ReductionProp.{u}) (X : Completion.Limit k p) :
    project k p firstLevel X = 0 ↔ ∃ Y : Completion.Limit k p, (PowerSeries.X : PowerSeries k) • Y = X := by
  simpa only [show (firstLevel : ℕ) = 1 from rfl, pow_one] using (red k p).2.1 firstLevel |>.2 X

local notation "ℏ" => (PowerSeries.X : PowerSeries k)

private theorem exists_linear_division {R M N : Type*}
    [CommSemiring R] [AddCommMonoid M] [AddCommGroup N] [Module R M] [Module R N]
    (h : R) (hinj : Function.Injective (h • · : N → N)) (f g : M →ₗ[R] N)
    (hd : ∀ x, ∃ y : N, h • y = f x - g x) :
    ∃ divided : M →ₗ[R] N, ∀ x, h • divided x = f x - g x := by
  let mulParameter := LinearMap.lsmul R N h
  let numerator := f - g
  let intoRange := numerator.codRestrict (LinearMap.range mulParameter)
    (fun x => LinearMap.mem_range.mpr (hd x))
  let cancelParameter := LinearEquiv.ofInjective mulParameter hinj
  refine ⟨cancelParameter.symm.toLinearMap.comp intoRange, fun x => ?_⟩
  exact LinearEquiv.ofInjective_symm_apply (h := hinj) mulParameter (intoRange x)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
private theorem exists_divided (red : Completion.ReductionProp.{u})
    (r : ClassicalReduction D) :
    ∃ divided : Uh k →ₗ[PowerSeries k] CompletedSquare k,
      ∀ X, ℏ • divided X = D.comul X - completedFlip (D.comul X) := by
  let opposite := (completedFlip (k := k)).comp D.comul
  refine exists_linear_division (M := Uh k) (N := CompletedSquare k)
    ℏ (red k .square).1 D.comul.toLinearMap opposite.toLinearMap ?_
  intro X
  change ∃ Y : CompletedSquare k, ℏ • Y = D.comul X - completedFlip (D.comul X)
  have hz : specializeSquare r (D.comul X - completedFlip (D.comul X)) = 0 := calc
    _ = specializeSquare r (D.comul X) - specializeSquare r (completedFlip (D.comul X)) :=
      RingHom.map_sub (specializeSquare r).toRingHom (D.comul X) (completedFlip (D.comul X))
    _ = 0 := by rw [specializeSquare_flip, specialize_comul, classical_cocommutative, sub_self]
  exact (project_first_eq_zero red _).mp ((specializeSquare_eq_zero r _).mp hz)

private theorem specialize_surj (r : ClassicalReduction D) :
    Function.Surjective (specialize r) :=
  r.equiv.surjective.comp (Ideal.Quotient.mkₐ_surjective k (ClassicalLimit.parameterIdeal k .single))

private local instance scalarTower (p : Completion.TensorPower) :
    IsScalarTower k (PowerSeries k) (Completion.Limit k p) :=
  IsScalarTower.of_algebraMap_eq' rfl

private theorem exists_reduced (red : Completion.ReductionProp.{u})
    (r : ClassicalReduction D) (divided : Uh k →ₗ[PowerSeries k] CompletedSquare k) :
    ∃ skew : Classical k →ₗ[k] ClassicalSquare k,
      ∀ X, specializeSquare r (divided X) = skew (specialize r X) := by
  let f := (specialize r).toLinearMap
  let g := (specializeSquare r).toLinearMap.comp (divided.restrictScalars k)
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro X hX
    have hx : specialize r X = 0 := LinearMap.mem_ker.mp hX
    obtain ⟨Y, rfl⟩ := (project_first_eq_zero red X).mp ((specialize_eq_zero r X).mp hx)
    apply LinearMap.mem_ker.mpr
    change specializeSquare r (divided (ℏ • Y)) = 0
    rw [divided.map_smul]
    exact (specializeSquare_eq_zero r _).mpr
      ((project_first_eq_zero red _).mpr ⟨divided Y, rfl⟩)
  refine ⟨f.liftOfSurjective (specialize_surj r) ⟨g, hker⟩, fun X => ?_⟩
  exact (LinearMap.equivOfSurjective_apply (specialize_surj r) hker (m := X)).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
private theorem divided_flip (red : Completion.ReductionProp.{u})
    (divided : Uh k →ₗ[PowerSeries k] CompletedSquare k)
    (hdiv : ∀ X, ℏ • divided X = D.comul X - completedFlip (D.comul X)) (X : Uh k) :
    completedFlip (divided X) = -divided X := by
  apply (red k .square).1
  let flip : CompletedSquare k →ₐ[PowerSeries k] CompletedSquare k := completedFlip
  let a : CompletedSquare k := D.comul X
  let z : CompletedSquare k := divided X
  change ℏ • flip z = ℏ • (-z)
  calc
    ℏ • flip z = flip (ℏ • z) := (flip.toLinearMap.map_smul ℏ z).symm
    _ = flip (a - flip a) := congrArg flip (hdiv X)
    _ = flip a - flip (flip a) := by
      have hadd : flip (a - flip a) + flip (flip a) = flip a := calc
        _ = flip ((a - flip a) + flip a) := (flip.toLinearMap.map_add (a - flip a) (flip a)).symm
        _ = flip a := congrArg flip (sub_add_cancel a (flip a))
      have hsub := eq_sub_of_add_eq (G := CompletedSquare k) hadd
      exact Subtype.ext (congrArg Subtype.val hsub)
    _ = flip a - a := congrArg (flip a - ·) (completedFlip_flip a)
    _ = -(a - flip a) := (neg_sub a (flip a)).symm
    _ = -(ℏ • z) := congrArg Neg.neg (hdiv X).symm
    _ = ℏ • (-z) := (smul_neg ℏ z).symm

private theorem divided_mul {R A B : Type*}
    [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (h : R) (hinj : Function.Injective (h • · : B → B))
    (f g : A →ₐ[R] B) (d : A →ₗ[R] B)
    (hd : ∀ x, h • d x = f x - g x) (x y : A) :
    d (x * y) = f x * d y + d x * g y := by
  apply hinj
  change h • d (x * y) = h • (f x * d y + d x * g y)
  rw [hd (x * y), smul_add, ← Algebra.mul_smul_comm, ← Algebra.smul_mul_assoc,
    hd y, hd x, map_mul f x y, map_mul g x y, mul_sub, sub_mul]
  abel

set_option backward.isDefEq.respectTransparency false in
private theorem skew_mul (red : Completion.ReductionProp.{u}) (r : ClassicalReduction D)
    (divided : Uh k →ₗ[PowerSeries k] CompletedSquare k)
    (hdiv : ∀ X, ℏ • divided X = D.comul X - completedFlip (D.comul X))
    (skew : Classical k →ₗ[k] ClassicalSquare k)
    (hreduce : ∀ X, specializeSquare r (divided X) = skew (specialize r X))
    (x y : Classical k) :
    skew (x * y) = r.hopf.comul x * skew y + skew x * r.hopf.comul y := by
  obtain ⟨X, rfl⟩ := specialize_surj r x
  obtain ⟨Y, rfl⟩ := specialize_surj r y
  let opposite := (completedFlip (k := k)).comp D.comul
  have hd := divided_mul (A := Uh k) (B := CompletedSquare k)
    ℏ (red k .square).1 D.comul opposite divided hdiv X Y
  change divided (X * Y) = D.comul X * divided Y + divided X * completedFlip (D.comul Y) at hd
  have h := congrArg (specializeSquare r) hd
  simpa only [map_add, map_mul, hreduce, specialize_comul, specializeSquare_flip,
    classical_cocommutative] using h

private theorem derivation_commutator {R A B : Type*}
    [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (d : A →ₗ[R] B)
    (hd : ∀ x y, d (x * y) = f x * d y + d x * f y) (x y : A) :
    d (commutator x y) = commutator (f x) (d y) + commutator (d x) (f y) := by
  change d (x * y - y * x) = (f x * d y - d y * f x) + (d x * f y - f y * d x)
  rw [map_sub, hd x y, hd y x]
  abel

omit [CharZero k] in
private theorem diagonalAdjoint_eq (x : Classical k) (z : ClassicalSquare k) :
    diagonalAdjoint x z = commutator (x ⊗ₜ[k] 1 + 1 ⊗ₜ[k] x) z := by
  let p : ClassicalSquare k := x ⊗ₜ[k] 1 + 1 ⊗ₜ[k] x
  let bracket := LinearMap.mulLeft k p - LinearMap.mulRight k p
  have h : diagonalAdjoint x = bracket := by
    apply TensorProduct.ext'
    intro a b
    simp only [diagonalAdjoint, bracket, p, LinearMap.add_apply, LinearMap.sub_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    abel
  exact LinearMap.congr_fun h z

private theorem dividedSkew_nonempty (red : Completion.ReductionProp.{u})
    (r : ClassicalReduction D) : Nonempty (DividedSkew r) := by
  obtain ⟨divided, hdiv⟩ := exists_divided red r
  obtain ⟨skew, hreduce⟩ := exists_reduced red r divided
  have hcomm := derivation_commutator r.hopf.comul skew (skew_mul red r divided hdiv skew hreduce)
  refine ⟨{
    divided := divided
    skew := skew
    specialize_surjective := specialize_surj r
    cocommutative := classical_cocommutative r
    division_eq := fun X Z => ?_
    reduce_divided := hreduce
    flip_skew := fun x => ?_
    skew_commutator := hcomm
    primitive_cocycle := fun x y hx hy => ?_ }⟩
  · rw [← hdiv X]
    exact (red k .square).1.eq_iff
  · obtain ⟨X, rfl⟩ := specialize_surj r x
    rw [← hreduce X, ← specializeSquare_flip, divided_flip red divided hdiv X]
    exact RingHom.map_neg (specializeSquare r).toRingHom (divided X)
  · rw [hcomm, hx, hy, diagonalAdjoint_eq, diagonalAdjoint_eq]
    symm
    exact (sub_eq_add_neg _ _).trans (congrArg (_ + ·) (neg_sub _ _))

/-- The first-order skew coproduct, conditional on the completed classical limit. -/
theorem skew_reduction_conditional (classical_limit : ClassicalLimitProp.{u}) :
    SkewReductionProp.{u} := by
  intro k _ _
  obtain ⟨d, s, D, hproject, hhopf, hcontinuous, ⟨r⟩⟩ := (classical_limit.2.2.2 k).2
  exact ⟨d, s, D, hproject, hhopf, hcontinuous, r, dividedSkew_nonempty classical_limit.2.1 r⟩

end LieNotes.Quantum.SkewReduction

universe v8_closure_00084ebd51f33588_u0
theorem _root_.«LieNotes».«Quantum».«SkewReduction».«skew_reduction» : _root_.«Specs».«LieNotes».«Quantum».«SkewReduction».«SkewReductionProp».{v8_closure_00084ebd51f33588_u0} :=
  @_root_.«LieNotes».«Quantum».«SkewReduction».«skew_reduction_conditional».{v8_closure_00084ebd51f33588_u0} (@_root_.«LieNotes».«Quantum».«ClassicalLimit».«classical_limit».{v8_closure_00084ebd51f33588_u0})
