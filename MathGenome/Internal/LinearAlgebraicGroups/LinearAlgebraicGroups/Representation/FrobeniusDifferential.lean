import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FrobeniusDifferential
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.RootWeightAction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RelativeFrobenius
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Polynomial.Laurent

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RootWeightAction
open AlgebraicGeometry CategoryTheory Opposite WithConv

universe u

namespace LinearAlgebraicGroups.Representation.FrobeniusDifferential

open Specs.FrobeniusDifferential
open Specs.RelativeFrobenius (PullbackFormula twistCoordinates scalarTensor extendAlong)
open Specs.StandardGroups (SLCoordinates specialLinearPoints)

open private extAlong from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RelativeFrobenius
open private StandardGroups.Representation.convolutionIso
  StandardGroups.specialLinearRepresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private convolutionScalarExtension from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent

noncomputable section

variable {k : Type u} [Field k]

private def specPoint {A : HopfAlgebraCategory k} {R : TestAlgebra k}
    (g : A →ₐ[k] R) : ((groupPointsFunctor k).obj (specGroup A)).obj R :=
  (hopfSpecPointIso A).hom.app R (toConv g)

private theorem specPoint_comp {A B : HopfAlgebraCategory k} {R : TestAlgebra k}
    (f : B ⟶ A) (g : A →ₐ[k] R) :
    ((groupPointsFunctor k).map (specGroupMap f)).app R (specPoint g) =
      specPoint (g.comp f.hom.toAlgHom) := by
  apply Over.OverMorphism.ext
  exact (Spec.map_comp (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)
    (CommRingCat.ofHom g.toRingHom)).symm

private theorem dualNumber_pow {p : ℕ} [Fact p.Prime] [CharP k p]
    (z : DualNumber k) :
    z ^ p = (TrivSqZeroExt.inl z.fst : DualNumber k) ^ p := by
  let : CharP (DualNumber k) p :=
    CharP.of_ringHom_of_ne_zero (algebraMap k (DualNumber k)) p
      (Fact.out : p.Prime).ne_zero
  have h : (TrivSqZeroExt.inr z.snd : DualNumber k) ^ p = 0 :=
    pow_eq_zero_of_le (Fact.out : p.Prime).two_le (by
      rw [pow_two, TrivSqZeroExt.inr_mul_inr])
  calc
    z ^ p = (TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inr z.snd : DualNumber k) ^ p :=
      congrArg (· ^ p) z.inl_fst_add_inr_snd_eq.symm
    _ = _ := by rw [add_pow_char, h, add_zero]

theorem relativeFrobeniusDifferential_conditional
    (_rootWeightAction : Specs.RootWeightAction.Statement.{u}) :
    RelativeFrobeniusDifferential.{u} := by
  intro k _ p _ _ A f hf
  let R := CommAlgCat.of k (DualNumber k)
  let S := CommAlgCat.of k k
  let e := hopfSpecPointIso A
  apply AddMonoidHom.ext
  intro v
  let x : (convolutionPoints A).obj R := e.inv.app R v.toMul.val
  have hx : e.hom.app R x = v.toMul.val :=
    DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.inv_hom_id_app R)) v.toMul.val
  have hred := DFunLike.congr_fun
    (congrArg GrpCat.Hom.hom (e.hom.naturality (dualReduction k))) x
  change e.hom.app S ((convolutionPoints A).map (dualReduction k) x) =
    reduceTangentPoints (specGroup A) (e.hom.app R x) at hred
  rw [hx, v.toMul.property, ← map_one (e.hom.app S).hom] at hred
  have hred' : (convolutionPoints A).map (dualReduction k) x = 1 := by
    calc
      _ = e.inv.app S (e.hom.app S ((convolutionPoints A).map (dualReduction k) x)) :=
        (GrpCat.inv_hom_apply (e.app S) _).symm
      _ = e.inv.app S (e.hom.app S 1) := congrArg (fun t => e.inv.app S t) hred
      _ = _ := GrpCat.inv_hom_apply (e.app S) _
  -- Both points have the same constant coefficient on every coordinate.
  have hfst (a : A) :
      (x.ofConv a).fst = ((1 : (convolutionPoints A).obj R).ofConv a).fst := by
    have h := congrArg (fun y : (convolutionPoints A).obj S => y.ofConv a) hred'
    change (x.ofConv a).fst = _ at h
    exact h.trans (congrArg (fun y : (convolutionPoints A).obj S => y.ofConv a)
      (map_one ((convolutionPoints A).map (dualReduction k)).hom)).symm
  have hcomp : x.ofConv.comp f.hom.toAlgHom =
      (1 : (convolutionPoints A).obj R).ofConv.comp f.hom.toAlgHom := by
    apply extAlong (frobenius k p) A
    intro a
    change x.ofConv (f.hom (scalarTensor (frobenius k p) A 1 a)) =
      (1 : (convolutionPoints A).obj R).ofConv (f.hom (scalarTensor (frobenius k p) A 1 a))
    rw [hf, one_smul, map_pow, map_pow]
    rw [dualNumber_pow (x.ofConv a), dualNumber_pow ((1 : (convolutionPoints A).obj R).ofConv a),
      hfst a]
  apply Subtype.ext
  change ((groupPointsFunctor k).map (specGroupMap f)).app R v.toMul.val = 1
  change specPoint x.ofConv = v.toMul.val at hx
  rw [← hx, specPoint_comp f, hcomp, ← specPoint_comp f]
  change ((groupPointsFunctor k).map (specGroupMap f)).app R (e.hom.app R 1) = 1
  rw [map_one, map_one]

private abbrev sl2Hopf (k : Type u) [Field k] : HopfAlgebraCategory k :=
  letI := StandardGroups.specialLinearHopf k SL2Index
  CommHopfAlgCat.of k (SLCoordinates k SL2Index)

private def sl2PointIso :
    (groupPointsFunctor k).obj (specGroup (sl2Hopf k)) ≅ specialLinearPoints k SL2Index :=
  StandardGroups.specialLinearGroupPointsIso k SL2Index

private theorem coordinates_specPoint {A : HopfAlgebraCategory k} {R : TestAlgebra k}
    (g : A →ₐ[k] R) :
    (hopfSpecPointIso A).inv.app R (specPoint g) = toConv g :=
  DFunLike.congr_fun (congrArg GrpCat.Hom.hom ((hopfSpecPointIso A).hom_inv_id_app R)) (toConv g)

private theorem sl2PointIso_eval :
    IsMatrixIdentification (sl2Hopf k) (sl2Matrix k) sl2PointIso := by
  intro R g
  let c := StandardGroups.Representation.convolutionIso
    (StandardGroups.specialLinearRepresentation (k := k) (ι := SL2Index))
  change (c.hom.app R ((hopfSpecPointIso (sl2Hopf k)).inv.app R (specPoint g)) :
    Matrix.SpecialLinearGroup SL2Index R).val = _
  rw [coordinates_specPoint]
  rfl

private def sl2ScalarExtensionIso {K : Type u} [Field K] (σ : k →+* K) :
    (groupPointsFunctor K).obj (specGroup (extendAlong σ (sl2Hopf k))) ≅
      specialLinearPoints K SL2Index := by
  letI := σ.toAlgebra
  let e : restrictTestAlgebra k K ⋙ specialLinearPoints k SL2Index ≅
      specialLinearPoints K SL2Index :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  exact (hopfSpecPointIso (extendAlong σ (sl2Hopf k))).symm ≪≫
    convolutionScalarExtension K (sl2Hopf k) ≪≫
    Functor.isoWhiskerLeft (restrictTestAlgebra k K)
      (hopfSpecPointIso (sl2Hopf k) ≪≫ sl2PointIso) ≪≫ e

private theorem sl2ScalarExtensionIso_eval {K : Type u} [Field K] (σ : k →+* K)
    (R : TestAlgebra K) (g : extendAlong σ (sl2Hopf k) →ₐ[K] R) :
    ((sl2ScalarExtensionIso σ).hom.app R (specPoint g) :
      Matrix.SpecialLinearGroup SL2Index R).val =
      g.mapMatrix (fun i j => scalarTensor σ (sl2Hopf k) 1 (sl2Matrix k i j)) := by
  let : Algebra k K := σ.toAlgebra
  let S := (restrictTestAlgebra k K).obj R
  let a := (convolutionScalarExtension K (sl2Hopf k)).hom.app R
  change ((sl2PointIso (k := k)).hom.app S
    (specPoint (a ((hopfSpecPointIso (extendAlong σ (sl2Hopf k))).inv.app R (specPoint g))).ofConv) :
      Matrix.SpecialLinearGroup SL2Index S).val = _
  rw [coordinates_specPoint]
  exact sl2PointIso_eval S (a (toConv g)).ofConv

private def laurentUnit : (LaurentPolynomial k)ˣ :=
  ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1),
    by rw [← LaurentPolynomial.T_add]; exact LaurentPolynomial.T_zero,
    by rw [← LaurentPolynomial.T_add]; exact LaurentPolynomial.T_zero⟩

private theorem laurentUnit_pow (p : ℕ) :
    ((laurentUnit (k := k) ^ p : (LaurentPolynomial k)ˣ) : LaurentPolynomial k) =
      LaurentPolynomial.T (p : ℤ) := by
  rw [Units.val_pow_eq_pow_val]
  change LaurentPolynomial.T 1 ^ p = _
  rw [LaurentPolynomial.T_pow, mul_one]

private theorem laurentUnit_neg_pow (p : ℕ) :
    ((laurentUnit (k := k) ^ (-(p : ℤ)) : (LaurentPolynomial k)ˣ) : LaurentPolynomial k) =
      LaurentPolynomial.T (-(p : ℤ)) := by
  rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
  change LaurentPolynomial.T (-1) ^ p = _
  rw [LaurentPolynomial.T_pow, mul_neg, mul_one]

private theorem laurentMonomial_injective :
    Function.Injective (LaurentPolynomial.T (R := k)) := by
  intro m n h
  have hd := congrArg LaurentPolynomial.degree h
  rwa [LaurentPolynomial.degree_T, LaurentPolynomial.degree_T, WithBot.coe_inj] at hd

private theorem diagonal_pow (p : ℕ) (hp : p ≠ 0) (R : TestAlgebra k) (t : Rˣ) :
    (fun i j => diagonalMatrix t i j ^ p : Matrix SL2Index SL2Index R) =
      Matrix.diagonal (diagonalEntries
        ((torusCharacter (k := k) (p : ℤ)).app R t : Rˣ).val
        ((torusCharacter (k := k) (-(p : ℤ))).app R t : Rˣ).val) := by
  classical
  ext i j
  change Matrix.diagonal _ i j ^ p = Matrix.diagonal _ i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    change diagonalEntries (t : R) (↑t⁻¹ : R) i ^ p =
      diagonalEntries (↑(t ^ (p : ℤ)) : R) (↑(t ^ (-(p : ℤ))) : R) i
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    simp only [diagonalEntries, Units.val_pow_eq_pow_val]
    rcases i with ⟨i⟩
    fin_cases i <;> rfl
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij, zero_pow hp]

set_option maxHeartbeats 1200000 in
theorem splitSL2Example_conditional
    (rootWeightAction : Specs.RootWeightAction.Statement.{u}) :
    SplitSL2Example.{u} := by
  intro k _ p _ _
  let A := sl2Hopf k
  let f := RelativeFrobenius.pullback p A
  let e := sl2PointIso (k := k)
  let eTwist := sl2ScalarExtensionIso (frobenius k p)
  have hf : PullbackFormula k p A f := RelativeFrobenius.pullback_formula p A
  have he : IsMatrixIdentification A (sl2Matrix k) e := sl2PointIso_eval
  have heTwist : IsMatrixIdentification (twistCoordinates k p A)
      (fun i j => scalarTensor (frobenius k p) A 1 (sl2Matrix k i j)) eTwist := by
    intro R g
    exact sl2ScalarExtensionIso_eval (frobenius k p) R g
  refine ⟨StandardGroups.specialLinearHopf k SL2Index, f, e, eTwist, hf, he, heTwist, ?_⟩
  let F := (groupPointsFunctor k).map (specGroupMap f)
  let ρ := F ≫ eTwist.hom ≫ naturalModule
  change mapDualKernel ρ = 0 ∧ _ ∧ _ ∧ _
  have hr : mapPointKernel (specGroupMap f) = 0 :=
    relativeFrobeniusDifferential_conditional rootWeightAction k p A f hf
  have hzero : mapDualKernel ρ = 0 := by
    apply AddMonoidHom.ext
    intro x
    have hx := congrArg (fun g => (g x).toMul.val) hr
    let R := CommAlgCat.of k (DualNumber k)
    change F.app R x.toMul.val = 1 at hx
    apply Subtype.ext
    change naturalModule.app R (eTwist.hom.app R (F.app R x.toMul.val)) = 1
    rw [hx, map_one, map_one]
  have hpow (R : TestAlgebra k) (g : ((groupPointsFunctor k).obj (specGroup A)).obj R)
      (i j : SL2Index) :
      (ρ.app R g : Matrix.GeneralLinearGroup SL2Index R).val i j =
        (e.hom.app R g : Matrix.SpecialLinearGroup SL2Index R).val i j ^ p := by
    let x := (hopfSpecPointIso A).inv.app R g
    have hx : specPoint x.ofConv = g :=
      DFunLike.congr_fun (congrArg GrpCat.Hom.hom ((hopfSpecPointIso A).inv_hom_id_app R)) g
    rw [← hx]
    have h₁ := congrFun (congrFun (he R x.ofConv) i) j
    have h₂ := congrFun (congrFun (heTwist R (x.ofConv.comp f.hom.toAlgHom)) i) j
    change (e.hom.app R (specPoint x.ofConv) : Matrix.SpecialLinearGroup SL2Index R).val i j =
      x.ofConv (sl2Matrix k i j) at h₁
    change (eTwist.hom.app R (specPoint (x.ofConv.comp f.hom.toAlgHom)) :
      Matrix.SpecialLinearGroup SL2Index R).val i j =
      x.ofConv (f.hom (scalarTensor (frobenius k p) A 1 (sl2Matrix k i j))) at h₂
    change (eTwist.hom.app R (F.app R (specPoint x.ofConv)) :
      Matrix.SpecialLinearGroup SL2Index R).val i j = _
    rw [specPoint_comp f, h₁, h₂, hf, one_smul, map_pow]
  have hdiag (R : TestAlgebra k) (t : Rˣ) :
      (ρ.app R (e.inv.app R (diagonalPoint t)) : Matrix.GeneralLinearGroup SL2Index R).val =
        Matrix.diagonal (diagonalEntries
          ((torusCharacter (k := k) (p : ℤ)).app R t : Rˣ).val
          ((torusCharacter (k := k) (-(p : ℤ))).app R t : Rˣ).val) := by
    have ht : e.hom.app R (e.inv.app R (diagonalPoint t)) = diagonalPoint t :=
      DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.inv_hom_id_app R)) (diagonalPoint t)
    rw [← diagonal_pow p (Fact.out : p.Prime).ne_zero]
    exact Matrix.ext fun i j => by rw [hpow, ht]; rfl
  refine ⟨hzero, ?_, ?_, hdiag⟩
  · let R := CommAlgCat.of k (LaurentPolynomial k)
    let i : SL2Index := ULift.up 0
    refine ⟨R, e.inv.app R (diagonalPoint laurentUnit), ?_⟩
    intro h
    have hh := hdiag R laurentUnit
    rw [h] at hh
    have hx := congrFun (congrFun hh i) i
    change (1 : Matrix SL2Index SL2Index R) i i = _ at hx
    rw [Matrix.one_apply_eq, Matrix.diagonal_apply_eq] at hx
    change (1 : LaurentPolynomial k) = (↑(laurentUnit (k := k) ^ (p : ℤ)) :
      LaurentPolynomial k) at hx
    have ht : (1 : LaurentPolynomial k) = (↑(laurentUnit (k := k) ^ p) : LaurentPolynomial k) := by
      simpa only [zpow_natCast] using hx
    rw [laurentUnit_pow, ← LaurentPolynomial.T_zero] at ht
    have := laurentMonomial_injective ht
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this.symm)
  · intro h
    let R := CommAlgCat.of k (LaurentPolynomial k)
    have hx := congrArg (fun e : Specs.StandardGroups.multiplicativePoints k ⟶
        Specs.StandardGroups.multiplicativePoints k =>
      (e.app R (laurentUnit (k := k)) : (LaurentPolynomial k)ˣ).val) h
    change (↑(laurentUnit (k := k) ^ (p : ℤ)) : LaurentPolynomial k) =
      ↑(laurentUnit (k := k) ^ (-(p : ℤ))) at hx
    rw [zpow_natCast, laurentUnit_pow, laurentUnit_neg_pow] at hx
    have hh := laurentMonomial_injective hx
    have hp := (Fact.out : p.Prime).pos
    omega

end

end LinearAlgebraicGroups.Representation.FrobeniusDifferential

universe v8_closure_6b2c2fc65459d755_u0
theorem _root_.«LinearAlgebraicGroups».«Representation».«FrobeniusDifferential».«relativeFrobeniusDifferential» : _root_.«LinearAlgebraicGroups».«Specs».«FrobeniusDifferential».«RelativeFrobeniusDifferential».{v8_closure_6b2c2fc65459d755_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«FrobeniusDifferential».«relativeFrobeniusDifferential_conditional».{v8_closure_6b2c2fc65459d755_u0} (@_root_.«LinearAlgebraicGroups».«Representation».«RootWeightAction».«rootWeightAction».{v8_closure_6b2c2fc65459d755_u0})
theorem _root_.«LinearAlgebraicGroups».«Representation».«FrobeniusDifferential».«splitSL2Example» : _root_.«LinearAlgebraicGroups».«Specs».«FrobeniusDifferential».«SplitSL2Example».{v8_closure_6b2c2fc65459d755_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«FrobeniusDifferential».«splitSL2Example_conditional».{v8_closure_6b2c2fc65459d755_u0} (@_root_.«LinearAlgebraicGroups».«Representation».«RootWeightAction».«rootWeightAction».{v8_closure_6b2c2fc65459d755_u0})
