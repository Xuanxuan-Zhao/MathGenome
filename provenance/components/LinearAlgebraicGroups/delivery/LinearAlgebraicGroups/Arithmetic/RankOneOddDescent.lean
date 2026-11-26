import Specs.LinearAlgebraicGroups.Arithmetic.RankOneOddDescent
import LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting
import LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
import LinearAlgebraicGroups.Descent.InnerTypeA
import LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import LinearAlgebraicGroups.RootData.SpecialLinearDatum
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.RingTheory.PolynomialAlgebra
import Batteries.Tactic.OpenPrivate
import LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import LinearAlgebraicGroups.Affine.Stabilizers
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ProjectiveClassification

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.RankOneOddDescent

open LinearAlgebraicGroups.Specs
open _root_.Specs.RM03.CSA (isCentralSimple)

noncomputable section

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

open RM03.CSA (degree BaseChange)
open Specs.StandardGroups (additivePoints)
open private matrixOne from LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting

/-- A central simple algebra of degree two either is split over the ground field
or has division scalar extension along any finite extension of odd degree. -/
theorem degreeTwoCSA_split_or_oddBaseChange_division {A : Type u} [Ring A] [Algebra F A]
    [Module.Finite F E] (hA : isCentralSimple F A) (hd : degree F A = 2)
    (he : Odd (Module.finrank F E)) :
    Nonempty (A ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) ∨
      Nontrivial (BaseChange F E A) ∧ ∀ x : BaseChange F E A, x ≠ 0 → IsUnit x := by
  obtain ⟨n, B, _, _, hB, hn, ⟨e⟩⟩ := RM03.CSA.MatrixDivision.exists_presentation F A hA
  have hB' := RM03.CSA.isCentralSimple_of_isCentralDivision F B hB
  have hdeg := RM03.CSA.degree_matrix_division hA hB hn e
  change RM03.CSA.degree F A = 2 at hd
  rw [hd] at hdeg
  have hpos := RM03.CSA.degree_pos hB'
  have hnle : n ≤ 2 := by nlinarith
  by_cases hn₁ : n = 1
  · subst n
    have hdB : degree F B = 2 := by simpa using hdeg.symm
    obtain ⟨hnB, hunit⟩ := LocalQuadraticSplitting.odd_extension_division hB hdB he
    let e' : BaseChange F E A ≃ₐ[E] BaseChange F E B :=
      Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[E] E) (e.trans matrixOne)
    exact Or.inr ⟨e'.symm.injective.nontrivial, fun x hx => by
      simpa using (hunit (e' x) (fun h => hx (e'.injective (h.trans e'.map_zero.symm)))).map
        e'.symm.toMonoidHom⟩
  · have hn₂ : n = 2 := by omega
    subst n
    have hdB : RM03.CSA.degree F B = 1 := by omega
    have hb : Module.finrank F B = 1 := by
      simpa [hdB] using RM03.CSA.finrank_eq_degree_sq hB'
    obtain ⟨b⟩ := (Module.nonempty_algEquiv_iff_finrank_eq_one (R := F) (S := B)).mpr hb
    exact Or.inl ⟨e.trans (b.symm.mapMatrix (m := Fin 2))⟩

/-- A group functor represented faithfully in a division algebra's units has
no nontrivial additive one-parameter subgroup. At the universal parameter
the image is a polynomial unit, hence constant. -/
theorem additiveHom_trivial_of_division
    {A : Type u} [Ring A] [Algebra F A] [Nontrivial A]
    (hA : ∀ x : A, x ≠ 0 → IsUnit x)
    (H : TestAlgebra F ⥤ GrpCat.{u})
    (v : ∀ R : TestAlgebra F, H.obj R →* (R ⊗[F] A))
    (hv : ∀ R, Function.Injective (v R))
    (hn : ∀ {R T : TestAlgebra F} (f : R ⟶ T) (x : H.obj R),
      v T (H.map f x) = Algebra.TensorProduct.map f.hom (AlgHom.id F A) (v R x))
    (c : additivePoints F ⟶ H) (R : TestAlgebra F) (r : R) :
    c.app R (Multiplicative.ofAdd r) = 1 := by
  let : NoZeroDivisors A := ⟨fun {x y} h => or_iff_not_imp_left.mpr (fun hx => by
    obtain ⟨a, rfl⟩ := hA x hx
    exact (Units.mul_right_inj a).mp (h.trans (mul_zero _).symm))⟩
  let P := CommAlgCat.of F (Polynomial F)
  let X : (additivePoints F).obj P := Multiplicative.ofAdd (Polynomial.X : Polynomial F)
  let x := v P (c.app P X)
  let e : P ⊗[F] A ≃ₐ[F] Polynomial A :=
    (Algebra.TensorProduct.comm F (Polynomial F) A).trans (polyEquivTensor F A).symm
  have hunit : IsUnit (e x) := ((Group.isUnit (c.app P X)).map (v P)).map e.toMonoidHom
  have hconst : x = (1 : P) ⊗ₜ[F] (e x).coeff 0 := by
    apply e.injective
    change e x = (polyEquivTensor F A).symm ((e x).coeff 0 ⊗ₜ[F] (1 : Polynomial F))
    rw [polyEquivTensor_symm_apply_tmul_eq_smul]
    simpa only [Polynomial.map_one, Polynomial.smul_eq_C_mul, mul_one] using
      Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit hunit)
  have eval (t : R) : v R (c.app R (Multiplicative.ofAdd t)) =
      (1 : R) ⊗ₜ[F] (e x).coeff 0 := by
    let a : P ⟶ R := CommAlgCat.ofHom (Polynomial.aeval t)
    have ht : (additivePoints F).map a X =
        (Multiplicative.ofAdd t : (additivePoints F).obj R) :=
      congrArg Multiplicative.ofAdd (Polynomial.aeval_X t)
    have hc := ConcreteCategory.congr_hom (c.naturality a) X
    change c.app R ((additivePoints F).map a X) = H.map a (c.app P X) at hc
    change v R (c.app R (Multiplicative.ofAdd t : (additivePoints F).obj R)) = _
    rw [← ht, hc, hn]
    change Algebra.TensorProduct.map a.hom (AlgHom.id F A) x = _
    conv_lhs => rw [hconst]
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  have hzero : Multiplicative.ofAdd (0 : R) = (1 : Multiplicative R) := rfl
  have hzero' : c.app R (Multiplicative.ofAdd (0 : R)) = 1 :=
    (congrArg (c.app R).hom hzero).trans ((c.app R).hom.map_one)
  exact (hv R) ((eval r).trans ((eval 0).symm.trans (congrArg (v R) hzero')))


open Matrix

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000


private abbrev I := ULift.{u} (Fin 2)
private def first : I.{u} := ⟨0⟩
private def second : I.{u} := ⟨1⟩
private theorem first_ne_second : first.{u} ≠ second.{u} := by decide

private def diagonalEntries {R : Type u} [CommRing R] (t : Rˣ) (j : I.{u}) : R :=
  if j = first then (↑t : R) else ↑t⁻¹

private def diagonalSL {R : Type u} [CommRing R] : Rˣ →* SpecialLinearGroup I.{u} R where
  toFun t := ⟨diagonal (diagonalEntries t), by
    rw [det_diagonal]
    calc
      ∏ j, diagonalEntries t j = ∏ j : Fin 2, diagonalEntries t ⟨j⟩ :=
        Fintype.prod_equiv (Equiv.ulift : I.{u} ≃ Fin 2) (diagonalEntries t)
          (fun j => diagonalEntries t ⟨j⟩) (fun _ => rfl)
      _ = 1 := by
        rw [Fin.prod_univ_two]
        simp [diagonalEntries, first]⟩
  map_one' := by
    apply Subtype.ext
    change diagonal (diagonalEntries (1 : Rˣ)) = 1
    rw [diagonal_eq_one]
    funext j
    simp [diagonalEntries]
  map_mul' t s := by
    apply Subtype.ext
    change diagonal (diagonalEntries (t * s)) =
      diagonal (diagonalEntries t) * diagonal (diagonalEntries s)
    rw [diagonal_mul_diagonal]
    congr
    ext j
    by_cases h : j = first
    · simp [diagonalEntries, h]
    · simp [diagonalEntries, h, mul_comm]

private theorem diagonalSL_natural {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (t : Rˣ) :
    SpecialLinearGroup.map f (diagonalSL t) = diagonalSL (Units.map f.toMonoidHom t) := by
  apply Subtype.ext
  change (diagonal (diagonalEntries t)).map f =
    diagonal (diagonalEntries (Units.map f.toMonoidHom t))
  rw [diagonal_map f.map_zero]
  congr
  ext j
  by_cases h : j = first <;> simp [diagonalEntries, h, ← map_inv]

private def upperTransvection {R : Type u} [CommRing R] :
    SpecialLinearGroup I.{u} R := SpecialLinearGroup.transvection first_ne_second 1

private theorem not_commute_diagonalSL {R : Type u} [CommRing R] (t : Rˣ)
    (h : (↑t : R) ≠ ↑t⁻¹) : ¬ Commute upperTransvection (diagonalSL t) := by
  intro eq
  apply h
  have he := congrArg (fun x : SpecialLinearGroup I.{u} R => x.val first second) eq.eq
  change ((upperTransvection (R := R)).val * diagonal (diagonalEntries t)) first second =
    (diagonal (diagonalEntries t) * (upperTransvection (R := R)).val) first second at he
  rw [mul_diagonal, diagonal_mul] at he
  simpa [diagonalEntries, upperTransvection, SpecialLinearGroup.transvection_coe, first_ne_second, first_ne_second.symm] using he.symm


open CharacterDescent (Cocharacter)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open StandardGroups (multiplicativePoints specialLinearPoints)
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Opposite

open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private integerPointsIso from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

private def diagonalPoints : multiplicativePoints F ⟶ specialLinearPoints F I.{u} where
  app _ := GrpCat.ofHom diagonalSL
  naturality R S f := by
    apply GrpCat.ext
    intro t
    exact (diagonalSL_natural f.hom.toRingHom t).symm

/-- In a split SL₂ the diagonal cocharacter fails to commute with the upper
transvection at the universal Laurent unit, including in characteristic two. -/
theorem noncentralCocharacter_of_splitSL2 (H : AffineAlgebraicGroup F)
    (s : (groupPointsFunctor F).obj H.val ≅ specialLinearPoints F I.{u}) :
    ∃ (c : Cocharacter H.val) (Y : SchemeOver F) (g : Y ⟶ H.val.X),
      ¬ Centralizes c g := by
  let M := specGroup (groupAlgebra F IntegerCharacters)
  let e := LinearAlgebraicGroups.DiagonalizableGroups.groupAlgebraPointsIso F IntegerCharacters
    ≪≫ integerPointsIso
  let ψ := e.hom ≫ diagonalPoints (F := F) ≫ s.inv
  have hM : IsAffine M.X.left :=
    (DiagonalizableGroups.diagonalGroup F IntegerCharacters).property.1
  let c : Cocharacter H.val := (groupHomEquiv M H.val hM).symm ψ
  have hc : (groupPointsFunctor F).map c = ψ :=
    (groupHomEquiv M H.val hM).apply_symm_apply ψ
  let R := CommAlgCat.of F (LaurentPolynomial F)
  let Y := (testSpec F).obj (op R)
  let t : Rˣ := {
    val := LaurentPolynomial.T 1
    inv := LaurentPolynomial.T (-1)
    val_inv := by rw [← LaurentPolynomial.T_add]; norm_num
    inv_val := by rw [← LaurentPolynomial.T_add]; norm_num }
  have ht : (↑t : R) ≠ ↑t⁻¹ := by
    intro h
    change (LaurentPolynomial.T 1 : LaurentPolynomial F) = LaurentPolynomial.T (-1) at h
    have hz := congrArg (fun p : LaurentPolynomial F => p.coeff (1 : ℤ)) h
    have h1 : (1 : ℤ) ≠ -1 := by decide
    simp only [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne h1] at hz
    exact one_ne_zero hz
  let g : Points H.val.X R := s.inv.app R upperTransvection
  let p : Points M.X R := e.inv.app R t
  refine ⟨c, Y, g, fun h => ?_⟩
  have heq : Commute g (p ≫ c.hom.hom) := by
    simpa only [Category.id_comp] using (centralizes_iff c g).mp h Y (𝟙 Y) p
  have hmat := heq.map (s.hom.app R).hom
  have hg : s.hom.app R g = upperTransvection :=
    ConcreteCategory.congr_hom (s.inv_hom_id_app R) upperTransvection
  have hp : s.hom.app R (p ≫ c.hom.hom) = diagonalSL t := by
    change s.hom.app R (((groupPointsFunctor F).map c).app R p) = _
    rw [hc]
    change s.hom.app R (s.inv.app R (diagonalSL (e.hom.app R (e.inv.app R t)))) = _
    have h₁ := ConcreteCategory.congr_hom (s.inv_hom_id_app R)
      (diagonalSL (e.hom.app R (e.inv.app R t)))
    have h₂ := ConcreteCategory.congr_hom (e.inv_hom_id_app R) t
    exact h₁.trans (congrArg diagonalSL h₂)
  change Commute (s.hom.app R g) (s.hom.app R (p ≫ c.hom.hom)) at hmat
  rw [hg, hp] at hmat
  exact not_commute_diagonalSL t ht hmat

open scoped MatrixGroups
open _root_.RM03.CSA.NormOneGroup (innerAut)

private def lowerTransvection {R : Type u} [CommRing R] :
    SpecialLinearGroup I.{u} R := SpecialLinearGroup.transvection first_ne_second.symm 1

private def extendFromTransvections {R : Type u} [CommRing R]
    (upper lower m : Matrix I.{u} I.{u} R) : Matrix I.{u} I.{u} R :=
  m second second • 1 + m first second • (upper - 1) + m second first • (lower - 1) +
    (m first first - m second second) • ((upper - 1) * (lower - 1))

private theorem extendFromTransvections_self {R : Type u} [CommRing R]
    (m : Matrix I.{u} I.{u} R) :
    extendFromTransvections upperTransvection.val lowerTransvection.val m = m := by
  have hu : (upperTransvection.val : Matrix I.{u} I.{u} R) - 1 = single first second 1 :=
    add_sub_cancel_left 1 _
  have hl : (lowerTransvection.val : Matrix I.{u} I.{u} R) - 1 = single second first 1 :=
    add_sub_cancel_left 1 _
  rw [extendFromTransvections, hu, hl, single_mul_single_same, one_mul]
  ext ⟨i⟩ ⟨j⟩
  fin_cases i <;> fin_cases j <;>
    simp [first, second, Matrix.single, Matrix.of_apply]

private theorem map_extendFromTransvections {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a b m : Matrix I.{u} I.{u} R) :
    (extendFromTransvections a b m).map f =
      extendFromTransvections (a.map f) (b.map f) (m.map f) := by
  change f.mapMatrix (extendFromTransvections a b m) =
    extendFromTransvections (f.mapMatrix a) (f.mapMatrix b) (f.mapMatrix m)
  have hsmul (r : R) (m : Matrix I.{u} I.{u} R) :
      f.mapMatrix (r • m) = f r • f.mapMatrix m := by
    ext i j
    exact f.map_mul r (m i j)
  simp only [extendFromTransvections, map_add, hsmul, map_one, map_mul, map_sub]
  rfl

private theorem algHom_extendFromTransvections {R : Type u} [CommRing R]
    (f : Matrix I.{u} I.{u} R →ₐ[R] Matrix I.{u} I.{u} R)
    (m : Matrix I.{u} I.{u} R) :
    extendFromTransvections (f upperTransvection.val) (f lowerTransvection.val) m = f m := by
  have h := congrArg f (extendFromTransvections_self m)
  simpa only [extendFromTransvections, map_add, map_sub, map_one, map_mul, map_smul] using h

private theorem map_upperTransvection {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    SpecialLinearGroup.map f (upperTransvection (R := R)) = upperTransvection := by
  apply Subtype.ext
  change (upperTransvection.val : Matrix I.{u} I.{u} R).map f = _
  simp [upperTransvection, SpecialLinearGroup.transvection_coe, Matrix.map_add,
    Matrix.map_one f f.map_zero f.map_one, Matrix.map_single _ _ _ f]

private theorem map_lowerTransvection {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    SpecialLinearGroup.map f (lowerTransvection (R := R)) = lowerTransvection := by
  apply Subtype.ext
  change (lowerTransvection.val : Matrix I.{u} I.{u} R).map f = _
  simp [lowerTransvection, SpecialLinearGroup.transvection_coe, Matrix.map_add,
    Matrix.map_one f f.map_zero f.map_one, Matrix.map_single _ _ _ f]

/-- A natural automorphism which is matrix conjugation after a field
extension acts over every test algebra by extension of a matrix algebra
automorphism over the ground field. -/
private theorem matrixAlgebraAutomorphism_of_local_conjugation
    {L : Type u} [Field L] [Algebra F L]
    (a : Aut (specialLinearPoints F I.{u})) (b : GL I.{u} L)
    (hb : ∀ (R : TestAlgebra F) (j : L →ₐ[F] R) (x : SpecialLinearGroup I.{u} R),
      (a.asIso.hom.app R x).val = (innerAut (R := R) (GeneralLinearGroup.map j.toRingHom b)) x.val) :
    ∃ e : Matrix I.{u} I.{u} F ≃ₐ[F] Matrix I.{u} I.{u} F,
      ∀ (R : TestAlgebra F) (x : SpecialLinearGroup I.{u} R),
        (a.asIso.hom.app R x).val =
          extendFromTransvections ((e upperTransvection.val).map (algebraMap F R))
            ((e lowerTransvection.val).map (algebraMap F R)) x.val := by
  let R₀ := CommAlgCat.of F F
  let U := (a.asIso.hom.app R₀ upperTransvection).val
  let V := (a.asIso.hom.app R₀ lowerTransvection).val
  let ψ := extendFromTransvections U V
  have hNat {R S : TestAlgebra F} (f : R ⟶ S) (x : SpecialLinearGroup I.{u} R) :
      (a.asIso.hom.app S (SpecialLinearGroup.map f.hom.toRingHom x)).val =
        ((a.asIso.hom.app R x).val).map f.hom := by
    exact congrArg Subtype.val (ConcreteCategory.congr_hom (a.asIso.hom.naturality f) x)
  have hψ (R : TestAlgebra F) (j : L →ₐ[F] R) (m : Matrix I.{u} I.{u} R) :
      extendFromTransvections (U.map (algebraMap F R)) (V.map (algebraMap F R)) m =
        innerAut (R := R) (GeneralLinearGroup.map j.toRingHom b) m := by
    let f : R₀ ⟶ R := CommAlgCat.ofHom (Algebra.ofId F R)
    have hu := hNat f (upperTransvection (R := R₀))
    have hl := hNat f (lowerTransvection (R := R₀))
    rw [map_upperTransvection] at hu
    rw [map_lowerTransvection] at hl
    change (a.asIso.hom.app R upperTransvection).val = U.map (algebraMap F R) at hu
    change (a.asIso.hom.app R lowerTransvection).val = V.map (algebraMap F R) at hl
    rw [← hu, ← hl, hb R j, hb R j]
    exact algHom_extendFromTransvections (innerAut (R := R) _).toAlgHom m
  let coeff := (algebraMap F L).mapMatrix (m := I.{u})
  have hι : Function.Injective coeff := fun _ _ h => Matrix.ext fun i j =>
    (algebraMap F L).injective (congrFun (congrFun h i) j)
  let φ := innerAut (R := L) b
  have hcompat (m : Matrix I.{u} I.{u} F) : coeff (ψ m) = φ (coeff m) := by
    rw [show coeff (ψ m) = _ from map_extendFromTransvections (algebraMap F L) U V m]
    have hi : GeneralLinearGroup.map ((AlgHom.id L L).restrictScalars F).toRingHom b = b := by
      apply Units.ext
      rfl
    have hh := hψ (CommAlgCat.of F L) ((AlgHom.id L L).restrictScalars F) (coeff m)
    rw [hi] at hh
    exact hh
  let f : Matrix I.{u} I.{u} F →ₐ[F] Matrix I.{u} I.{u} F :=
    { toFun := ψ
      map_one' := hι (by rw [hcompat, map_one, map_one])
      map_zero' := hι (by rw [hcompat, map_zero, map_zero])
      map_add' := fun x y => hι (by rw [hcompat, map_add, map_add, map_add, hcompat, hcompat])
      map_mul' := fun x y => hι (by rw [hcompat, map_mul, map_mul, map_mul, hcompat, hcompat])
      commutes' := fun x => hι (by
        have h : coeff (algebraMap F (Matrix I.{u} I.{u} F) x) =
            algebraMap L (Matrix I.{u} I.{u} L) (algebraMap F L x) := by
          ext i j
          by_cases hij : i = j <;> simp [coeff, Matrix.algebraMap_matrix_apply, hij]
        rw [hcompat, h, φ.commutes]) }
  have hf : Function.Injective f := fun x y h => hι (φ.injective (by
    rw [← hcompat, ← hcompat]
    exact congrArg coeff h))
  let e := AlgEquiv.ofBijective f ⟨hf,
    (LinearMap.injective_iff_surjective (f := f.toLinearMap)).mp hf⟩
  refine ⟨e, fun R x => ?_⟩
  let D := R ⊗[F] L
  let j : R →ₐ[F] D := Algebra.TensorProduct.includeLeft
  let k : L →ₐ[F] D := Algebra.TensorProduct.includeRight
  let S := CommAlgCat.of F D
  have hj : Function.Injective j :=
    Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F L).injective
  apply (show Function.Injective (j.toRingHom.mapMatrix (m := I.{u})) from
    fun _ _ h => Matrix.ext fun i j => hj (congrFun (congrFun h i) j))
  change ((a.asIso.hom.app R x).val).map j =
    (extendFromTransvections ((f upperTransvection.val).map (algebraMap F R))
      ((f lowerTransvection.val).map (algebraMap F R)) x.val).map j
  have hnat := hNat (R := R) (S := S) (CommAlgCat.ofHom j) x
  change (a.asIso.hom.app S (SpecialLinearGroup.map j.toRingHom x)).val =
    ((a.asIso.hom.app R x).val).map j at hnat
  rw [← hnat]
  have hm := map_extendFromTransvections j.toRingHom
    ((f upperTransvection.val).map (algebraMap F R)) ((f lowerTransvection.val).map (algebraMap F R)) x.val
  change _ = (extendFromTransvections ((f upperTransvection.val).map (algebraMap F R))
    ((f lowerTransvection.val).map (algebraMap F R)) x.val).map j.toRingHom
  rw [hm, Matrix.map_map, Matrix.map_map]
  have hjF : j.toRingHom.comp (algebraMap F R) = algebraMap F D := by
    ext x
    exact j.commutes x
  change (a.asIso.hom.app S (SpecialLinearGroup.map j.toRingHom x)).val =
     extendFromTransvections ((f upperTransvection.val).map (j.toRingHom.comp (algebraMap F R)))
       ((f lowerTransvection.val).map (j.toRingHom.comp (algebraMap F R))) (x.val.map j)
  rw [hjF]
  have hu : f upperTransvection.val = U := by
    change extendFromTransvections U V upperTransvection.val = U
    simp [extendFromTransvections, upperTransvection, SpecialLinearGroup.transvection_coe,
      Matrix.single, Matrix.of_apply, first_ne_second, first_ne_second.symm]
  have hl : f lowerTransvection.val = V := by
    change extendFromTransvections U V lowerTransvection.val = V
    simp [extendFromTransvections, lowerTransvection, SpecialLinearGroup.transvection_coe,
      Matrix.single, Matrix.of_apply, first_ne_second, first_ne_second.symm]
  rw [hu, hl, hψ S k]
  exact hb S k (SpecialLinearGroup.map j.toRingHom x)

/-- Field-local conjugation of an automorphism of SL₂ descends to conjugation
by an invertible matrix over the field. -/
private theorem matrixConjugation_of_local_conjugation
    {L : Type u} [Field L] [Algebra F L]
    (a : Aut (specialLinearPoints F I.{u})) (b : GL I.{u} L)
    (hb : ∀ (R : TestAlgebra F) (j : L →ₐ[F] R) (x : SpecialLinearGroup I.{u} R),
      (a.asIso.hom.app R x).val = (innerAut (R := R) (GeneralLinearGroup.map j.toRingHom b)) x.val) :
    ∃ c : GL I.{u} F, ∀ (R : TestAlgebra F) (x : SpecialLinearGroup I.{u} R),
      (a.asIso.hom.app R x).val =
        (innerAut (R := R) (GeneralLinearGroup.map (algebraMap F R) c)) x.val := by
  obtain ⟨e, he⟩ := matrixAlgebraAutomorphism_of_local_conjugation a b hb
  have hA : isCentralSimple F (Matrix I.{u} I.{u} F) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨c, hc⟩ := _root_.RM03.CSA.algEquiv_isInner hA e
  refine ⟨c, fun R x => (he R x).trans ?_⟩
  have h (m : Matrix I.{u} I.{u} F) :
      (e m).map (algebraMap F R) =
        (innerAut (R := R) (GeneralLinearGroup.map (algebraMap F R) c))
          (m.map (algebraMap F R)) := by
    rw [hc m]
    exact (((algebraMap F R).mapMatrix.map_mul _ _).trans
      (congrArg (· * _) ((algebraMap F R).mapMatrix.map_mul _ _)))
  have hu := h upperTransvection.val
  have hl := h lowerTransvection.val
  have hu' := congrArg Subtype.val
    (map_upperTransvection (R := F) (S := R) (algebraMap F R))
  have hl' := congrArg Subtype.val
    (map_lowerTransvection (R := F) (S := R) (algebraMap F R))
  change (upperTransvection.val : Matrix I.{u} I.{u} F).map (algebraMap F R) = _ at hu'
  change (lowerTransvection.val : Matrix I.{u} I.{u} F).map (algebraMap F R) = _ at hl'
  rw [hu, hl, hu', hl']
  exact algHom_extendFromTransvections (innerAut (R := R) _).toAlgHom x.val


open Specs.Pinning (PinnedGroup AttachedDatum)
open Specs.SpecialLinearDatum
open Specs.GeometricBorelConjugacy (IsQuasiSplit)

/-- The sole simple coroot generates the cocharacter lattice of the pinned matrix SL₂. -/
private theorem basedAutomorphism_eq_one
    {G : AffineAlgebraicGroup F} {s : GeneralLinearStructure.SpecialMatrixPoints G 2}
    {T : DiagonalTorus (r := 1) s} {L : LatticeIdentification T} {M : RootIdentification T L}
    (B : UpperTriangularBorel T L M) (D : AttachedDatum B.pair) (a : Aut D.toBased) :
    a = 1 := by
  letI := D.comm
  have hD := LinearAlgebraicGroups.RootData.SpecialLinearDatum.matrixBasedDatum_of_attachedDatum B D
  let p : RootIndices 2 := ⟨(0, 1), by decide⟩
  let α : D.toBased.I := M.indices p
  have hbase (i : D.toBased.I) : i ∈ D.toBased.base.support ↔ i = α := by
    change i ∈ D.base.support ↔ i = α
    obtain ⟨q, rfl⟩ := M.indices.surjective i
    rw [hD.2, M.indices.injective.eq_iff]
    constructor
    · rintro ⟨j, h₁, h₂⟩
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      apply Subtype.ext
      exact Prod.ext h₁ h₂
    · rintro rfl
      exact ⟨0, rfl, rfl⟩
  let f := a.asIso.hom.val
  have hf : f.indexEquiv α = α := (hbase _).mp (by
    have hm : f.indexEquiv α ∈ f.indexEquiv '' (D.toBased.base.support : Set D.toBased.I) :=
      ⟨α, (hbase α).mpr rfl, rfl⟩
    change f.indexEquiv α ∈ (D.toBased.base.support : Set D.toBased.I)
    exact a.asIso.hom.property ▸ hm)
  have hα : f.toHom.coweightMap (D.toBased.datum.coroot α) = D.toBased.datum.coroot α := by
    have hm := RootPairing.Hom.coroot_coweightMap_apply _ _ (f.indexEquiv α) f.toHom
    rw [Equiv.symm_apply_apply, hf] at hm
    exact hm
  obtain ⟨_, y, _, hy, _, _⟩ := LinearAlgebraicGroups.RootData.SpecialLinearDatum.sizeTwoLattices
  let z : D.toBased.Y ≃ₗ[ℤ] ℤ := L.cocharacters.trans y
  have hz : z (D.toBased.datum.coroot α) = 1 := by
    change y (L.cocharacters (D.datum.rootDatum.coroot (M.indices p))) = 1
    rw [hD.1]
    exact hy
  have span (v : D.toBased.Y) : z v • D.toBased.datum.coroot α = v := by
    apply z.injective
    rw [map_smul, hz, smul_eq_mul, mul_one]
  apply Aut.ext
  apply Iso.ext
  apply Subtype.ext
  apply (RootPairing.Equiv.coweightHom_injective D.toBased.datum)
  apply MulOpposite.unop_injective
  apply LinearEquiv.toLinearMap_injective
  change f.toHom.coweightMap = LinearMap.id
  apply LinearMap.ext
  intro v
  change f.toHom.coweightMap v = v
  calc
    f.toHom.coweightMap v = f.toHom.coweightMap (z v • D.toBased.datum.coroot α) :=
      congrArg f.toHom.coweightMap (span v).symm
    _ = v := by rw [map_smul, hα, span]

/-- Both quasi-split models lie in the sole outer fibre of the split pinning. -/
private theorem quasiSplitForm_is_split
    {S : Type u} [Field S] [Algebra F S] [IsSepClosure F S]
    (G H : AffineAlgebraicGroup F) (s : GeneralLinearStructure.SpecialMatrixPoints G 2)
    (hH : Nonempty ((groupBaseChange F S).obj G.val ≅ (groupBaseChange F S).obj H.val))
    (hq : IsQuasiSplit H) :
    Nonempty (G.val ≅ H.val) := by
  obtain ⟨T, L, M, B, _, _, hp, _⟩ :=
    LinearAlgebraicGroups.RootData.SpecialLinearDatum.matrixPinnedDatum F 1 G s
  obtain ⟨A, U, _, _, pin, _⟩ := hp
  let P : PinnedGroup A := ⟨B.pair, U, pin⟩
  obtain ⟨D, _, _, Seq, _, C, h, _, _, _, hclass⟩ :=
    LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.quasiSplitInnerForms (S := S) P
  letI : Subsingleton (Aut D.toBased) :=
    ⟨fun a b => (basedAutomorphism_eq_one B D a).trans (basedAutomorphism_eq_one B D b).symm⟩
  letI : TopologicalSpace (Specs.AutomorphismSequence.RelativeAut P.pair.G.val
      (Specs.RelativeFormComparison.fieldTest F S)) := ⊥
  letI : TopologicalSpace (Aut D.toBased) := ⊥
  letI : DiscreteTopology (Specs.AutomorphismSequence.RelativeAut P.pair.G.val
      (Specs.RelativeFormComparison.fieldTest F S)) := ⟨rfl⟩
  letI : TopologicalSpace (Gal(S/F)) := krullTopology F S
  let G' : LinearAlgebraicGroups.Descent.Forms.SchemeModels S G := ⟨G, ⟨Iso.refl _⟩⟩
  let H' : LinearAlgebraicGroups.Descent.Forms.SchemeModels S G := ⟨H, hH⟩
  let g : LinearAlgebraicGroups.Descent.Forms.SchemeFormClasses S G := Quotient.mk _ G'
  let j : LinearAlgebraicGroups.Descent.Forms.SchemeFormClasses S G := Quotient.mk _ H'
  let x := QuasiSplitInnerForms.mapH1 (QuasiSplitInnerForms.outerHom (S := S) Seq)
    continuous_of_discreteTopology h.1 (C.equiv g)
  have eq (a b : LinearAlgebraicGroups.Descent.NonabelianCohomology.H1
      (QuasiSplitInnerForms.trivialOuterAction (k := F) (S := S) D.toBased)) : a = b := by
    induction a using Quotient.inductionOn with
    | _ a =>
      induction b using Quotient.inductionOn with
      | _ b =>
        have : a = b := Subtype.ext (funext fun _ => Subsingleton.elim _ _)
        subst b
        rfl
  have hg := (hclass x g).mp ⟨rfl, G', rfl, B.reductive, B.limits.parabolic, B.isBorel⟩
  have hj := (hclass x j).mp ⟨eq _ _, H', rfl, hq⟩
  exact Quotient.exact (C.equiv.injective (hg.trans hj.symm))

open Specs.AutomorphismSequence (scalarAut)
open LinearAlgebraicGroups.Descent.InnerTypeA.Specification
open private affineGroupIso affineGroupIso_hom affine_baseChange baseChangePointIso affineLift
  from LinearAlgebraicGroups.Descent.InnerTypeA

private theorem affineFieldLift {X Y : AffineAlgebraicGroup F} (q : X.val ⟶ Y.val)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (p : Points Y.val.X (CommAlgCat.of F F)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L)
      (g : Points X.val.X (CommAlgCat.of F L)),
      g ≫ q.hom.hom = mapPoints (CommAlgCat.ofHom (Algebra.ofId F L)) p := by
  obtain ⟨R, f, x, _, hs, hx⟩ := affineLift X.property.1 Y.property.1 q.hom.hom p
  change Surjective (Spec.map (CommRingCat.ofHom f.hom.toRingHom)) at hs
  letI := hs
  obtain ⟨v, _⟩ := (Spec.map (CommRingCat.ofHom f.hom.toRingHom)).surjective
    (IsLocalRing.closedPoint F)
  let L := v.asIdeal.ResidueField
  let j : R ⟶ CommAlgCat.of F L := CommAlgCat.ofHom (IsScalarTower.toAlgHom F R L)
  refine ⟨L, inferInstance, inferInstance, mapPoints j x, ?_⟩
  have hfj : f ≫ j = CommAlgCat.ofHom (Algebra.ofId F L) := by
    ext
  change ((testSpec F).map j.op ≫ x) ≫ q.hom.hom = _
  rw [Category.assoc, hx]
  change (testSpec F).map j.op ≫ (testSpec F).map f.op ≫ p =
    (testSpec F).map (CommAlgCat.ofHom (Algebra.ofId F L)).op ≫ p
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp, hfj]

private theorem exists_splitSL2 (F : Type u) [Field F] :
    ∃ G : AffineAlgebraicGroup F, Nonempty (GeneralLinearStructure.SpecialMatrixPoints G 2) := by
  obtain ⟨_, sl, hsl⟩ :=
    LinearAlgebraicGroups.StandardGroups.specialLinearGroupSpecification F I.{u}
  obtain ⟨_, _, _, _, _, _, _, hpoints⟩ := hsl
  letI := sl.hopf
  exact ⟨_, ⟨hpoints.choose_spec.2.choose⟩⟩

/-- Use the adjoint image in the automorphism sheaf, then descend matrix conjugation
from a field lifting its adjoint point. -/
private theorem matrixConjugation (a : Aut (specialLinearPoints F I.{u})) :
    ∃ c : GL I.{u} F, ∀ (R : TestAlgebra F) (x : SpecialLinearGroup I.{u} R),
      (a.asIso.hom.app R x).val =
        (innerAut (R := R) (GeneralLinearGroup.map (algebraMap F R) c)) x.val := by
  obtain ⟨G, ⟨s⟩⟩ := exists_splitSL2 F
  let b := affineGroupIso G.property.1 G.property.1 (s ≪≫ a.asIso ≪≫ s.symm)
  have hb := affineGroupIso_hom G.property.1 G.property.1 (s ≪≫ a.asIso ≪≫ s.symm)
  obtain ⟨T, L, M, B, _, _, hp, _⟩ :=
    LinearAlgebraicGroups.RootData.SpecialLinearDatum.matrixPinnedDatum F 1 G s
  obtain ⟨A, U, _, _, pin, _⟩ := hp
  let P : PinnedGroup A := ⟨B.pair, U, pin⟩
  obtain ⟨D, l, Q, Seq, _, _⟩ :=
    LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.automorphismSequences P
  letI : Subsingleton (Aut D.toBased) :=
    ⟨fun a b => (basedAutomorphism_eq_one B D a).trans (basedAutomorphism_eq_one B D b).symm⟩
  let V := (testSpec F).obj (op (CommAlgCat.of F F))
  let f := scalarAut (Aut.of b) V
  have hout : Seq.outer.app (op V) f = 1 := by
    apply ULift.ext
    apply LocallyConstant.ext
    intro t
    exact Subsingleton.elim _ _
  obtain ⟨p, hp⟩ := (Seq.exact (op V) f).mp hout
  letI := Q.fppf.1
  letI := Q.fppf.2.1
  obtain ⟨L', _, _, g, hg⟩ := affineFieldLift Q.projection p.down
  let v := (testSpec F).map (CommAlgCat.ofHom (Algebra.ofId F L')).op
  have he := ConcreteCategory.congr_hom (Seq.inner.naturality v.op) p
  change Seq.inner.app _ ⟨mapPoints (CommAlgCat.ofHom (Algebra.ofId F L')) p.down⟩ =
    Specs.AutomorphismSequence.restrictAut v (Seq.inner.app (op V) p) at he
  rw [hp, ← hg, Seq.onLift] at he
  apply matrixConjugation_of_local_conjugation a
    (SpecialLinearGroup.toGL (s.hom.app (CommAlgCat.of F L') g))
  intro R j x
  let W : Over ((testSpec F).obj (op (CommAlgCat.of F L'))) :=
    Over.mk ((testSpec F).map (CommAlgCat.ofHom j).op)
  let z : Points G.val.X R := s.inv.app R x
  let gj : Points G.val.X R := mapPoints (CommAlgCat.ofHom j) g
  have hApp := congrArg
    (fun b : Specs.AutomorphismSequence.RelativeAut G.val _ => b.asIso.hom.app (op W)) he
  have ee := ConcreteCategory.congr_hom hApp z
  change gj * z * gj⁻¹ =
    ((groupPointsFunctor F).map b.hom).app R z at ee
  rw [hb] at ee
  have h := congrArg (fun w => (s.hom.app R w : SpecialLinearGroup I.{u} R).val) ee
  have hs := ConcreteCategory.congr_hom (s.inv_hom_id_app R) x
  have hm := ConcreteCategory.congr_hom (s.hom.naturality (CommAlgCat.ofHom j)) g
  change s.hom.app R (mapPoints (CommAlgCat.ofHom j) g) =
    SpecialLinearGroup.map j.toRingHom (s.hom.app (CommAlgCat.of F L') g) at hm
  change s.hom.app R gj = _ at hm
  simp only [map_mul, map_inv, hm, show s.hom.app R z = x from hs] at h
  have h' := ConcreteCategory.congr_hom (s.inv_hom_id_app R) (a.asIso.hom.app R x)
  change _ = (s.hom.app R (s.inv.app R (a.asIso.hom.app R (s.hom.app R z)))).val at h
  change s.hom.app R (s.inv.app R (a.asIso.hom.app R x)) = a.asIso.hom.app R x at h'
  rw [show s.hom.app R z = x from hs, h'] at h
  let m := SpecialLinearGroup.map j.toRingHom (s.hom.app (CommAlgCat.of F L') g)
  have hm' : GeneralLinearGroup.map j.toRingHom
      (SpecialLinearGroup.toGL (s.hom.app (CommAlgCat.of F L') g)) =
        SpecialLinearGroup.toGL m := by
    apply Units.ext
    rfl
  rw [hm']
  change (a.asIso.hom.app R x).val = m.val * x.val *
    ((SpecialLinearGroup.toGL m)⁻¹ : GL I.{u} R).val
  rw [← map_inv]
  exact h.symm

section GaloisDescent

variable {K : Type u} [Field K] [Algebra F K]

open private twistTestAlgebra twistIdentity twistMap twistIdentity_comm testAlgebraHom
  from LinearAlgebraicGroups.Descent.InnerTypeA

private abbrev untwistTest (σ : Gal(K/F)) (R : TestAlgebra K) :=
  twistTestAlgebra σ⁻¹ R

private def untwist (σ : Gal(K/F)) (R : TestAlgebra K) :
    restrictTestAlgebraObj F K (untwistTest σ R) ⟶ restrictTestAlgebraObj F K R :=
  testAlgebraHom (RingHom.id R) (fun a => congrArg (algebraMap K R) ((σ⁻¹).symm.commutes a))

private def untwistIso (σ : Gal(K/F)) (R : TestAlgebra K) :
    restrictTestAlgebraObj F K (untwistTest σ R) ≅ restrictTestAlgebraObj F K R where
  hom := untwist σ R
  inv := twistIdentity σ⁻¹ R
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

private def semilinearAutomorphism (H : GroupScheme F)
    (z : restrictTestAlgebra F K ⋙ (groupPointsFunctor F).obj H ≅
      specialLinearPoints K I.{u}) (σ : Gal(K/F)) :
    Aut (specialLinearPoints K I.{u}) :=
  Aut.of (NatIso.ofComponents (fun R =>
    (z.app (untwistTest σ R)).symm ≪≫
      ((groupPointsFunctor F).obj H).mapIso (untwistIso σ R) ≪≫ z.app R)
    (by
      intro R S f
      let g := twistMap σ⁻¹ f
      have hu : (restrictTestAlgebra F K).map g ≫ untwist σ S =
          untwist σ R ≫ (restrictTestAlgebra F K).map f := by ext; rfl
      change (specialLinearPoints K I.{u}).map f ≫
          (z.inv.app (untwistTest σ S) ≫ _ ≫ z.hom.app S) =
        (z.inv.app (untwistTest σ R) ≫ _ ≫ z.hom.app R) ≫
          (specialLinearPoints K I.{u}).map f
      have hinv := z.inv.naturality g
      have hhom := z.hom.naturality f
      change (specialLinearPoints K I.{u}).map f ≫ z.inv.app (untwistTest σ S) =
        z.inv.app (untwistTest σ R) ≫ ((groupPointsFunctor F).obj H).map
          ((restrictTestAlgebra F K).map g) at hinv
      simp only [Category.assoc]
      rw [reassoc_of% hinv, ← hhom]
      let P := (groupPointsFunctor F).obj H
      change z.inv.app (untwistTest σ R) ≫ P.map ((restrictTestAlgebra F K).map g) ≫
          P.map (untwist σ S) ≫ z.hom.app S =
        z.inv.app (untwistTest σ R) ≫ P.map (untwist σ R) ≫
          P.map ((restrictTestAlgebra F K).map f) ≫ z.hom.app S
      rw [← P.map_comp_assoc, ← P.map_comp_assoc, hu]))

private theorem semilinear_matrix_formula (H : GroupScheme F)
    (z : restrictTestAlgebra F K ⋙ (groupPointsFunctor F).obj H ≅
      specialLinearPoints K I.{u}) (σ : Gal(K/F))
    (b : GL I.{u} K)
    (hb : ∀ (R : TestAlgebra K) (x : SpecialLinearGroup I.{u} R),
      ((semilinearAutomorphism H z σ).asIso.hom.app R x).val =
        (innerAut (R := R) (GeneralLinearGroup.map (algebraMap K R) b)) x.val)
    {R S : TestAlgebra K} (f : restrictTestAlgebraObj F K R ⟶ restrictTestAlgebraObj F K S)
    (hf : ∀ a : K, f.hom (algebraMap K R a) = algebraMap K S (σ a))
    (x : Points H.X (restrictTestAlgebraObj F K R)) :
    (z.hom.app S (mapPoints f x)).val =
      (innerAut (R := S) (GeneralLinearGroup.map (algebraMap K S) b))
        ((z.hom.app R x).val.map f.hom) := by
  let g : R ⟶ untwistTest σ S := testAlgebraHom f.hom.toRingHom hf
  have hg : (restrictTestAlgebra F K).map g ≫ untwist σ S = f := by ext; rfl
  have hn := ConcreteCategory.congr_hom (z.hom.naturality g) x
  change z.hom.app (untwistTest σ S) (mapPoints ((restrictTestAlgebra F K).map g) x) =
    SpecialLinearGroup.map f.hom.toRingHom (z.hom.app R x) at hn
  have h := hb S (SpecialLinearGroup.map f.hom.toRingHom (z.hom.app R x))
  rw [← hn] at h
  change (z.hom.app S (mapPoints (untwist σ S) (z.inv.app (untwistTest σ S)
    (z.hom.app (untwistTest σ S) (mapPoints ((restrictTestAlgebra F K).map g) x))))).val = _ at h
  have hcancel := ConcreteCategory.congr_hom (z.hom_inv_id_app (untwistTest σ S))
    (mapPoints ((restrictTestAlgebra F K).map g) x)
  have hc : z.inv.app (untwistTest σ S) (z.hom.app (untwistTest σ S)
      (mapPoints ((restrictTestAlgebra F K).map g) x)) =
      mapPoints ((restrictTestAlgebra F K).map g) x := hcancel
  rw [hc] at h
  have hmap : mapPoints (untwist σ S) (mapPoints ((restrictTestAlgebra F K).map g) x) =
      mapPoints f x := by
    rw [← hg]
    simp only [mapPoints, op_comp, Functor.map_comp, Category.assoc]
  rw [hmap, hn] at h
  exact h

open _root_.RM03.Brauer.ProjectiveClassification (Cocycle Implements IsTransport)
open LinearAlgebraicGroups.Descent.MatrixAlgebraForms (projectiveAction)
open private liftSpecialLinear from LinearAlgebraicGroups.Descent.InnerTypeA

private def unliftGL {K : Type u} [CommRing K] : GL I.{u} K ≃* GL (Fin 2) K :=
  (LinearAlgebraicGroups.Descent.MatrixAlgebraForms.liftMatrix (R := K) (n := 2)).symm

private def liftMatrixAlg {K : Type u} [CommRing K] :
    Matrix (Fin 2) (Fin 2) K ≃ₐ[K] Matrix I.{u} I.{u} K :=
  Matrix.reindexAlgEquiv K K Equiv.ulift.symm

private theorem matrixAlgHom_ext {R : Type u} [CommRing R]
    {f g : Matrix I.{u} I.{u} R →ₐ[R] Matrix I.{u} I.{u} R}
    (h₁ : f upperTransvection.val = g upperTransvection.val)
    (h₂ : f lowerTransvection.val = g lowerTransvection.val) :
    f = g := by
  ext m : 1
  rw [← algHom_extendFromTransvections f m, ← algHom_extendFromTransvections g m, h₁, h₂]

private def fieldCoefficientMap (σ : Gal(K/F)) :
    restrictTestAlgebraObj F K (CommAlgCat.of K K) ⟶
      restrictTestAlgebraObj F K (CommAlgCat.of K K) :=
  testAlgebraHom σ.toRingHom σ.commutes

private def galOnSplitPoints (H : GroupScheme F)
    (z : restrictTestAlgebra F K ⋙ (groupPointsFunctor F).obj H ≅
      specialLinearPoints K I.{u}) (σ : Gal(K/F)) :
    SpecialLinearGroup I.{u} K →* SpecialLinearGroup I.{u} K :=
  let R := CommAlgCat.of K K
  (z.hom.app R).hom.comp ((((groupPointsFunctor F).obj H).map
    (fieldCoefficientMap σ)).hom.comp (z.inv.app R).hom)

private theorem galOnSplitPoints_mul (H : GroupScheme F)
    (z : restrictTestAlgebra F K ⋙ (groupPointsFunctor F).obj H ≅
      specialLinearPoints K I.{u}) (σ τ : Gal(K/F)) (x : SpecialLinearGroup I.{u} K) :
    galOnSplitPoints H z (σ * τ) x =
      galOnSplitPoints H z σ (galOnSplitPoints H z τ x) := by
  let R := CommAlgCat.of K K
  let f : (restrictTestAlgebra F K).obj R ⟶ (restrictTestAlgebra F K).obj R :=
    fieldCoefficientMap σ
  let g : (restrictTestAlgebra F K).obj R ⟶ (restrictTestAlgebra F K).obj R :=
    fieldCoefficientMap τ
  let P := (groupPointsFunctor F).obj H
  change z.hom.app R (P.map (g ≫ f) (z.inv.app R x)) =
    z.hom.app R (P.map f (z.inv.app R (z.hom.app R (P.map g (z.inv.app R x)))))
  rw [P.map_comp]
  have hh := ConcreteCategory.congr_hom (z.hom_inv_id_app R) (P.map g (z.inv.app R x))
  change z.inv.app R (z.hom.app R (P.map g (z.inv.app R x))) = _ at hh
  rw [show z.inv.app R (z.hom.app R (P.map g (z.inv.app R x))) =
    P.map g (z.inv.app R x) from hh]
  rfl

/-- The semilinear action from the given scalar extension induces a projective
matrix cocycle. The two transvections detect its composition law. -/
private theorem rankOneCocycle (H : GroupScheme F)
    (z : restrictTestAlgebra F K ⋙ (groupPointsFunctor F).obj H ≅
      specialLinearPoints K I.{u}) :
    ∃ (c : Cocycle F K 2) (b : Gal(K/F) → GL I.{u} K),
      (∀ σ, ProjGenLinGroup.mk (unliftGL (b σ)) = c.val σ) ∧
      ∀ {R S : TestAlgebra K} (σ : Gal(K/F))
        (f : restrictTestAlgebraObj F K R ⟶ restrictTestAlgebraObj F K S),
        (∀ a : K, f.hom (algebraMap K R a) = algebraMap K S (σ a)) →
        ∀ x : Points H.X (restrictTestAlgebraObj F K R),
          (z.hom.app S (mapPoints f x)).val =
            (innerAut (R := S) (GeneralLinearGroup.map (algebraMap K S) (b σ)))
              ((z.hom.app R x).val.map f.hom) := by
  choose b hb using fun σ : Gal(K/F) => matrixConjugation (semilinearAutomorphism H z σ)
  have hform {R S : TestAlgebra K} (σ : Gal(K/F))
      (f : restrictTestAlgebraObj F K R ⟶ restrictTestAlgebraObj F K S)
      (hf : ∀ a : K, f.hom (algebraMap K R a) = algebraMap K S (σ a))
      (x : Points H.X (restrictTestAlgebraObj F K R)) :=
    semilinear_matrix_formula H z σ (b σ) (hb σ) f hf x
  let c (σ : Gal(K/F)) := ProjGenLinGroup.mk (unliftGL (b σ))
  obtain ⟨e, hmk, hgal⟩ :=
    LinearAlgebraicGroups.Descent.MatrixAlgebraForms.conjugationIdentification
      (k := F) (K := K) (n := 2) (by decide)
  let E := liftMatrixAlg (K := K)
  have he (σ : Gal(K/F)) (x : Matrix I.{u} I.{u} K) :
      E (e (c σ) (E.symm x)) = innerAut (R := K) (b σ) x := by
    rw [show c σ = ProjGenLinGroup.mk (unliftGL (b σ)) from rfl, hmk]
    simp only [map_mul]
    have liftVal (g : GL I.{u} K) : E (unliftGL g).val = g.val := rfl
    rw [liftVal, E.apply_symm_apply, ← map_inv unliftGL, liftVal]
    rfl
  have hcoeff (σ : Gal(K/F)) (x : Matrix I.{u} I.{u} K) :
      E.symm (x.map σ) = (E.symm x).map σ := rfl
  have hpoint (σ : Gal(K/F)) (x : SpecialLinearGroup I.{u} K) :
      (galOnSplitPoints H z σ x).val = E (e (c σ) ((E.symm x.val).map σ)) := by
    let R := CommAlgCat.of K K
    have hh := hform (R := R) (S := R) σ (fieldCoefficientMap σ)
      (fun _ => rfl) (z.inv.app R x)
    change (galOnSplitPoints H z σ x).val = _ at hh
    rw [show z.hom.app R (z.inv.app R x) = x from
      ConcreteCategory.congr_hom (z.inv_hom_id_app R) x] at hh
    rw [← hcoeff, he]
    exact hh
  refine ⟨⟨c, fun σ τ => ?_⟩, b, fun _ => rfl, @hform⟩
  apply e.injective
  rw [map_mul]
  let f := E.symm.trans ((e (c (σ * τ))).trans E)
  -- The two matrix automorphisms are compared on the upper and lower transvections.
  have eq (x : SpecialLinearGroup I.{u} K)
      (hx : x.val.map (σ * τ) = x.val) (ht : x.val.map τ = x.val) :
      E (e (c (σ * τ)) (E.symm x.val)) =
        E (e (c σ) (e (projectiveAction 2 σ (c τ)) (E.symm x.val))) := by
    have hs : x.val.map σ = x.val := by
      have hm : x.val.map (σ * τ) = (x.val.map τ).map σ := rfl
      rw [ht] at hm
      exact hm.symm.trans hx
    have hh := congrArg Subtype.val (galOnSplitPoints_mul H z σ τ x)
    simp only [hpoint, ← hcoeff, hx, ht] at hh
    rw [hcoeff, E.symm_apply_apply, hgal, ← hcoeff, hs] at hh
    exact hh
  have unitMap (x : SpecialLinearGroup I.{u} K) (h : ∀ g : Gal(K/F), x.val.map g = x.val) :
      f x.val = (E.symm.trans ((e (projectiveAction 2 σ (c τ))).trans ((e (c σ)).trans E))) x.val :=
    eq x (h _) (h _)
  have hu (g : Gal(K/F)) : (upperTransvection (R := K)).val.map g = upperTransvection.val :=
    congrArg Subtype.val (map_upperTransvection g.toRingHom)
  have hl (g : Gal(K/F)) : (lowerTransvection (R := K)).val.map g = lowerTransvection.val :=
    congrArg Subtype.val (map_lowerTransvection g.toRingHom)
  let g := E.symm.trans ((e (projectiveAction 2 σ (c τ))).trans ((e (c σ)).trans E))
  have heq : f.toAlgHom = g.toAlgHom :=
    matrixAlgHom_ext (unitMap upperTransvection hu) (unitMap lowerTransvection hl)
  apply AlgEquiv.ext
  intro x
  exact E.injective (DFunLike.congr_fun heq (E x))

open _root_.RM03.CSA.NormOneGroup (normOneFunctor normOne extendSplitting extendSplitting_tmul
  extendSplitting_natural changeCoefficients)
open private normOneRepresentation
  from LinearAlgebraicGroups.Descent.InnerTypeA
open private spectrumPointsIso
  LinearAlgebraicGroups.StandardGroups.Representation.hopf
  LinearAlgebraicGroups.StandardGroups.Representation.convolutionIso
  from LinearAlgebraicGroups.Affine.StandardGroups
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes
open private SemilinearTestMap SemilinearTestMap.restrict semilinearSource semilinearSourceMap semilinearPoint
  semilinearPoint_apply semilinearPoint_bijective semilinearPoint_natural
  scalarMorphism scalarMorphismIso scalarMorphism_descends groupBaseChange_injective
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl

private def normGroup {A idx : Type u} [Ring A] [Algebra F A] [Fintype idx]
    (hA : isCentralSimple F A) (basis : Module.Basis idx F A) : AffineAlgebraicGroup F :=
  let P := normOneRepresentation hA basis
  letI := LinearAlgebraicGroups.StandardGroups.Representation.hopf P
  Specs.StandardGroups.spectrum F (NormOneCoordinates hA basis)

private def normGroupPoints {A idx : Type u} [Ring A] [Algebra F A] [Fintype idx]
    (hA : isCentralSimple F A) (basis : Module.Basis idx F A) :
    (groupPointsFunctor F).obj (normGroup hA basis).val ≅ normOneFunctor hA basis :=
  let P := normOneRepresentation hA basis
  letI := LinearAlgebraicGroups.StandardGroups.Representation.hopf P
  spectrumPointsIso (LinearAlgebraicGroups.StandardGroups.Representation.convolutionIso P)

private theorem normAt_eq_det_two {A idx : Type u} [Ring A] [Algebra F A] [Fintype idx]
    (hA : isCentralSimple F A) (basis : Module.Basis idx F A) (hd : degree F A = 2)
    (s : (K ⊗[F] A) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K)
    (R : TestAlgebra K) (x : restrictTestAlgebraObj F K R ⊗[F] A) :
    _root_.RM03.CSA.NormOneGroup.normAt hA basis x = (extendSplitting s x).det := by
  let e := finCongr hd
  let t := s.trans (Matrix.reindexAlgEquiv K K e.symm)
  let q := Matrix.reindexAlgEquiv R R e.symm
  let R' := restrictTestAlgebraObj F K R
  have ht : extendSplitting (R := R') t x = q (extendSplitting (R := R') s x) := by
    refine TensorProduct.inductionOn x (fun r a => ?_) (fun x y hx hy => ?_)
    · rw [extendSplitting_tmul, extendSplitting_tmul]
      rfl
    · simp only [map_add, hx, hy]
  rw [_root_.RM03.CSA.NormOneGroup.normAt_eq_det hA basis t, ht]
  exact Matrix.det_reindex_self _ _

private def normSplitPoints {A idx : Type u} [Ring A] [Algebra F A] [Fintype idx]
    (hA : isCentralSimple F A) (basis : Module.Basis idx F A) (hd : degree F A = 2)
    (s : (K ⊗[F] A) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) :
    restrictTestAlgebra F K ⋙ normOneFunctor hA basis ≅ specialLinearPoints K I.{u} :=
  NatIso.ofComponents (fun R =>
    let d := extendSplitting (R := restrictTestAlgebraObj F K R) s
    let e : normOne (R := restrictTestAlgebraObj F K R) hA basis ≃*
        SpecialLinearGroup (Fin 2) R :=
      { toFun := fun x => ⟨d x.val, (normAt_eq_det_two hA basis hd s R x.val).symm.trans x.prop⟩
        invFun := fun y => ⟨d.symm y.val, (normAt_eq_det_two hA basis hd s R _).trans
          (congrArg Matrix.det (d.apply_symm_apply y.val) |>.trans y.prop)⟩
        left_inv := fun x => Subtype.ext (d.symm_apply_apply x.val)
        right_inv := fun y => Subtype.ext (d.apply_symm_apply y.val)
        map_mul' := fun x y => Subtype.ext (d.map_mul x.val y.val) }
    (e.trans (liftSpecialLinear 2)).toGrpIso)
    (by
      intro R S f
      apply GrpCat.ext
      intro x
      apply Subtype.ext
      let R' := restrictTestAlgebraObj F K R
      let S' := restrictTestAlgebraObj F K S
      let q := Matrix.reindexAlgEquiv S S (Equiv.ulift.symm : Fin 2 ≃ I.{u})
      change q (extendSplitting (R := S') s
        (changeCoefficients ((restrictTestAlgebra F K).map f).hom x.val)) =
        q ((extendSplitting (R := R') s x.val).map f.hom)
      exact congrArg q (extendSplitting_natural (R := R') (S := S') s f.hom x.val))

/-- A comparison of split point functors which intertwines scalar actions gives
an isomorphism of the original affine group schemes. -/
private theorem descendSplitComparison [IsGalois F K]
    (G H : AffineAlgebraicGroup F)
    (zG : restrictTestAlgebra F K ⋙ (groupPointsFunctor F).obj G.val ≅ specialLinearPoints K I.{u})
    (zH : restrictTestAlgebra F K ⋙ (groupPointsFunctor F).obj H.val ≅ specialLinearPoints K I.{u})
    (hg : ∀ (σ : Gal(K/F)) (R : TestAlgebra K)
      (y : (specialLinearPoints K I.{u}).obj (semilinearSource σ R)),
      zG.hom.app R (mapPoints ((SemilinearTestMap.restrict (semilinearSourceMap σ R)))
        (zG.inv.app (semilinearSource σ R) y)) =
      zH.hom.app R (mapPoints ((SemilinearTestMap.restrict (semilinearSourceMap σ R)))
        (zH.inv.app (semilinearSource σ R) y))) :
    Nonempty (G.val ≅ H.val) := by
  let g := baseChangePointIso (K := K) G.val ≪≫ zG
  let h := baseChangePointIso (K := K) H.val ≪≫ zH
  let iso := affineGroupIso (affine_baseChange G.val.X G.property.1)
    (affine_baseChange H.val.X H.property.1) (g ≪≫ h.symm)
  have hh := affineGroupIso_hom (affine_baseChange G.val.X G.property.1)
    (affine_baseChange H.val.X H.property.1) (g ≪≫ h.symm)
  have heq (R : TestAlgebra K) (p : Points ((groupBaseChange F K).obj G.val).X R) :
      h.hom.app R (p ≫ iso.hom.hom.hom) = g.hom.app R p := by
    change h.hom.app R (((groupPointsFunctor K).map iso.hom).app R p) = _
    rw [hh]
    exact ConcreteCategory.congr_hom (h.inv_hom_id_app R) (g.hom.app R p)
  have hInv (σ : Gal(K/F)) : scalarMorphism σ iso.hom = iso.hom := by
    apply Grp.hom_ext
    apply hom_ext_of_points (affine_baseChange G.val.X G.property.1)
    intro R q
    let R' := semilinearSource σ R
    let a := semilinearSourceMap σ R
    obtain ⟨p, rfl⟩ := (semilinearPoint_bijective G.val a (Equiv.refl R).bijective).2 q
    rw [← semilinearPoint_natural σ a iso.hom p]
    apply (h.app R).groupIsoToMulEquiv.injective
    change h.hom.app R (semilinearPoint H.val a (p ≫ iso.hom.hom.hom)) =
      h.hom.app R (semilinearPoint G.val a p ≫ iso.hom.hom.hom)
    rw [heq]
    change zH.hom.app R (baseChangePoint F K H.val.X R
        (semilinearPoint H.val a (p ≫ iso.hom.hom.hom))) =
      zG.hom.app R (baseChangePoint F K G.val.X R (semilinearPoint G.val a p))
    rw [semilinearPoint_apply, semilinearPoint_apply]
    let y := g.hom.app R' p
    have hyG : zG.inv.app R' y = baseChangePoint F K G.val.X R' p :=
      ConcreteCategory.congr_hom (zG.hom_inv_id_app R') _
    have hyH : zH.inv.app R' y = baseChangePoint F K H.val.X R' (p ≫ iso.hom.hom.hom) := by
      change zH.inv.app R' (g.hom.app R' p) = _
      rw [← heq]
      exact ConcreteCategory.congr_hom (zH.hom_inv_id_app R') _
    have ht := hg σ R y
    change zG.hom.app R (mapPoints (SemilinearTestMap.restrict a) (zG.inv.app R' y)) =
      zH.hom.app R (mapPoints (SemilinearTestMap.restrict a) (zH.inv.app R' y)) at ht
    rw [hyG, hyH] at ht
    exact ht.symm
  have hInv' (σ : Gal(K/F)) : scalarMorphism σ iso.inv = iso.inv := by
    have he : scalarMorphismIso σ iso = iso := Iso.ext (hInv σ)
    exact congrArg Iso.inv he
  obtain ⟨f, hf⟩ := scalarMorphism_descends G H iso.hom hInv
  obtain ⟨r, hr⟩ := scalarMorphism_descends H G iso.inv hInv'
  have hinv : f ≫ r = 𝟙 _ := groupBaseChange_injective (K := K) (by
    rw [Functor.map_comp, hf, hr, iso.hom_inv_id]
    exact ((groupBaseChange F K).map_id _).symm)
  have hhom : r ≫ f = 𝟙 _ := groupBaseChange_injective (K := K) (by
    rw [Functor.map_comp, hr, hf, iso.inv_hom_id]
    exact ((groupBaseChange F K).map_id _).symm)
  exact ⟨⟨f, r, hinv, hhom⟩⟩

/-- The determinant-one locus of the descended algebra has the same action on
all test algebras as the given form. -/
private theorem rankOneNormModel [FiniteDimensional F K] [IsGalois F K]
    (H : AffineAlgebraicGroup F)
    (zH : restrictTestAlgebra F K ⋙ (groupPointsFunctor F).obj H.val ≅ specialLinearPoints K I.{u}) :
    ∃ (A idx : Type u) (_ : Ring A) (_ : Algebra F A) (_ : Fintype idx)
      (hA : isCentralSimple F A) (basis : Module.Basis idx F A),
      degree F A = 2 ∧ Nonempty ((normGroup hA basis).val ≅ H.val) := by
  obtain ⟨c, b, hb, hpoint⟩ := rankOneCocycle H.val zH
  obtain ⟨ρ, hρ, hA, hd, s, hs, _⟩ :=
    LinearAlgebraicGroups.Descent.MatrixAlgebraForms.effectiveDescent (by decide : 0 < 2) c
  let A := ρ.fixedSubalgebra
  letI : Module.Finite F A := hA.2.2
  let basis := Module.Free.chooseBasis F A
  let p := normGroupPoints hA basis
  let zG := Functor.isoWhiskerLeft (restrictTestAlgebra F K) p ≪≫ normSplitPoints hA basis hd s
  let d (R : TestAlgebra K) := extendSplitting (R := restrictTestAlgebraObj F K R) s
  have hdcomp := LinearAlgebraicGroups.Descent.InnerTypeA.cocycleOnTestAlgebras s d
    (fun R => extendSplitting_tmul (R := restrictTestAlgebraObj F K R) s)
  refine ⟨A, _, inferInstance, inferInstance, inferInstance, hA, basis, hd,
    descendSplitComparison (normGroup hA basis) H zG zH ?_⟩
  intro σ R y
  let a := semilinearSourceMap σ R
  let T := semilinearSource σ R
  let g := zG.inv.app T y
  let h := zH.inv.app T y
  have hyG : zG.hom.app T g = y := ConcreteCategory.congr_hom (zG.inv_hom_id_app T) y
  have hyH : zH.hom.app T h = y := ConcreteCategory.congr_hom (zH.inv_hom_id_app T) y
  change zG.hom.app R (mapPoints (SemilinearTestMap.restrict a) g) = zH.hom.app R (mapPoints (SemilinearTestMap.restrict a) h)
  apply Subtype.ext
  have ha (k : K) : (SemilinearTestMap.restrict a).hom (algebraMap K T k) =
      algebraMap K R (σ k) := rfl
  rw [hpoint σ (SemilinearTestMap.restrict a) ha h, hyH, ← hyG]
  let E' (S : TestAlgebra K) := liftMatrixAlg (K := S)
  let x : normOne (R := restrictTestAlgebraObj F K T) hA basis := p.hom.app _ g
  have hnat := ConcreteCategory.congr_hom (p.hom.naturality (SemilinearTestMap.restrict a)) g
  change p.hom.app _ (mapPoints (SemilinearTestMap.restrict a) g) = (normOneFunctor hA basis).map (SemilinearTestMap.restrict a) x at hnat
  change E' R (d R (p.hom.app _ (mapPoints (SemilinearTestMap.restrict a) g)).val) =
    innerAut (R := R) (GeneralLinearGroup.map (algebraMap K R) (b σ))
      ((E' T (d T x.val)).map (SemilinearTestMap.restrict a).hom)
  rw [hnat]
  have comp := hdcomp ρ c hs hρ σ (unliftGL (b σ)) (hb σ) (SemilinearTestMap.restrict a) ha x.val
  change d R ((normOneFunctor hA basis).map (SemilinearTestMap.restrict a) x).val = _ at comp
  rw [comp]
  simp only [map_mul]
  rfl

end GaloisDescent

open Specs.Unipotent (baseChangedAlgebraicGroup)
open _root_.RM03.CSA.NormOneGroup (normOneFunctor)
open private groupBaseChangeTowerIso from LinearAlgebraicGroups.Relative.RationalCocharacter
open private baseChangeSelfIso from LinearAlgebraicGroups.Reductive.NontrivialRationalTorus

private def restrictSL2 {F K : Type u} [Field F] [Field K] [Algebra F K] :
    restrictTestAlgebra F K ⋙ specialLinearPoints F I.{u} ≅ specialLinearPoints K I.{u} :=
  NatIso.ofComponents (fun _ => (MulEquiv.refl _).toGrpIso)
    (by
      intro R S a
      apply GrpCat.ext
      intro x
      rfl)

private def splitSL2_extend {F K : Type u} [Field F] [Field K] [Algebra F K]
    {G : GroupScheme F} (s : (groupPointsFunctor F).obj G ≅ specialLinearPoints F I.{u}) :
    (groupPointsFunctor K).obj ((groupBaseChange F K).obj G) ≅ specialLinearPoints K I.{u} :=
  baseChangePointIso G ≪≫ Functor.isoWhiskerLeft (restrictTestAlgebra F K) s ≪≫ restrictSL2

private theorem quasiSplitBaseChange_is_split {K : Type u} [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K]
    (H : AffineAlgebraicGroup F)
    (s : (groupPointsFunctor K).obj ((groupBaseChange F K).obj H.val) ≅ specialLinearPoints K I.{u})
    (hq : IsQuasiSplit (baseChangedAlgebraicGroup E H)) :
    Nonempty ((groupPointsFunctor E).obj ((groupBaseChange F E).obj H.val) ≅
      specialLinearPoints E I.{u}) := by
  let S := SeparableClosure E
  let j : K →ₐ[F] S := IsSepClosed.lift
  letI : Algebra K S := j.toRingHom.toAlgebra
  letI : IsScalarTower F K S := IsScalarTower.of_algebraMap_eq fun a => (j.commutes a).symm
  let H' := baseChangedAlgebraicGroup E H
  obtain ⟨G, ⟨t⟩⟩ := exists_splitSL2 E
  let a := ((groupPointsFunctor S).mapIso ((groupBaseChangeTowerIso
    (k := F) (K := E) (L := S)).app H.val)) ≪≫
      ((groupPointsFunctor S).mapIso ((groupBaseChangeTowerIso
        (k := F) (K := K) (L := S)).app H.val)).symm ≪≫ splitSL2_extend s
  let b := splitSL2_extend (K := S) t
  let i := affineGroupIso (affine_baseChange G.val.X G.property.1)
    (affine_baseChange H'.val.X H'.property.1) (b ≪≫ a.symm)
  obtain ⟨f⟩ := quasiSplitForm_is_split (S := S) G H' t ⟨i⟩ hq
  exact ⟨(groupPointsFunctor E).mapIso f.symm ≪≫ t⟩

private def upperTransvectionPoints (F : Type u) [Field F] :
    additivePoints F ⟶ specialLinearPoints F I.{u} where
  app R := GrpCat.ofHom
    { toFun := fun x => SpecialLinearGroup.transvection first_ne_second (Multiplicative.toAdd x)
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' x y := by
        apply Subtype.ext
        change transvection first second (Multiplicative.toAdd x + Multiplicative.toAdd y) = _
        exact (Matrix.transvection_mul_transvection_same first second first_ne_second _ _).symm }
  naturality R S f := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    change Multiplicative R at x
    change transvection first second (f.hom (Multiplicative.toAdd x)) =
      (transvection first second (Multiplicative.toAdd x)).map f.hom
    simp [Matrix.transvection, Matrix.map_add,
      Matrix.map_one f.hom f.hom.map_zero f.hom.map_one, Matrix.map_single _ _ _ f.hom]

private theorem upperTransvection_ne_one (F : Type u) [Field F] :
    (upperTransvection (R := F)) ≠ (1 : SpecialLinearGroup I.{u} F) := by
  intro h
  have hm := congrArg (fun m : SpecialLinearGroup I.{u} F => m.val first second) h
  have h₁ : (upperTransvection (R := F)).val first second = 1 := by
    simp [upperTransvection, SpecialLinearGroup.transvection_coe, Matrix.single,
      Matrix.of_apply, first_ne_second]
  have h₀ : (1 : Matrix I.{u} I.{u} F) first second = 0 := Matrix.one_apply_ne first_ne_second
  exact one_ne_zero (h₁.symm.trans (hm.trans h₀))

/-- A split scalar extension would give the upper additive root subgroup inside
the units of the scalar-extended algebra. -/
private theorem normGroup_not_split_of_division {A idx : Type u} [Ring A] [Algebra F A]
    [Fintype idx] (hA : isCentralSimple F A) (basis : Module.Basis idx F A)
    [Nontrivial (E ⊗[F] A)] (hu : ∀ x : E ⊗[F] A, x ≠ 0 → IsUnit x)
    (s : (groupPointsFunctor E).obj ((groupBaseChange F E).obj (normGroup hA basis).val) ≅
      specialLinearPoints E I.{u}) : False := by
  let P := restrictTestAlgebra F E ⋙ normOneFunctor hA basis
  let z := baseChangePointIso (K := E) (normGroup hA basis).val ≪≫
    Functor.isoWhiskerLeft (restrictTestAlgebra F E) (normGroupPoints hA basis)
  let c := upperTransvectionPoints E ≫ s.inv ≫ z.hom
  let e (R : TestAlgebra E) :=
    let T := restrictTestAlgebraObj F E R
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid E T T).symm
      (AlgEquiv.refl : A ≃ₐ[F] A)).trans (Algebra.TensorProduct.assoc F E T T E A)
  let v (R : TestAlgebra E) : P.obj R →* (R ⊗[E] (E ⊗[F] A)) :=
    (e R).toMonoidHom.comp
      { toFun := Subtype.val
        map_one' := rfl
        map_mul' _ _ := rfl }
  have hv (R : TestAlgebra E) : Function.Injective (v R) :=
    (e R).injective.comp Subtype.val_injective
  have hn {R T : TestAlgebra E} (f : R ⟶ T) (x : P.obj R) :
      v T (P.map f x) = Algebra.TensorProduct.map f.hom (AlgHom.id E (E ⊗[F] A)) (v R x) := by
    change e T (Algebra.TensorProduct.map ((restrictTestAlgebra F E).map f).hom
      (AlgHom.id F A) x.val) = Algebra.TensorProduct.map f.hom (AlgHom.id E (E ⊗[F] A))
        (e R x.val)
    generalize x.val = w
    induction w using TensorProduct.inductionOn with
    | tmul r a => simp [e]
    | add x y hx hy => simp only [map_add, hx, hy]
  let R := CommAlgCat.of E E
  have ht := additiveHom_trivial_of_division hu P v hv @hn c R (1 : R)
  have hh := congrArg (fun u => s.hom.app R (z.inv.app R u)) ht
  have h₁ := ConcreteCategory.congr_hom (z.hom_inv_id_app R)
    (s.inv.app R (upperTransvection (R := E)))
  have h₂ := ConcreteCategory.congr_hom (s.inv_hom_id_app R) (upperTransvection (R := E))
  change s.hom.app R (z.inv.app R (z.hom.app R (s.inv.app R upperTransvection))) =
    s.hom.app R (z.inv.app R 1) at hh
  change z.inv.app R (z.hom.app R (s.inv.app R upperTransvection)) =
    s.inv.app R upperTransvection at h₁
  change s.hom.app R (s.inv.app R upperTransvection) = upperTransvection at h₂
  rw [h₁, h₂, map_one, map_one] at hh
  exact upperTransvection_ne_one E hh

/-- A form of SL₂ that is quasi-split over a finite separable extension of odd
degree has a noncentral cocharacter over the ground field. -/
theorem rankOneDescent : Specs.Arithmetic.RankOneOddDescent.RankOneDescent.{u} := by
  intro F E K _ _ _ _ _ _ _ _ _ hodd H ⟨s⟩ hq
  let z := (baseChangePointIso (K := K) H.val).symm ≪≫ s
  obtain ⟨A, idx, _, _, _, hA, basis, hd, ⟨j⟩⟩ := rankOneNormModel H z
  let N := normGroup hA basis
  rcases degreeTwoCSA_split_or_oddBaseChange_division (E := E) hA hd hodd with he | hdiv
  · obtain ⟨e⟩ := he
    let d := (Algebra.TensorProduct.lid F A).trans e
    let split := baseChangePointIso (K := F) N.val ≪≫
      Functor.isoWhiskerLeft (restrictTestAlgebra F F) (normGroupPoints hA basis) ≪≫
      normSplitPoints hA basis hd d
    let own := (groupPointsFunctor F).mapIso ((baseChangeSelfIso F).app N.val).symm ≪≫ split
    exact noncentralCocharacter_of_splitSL2 H ((groupPointsFunctor F).mapIso j.symm ≪≫ own)
  · obtain ⟨zE⟩ := quasiSplitBaseChange_is_split (E := E) H s hq
    letI := hdiv.1
    exact (normGroup_not_split_of_division hA basis hdiv.2
      ((groupPointsFunctor E).mapIso ((groupBaseChange F E).mapIso j) ≪≫ zE)).elim

end

end LinearAlgebraicGroups.Arithmetic.RankOneOddDescent
