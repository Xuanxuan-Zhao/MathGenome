import Specs.LinearAlgebraicGroups.Arithmetic.IntegralModels
import LinearAlgebraicGroups.Affine.StandardGroups
import LinearAlgebraicGroups.Affine.FaithfulLinearization
import LinearAlgebraicGroups.Descent.RelativeRank
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.DedekindDomain.Factorization
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.RootData.SpecialLinearDatum
open AlgebraicGeometry CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

namespace LinearAlgebraicGroups.Arithmetic.IntegralModels

open Specs.IntegralModels
open Specs.StandardGroups (GLCoordinates SLCoordinates genericDeterminant universalMatrix)
open Specs.Unipotent (Index)
open IsDedekindDomain

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

private def affineGroupIsoOfPoints {k : Type u} [Field k] {G H : GroupScheme k}
    (hG : IsAffine G.X.left) (hH : IsAffine H.X.left)
    (e : (groupPointsFunctor k).obj G ≅ (groupPointsFunctor k).obj H) : G ≅ H := by
  let F := groupPointsFunctor k
  let f := (groupHomEquiv G H hG).symm e.hom
  let g := (groupHomEquiv H G hH).symm e.inv
  have hf : F.map f = e.hom := (groupHomEquiv G H hG).apply_symm_apply _
  have hg : F.map g = e.inv := (groupHomEquiv H G hH).apply_symm_apply _
  refine ⟨f, g, ?_, ?_⟩
  · apply (groupHomEquiv G G hG).injective
    change F.map (f ≫ g) = F.map (𝟙 _)
    simp [hf, hg]
  · apply (groupHomEquiv H H hH).injective
    change F.map (g ≫ f) = F.map (𝟙 _)
    simp [hf, hg]

private theorem affineGroupIsoOfPoints_map {k : Type u} [Field k] {G H : GroupScheme k}
    (hG : IsAffine G.X.left) (hH : IsAffine H.X.left)
    (e : (groupPointsFunctor k).obj G ≅ (groupPointsFunctor k).obj H) :
    (groupPointsFunctor k).map (affineGroupIsoOfPoints hG hH e).hom = e.hom :=
  (groupHomEquiv G H hG).apply_symm_apply _

private def coordinateMap {k : Type u} [Field k] {A B : TestAlgebra k}
    (f : (testSpec k).obj (op A) ⟶ (testSpec k).obj (op B)) : B ⟶ A :=
  ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage f).unop

private theorem coordinateMap_spec {k : Type u} [Field k] {A B : TestAlgebra k}
    (f : (testSpec k).obj (op A) ⟶ (testSpec k).obj (op B)) :
    (testSpec k).map (coordinateMap f).op = f :=
  (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage f

private theorem specMap_surjective {A B : CommRingCat} (f : A ⟶ B)
    (hf : IsClosedImmersion (Spec.map f)) : Function.Surjective f := by
  letI := hf
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map f)).2
  have he : (Scheme.ΓSpecIso _).inv ≫ (Spec.map f).appTop ≫ (Scheme.ΓSpecIso _).hom = f := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [← he]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).2.comp
    (hs.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2)

open private glEvaluation glEvaluation_entry evaluatedGeneralLinear
  matrixEvaluation matrixEvaluation_mapMatrix isUnit_matrixEvaluation_det glCoordinates_ext
  from LinearAlgebraicGroups.Affine.StandardGroups

private theorem glPoint_eval {k : Type u} [Field k] {ι : Type u} [Fintype ι] [DecidableEq ι]
    {R : TestAlgebra k} (a : CommAlgCat.of k (GLCoordinates k ι) ⟶ R) (i j : ι) :
    ((StandardGroups.generalLinearGroupPointsIso k ι).hom.app R
      ((testSpec k).map a.op)).val i j = a.hom (universalMatrix k ι i j) := by
  letI := StandardGroups.generalLinearHopf k ι
  let e := hopfSpecPointIso (CommHopfAlgCat.of k (GLCoordinates k ι))
  let x := WithConv.toConv a.hom
  have he : e.hom.app R x = (testSpec k).map a.op := by
    apply Over.OverMorphism.ext
    rfl
  rw [← he]
  change (evaluatedGeneralLinear (ι := ι) (e.inv.app R (e.hom.app R x)).ofConv).val i j = _
  exact congrArg (fun y : WithConv (GLCoordinates k ι →ₐ[k] R) =>
    (evaluatedGeneralLinear y.ofConv).val i j) (GrpCat.inv_hom_apply (e.app R) x)

/-- Pull back a coordinate of the second realization through the first closed immersion. -/
private theorem changeOfCoordinates {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (i j : MatrixRealization G) (l m : Index.{u} j.size) :
    ∃ a : GLCoordinates k (Index.{u} i.size), ∀ g : RationalPoints G,
      glEvaluation (i.onPoints g) a = (j.onPoints g).val l m := by
  let L := StandardGroups.generalLinearGroup k (Index.{u} i.size)
  let M := StandardGroups.generalLinearGroup k (Index.{u} j.size)
  let iIso : i.ambient.val ≅ L.val := affineGroupIsoOfPoints i.ambient.prop.1 L.prop.1
    (i.matrix ≪≫ (StandardGroups.generalLinearGroupPointsIso k _).symm)
  let jIso : j.ambient.val ≅ M.val := affineGroupIsoOfPoints j.ambient.prop.1 M.prop.1
    (j.matrix ≪≫ (StandardGroups.generalLinearGroupPointsIso k _).symm)
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.prop.1
  let f := e.hom ≫ i.embedding.hom.hom ≫ iIso.hom.hom.hom
  let h := e.hom ≫ j.embedding.hom.hom ≫ jIso.hom.hom.hom
  let a := coordinateMap (k := k) (A := A.unop)
    (B := CommAlgCat.of k (GLCoordinates k (Index.{u} i.size))) f
  let b := coordinateMap (k := k) (A := A.unop)
    (B := CommAlgCat.of k (GLCoordinates k (Index.{u} j.size))) h
  have ha : Function.Surjective a.hom := by
    have hf : IsClosedImmersion f.left := by
      letI := i.closed
      change IsClosedImmersion (e.hom.left ≫ i.embedding.hom.hom.left ≫ iIso.hom.hom.hom.left)
      let FG := Grp.forget (SchemeOver k) ⋙ Over.forget _
      haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
      haveI : IsIso iIso.hom.hom.hom.left := inferInstanceAs (IsIso (FG.map iIso.hom))
      infer_instance
    have hf' := congrArg Over.Hom.left (coordinateMap_spec f)
    rw [algSpec_map_left] at hf'
    exact specMap_surjective _ (hf' ▸ (show IsClosedImmersion f.left from hf))
  obtain ⟨c, hc⟩ := ha (b.hom (universalMatrix k _ l m))
  refine ⟨c, fun g ↦ ?_⟩
  let q : Points ((testSpec k).obj A) (CommAlgCat.of k k) := g ≫ e.inv
  let p : A.unop ⟶ CommAlgCat.of k k := coordinateMap q
  have images (v : MatrixRealization G) (g : RationalPoints G) :
      let L := StandardGroups.generalLinearGroup k (Index.{u} v.size)
      let m := StandardGroups.generalLinearGroupPointsIso k (Index.{u} v.size)
      let E := affineGroupIsoOfPoints v.ambient.prop.1 L.prop.1 (v.matrix ≪≫ m.symm)
      m.hom.app (CommAlgCat.of k k) (g ≫ v.embedding.hom.hom ≫ E.hom.hom.hom) =
        v.onPoints g := by
    intro L m E
    let R := CommAlgCat.of k k
    let x : Points v.ambient.val.X R := g ≫ v.embedding.hom.hom
    have hh := affineGroupIsoOfPoints_map v.ambient.prop.1 L.prop.1 (v.matrix ≪≫ m.symm)
    have hh' := congrArg (fun α => α.app R x) hh
    change x ≫ E.hom.hom.hom = (v.matrix.hom.app R ≫ m.inv.app R) x at hh'
    rw [← Category.assoc, show g ≫ v.embedding.hom.hom = x from rfl, hh',
      GrpCat.comp_apply]
    exact GrpCat.hom_inv_apply (m.app R) (v.matrix.hom.app R x)
  have hi (s t : Index.{u} i.size) :
      (i.onPoints g).val s t = (a ≫ p).hom (universalMatrix k _ s t) := by
    have hh : (testSpec k).map (a ≫ p).op = g ≫ i.embedding.hom.hom ≫ iIso.hom.hom.hom := by
      rw [CategoryTheory.op_comp, Functor.map_comp]
      rw [show (testSpec k).map a.op = f from coordinateMap_spec f,
        show (testSpec k).map p.op = q from coordinateMap_spec q]
      simp [q, f]
    rw [← glPoint_eval, hh, images i g]
  have hj : (j.onPoints g).val l m = (b ≫ p).hom (universalMatrix k _ l m) := by
    have hh : (testSpec k).map (b ≫ p).op = g ≫ j.embedding.hom.hom ≫ jIso.hom.hom.hom := by
      rw [CategoryTheory.op_comp, Functor.map_comp]
      rw [show (testSpec k).map b.op = h from coordinateMap_spec h,
        show (testSpec k).map p.op = q from coordinateMap_spec q]
      simp [q, h]
    rw [← glPoint_eval, hh, images j g]
  have he : glEvaluation (i.onPoints g) = (a ≫ p).hom := by
    apply glCoordinates_ext
    intro s t
    exact (glEvaluation_entry _ s t).trans (hi s t)
  rw [he, hj]
  exact congrArg p.hom hc

private theorem clearPolynomialDenominators {D k σ : Type u} [CommRing D] [IsDomain D]
    [Field k] [Algebra D k] [IsFractionRing D k] (p : MvPolynomial σ k) :
    ∃ d : D, d ≠ 0 ∧ ∃ q : MvPolynomial σ D,
      MvPolynomial.map (algebraMap D k) q = MvPolynomial.C (algebraMap D k d) * p := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples D⁰ p.support p.coeff
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp d.2, ?_⟩
  have h : MvPolynomial.C (algebraMap D k d) * p ∈
      Set.range (MvPolynomial.map (algebraMap D k)) := by
    refine MvPolynomial.mem_range_map_iff_coeffs_subset.mpr ?_
    intro c hc
    obtain ⟨m, hm, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    rw [MvPolynomial.coeff_C_mul]
    by_cases hp : m ∈ p.support
    · obtain ⟨b, hb⟩ := hd m hp
      exact ⟨b, hb.trans (Algebra.smul_def (d : D) _)⟩
    · rw [MvPolynomial.notMem_support_iff.mp hp, mul_zero]
      exact ⟨0, map_zero _⟩
  exact h

private theorem glEvaluation_polynomial {k ι : Type u} [Field k] [Fintype ι] [DecidableEq ι]
    (g : Matrix.GeneralLinearGroup ι k) (p : MvPolynomial (ι × ι) k) :
    glEvaluation g (algebraMap (MvPolynomial (ι × ι) k) (GLCoordinates k ι) p) =
      matrixEvaluation g.val p :=
  IsLocalization.Away.lift_eq (S := GLCoordinates k ι) (genericDeterminant k ι)
    (g := (matrixEvaluation g.val).toRingHom) (isUnit_matrixEvaluation_det g) p

private theorem glEvaluation_genericDeterminant {k ι : Type u} [Field k] [Fintype ι]
    [DecidableEq ι] (g : Matrix.GeneralLinearGroup ι k) :
    glEvaluation g (algebraMap (MvPolynomial (ι × ι) k) (GLCoordinates k ι)
      (genericDeterminant k ι)) = g.val.det :=
  (glEvaluation_polynomial g _).trans
    (((matrixEvaluation g.val).map_det _).trans (congrArg Matrix.det
      (matrixEvaluation_mapMatrix g.val)))

private def matrixPolynomialOver {D R ι : Type u} [CommRing D] [CommRing R] [Algebra D R]
    [Fintype ι] [DecidableEq ι] (p : MvPolynomial (ι × ι) D) (n : ℕ)
    (g : Matrix.GeneralLinearGroup ι R) : R :=
  MvPolynomial.eval₂ (algebraMap D R) (fun ij => g.val ij.1 ij.2) p *
    (↑((Matrix.GeneralLinearGroup.det g)⁻¹) : R) ^ n

private theorem matrixPolynomialOver_natural {D R R' ι : Type u}
    [CommRing D] [CommRing R] [CommRing R'] [Algebra D R] [Algebra D R']
    [Fintype ι] [DecidableEq ι] (f : R →ₐ[D] R')
    (p : MvPolynomial (ι × ι) D) (n : ℕ) (g : Matrix.GeneralLinearGroup ι R) :
    f (matrixPolynomialOver p n g) = matrixPolynomialOver p n (Matrix.GeneralLinearGroup.map f g) := by
  have hf : f.toRingHom.comp (algebraMap D R) = algebraMap D R' :=
    RingHom.ext f.commutes
  simp only [matrixPolynomialOver, map_mul, map_pow, Matrix.GeneralLinearGroup.map_det]
  change f (MvPolynomial.eval₂ (algebraMap D R) _ p) * _ = _ * _
  congr 1
  exact (MvPolynomial.hom_eval₂ p _ f.toRingHom _).trans (by rw [hf]; rfl)

private theorem glEvaluation_integralMultiple {D k ι : Type u} [CommRing D] [IsDomain D]
    [Field k] [Algebra D k] [IsFractionRing D k] [Fintype ι] [DecidableEq ι]
    (a : GLCoordinates k ι) :
    ∃ (d : D) (_ : d ≠ 0) (p : MvPolynomial (ι × ι) D) (n : ℕ),
      ∀ g : Matrix.GeneralLinearGroup ι k,
        algebraMap D k d * glEvaluation g a = matrixPolynomialOver p n g := by
  obtain ⟨n, q, hq⟩ := IsLocalization.Away.surj (genericDeterminant k ι) a
  obtain ⟨d, hd, p, hp⟩ := clearPolynomialDenominators (D := D) q
  refine ⟨d, hd, p, n, fun g => ?_⟩
  have he := congrArg (glEvaluation g) hq
  rw [map_mul, map_pow, glEvaluation_genericDeterminant, glEvaluation_polynomial] at he
  let eval : MvPolynomial (ι × ι) k →+* k := MvPolynomial.eval (fun ij => g.val ij.1 ij.2)
  have hy := congrArg eval hp
  change MvPolynomial.eval (fun ij : ι × ι => g.val ij.1 ij.2) (MvPolynomial.map _ p) =
    eval (MvPolynomial.C (algebraMap D k d) * q) at hy
  rw [MvPolynomial.eval_map, map_mul, show eval (MvPolynomial.C (algebraMap D k d)) =
    algebraMap D k d from MvPolynomial.eval_C _] at hy
  change MvPolynomial.eval₂ (algebraMap D k) (fun ij : ι × ι => g.val ij.1 ij.2) p =
    algebraMap D k d * matrixEvaluation g.val q at hy
  change _ = MvPolynomial.eval₂ (algebraMap D k) (fun ij : ι × ι => g.val ij.1 ij.2) p *
    (↑((Matrix.GeneralLinearGroup.det g)⁻¹) : k) ^ n
  rw [hy, ← he, mul_assoc, mul_assoc, ← mul_pow]
  change _ = algebraMap D k d * (glEvaluation g a * ((↑(Matrix.GeneralLinearGroup.det g) : k) *
    ↑((Matrix.GeneralLinearGroup.det g)⁻¹)) ^ n)
  rw [Units.mul_inv, one_pow, mul_one]

private theorem glMap_injective {R k ι : Type u} [CommRing R] [CommRing k]
    [Fintype ι] [DecidableEq ι] {f : R →+* k} (hf : Function.Injective f) :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := ι) f) := by
  intro a b h
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact hf (congrArg (fun c : Matrix.GeneralLinearGroup ι k => c.val i j) h)

private def integralMatrixLift {R k : Type u} [CommRing R] [Field k] [Algebra R k]
    {G : AffineAlgebraicGroup k} (i : MatrixRealization G)
    (hinj : Function.Injective (algebraMap R k)) :
    integralSubgroup (R := R) i →* Matrix.GeneralLinearGroup (Index.{u} i.size) R :=
  (MonoidHom.ofInjective (glMap_injective hinj)).symm.toMonoidHom.comp
    ((i.onPoints.comp (integralSubgroup (R := R) i).subtype).codRestrict _ fun g => g.2)

private theorem integralMatrixLift_map {R k : Type u} [CommRing R] [Field k] [Algebra R k]
    {G : AffineAlgebraicGroup k} (i : MatrixRealization G)
    (hinj : Function.Injective (algebraMap R k)) (g : integralSubgroup (R := R) i) :
    Matrix.GeneralLinearGroup.map (algebraMap R k) (integralMatrixLift i hinj g) = i.onPoints g :=
  congrArg Subtype.val ((MonoidHom.ofInjective (glMap_injective hinj)).apply_symm_apply
    (⟨i.onPoints g, g.2⟩ : (Matrix.GeneralLinearGroup.map (algebraMap R k)).range))

private theorem gl_mem_range_of_entries_and_inverse {R k ι : Type u} [CommRing R] [Field k]
    [Algebra R k] [Fintype ι] [DecidableEq ι] (hinj : Function.Injective (algebraMap R k))
    (g : Matrix.GeneralLinearGroup ι k)
    (h : ∀ l m, ∃ a : R, algebraMap R k a = g.val l m)
    (h' : ∀ l m, ∃ a : R, algebraMap R k a = g⁻¹.val l m) :
    g ∈ (Matrix.GeneralLinearGroup.map (algebraMap R k)).range := by
  choose A hA using h
  choose B hB using h'
  change Matrix ι ι R at A B
  let f := (algebraMap R k).mapMatrix (m := ι)
  have hA' : f A = g.val := Matrix.ext hA
  have hB' : f B = g⁻¹.val := Matrix.ext hB
  have hf : Function.Injective f := by
    intro x y hx
    exact Matrix.ext fun l m => hinj (congrArg (fun z : Matrix ι ι k => z l m) hx)
  have hAB : A * B = 1 := by
    apply hf
    rw [map_mul, hA', hB', map_one]
    exact g.val_inv
  have hBA : B * A = 1 := by
    apply hf
    rw [map_mul, hA', hB', map_one]
    exact g.inv_val
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA'⟩

/-- Reducing modulo the cleared denominators produces a finite-index subgroup
whose points are integral in the other realization. -/
private theorem integralSubgroup_relIndex {D R k : Type u} [CommRing D] [IsDomain D]
    [CommRing R] [Field k] [Algebra D R] [Algebra D k] [Algebra R k]
    [IsScalarTower D R k] [IsFractionRing D k] (hinj : Function.Injective (algebraMap R k))
    (hfinite : ∀ d : D, d ≠ 0 → Finite (R ⧸ Ideal.span {(algebraMap D R d)}))
    {G : AffineAlgebraicGroup k} (i j : MatrixRealization G) :
    (integralSubgroup (R := R) j).IsFiniteRelIndex (integralSubgroup (R := R) i) := by
  classical
  let H := integralSubgroup (R := R) i
  let J := integralSubgroup (R := R) j
  let e := integralMatrixLift i hinj
  choose a ha using fun p : Index.{u} j.size × Index.{u} j.size => changeOfCoordinates i j p.1 p.2
  choose d hd q n hq using fun p => glEvaluation_integralMultiple (D := D) (a p)
  let I p : Ideal R := Ideal.span {(algebraMap D R (d p))}
  let reduction p : H →* Matrix.GeneralLinearGroup (Index.{u} i.size) (R ⧸ I p) :=
    (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (I p))).comp e
  have hidx (p) : (reduction p).ker.FiniteIndex := by
    haveI : Finite (R ⧸ I p) := hfinite _ (hd p)
    haveI : Finite (Matrix.GeneralLinearGroup (Index.{u} i.size) (R ⧸ I p)) :=
      Finite.of_injective Units.val Units.val_injective
    infer_instance
  let C : Subgroup H := ⨅ p, (reduction p).ker
  haveI : C.FiniteIndex := Subgroup.finiteIndex_iInf hidx
  have hentry (g : H) (hg : g ∈ C) (p : Index.{u} j.size × Index.{u} j.size) :
      ∃ x : R, algebraMap R k x = (j.onPoints g).val p.1 p.2 := by
    let z := matrixPolynomialOver (q p) (n p) (e g)
    let z₁ := matrixPolynomialOver (q p) (n p) (1 : Matrix.GeneralLinearGroup (Index.{u} i.size) R)
    have hmod : (reduction p) g = 1 := Subgroup.mem_iInf.mp hg p
    let red : R →ₐ[D] R ⧸ I p := Ideal.Quotient.mkₐ D (I p)
    have heq : red z = red z₁ := by
      rw [show z = matrixPolynomialOver (q p) (n p) (e g) from rfl,
        show z₁ = matrixPolynomialOver (q p) (n p) 1 from rfl,
        matrixPolynomialOver_natural, matrixPolynomialOver_natural, map_one]
      exact congrArg (matrixPolynomialOver (q p) (n p)) hmod
    have hz : z - z₁ ∈ I p :=
      Ideal.Quotient.eq_zero_iff_mem.mp (by change red (z - z₁) = 0; rw [map_sub, heq, sub_self])
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hz
    let f : R →ₐ[D] k := IsScalarTower.toAlgHom D R k
    have hzg : f z = algebraMap D k (d p) * (j.onPoints g).val p.1 p.2 := by
      dsimp only [z]
      rw [matrixPolynomialOver_natural, show Matrix.GeneralLinearGroup.map f (e g) = i.onPoints g
        from integralMatrixLift_map i hinj g, ← hq p, ha p]
    have hz₁ : f z₁ = algebraMap D k (d p) *
        ((1 : Matrix.GeneralLinearGroup (Index.{u} j.size) k).val p.1 p.2) := by
      dsimp only [z₁]
      rw [matrixPolynomialOver_natural, map_one, ← map_one i.onPoints, ← hq p, ha p, map_one]
    have hd' : algebraMap D k (d p) ≠ 0 := fun h =>
      hd p ((IsFractionRing.injective D k) (h.trans (map_zero _).symm))
    refine ⟨t + (1 : Matrix (Index.{u} j.size) (Index.{u} j.size) R) p.1 p.2, ?_⟩
    change f _ = _
    apply mul_left_cancel₀ hd'
    have htk := congrArg f ht
    rw [map_mul, map_sub, f.commutes, hzg, hz₁] at htk
    rw [map_add, mul_add, show f ((1 : Matrix (Index.{u} j.size) (Index.{u} j.size) R)
      p.1 p.2) = (1 : Matrix (Index.{u} j.size) (Index.{u} j.size) k) p.1 p.2 from by
        simp [Matrix.one_apply, apply_ite]]
    linear_combination htk
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
  apply Subgroup.finiteIndex_of_le (H := C)
  intro g hg
  apply gl_mem_range_of_entries_and_inverse hinj (j.onPoints g)
  · intro l m
    exact hentry g hg (l, m)
  · intro l m
    simpa only [Subgroup.coe_inv, map_inv] using hentry g⁻¹ (C.inv_mem hg) (l, m)

private theorem integralSubgroup_commensurable {D R k : Type u} [CommRing D] [IsDomain D]
    [CommRing R] [Field k] [Algebra D R] [Algebra D k] [Algebra R k]
    [IsScalarTower D R k] [IsFractionRing D k] (hinj : Function.Injective (algebraMap R k))
    (hfinite : ∀ d : D, d ≠ 0 → Finite (R ⧸ Ideal.span {(algebraMap D R d)}))
    {G : AffineAlgebraicGroup k} (i j : MatrixRealization G) :
    (integralSubgroup (R := R) i).Commensurable (integralSubgroup (R := R) j) :=
  ⟨integralSubgroup_relIndex hinj hfinite j i, integralSubgroup_relIndex hinj hfinite i j⟩

private theorem rationalIndependence : RationalIndependence := by
  intro G i j
  exact integralSubgroup_commensurable (D := ℤ) (IsFractionRing.injective ℤ ℚ)
    (fun d hd => Ring.HasFiniteQuotients.finiteQuotient (by simpa using hd)) i j

private theorem finiteLocalizedQuotient {D A : Type u} [CommRing D] [CommRing A] [Algebra D A]
    (M : Submonoid D) [IsLocalization M A] (d : D)
    [Finite (D ⧸ Ideal.span {d})] : Finite (A ⧸ Ideal.span {(algebraMap D A d)}) := by
  let J : Ideal D := Ideal.span {d}
  let I : Ideal A := Ideal.span {(algebraMap D A d)}
  let q := Ideal.Quotient.mk I
  let f : D →+* A ⧸ I := q.comp (algebraMap D A)
  let F : D ⧸ J →+* A ⧸ I := Ideal.Quotient.lift J f (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul]
    have h : f d = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    rw [h, zero_mul])
  let P := {b : Set.range F // IsUnit b.val}
  let φ : Set.range F × P → A ⧸ I := fun (a, b) => a.val * ↑(b.property.unit⁻¹)
  apply Finite.of_surjective φ
  intro z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj M z
  have hb : IsUnit (f b) := (IsLocalization.map_units A b).map q
  let a' : Set.range F := ⟨f a, Ideal.Quotient.mk J a, rfl⟩
  let b' : P := ⟨⟨f b, Ideal.Quotient.mk J b, rfl⟩, hb⟩
  refine ⟨(a', b'), ?_⟩
  have hz : q z * f b = f a := by simpa [f, q] using congrArg q hab
  change f a * ↑(hb.unit⁻¹) = q z
  rw [← hz, mul_assoc]
  have hinv : f b * (↑(hb.unit⁻¹) : A ⧸ I) = 1 :=
    congrArg (fun c : A ⧸ I => c * ↑(hb.unit⁻¹)) hb.unit_spec.symm |>.trans (Units.mul_inv _)
  rw [hinv, mul_one]

private def sIntegerAtPrime {K : Type u} [Field K] [NumberField K]
    {S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers K))}
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) (hv : v ∉ S) :
    SIntegers K S →+* v.valuationSubringAtPrime K where
  toFun x := ⟨x.val, by
    rw [v.valuationSubringAtPrime_eq_valuationSubring]
    exact x.2 v hv⟩
  map_one' := rfl
  map_zero' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- At places where the denominator is a unit there is no congruence condition. -/
private theorem finiteSIntegerQuotient {K : Type u} [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (d : NumberField.RingOfIntegers K) (hd : d ≠ 0) :
    Finite ((SIntegers K S) ⧸ Ideal.span {(algebraMap (NumberField.RingOfIntegers K)
      (SIntegers K S) d)}) := by
  let D := NumberField.RingOfIntegers K
  let R := SIntegers K S
  let I : Ideal R := Ideal.span {(algebraMap D R d)}
  let V := {v : HeightOneSpectrum D // v ∉ S ∧ v.asIdeal ∣ Ideal.span {d}}
  haveI : Finite V := ((Ideal.finite_factors (R := D)
    (I := Ideal.span {d}) (by simpa using hd)).subset (fun _ h => h.2)).to_subtype
  let J (v : V) : Ideal (v.val.valuationSubringAtPrime K) :=
    Ideal.span {(algebraMap D (v.val.valuationSubringAtPrime K) d)}
  haveI : Finite (D ⧸ Ideal.span {d}) :=
    Ring.HasFiniteQuotients.finiteQuotient (by simpa using hd)
  haveI (v : V) : Finite ((v.val.valuationSubringAtPrime K) ⧸ J v) :=
    finiteLocalizedQuotient v.val.asIdeal.primeCompl d
  let f (v : V) : R →+* (v.val.valuationSubringAtPrime K) ⧸ J v :=
    (Ideal.Quotient.mk (J v)).comp (sIntegerAtPrime v.val v.2.1)
  have hf (v : V) (x : R) (hx : x ∈ I) : f v x = 0 := by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [map_mul]
    have h : f v (algebraMap D R d) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    rw [h, zero_mul]
  let F (v : V) := Ideal.Quotient.lift I (f v) (fun x hx => hf v x hx)
  apply Finite.of_injective (fun x : R ⧸ I => fun v : V => F v x)
  intro x y h
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  apply Ideal.Quotient.eq.mpr
  have hdK : algebraMap D K d ≠ 0 := fun e =>
    hd ((IsFractionRing.injective D K) (e.trans (map_zero _).symm))
  let a : K := ((x : K) - (y : K)) / algebraMap D K d
  have ha : a ∈ R := by
    intro v hv
    by_cases hvd : v.asIdeal ∣ Ideal.span {d}
    · let w : V := ⟨v, hv, hvd⟩
      have he : f w x = f w y := congrFun h w
      have hzero : f w (x - y) = 0 := by rw [map_sub, he, sub_self]
      have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hmem
      have hba : algebraMap D K d * (b : K) = (x : K) - (y : K) :=
        (congrArg Subtype.val hb).symm
      rw [show a = (b : K) from (div_eq_iff hdK).mpr (by simpa [mul_comm] using hba.symm)]
      have hbmem : (b : K) ∈ (v.valuationSubringAtPrime K : Set K) := b.property
      exact (v.valuation K).mem_valuationSubring_iff _ |>.mp
        ((congrArg (fun U : ValuationSubring K => (b : K) ∈ (U : Set K))
          (v.valuationSubringAtPrime_eq_valuationSubring (K := K))).mp hbmem)
    · have hvd' : v.valuation K (algebraMap D K d) = 1 :=
        le_antisymm (v.valuation_le_one d)
          (not_lt.mp (fun hlt => hvd ((v.valuation_lt_one_iff_dvd (K := K) d).mp hlt)))
      change v.valuation K a ≤ 1
      rw [show a = ((x - y : R) : K) / algebraMap D K d from rfl, map_div₀, hvd', div_one]
      exact (x - y : R).2 v hv
  refine Ideal.mem_span_singleton.mpr ⟨⟨a, ha⟩, ?_⟩
  apply Subtype.ext
  change (x : K) - (y : K) = algebraMap D K d * a
  calc
    (x : K) - (y : K) = a * algebraMap D K d :=
      (div_eq_iff hdK).mp (show ((x : K) - (y : K)) / algebraMap D K d = a from rfl)
    _ = _ := mul_comm _ _

private theorem numberFieldIndependence : NumberFieldIndependence.{u} := by
  intro K _ _ S G i j
  exact integralSubgroup_commensurable (D := NumberField.RingOfIntegers K)
    (by exact Subtype.val_injective : Function.Injective (algebraMap (SIntegers K S) K)) (finiteSIntegerQuotient S) i j

private theorem arithmeticClass : ArithmeticClass := by
  intro G H
  obtain ⟨n, L, ⟨e⟩, f, hf⟩ := LinearAlgebraicGroups.faithfulLinearization ℚ G
  let i : MatrixRealization G := ⟨n, L, e, f, hf⟩
  refine ⟨⟨i⟩, ⟨?_, fun h => ⟨i, h i⟩⟩⟩
  rintro ⟨j, hj⟩ l
  exact hj.trans (rationalIndependence G j l)

open private evaluatedSpecialLinear from LinearAlgebraicGroups.Affine.StandardGroups

private theorem slPoint_eval {k : Type u} [Field k] {ι : Type u} [Fintype ι] [DecidableEq ι]
    {R : TestAlgebra k} (a : CommAlgCat.of k (SLCoordinates k ι) ⟶ R) (i j : ι) :
    ((StandardGroups.specialLinearGroupPointsIso k ι).hom.app R
      ((testSpec k).map a.op)).val i j =
      a.hom (Ideal.Quotient.mk _ (universalMatrix k ι i j)) := by
  letI := StandardGroups.specialLinearHopf k ι
  let e := hopfSpecPointIso (CommHopfAlgCat.of k (SLCoordinates k ι))
  let x := WithConv.toConv a.hom
  have he : e.hom.app R x = (testSpec k).map a.op := by
    apply Over.OverMorphism.ext
    rfl
  rw [← he]
  change (evaluatedSpecialLinear (ι := ι) (e.inv.app R (e.hom.app R x)).ofConv).val i j = _
  exact congrArg (fun y : WithConv (SLCoordinates k ι →ₐ[k] R) =>
    (evaluatedSpecialLinear y.ofConv).val i j) (GrpCat.inv_hom_apply (e.app R) x)

private def specialToGeneralPoints (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :
    Specs.StandardGroups.specialLinearPoints k ι ⟶ Specs.StandardGroups.generalLinearPoints k ι where
  app R := GrpCat.ofHom Matrix.SpecialLinearGroup.toGL
  naturality R A a := by
    apply GrpCat.ext
    intro x
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl

private theorem specialLinearIntegralRealization (n : ℕ) (G : AffineAlgebraicGroup ℚ)
    (s : Specs.GeneralLinearStructure.SpecialMatrixPoints G n) :
    ∃ i : MatrixRealization G, (specialLinearIntegralMap s).range = integralSubgroup (R := ℤ) i := by
  let k := ℚ
  let L := StandardGroups.generalLinearGroup k (Index.{0} n)
  let S := StandardGroups.specialLinearGroup k (Index.{0} n)
  let c := StandardGroups.generalLinearGroupPointsIso k (Index.{0} n)
  let b := StandardGroups.specialLinearGroupPointsIso k (Index.{0} n)
  let α := b.hom ≫ specialToGeneralPoints k (Index.{0} n) ≫ c.inv
  let f := (AffineAlgebraicGroup.groupHomEquiv S L).symm α
  have hf : (groupPointsFunctor k).map f = α :=
    (AffineAlgebraicGroup.groupHomEquiv S L).apply_symm_apply α
  let e := affineGroupIsoOfPoints G.prop.1 S.prop.1 (s ≪≫ b.symm)
  have he := affineGroupIsoOfPoints_map G.prop.1 S.prop.1 (s ≪≫ b.symm)
  let q := CommAlgCat.ofHom (Ideal.Quotient.mkₐ k
    (Specs.StandardGroups.determinantOneIdeal k (Index.{0} n)))
  have hq : f.hom.hom = (testSpec k).map q.op := by
    let R := CommAlgCat.of k (SLCoordinates k (Index.{0} n))
    let x : Points S.val.X R := (testSpec k).map (𝟙 (op R))
    have hx : x = 𝟙 S.val.X := (testSpec k).map_id _
    apply (Function.LeftInverse.injective (GrpCat.inv_hom_apply (c.app R)))
    change c.hom.app R f.hom.hom = c.hom.app R ((testSpec k).map q.op)
    have hh := congrArg (fun z => c.hom.app R (z.app R x)) hf
    change c.hom.app R (x ≫ f.hom.hom) =
      c.hom.app R (c.inv.app R (Matrix.SpecialLinearGroup.toGL (b.hom.app R x))) at hh
    have hh' : c.hom.app R f.hom.hom = Matrix.SpecialLinearGroup.toGL (b.hom.app R x) := by
      have hc := GrpCat.hom_inv_apply (c.app R) (Matrix.SpecialLinearGroup.toGL (b.hom.app R x))
      have hx' : x ≫ f.hom.hom = f.hom.hom :=
        (congrArg (· ≫ f.hom.hom) hx).trans (Category.id_comp _)
      exact (congrArg (c.hom.app R) hx').symm.trans (hh.trans hc)
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [hh', glPoint_eval]
    exact slPoint_eval (𝟙 R) i j
  have hc : IsClosedImmersion f.hom.hom.left := by
    rw [hq, algSpec_map_left]
    exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hc' : IsClosedImmersion (e.hom ≫ f).hom.hom.left := by
    change IsClosedImmersion (e.hom.hom.hom.left ≫ f.hom.hom.left)
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget _
    letI : IsIso e.hom.hom.hom.left := inferInstanceAs (IsIso (F.map e.hom))
    letI := hc
    infer_instance
  let i : MatrixRealization G := ⟨n, L, c, e.hom ≫ f, hc'⟩
  have h (g : RationalPoints G) :
      i.onPoints g = Matrix.SpecialLinearGroup.toGL (s.hom.app (CommAlgCat.of k k) g) := by
    let R := CommAlgCat.of k k
    let y := s.hom.app R g
    change c.hom.app R (g ≫ (e.hom ≫ f).hom.hom) = Matrix.SpecialLinearGroup.toGL y
    have hcomp := congrArg (fun z => c.hom.app R (z.app R g))
      (show (groupPointsFunctor k).map (e.hom ≫ f) = (s ≪≫ b.symm).hom ≫ α by
        rw [Functor.map_comp, he, hf])
    change _ = c.hom.app R (c.inv.app R
      (Matrix.SpecialLinearGroup.toGL (b.hom.app R (b.inv.app R y)))) at hcomp
    exact hcomp.trans ((GrpCat.hom_inv_apply (c.app R) _).trans
      (congrArg Matrix.SpecialLinearGroup.toGL (GrpCat.hom_inv_apply (b.app R) y)))
  refine ⟨i, ?_⟩
  ext g
  change g ∈ (specialLinearIntegralMap s).range ↔ i.onPoints g ∈
    (Matrix.GeneralLinearGroup.map (algebraMap ℤ ℚ)).range
  rw [h g]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨Matrix.SpecialLinearGroup.toGL x, ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro l m
    rw [show s.hom.app (CommAlgCat.of ℚ ℚ) (specialLinearIntegralMap s x) =
      Matrix.SpecialLinearGroup.map (algebraMap ℤ ℚ) x from
      GrpCat.hom_inv_apply (s.app (CommAlgCat.of ℚ ℚ)) _]
    rfl
  · rintro ⟨x, hx⟩
    have hd : x.val.det = 1 := by
      apply (IsFractionRing.injective ℤ ℚ)
      rw [map_one, (algebraMap ℤ ℚ).map_det]
      have hmat := congrArg
        (fun y : Matrix.GeneralLinearGroup (Index.{0} n) ℚ => y.val.det) hx
      exact hmat.trans ((s.hom.app (CommAlgCat.of ℚ ℚ) g).property)
    refine ⟨⟨x.val, hd⟩, ?_⟩
    apply (Function.LeftInverse.injective
      (GrpCat.inv_hom_apply (s.app (CommAlgCat.of ℚ ℚ))))
    let R := CommAlgCat.of ℚ ℚ
    let v : Matrix.SpecialLinearGroup (Index.{0} n) ℤ := ⟨x.val, hd⟩
    exact (GrpCat.hom_inv_apply (s.app R) (Matrix.SpecialLinearGroup.map (algebraMap ℤ ℚ) v)).trans
      (Subtype.ext (congrArg Units.val hx))

private theorem specialLinearArithmetic : SpecialLinearArithmetic := by
  intro n G s
  obtain ⟨i, he⟩ := specialLinearIntegralRealization n G s
  refine ⟨⟨i, he ▸ Subgroup.Commensurable.refl _⟩, fun m hm => ?_⟩
  have hc : (principalCongruence n m).FiniteIndex := by
    have h : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    haveI : Finite (ℤ ⧸ Ideal.span {(m : ℤ)}) :=
      Ring.HasFiniteQuotients.finiteQuotient (by simpa using h)
    haveI : Finite (Matrix.SpecialLinearGroup (Index.{0} n) (ℤ ⧸ Ideal.span {(m : ℤ)})) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    unfold principalCongruence
    infer_instance
  refine ⟨hc, ⟨i, ?_⟩⟩
  rw [← he, ← Subgroup.map_top]
  exact (Subgroup.Commensurable.top_right_iff.mpr hc).map (specialLinearIntegralMap s)

private theorem realEmbeddings : RealEmbeddings := by
  have hreal (G : AffineAlgebraicGroup ℚ) : Function.Injective (realPointMap G) := by
    obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.prop.1
    intro g h hgh
    let p : A.unop ⟶ CommAlgCat.of ℚ ℚ := coordinateMap (g ≫ e.inv)
    let q : A.unop ⟶ CommAlgCat.of ℚ ℚ := coordinateMap (h ≫ e.inv)
    let f : CommAlgCat.of ℚ ℚ ⟶ CommAlgCat.of ℚ ℝ := CommAlgCat.ofHom (Algebra.ofId ℚ ℝ)
    have hh : (testSpec ℚ).map (p ≫ f).op = (testSpec ℚ).map (q ≫ f).op := by
      rw [CategoryTheory.op_comp, CategoryTheory.op_comp, Functor.map_comp, Functor.map_comp,
        coordinateMap_spec, coordinateMap_spec, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ e.inv) hgh
    have he := Quiver.Hom.op_inj ((algSpec.fullyFaithful (R := CommRingCat.of ℚ)).map_injective hh)
    have hpq : p = q := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro x
      exact (algebraMap ℚ ℝ).injective (congrArg (fun z : A.unop ⟶ CommAlgCat.of ℚ ℝ => z.hom x) he)
    apply (cancel_mono e.inv).mp
    have hmap : (testSpec ℚ).map p.op = (testSpec ℚ).map q.op :=
      congrArg (fun z : A.unop ⟶ CommAlgCat.of ℚ ℚ => (testSpec ℚ).map z.op) hpq
    calc
      g ≫ e.inv = (testSpec ℚ).map p.op := (coordinateMap_spec (g ≫ e.inv)).symm
      _ = (testSpec ℚ).map q.op := hmap
      _ = h ≫ e.inv := coordinateMap_spec (h ≫ e.inv)
  refine ⟨hreal, fun n G s => ⟨?_, ?_⟩⟩
  · refine (hreal G).comp ?_
    intro x y hxy
    let R := CommAlgCat.of ℚ ℚ
    let S := s.app R
    have h := (Function.LeftInverse.injective (GrpCat.hom_inv_apply S)) hxy
    change Matrix.SpecialLinearGroup.map (algebraMap ℤ ℚ) x =
      Matrix.SpecialLinearGroup.map (algebraMap ℤ ℚ) y at h
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    exact (IsFractionRing.injective ℤ ℚ)
      (congrArg (fun a : Matrix.SpecialLinearGroup (Index.{0} n) ℚ => a.val i j)
        h)
  · apply MonoidHom.ext
    intro x
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have h := congrArg (fun z => z ((specialLinearIntegralMap s) x))
      (s.hom.naturality (CommAlgCat.ofHom (Algebra.ofId ℚ ℝ)))
    change ((s.hom.app (CommAlgCat.of ℚ ℝ)) (realPointMap G (specialLinearIntegralMap s x))).val i j =
      algebraMap ℤ ℝ (x.val i j)
    let Q := CommAlgCat.of ℚ ℚ
    let R := CommAlgCat.of ℚ ℝ
    have hnat : (s.hom.app R) (realPointMap G (specialLinearIntegralMap s x)) =
        Matrix.SpecialLinearGroup.map (algebraMap ℚ ℝ)
          ((s.hom.app Q) (specialLinearIntegralMap s x)) := h
    rw [hnat]
    change algebraMap ℚ ℝ (((s.hom.app Q) (specialLinearIntegralMap s x)).val i j) = _
    have hs : (s.hom.app Q) (specialLinearIntegralMap s x) =
        Matrix.SpecialLinearGroup.map (algebraMap ℤ ℚ) x :=
      GrpCat.hom_inv_apply (s.app Q) _
    rw [hs]
    exact (IsScalarTower.algebraMap_apply ℤ ℚ ℝ (x.val i j)).symm

open private dimension_of_iso standard_torus_dimension split_baseChange_dimension reductive_of_semisimple
  from LinearAlgebraicGroups.Descent.RelativeRank

private theorem specialLinearRank
    (hs : Specs.SpecialLinearDatum.Semisimple.{u})
    (ht : Specs.SpecialLinearDatum.SplitDiagonalTorus.{u}) : SpecialLinearRank.{u} := by
  intro k _ r G s
  obtain ⟨T, hc, hm⟩ := ht k r G s
  have hred := reductive_of_semisimple G (hs k r G s)
  let W := StandardGroups.multiplicativePowerGroup k (Index.{u} r)
  let T₀ := Specs.Unipotent.closedSubgroupAlgebraicGroup T.subgroup
  let e : T.subgroup.group ≅ W.val := affineGroupIsoOfPoints T₀.prop.1 W.prop.1
    (T.pointsIso ≪≫ (StandardGroups.multiplicativePowerGroupPointsIso k (Index.{u} r)).symm)
  have hdim := (split_baseChange_dimension (AlgebraicClosure k) T.split).2
  calc
    Specs.RelativeRank.relativeRank G = Specs.RelativeRank.geometricRank G :=
      (Descent.RelativeRank.rankComparison G hred).2 ⟨hred, T.subgroup, T.split, hc, hm⟩
    _ = topologicalKrullDim ((groupBaseChange k (AlgebraicClosure k)).obj
          T.subgroup.group).X.left :=
      ((Descent.RelativeRank.maximalGeometricDimension G hred).2 _ hm).symm
    _ = topologicalKrullDim T.subgroup.group.X.left := hdim
    _ = topologicalKrullDim W.val.X.left := dimension_of_iso e
    _ = (r : WithBot ℕ∞) := standard_torus_dimension r

/-- Conditional draft for F11, using the ordered frozen special-linear premises. -/
theorem integralModels_conditional.{v}
    (_ : Specs.SpecialLinearDatum.AdjacentPositiveRoots)
    (_ : Specs.SpecialLinearDatum.MatrixPinnedDatum.{v})
    (_ : Specs.SpecialLinearDatum.NormalizedWord.{v})
    (_ : Specs.SpecialLinearDatum.RankOneTrivial.{v})
    (hs : Specs.SpecialLinearDatum.Semisimple.{v})
    (_ : Specs.SpecialLinearDatum.SimpleCartanPairings)
    (_ : Specs.SpecialLinearDatum.SimpleCorootBasis)
    (_ : Specs.SpecialLinearDatum.SizeOneLattices)
    (_ : Specs.SpecialLinearDatum.SizeTwoLattices)
    (ht : Specs.SpecialLinearDatum.SplitDiagonalTorus.{v}) :
    ArithmeticIntegralModels.{v} :=
  ⟨rationalIndependence, numberFieldIndependence, arithmeticClass, specialLinearArithmetic,
    realEmbeddings, specialLinearRank hs ht⟩

end

end LinearAlgebraicGroups.Arithmetic.IntegralModels

universe v8_closure_6f451c3e9caa76c5_u0
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«IntegralModels».«integralModels» : _root_.«LinearAlgebraicGroups».«Specs».«IntegralModels».«ArithmeticIntegralModels».{v8_closure_6f451c3e9caa76c5_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«IntegralModels».«integralModels_conditional».{v8_closure_6f451c3e9caa76c5_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«adjacentPositiveRoots») (@_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«matrixPinnedDatum».{v8_closure_6f451c3e9caa76c5_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«normalizedWord».{v8_closure_6f451c3e9caa76c5_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«rankOneTrivial».{v8_closure_6f451c3e9caa76c5_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«semisimple».{v8_closure_6f451c3e9caa76c5_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«simpleCartanPairings») (@_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«simpleCorootBasis») (@_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«sizeOneLattices») (@_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«sizeTwoLattices») (@_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«splitDiagonalTorus».{v8_closure_6f451c3e9caa76c5_u0})
