import Specs.LinearAlgebraicGroups.Reductive.RealTori
import LinearAlgebraicGroups.Affine.StandardGroups
import LinearAlgebraicGroups.Affine.ClosedSubgroups
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Complex.Polynomial.Basic

import LinearAlgebraicGroups.Reductive.TorusCentralizer
open AlgebraicGeometry CategoryTheory Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

namespace LinearAlgebraicGroups.Reductive.RealTori

open Specs.RealTori
open Specs.GeometricRadicals (IsTorus IsSplitTorus IsMaximalTorus baseChangedSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme)

open private Representation specialLinearRepresentation
  spectrumPointsIso from LinearAlgebraicGroups.Affine.StandardGroups
open private Representation.mk Representation.equiv Representation.naturality
  Representation.hopf Representation.convolutionIso Representation.compatible
  from LinearAlgebraicGroups.Affine.StandardGroups

noncomputable section

set_option maxHeartbeats 700000

private abbrev SL := StandardGroups.specialLinearGroup ℝ (Fin 2)
private abbrev slPoints := StandardGroups.specialLinearGroupPointsIso ℝ (Fin 2)

private abbrev Coord := Specs.StandardGroups.SLCoordinates ℝ (Fin 2)

private abbrev entry (i j : Fin 2) : Coord :=
  Ideal.Quotient.mk _ (Specs.StandardGroups.universalMatrix ℝ (Fin 2) i j)

private def diagonal (t : ℝˣ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨diagonalMatrix t, by simp [diagonalMatrix, Matrix.det_fin_two]⟩

private def rotation {R : Type} [CommRing R] (a b : R) (h : a ^ 2 + b ^ 2 = 1) :
    Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨rotationMatrix a b, by
    rw [rotationMatrix, Matrix.det_fin_two]
    simpa [pow_two] using h⟩

private abbrev aevalSL := @specialLinearRepresentation ℝ _ (Fin 2) _ _

private abbrev constant (R : TestAlgebra ℝ) (c : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.SpecialLinearGroup (Fin 2) R :=
  Matrix.SpecialLinearGroup.map (algebraMap ℝ R) c

private abbrev centralizerPoints (c : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    TestAlgebra ℝ ⥤ GrpCat where
  obj R := GrpCat.of (Subgroup.centralizer {constant R c})
  map {R S} f := GrpCat.ofHom
    (((SL₂Points.map f).hom.comp (Subgroup.centralizer {constant R c}).subtype).codRestrict
      (Subgroup.centralizer {constant S c}) (by
        intro x
        have hc : (SL₂Points.map f).hom (constant R c) = constant S c := by
          apply Matrix.SpecialLinearGroup.ext
          intro i j
          exact f.hom.commutes (c i j)
        have h : Commute x.val (constant R c) :=
          Subgroup.mem_centralizer_singleton_iff.mp x.property
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hc ▸ h.map (SL₂Points.map f).hom)))
  map_id R := by apply GrpCat.ext; intro x; apply Subtype.ext; rfl
  map_comp f g := by apply GrpCat.ext; intro x; apply Subtype.ext; rfl

private def commutationEquation (c : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ij : Fin 2 × Fin 2) :
    Coord :=
  ∑ l : Fin 2, (entry ij.1 l * algebraMap ℝ Coord (c l ij.2) -
    algebraMap ℝ Coord (c ij.1 l) * entry l ij.2)

private def commutationIdeal (c : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Ideal Coord :=
  Ideal.span (Set.range (commutationEquation c))

private abbrev CentralizerCoord (c : Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
  Coord ⧸ commutationIdeal c

private abbrev quotientMap (c : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Coord →ₐ[ℝ] CentralizerCoord c :=
  Ideal.Quotient.mkₐ ℝ (commutationIdeal c)

private theorem evaluates_commuting (R : TestAlgebra ℝ)
    (c : Matrix.SpecialLinearGroup (Fin 2) ℝ) (f : Coord →ₐ[ℝ] R) :
    Representation.equiv aevalSL R f ∈ Subgroup.centralizer {constant R c} ↔
      ∀ ij, f (commutationEquation c ij) = 0 := by
  let g : Matrix.SpecialLinearGroup (Fin 2) R := Representation.equiv aevalSL R f
  change g ∈ Subgroup.centralizer {constant R c} ↔ _
  rw [Subgroup.mem_centralizer_singleton_iff]
  have eval (i j : Fin 2) :
      f (commutationEquation c (i, j)) =
        (g.val * (constant R c).val) i j - ((constant R c).val * g.val) i j := by
    simp [commutationEquation, Matrix.mul_apply, Finset.sum_sub_distrib, g]
    rfl
  constructor
  · intro h ij
    rw [eval, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, h, sub_self]
  · intro h
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have e := h (i, j)
    rw [eval] at e
    exact sub_eq_zero.mp e

private def centralizerEquiv (c : Matrix.SpecialLinearGroup (Fin 2) ℝ) (R : TestAlgebra ℝ) :
    (CentralizerCoord c →ₐ[ℝ] R) ≃ Subgroup.centralizer {constant R c} where
  toFun f := ⟨Representation.equiv aevalSL R (f.comp (quotientMap c)), by
    apply (evaluates_commuting R c _).mpr
    intro ij
    have h : quotientMap c (commutationEquation c ij) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨ij, rfl⟩)
    change f (quotientMap c (commutationEquation c ij)) = 0
    rw [h, map_zero]⟩
  invFun g :=
    let f := (Representation.equiv aevalSL R).symm g.val
    Ideal.Quotient.liftₐ (commutationIdeal c) f (by
      let e : (Coord →ₐ[ℝ] R) ≃ Matrix.SpecialLinearGroup (Fin 2) R :=
        Representation.equiv aevalSL R
      have hg : e f ∈ Subgroup.centralizer {constant R c} := by
        change e (e.symm g.val) ∈ _
        rw [e.apply_symm_apply]
        exact g.property
      have h := (evaluates_commuting R c f).mp hg
      have hle : commutationIdeal c ≤ RingHom.ker f.toRingHom := by
        apply Ideal.span_le.mpr
        rintro _ ⟨ij, rfl⟩
        exact RingHom.mem_ker.mpr (h ij)
      exact fun x hx ↦ RingHom.mem_ker.mp (hle hx))
  left_inv := by
    intro f
    apply Ideal.Quotient.algHom_ext ℝ
    change (Representation.equiv aevalSL R).symm
      (Representation.equiv aevalSL R (f.comp (quotientMap c))) = f.comp (quotientMap c)
    exact Equiv.symm_apply_apply _ _
  right_inv := by
    intro g
    apply Subtype.ext
    exact (Representation.equiv aevalSL R).apply_symm_apply _

private def centralizerRepresentation (c : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Representation (CentralizerCoord c) (centralizerPoints c) :=
  Representation.mk (centralizerEquiv c) (by
    intro R S f h
    apply Subtype.ext
    exact Representation.naturality aevalSL f (h.comp (quotientMap c)))

private abbrev centralizerHopf (c : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    HopfAlgebra ℝ (CentralizerCoord c) :=
  Representation.hopf (centralizerRepresentation c)

private def centralizerGroup (c : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    AffineAlgebraicGroup ℝ :=
  letI := centralizerHopf c
  Specs.StandardGroups.spectrum ℝ (CentralizerCoord c)

private def centralizerPointsIso (c : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (groupPointsFunctor ℝ).obj (centralizerGroup c).val ≅ centralizerPoints c :=
  letI := centralizerHopf c
  spectrumPointsIso (Representation.convolutionIso (centralizerRepresentation c))

private def centralizerQuotient (c : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    letI := StandardGroups.specialLinearHopf ℝ (Fin 2)
    letI := centralizerHopf c
    (CommHopfAlgCat.of ℝ Coord ⟶ CommHopfAlgCat.of ℝ (CentralizerCoord c)) := by
  letI := StandardGroups.specialLinearHopf ℝ (Fin 2)
  letI := centralizerHopf c
  obtain ⟨hmul, hone, _⟩ := Representation.compatible aevalSL (centralizerRepresentation c) (quotientMap c)
    (fun R ↦ (Subgroup.centralizer {constant R c}).subtype) (fun _ _ ↦ rfl)
  exact CommHopfAlgCat.ofHom (BialgHom.ofAlgHom (quotientMap c) hone.symm hmul)

private def centralizer (c : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ClosedSubgroup SL.val := by
  refine ⟨(centralizerGroup c).val, specGroupMap (centralizerQuotient c), ?_⟩
  let q : CommRingCat.of Coord ⟶ CommRingCat.of (CentralizerCoord c) :=
    CommRingCat.ofHom (quotientMap c).toRingHom
  change IsClosedImmersion (Spec.map q)
  apply IsClosedImmersion.spec_of_surjective
  exact Ideal.Quotient.mk_surjective

private theorem spectrumPointsIso_eval {A : Type} [CommRing A] [HopfAlgebra ℝ A]
    [Algebra.FiniteType ℝ A] {F : TestAlgebra ℝ ⥤ GrpCat}
    (c : convolutionPoints (CommHopfAlgCat.of ℝ A) ≅ F) (R : TestAlgebra ℝ)
    (f : WithConv (A →ₐ[ℝ] R)) :
    (spectrumPointsIso c).hom.app R
      ((hopfSpecPointIso (CommHopfAlgCat.of ℝ A)).hom.app R f) = c.hom.app R f := by
  let e := hopfSpecPointIso (CommHopfAlgCat.of ℝ A)
  have h := ConcreteCategory.congr_hom (e.app R).hom_inv_id f
  exact congrArg (fun x : (convolutionPoints (CommHopfAlgCat.of ℝ A)).obj R ↦ c.hom.app R x) h

set_option linter.style.haveILetI false in
private theorem centralizer_matrixPoint (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (R : TestAlgebra ℝ) (p : Points (centralizer c).group.X R) :
    matrixPoint slPoints (centralizer c) R p =
      ((centralizerPointsIso c).hom.app R p : Subgroup.centralizer {constant R c}).val := by
  letI := StandardGroups.specialLinearHopf ℝ (Fin 2)
  letI := centralizerHopf c
  let A : HopfAlgebraCategory ℝ := by
    letI := StandardGroups.specialLinearHopf ℝ (Fin 2)
    exact CommHopfAlgCat.of ℝ Coord
  let B : HopfAlgebraCategory ℝ := by
    letI := centralizerHopf c
    exact CommHopfAlgCat.of ℝ (CentralizerCoord c)
  let e := hopfSpecPointIso B
  let p' : ((groupPointsFunctor ℝ).obj (specGroup B)).obj R := p
  obtain ⟨f, hp⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.app R)).2 p'
  have h :
      ((groupPointsFunctor ℝ).map (centralizer c).inclusion).app R (e.hom.app R f) =
        (hopfSpecPointIso A).hom.app R (toConv (f.ofConv.comp (quotientMap c))) := by
    let q : CommRingCat.of Coord ⟶ CommRingCat.of (CentralizerCoord c) :=
      CommRingCat.ofHom (quotientMap c).toRingHom
    let a : CommRingCat.of (CentralizerCoord c) ⟶ CommRingCat.of R :=
      CommRingCat.ofHom f.ofConv.toRingHom
    apply Over.OverMorphism.ext
    change Spec.map a ≫ Spec.map q = Spec.map (q ≫ a)
    exact (Spec.map_comp q a).symm
  change slPoints.hom.app R (((groupPointsFunctor ℝ).map (centralizer c).inclusion).app R p') =
    ((centralizerPointsIso c).hom.app R p' : Subgroup.centralizer {constant R c}).val
  have hA : slPoints.hom.app R ((hopfSpecPointIso A).hom.app R
      (toConv (f.ofConv.comp (quotientMap c)))) =
      Representation.equiv aevalSL R (f.ofConv.comp (quotientMap c)) :=
    spectrumPointsIso_eval (Representation.convolutionIso aevalSL) R _
  have hB : (centralizerPointsIso c).hom.app R (e.hom.app R f) =
      centralizerEquiv c R f.ofConv :=
    spectrumPointsIso_eval (Representation.convolutionIso (centralizerRepresentation c)) R _
  let left (x : Points (centralizer c).group.X R) := matrixPoint slPoints (centralizer c) R x
  let right (x : Points (centralizer c).group.X R) :=
    ((centralizerPointsIso c).hom.app R x : Subgroup.centralizer {constant R c}).val
  let val (x : (centralizerPoints c).obj R) := (x : Subgroup.centralizer {constant R c}).val
  exact (congrArg left hp.symm).trans
    ((congrArg (fun x : Points SL.val.X R ↦ slPoints.hom.app R x) h).trans
      (hA.trans ((congrArg val hB).symm.trans (congrArg right hp))))

private theorem centralizer_range (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (R : TestAlgebra ℝ) (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    (∃ p, matrixPoint slPoints (centralizer c) R p = g) ↔
      g ∈ Subgroup.centralizer {constant R c} := by
  constructor
  · rintro ⟨p, rfl⟩
    rw [centralizer_matrixPoint]
    exact ((centralizerPointsIso c).hom.app R p : Subgroup.centralizer {constant R c}).property
  · intro h
    let z : (centralizerPoints c).obj R := (⟨g,h⟩ : Subgroup.centralizer {constant R c})
    let p : Points (centralizer c).group.X R := (centralizerPointsIso c).inv.app R z
    refine ⟨p, (centralizer_matrixPoint c R p).trans ?_⟩
    exact congrArg (fun x : (centralizerPoints c).obj R ↦
      (x : Subgroup.centralizer {constant R c}).val)
        (ConcreteCategory.congr_hom ((centralizerPointsIso c).app R).inv_hom_id z)

private def twoUnit : ℝˣ := Units.mk0 2 (by norm_num)
private def diagonalTest := diagonal twoUnit

private def rotationTest := rotation (0 : ℝ) 1 (by norm_num)

private abbrev D := centralizer diagonalTest
private abbrev T := centralizer rotationTest

private abbrev MatrixSL (R : Type) [CommRing R] := Matrix.SpecialLinearGroup (Fin 2) R

private abbrev DiagonalPoints (R : TestAlgebra ℝ) :=
  Subgroup.centralizer ({constant R diagonalTest} : Set (MatrixSL R))

private abbrev RotationPoints (R : TestAlgebra ℝ) :=
  Subgroup.centralizer ({constant R rotationTest} : Set (MatrixSL R))

private theorem diagonal_iff (R : TestAlgebra ℝ) (g : MatrixSL R) :
    g ∈ DiagonalPoints R ↔ ∃ t : Rˣ, g.val = diagonalMatrix t := by
  let a : R := algebraMap ℝ R 2
  let d : R := algebraMap ℝ R (2⁻¹)
  have hc : (constant R diagonalTest).val = !![a, 0; 0, d] := by
    ext i j
    change algebraMap ℝ R (diagonalTest i j) = _
    fin_cases i <;> fin_cases j <;> simp [diagonalTest, diagonal, diagonalMatrix, a, d, twoUnit]
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hm : g.val * !![a, 0; 0, d] = !![a, 0; 0, d] * g.val := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul, hc] using congrArg Subtype.val h
    have e01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R ↦ M 0 1) hm
    have e10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R ↦ M 1 0) hm
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
    have hunit : IsUnit (d - a) := by
      rw [← map_sub]
      exact (isUnit_iff_ne_zero.mpr (by norm_num : (2⁻¹ : ℝ) - 2 ≠ 0)).map (algebraMap ℝ R)
    have h01 : g 0 1 = 0 := hunit.mul_right_cancel (by
      rw [mul_sub, zero_mul, e01, mul_comm a, sub_self])
    have h10 : g 1 0 = 0 := hunit.mul_right_cancel (by
      rw [mul_sub, zero_mul, mul_comm _ d, ← e10, sub_self])
    have hdet : g 0 0 * g 1 1 = 1 := by
      simpa only [Matrix.det_fin_two, h01, h10, zero_mul, sub_zero] using g.det_coe
    let t : Rˣ := ⟨g 0 0, g 1 1, hdet, by rwa [mul_comm]⟩
    refine ⟨t, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonalMatrix, t, h01, h10]
  · rintro ⟨t, ht⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (g.val * (constant R diagonalTest).val) i j =
      ((constant R diagonalTest).val * g.val) i j
    rw [ht, hc]
    fin_cases i <;> fin_cases j <;> simp [diagonalMatrix, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem rotation_iff (R : TestAlgebra ℝ) (g : MatrixSL R) :
    g ∈ RotationPoints R ↔ ∃ a b : R, a ^ 2 + b ^ 2 = 1 ∧ g.val = rotationMatrix a b := by
  have hc : (constant R rotationTest).val = !![0, -1; 1, 0] := by
    ext i j
    change algebraMap ℝ R (rotationTest i j) = _
    fin_cases i <;> fin_cases j <;> simp [rotationTest, rotation, rotationMatrix]
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hm : g.val * !![0, -1; 1, 0] = !![0, -1; 1, 0] * g.val := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul, hc] using congrArg Subtype.val h
    have e00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R ↦ M 0 0) hm
    have e10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R ↦ M 1 0) hm
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
    have he : g.val = rotationMatrix (g 0 0) (g 1 0) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [rotationMatrix, e00, e10]
    refine ⟨g 0 0, g 1 0, ?_, he⟩
    have hd := g.det_coe
    rw [he, rotationMatrix, Matrix.det_fin_two] at hd
    simpa [pow_two] using hd
  · rintro ⟨a, b, _, hab⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (g.val * (constant R rotationTest).val) i j =
      ((constant R rotationTest).val * g.val) i j
    rw [hab, hc]
    fin_cases i <;> fin_cases j <;>
      simp [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two]

private theorem rotation_entries (R : TestAlgebra ℝ) (g : RotationPoints R) :
    g.val.val = rotationMatrix (g.val 0 0) (g.val 1 0) ∧
      (g.val 0 0) ^ 2 + (g.val 1 0) ^ 2 = 1 := by
  obtain ⟨a, b, h, e⟩ := (rotation_iff R g.val).mp g.property
  have ha : g.val 0 0 = a := congrArg (fun M : Matrix (Fin 2) (Fin 2) R ↦ M 0 0) e
  have hb : g.val 1 0 = b := congrArg (fun M : Matrix (Fin 2) (Fin 2) R ↦ M 1 0) e
  exact ⟨by rwa [ha, hb], by rwa [ha, hb]⟩

private def diagonalParam (R : TestAlgebra ℝ) (t : Rˣ) : DiagonalPoints R :=
  ⟨⟨diagonalMatrix t, by simp [diagonalMatrix, Matrix.det_fin_two]⟩,
    (diagonal_iff R _).mpr ⟨t, rfl⟩⟩

private def diagonalMulEquiv (R : TestAlgebra ℝ) : Rˣ ≃* DiagonalPoints R :=
  MulEquiv.ofBijective
    (show Rˣ →* DiagonalPoints R from
      { toFun := diagonalParam R
        map_one' := by
          apply Subtype.ext
          apply Matrix.SpecialLinearGroup.ext
          intro i j
          fin_cases i <;> fin_cases j <;> simp [diagonalParam, diagonalMatrix]
        map_mul' := by
          intro s t
          apply Subtype.ext
          apply Matrix.SpecialLinearGroup.ext
          intro i j
          change diagonalMatrix (s * t) i j = (diagonalMatrix s * diagonalMatrix t) i j
          fin_cases i <;> fin_cases j <;>
            simp [diagonalMatrix, Matrix.mul_apply, Fin.sum_univ_two, mul_comm] })
    (by
      constructor
      · intro t s h
        apply Units.ext
        exact congrArg (fun x : DiagonalPoints R ↦ x.val 0 0) h
      · intro g
        obtain ⟨t, h⟩ := (diagonal_iff R g.val).mp g.property
        exact ⟨t, Subtype.ext (Subtype.ext h.symm)⟩)



private theorem diagonalMulEquiv_symm_val (R : TestAlgebra ℝ) (g : DiagonalPoints R) :
    ((diagonalMulEquiv R).symm g : R) = g.val 0 0 := by
  obtain ⟨t, rfl⟩ := (diagonalMulEquiv R).surjective g
  rw [MulEquiv.symm_apply_apply]
  rfl

private def diagonalUnitIso :
    centralizerPoints diagonalTest ≅ Specs.StandardGroups.multiplicativePoints ℝ :=
  NatIso.ofComponents (fun R ↦ (diagonalMulEquiv R).symm.toGrpIso) (by
    intro R S f
    apply GrpCat.ext
    intro g
    apply Units.ext
    let m : DiagonalPoints S := (centralizerPoints diagonalTest).map f g
    change ((diagonalMulEquiv S).symm m : S) = f.hom ((diagonalMulEquiv R).symm g : R)
    rw [diagonalMulEquiv_symm_val, diagonalMulEquiv_symm_val]
    rfl)


section PointComparisons

variable {k : Type} [Field k]

private def groupIsoOfPoints {G H : GroupScheme k} (hG : IsAffine G.X.left)
    (hH : IsAffine H.X.left) (e : (groupPointsFunctor k).obj G ≅ (groupPointsFunctor k).obj H) :
    G ≅ H := by
  let f := (groupHomEquiv G H hG).symm e.hom
  let g := (groupHomEquiv H G hH).symm e.inv
  have hf : (groupPointsFunctor k).map f = e.hom :=
    (groupHomEquiv G H hG).apply_symm_apply _
  have hg : (groupPointsFunctor k).map g = e.inv :=
    (groupHomEquiv H G hH).apply_symm_apply _
  refine ⟨f, g, ?_, ?_⟩
  · apply (groupHomEquiv G G hG).injective
    change (groupPointsFunctor k).map (f ≫ g) = (groupPointsFunctor k).map (𝟙 G)
    simp [hf, hg]
  · apply (groupHomEquiv H H hH).injective
    change (groupPointsFunctor k).map (g ≫ f) = (groupPointsFunctor k).map (𝟙 H)
    simp [hf, hg]

private theorem map_groupIsoOfPoints {G H : GroupScheme k} (hG : IsAffine G.X.left)
    (hH : IsAffine H.X.left) (e : (groupPointsFunctor k).obj G ≅ (groupPointsFunctor k).obj H) :
    (groupPointsFunctor k).map (groupIsoOfPoints hG hH e).hom = e.hom :=
  (groupHomEquiv G H hG).apply_symm_apply _

private def baseChangePointsIso (K : Type) [Field K] [Algebra k K] (G : GroupScheme k) :
    (groupPointsFunctor K).obj ((groupBaseChange k K).obj G) ≅
      restrictTestAlgebra k K ⋙ (groupPointsFunctor k).obj G :=
  NatIso.ofComponents (fun R ↦ (baseChangePointGroupEquiv K G R).toGrpIso)
    (by
      intro R S f
      apply GrpCat.ext
      intro p
      exact (baseChangePointsNaturality k K G.X f p).symm)

private theorem affine_baseChange (K : Type) [Field K] [Algebra k K] (G : GroupScheme k)
    (h : IsAffine G.X.left) : IsAffine ((groupBaseChange k K).obj G).X.left := by
  let := h
  change IsAffine (Limits.pullback G.X.hom (fieldSpecMap k K))
  infer_instance

private abbrev rankOne (k : Type) [Field k] :=
  Specs.StandardGroups.multiplicativePowerGroup k (ULift (Fin 1))

private def rankOnePointsIso (k : Type) [Field k] :
    (groupPointsFunctor k).obj (rankOne k).val ≅ Specs.StandardGroups.multiplicativePoints k :=
  StandardGroups.multiplicativePowerGroupPointsIso k (ULift (Fin 1)) ≪≫
    NatIso.ofComponents (fun R ↦
      (MulEquiv.piUnique (fun _ : ULift (Fin 1) ↦ Rˣ)).toGrpIso) (by
      intro R S f
      apply GrpCat.ext
      intro x
      rfl)

private theorem split_isTorus {H : GroupScheme k} (h : IsSplitTorus H) : IsTorus H := by
  obtain ⟨r, ⟨e⟩⟩ := h
  have h : fieldSpecMap k k = 𝟙 (Spec (CommRingCat.of k)) := by
    change Spec.map (𝟙 (CommRingCat.of k)) = _
    exact Spec.map_id _
  let i : baseChange k k ≅ 𝟭 (SchemeOver k) :=
    eqToIso (congrArg (fun f : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) ↦ Over.pullback f) h) ≪≫
      Over.pullbackId
  exact ⟨k, inferInstance, inferInstance, inferInstance, r,
    ⟨((Functor.mapGrpNatIso i) ≪≫ Functor.mapGrpIdIso).app H ≪≫ e⟩⟩

end PointComparisons

private def diagonalSplit (K : Type) [Field K] [Algebra ℝ K] :
    (groupBaseChange ℝ K).obj D.group ≅ (rankOne K).val :=
  groupIsoOfPoints (affine_baseChange K _ (centralizerGroup diagonalTest).property.1)
    (rankOne K).property.1
    (baseChangePointsIso K D.group ≪≫
      Functor.isoWhiskerLeft (restrictTestAlgebra ℝ K) (centralizerPointsIso diagonalTest) ≪≫
      Functor.isoWhiskerLeft (restrictTestAlgebra ℝ K) diagonalUnitIso ≪≫
      NatIso.ofComponents (fun R ↦ Iso.refl _) (by intro R S f; rfl) ≪≫
      (rankOnePointsIso K).symm)

private def diagonalRealSplit : D.group ≅ (rankOne ℝ).val :=
  groupIsoOfPoints (centralizerGroup diagonalTest).property.1 (rankOne ℝ).property.1
    (centralizerPointsIso diagonalTest ≪≫ diagonalUnitIso ≪≫ (rankOnePointsIso ℝ).symm)

section RotationSplitting

variable {K : Type} [Field K] [Algebra ℝ K]

private abbrev restrictR (R : TestAlgebra K) := (restrictTestAlgebra ℝ K).obj R

private def rotationParam (R : TestAlgebra ℝ) (a b : R) (h : a ^ 2 + b ^ 2 = 1) :
    RotationPoints R :=
  ⟨rotation a b h, (rotation_iff R _).mpr ⟨a, b, h, rfl⟩⟩

private theorem rotation_mul_entries {R : TestAlgebra ℝ} (g h : RotationPoints R) :
    (g * h).val 0 0 = g.val 0 0 * h.val 0 0 - g.val 1 0 * h.val 1 0 ∧
    (g * h).val 1 0 = g.val 1 0 * h.val 0 0 + g.val 0 0 * h.val 1 0 := by
  change (g.val.val * h.val.val) 0 0 = _ ∧ (g.val.val * h.val.val) 1 0 = _
  rw [rotation_entries R g |>.1, rotation_entries R h |>.1]
  simp [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]

private theorem eigenvalue_mul {R : Type} [CommRing R] {i : R} (hi : i * i = -1)
    (a b : R) : (a + i * b) * (a - i * b) = a ^ 2 + b ^ 2 := by
  linear_combination -(b ^ 2) * hi

private def rotationEigenUnit (R : TestAlgebra K) (i : K) (hi : i * i = -1)
    (g : RotationPoints (restrictR R)) : Rˣ := by
  let a : R := g.val 0 0
  let b : R := g.val 1 0
  let j := algebraMap K R i
  have hj : j * j = -1 := by simp [j, ← map_mul, hi]
  have hprod : (a + j * b) * (a - j * b) = 1 :=
    (eigenvalue_mul hj a b).trans (rotation_entries (restrictR R) g).2
  exact ⟨a + j * b, a - j * b, hprod, by rwa [mul_comm]⟩

private theorem rotationEigenUnit_mul (R : TestAlgebra K) (i : K) (hi : i * i = -1)
    (g h : RotationPoints (restrictR R)) :
    rotationEigenUnit R i hi (g * h) = rotationEigenUnit R i hi g * rotationEigenUnit R i hi h := by
  apply Units.ext
  let j := algebraMap K R i
  have hj : j * j = -1 := by simp [j, ← map_mul, hi]
  change (g * h).val 0 0 + j * (g * h).val 1 0 =
    (g.val 0 0 + j * g.val 1 0) * (h.val 0 0 + j * h.val 1 0)
  rw [(rotation_mul_entries g h).1, (rotation_mul_entries g h).2]
  linear_combination -(g.val 1 0 * h.val 1 0) * hj

private def rotationUnitEquiv (R : TestAlgebra K) (i : K) (hi : i * i = -1) :
    RotationPoints (restrictR R) ≃* Rˣ :=
  MulEquiv.ofBijective
    ({ toFun := rotationEigenUnit R i hi
       map_one' := by apply Units.ext; change 1 + algebraMap K R i * 0 = 1; simp
       map_mul' := rotationEigenUnit_mul R i hi } : RotationPoints (restrictR R) →* Rˣ)
    (by
      let j := algebraMap K R i
      let half := algebraMap ℝ (restrictR R) ((2 : ℝ)⁻¹)
      have hj : j * j = -1 := by simp [j, ← map_mul, hi]
      have hhalf : (2 : R) * half = 1 := by
        change (2 : restrictR R) * half = 1
        rw [show (2 : restrictR R) = algebraMap ℝ (restrictR R) 2 by exact (map_ofNat (algebraMap ℝ (restrictR R)) 2).symm, ← map_mul]
        norm_num
      constructor
      · intro g h e
        have ep : g.val 0 0 + j * g.val 1 0 = h.val 0 0 + j * h.val 1 0 :=
          congrArg Units.val e
        have em : g.val 0 0 - j * g.val 1 0 = h.val 0 0 - j * h.val 1 0 :=
          congrArg (fun z : Rˣ ↦ (↑z⁻¹ : R)) e
        have ea : g.val 0 0 = h.val 0 0 := by
          linear_combination half * ep + half * em - (g.val 0 0 - h.val 0 0) * hhalf
        have eb : g.val 1 0 = h.val 1 0 := by
          linear_combination (-half * j) * ep + (half * j) * em +
            (2 * half * (g.val 1 0 - h.val 1 0)) * hj -
            (g.val 1 0 - h.val 1 0) * hhalf
        apply Subtype.ext
        apply Subtype.ext
        rw [(rotation_entries (restrictR R) g).1, (rotation_entries (restrictR R) h).1, ea, eb]
      · intro z
        let a : R := half * ((z : R) + ↑z⁻¹)
        let b : R := -half * j * ((z : R) - ↑z⁻¹)
        have hp : a + j * b = z.val := by
          dsimp [a, b]
          linear_combination -(half * ((z : R) - ↑z⁻¹)) * hj + (z : R) * hhalf
        have hm : a - j * b = (↑z⁻¹ : R) := by
          dsimp [a, b]
          linear_combination (half * ((z : R) - ↑z⁻¹)) * hj + (↑z⁻¹ : R) * hhalf
        have h : a ^ 2 + b ^ 2 = 1 := by
          rw [← eigenvalue_mul hj, hp, hm]
          exact z.val_inv
        refine ⟨rotationParam (restrictR R) a b h, ?_⟩
        apply Units.ext
        exact hp)

private def rotationUnitIso (i : K) (hi : i * i = -1) :
    restrictTestAlgebra ℝ K ⋙ centralizerPoints rotationTest ≅
      Specs.StandardGroups.multiplicativePoints K :=
  NatIso.ofComponents (fun R ↦ (rotationUnitEquiv R i hi).toGrpIso) (by
    intro R S f
    apply GrpCat.ext
    intro g
    apply Units.ext
    change f.hom (g.val 0 0) + algebraMap K S i * f.hom (g.val 1 0) =
      f.hom (g.val 0 0 + algebraMap K R i * g.val 1 0)
    simp)

private def rotationPointIso (i : K) (hi : i * i = -1) :
    (groupPointsFunctor K).obj ((groupBaseChange ℝ K).obj T.group) ≅
      Specs.StandardGroups.multiplicativePoints K :=
  baseChangePointsIso K T.group ≪≫
    Functor.isoWhiskerLeft (restrictTestAlgebra ℝ K) (centralizerPointsIso rotationTest) ≪≫
      rotationUnitIso i hi

private def rotationSplit (i : K) (hi : i * i = -1) :
    (groupBaseChange ℝ K).obj T.group ≅ (rankOne K).val :=
  groupIsoOfPoints (affine_baseChange K _ (centralizerGroup rotationTest).property.1)
    (rankOne K).property.1 (rotationPointIso i hi ≪≫ (rankOnePointsIso K).symm)

private theorem rotationSplit_eval (i : K) (hi : i * i = -1)
    (R : TestAlgebra K) (p : Points ((groupBaseChange ℝ K).obj T.group).X R) :
    let M := matrixPoint slPoints T (restrictR R) (baseChangePoint ℝ K T.group.X R p)
    let z : Rˣ := (rankOnePointsIso K).hom.app R
      (((groupPointsFunctor K).map (rotationSplit i hi).hom).app R p)
    (z : R) = M 0 0 + algebraMap K R i * M 1 0 := by
  dsimp only
  rw [rotationSplit, map_groupIsoOfPoints]
  have he : (rotationPointIso i hi ≪≫ (rankOnePointsIso K).symm) ≪≫ rankOnePointsIso K =
      rotationPointIso i hi := by simp
  change (((rotationPointIso i hi ≪≫ (rankOnePointsIso K).symm) ≪≫ rankOnePointsIso K).hom.app R p
    : Rˣ).val = _
  rw [he, centralizer_matrixPoint]
  rfl

end RotationSplitting

section Maximality

open scoped TensorProduct

private theorem mapPoints_injective {k : Type} [Field k] {X : SchemeOver k}
    (hX : IsAffine X.left) {R S : TestAlgebra k} (a : R ⟶ S)
    (ha : Function.Injective a.hom) : Function.Injective (mapPoints (X := X) a) := by
  intro p q he
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr hX
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let f := ff.preimage (p ≫ e.inv)
  let g := ff.preimage (q ≫ e.inv)
  have hf : (testSpec k).map f = p ≫ e.inv := ff.map_preimage _
  have hg : (testSpec k).map g = q ≫ e.inv := ff.map_preimage _
  have hcomp : a.op ≫ f = a.op ≫ g := by
    apply ff.map_injective
    rw [Functor.map_comp, Functor.map_comp, hf, hg, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun t ↦ t ≫ e.inv) he
  have hfg : f = g := by
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    ext x
    exact ha (congrArg (fun b : A.unop ⟶ S ↦ b.hom x) (congrArg Quiver.Hom.unop hcomp))
  exact (cancel_mono e.inv).mp (hf.symm.trans ((congrArg (testSpec k).map hfg).trans hg))

private theorem torus_points_commute {k : Type} [Field k] {S : GroupScheme k}
    (hS : IsAffine S.X.left) (h : IsTorus S) (R : TestAlgebra k) (p q : Points S.X R) :
    p * q = q * p := by
  obtain ⟨E, _, _, _, r, ⟨e⟩⟩ := h
  let B : TestAlgebra E := CommAlgCat.of E (E ⊗[k] R)
  let j₀ : R →ₐ[k] E ⊗[k] R := Algebra.TensorProduct.includeRight
  let C := (restrictTestAlgebra k E).obj B
  let a : R ⟶ C :=
    ConcreteCategory.ofHom (C := CommAlgCat k)
      (@AlgHom.mk k R C _ _ _ R.algebra C.algebra j₀.toRingHom
        (fun x ↦ (j₀.commutes x).trans (IsScalarTower.algebraMap_apply k E _ x)))
  have ha : Function.Injective a.hom := by
    change Function.Injective j₀
    exact Algebra.TensorProduct.includeRight_injective (A := E) (B := R) (algebraMap k E).injective
  apply mapPoints_injective hS a ha
  change (testSpec k).map a.op ≫ (p * q) = (testSpec k).map a.op ≫ (q * p)
  simp only [MonObj.comp_mul]
  let z := (baseChangePointGroupEquiv E S B).symm
  apply z.injective
  rw [map_mul, map_mul]
  let j := (((groupPointsFunctor E).mapIso e) ≪≫
    StandardGroups.multiplicativePowerGroupPointsIso E (ULift (Fin r))).app B
  let f : Points ((groupBaseChange k E).obj S).X B →* (ULift (Fin r) → Bˣ) := j.hom.hom
  have hinj : Function.Injective f := (ConcreteCategory.bijective_of_isIso j.hom).1
  apply hinj
  simp only [map_mul]
  exact mul_comm _ _

variable (K : Type) [Field K] [Algebra ℝ K]

private abbrev changedSL := (groupBaseChange ℝ K).obj SL.val

private def changedSLPoints :
    (groupPointsFunctor K).obj (changedSL K) ≅ restrictTestAlgebra ℝ K ⋙ SL₂Points :=
  baseChangePointsIso K SL.val ≪≫ Functor.isoWhiskerLeft (restrictTestAlgebra ℝ K) slPoints

private abbrev changedCentralizer (c : MatrixSL ℝ) : ClosedSubgroup (changedSL K) :=
  baseChangedSubgroup K (centralizer c)
    (baseChangeClosedSubgroup ℝ K (centralizer c).inclusion (centralizer c).isClosedImmersion)

private def changedCentralizerPoints (c : MatrixSL ℝ) :
    (groupPointsFunctor K).obj (changedCentralizer K c).group ≅
      restrictTestAlgebra ℝ K ⋙ centralizerPoints c :=
  baseChangePointsIso K (centralizer c).group ≪≫
    Functor.isoWhiskerLeft (restrictTestAlgebra ℝ K) (centralizerPointsIso c)

private theorem changedCentralizer_compat (c : MatrixSL ℝ) (R : TestAlgebra K)
    (p : Points (changedCentralizer K c).group.X R) :
    (changedSLPoints K).hom.app R
      (((groupPointsFunctor K).map (changedCentralizer K c).inclusion).app R p) =
      ((changedCentralizerPoints K c).hom.app R p :
        Subgroup.centralizer {constant (restrictR R) c}).val := by
  let S := restrictR R
  change slPoints.hom.app S
      (baseChangePoint ℝ K SL.val.X R
        (p ≫ (baseChange ℝ K).map (centralizer c).inclusion.hom.hom)) = _
  have hn := baseChangePointsSchemeNaturality ℝ K (centralizer c).inclusion.hom.hom R p
  exact (congrArg (fun x : Points SL.val.X S ↦ slPoints.hom.app S x) hn).trans
    (centralizer_matrixPoint c S (baseChangePoint ℝ K (centralizer c).group.X R p))

private theorem changedCentralizer_maximal (c : MatrixSL ℝ)
    (hC : IsTorus (changedCentralizer K c).group) : IsMaximalTorus (changedCentralizer K c) := by
  refine ⟨hC, ?_⟩
  rintro S hS ⟨i, hi⟩
  let P := groupPointsFunctor K
  let C := changedCentralizer K c
  let F := restrictTestAlgebra ℝ K ⋙ centralizerPoints c
  let H := restrictTestAlgebra ℝ K ⋙ SL₂Points
  let E := changedSLPoints K
  let B := changedCentralizerPoints K c
  let : IsAffine (changedSL K).X.left := affine_baseChange K SL.val SL.property.1
  let := S.isClosedImmersion
  have hA := isAffine_of_isAffineHom S.inclusion.hom.hom.left
  let φ : P.obj S.group ⟶ H := P.map S.inclusion ≫ E.hom
  have hmem (R : TestAlgebra K) (p : Points S.group.X R) :
      φ.app R p ∈ Subgroup.centralizer {constant (restrictR R) c} := by
    let y : F.obj R := ⟨constant (restrictR R) c, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    let t : Points C.group.X R := B.inv.app R y
    let q : Points S.group.X R := (P.map i).app R t
    have ht : B.hom.app R t = y := ConcreteCategory.congr_hom (B.app R).inv_hom_id y
    have hq : φ.app R q = constant (restrictR R) c := by
      change E.hom.app R ((P.map S.inclusion).app R ((P.map i).app R t)) = _
      have e : P.map i ≫ P.map S.inclusion = P.map C.inclusion := by rw [← P.map_comp, hi]
      have eq := congrArg (fun f : P.obj C.group ⟶ P.obj (changedSL K) ↦ f.app R t) e
      change (P.map S.inclusion).app R ((P.map i).app R t) = _ at eq
      rw [eq]
      exact (changedCentralizer_compat K c R t).trans (congrArg
        (fun z : F.obj R ↦ (z : Subgroup.centralizer {constant (restrictR R) c}).val) ht)
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [← hq]
    let f : Points S.group.X R →* MatrixSL (restrictR R) := (φ.app R).hom
    change f p * f q = f q * f p
    rw [← map_mul, ← map_mul, torus_points_commute hA hS R p q]
  let ψ : P.obj S.group ⟶ F :=
    { app := fun R ↦ GrpCat.ofHom ((φ.app R).hom.codRestrict
        (Subgroup.centralizer {constant (restrictR R) c}) (hmem R))
      naturality := by
        intro R R' f
        apply GrpCat.ext
        intro p
        apply Subtype.ext
        exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom (φ.naturality f)) p }
  let j := (groupHomEquiv S.group C.group hA).symm (ψ ≫ B.inv)
  have hj : P.map j = ψ ≫ B.inv := (groupHomEquiv _ _ hA).apply_symm_apply _
  refine ⟨j, (groupHomEquiv _ _ hA).injective ?_⟩
  change P.map (j ≫ C.inclusion) = P.map S.inclusion
  rw [P.map_comp]
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  intro p
  apply (ConcreteCategory.bijective_of_isIso (E.hom.app R)).1
  change E.hom.app R ((P.map C.inclusion).app R ((P.map j).app R p)) = φ.app R p
  let x : Points C.group.X R := (P.map j).app R p
  have hx : x = B.inv.app R (ψ.app R p) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hj R) p
  have h := (congrArg (fun v : Points C.group.X R ↦ B.hom.app R v) hx).trans
    (ConcreteCategory.congr_hom (B.app R).inv_hom_id (ψ.app R p))
  exact (changedCentralizer_compat K c R x).trans
    (congrArg (fun v : F.obj R ↦ (v : Subgroup.centralizer {constant (restrictR R) c}).val) h)

end Maximality

private theorem rotation_square_surjective :
    Function.Surjective (fun g : RotationPoints (CommAlgCat.of ℝ ℝ) ↦ g * g) := by
  let R := CommAlgCat.of ℝ ℝ
  intro g
  let z : ℂ := ⟨g.val 0 0, g.val 1 0⟩
  have hz : Complex.normSq z = 1 := by
    rw [Complex.normSq_mk]
    simpa only [pow_two] using (rotation_entries R g).2
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z (n := 2) (by decide)
  have hpow : Complex.normSq w ^ 2 = (1 : ℝ) ^ 2 := by
    rw [pow_two, ← Complex.normSq_mul, ← pow_two, hw, hz, one_pow]
  have hnorm : Complex.normSq w = 1 :=
    (sq_eq_sq_iff_eq_or_eq_neg.mp hpow).resolve_right (by
      have h := Complex.normSq_nonneg w
      linarith)
  have hab : w.re ^ 2 + w.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using hnorm
  let x := rotationParam R w.re w.im hab
  refine ⟨x, ?_⟩
  have ha := (rotation_mul_entries x x).1
  have hb := (rotation_mul_entries x x).2
  have hRe : (w ^ 2).re = z.re := congrArg Complex.re hw
  have hIm : (w ^ 2).im = z.im := congrArg Complex.im hw
  have ea : (x * x).val 0 0 = g.val 0 0 := by
    rw [ha]
    simpa [x, rotationParam, rotation, rotationMatrix, z, pow_two, Complex.mul_re] using hRe
  have eb : (x * x).val 1 0 = g.val 1 0 := by
    rw [hb]
    simpa [x, rotationParam, rotation, rotationMatrix, z, pow_two, Complex.mul_im, add_comm] using hIm
  apply Subtype.ext
  apply Subtype.ext
  rw [(rotation_entries R (x * x)).1, (rotation_entries R g).1, ea, eb]

private theorem rotation_nonsplit : ¬ IsSplitTorus T.group := by
  rintro ⟨r, ⟨e⟩⟩
  let R := CommAlgCat.of ℝ ℝ
  let E := (centralizerPointsIso rotationTest).symm ≪≫
    (groupPointsFunctor ℝ).mapIso e ≪≫
    StandardGroups.multiplicativePowerGroupPointsIso ℝ (ULift (Fin r))
  let f : RotationPoints R →* (ULift (Fin r) → ℝˣ) := (E.hom.app R).hom
  have hf : Function.Bijective f := ConcreteCategory.bijective_of_isIso (E.hom.app R)
  cases r with
  | zero =>
      let x : RotationPoints R := rotationParam R 0 1 (by norm_num [R])
      have hx : f x = f 1 := Subsingleton.elim _ _
      have h := congrArg (fun y : RotationPoints R ↦ y.val 1 0) (hf.1 hx)
      change (1 : ℝ) = 0 at h
      exact one_ne_zero h
  | succ r =>
      let neg : ℝˣ := Units.mk0 (-1) (by norm_num)
      let y : ULift (Fin (r + 1)) → ℝˣ := fun _ ↦ neg
      obtain ⟨z, hz⟩ := hf.2 y
      obtain ⟨x, hx⟩ := rotation_square_surjective z
      change x * x = z at hx
      have hs : f x * f x = y := by rw [← map_mul, hx, hz]
      let j : ULift (Fin (r + 1)) := ⟨0⟩
      have h := congrArg (fun v : ULift (Fin (r + 1)) → ℝˣ ↦ (v j : ℝ)) hs
      change ((f x j : ℝˣ) : ℝ) * ((f x j : ℝˣ) : ℝ) = -1 at h
      nlinarith [mul_self_nonneg ((f x j : ℝˣ) : ℝ)]

private theorem matrixPoint_naturality {G : GroupScheme ℝ}
    (e : (groupPointsFunctor ℝ).obj G ≅ SL₂Points) (C : ClosedSubgroup G)
    {R S : TestAlgebra ℝ} (f : R ⟶ S) (p : Points C.group.X R) :
    matrixPoint e C S (mapPoints f p) =
      (SL₂Points.map f).hom (matrixPoint e C R p) := by
  let E := (groupPointsFunctor ℝ).obj C.group
  let t : E ⟶ SL₂Points := (groupPointsFunctor ℝ).map C.inclusion ≫ e.hom
  have h : E.map f ≫ t.app S = t.app R ≫ SL₂Points.map f := t.naturality f
  exact DFunLike.congr_fun (congrArg (fun x : E.obj R ⟶ SL₂Points.obj S ↦ x.hom) h)
    (show E.obj R from p)

private theorem complex_rotation_entries (R : TestAlgebra ℂ)
    (p : Points ((groupBaseChange ℝ ℂ).obj T.group).X R) :
    let M := complexMatrixPoint slPoints T R p
    M.val = rotationMatrix (M 0 0) (M 1 0) ∧ (M 0 0) ^ 2 + (M 1 0) ^ 2 = 1 := by
  dsimp only [complexMatrixPoint]
  rw [centralizer_matrixPoint]
  exact rotation_entries (restrictR R) _

private theorem eigenvectors {R : Type} [CommRing R] {i : R} (hi : i * i = -1) (a b : R) :
    rotationMatrix a b *ᵥ ![1, -i] = (a + i * b) • (![1, -i] : Fin 2 → R) ∧
    rotationMatrix a b *ᵥ ![1, i] = (a - i * b) • (![1, i] : Fin 2 → R) := by
  constructor <;> (funext j; fin_cases j <;>
    simp [rotationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul])
  · ring
  · linear_combination b * hi
  · ring
  · linear_combination b * hi

private abbrev ComplexRotation := (groupBaseChange ℝ ℂ).obj T.group

private def complexPlus : ComplexRotation ≅ RankOneTorus ℂ :=
  rotationSplit Complex.I Complex.I_mul_I

private def complexMinus : ComplexRotation ≅ RankOneTorus ℂ :=
  rotationSplit (-Complex.I) (by simp)

private theorem complexPlus_eval (R : TestAlgebra ℂ) (p : Points ComplexRotation.X R) :
    (characterValue (rankOnePointsIso ℂ) complexPlus.hom R p : R) =
      complexMatrixPoint slPoints T R p 0 0 +
        algebraMap ℂ R Complex.I * complexMatrixPoint slPoints T R p 1 0 :=
  rotationSplit_eval _ _ R p

private theorem complexMinus_eval (R : TestAlgebra ℂ) (p : Points ComplexRotation.X R) :
    (characterValue (rankOnePointsIso ℂ) complexMinus.hom R p : R) =
      complexMatrixPoint slPoints T R p 0 0 -
        algebraMap ℂ R Complex.I * complexMatrixPoint slPoints T R p 1 0 := by
  have h := rotationSplit_eval (-Complex.I) (by simp) R p
  change (characterValue (rankOnePointsIso ℂ) complexMinus.hom R p : R) =
      complexMatrixPoint slPoints T R p 0 0 +
        algebraMap ℂ R (-Complex.I) * complexMatrixPoint slPoints T R p 1 0 at h
  simpa only [map_neg, neg_mul, sub_eq_add_neg] using h

private theorem complexCharacters_product (R : TestAlgebra ℂ) (p : Points ComplexRotation.X R) :
    characterValue (rankOnePointsIso ℂ) complexPlus.hom R p *
      characterValue (rankOnePointsIso ℂ) complexMinus.hom R p = 1 := by
  let i := algebraMap ℂ R Complex.I
  have hi : i * i = -1 := by simp [i, ← map_mul, Complex.I_mul_I]
  apply Units.ext
  rw [Units.val_mul, complexPlus_eval, complexMinus_eval, eigenvalue_mul hi]
  exact (complex_rotation_entries R p).2

private theorem inverse_characters_distinct {V : GroupScheme ℂ}
    (u : (groupPointsFunctor ℂ).obj (RankOneTorus ℂ) ≅ Specs.StandardGroups.multiplicativePoints ℂ)
    (chi : V ≅ RankOneTorus ℂ) (psi : V ⟶ RankOneTorus ℂ)
    (h : ∀ p : Points V.X (CommAlgCat.of ℂ ℂ),
      characterValue u chi.hom (CommAlgCat.of ℂ ℂ) p *
        characterValue u psi (CommAlgCat.of ℂ ℂ) p = 1) : chi.hom ≠ psi := by
  intro he
  let S := CommAlgCat.of ℂ ℂ
  let e := (((groupPointsFunctor ℂ).mapIso chi) ≪≫ u).app S
  let z : ℂˣ := Units.mk0 2 (by norm_num)
  obtain ⟨p, hp⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2
    (show (Specs.StandardGroups.multiplicativePoints ℂ).obj S from z)
  have hp' : characterValue u chi.hom S p = z := hp
  have hprod := h p
  rw [← he, hp'] at hprod
  have hz : (2 : ℂ) * 2 = 1 := congrArg (fun x : ℂˣ ↦ x.val) hprod
  norm_num at hz

private theorem complexCharacters_distinct : complexPlus.hom ≠ complexMinus.hom :=
  inverse_characters_distinct (rankOnePointsIso ℂ) complexPlus complexMinus.hom
    (complexCharacters_product (CommAlgCat.of ℂ ℂ))

private theorem rotationCharacters : RotationCharacters slPoints T := by
  refine ⟨rankOnePointsIso ℂ, complexPlus, complexMinus.hom, complexCharacters_distinct, ?_, ?_⟩
  · intro R p
    let M := complexMatrixPoint slPoints T R p
    let i := algebraMap ℂ R Complex.I
    have hi : i * i = -1 := by simp [i, ← map_mul, Complex.I_mul_I]
    let zPlus := characterValue (rankOnePointsIso ℂ) complexPlus.hom R p
    let zMinus := characterValue (rankOnePointsIso ℂ) complexMinus.hom R p
    change (zPlus : R) = M 0 0 + i * M 1 0 ∧ (zMinus : R) = M 0 0 - i * M 1 0 ∧
      zPlus * zMinus = 1 ∧ M.val *ᵥ ![1, -i] = (zPlus : R) • ![1, -i] ∧
      M.val *ᵥ ![1, i] = (zMinus : R) • ![1, i]
    have hPlus : (zPlus : R) = M 0 0 + i * M 1 0 := complexPlus_eval R p
    have hMinus : (zMinus : R) = M 0 0 - i * M 1 0 := complexMinus_eval R p
    have hM : M.val = rotationMatrix (M 0 0) (M 1 0) := (complex_rotation_entries R p).1
    refine ⟨hPlus, hMinus, ?_, ?_, ?_⟩
    · exact complexCharacters_product R p
    · exact (congrArg (fun N : Matrix (Fin 2) (Fin 2) R ↦ N *ᵥ ![1, -i]) hM).trans
        ((eigenvectors hi (M 0 0) (M 1 0)).1.trans
          (congrArg (fun a : R ↦ a • (![1, -i] : Fin 2 → R)) hPlus.symm))
    · exact (congrArg (fun N : Matrix (Fin 2) (Fin 2) R ↦ N *ᵥ ![1, i]) hM).trans
        ((eigenvectors hi (M 0 0) (M 1 0)).2.trans
          (congrArg (fun a : R ↦ a • (![1, i] : Fin 2 → R)) hMinus.symm))
  · intro R S f hf p q h
    let M := complexMatrixPoint slPoints T R p
    let N := complexMatrixPoint slPoints T S q
    have hM : N = (SL₂Points.map f).hom M :=
      (congrArg (matrixPoint slPoints T (restrictR S)) h).trans
        (matrixPoint_naturality slPoints T f (baseChangePoint ℝ ℂ T.group.X R p))
    have ha : N 0 0 = f.hom (M 0 0) :=
      congrArg (fun g : MatrixSL S ↦ g 0 0) hM
    have hb : N 1 0 = f.hom (M 1 0) :=
      congrArg (fun g : MatrixSL S ↦ g 1 0) hM
    have hi : f.hom (algebraMap ℂ R Complex.I) = -(algebraMap ℂ S Complex.I) := by
      have hI : star Complex.I = -Complex.I := Complex.conj_I
      simpa only [hI, map_neg] using hf Complex.I
    change f.hom (characterValue (rankOnePointsIso ℂ) complexPlus.hom R p : R) =
        (characterValue (rankOnePointsIso ℂ) complexMinus.hom S q : S) ∧
      f.hom (characterValue (rankOnePointsIso ℂ) complexMinus.hom R p : R) =
        (characterValue (rankOnePointsIso ℂ) complexPlus.hom S q : S)
    constructor
    · rw [complexPlus_eval, complexMinus_eval]
      change f.hom (M 0 0 + algebraMap ℂ R Complex.I * M 1 0) =
        N 0 0 - algebraMap ℂ S Complex.I * N 1 0
      rw [map_add, map_mul, hi, ha, hb, neg_mul, sub_eq_add_neg]
    · rw [complexMinus_eval, complexPlus_eval]
      change f.hom (M 0 0 - algebraMap ℂ R Complex.I * M 1 0) =
        N 0 0 + algebraMap ℂ S Complex.I * N 1 0
      rw [map_sub, map_mul, hi, ha, hb, neg_mul, sub_neg_eq_add]

universe u

/-- The real diagonal and plane rotation tori, with their complex eigencharacters. -/
theorem realMaximalTori_conditional
    (_ : Specs.TorusCentralizer.MaximalTorusCentralizer.{u}) : RealMaximalTori := by
  refine ⟨SL, slPoints, D, T, ?_, ?_, ⟨diagonalRealSplit⟩, ?_, ?_, ?_, rotationCharacters,
    rotation_nonsplit, ?_⟩
  · intro R g
    exact (centralizer_range diagonalTest R g).trans (diagonal_iff R g)
  · intro R g
    exact (centralizer_range rotationTest R g).trans (rotation_iff R g)
  · exact ⟨ℂ, inferInstance, inferInstance, inferInstance, 1, ⟨complexPlus⟩⟩
  · let K := AlgebraicClosure ℝ
    exact ⟨(changedCentralizer K diagonalTest).isClosedImmersion,
      changedCentralizer_maximal K diagonalTest (split_isTorus ⟨1, ⟨diagonalSplit K⟩⟩)⟩
  · let K := AlgebraicClosure ℝ
    obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) (n := 2) (by decide)
    have hi' : i * i = -1 := by simpa only [pow_two] using hi
    exact ⟨(changedCentralizer K rotationTest).isClosedImmersion,
      changedCentralizer_maximal K rotationTest (split_isTorus ⟨1, ⟨rotationSplit i hi'⟩⟩)⟩
  · rintro ⟨_, e, _⟩
    exact rotation_nonsplit ⟨1, ⟨e.symm ≪≫ diagonalRealSplit⟩⟩

end

end LinearAlgebraicGroups.Reductive.RealTori

theorem _root_.«LinearAlgebraicGroups».«Reductive».«RealTori».«realMaximalTori» : _root_.«LinearAlgebraicGroups».«Specs».«RealTori».«RealMaximalTori» :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«RealTori».«realMaximalTori_conditional».{0} (@_root_.«LinearAlgebraicGroups».«Reductive».«TorusCentralizer».«maximalTorusCentralizer».{0})
