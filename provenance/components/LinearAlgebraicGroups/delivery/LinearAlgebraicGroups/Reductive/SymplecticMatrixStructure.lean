import Specs.LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure
import LinearAlgebraicGroups.Affine.StandardGroups
import LinearAlgebraicGroups.Affine.IdentityTangent
import LinearAlgebraicGroups.Unipotent.Criteria
import LinearAlgebraicGroups.Reductive.GeometricRadicals
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import MathGenome.Internal.AlgebraCore.P103.Ch06.AffineDimension
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import LinearAlgebraicGroups.Affine.SmoothnessCriteria

open AlgebraicGeometry CategoryTheory Matrix Opposite
open scoped Matrix

set_option maxHeartbeats 1000000

universe u

namespace LinearAlgebraicGroups.SymplecticMatrixStructure

open LinearAlgebraicGroups.Specs Specs.SymplecticMatrixStructure Specs.StandardGroups
noncomputable section

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {k : Type u} [Field k]

open private Representation Representation.mk
  Representation.hopf
  Representation.operations
  Representation.compatible
  Representation.represents
  Representation.convolutionIso
  generalLinearRepresentation
  glEvaluation
  glEvaluation_entry
  glCoordinates_ext
  spectrumPointsIso
  from LinearAlgebraicGroups.Affine.StandardGroups

theorem pointEquation : PointEquation.{u} := by
  intro ι R _ _ _ g
  refine ⟨SymplecticGroup.mem_iff', SymplecticGroup.mem_iff'.trans ?_⟩
  have hcomp := Matrix.toLinearMap₂'_comp (Matrix.J ι R) g g
  constructor
  · intro hg x y
    rw [hg] at hcomp
    exact congrArg (fun f : LinearMap.BilinForm R (Indices ι → R) => f x y) hcomp
  · intro hg
    let e : Matrix (Indices ι) (Indices ι) R ≃ₗ[R] LinearMap.BilinForm R (Indices ι → R) :=
      Matrix.toLinearMap₂' R
    apply e.injective
    have he :
        (alternatingForm ι R).compl₁₂ (Matrix.toLin' g) (Matrix.toLin' g) = alternatingForm ι R :=
      DFunLike.ext _ _ fun x => DFunLike.ext _ _ fun y => hg x y
    exact hcomp.symm.trans he

theorem perfectAlternatingForm : PerfectAlternatingForm.{u} := by
  intro ι R _ _ _
  constructor
  · intro x
    change Matrix.toLinearMap₂' R (Matrix.J ι R) x x = 0
    rw [Matrix.toLinearMap₂'_apply']
    simp [Matrix.J, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.neg_mulVec, mul_comm, Finset.sum_neg_distrib]
  · refine ⟨Matrix.Nondegenerate.toLinearMap₂' ?_, Matrix.isUnit_det_J ι R⟩
    exact Matrix.Nondegenerate.of_det_mem_nonZeroDivisors
      (Matrix.isUnit_det_J ι R).mem_nonZeroDivisors

private theorem map_matrixEquation {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Matrix (Indices ι) (Indices ι) R) :
    (matrixEquation M).map f = matrixEquation (M.map f) := by
  simp [matrixEquation, Matrix.map_sub, Matrix.map_mul, Matrix.transpose_map]

def toGeneralLinear {R : Type u} [CommRing R] :
    PointGroup ι R →* Matrix.GeneralLinearGroup (Indices ι) R where
  toFun g := Matrix.GeneralLinearGroup.mk'' g.val (SymplecticGroup.symplectic_det g.property)
  map_one' := Matrix.GeneralLinearGroup.ext fun _ _ => rfl
  map_mul' _ _ := Matrix.GeneralLinearGroup.ext fun _ _ => rfl

local notation "glUniversal" => universalMatrix k (Indices ι)
local notation "quotient" => Ideal.Quotient.mkₐ k (symplecticIdeal k ι)

theorem universalSymplecticMatrix_mem :
    universalSymplecticMatrix k ι ∈ Matrix.symplecticGroup ι (Coordinates k ι) := by
  apply SymplecticGroup.mem_iff'.mpr
  apply sub_eq_zero.mp
  change matrixEquation ((quotient).mapMatrix glUniversal) = 0
  rw [← show (matrixEquation glUniversal).map (quotient).toRingHom = matrixEquation ((quotient).mapMatrix glUniversal)
    from map_matrixEquation (quotient).toRingHom glUniversal]
  ext i j
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(i, j), rfl⟩)

private def evaluatePoint {R : Type u} [CommRing R] [Algebra k R]
    (f : Coordinates k ι →ₐ[k] R) : PointGroup ι R :=
  ⟨f.mapMatrix (universalSymplecticMatrix k ι),
    SymplecticGroup.map_mem universalSymplecticMatrix_mem f⟩

private def evaluateCoordinates {R : Type u} [CommRing R] [Algebra k R]
    (g : PointGroup ι R) : Coordinates k ι →ₐ[k] R := by
  let f : GLCoordinates k (Indices ι) →ₐ[k] R := glEvaluation (toGeneralLinear g)
  refine Ideal.Quotient.liftₐ (symplecticIdeal k ι) f ?_
  have h : f.mapMatrix glUniversal = g.val := Matrix.ext fun i j => glEvaluation_entry (toGeneralLinear g) i j
  have hzero : (matrixEquation glUniversal).map f.toRingHom = 0 := by
    rw [map_matrixEquation, show (glUniversal).map f.toRingHom = f.mapMatrix glUniversal from rfl, h]
    exact sub_eq_zero.mpr (SymplecticGroup.mem_iff'.mp g.property)
  have hle : symplecticIdeal k ι ≤ RingHom.ker f.toRingHom := by
    intro a ha
    refine (Ideal.span_le.mpr ?_) ha
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact congrFun (congrFun hzero i) j
  exact fun a ha => hle ha

private theorem evaluateCoordinates_entry {R : Type u} [CommRing R] [Algebra k R]
    (g : PointGroup ι R) (i j : Indices ι) :
    evaluateCoordinates g (universalSymplecticMatrix k ι i j) = g.val i j :=
  glEvaluation_entry (toGeneralLinear g) i j

private def symplecticRepresentation :
    Representation (Coordinates k ι) (symplecticPoints k ι) :=
  Representation.mk (fun R =>
    { toFun := evaluatePoint
      invFun := evaluateCoordinates
      left_inv := fun f => by
        apply Ideal.Quotient.algHom_ext k
        exact glCoordinates_ext fun i j => evaluateCoordinates_entry (evaluatePoint f) i j
      right_inv := fun g => Subtype.ext (Matrix.ext (evaluateCoordinates_entry g)) })
    (fun _ _ => Subtype.ext (Matrix.ext fun _ _ => rfl))

/-- The coordinate Hopf algebra of the fixed symplectic subscheme of GL. -/
@[instance_reducible]
def symplecticHopf (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :
    HopfAlgebra k (Coordinates k ι) :=
  (Representation.hopf (symplecticRepresentation (k := k) (ι := ι)))

/-- The split symplectic affine algebraic group on the hyperbolic space indexed by ι. -/
def symplecticGroup (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :
    AffineAlgebraicGroup k :=
  letI := symplecticHopf k ι
  spectrum k (Coordinates k ι)

def symplecticGroupPointsIso (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :
    (groupPointsFunctor k).obj (symplecticGroup k ι).val ≅ symplecticPoints k ι :=
  letI := symplecticHopf k ι
  spectrumPointsIso (Representation.convolutionIso (symplecticRepresentation (k := k) (ι := ι)))

local instance : HopfAlgebra k (GLCoordinates k (Indices ι)) :=
  StandardGroups.generalLinearHopf k (Indices ι)

local instance : HopfAlgebra k (Coordinates k ι) := symplecticHopf k ι

private theorem quotient_operations :
    (Algebra.TensorProduct.map quotient quotient).comp
        (Representation.operations (generalLinearRepresentation (k := k) (ι := Indices ι))).delta =
      (Representation.operations (symplecticRepresentation (k := k) (ι := ι))).delta.comp quotient ∧
    (Representation.operations (generalLinearRepresentation (k := k) (ι := Indices ι))).epsilon =
      (Representation.operations (symplecticRepresentation (k := k) (ι := ι))).epsilon.comp quotient ∧
    (quotient).comp (Representation.operations (generalLinearRepresentation (k := k) (ι := Indices ι))).inverse =
      (Representation.operations (symplecticRepresentation (k := k) (ι := ι))).inverse.comp quotient :=
  (Representation.compatible (generalLinearRepresentation (k := k) (ι := Indices ι)))
    (symplecticRepresentation (k := k) (ι := ι)) quotient (fun _ => toGeneralLinear)
    (fun _ _ => Matrix.GeneralLinearGroup.ext fun _ _ => rfl)

def quotientHom : CommHopfAlgCat.of k (GLCoordinates k (Indices ι)) ⟶
    CommHopfAlgCat.of k (Coordinates k ι) :=
  CommHopfAlgCat.ofHom (BialgHom.ofAlgHom quotient quotient_operations.2.1.symm quotient_operations.1)

/-- The inclusion is the closed immersion induced by the quotient of the A03 coordinates. -/
def symplecticClosedSubgroup (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :
    ClosedSubgroup (StandardGroups.generalLinearGroup k (Indices ι)).val :=
  ⟨(symplecticGroup k ι).val, specGroupMap quotientHom,
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mkₐ k (symplecticIdeal k ι)).toRingHom)
      Ideal.Quotient.mk_surjective⟩

theorem matrixPresentation : MatrixPresentation.{u} := by
  intro k ι _ _ _
  exact ⟨(Representation.operations (generalLinearRepresentation (k := k) (ι := Indices ι))),
    (Representation.operations (symplecticRepresentation (k := k) (ι := ι))),
    (Representation.represents (generalLinearRepresentation (k := k) (ι := Indices ι))) _ (fun _ _ => rfl),
    (Representation.represents (symplecticRepresentation (k := k) (ι := ι))) _ (fun _ _ => rfl),
    quotient_operations.1, quotient_operations.2.1, quotient_operations.2.2,
    (symplecticClosedSubgroup k ι).inclusion, rfl,
    (symplecticClosedSubgroup k ι).isClosedImmersion⟩

section Tangent

open private dualKernelIso mapDualKernel_scale from LinearAlgebraicGroups.Affine.IdentityTangent

local notation "Mat" => Matrix (Indices ι) (Indices ι) k
local notation "Jk" => Matrix.J ι k

private def dualMatrix (A B : Mat) : Matrix (Indices ι) (Indices ι) (DualNumber k) :=
  fun i j => (⟨A i j, B i j⟩ : DualNumber k)

omit [Fintype ι] [DecidableEq ι] [Field k] in
private theorem dualMatrix_injective {A B C D : Mat} (h : dualMatrix A B = dualMatrix C D) :
    A = C ∧ B = D := by
  exact ⟨Matrix.ext fun i j => congrArg (fun m => (m i j).fst) h,
    Matrix.ext fun i j => congrArg (fun m => (m i j).snd) h⟩

omit [DecidableEq ι] in
private theorem dualMatrix_mul (A B C D : Mat) :
    dualMatrix A B * dualMatrix C D = dualMatrix (A * C) (A * D + B * C) := by
  apply Matrix.ext
  intro i j
  apply TrivSqZeroExt.ext
  · simp only [Matrix.mul_apply, TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul]
    rfl
  · simp only [Matrix.mul_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul,
      smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    exact Finset.sum_add_distrib

omit [Fintype ι] [DecidableEq ι] [Field k] in
private theorem dualMatrix_transpose (A B : Mat) :
    (dualMatrix A B)ᵀ = dualMatrix Aᵀ Bᵀ := rfl

omit [Fintype ι] in
private theorem dualMatrix_J : dualMatrix Jk 0 = Matrix.J ι (DualNumber k) := by
  have hm := Matrix.map_J ι (TrivSqZeroExt.inlHom k k)
  exact hm

private theorem lieEquation (X : Mat) :
    Xᵀ * Jk + Jk * X = 0 ↔ (Jk * X).IsSymm := by
  rw [Matrix.IsSymm, Matrix.transpose_mul, Matrix.J_transpose, Matrix.mul_neg,
    add_eq_zero_iff_neg_eq]

private theorem tangentMatrix_mem (X : Mat) :
    dualMatrix 1 X ∈ Matrix.symplecticGroup ι (DualNumber k) ↔ (Jk * X).IsSymm := by
  rw [SymplecticGroup.mem_iff', ← dualMatrix_J, dualMatrix_transpose, dualMatrix_mul,
    dualMatrix_mul]
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_zero, zero_add, Matrix.mul_one]
  rw [← lieEquation, add_comm (Xᵀ * Jk)]
  exact ⟨fun h => (dualMatrix_injective h).2, fun h => congrArg (dualMatrix Jk) h⟩

private def tangentCoefficients (p : DualKernel (symplecticPoints k ι)) : Mat :=
  fun i j => (p.toMul.val.val i j).snd

private theorem tangentFst (p : DualKernel (symplecticPoints k ι)) :
    (fun i j => (p.toMul.val.val i j).fst) = (1 : Mat) :=
  congrArg Subtype.val p.toMul.property

private theorem tangentMatrix_eq (p : DualKernel (symplecticPoints k ι)) :
    dualMatrix 1 (tangentCoefficients p) = p.toMul.val.val := by
  apply Matrix.ext
  intro i j
  exact TrivSqZeroExt.ext (congrFun (congrFun (tangentFst p).symm i) j) rfl

private def tangentFromCoefficients (X : symplecticLieSubspace k ι) :
    DualKernel (symplecticPoints k ι) :=
  ⟨⟨dualMatrix 1 X.val, (tangentMatrix_mem X.val).2 X.property⟩, by
    apply Subtype.ext
    rfl⟩

private def tangentMatrixIso : DualKernel (symplecticPoints k ι) ≃+ symplecticLieSubspace k ι where
  toFun p := ⟨tangentCoefficients p, (tangentMatrix_mem _).mp
    ((tangentMatrix_eq p).symm ▸ p.toMul.val.property)⟩
  invFun := tangentFromCoefficients
  left_inv p := Subtype.ext (Subtype.ext (tangentMatrix_eq p))
  right_inv _ := Subtype.ext rfl
  map_add' p q := by
    apply Subtype.ext
    change tangentCoefficients (p + q) = tangentCoefficients p + tangentCoefficients q
    ext i j
    change ((p.toMul.val.val * q.toMul.val.val) i j).snd = _
    rw [← tangentMatrix_eq p, ← tangentMatrix_eq q, dualMatrix_mul]
    simp [dualMatrix, add_comm]

theorem lieComparison : LieComparison.{u} := by
  intro k ι _ _ _ G c
  refine ⟨(dualKernelIso c).trans tangentMatrixIso, fun _ _ _ => rfl, ?_⟩
  intro s p
  change tangentMatrixIso (mapDualKernel c.hom (scalePointKernel G s p)) = _
  rw [mapDualKernel_scale]
  apply Subtype.ext
  ext i j
  change (dualNumberScale s _).snd = s • _
  rw [dualNumberScale, TrivSqZeroExt.snd_map]
  rfl

end Tangent

section Smoothness

variable {R : Type u} [CommRing R]

private theorem equation_transpose (A : Matrix (Indices ι) (Indices ι) R) :
    (matrixEquation A)ᵀ = -matrixEquation A := by
  simp [matrixEquation, Matrix.transpose_mul, Matrix.J_transpose,
    Matrix.mul_assoc, sub_eq_add_neg, add_comm]

private theorem matrixForm_single (M : Matrix (Indices ι) (Indices ι) R) (i j : Indices ι) :
    Matrix.toLinearMap₂' R M (Pi.single i (1 : R)) (Pi.single j (1 : R)) = M i j := by
  rw [Matrix.toLinearMap₂'_apply', Matrix.mulVec_single_one, single_one_dotProduct,
    Matrix.col_apply]

private theorem equation_diag (A : Matrix (Indices ι) (Indices ι) R) (i : Indices ι) :
    matrixEquation A i i = 0 := by
  let e : Indices ι → R := Pi.single i 1
  have h := Matrix.toLinearMap₂'_comp (Matrix.J ι R) A A
  have h' := congrArg (fun f : LinearMap.BilinForm R (Indices ι → R) => f e e) h
  have ha := (perfectAlternatingForm ι R).1
  change alternatingForm ι R (A *ᵥ e) (A *ᵥ e) =
    Matrix.toLinearMap₂' R (Aᵀ * Matrix.J ι R * A) e e at h'
  have hA : (Aᵀ * Matrix.J ι R * A) i i = 0 := by
    rw [ha (A *ᵥ e)] at h'
    exact (matrixForm_single (Aᵀ * Matrix.J ι R * A) i i).symm.trans h'.symm
  have hJ : Matrix.J ι R i i = 0 := by
    have he := ha e
    change Matrix.toLinearMap₂' R (Matrix.J ι R) e e = 0 at he
    exact (matrixForm_single (Matrix.J ι R) i i).symm.trans he
  change (Aᵀ * Matrix.J ι R * A) i i - Matrix.J ι R i i = 0
  rw [hA, hJ, sub_zero]

omit [DecidableEq ι] in
private theorem matrix_mul_eq_zero_of_square_zero {I : Ideal R} (hI : I ^ 2 = ⊥)
    {A B : Matrix (Indices ι) (Indices ι) R}
    (hA : A.map (Ideal.Quotient.mk I) = 0) (hB : B.map (Ideal.Quotient.mk I) = 0) :
    A * B = 0 := by
  rw [pow_two] at hI
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro l _
  have ha : A i l ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (congrFun (congrFun hA i) l)
  have hb : B l j ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (congrFun (congrFun hB l) j)
  have hm := Ideal.mul_mem_mul ha hb
  rwa [hI, Ideal.mem_bot] at hm

private theorem symplectic_lift (I : Ideal R) (hI : I ^ 2 = ⊥) (g : PointGroup ι (R ⧸ I)) :
    ∃ h : PointGroup ι R, mapSymplecticPoint (Ideal.Quotient.mk I) h = g := by
  let π := Ideal.Quotient.mk I
  choose lift hlift using (Ideal.Quotient.mk_surjective (I := I))
  let A : Matrix (Indices ι) (Indices ι) R := g.val.map lift
  have hA : A.map π = g.val := Matrix.ext fun i j => hlift (g.val i j)
  let E := matrixEquation A
  have hE : E.map π = 0 := by
    rw [map_matrixEquation, hA]
    exact sub_eq_zero.mpr (SymplecticGroup.mem_iff'.mp g.property)
  let e := Fintype.equivFin (Indices ι)
  let P : Matrix (Indices ι) (Indices ι) R :=
    fun i j => if e i < e j then -E i j else 0
  have hP : P.map π = 0 := by
    apply Matrix.ext
    intro i j
    have h := congrFun (congrFun hE i) j
    change π (E i j) = 0 at h
    change π (P i j) = 0
    by_cases hij : e i < e j <;> simp [P, hij, h]
  have hEP : E + P - Pᵀ = 0 := by
    apply Matrix.ext
    intro i j
    have hji : E j i = -E i j := congrFun (congrFun (equation_transpose A) i) j
    change E i j + P i j - P j i = 0
    rcases lt_trichotomy (e i) (e j) with hij | hij | hji'
    · simp [P, hij, not_lt_of_gt hij]
    · have hij := e.injective hij
      subst j
      simp [P, E, equation_diag]
    · simp [P, hji', not_lt_of_gt hji', hji]
  let J := Matrix.J ι R
  let Y := (-J) * P
  have hY : Y.map π = 0 := by rw [show Y = (-J) * P from rfl, Matrix.map_mul, hP, Matrix.mul_zero]
  have hYt : Yᵀ.map π = 0 := by rw [Matrix.transpose_map, hY, Matrix.transpose_zero]
  have hJY : J * Y = P := by
    change J * ((-J) * P) = P
    rw [← Matrix.mul_assoc, Matrix.mul_neg, Matrix.J_squared, neg_neg, Matrix.one_mul]
  have hYJ : Yᵀ * J = -Pᵀ := by
    have h := congrArg Matrix.transpose hJY
    simp only [Matrix.transpose_mul, J, Matrix.J_transpose, Matrix.mul_neg] at h
    exact neg_eq_iff_eq_neg.mp h
  have hEY : E * Y = 0 := matrix_mul_eq_zero_of_square_zero hI hE hY
  have hYE : Yᵀ * E = 0 := matrix_mul_eq_zero_of_square_zero hI hYt hE
  have hYP : Yᵀ * P = 0 := matrix_mul_eq_zero_of_square_zero hI hYt hP
  have hJE : Aᵀ * J * A = J + E := by
    change _ = J + (_ - J)
    abel
  have hfix : (A * (1 + Y))ᵀ * J * (A * (1 + Y)) = J := by
    have hrewrite :
        (A * (1 + Y))ᵀ * J * (A * (1 + Y)) = (1 + Y)ᵀ * (Aᵀ * J * A) * (1 + Y) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hrewrite, hJE]
    have hleft : (1 + Y)ᵀ * (J + E) = J + E - Pᵀ := by
      simp [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, hYE, hYJ, sub_eq_add_neg]
      abel
    have hright : (1 + Y)ᵀ * (J + E) * (1 + Y) = J + (E + P - Pᵀ) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc _ (J + E) Y,
        Matrix.add_mul J E Y, hJY, hEY, add_zero, hleft, Matrix.transpose_add,
        Matrix.transpose_one, Matrix.add_mul, Matrix.one_mul, hYP, add_zero]
      abel
    simpa [hEP, Matrix.mul_assoc] using hright
  refine ⟨⟨A * (1 + Y), SymplecticGroup.mem_iff'.mpr hfix⟩, Subtype.ext ?_⟩
  change (A * (1 + Y)).map π = g.val
  simp [hA, hY, Matrix.map_add, Matrix.map_one π (map_zero π) (map_one π)]

theorem smoothness : Specs.SymplecticMatrixStructure.Smoothness.{u} := by
  intro k ι _ _ _
  have hSmooth : Algebra.Smooth k (Coordinates k ι) := by
    refine ⟨?_, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
    rw [Algebra.FormallySmooth.iff_comp_surjective]
    intro R _ _ I hI f
    obtain ⟨g, hg⟩ := symplectic_lift I hI (evaluatePoint f)
    refine ⟨evaluateCoordinates g, ?_⟩
    apply Ideal.Quotient.algHom_ext k
    apply glCoordinates_ext
    intro i j
    change (Ideal.Quotient.mk I) (evaluateCoordinates g (universalSymplecticMatrix k ι i j)) =
      f (universalSymplecticMatrix k ι i j)
    rw [evaluateCoordinates_entry]
    exact congrFun (congrFun (congrArg Subtype.val hg) i) j
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (Coordinates k ι))))
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr hSmooth)

end Smoothness

section Diagonal

variable {R : Type u} [CommRing R]

omit [Fintype ι] in
private theorem diagonal_blocks (a b : ι → R) :
    Matrix.diagonal (Sum.elim a b) = Matrix.fromBlocks (Matrix.diagonal a) 0 0 (Matrix.diagonal b) := by
  apply Matrix.ext
  rintro (i | i) (j | j) <;> simp [Matrix.diagonal_apply]

theorem hyperbolicDiagonal_mem (t : ι → Rˣ) :
    hyperbolicDiagonal t ∈ Matrix.symplecticGroup ι R := by
  rw [hyperbolicDiagonal, diagonal_blocks, SymplecticGroup.fromBlocks_mem_iff]
  simp [Matrix.diagonal_mul_diagonal, ← Units.val_mul, Matrix.diagonal_one]

def diagonalPoint (ι R : Type u) [Fintype ι] [DecidableEq ι] [CommRing R] :
    (ι → Rˣ) →* PointGroup ι R where
  toFun t := ⟨hyperbolicDiagonal t, hyperbolicDiagonal_mem t⟩
  map_one' := by
    apply Subtype.ext
    change hyperbolicDiagonal (1 : ι → Rˣ) = 1
    rw [hyperbolicDiagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    cases i <;> simp
  map_mul' t s := by
    apply Subtype.ext
    change hyperbolicDiagonal (t * s) = hyperbolicDiagonal t * hyperbolicDiagonal s
    simp only [hyperbolicDiagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    cases i <;> simp [mul_comm]

private def diagonalCharacter : Indices ι → (ι → ℤ) :=
  Sum.elim (fun i => Pi.single i 1) (fun i => Pi.single i (-1))

omit [Fintype ι] in
private theorem diagonalCharacter_injective :
    Function.Injective (diagonalCharacter (ι := ι)) := by
  rintro (i | i) (j | j) h
  · by_cases hij : i = j
    · exact congrArg Sum.inl hij
    · have he := congrFun h i
      simp [diagonalCharacter, hij] at he
  · have he := congrFun h i
    by_cases hij : i = j <;> simp [diagonalCharacter, hij] at he
  · have he := congrFun h i
    by_cases hij : i = j <;> simp [diagonalCharacter, hij] at he
  · by_cases hij : i = j
    · exact congrArg Sum.inr hij
    · have he := congrFun h i
      simp [diagonalCharacter, hij] at he

private abbrev LaurentUnits (R ι : Type u) [CommRing R] :=
  (AddMonoidAlgebra.of R (ι → ℤ)).toHomUnits

omit [Fintype ι] in
private theorem universalDiagonal_apply (j : Indices ι) :
    hyperbolicDiagonal (fun i : ι => LaurentUnits R ι (Multiplicative.ofAdd (Pi.single i 1))) j j =
      AddMonoidAlgebra.single (diagonalCharacter j) (1 : R) := by
  cases j with
  | inl i => simp [hyperbolicDiagonal, diagonalCharacter, LaurentUnits, MonoidHom.toHomUnits]
  | inr i =>
    rw [hyperbolicDiagonal, Matrix.diagonal_apply_eq, Sum.elim_inr, ← map_inv]
    change AddMonoidAlgebra.single (-((Pi.single i 1 : ι → ℤ))) 1 = _
    congr 1
    funext j
    by_cases hij : i = j <;> simp [diagonalCharacter, hij]

private theorem offDiagonal_eq_zero_of_centralizes {g : Matrix (Indices ι) (Indices ι) R}
    (h : CentralizesDiagonal g) {i j : Indices ι} (hij : i ≠ j) : g i j = 0 := by
  let t (l : ι) := LaurentUnits R ι (Multiplicative.ofAdd (Pi.single l 1))
  let f := algebraMap R (AddMonoidAlgebra R (ι → ℤ))
  have hc := congrFun (congrFun (h _ f t).eq i) j
  unfold hyperbolicDiagonal at hc
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
  have hc' : f (g i j) * hyperbolicDiagonal t j j = hyperbolicDiagonal t i i * f (g i j) := by
    simpa [hyperbolicDiagonal] using hc
  rw [universalDiagonal_apply, universalDiagonal_apply] at hc'
  change AddMonoidAlgebra.single 0 (g i j) * AddMonoidAlgebra.single (diagonalCharacter j) 1 =
    AddMonoidAlgebra.single (diagonalCharacter i) 1 * AddMonoidAlgebra.single 0 (g i j) at hc'
  simp only [AddMonoidAlgebra.single_mul_single, zero_add, add_zero, mul_one, one_mul] at hc'
  have he := congrArg (fun x : AddMonoidAlgebra R (ι → ℤ) => x.coeff (diagonalCharacter j)) hc'
  simpa [AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
    diagonalCharacter_injective.ne hij] using he

theorem diagonalCentralizer : DiagonalCentralizer.{u} := by
  intro ι R _ _ _ g
  constructor
  · intro h
    let d (i : Indices ι) := g.val i i
    have hg : g.val = Matrix.diagonal d := by
      apply Matrix.ext
      intro i j
      by_cases hij : i = j
      · subst j
        simp [d]
      · rw [Matrix.diagonal_apply_ne _ hij]
        exact offDiagonal_eq_zero_of_centralizes h hij
    have hd : ∀ i : ι, d (Sum.inl i) * d (Sum.inr i) = 1 := by
      intro i
      have hsp := SymplecticGroup.mem_iff'.mp g.property
      rw [hg, Matrix.diagonal_transpose] at hsp
      have he := congrFun (congrFun hsp (Sum.inr i)) (Sum.inl i)
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
      simpa [Matrix.J, mul_comm] using he
    let t (i : ι) : Rˣ :=
      ⟨d (Sum.inl i), d (Sum.inr i), hd i, (mul_comm _ _).trans (hd i)⟩
    refine ⟨t, hg.trans ?_⟩
    unfold hyperbolicDiagonal
    congr 1
    funext i
    cases i <;> rfl
  · rintro ⟨t, ht⟩ S _ f s
    rw [ht]
    exact show (hyperbolicDiagonal t).map f * hyperbolicDiagonal s =
        hyperbolicDiagonal s * (hyperbolicDiagonal t).map f by
      simp [hyperbolicDiagonal, Matrix.diagonal_map, Matrix.diagonal_mul_diagonal, mul_comm]

end Diagonal

section NaturalAction

local notation "B" => alternatingForm ι k

private def transvection (v : Indices ι → k) (a : k) :
    (Indices ι → k) →ₗ[k] (Indices ι → k) :=
  LinearMap.id + ((a • (B v)).smulRight v)

private theorem transvection_apply (v : Indices ι → k) (a : k) (x : Indices ι → k) :
    transvection v a x = x + (a * B v x) • v := rfl

private theorem transvection_preserves (v : Indices ι → k) (a : k) (x y : Indices ι → k) :
    B (transvection v a x) (transvection v a y) = B x y := by
  have ha := (perfectAlternatingForm ι k).1
  have hn := (LinearMap.IsAlt.neg ha v x).symm
  simp only [transvection_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, ha v, hn]
  ring

private theorem move_of_pair_ne_zero {x y : Indices ι → k} (h : B x y ≠ 0) :
    ∃ g : PointGroup ι k, g.val *ᵥ x = y := by
  let v := y - x
  have ha := (perfectAlternatingForm ι k).1
  have hvx : B v x = -B x y := by
    simp [v, ha x, ← LinearMap.IsAlt.neg ha x y]
  let a := (B v x)⁻¹
  have hvx' : B v x ≠ 0 := by rw [hvx]; exact neg_ne_zero.mpr h
  let M := LinearMap.toMatrix' (transvection v a)
  have hm (z : Indices ι → k) : M *ᵥ z = transvection v a z := by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  refine ⟨⟨M, ((pointEquation ι k M).2).mpr ?_⟩, ?_⟩
  · intro u w
    rw [hm, hm, transvection_preserves]
  · rw [hm, transvection_apply, inv_mul_cancel₀ hvx', one_smul]
    exact add_sub_cancel _ _

theorem transitiveNaturalAction : TransitiveNaturalAction.{u} := by
  intro k ι _ _ _ x y hx hy
  let form := alternatingForm ι k
  by_cases hxy : form x y = 0
  · have hp := perfectAlternatingForm ι k
    have hl : ∀ z : Indices ι → k, z ≠ 0 → ∃ w, form z w ≠ 0 := by
      intro z hz
      exact not_forall.mp fun h => hz (hp.2.1.1 z h)
    obtain ⟨z, hxz⟩ := hl x hx
    obtain ⟨w, hyw⟩ := hl y hy
    have hboth : ∃ z, form x z ≠ 0 ∧ form y z ≠ 0 := by
      by_cases hyz : form y z = 0
      · by_cases hxw : form x w = 0
        · exact ⟨z + w, by simpa [map_add, hxw] using hxz, by simpa [map_add, hyz] using hyw⟩
        · exact ⟨w, hxw, hyw⟩
      · exact ⟨z, hxz, hyz⟩
    obtain ⟨t, hxt, hyt⟩ := hboth
    obtain ⟨g, hg⟩ := move_of_pair_ne_zero hxt
    have hty : form t y ≠ 0 :=
      (LinearMap.IsAlt.neg hp.1 y t) ▸ neg_ne_zero.mpr hyt
    obtain ⟨h, hh⟩ := move_of_pair_ne_zero hty
    refine ⟨h * g, ?_⟩
    change (h.val * g.val) *ᵥ x = y
    rw [← Matrix.mulVec_mulVec, hg, hh]
  · exact move_of_pair_ne_zero hxy

end NaturalAction

section Cell

variable {R : Type u} [CommRing R]

/-- The symmetric upper shear in the hyperbolic decomposition. -/
def upperShear (T : Matrix ι ι R) (hT : T.IsSymm) : PointGroup ι R :=
  ⟨Matrix.fromBlocks 1 T 0 1, by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    simp [hT.eq]⟩

/-- The symmetric lower shear in the hyperbolic decomposition. -/
def lowerShear (S : Matrix ι ι R) (hS : S.IsSymm) : PointGroup ι R :=
  ⟨Matrix.fromBlocks 1 0 S 1, by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    simp [hS.eq]⟩

/-- The block-diagonal embedding of the Levi GL. -/
def leviBlock (A : Matrix ι ι R) (hA : IsUnit A.det) : PointGroup ι R :=
  ⟨Matrix.fromBlocks A 0 0 A⁻¹ᵀ, by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.transpose_zero, sub_zero, true_and]
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hA, Matrix.transpose_one]⟩

private theorem bigCellDecomposition (g : PointGroup ι R) (hA : IsUnit g.val.toBlocks₁₁.det) :
    ∃ (hS : (g.val.toBlocks₂₁ * g.val.toBlocks₁₁⁻¹).IsSymm)
      (hT : (g.val.toBlocks₁₁⁻¹ * g.val.toBlocks₁₂).IsSymm),
      g = lowerShear _ hS * leviBlock g.val.toBlocks₁₁ hA * upperShear _ hT := by
  let A := g.val.toBlocks₁₁
  let B := g.val.toBlocks₁₂
  let C := g.val.toBlocks₂₁
  let D := g.val.toBlocks₂₂
  have hblock : Matrix.fromBlocks A B C D = g.val := Matrix.fromBlocks_toBlocks _
  have h := SymplecticGroup.fromBlocks_mem_iff.mp (hblock.symm ▸ g.property)
  have ht := SymplecticGroup.transpose_mem g.property
  rw [← hblock, Matrix.fromBlocks_transpose] at ht
  have h' := (SymplecticGroup.fromBlocks_mem_iff.mp ht).1
  simp only [Matrix.transpose_transpose] at h'
  have hright : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ hA
  have hleft : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hA
  have hrightT : A⁻¹ᵀ * Aᵀ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hright
  have hleftT : Aᵀ * A⁻¹ᵀ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hleft
  have hS : (C * A⁻¹).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_mul]
    calc
      A⁻¹ᵀ * Cᵀ = A⁻¹ᵀ * (Cᵀ * A) * A⁻¹ := by
        rw [Matrix.mul_assoc _ (Cᵀ * A) A⁻¹, Matrix.mul_assoc Cᵀ A A⁻¹, hright, Matrix.mul_one]
      _ = C * A⁻¹ := by
        rw [← h.1, ← Matrix.mul_assoc A⁻¹ᵀ Aᵀ C, hrightT, Matrix.one_mul]
  have hT : (A⁻¹ * B).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_mul]
    calc
      Bᵀ * A⁻¹ᵀ = A⁻¹ * (A * Bᵀ) * A⁻¹ᵀ := by
        rw [← Matrix.mul_assoc _ A Bᵀ, hleft, Matrix.one_mul]
      _ = A⁻¹ * B := by
        rw [h', Matrix.mul_assoc, Matrix.mul_assoc B Aᵀ A⁻¹ᵀ, hleftT, Matrix.mul_one]
  have hd : D = (C * A⁻¹) * B + A⁻¹ᵀ := by
    have hb : Aᵀ * D = 1 + Cᵀ * B := eq_add_of_sub_eq h.2.2
    calc
      D = A⁻¹ᵀ * (Aᵀ * D) := by rw [← Matrix.mul_assoc, hrightT, Matrix.one_mul]
      _ = (C * A⁻¹) * B + A⁻¹ᵀ := by
        rw [hb, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc,
          ← Matrix.transpose_mul, hS.eq, add_comm]
  refine ⟨hS, hT, Subtype.ext ?_⟩
  change g.val = Matrix.fromBlocks 1 0 (C * A⁻¹) 1 * Matrix.fromBlocks A 0 0 A⁻¹ᵀ *
    Matrix.fromBlocks 1 (A⁻¹ * B) 0 1
  rw [← hblock, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.mul_assoc C A⁻¹ A, hleft, Matrix.mul_one]
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero]
  rw [← Matrix.mul_assoc A A⁻¹ B, hright, Matrix.one_mul, hd, Matrix.mul_assoc C A⁻¹ B]

theorem bigCellFactorization (g : PointGroup ι R) (hA : IsUnit g.val.toBlocks₁₁.det) :
    ∃ (S T : Matrix ι ι R) (hS : S.IsSymm) (hT : T.IsSymm),
      g = lowerShear S hS * leviBlock g.val.toBlocks₁₁ hA * upperShear T hT := by
  obtain ⟨hS, hT, h⟩ := bigCellDecomposition g hA
  exact ⟨_, _, hS, hT, h⟩

open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from Mathlib.LinearAlgebra.SymplecticGroup

/-- An upper shear moves any field-valued point into the first-block chart. -/
theorem moveToBigCell (g : PointGroup ι k) :
    ∃ (T : Matrix ι ι k) (hT : T.IsSymm), IsUnit ((upperShear T hT * g).val.toBlocks₁₁.det) := by
  let A := g.val.toBlocks₁₁
  let B := g.val.toBlocks₁₂
  let C := g.val.toBlocks₂₁
  let D := g.val.toBlocks₂₂
  have hblock : Matrix.fromBlocks A B C D = g.val := Matrix.fromBlocks_toBlocks _
  have h := SymplecticGroup.fromBlocks_mem_iff.mp (hblock.symm ▸ g.property)
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr
    (SymplecticGroup.symplectic_det g.property))
  have hker (x : ι → k) (hx : A • x = 0) (hy : C • x = 0) : x = 0 := by
    change A *ᵥ x = 0 at hx
    change C *ᵥ x = 0 at hy
    have he := hinj (a₁ := Sum.elim x 0) (a₂ := Sum.elim 0 0) (by
      rw [← hblock]
      simp [Matrix.fromBlocks_mulVec, hx, hy])
    exact funext fun i => congrFun he (Sum.inl i)
  obtain ⟨T, hT, hunit⟩ := exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot hker h.1
  refine ⟨T, hT, ?_⟩
  change IsUnit ((Matrix.fromBlocks 1 T 0 1 * g.val).toBlocks₁₁.det)
  rw [← hblock, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, Matrix.one_mul]
  exact (Matrix.isUnit_iff_isUnit_det _).mp hunit

end Cell

section Connectedness

open private matrixEvaluation matrixEvaluation_mapMatrix from LinearAlgebraicGroups.Affine.StandardGroups

private abbrev ParametersFor (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] (β : Type) :=
  MvPolynomial (β × Sym2 ι) (GLCoordinates k ι)

private abbrev Parameters (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :=
  ParametersFor k ι (Fin 3)

variable {β : Type}

private def parameterMatrix (j : β) : Matrix ι ι (ParametersFor k ι β) :=
  fun a b => MvPolynomial.X (j, Sym2.mk a b)

private theorem parameterMatrix_symm (j : β) :
    (parameterMatrix (k := k) (ι := ι) j).IsSymm :=
  Matrix.ext fun _ _ => congrArg (fun s => MvPolynomial.X (j, s)) Sym2.eq_swap

private abbrev parameterLevi : Matrix ι ι (ParametersFor k ι β) :=
  (algebraMap (GLCoordinates k ι) (ParametersFor k ι β)).mapMatrix (universalMatrix k ι)

private theorem parameterLevi_unit :
    IsUnit (parameterLevi (k := k) (ι := ι) (β := β)).det := by
  rw [← RingHom.map_det]
  exact (StandardGroups.isUnit_universalDeterminant k ι).map _

private def parameterPoint : PointGroup ι (Parameters k ι) :=
  (upperShear (parameterMatrix 2) (parameterMatrix_symm 2))⁻¹ *
    lowerShear (parameterMatrix 0) (parameterMatrix_symm 0) *
    leviBlock parameterLevi parameterLevi_unit *
    upperShear (parameterMatrix 1) (parameterMatrix_symm 1)

private def parameterMap : Coordinates k ι →ₐ[k] Parameters k ι :=
  evaluateCoordinates parameterPoint

private def parameterValues {R : Type u} [CommRing R]
    (M : β → Matrix ι ι R) (hM : ∀ j, (M j).IsSymm) : β × Sym2 ι → R :=
  fun j => Sym2.lift ⟨M j.1, fun a b => (congrFun (congrFun (hM j.1).eq a) b).symm⟩ j.2

private def parameterEvaluation {R : Type u} [CommRing R] [Algebra k R]
    (f : GLCoordinates k ι →ₐ[k] R) (x : β × Sym2 ι → R) :
    ParametersFor k ι β →ₐ[k] R where
  __ := MvPolynomial.eval₂Hom f.toRingHom x
  commutes' r := by
    change MvPolynomial.eval₂Hom f.toRingHom x (MvPolynomial.C (algebraMap k (GLCoordinates k ι) r)) =
      algebraMap k R r
    rw [MvPolynomial.eval₂Hom_C]
    exact f.commutes r

private theorem parameterEvaluation_matrix {R : Type u} [CommRing R] [Algebra k R]
    (f : GLCoordinates k ι →ₐ[k] R) (M : β → Matrix ι ι R) (hM : ∀ j, (M j).IsSymm)
    (j : β) :
    (parameterMatrix j).map (parameterEvaluation f (parameterValues M hM)).toRingHom = M j := by
  apply Matrix.ext
  intro a b
  change MvPolynomial.eval₂Hom f.toRingHom (parameterValues M hM)
    (MvPolynomial.X (j, Sym2.mk a b)) = _
  rw [MvPolynomial.eval₂Hom_X']
  exact Sym2.lift_mk _ a b

private theorem parameterEvaluation_levi {R : Type u} [CommRing R] [Algebra k R]
    (A : Matrix.GeneralLinearGroup ι R) (x : β × Sym2 ι → R) :
    parameterLevi.map (parameterEvaluation (glEvaluation (k := k) A) x).toRingHom = A.val := by
  apply Matrix.ext
  intro a b
  change MvPolynomial.eval₂Hom (glEvaluation (k := k) A).toRingHom x
    (MvPolynomial.C (universalMatrix k ι a b)) = _
  rw [MvPolynomial.eval₂Hom_C]
  exact glEvaluation_entry A a b

private theorem map_leviBlock {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix ι ι R) (hA : IsUnit A.det)
    (hB : IsUnit (A.map f).det) :
    mapSymplecticPoint f (leviBlock A hA) = leviBlock (A.map f) hB := by
  have hInv : A⁻¹.map f = (A.map f)⁻¹ := by
    symm
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one f (map_zero f) (map_one f)]
  apply Subtype.ext
  change (Matrix.fromBlocks A 0 0 A⁻¹ᵀ).map f = Matrix.fromBlocks (A.map f) 0 0 (A.map f)⁻¹ᵀ
  rw [Matrix.fromBlocks_map, Matrix.transpose_map, hInv, Matrix.map_zero f (map_zero f)]

private theorem parameterPoint_surjective {R : Type u} [Field R] [Algebra k R]
    (g : PointGroup ι R) :
    ∃ f : Parameters k ι →ₐ[k] R, mapSymplecticPoint f.toRingHom parameterPoint = g := by
  obtain ⟨U, hU, hu⟩ := moveToBigCell g
  let h := upperShear U hU * g
  obtain ⟨S, T, hS, hT, hst⟩ := bigCellFactorization h hu
  let A : Matrix.GeneralLinearGroup ι R := Matrix.GeneralLinearGroup.mk'' h.val.toBlocks₁₁ hu
  let M : Fin 3 → Matrix ι ι R := ![S, T, U]
  have hM (j : Fin 3) : (M j).IsSymm := by
    fin_cases j
    · exact hS
    · exact hT
    · exact hU
  let f := parameterEvaluation (glEvaluation (k := k) A) (parameterValues M hM)
  have hs (j : Fin 3) := parameterEvaluation_matrix (glEvaluation (k := k) A) M hM j
  have ha := parameterEvaluation_levi (k := k) A (parameterValues M hM)
  have hup (j : Fin 3) :
      mapSymplecticPoint f.toRingHom (upperShear (parameterMatrix j) (parameterMatrix_symm j)) =
        upperShear (M j) (hM j) := by
    apply Subtype.ext
    change (Matrix.fromBlocks 1 (parameterMatrix j) 0 1).map f.toRingHom =
      Matrix.fromBlocks 1 (M j) 0 1
    rw [Matrix.fromBlocks_map, hs j]
    simp [Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_zero _ (map_zero f)]
  have hlo :
      mapSymplecticPoint f.toRingHom (lowerShear (parameterMatrix 0) (parameterMatrix_symm 0)) =
        lowerShear S hS := by
    apply Subtype.ext
    change (Matrix.fromBlocks 1 0 (parameterMatrix 0) 1).map f.toRingHom =
      Matrix.fromBlocks 1 0 S 1
    rw [Matrix.fromBlocks_map, hs 0]
    simp [Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_zero _ (map_zero f), M]
  have hl :
      mapSymplecticPoint f.toRingHom (leviBlock parameterLevi parameterLevi_unit) =
        leviBlock h.val.toBlocks₁₁ hu := by
    have hb : IsUnit (parameterLevi.map f.toRingHom).det := ha.symm ▸ hu
    rw [map_leviBlock f.toRingHom _ _ hb]
    apply Subtype.ext
    change Matrix.fromBlocks (parameterLevi.map f.toRingHom) 0 0
        (parameterLevi.map f.toRingHom)⁻¹ᵀ =
      Matrix.fromBlocks h.val.toBlocks₁₁ 0 0 h.val.toBlocks₁₁⁻¹ᵀ
    rw [ha]
    rfl
  refine ⟨f, ?_⟩
  rw [parameterPoint, map_mul, map_mul, map_mul, map_inv, hup, hup, hlo, hl]
  change ((upperShear U hU)⁻¹ * lowerShear S hS) * leviBlock h.val.toBlocks₁₁ hu *
    upperShear T hT = g
  rw [mul_assoc (upperShear U hU)⁻¹, mul_assoc (upperShear U hU)⁻¹, ← hst, inv_mul_cancel_left]

private theorem parameterMap_comap_surjective :
    Function.Surjective (PrimeSpectrum.comap (parameterMap (k := k) (ι := ι)).toRingHom) := by
  intro p
  let K := p.asIdeal.ResidueField
  let a : Coordinates k ι →ₐ[k] K := IsScalarTower.toAlgHom k (Coordinates k ι) K
  obtain ⟨f, hf⟩ := parameterPoint_surjective (k := k) (ι := ι) (evaluatePoint a)
  have hcomp : f.comp parameterMap = a := by
    apply Ideal.Quotient.algHom_ext k
    apply glCoordinates_ext
    intro i j
    change f (evaluateCoordinates parameterPoint (universalSymplecticMatrix k ι i j)) = _
    rw [evaluateCoordinates_entry]
    exact congrFun (congrFun (congrArg Subtype.val hf) i) j
  let z : PrimeSpectrum K := ⟨⊥, inferInstance⟩
  refine ⟨PrimeSpectrum.comap f.toRingHom z, PrimeSpectrum.ext ?_⟩
  change ((PrimeSpectrum.comap parameterMap.toRingHom ∘ PrimeSpectrum.comap f.toRingHom) z).asIdeal = _
  rw [← PrimeSpectrum.comap_comp]
  change (PrimeSpectrum.comap (f.comp parameterMap).toRingHom z).asIdeal = _
  rw [hcomp]
  exact Ideal.ker_algebraMap_residueField p.asIdeal

private theorem genericDeterminant_ne_zero : genericDeterminant k ι ≠ 0 := by
  intro hz
  have h1 : matrixEvaluation (1 : Matrix ι ι k) (genericDeterminant k ι) = 1 := by
    rw [genericDeterminant, AlgHom.map_det, matrixEvaluation_mapMatrix, Matrix.det_one]
  rw [hz, map_zero] at h1
  exact zero_ne_one h1

private theorem parameters_isDomain : IsDomain (Parameters k ι) := by
  have : IsDomain (GLCoordinates k ι) := Localization.Away.isDomain genericDeterminant_ne_zero
  infer_instance

theorem irreducibleSymplecticScheme (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :
    IrreducibleSpace (symplecticScheme k ι).left := by
  have : IsDomain (Parameters k ι) := parameters_isDomain
  change IrreducibleSpace (PrimeSpectrum (Coordinates k ι))
  exact parameterMap_comap_surjective.irreducibleSpace (PrimeSpectrum.continuous_comap _)

end Connectedness

section Dimension

/-- The determinant of the first diagonal block, which cuts out the identity chart. -/
private def firstBlockDet : Coordinates k ι :=
  (universalSymplecticMatrix k ι).toBlocks₁₁.det

private abbrev CellCoordinates (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :=
  Localization.Away (firstBlockDet (k := k) (ι := ι))

private abbrev CellParameters (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :=
  ParametersFor k ι (Fin 2)

private def cellProduct {R : Type u} [CommRing R]
    (A S T : Matrix ι ι R) (hA : IsUnit A.det) (hS : S.IsSymm) (hT : T.IsSymm) :
    PointGroup ι R :=
  lowerShear S hS * leviBlock A hA * upperShear T hT

private theorem cellProduct_blocks {R : Type u} [CommRing R]
    (A S T : Matrix ι ι R) (hA : IsUnit A.det) (hS : S.IsSymm) (hT : T.IsSymm) :
    (cellProduct A S T hA hS hT).val =
      Matrix.fromBlocks A (A * T) (S * A) ((S * A) * T + A⁻¹ᵀ) := by
  change Matrix.fromBlocks 1 0 S 1 * Matrix.fromBlocks A 0 0 A⁻¹ᵀ *
    Matrix.fromBlocks 1 T 0 1 = _
  simp [Matrix.fromBlocks_multiply]

private theorem map_cellProduct {R Q : Type u} [CommRing R] [CommRing Q]
    (f : R →+* Q) (A S T : Matrix ι ι R) (hA : IsUnit A.det) (hS : S.IsSymm) (hT : T.IsSymm)
    (hA' : IsUnit (A.map f).det) (hS' : (S.map f).IsSymm) (hT' : (T.map f).IsSymm) :
    mapSymplecticPoint f (cellProduct A S T hA hS hT) =
      cellProduct (A.map f) (S.map f) (T.map f) hA' hS' hT' := by
  have hs : mapSymplecticPoint f (lowerShear S hS) = lowerShear (S.map f) hS' := by
    apply Subtype.ext
    change (Matrix.fromBlocks 1 0 S 1).map f = _
    simp [lowerShear, Matrix.fromBlocks_map, Matrix.map_one _ (map_zero f) (map_one f),
      Matrix.map_zero _ (map_zero f)]
  have ht : mapSymplecticPoint f (upperShear T hT) = upperShear (T.map f) hT' := by
    apply Subtype.ext
    change (Matrix.fromBlocks 1 T 0 1).map f = _
    simp [upperShear, Matrix.fromBlocks_map, Matrix.map_one _ (map_zero f) (map_one f),
      Matrix.map_zero _ (map_zero f)]
  simp only [cellProduct, map_mul, hs, ht, map_leviBlock f A hA hA']

private def cellParameterPoint : PointGroup ι (CellParameters k ι) :=
  cellProduct parameterLevi (parameterMatrix 0) (parameterMatrix 1) parameterLevi_unit
    (parameterMatrix_symm 0) (parameterMatrix_symm 1)

private def cellParameterMap : Coordinates k ι →ₐ[k] CellParameters k ι :=
  evaluateCoordinates cellParameterPoint

private theorem evaluateCoordinates_matrix {R : Type u} [CommRing R] [Algebra k R]
    (g : PointGroup ι R) :
    (evaluateCoordinates (k := k) g).mapMatrix (universalSymplecticMatrix k ι) = g.val :=
  Matrix.ext (evaluateCoordinates_entry g)

private theorem cellParameterMap_det :
    IsUnit ((cellParameterMap (k := k) (ι := ι)) firstBlockDet) := by
  have h := evaluateCoordinates_matrix (k := k) (cellParameterPoint (k := k) (ι := ι))
  change IsUnit ((evaluateCoordinates cellParameterPoint) _)
  rw [firstBlockDet, AlgHom.map_det]
  change IsUnit (((evaluateCoordinates cellParameterPoint).mapMatrix
    (universalSymplecticMatrix k ι)).toBlocks₁₁.det)
  rw [h, cellParameterPoint, cellProduct_blocks, Matrix.toBlocks_fromBlocks₁₁]
  exact parameterLevi_unit

private def cellToParameters : CellCoordinates k ι →ₐ[k] CellParameters k ι :=
  IsLocalization.Away.liftAlgHom _ cellParameterMap_det

private def cellUniversal : PointGroup ι (CellCoordinates k ι) :=
  evaluatePoint (IsScalarTower.toAlgHom k (Coordinates k ι) (CellCoordinates k ι))

private theorem cellUniversal_unit :
    IsUnit ((cellUniversal (k := k) (ι := ι)).val.toBlocks₁₁.det) := by
  change IsUnit ((algebraMap (Coordinates k ι) (CellCoordinates k ι)).mapMatrix
    (universalSymplecticMatrix k ι).toBlocks₁₁).det
  rw [← RingHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit (firstBlockDet (k := k) (ι := ι))

private abbrev cellCoefficients :
    Fin 2 → Matrix ι ι (CellCoordinates k ι) :=
  let g := (cellUniversal (k := k) (ι := ι)).val
  ![g.toBlocks₂₁ * g.toBlocks₁₁⁻¹, g.toBlocks₁₁⁻¹ * g.toBlocks₁₂]

private theorem cellCoefficients_symm (j : Fin 2) :
    (cellCoefficients (k := k) (ι := ι) j).IsSymm := by
  obtain ⟨hS, hT, _⟩ := bigCellDecomposition cellUniversal
    (cellUniversal_unit (k := k) (ι := ι))
  fin_cases j
  · exact hS
  · exact hT

private abbrev cellFirstBlock : Matrix.GeneralLinearGroup ι (CellCoordinates k ι) :=
  Matrix.GeneralLinearGroup.mk'' (cellUniversal (k := k) (ι := ι)).val.toBlocks₁₁
    cellUniversal_unit

private def cellFromParameters : CellParameters k ι →ₐ[k] CellCoordinates k ι :=
  parameterEvaluation (glEvaluation cellFirstBlock)
    (parameterValues cellCoefficients cellCoefficients_symm)

private theorem cellFromParameters_point :
    mapSymplecticPoint (cellFromParameters (k := k) (ι := ι)).toRingHom cellParameterPoint =
      cellUniversal := by
  let f := cellFromParameters (k := k) (ι := ι)
  let A : Matrix.GeneralLinearGroup ι (CellCoordinates k ι) := cellFirstBlock
  let M : Fin 2 → Matrix ι ι (CellCoordinates k ι) := cellCoefficients
  have hA : parameterLevi.map f.toRingHom = A.val :=
    parameterEvaluation_levi (k := k) A (parameterValues M cellCoefficients_symm)
  have hM (j : Fin 2) : (parameterMatrix j).map f.toRingHom = M j :=
    parameterEvaluation_matrix (glEvaluation (k := k) A) M cellCoefficients_symm j
  obtain ⟨hS, hT, hg⟩ := bigCellDecomposition cellUniversal
    (cellUniversal_unit (k := k) (ι := ι))
  have hu : IsUnit (parameterLevi.map f.toRingHom).det := hA.symm ▸ cellUniversal_unit
  have hs : ((parameterMatrix 0).map f.toRingHom).IsSymm := (hM 0).symm ▸ hS
  have ht : ((parameterMatrix 1).map f.toRingHom).IsSymm := (hM 1).symm ▸ hT
  change mapSymplecticPoint f.toRingHom cellParameterPoint = cellUniversal
  rw [cellParameterPoint, map_cellProduct f.toRingHom _ _ _ _ _ _ hu hs ht]
  apply Subtype.ext
  trans (cellProduct _ _ _ cellUniversal_unit hS hT).val
  · simp only [cellProduct_blocks, hA, hM]
    rfl
  · exact (congrArg Subtype.val hg).symm

private theorem cellToParameters_map (x : Coordinates k ι) :
    cellToParameters (algebraMap (Coordinates k ι) (CellCoordinates k ι) x) =
      cellParameterMap x :=
  IsLocalization.Away.lift_eq _ cellParameterMap_det x

private theorem cellToParameters_point :
    mapSymplecticPoint (cellToParameters (k := k) (ι := ι)).toRingHom cellUniversal =
      cellParameterPoint := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  exact (cellToParameters_map (universalSymplecticMatrix k ι i j)).trans
    (evaluateCoordinates_entry cellParameterPoint i j)

private theorem cellFromParameters_leftInverse :
    (cellFromParameters (k := k) (ι := ι)).comp cellToParameters = AlgHom.id _ _ := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (firstBlockDet (k := k) (ι := ι)))
  apply RingHom.ext
  intro x
  change cellFromParameters (cellToParameters
    (algebraMap (Coordinates k ι) (CellCoordinates k ι) x)) =
      algebraMap (Coordinates k ι) (CellCoordinates k ι) x
  rw [cellToParameters_map]
  have h : (cellFromParameters (k := k) (ι := ι)).comp cellParameterMap =
      IsScalarTower.toAlgHom k (Coordinates k ι) (CellCoordinates k ι) := by
    apply Ideal.Quotient.algHom_ext k
    apply glCoordinates_ext
    intro i j
    change cellFromParameters (cellParameterMap (universalSymplecticMatrix k ι i j)) =
      algebraMap (Coordinates k ι) (CellCoordinates k ι) (universalSymplecticMatrix k ι i j)
    rw [cellParameterMap, evaluateCoordinates_entry]
    exact congrFun (congrFun (congrArg Subtype.val cellFromParameters_point) i) j
  exact DFunLike.congr_fun h x

private theorem cellFromParameters_rightInverse :
    (cellToParameters (k := k) (ι := ι)).comp cellFromParameters = AlgHom.id _ _ := by
  let f := cellToParameters (k := k) (ι := ι)
  have h := congrArg Subtype.val (cellToParameters_point (k := k) (ι := ι))
  change (cellUniversal (k := k) (ι := ι)).val.map f.toRingHom = _ at h
  rw [cellParameterPoint, cellProduct_blocks] at h
  let g := (cellUniversal (k := k) (ι := ι)).val
  have hA : g.toBlocks₁₁.map f.toRingHom = parameterLevi :=
    congrArg Matrix.toBlocks₁₁ h
  have hB : g.toBlocks₁₂.map f.toRingHom = parameterLevi * parameterMatrix 1 :=
    congrArg Matrix.toBlocks₁₂ h
  have hC : g.toBlocks₂₁.map f.toRingHom = parameterMatrix 0 * parameterLevi :=
    congrArg Matrix.toBlocks₂₁ h
  have hi : (cellUniversal (k := k) (ι := ι)).val.toBlocks₁₁⁻¹.map f.toRingHom =
      (parameterLevi (k := k) (ι := ι) (β := Fin 2))⁻¹ := by
    symm
    apply Matrix.inv_eq_right_inv
    rw [← hA, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ cellUniversal_unit]
    exact Matrix.map_one f.toRingHom (map_zero f) (map_one f)
  let A : Matrix.GeneralLinearGroup ι (CellCoordinates k ι) := cellFirstBlock
  let M : Fin 2 → Matrix ι ι (CellCoordinates k ι) := cellCoefficients
  have he : parameterLevi.map (cellFromParameters (k := k) (ι := ι)).toRingHom = A.val :=
    parameterEvaluation_levi (k := k) A (parameterValues M cellCoefficients_symm)
  have hm (j : Fin 2) :
      (parameterMatrix j).map (cellFromParameters (k := k) (ι := ι)).toRingHom = M j :=
    parameterEvaluation_matrix (glEvaluation (k := k) A) M cellCoefficients_symm j
  apply MvPolynomial.algHom_ext'
  · apply glCoordinates_ext
    intro i j
    change f (cellFromParameters (MvPolynomial.C (universalMatrix k ι i j))) =
      parameterLevi i j
    change f (parameterLevi.map cellFromParameters.toRingHom i j) = _
    rw [he]
    exact congrFun (congrFun hA i) j
  · rintro ⟨l, s⟩
    induction s using Sym2.ind with
    | _ i j =>
      change f (cellFromParameters (parameterMatrix l i j)) = parameterMatrix l i j
      rw [show cellFromParameters (parameterMatrix l i j) =
        cellCoefficients l i j from congrFun (congrFun (hm l) i) j]
      have hc : (cellCoefficients l).map f.toRingHom = parameterMatrix l := by
        fin_cases l
        · change ((_ : Matrix ι ι (CellCoordinates k ι)) * _).map f.toRingHom = _
          rw [Matrix.map_mul, hi]
          rw [hC, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ parameterLevi_unit, Matrix.mul_one]
          rfl
        · change ((_ : Matrix ι ι (CellCoordinates k ι)) * _).map f.toRingHom = _
          rw [Matrix.map_mul, hi]
          rw [hB, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ parameterLevi_unit, Matrix.one_mul]
          rfl
      exact congrFun (congrFun hc i) j

private def cellCoordinatesEquiv : CellCoordinates k ι ≃ₐ[k] CellParameters k ι :=
  AlgEquiv.ofAlgHom cellToParameters cellFromParameters
    cellFromParameters_rightInverse cellFromParameters_leftInverse

open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria

private theorem coordinates_isDomain : IsDomain (Coordinates k ι) := by
  let A := CommRingCat.of (Coordinates k ι)
  let f := Spec.map (CommRingCat.ofHom (algebraMap k (Coordinates k ι)))
  have hs : Smooth f := smoothness k ι
  have hred : IsReduced (Spec A) := @isReduced_of_smooth_over_field k _ (Spec A) f hs
  have : _root_.IsReduced (Coordinates k ι) := (affine_isReduced_iff A).mp hred
  have hi : IrreducibleSpace (PrimeSpectrum (Coordinates k ι)) := irreducibleSymplecticScheme k ι
  have hp := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hi
  rw [nilradical_eq_zero (Coordinates k ι)] at hp
  have : IsDomain (Coordinates k ι ⧸ (⊥ : Ideal (Coordinates k ι))) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr hp
  exact (RingEquiv.quotientBot _).symm.injective.isDomain _

private theorem firstBlockDet_ne_zero : firstBlockDet (k := k) (ι := ι) ≠ 0 := by
  intro h
  have he := evaluateCoordinates_matrix (k := k) (1 : PointGroup ι k)
  have e : (evaluateCoordinates (k := k) (1 : PointGroup ι k)) firstBlockDet = 1 := by
    rw [firstBlockDet, AlgHom.map_det]
    change (((evaluateCoordinates (k := k) (1 : PointGroup ι k)).mapMatrix
      (universalSymplecticMatrix k ι)).toBlocks₁₁).det = 1
    rw [he]
    change (Matrix.toBlocks₁₁ (1 : Matrix (Indices ι) (Indices ι) k)).det = 1
    have hA : Matrix.toBlocks₁₁ (1 : Matrix (Indices ι) (Indices ι) k) = 1 := by
      apply Matrix.ext
      intro i j
      change (1 : Matrix (Indices ι) (Indices ι) k) (Sum.inl i) (Sum.inl j) =
        (1 : Matrix ι ι k) i j
      simp [Matrix.one_apply]
    rw [hA, Matrix.det_one]
  rw [h, map_zero] at e
  exact zero_ne_one e

private theorem dimension_away {A : Type u} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (d : A) (hd : d ≠ 0) :
    ringKrullDim (Localization.Away d) = ringKrullDim A := by
  let B := Localization.Away d
  let F := FractionRing A
  have : IsDomain B := Localization.Away.isDomain hd
  have : Algebra.FiniteType k B :=
    Algebra.FiniteType.trans (R := k) (S := A) (A := B) inferInstance inferInstance
  let le : Submonoid.powers d ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hd
  letI : Algebra B F :=
    IsLocalization.localizationAlgebraOfSubmonoidLe B F _ _ le
  have : IsScalarTower A B F := IsLocalization.localization_isScalarTower_of_submonoid_le B F _ _ le
  have : IsScalarTower k B F := IsScalarTower.to₁₃₄ k A B F
  have : IsFractionRing B F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers d) B F
  let e := (IsLocalization.algEquiv (nonZeroDivisors B) (FractionRing B) F).restrictScalars k
  rw [P103.Ch06.AffineDimension.domain_dimension k B, P103.Ch06.AffineDimension.domain_dimension k A,
    e.trdeg_eq]

theorem dimension : Specs.SymplecticMatrixStructure.Dimension.{u} := by
  intro k ι _ _ _
  have : IsDomain (Coordinates k ι) := coordinates_isDomain
  have : IsDomain (GLCoordinates k ι) := Localization.Away.isDomain
    (genericDeterminant_ne_zero (k := k) (ι := ι))
  rw [← dimension_away (k := k) _ firstBlockDet_ne_zero,
    ringKrullDim_eq_of_ringEquiv (cellCoordinatesEquiv (k := k) (ι := ι)).toRingEquiv]
  change ringKrullDim (MvPolynomial (Fin 2 × Sym2 ι) (GLCoordinates k ι)) = _
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    dimension_away (k := k) _ genericDeterminant_ne_zero,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp only [zero_add, ← Nat.cast_add, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_fin, Sym2.card]
  congr 1
  let n := Fintype.card ι
  have h : (n + 1).choose 2 * 2 = n * (n + 1) := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm (n + 1) n,
      Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_succ_self n))]
  rw [Nat.mul_comm 2, h]
  ring

end Dimension

section BaseChange

variable (K : Type u) [Field K] [Algebra k K]

open private groupBaseChangePointIso from LinearAlgebraicGroups.Affine.RationalRepresentations

/-- The same symplectic equations represent points after arbitrary field extension. -/
def baseChangeSymplecticPointsIso {G : GroupScheme k}
    (c : (groupPointsFunctor k).obj G ≅ symplecticPoints k ι) :
    (groupPointsFunctor K).obj ((groupBaseChange k K).obj G) ≅ symplecticPoints K ι :=
  groupBaseChangePointIso K G ≪≫ Functor.isoWhiskerLeft (restrictTestAlgebra k K) c

end BaseChange

open private groupIsoOfPoints from LinearAlgebraicGroups.Unipotent.Criteria

theorem geometricConnectedness : GeometricConnectedness.{u} := by
  intro k ι _ _ _
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun X : Scheme.{u} => ConnectedSpace X)).mpr ?_⟩
  intro K _ _
  let G := symplecticGroup k ι
  let H := Specs.Unipotent.baseChangedAlgebraicGroup K G
  let e : H.val ≅ (symplecticGroup K ι).val :=
    groupIsoOfPoints (baseChangeSymplecticPointsIso K (symplecticGroupPointsIso k ι) ≪≫
      (symplecticGroupPointsIso K ι).symm)
  let e' := ((Grp.forget (SchemeOver K)) ⋙ Over.forget (Spec (CommRingCat.of K))).mapIso e
  have : IrreducibleSpace
      (((Grp.forget (SchemeOver K)) ⋙ Over.forget (Spec (CommRingCat.of K))).obj
        (symplecticGroup K ι).val) :=
    irreducibleSymplecticScheme K ι
  change ConnectedSpace H.val.X.left
  let j := (Scheme.homeoOfIso e').symm
  exact j.surjective.connectedSpace j.continuous


section TorusEmbedding

open WithConv

open private Representation.equiv laurentPowerMulEquiv laurentPowerMulEquiv_eval
  laurentPowerIso basis_expansion from LinearAlgebraicGroups.Affine.StandardGroups

private def torusRepresentation :
    Representation (LaurentPowerCoordinates k ι) (multiplicativePowerPoints k ι) :=
  Representation.mk (fun R =>
    { toFun := fun f => laurentPowerMulEquiv R (toConv f)
      invFun := fun t => ((laurentPowerMulEquiv R).symm t).ofConv
      left_inv := fun f => congrArg ofConv ((laurentPowerMulEquiv R).symm_apply_apply (toConv f))
      right_inv := fun t => (laurentPowerMulEquiv R).apply_symm_apply t })
    (fun a f => DFunLike.congr_fun (congrArg GrpCat.Hom.hom (laurentPowerIso.hom.naturality a))
      (toConv f))

private def diagonalUnits (R : Type u) [CommRing R] (i : ι) :
    (AddMonoidAlgebra R (ι → ℤ))ˣ :=
  LaurentUnits R ι (Multiplicative.ofAdd (Pi.single i 1))

private def torusCoordinateMap : Coordinates k ι →ₐ[k] LaurentPowerCoordinates k ι :=
  evaluateCoordinates (diagonalPoint ι _ (diagonalUnits k))

private theorem torusCoordinateMap_compatibility (R : TestAlgebra k)
    (f : LaurentPowerCoordinates k ι →ₐ[k] R) :
    Representation.equiv (symplecticRepresentation (k := k) (ι := ι)) R
      (f.comp torusCoordinateMap) =
    diagonalPoint ι R (Representation.equiv torusRepresentation R f) := by
  have hunit (i : ι) : Units.map f.toMonoidHom ((diagonalUnits k) i) =
      (Representation.equiv torusRepresentation R f : ι → Rˣ) i := by
    apply Units.ext
    exact (laurentPowerMulEquiv_eval R f i).symm
  have hmat : (torusCoordinateMap (k := k) (ι := ι)).mapMatrix (universalSymplecticMatrix k ι) =
      hyperbolicDiagonal (diagonalUnits k) :=
    Matrix.ext (evaluateCoordinates_entry (diagonalPoint ι _ (diagonalUnits k)))
  apply Subtype.ext
  change f.mapMatrix ((torusCoordinateMap (k := k) (ι := ι)).mapMatrix
    (universalSymplecticMatrix k ι)) =
    hyperbolicDiagonal (Representation.equiv torusRepresentation R f)
  rw [hmat]
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    cases i with
    | inl i =>
      simpa [hyperbolicDiagonal] using congrArg Units.val (hunit i)
    | inr i =>
      have h := congrArg (fun t : Rˣ => (↑t⁻¹ : R)) (hunit i)
      simpa [hyperbolicDiagonal, Units.coe_map_inv] using h
  · simp [hyperbolicDiagonal, Matrix.diagonal_apply_ne _ hij]

private theorem torusCoordinateMap_surjective :
    Function.Surjective (torusCoordinateMap (k := k) (ι := ι)) := by
  let a := torusCoordinateMap (k := k) (ι := ι)
  have hplus (i : ι) : (↑(diagonalUnits k i) : LaurentPowerCoordinates k ι) ∈ a.range := by
    refine ⟨universalSymplecticMatrix k ι (Sum.inl i) (Sum.inl i), ?_⟩
    change evaluateCoordinates (diagonalPoint ι _ (diagonalUnits k))
      (universalSymplecticMatrix k ι _ _) = _
    rw [evaluateCoordinates_entry]
    simp [diagonalPoint, hyperbolicDiagonal]
  have hminus (i : ι) : (↑(diagonalUnits k i)⁻¹ : LaurentPowerCoordinates k ι) ∈ a.range := by
    refine ⟨universalSymplecticMatrix k ι (Sum.inr i) (Sum.inr i), ?_⟩
    change evaluateCoordinates (diagonalPoint ι _ (diagonalUnits k))
      (universalSymplecticMatrix k ι _ _) = _
    rw [evaluateCoordinates_entry]
    simp [diagonalPoint, hyperbolicDiagonal]
  have hp (i : ι) (n : ℤ) :
      (↑((diagonalUnits k i) ^ n) : LaurentPowerCoordinates k ι) ∈ a.range := by
    cases n with
    | ofNat n => simpa using a.range.pow_mem (hplus i) n
    | negSucc n => simpa using a.range.pow_mem (hminus i) (n + 1)
  let v : Multiplicative (ι → ℤ) →* LaurentPowerCoordinates k ι :=
    (Units.coeHom _).comp (LaurentUnits k ι)
  have hm (m : ι → ℤ) : AddMonoidAlgebra.single m (1 : k) ∈ a.range := by
    have hc := congrArg v (basis_expansion (Multiplicative.ofAdd m))
    change v (∏ i, Multiplicative.ofAdd (Pi.single i 1) ^ m i) =
      AddMonoidAlgebra.single m 1 at hc
    rw [map_prod] at hc
    rw [← hc]
    apply a.range.prod_mem
    intro i _
    change (↑(LaurentUnits k ι (Multiplicative.ofAdd (Pi.single i 1) ^ m i)) :
      LaurentPowerCoordinates k ι) ∈ a.range
    rw [map_zpow]
    exact hp i (m i)
  intro x
  change x ∈ a.range
  induction x using AddMonoidAlgebra.induction_on with
  | of m => exact hm m
  | add x y hx hy => exact a.range.add_mem hx hy
  | smul r x hx => exact a.range.smul_mem hx r

@[instance_reducible]
private def diagonalHopf (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :
    HopfAlgebra k (LaurentPowerCoordinates k ι) :=
  Representation.hopf (torusRepresentation (k := k) (ι := ι))

private def diagonalGroup (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :
    AffineAlgebraicGroup k :=
  letI := diagonalHopf k ι
  spectrum k (LaurentPowerCoordinates k ι)

private def diagonalGroupPointsIso (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :
    (groupPointsFunctor k).obj (diagonalGroup k ι).val ≅ multiplicativePowerPoints k ι :=
  letI := diagonalHopf k ι
  spectrumPointsIso (Representation.convolutionIso (torusRepresentation (k := k) (ι := ι)))

local instance : HopfAlgebra k (LaurentPowerCoordinates k ι) := diagonalHopf k ι

private def diagonalHopfMap : CommHopfAlgCat.of k (Coordinates k ι) ⟶
    CommHopfAlgCat.of k (LaurentPowerCoordinates k ι) := by
  letI : Bialgebra k (Coordinates k ι) := (symplecticHopf k ι).toBialgebra
  letI : Bialgebra k (LaurentPowerCoordinates k ι) := (diagonalHopf k ι).toBialgebra
  have h := Representation.compatible (symplecticRepresentation (k := k) (ι := ι))
    torusRepresentation torusCoordinateMap (fun R => diagonalPoint ι R) torusCoordinateMap_compatibility
  exact CommHopfAlgCat.ofHom (BialgHom.ofAlgHom torusCoordinateMap h.2.1.symm h.1)

def symplecticDiagonalTorus (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :
    ClosedSubgroup (symplecticGroup k ι).val :=
  ⟨(diagonalGroup k ι).val, specGroupMap diagonalHopfMap,
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (torusCoordinateMap (k := k) (ι := ι)).toRingHom)
      torusCoordinateMap_surjective⟩

private theorem diagonalTorus_points (R : TestAlgebra k) (t : ι → Rˣ) :
    (show PointGroup ι R from
      (symplecticGroupPointsIso k ι).hom.app R
        (((groupPointsFunctor k).map (symplecticDiagonalTorus k ι).inclusion).app R
          ((diagonalGroupPointsIso k ι).inv.app R t))).val = hyperbolicDiagonal t := by
  let f := (Representation.equiv (torusRepresentation (k := k) (ι := ι)) R).symm t
  let A := CommHopfAlgCat.of k (LaurentPowerCoordinates k ι)
  let C := CommHopfAlgCat.of k (Coordinates k ι)
  let d := diagonalGroupPointsIso k ι
  let c := symplecticGroupPointsIso k ι
  have hft : Representation.equiv (torusRepresentation (k := k) (ι := ι)) R f = t :=
    Equiv.apply_symm_apply _ _
  have hd :
      d.hom.app R ((hopfSpecPointIso A).hom.app R (toConv f)) = t := by
    change ((hopfSpecPointIso A ≪≫ d).hom.app R) (toConv f) = t
    have he : hopfSpecPointIso A ≪≫ d =
        Representation.convolutionIso (torusRepresentation (k := k) (ι := ι)) := by
      change (hopfSpecPointIso A ≪≫ ((hopfSpecPointIso A).symm ≪≫ _)) = _
      simp
    rw [he]
    exact hft
  have hp : d.inv.app R t = (hopfSpecPointIso A).hom.app R (toConv f) := by
    rw [← hd]
    exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom (Iso.hom_inv_id_app d R)) _
  have he :
      ((groupPointsFunctor k).map (symplecticDiagonalTorus k ι).inclusion).app R
        ((hopfSpecPointIso A).hom.app R (toConv f)) =
      (hopfSpecPointIso C).hom.app R (toConv (f.comp (torusCoordinateMap (k := k) (ι := ι)))) := by
    apply Over.OverMorphism.ext
    exact (Spec.map_comp (CommRingCat.ofHom
      (torusCoordinateMap (k := k) (ι := ι)).toRingHom) (CommRingCat.ofHom f.toRingHom)).symm
  have hc : hopfSpecPointIso C ≪≫ c =
      Representation.convolutionIso (symplecticRepresentation (k := k) (ι := ι)) := by
    change (hopfSpecPointIso C ≪≫ ((hopfSpecPointIso C).symm ≪≫ _)) = _
    simp
  rw [hp, he]
  change (show PointGroup ι R from (hopfSpecPointIso C ≪≫ c).hom.app R
    (toConv (f.comp (torusCoordinateMap (k := k) (ι := ι))))).val = _
  rw [hc]
  exact congrArg Subtype.val ((torusCoordinateMap_compatibility R f).trans
    (congrArg (diagonalPoint ι R) hft))

private def reindexPowerPoints {α β : Type u} (e : α ≃ β) :
    multiplicativePowerPoints k α ≅ multiplicativePowerPoints k β :=
  NatIso.ofComponents (fun R =>
    (show (α → Rˣ) ≃* (β → Rˣ) from
      { toFun := fun x j => x (e.symm j)
        invFun := fun y i => y (e i)
        left_inv := fun x => funext fun i => congrArg x (e.symm_apply_apply i)
        right_inv := fun y => funext fun j => congrArg y (e.apply_symm_apply j)
        map_mul' := fun _ _ => rfl }).toGrpIso)
    (by intro R S f; apply GrpCat.ext; intro x; rfl)

theorem diagonalTorusEmbedding : DiagonalTorusEmbedding.{u} := by
  intro k ι _ _ _ G c
  let S := symplecticGroup k ι
  let T := symplecticDiagonalTorus k ι
  let d := diagonalGroupPointsIso k ι
  let ps := symplecticGroupPointsIso k ι
  let e : S.val ⟶ G.val := (groupHomEquiv S.val G.val S.property.1).symm (ps.hom ≫ c.inv)
  have he : (groupPointsFunctor k).map e = ps.hom ≫ c.inv :=
    (groupHomEquiv S.val G.val S.property.1).apply_symm_apply _
  have hiso : IsIso e := by
    let i : G.val ⟶ S.val := (groupHomEquiv G.val S.val G.property.1).symm (c.hom ≫ ps.inv)
    have hi : (groupPointsFunctor k).map i = c.hom ≫ ps.inv :=
      (groupHomEquiv G.val S.val G.property.1).apply_symm_apply _
    have h₁ : e ≫ i = 𝟙 S.val := by
      apply (groupHomComparison k S.val S.val S.property.1).1
      simp [he, hi]
    have h₂ : i ≫ e = 𝟙 G.val := by
      apply (groupHomComparison k G.val G.val G.property.1).1
      simp [he, hi]
    exact ⟨i, h₁, h₂⟩
  have he' : IsIso e.hom.hom.left := by
    change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget (Spec (CommRingCat.of k))).map e)
    infer_instance
  have hiT : IsClosedImmersion T.inclusion.hom.hom.left := T.isClosedImmersion
  refine ⟨⟨T.group, T.inclusion ≫ e, inferInstanceAs
    (IsClosedImmersion (T.inclusion.hom.hom.left ≫ e.hom.hom.left))⟩, d, ?_, ?_⟩
  · let ix : ι ≃ ULift.{u} (Fin (Fintype.card ι)) :=
      (Fintype.equivFin ι).trans Equiv.ulift.symm
    exact ⟨groupIsoOfPoints (d ≪≫ reindexPowerPoints ix ≪≫
      (StandardGroups.multiplicativePowerGroupPointsIso k _).symm)⟩
  · intro R t
    simp only [Functor.map_comp, he, NatTrans.comp_app, GrpCat.comp_apply]
    simp only [Iso.inv_hom_id_app_apply]
    exact diagonalTorus_points (k := k) (ι := ι) R t

end TorusEmbedding

section MaximalTorus

open scoped TensorProduct

open private groupBaseChangePointIso from LinearAlgebraicGroups.Affine.RationalRepresentations

private def baseChangePowerPointsIso {K : Type u} [Field K] [Algebra k K]
    {T : GroupScheme k} (d : (groupPointsFunctor k).obj T ≅ multiplicativePowerPoints k ι) :
    (groupPointsFunctor K).obj ((groupBaseChange k K).obj T) ≅ multiplicativePowerPoints K ι :=
  groupBaseChangePointIso K T ≪≫ Functor.isoWhiskerLeft (restrictTestAlgebra k K) d

private theorem baseChange_diagonal_points {K : Type u} [Field K] [Algebra k K]
    {G : GroupScheme k} (c : (groupPointsFunctor k).obj G ≅ symplecticPoints k ι)
    (T : ClosedSubgroup G)
    (d : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k ι)
    (hd : ∀ (R : TestAlgebra k) (t : ι → Rˣ),
      (show PointGroup ι R from
        c.hom.app R (((groupPointsFunctor k).map T.inclusion).app R (d.inv.app R t))).val =
          hyperbolicDiagonal t)
    (R : TestAlgebra K) (t : ι → Rˣ) :
    (show PointGroup ι R from
      (baseChangeSymplecticPointsIso K c).hom.app R
        (((groupPointsFunctor K).map ((groupBaseChange k K).map T.inclusion)).app R
          ((baseChangePowerPointsIso d).inv.app R t))).val = hyperbolicDiagonal t := by
  let r := (restrictTestAlgebra k K).obj R
  let p : Points ((baseChange k K).obj T.group.X) R :=
    (baseChangePowerPointsIso (K := K) d).inv.app R t
  have hp : baseChangePoint k K T.group.X R p = d.inv.app r t := by
    let e := groupBaseChangePointIso K T.group
    change e.hom.app R (e.inv.app R (d.inv.app r t)) = _
    exact Iso.inv_hom_id_app_apply e R (d.inv.app r t)
  let entryMatrix (x : Points G.X r) : Matrix (Indices ι) (Indices ι) R :=
    (show PointGroup ι r from c.hom.app r x).val
  change entryMatrix (baseChangePoint k K G.X R
    (p ≫ (baseChange k K).map T.inclusion.hom.hom)) = _
  have hnat := baseChangePointsSchemeNaturality k K T.inclusion.hom.hom R p
  have heq := hnat.trans (congrArg (fun x : Points T.group.X r => x ≫ T.inclusion.hom.hom) hp)
  exact (congrArg entryMatrix heq).trans (hd r t)

/-- The image of a torus under the symplectic representation has commuting points.
One can check this after the injective extension R → E ⊗ R to a splitting field. -/
private theorem torusImageCommutes {G S : GroupScheme k}
    (c : (groupPointsFunctor k).obj G ≅ symplecticPoints k ι)
    (i : S ⟶ G) (hS : GeometricRadicals.IsTorus S)
    (R : TestAlgebra k) (p q : Points S.X R) :
    Commute ((c.hom.app R) (((groupPointsFunctor k).map i).app R p))
      ((c.hom.app R) (((groupPointsFunctor k).map i).app R q)) := by
  obtain ⟨E, _, _, _, r, ⟨e⟩⟩ := hS
  let U := CommAlgCat.of E (E ⊗[k] R)
  let U' := (restrictTestAlgebra k E).obj U
  let f := (Algebra.TensorProduct.includeRight : R →ₐ[k] E ⊗[k] R)
  let f₀ : R →+* E ⊗[k] R := f.toRingHom
  let a : R ⟶ U' := by
    apply ConcreteCategory.ofHom (X := R) (Y := U')
    refine @AlgHom.mk k R U' _ _ _ R.algebra U'.algebra f₀ ?_
    intro x
    change f (algebraMap k R x) = algebraMap E (E ⊗[k] R) (algebraMap k E x)
    exact (f.commutes x).trans (IsScalarTower.algebraMap_apply k E (E ⊗[k] R) x)
  have ha : Function.Injective a.hom := by
    change Function.Injective f
    exact Algebra.TensorProduct.includeRight_injective (B := R) (RingHom.injective (algebraMap k E))
  let m := (groupPointsFunctor k).map i ≫ c.hom
  let ap := ((symplecticPoints k ι).map a).hom
  have hap : Function.Injective ap := by
    intro x y h
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    exact ha (congrFun (congrFun (congrArg Subtype.val h) i) j)
  let F := (groupPointsFunctor E).obj ((groupBaseChange k E).obj S)
  let H := (groupPointsFunctor k).obj S
  let b : F.obj U ≃* H.obj U' := baseChangePointGroupEquiv E S U
  let ψ := ((groupPointsFunctor E).mapIso e ≪≫
    StandardGroups.multiplicativePowerGroupPointsIso E _).app U
  let p' : H.obj U' := H.map a p
  let q' : H.obj U' := H.map a q
  have hcomm : Commute p' q' := by
    let x := b.symm p'
    let y := b.symm q'
    have hxy : Commute x y := by
      change x * y = y * x
      apply (ConcreteCategory.bijective_of_isIso ψ.hom).1
      let ψ₀ : F.obj U →* (ULift.{u} (Fin r) → Uˣ) := ψ.hom.hom
      change ψ₀ (x * y) = ψ₀ (y * x)
      rw [map_mul, map_mul]
      exact mul_comm _ _
    have hc : Commute (b x) (b y) := hxy.map b.toMonoidHom
    change Commute (b (b.symm p')) (b (b.symm q')) at hc
    simpa only [MulEquiv.apply_symm_apply] using hc
  have hnat (x : Points S.X R) : ap (m.app R x) = m.app U' (H.map a x) :=
    DFunLike.congr_fun (congrArg GrpCat.Hom.hom (m.naturality a).symm) x
  change (m.app R p) * (m.app R q) = (m.app R q) * (m.app R p)
  apply hap
  rw [map_mul, map_mul, hnat p, hnat q]
  exact (hcomm.map (m.app U').hom).eq

private theorem inclusionPoints_injective {G : GroupScheme k} (T : ClosedSubgroup G)
    (R : TestAlgebra k) :
    Function.Injective (((groupPointsFunctor k).map T.inclusion).app R) := by
  have hc := T.isClosedImmersion
  have hm : Mono T.inclusion.hom.hom :=
    (Over.forget _).mono_of_mono_map (f := T.inclusion.hom.hom)
      (inferInstanceAs (Mono T.inclusion.hom.hom.left))
  intro x y h
  exact (cancel_mono T.inclusion.hom.hom).mp h

private theorem diagonal_isOwnSchemeCentralizer {G : GroupScheme k}
    (c : (groupPointsFunctor k).obj G ≅ symplecticPoints k ι)
    (T : ClosedSubgroup G)
    (d : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k ι)
    (hd : ∀ (R : TestAlgebra k) (t : ι → Rˣ),
      (show PointGroup ι R from
        c.hom.app R (((groupPointsFunctor k).map T.inclusion).app R (d.inv.app R t))).val =
          hyperbolicDiagonal t) :
    IsOwnSchemeCentralizer T := by
  let P := (groupPointsFunctor k).obj G
  let Q := (groupPointsFunctor k).obj T.group
  let j := (groupPointsFunctor k).map T.inclusion
  intro R p
  let cR : P.obj R →* PointGroup ι R := (c.hom.app R).hom
  constructor
  · intro h
    have hc : CentralizesDiagonal (cR p).val := by
      intro S _ f t
      let : Algebra k S := (f.comp (algebraMap k R)).toAlgebra
      let U := CommAlgCat.of k S
      let a : R ⟶ U := CommAlgCat.ofHom { toRingHom := f, commutes' := fun _ => rfl }
      let q : Q.obj U := d.inv.app U t
      let cU : P.obj U →* PointGroup ι U := (c.hom.app U).hom
      have hnat : (cU (P.map a p)).val = (cR p).val.map f :=
        congrArg Subtype.val (DFunLike.congr_fun (congrArg GrpCat.Hom.hom (c.hom.naturality a)) p)
      have hdiag : (cU (j.app U q)).val = hyperbolicDiagonal t := hd U t
      have he := congrArg Subtype.val ((h U a q).map cU).eq
      change (cU (P.map a p)).val * (cU (j.app U q)).val =
        (cU (j.app U q)).val * (cU (P.map a p)).val at he
      rw [hnat, hdiag] at he
      exact he
    obtain ⟨t, ht⟩ := (diagonalCentralizer ι R (cR p)).mp hc
    refine ⟨d.inv.app R t, (ConcreteCategory.bijective_of_isIso (c.hom.app R)).1 ?_⟩
    exact Subtype.ext ((hd R t).trans ht.symm)
  · rintro ⟨q, rfl⟩ S a t
    have hcomm : Commute (Q.map a q) t := by
      change (Q.map a q) * t = t * (Q.map a q)
      apply (ConcreteCategory.bijective_of_isIso (d.hom.app S)).1
      let f : Q.obj S →* (ι → Sˣ) := (d.hom.app S).hom
      change f ((Q.map a q) * t) = f (t * (Q.map a q))
      rw [map_mul, map_mul, mul_comm]
    have hn : j.app S (Q.map a q) = P.map a (j.app R q) :=
      DFunLike.congr_fun (congrArg GrpCat.Hom.hom (j.naturality a)) q
    change Commute (P.map a (j.app R q)) (j.app S t)
    rw [← hn]
    exact hcomm.map (j.app S).hom

private theorem diagonal_isMaximalTorus {G : AffineAlgebraicGroup k}
    (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k ι)
    (T : ClosedSubgroup G.val)
    (d : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k ι)
    (hd : ∀ (R : TestAlgebra k) (t : ι → Rˣ),
      (show PointGroup ι R from
        c.hom.app R (((groupPointsFunctor k).map T.inclusion).app R (d.inv.app R t))).val =
          hyperbolicDiagonal t) :
    GeometricRadicals.IsMaximalTorus T := by
  constructor
  · let ix : ι ≃ ULift.{u} (Fin (Fintype.card ι)) :=
      (Fintype.equivFin ι).trans Equiv.ulift.symm
    let T' := Specs.Unipotent.baseChangedAlgebraicGroup k
      (Specs.Unipotent.closedSubgroupAlgebraicGroup T)
    refine ⟨k, inferInstance, inferInstance, inferInstance, Fintype.card ι, ?_⟩
    exact ⟨groupIsoOfPoints (G := T') (baseChangePowerPointsIso (K := k) d ≪≫
      reindexPowerPoints ix ≪≫ (StandardGroups.multiplicativePowerGroupPointsIso k _).symm)⟩
  · intro S hS hTS
    obtain ⟨i, hi⟩ := hTS
    let j := (groupPointsFunctor k).map T.inclusion
    let P := (groupPointsFunctor k).obj G.val
    let H := (groupPointsFunctor k).obj S.group
    let iS := (groupPointsFunctor k).map S.inclusion
    let iT := (groupPointsFunctor k).map i
    have hfactor (R : TestAlgebra k) (p : H.obj R) :
        ∃ q : ((groupPointsFunctor k).obj T.group).obj R, j.app R q = iS.app R p := by
      apply (diagonal_isOwnSchemeCentralizer c T d hd R (iS.app R p)).mp
      intro U a q
      have hp : iS.app U (H.map a p) = P.map a (iS.app R p) :=
        DFunLike.congr_fun (congrArg GrpCat.Hom.hom (iS.naturality a)) p
      have hq : iS.app U (iT.app U q) = j.app U q := by
        have he := congrArg (fun f : T.group ⟶ G.val => (groupPointsFunctor k).map f) hi
        rw [Functor.map_comp] at he
        exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom
          (congrArg (fun f => f.app U) he)) q
      change Commute (P.map a (iS.app R p)) (j.app U q)
      rw [← hp, ← hq]
      change _ * _ = _ * _
      apply (ConcreteCategory.bijective_of_isIso (c.hom.app U)).1
      rw [map_mul, map_mul]
      exact (torusImageCommutes c S.inclusion hS U (H.map a p) (iT.app U q)).eq
    let L := (groupPointsFunctor k).obj T.group
    let liftPoint (R : TestAlgebra k) (p : H.obj R) : L.obj R := Classical.choose (hfactor R p)
    have hlift (R : TestAlgebra k) (p : H.obj R) :
        j.app R (liftPoint R p) = ((groupPointsFunctor k).map S.inclusion).app R p :=
      Classical.choose_spec (hfactor R p)
    let liftHom (R : TestAlgebra k) : H.obj R →* L.obj R := by
      let jR : L.obj R →* ((groupPointsFunctor k).obj G.val).obj R := (j.app R).hom
      let iR : H.obj R →* ((groupPointsFunctor k).obj G.val).obj R :=
        (((groupPointsFunctor k).map S.inclusion).app R).hom
      have hh (p : H.obj R) : jR (liftPoint R p) = iR p := hlift R p
      refine { toFun := liftPoint R, map_one' := ?_, map_mul' := ?_ }
      · apply inclusionPoints_injective T R
        change jR (liftPoint R 1) = jR 1
        rw [hh, map_one, map_one]
      · intro x y
        apply inclusionPoints_injective T R
        change jR (liftPoint R (x * y)) = jR (liftPoint R x * liftPoint R y)
        rw [hh, map_mul jR, hh, hh, map_mul iR]
    let f : (groupPointsFunctor k).obj S.group ⟶ (groupPointsFunctor k).obj T.group :=
      { app R := ConcreteCategory.ofHom (X := H.obj R) (Y := L.obj R) (liftHom R)
        naturality R U a := by
          apply GrpCat.ext
          intro p
          apply inclusionPoints_injective T U
          change j.app U (liftPoint U (H.map a p)) = j.app U (L.map a (liftPoint R p))
          have hSmap := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (iS.naturality a)) p
          have hTmap := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (j.naturality a))
            (liftPoint R p)
          have h := congrArg (P.map a).hom (hlift R p).symm
          exact (hlift U (H.map a p)).trans (hSmap.trans (h.trans hTmap.symm)) }
    let S' := Specs.Unipotent.closedSubgroupAlgebraicGroup S
    let e := groupHomEquiv S.group T.group S'.property.1
    refine ⟨e.symm f, ?_⟩
    apply (groupHomComparison k S.group G.val S'.property.1).1
    change (groupPointsFunctor k).map (e.symm f ≫ T.inclusion) =
      (groupPointsFunctor k).map S.inclusion
    rw [Functor.map_comp, show (groupPointsFunctor k).map (e.symm f) = f from e.apply_symm_apply f]
    apply NatTrans.ext
    funext R
    apply GrpCat.ext
    intro p
    change j.app R (liftPoint R p) = _
    exact hlift R p

/-- The hyperbolic diagonal is a split torus of rank n and remains maximal over the algebraic closure. -/
theorem diagonalTorus : DiagonalTorus.{u} := by
  intro k ι _ _ _ G c
  obtain ⟨T, d, hrank, hd⟩ := diagonalTorusEmbedding k ι G c
  refine ⟨T, d, hrank, hd, diagonal_isOwnSchemeCentralizer c T d hd, ?_⟩
  let K := AlgebraicClosure k
  have hclosed : IsClosedImmersion ((groupBaseChange k K).map T.inclusion).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) (fieldSpecMap k K)
      T.inclusion.hom.hom T.isClosedImmersion
  refine ⟨hclosed, ?_⟩
  let G' := Specs.Unipotent.baseChangedAlgebraicGroup K G
  let T' := GeometricRadicals.baseChangedSubgroup K T hclosed
  exact diagonal_isMaximalTorus (G := G') (baseChangeSymplecticPointsIso K c) T'
    (baseChangePowerPointsIso d) (baseChange_diagonal_points c T d hd)

end MaximalTorus

section Reductivity

open WithConv LinearAlgebraicGroups.RationalRepresentations Specs.RationalRepresentations
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped TensorProduct

open private pointMatrix pointMatrix_evaluation pointMatrix_isCoactionMatrix
  from LinearAlgebraicGroups.Affine.RationalRepresentations
open private trivial_of_subsingleton_sections from LinearAlgebraicGroups.Reductive.GeometricRadicals

private def naturalMatrixRepresentation :
    symplecticPoints k ι ⟶ generalLinearPoints k (Indices ι) where
  app R := GrpCat.ofHom toGeneralLinear
  naturality _ _ _ := by
    apply GrpCat.ext
    intro g
    exact Matrix.GeneralLinearGroup.ext (fun _ _ => rfl)

private theorem invariantVector [Nonempty ι] {H : AffineAlgebraicGroup k}
    (hH : Specs.Unipotent.IsUnipotent H)
    (m : (groupPointsFunctor k).obj H.val ⟶ symplecticPoints k ι) :
    ∃ v : Indices ι → k, v ≠ 0 ∧ ∀ p : Points H.val.X (CommAlgCat.of k k),
      ((show PointGroup ι k from m.app (CommAlgCat.of k k) p).val *ᵥ v) = v := by
  obtain ⟨A, ⟨e⟩, hinv⟩ := hH
  let i : convolutionPoints A ≅ (groupPointsFunctor k).obj H.val :=
    hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso e
  let α := i.hom ≫ m ≫ naturalMatrixRepresentation
  let M := pointMatrix A α
  let b := Pi.basisFun k (Indices ι)
  let ρ := coactionOfMatrix A b M (pointMatrix_isCoactionMatrix A α)
  obtain ⟨v, hv, hf⟩ := hinv (Indices ι → k) ρ
  refine ⟨v, hv, ?_⟩
  let R := CommAlgCat.of k k
  intro p
  let q := i.inv.app R p
  have hp : i.hom.app R q = p :=
    DFunLike.congr_fun (congrArg GrpCat.Hom.hom (Iso.inv_hom_id_app i R)) p
  let g : A →ₐ[k] k := q.ofConv
  let T := (TensorProduct.rid k (Indices ι → k)).toLinearMap
  have hE :
      T.comp (evaluate A ρ g) = (g.mapMatrix M).mulVecLin := by
    apply b.ext
    intro j
    have hc := coaction_apply_basis A b ρ j
    rw [coefficients_coactionOfMatrix] at hc
    change T ((LinearMap.lTensor _ g.toLinearMap) (ρ.coaction (b j))) =
      (g.mapMatrix M) *ᵥ (b j)
    rw [hc, map_sum, map_sum]
    ext a
    simp [T, b, Matrix.col_apply, Pi.single_apply]
  have hmatrix := pointMatrix_evaluation A α R q
  change (show PointGroup ι k from m.app R (i.hom.app R q)).val = g.mapMatrix M at hmatrix
  rw [hp] at hmatrix
  rw [hmatrix]
  change ((g.mapMatrix M).mulVecLin) v = v
  rw [← hE, LinearMap.comp_apply, (invariantKernel A ρ v).mpr hf R g]
  exact (TensorProduct.rid_tmul v (1 : k)).trans (one_smul k v)

private theorem trivialNormalSubgroup [IsAlgClosed k] [Nonempty ι]
    {G : AffineAlgebraicGroup k} (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k ι)
    (N : ClosedSubgroup G.val) (hN : GeometricRadicals.IsSmoothConnectedNormal N)
    (hu : Specs.Unipotent.IsUnipotent (Specs.Unipotent.closedSubgroupAlgebraicGroup N)) :
    GeometricRadicals.IsTrivialSubgroup N := by
  let R := CommAlgCat.of k k
  let m := (groupPointsFunctor k).map N.inclusion ≫ c.hom
  let P := ((groupPointsFunctor k).obj N.group).obj R
  let Q := ((groupPointsFunctor k).obj G.val).obj R
  let imagePoint : P →* PointGroup ι k := (m.app R).hom
  obtain ⟨v, hv, hf⟩ := invariantVector hu m
  have hmatrix (p : Points N.group.X R) : (imagePoint p).val = 1 := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [Matrix.one_mulVec]
    let x : Indices ι → k := Pi.single j 1
    have hx : x ≠ 0 := by
      intro h
      exact (one_ne_zero : (1 : k) ≠ 0) (by simpa [x] using congrFun h j)
    obtain ⟨g, hg⟩ := transitiveNaturalAction k ι hv hx
    let s : Q := c.inv.app R g⁻¹
    let cR : Q →* PointGroup ι k := (c.hom.app R).hom
    have hs : cR s = g⁻¹ :=
      DFunLike.congr_fun (congrArg GrpCat.Hom.hom (Iso.inv_hom_id_app c R)) _
    obtain ⟨p', hp'⟩ := LinearAlgebraicGroups.normalSubgroup_conjugate_sections
      hN.2.2 s p
    have hconj : imagePoint p' = g⁻¹ * imagePoint p * g := by
      have h := congrArg cR hp'
      change imagePoint p' = cR (s * (show Q from p ≫ N.inclusion.hom.hom) * s⁻¹) at h
      rw [map_mul, map_mul, map_inv, hs, inv_inv] at h
      exact h
    have hmul : imagePoint p * g = g * imagePoint p' := by
      rw [hconj, ← mul_assoc g, ← mul_assoc g, mul_inv_cancel, one_mul]
    change (imagePoint p).val *ᵥ x = x
    conv_lhs => rw [← hg, Matrix.mulVec_mulVec]
    change (imagePoint p * g).val *ᵥ v = x
    rw [hmul]
    change (g.val * (imagePoint p').val) *ᵥ v = x
    have hfixed : (imagePoint p').val *ᵥ v = v := hf p'
    rw [← Matrix.mulVec_mulVec, hfixed, hg]
  have hmono : Mono N.inclusion.hom.hom := by
    have hci := N.isClosedImmersion
    exact (Over.forget _).mono_of_mono_map (f := N.inclusion.hom.hom)
      (inferInstanceAs (Mono N.inclusion.hom.hom.left))
  have hpq (p q : Points N.group.X R) : p = q := by
    apply (cancel_mono N.inclusion.hom.hom).mp
    apply (ConcreteCategory.bijective_of_isIso (c.hom.app R)).1
    exact Subtype.ext ((hmatrix p).trans (hmatrix q).symm)
  let Y := (testSpec k).obj (op R)
  let t : Y ⟶ 𝟙_ (SchemeOver k) := toUnit Y
  have ht : IsIso t := by
    have h : t.left = Y.hom := by
      have e := t.w
      change t.left ≫ 𝟙 _ = Y.hom at e
      simpa using e
    have hid : CommRingCat.ofHom (algebraMap k k) = 𝟙 (CommRingCat.of k) := by
      apply CommRingCat.hom_ext
      exact Algebra.algebraMap_self
    have : IsIso ((Over.forget (Spec (CommRingCat.of k))).map t) := by
      change IsIso t.left
      rw [h]
      change IsIso (Spec.map (CommRingCat.ofHom (algebraMap k k)))
      rw [hid]
      exact Spec.map_id _ ▸ inferInstanceAs (IsIso (𝟙 _))
    exact isIso_of_reflects_iso t (Over.forget _)
  have hsingle : Subsingleton ((𝟙_ (SchemeOver k)) ⟶ N.group.X) :=
    ⟨fun p q => (cancel_epi t).mp (hpq (t ≫ p) (t ≫ q))⟩
  exact @trivial_of_subsingleton_sections _ _ _ (Specs.Unipotent.closedSubgroupAlgebraicGroup N)
    hN.1 hsingle

theorem reductivity : Specs.SymplecticMatrixStructure.Reductivity.{u} := by
  intro k ι _ _ _ _ G hG
  obtain ⟨c⟩ := hG
  let S := symplecticGroup k ι
  let e : G.val ≅ S.val := groupIsoOfPoints (c ≪≫ (symplecticGroupPointsIso k ι).symm)
  let f := (Grp.forget (SchemeOver k)).map e.hom
  have hf : IsIso f.left := by
    change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget (Spec (CommRingCat.of k))).map e.hom)
    infer_instance
  have hw : f.left ≫ S.val.X.hom = G.val.X.hom := f.w
  refine ⟨?_, ?_, ?_⟩
  · rw [← hw]
    have hres : MorphismProperty.Respects (@AlgebraicGeometry.Smooth.{u}) @IsOpenImmersion :=
      inferInstance
    exact hres.toRespectsLeft.precomp f.left inferInstance _ (smoothness k ι)
  · rw [← hw]
    have : MorphismProperty.RespectsIso @GeometricallyConnected := by
      rw [GeometricallyConnected.eq_geometrically]
      infer_instance
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected f.left _).mpr
      (geometricConnectedness k ι)
  · let N := GeometricRadicals.geometricUnipotentRadical G
    have h := LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest G
    exact trivialNormalSubgroup (baseChangeSymplecticPointsIso (AlgebraicClosure k) c) N h.1 h.2.1

end Reductivity

end
end LinearAlgebraicGroups.SymplecticMatrixStructure
