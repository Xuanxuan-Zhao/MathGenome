import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalMixingQuadraticSpinRankOne
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj Matrix TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.LocalMixingQuadraticSpinRankOne

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme SubgroupSections)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Arithmetic.LocalMixingQuadraticSpinRankOne
open Specs.Arithmetic.IsotropicSpinGeneration (HyperbolicPair)
open Specs.CharacterDescent (Cocharacter)
open LinearAlgebraicGroups.Albert.SpinSpecification
open CocharacterDynamics

open private testPointSections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private rationalSourceIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalDensity

noncomputable section

set_option backward.isDefEq.respectTransparency false

private theorem localField_infinite (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : Infinite F := by
  obtain ⟨value, hpos, hlt⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := F)
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective value
  apply Infinite.of_injective (fun n : ℕ => x ^ n)
  intro m n h
  apply (pow_right_strictAnti₀ hpos hlt).injective
  simpa only [map_pow, hx] using congrArg (ValuativeRel.valuation F) h

section RationalPoints

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}

local notation "R₀" => CommAlgCat.of F F

private theorem rationalContractingSections (c : Cocharacter G.val) (D : LimitDecomposition c) :
    (testPointSections G.val).symm '' (SubgroupSections D.contracting (𝟙_ (SchemeOver F)) :
      Set (𝟙_ (SchemeOver F) ⟶ G.val.X)) =
    {g : GroupPoints G.val R₀ | HasLimit c g 1} := by
  ext g
  change (∃ p ∈ SubgroupSections D.contracting (𝟙_ (SchemeOver F)),
    (testPointSections G.val).symm p = g) ↔ HasLimit c g 1
  refine Iff.trans ?_ (D.contracting_points R₀ g).symm
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    refine ⟨(testPointSections D.contracting.group).symm s, ?_⟩
    change (((rationalSourceIso F).inv ≫ s) ≫ D.contracting.inclusion.hom.hom) =
      (rationalSourceIso F).inv ≫ (s ≫ D.contracting.inclusion.hom.hom)
    exact Category.assoc _ _ _
  · rintro ⟨s, rfl⟩
    let p := testPointSections D.contracting.group s
    refine ⟨p ≫ D.contracting.inclusion.hom.hom, ⟨p, rfl⟩, ?_⟩
    change (rationalSourceIso F).inv ≫
        ((rationalSourceIso F).hom ≫ s) ≫ D.contracting.inclusion.hom.hom =
      s ≫ D.contracting.inclusion.hom.hom
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ D.contracting.inclusion.hom.hom)
        ((testPointSections D.contracting.group).left_inv s))

private theorem oppositeLimits_generate (d : Cocharacter G.val)
    (hgen : ∀ (D : LimitDecomposition d) (E : LimitDecomposition (oppositeCocharacter d)),
      SubgroupSections D.contracting (𝟙_ (SchemeOver F)) ⊔
        SubgroupSections E.contracting (𝟙_ (SchemeOver F)) = ⊤) :
    Subgroup.closure ({g : GroupPoints G.val R₀ | HasLimit d g 1} ∪
      {g : GroupPoints G.val R₀ | HasLimit (oppositeCocharacter d) g 1}) = ⊤ := by
  obtain ⟨D⟩ := existsLimitDecomposition G d
  obtain ⟨E⟩ := existsLimitDecomposition G (oppositeCocharacter d)
  let e := (testPointSections G.val).symm
  rw [← rationalContractingSections d D, ← rationalContractingSections (oppositeCocharacter d) E]
  change Subgroup.closure
      ((↑((SubgroupSections D.contracting (𝟙_ (SchemeOver F))).map e.toMonoidHom) :
        Set (GroupPoints G.val R₀)) ∪
        ↑((SubgroupSections E.contracting (𝟙_ (SchemeOver F))).map e.toMonoidHom)) = ⊤
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, ← Subgroup.map_sup,
    hgen D E, Subgroup.map_top_of_surjective _ e.surjective]

end RationalPoints

section MatrixUnits

variable {R C : Type u} [CommRing R] [Ring C] [Algebra R C]

/-- A square-zero pair with anticommutator one determines a unital
representation of the two-by-two matrix algebra. -/
private def pairMatrix (x y : C) (M : Matrix (Fin 2) (Fin 2) R) : C :=
  M 0 0 • (x * y) + M 0 1 • x + M 1 0 • y + M 1 1 • (y * x)

private def pairMatrixAlgHom {x y : C} (hxx : x * x = 0) (hyy : y * y = 0)
    (hsum : x * y + y * x = 1) :
    Matrix (Fin 2) (Fin 2) R →ₐ[R] C where
  toFun := pairMatrix x y
  map_one' := by
    simpa [pairMatrix, Matrix.one_apply] using hsum
  map_add' M N := by
    simp only [pairMatrix, Matrix.add_apply, add_smul]
    abel
  map_zero' := by simp [pairMatrix]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simpa [pairMatrix, Matrix.smul_apply, Matrix.one_apply, ← smul_add] using
      congrArg (r • ·) hsum
  map_mul' M N := by
    have hxyx : x * y * x = x := by
      have he := congrArg (x * ·) hsum
      rwa [mul_add, ← mul_assoc x x y, hxx, zero_mul, zero_add,
        ← mul_assoc x y x, mul_one] at he
    have hyxy : y * x * y = y := by
      have he := congrArg (· * y) hsum
      rwa [add_mul, mul_assoc x y y, hyy, mul_zero, zero_add, one_mul] at he
    have h₁ : (x * y) * (x * y) = x * y := by rw [← mul_assoc, hxyx]
    have h₂ : (y * x) * (y * x) = y * x := by rw [← mul_assoc, hyxy]
    have h₃ : (x * y) * y = 0 := by rw [mul_assoc, hyy, mul_zero]
    have h₄ : (y * x) * x = 0 := by rw [mul_assoc, hxx, mul_zero]
    have h₅ : x * (x * y) = 0 := by rw [← mul_assoc, hxx, zero_mul]
    have h₆ : y * (y * x) = 0 := by rw [← mul_assoc, hyy, zero_mul]
    have h₇ : x * (y * x) = x := by rw [← mul_assoc, hxyx]
    have h₈ : y * (x * y) = y := by rw [← mul_assoc, hyxy]
    have hcross : (x * y) * (y * x) = 0 := by rw [← mul_assoc, h₃, zero_mul]
    have hcross' : (y * x) * (x * y) = 0 := by rw [← mul_assoc, h₄, zero_mul]
    simp only [pairMatrix, Matrix.mul_apply, Fin.sum_univ_two, mul_add, add_mul,
      smul_mul_assoc, mul_smul_comm, smul_smul, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈,
      hxx, hyy, hxyx, hyxy, hcross, hcross', smul_zero, zero_add, add_zero,
      add_smul, smul_add, mul_comm (N _ _) (M _ _)]
    abel

/-- A representation of a matrix algebra is faithful as soon as its scalar map is. -/
private theorem matrixAlgHom_injective {idx : Type u} [Fintype idx] [DecidableEq idx]
    (φ : Matrix idx idx R →ₐ[R] C) (hscalar : Function.Injective (algebraMap R C)) :
    Function.Injective φ := by
  intro M N heq
  ext i j
  have sandwich (P : Matrix idx idx R) (t : idx) :
      Matrix.single t i 1 * P * Matrix.single j t 1 = Matrix.single t t (P i j) := by
    ext a b
    by_cases hb : b = t
    · subst b
      rw [Matrix.mul_single_apply_same]
      by_cases ha : a = t
      · subst a
        simp only [Matrix.single_mul_apply_same, Matrix.single_apply_same, one_mul, mul_one]
      · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ ha,
          Matrix.single_apply_of_row_ne (Ne.symm ha), zero_mul]
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hb]
      simp [Ne.symm hb]
  have extract (P : Matrix idx idx R) :
      φ (algebraMap R (Matrix idx idx R) (P i j)) =
        ∑ t, φ (Matrix.single t i 1) * φ P * φ (Matrix.single j t 1) := by
    simp_rw [← map_mul, sandwich, ← map_sum, Matrix.sum_single_eq_diagonal]
    congr 1
  exact hscalar (by rw [← φ.commutes, ← φ.commutes, extract, extract, heq])

end MatrixUnits

section CliffordConjugation

variable {R C : Type u} [CommRing R] [Ring C] [Algebra R C]

private def fourEntries (e f z : C) (a b c d : R) : C :=
  a • (e * f) + b • (e * z) + c • (f * z) + d • (f * e)

/-- Clifford relations for a hyperbolic pair and one perpendicular vector. -/
private structure TripleRelations (e f z : C) (m : R) : Prop where
  ee : e * e = 0
  ff : f * f = 0
  sum : e * f + f * e = 1
  ze : z * e = -(e * z)
  zf : z * f = -(f * z)
  zz : z * z = m • 1

variable {e f z : C} {m : R} (rel : TripleRelations e f z m)

include rel

private theorem TripleRelations.swap : TripleRelations f e z m :=
  ⟨rel.ff, rel.ee, (add_comm ..).trans rel.sum, rel.zf, rel.ze, rel.zz⟩

private theorem TripleRelations.efe : e * f * e = e := by
  have he := congrArg (· * e) rel.sum
  rwa [add_mul, mul_assoc f e e, rel.ee, mul_zero, add_zero, one_mul] at he

omit rel in
private theorem fourEntries_swap (a b c d : R) :
    fourEntries f e z d c b a = fourEntries e f z a b c d := by
  unfold fourEntries
  abel

private theorem TripleRelations.right_e (a b c d : R) :
    e * fourEntries e f z a b c d = d • e + c • (e * f * z) := by
  have h₁ : e * (e * f) = 0 := by rw [← mul_assoc, rel.ee, zero_mul]
  have h₂ : e * (e * z) = 0 := by rw [← mul_assoc, rel.ee, zero_mul]
  have h₃ : e * (f * e) = e := by rw [← mul_assoc, rel.efe]
  simp only [fourEntries, mul_add, mul_smul_comm, h₁, h₂, h₃, smul_zero, zero_add,
    ← mul_assoc e f z]
  abel

private theorem TripleRelations.left_e (a b c d : R) :
    fourEntries e f z a b c d * e = a • e - c • (f * e * z) := by
  have h₁ : e * z * e = 0 := by rw [mul_assoc, rel.ze, mul_neg, ← mul_assoc, rel.ee, zero_mul, neg_zero]
  have h₂ : f * z * e = -(f * e * z) := by rw [mul_assoc, rel.ze, mul_neg, ← mul_assoc]
  have h₃ : f * e * e = 0 := by rw [mul_assoc, rel.ee, mul_zero]
  simp only [fourEntries, add_mul, smul_mul_assoc, rel.efe, h₁, h₂, h₃,
    smul_zero, add_zero, smul_neg, sub_eq_add_neg]

private theorem TripleRelations.right_fez (a b c d : R) :
    (f * e * z) * fourEntries e f z a b c d = d • (f * e * z) - (c * m) • f := by
  have h₁ : (f * e * z) * (e * f) = 0 := by
    calc
      _ = f * e * (z * e) * f := by noncomm_ring
      _ = -(f * (e * e) * z * f) := by rw [rel.ze]; noncomm_ring
      _ = 0 := by simp [rel.ee]
  have h₂ : (f * e * z) * (e * z) = 0 := by
    calc
      _ = f * e * (z * e) * z := by noncomm_ring
      _ = -(f * (e * e) * z * z) := by rw [rel.ze]; noncomm_ring
      _ = 0 := by simp [rel.ee]
  have h₃ : (f * e * z) * (f * z) = -(m • f) := by
    calc
      _ = f * e * (z * f) * z := by noncomm_ring
      _ = -((f * e * f) * (z * z)) := by rw [rel.zf]; noncomm_ring
      _ = _ := by rw [rel.swap.efe, rel.zz, mul_smul_comm, mul_one]
  have h₄ : (f * e * z) * (f * e) = f * e * z := by
    calc
      _ = f * e * (z * f) * e := by noncomm_ring
      _ = -((f * e * f) * (z * e)) := by rw [rel.zf]; noncomm_ring
      _ = f * e * z := by rw [rel.swap.efe, rel.ze, mul_neg, neg_neg, ← mul_assoc]
  simp only [fourEntries, mul_add, mul_smul_comm, h₁, h₂, h₃, h₄, smul_zero, zero_add,
    smul_neg, smul_smul, sub_eq_add_neg]
  abel

private theorem TripleRelations.conjugates_e (a b c d : R) :
    fourEntries e f z a b c d * e * fourEntries e f z d (-b) (-c) a =
      a ^ 2 • e - (c ^ 2 * m) • f - (a * c) • z := by
  rw [rel.left_e, sub_mul, smul_mul_assoc, smul_mul_assoc, rel.right_e, rel.right_fez]
  have hz : e * f * z + f * e * z = z := by rw [← add_mul, rel.sum, one_mul]
  calc
    _ = a ^ 2 • e - (c ^ 2 * m) • f - (a * c) • (e * f * z + f * e * z) := by module
    _ = _ := by rw [hz]

private theorem TripleRelations.conjugates_f (a b c d : R) :
    fourEntries e f z a b c d * f * fourEntries e f z d (-b) (-c) a =
      d ^ 2 • f - (b ^ 2 * m) • e - (d * b) • z := by
  simpa only [fourEntries_swap] using rel.swap.conjugates_e d c b a

private theorem TripleRelations.conjugates_perpendicular (a b c d k : R) (v : C)
    (he : v * e = -(e * v)) (hf : v * f = -(f * v)) (hz : z * v + v * z = k • 1)
    (hnorm : fourEntries e f z a b c d * fourEntries e f z d (-b) (-c) a = 1) :
    fourEntries e f z a b c d * v * fourEntries e f z d (-b) (-c) a =
      v + (k * a * b) • e + (k * c * d) • f - (k * b * c) • z := by
  let A := fourEntries e f z a b c d
  let A' := fourEntries e f z d (-b) (-c) a
  have h₁ : e * f * v = v * (e * f) := by
    calc
      _ = -(e * (v * f)) := by rw [hf]; noncomm_ring
      _ = _ := by rw [← mul_assoc v e f, he]; noncomm_ring
  have h₂ : f * e * v = v * (f * e) := by
    calc
      _ = -(f * (v * e)) := by rw [he]; noncomm_ring
      _ = _ := by rw [← mul_assoc v f e, hf]; noncomm_ring
  have h₃ : e * z * v = v * (e * z) + k • e := by
    rw [mul_assoc, eq_sub_of_add_eq hz, mul_sub, mul_smul_comm, mul_one]
    rw [← mul_assoc v e z, he]
    noncomm_ring
  have h₄ : f * z * v = v * (f * z) + k • f := by
    rw [mul_assoc, eq_sub_of_add_eq hz, mul_sub, mul_smul_comm, mul_one]
    rw [← mul_assoc v f z, hf]
    noncomm_ring
  have hv : A * v = v * A + (k * b) • e + (k * c) • f := by
    simp only [A, fourEntries, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      h₁, h₂, h₃, h₄]
    module
  have hf' : f * A' = d • f + (-b) • (f * e * z) := by
    simpa only [A', fourEntries_swap] using rel.swap.right_e a (-c) (-b) d
  have he' : e * A' = a • e + (-c) • (e * f * z) := rel.right_e d (-b) (-c) a
  have hsum : e * f * z + f * e * z = z := by rw [← add_mul, rel.sum, one_mul]
  change A * v * A' = _
  rw [hv, add_mul, add_mul, mul_assoc v A A', hnorm, mul_one, smul_mul_assoc,
    smul_mul_assoc, he', hf']
  calc
    _ = v + (k * a * b) • e + (k * c * d) • f -
      (k * b * c) • (e * f * z + f * e * z) := by module
    _ = _ := by rw [hsum]

end CliffordConjugation

section CliffordMatrix

open Specs.Arithmetic.SpinHyperbolicDynamics (vectorOver)
open private vector_square vector_swap orthogonal_vector_swap form_over polar_over
  change_vector change_vectorOver
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SpinHyperbolicDynamics

variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (q : QuadraticForm F V) (h : HyperbolicPair q) (w : h.perpendicular)
variable {I : Type u} [LinearOrder I] (b : Module.Basis I F V)
variable (R : TestAlgebra F)

private abbrev eVector : ScalarClifford q R := vectors q R (vectorOver R h.e)
private abbrev fVector : ScalarClifford q R := vectors q R (vectorOver R h.f)
private abbrev wVector : ScalarClifford q R := vectors q R (vectorOver R w.val)

private abbrev upperUnit : ScalarClifford q R := eVector q h R * wVector q h w R
private abbrev lowerUnit : ScalarClifford q R :=
  -(algebraMap F R ((q w.val)⁻¹)) • (fVector q h R * wVector q h w R)

include b in
private theorem cliffordTriple :
    TripleRelations (eVector q h R) (fVector q h R) (wVector q h w R)
      (algebraMap F R (q w.val)) := by
  let e := eVector q h R
  let f := fVector q h R
  let z := wVector q h w R
  let m : R := algebraMap F R (q w.val)
  have hew : q.polarBilin h.e w.val = 0 := w.property.1
  have hfw : q.polarBilin h.f w.val = 0 := w.property.2
  have he : e * e = 0 := by
    change vectors q R (vectorOver R h.e) * _ = _
    rw [vector_square q b, form_over, h.q_e, map_zero, map_zero]
  have hf : f * f = 0 := by
    change vectors q R (vectorOver R h.f) * _ = _
    rw [vector_square q b, form_over, h.q_f, map_zero, map_zero]
  have hz : z * z = m • 1 := by
    change vectors q R (vectorOver R w.val) * _ = _
    rw [vector_square q b, form_over, Algebra.algebraMap_eq_smul_one]
  have hze : z * e = -(e * z) :=
    orthogonal_vector_swap q b R _ _ (by rw [polar_over, hew, map_zero])
  have hzf : z * f = -(f * z) :=
    orthogonal_vector_swap q b R _ _ (by rw [polar_over, hfw, map_zero])
  refine ⟨he, hf, ?_, hze, hzf, hz⟩
  change vectors q R (vectorOver R h.e) * vectors q R (vectorOver R h.f) + _ = _
  rw [vector_swap q b, polar_over, h.polar_ef, map_one, map_one]

include b in
private theorem matrixUnitProducts (hw : q w.val ≠ 0) :
    let e := eVector q h R
    let f := fVector q h R
    let x := upperUnit q h w R
    let y := lowerUnit q h w R
    x * x = 0 ∧ y * y = 0 ∧ x * y = e * f ∧ y * x = f * e ∧ e * f + f * e = 1 := by
  let e := eVector q h R
  let f := fVector q h R
  let z := wVector q h w R
  let m : R := algebraMap F R (q w.val)
  let i : R := algebraMap F R ((q w.val)⁻¹)
  have him : i * m = 1 := by
    dsimp only [i, m]
    rw [← map_mul, inv_mul_cancel₀ hw, map_one]
  have rel := cliffordTriple q h w b R
  have he : e * e = 0 := rel.ee
  have hf : f * f = 0 := rel.ff
  have hz : z * z = m • 1 := rel.zz
  have hze : z * e = -(e * z) := rel.ze
  have hzf : z * f = -(f * z) := rel.zf
  have sq {v : ScalarClifford q R} (hv : v * v = 0) (hvz : z * v = -(v * z)) :
      (v * z) * (v * z) = 0 := by
    calc
      _ = (v * (z * v)) * z := by noncomm_ring
      _ = -(v * v) * (z * z) := by rw [hvz]; noncomm_ring
      _ = 0 := by rw [hv, neg_zero, zero_mul]
  have prod {v v' : ScalarClifford q R} (hv'z : z * v' = -(v' * z)) :
      (v * z) * (v' * z) = -(m • (v * v')) := by
    calc
      _ = (v * (z * v')) * z := by noncomm_ring
      _ = -((v * v') * (z * z)) := by rw [hv'z]; noncomm_ring
      _ = _ := by rw [hz, mul_smul_comm, mul_one]
  change (e * z) * (e * z) = 0 ∧ ((-i) • (f * z)) * ((-i) • (f * z)) = 0 ∧
    (e * z) * ((-i) • (f * z)) = e * f ∧ ((-i) • (f * z)) * (e * z) = f * e ∧
    e * f + f * e = 1
  refine ⟨sq he hze, ?_, ?_, ?_, ?_⟩
  · rw [smul_mul_assoc, mul_smul_comm, sq hf hzf, smul_zero, smul_zero]
  · rw [mul_smul_comm, prod hzf, neg_smul, smul_neg, neg_neg, smul_smul, him, one_smul]
  · rw [smul_mul_assoc, prod hze, neg_smul, smul_neg, neg_neg, smul_smul, him, one_smul]
  · exact rel.sum

private def cliffordMatrixAlgHom (hw : q w.val ≠ 0) :
    Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) R →ₐ[R] ScalarClifford q R :=
  let H := matrixUnitProducts q h w b R hw
  (pairMatrixAlgHom H.1 H.2.1 (by rw [H.2.2.1, H.2.2.2.1, H.2.2.2.2])).comp
    (Matrix.reindexAlgEquiv R R Equiv.ulift).toAlgHom

private theorem cliffordMatrixAlgHom_apply (hw : q w.val ≠ 0)
    (M : Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) R) :
    cliffordMatrixAlgHom q h w b R hw M = cliffordMatrix q h w R M := by
  change pairMatrix (upperUnit q h w R) (lowerUnit q h w R)
      (Matrix.reindex Equiv.ulift Equiv.ulift M) = _
  let H := matrixUnitProducts q h w b R hw
  simp only [pairMatrix, Matrix.reindex_apply, Matrix.submatrix_apply, H.2.2.1, H.2.2.2.1]
  rfl

open private scalar_tensor_injective changeModule_smul reversion_mul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

include b in
private theorem cliffordMatrix_injective (hw : q w.val ≠ 0) :
    Function.Injective (cliffordMatrix q h w R) := by
  intro M N hMN
  apply matrixAlgHom_injective (cliffordMatrixAlgHom q h w b R hw)
    (scalar_tensor_injective q R b)
  simpa only [cliffordMatrixAlgHom_apply q h w b R hw] using hMN

private def cliffordUnits (hw : q w.val ≠ 0) :
    Matrix.SpecialLinearGroup (ULift.{u} (Fin 2)) R →* (ScalarClifford q R)ˣ :=
  MonoidHom.toHomUnits ((cliffordMatrixAlgHom q h w b R hw).toMonoidHom.comp
    { toFun := Subtype.val
      map_one' := rfl
      map_mul' := fun _ _ => rfl })

private theorem cliffordUnits_value (hw : q w.val ≠ 0)
    (M : Matrix.SpecialLinearGroup (ULift.{u} (Fin 2)) R) :
    (cliffordUnits q h w b R hw M).val = cliffordMatrix q h w R M.val :=
  cliffordMatrixAlgHom_apply q h w b R hw M.val

private theorem cliffordMatrix_natural {R T : TestAlgebra F} (a : R ⟶ T)
    (M : Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) R) :
    coefficientMap q R a.hom (cliffordMatrix q h w R M) =
      cliffordMatrix q h w T (a.hom.toRingHom.mapMatrix M) := by
  have hs (r : R) (z : ScalarClifford q R) :
      coefficientMap q R a.hom (r • z) = a.hom r • coefficientMap q R a.hom z :=
    changeModule_smul a.hom r z
  simp only [cliffordMatrix, map_add, hs, map_mul, change_vector, change_vectorOver,
    map_neg, AlgHom.commutes]
  rfl

open private cliffordEquiv_even cliffordEquiv_vector conjugationLinear
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private vector_even_product over_decompose
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SpinHyperbolicDynamics
open private dynamicsPair from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration

private abbrev SLTwo (R : Type u) [CommRing R] := Matrix.SpecialLinearGroup (ULift.{u} (Fin 2)) R

private theorem cliffordUnits_entries (hw : q w.val ≠ 0) (M : SLTwo R) :
    let scale := -(algebraMap F R ((q w.val)⁻¹))
    (cliffordUnits q h w b R hw M).val =
      fourEntries (eVector q h R) (fVector q h R) (wVector q h w R)
        (M.val ⟨0⟩ ⟨0⟩) (M.val ⟨0⟩ ⟨1⟩) (M.val ⟨1⟩ ⟨0⟩ * scale) (M.val ⟨1⟩ ⟨1⟩) ∧
    (↑((cliffordUnits q h w b R hw M)⁻¹) : ScalarClifford q R) =
      fourEntries (eVector q h R) (fVector q h R) (wVector q h w R)
        (M.val ⟨1⟩ ⟨1⟩) (-(M.val ⟨0⟩ ⟨1⟩)) (-(M.val ⟨1⟩ ⟨0⟩ * scale))
        (M.val ⟨0⟩ ⟨0⟩) := by
  dsimp only
  have value (N : SLTwo R) :
      (cliffordUnits q h w b R hw N).val =
        fourEntries (eVector q h R) (fVector q h R) (wVector q h w R)
          (N.val ⟨0⟩ ⟨0⟩) (N.val ⟨0⟩ ⟨1⟩)
          (N.val ⟨1⟩ ⟨0⟩ * (-(algebraMap F R ((q w.val)⁻¹)))) (N.val ⟨1⟩ ⟨1⟩) := by
    rw [cliffordUnits_value, cliffordMatrix, fourEntries, smul_smul]
  refine ⟨value M, ?_⟩
  change ((cliffordUnits q h w b R hw M)⁻¹).val = _
  rw [← map_inv (cliffordUnits q h w b R hw), value]
  let N := Matrix.reindex Equiv.ulift Equiv.ulift M.val
  have hAdj : Matrix.reindex Equiv.ulift Equiv.ulift (M⁻¹ : SLTwo R).val =
      !![N 1 1, -N 0 1; -N 1 0, N 0 0] := by
    change Matrix.reindex Equiv.ulift Equiv.ulift (Matrix.adjugate M.val) = _
    rw [← Matrix.adjugate_reindex, Matrix.adjugate_fin_two]
  have hAdjEntry (i j : Fin 2) :
      (M⁻¹ : SLTwo R).val ⟨i⟩ ⟨j⟩ =
        (!![N 1 1, -N 0 1; -N 1 0, N 0 0] : Matrix (Fin 2) (Fin 2) R) i j :=
    congrFun (congrFun hAdj i) j
  rw [hAdjEntry 0 0, hAdjEntry 0 1, hAdjEntry 1 0, hAdjEntry 1 1]
  change fourEntries _ _ _ (M.val ⟨1⟩ ⟨1⟩) (-(M.val ⟨0⟩ ⟨1⟩))
    ((-(M.val ⟨1⟩ ⟨0⟩)) * _) (M.val ⟨0⟩ ⟨0⟩) = _
  rw [neg_mul]

private theorem cliffordUnits_normalizes (hw : q w.val ≠ 0) (M : SLTwo R) :
    Set.MapsTo (conjugate q R (cliffordUnits q h w b R hw M))
      (LinearMap.range (vectors q R)) (LinearMap.range (vectors q R)) := by
  let a := M.val ⟨0⟩ ⟨0⟩
  let p := M.val ⟨0⟩ ⟨1⟩
  let r := M.val ⟨1⟩ ⟨0⟩ * (-(algebraMap F R ((q w.val)⁻¹)))
  let d := M.val ⟨1⟩ ⟨1⟩
  let m := algebraMap F R (q w.val)
  let e := eVector q h R
  let f := fVector q h R
  let z := wVector q h w R
  let U := cliffordUnits q h w b R hw M
  let A := fourEntries e f z a p r d
  let A' := fourEntries e f z d (-p) (-r) a
  have hA : U.val = A := (cliffordUnits_entries q h w b R hw M).1
  have hA' : U⁻¹.val = A' := (cliffordUnits_entries q h w b R hw M).2
  have hnorm : A * A' = 1 := by rw [← hA, ← hA', Units.mul_inv]
  let rel : TripleRelations e f z m := cliffordTriple q h w b R
  let E := vectorOver R h.e
  let L := vectorOver R h.f
  let W := vectorOver R w.val
  have he : conjugate q R U (vectors q R E) ∈ LinearMap.range (vectors q R) := by
    refine ⟨a ^ 2 • E - (r ^ 2 * m) • L - (a * r) • W, ?_⟩
    simp only [map_sub, map_smul]
    change _ = U.val * e * U⁻¹.val
    rw [hA, hA']
    exact (rel.conjugates_e a p r d).symm
  have hf : conjugate q R U (vectors q R L) ∈ LinearMap.range (vectors q R) := by
    refine ⟨d ^ 2 • L - (p ^ 2 * m) • E - (d * p) • W, ?_⟩
    simp only [map_sub, map_smul]
    change _ = U.val * f * U⁻¹.val
    rw [hA, hA']
    exact (rel.conjugates_f a p r d).symm
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hx⟩ := over_decompose q (dynamicsPair h) b R x
  change conjugationLinear q R U (vectors q R x) ∈ LinearMap.range (vectors q R)
  rw [hx]
  simp only [map_add, map_smul]
  apply Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ he)
    (Submodule.smul_mem _ _ hf))
  let k := (ExtendedForm q R b).polarBilin W y.val
  have hyE : (ExtendedForm q R b).polarBilin E y.val = 0 := y.property.1
  have hyL : (ExtendedForm q R b).polarBilin L y.val = 0 := y.property.2
  let Y := vectors q R y.val
  have hYe : Y * e = -(e * Y) := orthogonal_vector_swap q b R E y.val hyE
  have hYf : Y * f = -(f * Y) := orthogonal_vector_swap q b R L y.val hyL
  have hYz : z * Y + Y * z = k • 1 := by
    change vectors q R W * vectors q R y.val + _ = _
    rw [vector_swap q b, Algebra.algebraMap_eq_smul_one]
  refine ⟨y.val + (k * a * p) • E + (k * r * d) • L - (k * p * r) • W, ?_⟩
  simp only [map_add, map_sub, map_smul]
  change _ = U.val * Y * U⁻¹.val
  rw [hA, hA']
  exact (rel.conjugates_perpendicular a p r d k Y hYe hYf hYz hnorm).symm

private theorem cliffordUnits_spin (hw : q w.val ≠ 0) (M : SLTwo R) :
    cliffordUnits q h w b R hw M ∈ spinUnits q R := by
  let U := cliffordUnits q h w b R hw M
  let rel := cliffordTriple q h w b R
  obtain ⟨hA, hA'⟩ := cliffordUnits_entries q h w b R hw M
  refine ⟨?_, ?_, cliffordUnits_normalizes q h w b R hw M, ?_⟩
  · change U.val ∈ evenPart q R
    rw [← cliffordEquiv_even q R b, hA]
    simp only [fourEntries, map_add, map_smul, eVector, fVector, wVector, map_mul,
      cliffordEquiv_vector]
    iterate 3 apply Submodule.add_mem
    all_goals exact Submodule.smul_mem _ _ (vector_even_product _ _ _)
  · have hv (x : V) : reversion q R (vectors q R (vectorOver R x)) =
        vectors q R (vectorOver R x) := by simp [vectorOver]
    have hr : reversion q R U.val = U⁻¹.val := by
      rw [hA, hA']
      unfold fourEntries
      simp only [map_add, map_smul, reversion_mul q R b, hv, eVector, fVector, wVector]
      erw [rel.ze, rel.zf]
      simp only [smul_neg, neg_smul]
      abel
    rw [show reversion q R (cliffordUnits q h w b R hw M).val = U⁻¹.val from hr, Units.inv_mul]
  · rw [← map_inv]
    exact cliffordUnits_normalizes q h w b R hw M⁻¹

end CliffordMatrix

section SchemeEmbedding

variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable {G : AffineAlgebraicGroup F}
variable (q : QuadraticForm F V) (h : HyperbolicPair q) (w : h.perpendicular)
variable {I : Type u} [LinearOrder I] (b : Module.Basis I F V)
variable (ρ : ∀ R : TestAlgebra F, GroupPoints G.val R →* (ScalarClifford q R)ˣ)

open private rep_value_natural rep_val_injective point_from_unit
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SpinHyperbolicDynamics

include b in
private theorem cliffordRankOneEmbedding (hw : q w.val ≠ 0)
    (hρ : IsSpinPointRepresentation q G.val ρ) :
    ∃ (A : AffineAlgebraicGroup F) (j : A.val ⟶ G.val),
      IsClosedImmersion j.hom.hom.left ∧
      ∃ e : (groupPointsFunctor F).obj A.val ≅
          Specs.StandardGroups.specialLinearPoints F (ULift.{u} (Fin 2)),
        ∀ (R : TestAlgebra F) (M : SLTwo R),
          (ρ R (((groupPointsFunctor F).map j).app R (e.inv.app R M))).val =
            cliffordMatrix q h w R M.val := by
  let A := StandardGroups.specialLinearGroup F (ULift.{u} (Fin 2))
  let e := StandardGroups.specialLinearGroupPointsIso F (ULift.{u} (Fin 2))
  have existsPoint (R : TestAlgebra F) (M : SLTwo R) :
      ∃ g : GroupPoints G.val R, (ρ R g).val = cliffordMatrix q h w R M.val := by
    obtain ⟨g, hg⟩ := point_from_unit q ρ hρ (cliffordUnits_spin q h w b R hw M)
    exact ⟨g, hg.trans (cliffordUnits_value q h w b R hw M)⟩
  let liftPoint (R : TestAlgebra F) (M : SLTwo R) := (existsPoint R M).choose
  have vlift (R : TestAlgebra F) (M : SLTwo R) :
      (ρ R (liftPoint R M)).val = cliffordMatrix q h w R M.val :=
    (existsPoint R M).choose_spec
  have vlift' (R : TestAlgebra F) (M : SLTwo R) :
      ρ R (liftPoint R M) = cliffordUnits q h w b R hw M :=
    Units.ext ((vlift R M).trans (cliffordUnits_value q h w b R hw M).symm)
  let α : Specs.StandardGroups.specialLinearPoints F (ULift.{u} (Fin 2)) ⟶
      (groupPointsFunctor F).obj G.val :=
    { app := fun R => GrpCat.ofHom
        ({ toFun := liftPoint R
           map_one' := by
             apply (hρ.1 R).1
             exact (vlift' R 1).trans ((map_one (cliffordUnits q h w b R hw)).trans
               (map_one (ρ R)).symm)
           map_mul' := fun M N => by
             apply (hρ.1 R).1
             exact (vlift' R (M * N)).trans
               ((map_mul (cliffordUnits q h w b R hw) M N).trans
                 ((congrArg₂ (· * ·) (vlift' R M).symm (vlift' R N).symm).trans
                   (map_mul (ρ R) (liftPoint R M) (liftPoint R N)).symm)) } : SLTwo R →* GroupPoints G.val R)
      naturality := by
        intro R T a
        apply GrpCat.ext
        intro M
        apply rep_val_injective q ρ hρ T
        change (ρ T (liftPoint T (Matrix.SpecialLinearGroup.map a.hom.toRingHom M))).val =
          (ρ T (mapPoints a (liftPoint R M))).val
        rw [rep_value_natural q ρ hρ, vlift, vlift, cliffordMatrix_natural]
        rfl }
  obtain ⟨j, hj⟩ := (groupHomComparison F A.val G.val A.property.1).2 (e.hom ≫ α)
  have eval (R : TestAlgebra F) (p : GroupPoints A.val R) :
      ((groupPointsFunctor F).map j).app R p = liftPoint R (e.hom.app R p) :=
    DFunLike.congr_fun (congrArg (fun τ => (τ.app R).hom) hj) p
  refine ⟨A, j, ?_, e, ?_⟩
  · apply RootData.RootGroups.isClosedImmersion_of_injectivePoints A G j
    intro R p s hps
    have he (g : GroupPoints A.val R) : e.inv.app R (e.hom.app R g) = g :=
      DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.app R).hom_inv_id) g
    have heq : e.hom.app R p = e.hom.app R s := by
      apply Subtype.ext
      apply cliffordMatrix_injective q h w b R hw
      calc
        _ = (ρ R (((groupPointsFunctor F).map j).app R p)).val :=
          (vlift R _).symm.trans (congrArg (fun g => (ρ R g).val) (eval R p).symm)
        _ = (ρ R (((groupPointsFunctor F).map j).app R s)).val :=
          congrArg (fun g : GroupPoints G.val R => (ρ R g).val) hps
        _ = _ := (congrArg (fun g => (ρ R g).val) (eval R s)).trans (vlift R _)
    simpa only [he] using congrArg (e.inv.app R) heq
  · intro R M
    rw [eval, vlift]
    congr 1
    exact congrArg (fun N : SLTwo R => N.val)
      (DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.app R).inv_hom_id) M)

private def matrixDiagonal (R : TestAlgebra F) (t : Rˣ) : SLTwo R :=
  ⟨Matrix.reindex Equiv.ulift.symm Equiv.ulift.symm !![(t : R), 0; 0, (↑t⁻¹ : R)], by
    rw [Matrix.det_reindex_self, Matrix.det_fin_two_of, zero_mul, sub_zero, Units.mul_inv]⟩

private theorem cliffordMatrix_diagonal (R : TestAlgebra F) (t : Rˣ) :
    cliffordMatrix q h w R (matrixDiagonal R t).val =
      (t : R) • (eVector q h R * fVector q h R) +
        (↑t⁻¹ : R) • (fVector q h R * eVector q h R) := by
  change (t : R) • _ + (0 : R) • _ + (0 : R) • _ + (↑t⁻¹ : R) • _ = _
  simp only [zero_smul, add_zero]

open private unitEquiv unitEquiv_unitPoint subgroupInclusionFactors
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

include b in
private theorem diagonalLift {A : AffineAlgebraicGroup F} (j : A.val ⟶ G.val)
    (hj : IsClosedImmersion j.hom.hom.left)
    (e : (groupPointsFunctor F).obj A.val ≅
      Specs.StandardGroups.specialLinearPoints F (ULift.{u} (Fin 2)))
    (hw : q w.val ≠ 0)
    (hρ : IsSpinPointRepresentation q G.val ρ)
    (hM : ∀ (R : TestAlgebra F) (M : SLTwo R),
      (ρ R (((groupPointsFunctor F).map j).app R (e.inv.app R M))).val =
        cliffordMatrix q h w R M.val)
    (d : Cocharacter G.val) (hd : Specs.Arithmetic.IsotropicSpinGeneration.HasSpinCocharacterFormula h ρ d) :
    ∃ c : Cocharacter A.val, c ≫ j = d ∧
      ∀ (R : TestAlgebra F) (t : Rˣ), e.hom.app R (cocharacterPoint c R t) = matrixDiagonal R t := by
  have eval (R : TestAlgebra F) (t : Rˣ) :
      ((groupPointsFunctor F).map j).app R (e.inv.app R (matrixDiagonal R t)) =
        cocharacterPoint d R t := by
    exact rep_val_injective q ρ hρ R
      ((hM R (matrixDiagonal R t)).trans
        ((cliffordMatrix_diagonal q h w R t).trans (hd R t).symm))
  have ha : IsAffine (specGroup
      (Specs.DiagonalizableGroups.groupAlgebra F Specs.DiagonalizableGroups.IntegerCharacters)).X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of
      (MonoidAlgebra F Specs.DiagonalizableGroups.IntegerCharacters.{u}))))
  let J : Specs.ClosedSubgroup G.val := ⟨A.val, j, hj⟩
  obtain ⟨c, hc⟩ := subgroupInclusionFactors ha J d (by
    intro R p
    let t := unitEquiv R p
    have hp : unitPoint R t = p :=
      (unitEquiv R).injective (unitEquiv_unitPoint R t)
    refine ⟨e.inv.app R (matrixDiagonal R t), ?_⟩
    exact (eval R t).trans (congrArg
      (fun p' => ((groupPointsFunctor F).map d).app R p') hp))
  change c ≫ j = d at hc
  refine ⟨c, hc, fun R t => ?_⟩
  have he (p : GroupPoints A.val R) : e.inv.app R (e.hom.app R p) = p :=
    DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.app R).hom_inv_id) p
  have hd' : cocharacterPoint d R t =
      ((groupPointsFunctor F).map j).app R (cocharacterPoint c R t) := by
    rw [← hc]
    change unitPoint R t ≫ c.hom.hom ≫ j.hom.hom =
      (unitPoint R t ≫ c.hom.hom) ≫ j.hom.hom
    exact (Category.assoc _ _ _).symm
  apply Subtype.ext
  apply cliffordMatrix_injective q h w b R hw
  let M : SLTwo R := e.hom.app R (cocharacterPoint c R t)
  change cliffordMatrix q h w R M.val = _
  refine (hM R M).symm.trans ?_
  have hp : e.inv.app R M = cocharacterPoint c R t := he _
  exact (congrArg (fun g : GroupPoints A.val R =>
      (ρ R (((groupPointsFunctor F).map j).app R g)).val) hp).trans
    ((congrArg (fun g : GroupPoints G.val R => (ρ R g).val)
      (hd'.symm.trans (eval R t).symm)).trans (hM R (matrixDiagonal R t)))

end SchemeEmbedding

section DiagonalLimits

variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable {G : AffineAlgebraicGroup F}
variable (q : QuadraticForm F V) (h : HyperbolicPair q) (w : h.perpendicular)
variable {I : Type u} [LinearOrder I] [Fintype I] (b : Module.Basis I F V)
variable (ρ : ∀ R : TestAlgebra F, GroupPoints G.val R →* (ScalarClifford q R)ˣ)
variable (R : TestAlgebra F)

open Specs.Arithmetic.IsotropicSpinGeneration (ShearPoint)
open Specs.Arithmetic.SpinHyperbolicDynamics (vectorOver)
open private polar_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SpinHyperbolicDynamics

include b in
private theorem upperCliffordValue (x : R) :
    cliffordMatrix q h w R (upper x).val =
      1 + eVector q h R * vectors q R (x • vectorOver R w.val) := by
  have hsum := (cliffordTriple q h w b R).sum
  let e := eVector q h R
  let f := fVector q h R
  let z := wVector q h w R
  change ((1 : R) + 0) • (e * f) + (0 + x) • (e * z) +
    ((0 : R) + 0) • lowerUnit q h w R + ((1 : R) + 0) • (f * e) =
      1 + e * vectors q R (x • vectorOver R w.val)
  simp only [zero_add, add_zero, one_smul, zero_smul, map_smul, mul_smul_comm]
  rw [← hsum]
  abel

include b in
private theorem lowerCliffordValue (x : R) :
    cliffordMatrix q h w R (lower x).val =
      1 + fVector q h R * vectors q R
        ((x * (-(algebraMap F R ((q w.val)⁻¹)))) • vectorOver R w.val) := by
  have hsum := (cliffordTriple q h w b R).sum
  let e := eVector q h R
  let f := fVector q h R
  let z := wVector q h w R
  let a := -(algebraMap F R ((q w.val)⁻¹))
  change ((1 : R) + 0) • (e * f) + ((0 : R) + 0) • (e * z) +
    (0 + x) • (a • (f * z)) + ((1 : R) + 0) • (f * e) =
      1 + f * vectors q R ((x * a) • vectorOver R w.val)
  simp only [zero_add, add_zero, one_smul, zero_smul, map_smul, mul_smul_comm, smul_smul]
  rw [← hsum]
  abel

include b in
private theorem upperShearPoint {g : GroupPoints G.val R} (x : R)
    (hg : (ρ R g).val = cliffordMatrix q h w R (upper x).val) : ShearPoint b h ρ h.e R g := by
  refine ⟨x • vectorOver R w.val, ?_, ?_, hg.trans (upperCliffordValue q h w b R x)⟩
  · change (ExtendedForm q R b).polarBilin (vectorOver R h.e) _ = _
    rw [map_smul, polar_over, show q.polarBilin h.e w.val = 0 from w.property.1,
      map_zero, smul_zero]
  · change (ExtendedForm q R b).polarBilin (vectorOver R h.f) _ = _
    rw [map_smul, polar_over, show q.polarBilin h.f w.val = 0 from w.property.2,
      map_zero, smul_zero]

include b in
private theorem lowerShearPoint {g : GroupPoints G.val R} (x : R)
    (hg : (ρ R g).val = cliffordMatrix q h w R (lower x).val) : ShearPoint b h ρ h.f R g := by
  refine ⟨(x * (-(algebraMap F R ((q w.val)⁻¹)))) • vectorOver R w.val, ?_, ?_,
    hg.trans (lowerCliffordValue q h w b R x)⟩
  · change (ExtendedForm q R b).polarBilin (vectorOver R h.e) _ = _
    rw [map_smul, polar_over, show q.polarBilin h.e w.val = 0 from w.property.1,
      map_zero, smul_zero]
  · change (ExtendedForm q R b).polarBilin (vectorOver R h.f) _ = _
    rw [map_smul, polar_over, show q.polarBilin h.f w.val = 0 from w.property.2,
      map_zero, smul_zero]

end DiagonalLimits

section WeightLimits

open scoped LaurentPolynomial BigOperators
open Specs.Arithmetic.SpinHyperbolicDynamics (vectorOver)
open private changeModule changeModule_smul conjugationLinear
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private change_vector change_vectorOver form_over polar_over rep_value_natural
  rep_val_injective point_from_unit from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SpinHyperbolicDynamics

variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable {G : AffineAlgebraicGroup F}
variable (q : QuadraticForm F V)
variable {I : Type u} [LinearOrder I] (b : Module.Basis I F V)
variable (ρ : ∀ R : TestAlgebra F, GroupPoints G.val R →* (ScalarClifford q R)ˣ)

private def HasSpinWeight (c : Cocharacter G.val) (n : ℤ) (v : V) : Prop :=
  ∀ (R : TestAlgebra F) (t : Rˣ),
    conjugate q R (ρ R (cocharacterPoint c R t)) (vectors q R (vectorOver R v)) =
      (t ^ n).val • vectors q R (vectorOver R v)

private theorem representedOrbit (hρ : IsSpinPointRepresentation q G.val ρ)
    (c : Cocharacter G.val) {R : TestAlgebra F} (g : GroupPoints G.val R) :
    (ρ (laurentAlgebra R) (orbit c g)).val =
      conjugate q (laurentAlgebra R)
        (ρ (laurentAlgebra R) (cocharacterPoint c (laurentAlgebra R) (laurentParameter R)))
        (coefficientMap q R (laurentConstants R).hom (ρ R g).val) := by
  change (ρ _ (_ * (show GroupPoints G.val (laurentAlgebra R) from
    mapPoints (laurentConstants R) g) * _⁻¹)).val = _
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, rep_value_natural q ρ hρ]
  rfl

set_option maxHeartbeats 850000 in
include b in
/-- Weight sums strictly above zero give polynomial families with identity value at zero. -/
private theorem weightedShear_hasLimit (hρ : IsSpinPointRepresentation q G.val ρ)
    (c : Cocharacter G.val) {e : V} (he : q e = 0) {n : ℤ}
    (heWeight : HasSpinWeight q ρ c n e) {J : Type u} (indices : Finset J) (weight : J → ℤ) (component : J → V)
    (hPerp : ∀ m ∈ indices, q.polarBilin e (component m) = 0)
    (hWeight : ∀ m ∈ indices, HasSpinWeight q ρ c (weight m) (component m))
    (hpositive : ∀ m ∈ indices, 0 < n + weight m)
    {g : GroupPoints G.val (CommAlgCat.of F F)}
    (hg : (ρ (CommAlgCat.of F F) g).val = 1 +
      vectors q F (1 ⊗ₜ[F] e) *
        vectors q F (1 ⊗ₜ[F] ∑ m ∈ indices, component m)) :
    HasLimit c g 1 := by
  let R := CommAlgCat.of F F
  let P := polynomialAlgebra R
  let L := laurentAlgebra R
  let t : Lˣ := laurentParameter R
  let p : P ⊗[F] V :=
    ∑ m ∈ indices, (Polynomial.X : P) ^ (n + weight m).toNat • vectorOver P (component m)
  have hp : (ExtendedForm q P b).polarBilin (vectorOver P e) p = 0 := by
    dsimp only [p]
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro m hm
    rw [map_smul, polar_over, hPerp m hm, map_zero, smul_zero]
  have heP : ExtendedForm q P b (vectorOver P e) = 0 := by
    rw [form_over, he, map_zero]
  obtain ⟨U, hU, hval, _, _⟩ :=
    IsotropicSpinGeneration.scalarShears q b P (vectorOver P e) p heP hp
  obtain ⟨y, hy⟩ := point_from_unit q ρ hρ hU
  have hyP : (ρ P y).val = 1 + vectors q P (vectorOver P e) * vectors q P p := hy.trans hval
  have htPower (m : J) (hm : m ∈ indices) :
      (polynomialToLaurent R).hom ((Polynomial.X : P) ^ (n + weight m).toNat) =
        (t ^ (n + weight m)).val := by
    change Polynomial.toLaurent ((Polynomial.X : Polynomial R) ^ (n + weight m).toNat) = _
    rw [Polynomial.toLaurent_X_pow, ← Int.toNat_of_nonneg (hpositive m hm).le, zpow_natCast]
    change LaurentPolynomial.T ((n + weight m).toNat : ℤ) =
      (LaurentPolynomial.T 1 : LaurentPolynomial R) ^ (n + weight m).toNat
    rw [LaurentPolynomial.T_pow, mul_one]
  refine ⟨y, rep_val_injective q ρ hρ L ?_, rep_val_injective q ρ hρ R ?_⟩
  · change (ρ L (mapPoints (polynomialToLaurent R) y)).val = (ρ L (orbit c g)).val
    rw [rep_value_natural q ρ hρ, hyP, map_add, map_mul, map_one, change_vector,
      change_vectorOver, change_vector, representedOrbit q ρ hρ c, hg,
      map_add, map_mul, map_one, change_vector, change_vectorOver, change_vector, change_vectorOver]
    let u := ρ L (cocharacterPoint c L t)
    have addMul (x z : ScalarClifford q L) :
        conjugate q L u (1 + x * z) =
          1 + conjugate q L u x * conjugate q L u z := by
      simp only [conjugate, mul_add, add_mul, mul_one, Units.mul_inv, mul_assoc]
      rw [← mul_assoc (↑u⁻¹ : ScalarClifford q L) (↑u), Units.inv_mul, one_mul]
    have hvec (m : J) (hm : m ∈ indices) :
        conjugate q L u (vectors q L (vectorOver L (component m))) =
          (t ^ weight m).val • vectors q L (vectorOver L (component m)) :=
      hWeight m hm L t
    change 1 + _ = conjugate q L u (1 + _ * _)
    rw [addMul, heWeight L t]
    have hs : vectorOver L (∑ m ∈ indices, component m) =
        ∑ m ∈ indices, vectorOver L (component m) :=
      map_sum (TensorProduct.mk F L V 1) component indices
    have hconj :
        conjugate q L u (vectors q L (vectorOver L (∑ m ∈ indices, component m))) =
          ∑ m ∈ indices, (t ^ weight m).val • vectors q L (vectorOver L (component m)) := by
      change conjugationLinear q L u (vectors q L (vectorOver L (∑ m ∈ indices, component m))) = _
      rw [hs, map_sum, map_sum]
      exact Finset.sum_congr rfl hvec
    have hpoly :
        vectors q L (changeModule (polynomialToLaurent R).hom p) =
          ∑ m ∈ indices, (t ^ (n + weight m)).val • vectors q L (vectorOver L (component m)) := by
      dsimp only [p]
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [changeModule_smul, change_vectorOver, htPower m hm, map_smul]
    rw [hconj, hpoly]
    apply congrArg (1 + ·)
    simp only [smul_mul_assoc, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul_comm, mul_smul_comm, smul_smul, ← Units.val_mul, ← zpow_add]
  · change (ρ R (mapPoints (polynomialEvaluate R 0) y)).val = (ρ R 1).val
    rw [rep_value_natural q ρ hρ, hyP, map_add, map_mul, map_one,
      change_vector, change_vectorOver, change_vector, map_one, Units.val_one]
    have hz : changeModule (polynomialEvaluate R 0).hom p = 0 := by
      simp only [p, map_sum, changeModule_smul, map_pow, change_vectorOver]
      apply Finset.sum_eq_zero
      intro m hm
      have hX : (polynomialEvaluate R 0).hom (Polynomial.X : P) = 0 := Polynomial.eval₂_X _ _
      have hm' := hpositive m hm
      rw [hX, zero_pow (by omega : (n + weight m).toNat ≠ 0), zero_smul]
    rw [hz, map_zero, mul_zero, add_zero]

end WeightLimits

section SpinWeights

open scoped LaurentPolynomial BigOperators
open Specs.Arithmetic.SpinHyperbolicDynamics (vectorOver)
open private changeModule changeModule_smul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private change_vectorOver
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SpinHyperbolicDynamics
open private evalLaurent evalLaurent_parameter cocharacterPoint_mul opposite_point
  unitPointHom_apply unitPointHom
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open LinearAlgebraicGroups.Albert.SpinFunctor
  (Spin vectorAction vectorAction_characterization vectorAction_naturality)

variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable {G : AffineAlgebraicGroup F}
variable (q : QuadraticForm F V)
variable {I : Type u} [LinearOrder I] (b : Module.Basis I F V)
variable (ρ : ∀ R : TestAlgebra F, GroupPoints G.val R →* (ScalarClifford q R)ˣ)
variable (hρ : IsSpinPointRepresentation q G.val ρ)

include hρ in
private def pointSpin (R : TestAlgebra F) : GroupPoints G.val R →* Spin q R b where
  toFun g := ⟨ρ R g, by
    change ρ R g ∈ spinUnits q R
    exact (hρ.1 R).2 ▸ Set.mem_range_self g⟩
  map_one' := Subtype.ext (map_one (ρ R))
  map_mul' x y := Subtype.ext (map_mul (ρ R) x y)

private def pointAction (R : TestAlgebra F) :
    GroupPoints G.val R →* (R ⊗[F] V) ≃ₗ[R] (R ⊗[F] V) :=
  (vectorAction q R b).comp (pointSpin q b ρ hρ R)

private theorem pointAction_formula (R : TestAlgebra F) (g : GroupPoints G.val R)
    (x : R ⊗[F] V) :
    vectors q R (pointAction q b ρ hρ R g x) = conjugate q R (ρ R g) (vectors q R x) :=
  vectorAction_characterization q R b (pointSpin q b ρ hρ R g) x

private theorem pointAction_natural {R T : TestAlgebra F} (a : R ⟶ T)
    (g : GroupPoints G.val R) (x : R ⊗[F] V) :
    changeModule a.hom (pointAction q b ρ hρ R g x) =
      pointAction q b ρ hρ T (mapPoints a g) (changeModule a.hom x) := by
  have hn : LinearAlgebraicGroups.Albert.SpinFunctor.map q b a.hom (pointSpin q b ρ hρ R g) =
      pointSpin q b ρ hρ T (mapPoints a g) := Subtype.ext (hρ.2 a g).symm
  exact (vectorAction_naturality q b a.hom (pointSpin q b ρ hρ R g) x).trans
    (congrArg (fun p => vectorAction q T b p (changeModule a.hom x)) hn)

private theorem laurentUnit_zpow {F : Type u} [Field F] (R : TestAlgebra F) (n : ℤ) :
    (laurentParameter R ^ n).val = (LaurentPolynomial.T n : LaurentPolynomial R) := by
  cases n with
  | ofNat j =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    change (LaurentPolynomial.T 1 : LaurentPolynomial R) ^ j = _
    rw [LaurentPolynomial.T_pow, mul_one]
  | negSucc j =>
    rw [Int.negSucc_eq, ← Nat.cast_succ, zpow_neg, zpow_natCast, ← inv_pow]
    change (LaurentPolynomial.T (-1) : LaurentPolynomial R) ^ (j + 1) = _
    rw [LaurentPolynomial.T_pow, mul_neg, mul_one, Nat.cast_succ]

private theorem spinAction_expansion (c : Cocharacter G.val) (v : V) :
    ∃ w : ℤ →₀ V, ∀ (R : TestAlgebra F) (t : Rˣ),
      pointAction q b ρ hρ R (cocharacterPoint c R t) (vectorOver R v) =
        ∑ n ∈ w.support, (t ^ n).val • vectorOver R (w n) := by
  let K := CommAlgCat.of F F
  let L := laurentAlgebra K
  let vec := pointAction q b ρ hρ L (cocharacterPoint c L (laurentParameter K)) (vectorOver L v)
  let E : (L ⊗[F] V) ≃ₗ[F] ℤ →₀ V :=
    (AddMonoidAlgebra.coeffLinearEquiv F).rTensor V ≪≫ₗ TensorProduct.finsuppScalarLeft F V ℤ
  let w := E vec
  have hv : vec = ∑ n ∈ w.support, (LaurentPolynomial.T n : L) ⊗ₜ[F] w n := by
    rw [show vec = E.symm w from (E.symm_apply_apply _).symm]
    conv_lhs => rw [← Finsupp.sum_single w]
    simp only [Finsupp.sum, map_sum, E, LinearEquiv.symm_trans_apply]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [TensorProduct.finsuppScalarLeft_symm_apply_single (R := F),
      LinearEquiv.rTensor_symm_tmul]
    rfl
  refine ⟨w, fun R t => ?_⟩
  let a : K ⟶ R := CommAlgCat.ofHom (Algebra.ofId F R)
  let ev := evalLaurent a t
  have h' := pointAction_natural q b ρ hρ ev
    (cocharacterPoint c L (laurentParameter K)) (vectorOver L v)
  rw [mapPoints_cocharacterPoint, evalLaurent_parameter, change_vectorOver] at h'
  change changeModule ev.hom vec = _ at h'
  rw [← h', hv, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  change ev.hom (LaurentPolynomial.T n) ⊗ₜ[F] w n = _
  rw [show ev.hom (LaurentPolynomial.T n) = (t ^ n).val from LaurentPolynomial.eval₂_T a.hom.toRingHom t n,
    vectorOver, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private def tensorLaurentCoeff (R : TestAlgebra F) (n : ℤ) :
    laurentAlgebra R ⊗[F] V →ₗ[F] R ⊗[F] V :=
  ((Finsupp.lapply n : (ℤ →₀ R) →ₗ[F] R) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv F).toLinearMap).rTensor V

private theorem tensorLaurentCoeff_monomial (R : TestAlgebra F) (n m : ℤ) (y : R ⊗[F] V) :
    tensorLaurentCoeff R (V := V) n ((LaurentPolynomial.T m : laurentAlgebra R) •
      changeModule (laurentConstants R).hom y) = if m = n then y else 0 := by
  induction y with
  | tmul a v =>
    change ((LaurentPolynomial.T m * LaurentPolynomial.C a : LaurentPolynomial R).coeff n) ⊗ₜ[F] v = _
    rw [mul_comm, ← LaurentPolynomial.single_eq_C_mul_T]
    rw [AddMonoidAlgebra.coeff_single]
    by_cases h : m = n <;> simp [h]
  | add y z hy hz =>
    simp only [map_add, smul_add, hy, hz]
    split_ifs <;> simp

include b hρ in
private theorem spinWeight_decomposition (c : Cocharacter G.val) (v : V) :
    ∃ w : ℤ →₀ V,
      v = ∑ n ∈ w.support, w n ∧ ∀ n ∈ w.support, HasSpinWeight q ρ c n (w n) := by
  obtain ⟨w, hw⟩ := spinAction_expansion q b ρ hρ c v
  refine ⟨w, ?_, ?_⟩
  · let R := CommAlgCat.of F F
    have hc : cocharacterPoint c R (1 : Rˣ) = 1 := by
      rw [cocharacterPoint, ← unitPointHom_apply, map_one, map_one]
    have H := hw R 1
    rw [hc, map_one] at H
    simp only [one_zpow, Units.val_one, one_smul] at H
    simpa [vectorOver] using congrArg (TensorProduct.lid F V) H
  · intro n hn R t
    let L := laurentAlgebra R
    let inc := laurentConstants R
    let s := Units.map inc.hom.toMonoidHom t
    let r := laurentParameter R
    let g := cocharacterPoint c L s
    have hmul := hw L (s * r)
    rw [cocharacterPoint_mul, map_mul] at hmul
    change pointAction q b ρ hρ L g
        (pointAction q b ρ hρ L (cocharacterPoint c L r) (vectorOver L v)) = _ at hmul
    rw [hw L r] at hmul
    have hnatur (u : V) : pointAction q b ρ hρ L g (vectorOver L u) =
        changeModule inc.hom (pointAction q b ρ hρ R (cocharacterPoint c R t) (vectorOver R u)) := by
      have H := pointAction_natural q b ρ hρ inc (cocharacterPoint c R t) (vectorOver R u)
      rw [mapPoints_cocharacterPoint, change_vectorOver] at H
      exact H.symm
    have hr (m : ℤ) : (r ^ m).val = (LaurentPolynomial.T m : L) :=
      laurentUnit_zpow R m
    simp only [map_sum, map_smul, hnatur, mul_zpow, Units.val_mul, hr] at hmul
    have hright (m : ℤ) :
        ((s ^ m).val * (LaurentPolynomial.T m : L)) • vectorOver L (w m) =
          (LaurentPolynomial.T m : L) •
            changeModule inc.hom ((t ^ m).val • vectorOver R (w m)) := by
      rw [changeModule_smul, change_vectorOver, smul_smul, mul_comm]
      congr 2
      exact (congrArg Units.val (map_zpow (Units.map inc.hom.toMonoidHom) t m)).symm
    simp_rw [hright] at hmul
    let coeff := tensorLaurentCoeff R (V := V) n
    have extract (x : ℤ → R ⊗[F] V) :
        coeff (∑ j ∈ w.support, (LaurentPolynomial.T j : L) • changeModule inc.hom (x j)) = x n := by
      rw [map_sum]
      rw [Finset.sum_eq_single n]
      · exact (tensorLaurentCoeff_monomial R n n (x n)).trans (if_pos rfl)
      · intro j _ hj
        exact (tensorLaurentCoeff_monomial R n j (x j)).trans (if_neg hj)
      · exact fun h => (h hn).elim
    have H := (extract _).symm.trans ((congrArg coeff hmul).trans (extract _))
    rw [← pointAction_formula q b ρ hρ, H, map_smul]

end SpinWeights

section WeightCentralizer

open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open private cocharactersOfCentralizer_are_central
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeChambers
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private centralizes_onAlgebras unitEquiv unitEquiv_unitPoint subgroupInclusionFactors
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}

private theorem commutes_in_regularCentralizer
    (hG : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G)
    (S : Specs.ClosedSubgroup G.val) (hS : Specs.Relative.MaximalSplitTori.IsMaximalSplitTorus S)
    (c : Cocharacter S.group) (hc : Specs.Relative.RelativeChambers.IsRegular S c)
    (d : Cocharacter G.val)
    (hd : ∀ (R : TestAlgebra F) (t s : Rˣ),
      Commute (cocharacterPoint d R t) (cocharacterPoint (c ≫ S.inclusion) R s))
    {R : TestAlgebra F} (g : GroupPoints G.val R)
    (hg : Centralizes (c ≫ S.inclusion) g) : Centralizes d g := by
  let cG := c ≫ S.inclusion
  obtain ⟨D⟩ := existsLimitDecomposition G cG
  have hD := Relative.RelativeChambers.regularLevi G (reductive_of_semisimple G hG.1) S hS.1 c D hc
  have ha : IsAffine (specGroup
      (Specs.DiagonalizableGroups.groupAlgebra F Specs.DiagonalizableGroups.IntegerCharacters)).X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of
      (MonoidAlgebra F Specs.DiagonalizableGroups.IntegerCharacters.{u}))))
  obtain ⟨d', eqd⟩ := subgroupInclusionFactors ha D.centralizer d (by
    intro T p
    let t := unitEquiv T p
    have hp : unitPoint T t = p :=
      (unitEquiv T).injective (unitEquiv_unitPoint T t)
    have cent : Centralizes cG (cocharacterPoint d T t) := by
      apply (centralizes_onAlgebras cG _).2
      intro T' a s
      rw [mapPoints_cocharacterPoint]
      exact hd T' _ s
    have h := (D.centralizer_points _ _).mp cent
    rw [← hp]
    exact h)
  obtain ⟨g', eqg⟩ := (D.centralizer_points _ _).mp hg
  have hcent := cocharactersOfCentralizer_are_central G S D.centralizer hS hD d' _ g'
  apply (centralizes_iff d g).2
  intro X a s
  have h := ((centralizes_iff d' g').1 hcent X a s).map
    (IsMonHom.monoidHom D.centralizer.inclusion.hom.hom X)
  change Commute ((a ≫ g') ≫ D.centralizer.inclusion.hom.hom)
    ((s ≫ d'.hom.hom) ≫ D.centralizer.inclusion.hom.hom) at h
  simpa only [Category.assoc, eqg, ← show d'.hom.hom ≫ D.centralizer.inclusion.hom.hom =
      d.hom.hom from (Grp.forget _).congr_map eqd] using h

end WeightCentralizer

section WeightArithmetic

open Specs.Arithmetic.SpinHyperbolicDynamics (vectorOver)
open private conjugationLinear vectors_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private form_over polar_over action_preserves_polar
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SpinHyperbolicDynamics
open private opposite_point from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open scoped BigOperators

variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable {G : AffineAlgebraicGroup F}
variable (q : QuadraticForm F V)
variable {I : Type u} [LinearOrder I] (b : Module.Basis I F V)
variable (ρ : ∀ R : TestAlgebra F, GroupPoints G.val R →* (ScalarClifford q R)ˣ)
variable (hρ : IsSpinPointRepresentation q G.val ρ)

private theorem conjugationMul (R : TestAlgebra F) (g : (ScalarClifford q R)ˣ)
    (x y : ScalarClifford q R) :
    conjugate q R g (x * y) = conjugate q R g x * conjugate q R g y := by
  simp only [conjugate, mul_assoc]
  rw [← mul_assoc (↑g⁻¹ : ScalarClifford q R) (↑g), Units.inv_mul, one_mul]

private theorem conjugationOne (R : TestAlgebra F) (g : (ScalarClifford q R)ˣ) :
    conjugate q R g 1 = 1 := by simp [conjugate]

private theorem constantVector_smul (R : TestAlgebra F) (s : F) (v : V) :
    vectorOver R (s • v) = (algebraMap F R s) • vectorOver R v := by
  rw [vectorOver, vectorOver, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul',
    Algebra.algebraMap_eq_smul_one, smul_eq_mul, mul_one]

private theorem HasSpinWeight.smul {c : Cocharacter G.val} {n : ℤ} {v : V}
    (h : HasSpinWeight q ρ c n v) (a : F) : HasSpinWeight q ρ c n (a • v) := by
  intro R t
  rw [constantVector_smul, map_smul]
  let U := ρ R (cocharacterPoint c R t)
  change (conjugationLinear q R U) ((algebraMap F R a) • vectors q R (vectorOver R v)) = _
  rw [map_smul]
  change _ • conjugate q R U _ = _
  rw [h R t, smul_smul, smul_smul, mul_comm]

private theorem HasSpinWeight.add {c : Cocharacter G.val} {n : ℤ} {v w : V}
    (hv : HasSpinWeight q ρ c n v) (hw : HasSpinWeight q ρ c n w) :
    HasSpinWeight q ρ c n (v + w) := by
  intro R t
  change conjugationLinear q R _ (vectors q R (1 ⊗ₜ[F] (v + w))) = _
  simp only [vectorOver, TensorProduct.tmul_add, map_add, smul_add]
  change conjugate q R _ _ + conjugate q R _ _ = _
  rw [hv R t, hw R t]

private theorem HasSpinWeight.zero (c : Cocharacter G.val) (n : ℤ) :
    HasSpinWeight q ρ c n 0 := by
  intro R t
  simp [vectorOver, conjugate]

private theorem HasSpinWeight.opposite {c : Cocharacter G.val} {n : ℤ} {v : V}
    (hv : HasSpinWeight q ρ c n v) : HasSpinWeight q ρ (oppositeCocharacter c) (-n) v := by
  intro R t
  rw [opposite_point, hv R t⁻¹, inv_zpow, zpow_neg]

private theorem exists_distinct_unit_powers [ValuativeRel F] [ValuativeRel.IsNontrivial F] :
    ∃ s : Fˣ, Function.Injective (fun n : ℤ => (s ^ n).val) := by
  obtain ⟨v, hv0, hv1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := F)
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective v
  have ha0 : a ≠ 0 := fun h => hv0.ne' (by simpa [h] using ha.symm)
  let s := Units.mk0 a ha0
  let t := Units.map (ValuativeRel.valuation F).toMonoidHom s
  have ht : t.val = v := ha
  refine ⟨s, fun i j H => (zpow_right_strictAnti₀ hv0 hv1).injective ?_⟩
  have hi (n : ℤ) : ValuativeRel.valuation F (s ^ n).val = v ^ n := by
    change ((Units.map (ValuativeRel.valuation F).toMonoidHom) (s ^ n)).val = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val, ht]
  simpa only [hi] using congrArg (ValuativeRel.valuation F) H

include b hρ in
private theorem weightAction {c : Cocharacter G.val} {n : ℤ} {v : V}
    (hv : HasSpinWeight q ρ c n v) (R : TestAlgebra F) (t : Rˣ) :
    pointAction q b ρ hρ R (cocharacterPoint c R t) (vectorOver R v) =
      (t ^ n).val • vectorOver R v := by
  apply vectors_injective q R b
  rw [pointAction_formula, hv R t, map_smul]

include b hρ in
private theorem spinWeights_polar {c : Cocharacter G.val} {i j : ℤ} {v w : V}
    (hv : HasSpinWeight q ρ c i v) (hw : HasSpinWeight q ρ c j w)
    (s : Fˣ) (hs : Function.Injective (fun n : ℤ => (s ^ n).val)) (hij : i + j ≠ 0) :
    q.polarBilin v w = 0 := by
  let R := CommAlgCat.of F F
  let g := cocharacterPoint c R s
  have H := action_preserves_polar q b R (pointSpin q b ρ hρ R g)
    (vectorOver R v) (vectorOver R w)
  change (ExtendedForm q R b).polarBilin (pointAction q b ρ hρ R g (vectorOver R v))
    (pointAction q b ρ hρ R g (vectorOver R w)) =
      (ExtendedForm q R b).polarBilin (vectorOver R v) (vectorOver R w) at H
  rw [weightAction q b ρ hρ hv R s, weightAction q b ρ hρ hw R s] at H
  simp only [map_smul, LinearMap.smul_apply, polar_over] at H
  change (s ^ j).val * ((s ^ i).val * q.polarBilin v w) = q.polarBilin v w at H
  by_contra hn
  have eq : (s ^ (i + j)).val = (s ^ (0 : ℤ)).val := by
    apply mul_right_cancel₀ hn
    simpa only [zpow_add, Units.val_mul, mul_assoc, zpow_zero, Units.val_one, one_mul,
      mul_left_comm (s ^ i).val] using H
  exact hij (hs eq)

include b hρ in
private theorem spinWeight_isotropic {c : Cocharacter G.val} {n : ℤ} {v : V}
    (hv : HasSpinWeight q ρ c n v) (s : Fˣ)
    (hs : Function.Injective (fun n : ℤ => (s ^ n).val)) (hn : n ≠ 0) : q v = 0 := by
  let R := CommAlgCat.of F F
  let g := cocharacterPoint c R s
  have H := LinearAlgebraicGroups.Albert.SpinFunctor.vectorAction_preserves q R b
    (pointSpin q b ρ hρ R g) (vectorOver R v)
  change ExtendedForm q R b (pointAction q b ρ hρ R g (vectorOver R v)) =
    ExtendedForm q R b (vectorOver R v) at H
  rw [weightAction q b ρ hρ hv R s, QuadraticMap.map_smul, form_over] at H
  change (s ^ n).val * (s ^ n).val * q v = q v at H
  by_contra hqv
  have eq : (s ^ (n + n)).val = (s ^ (0 : ℤ)).val := by
    apply mul_right_cancel₀ hqv
    simpa only [zpow_add, Units.val_mul, zpow_zero, Units.val_one, one_mul] using H
  have eq' := hs eq
  omega

end WeightArithmetic

section ZeroWeightShears

open Specs.Arithmetic.SpinHyperbolicDynamics (vectorOver IsDiagonal perpendicularOver shearValue)
open private rep_value_natural rep_val_injective form_over polar_over
  change_vector change_vectorOver shear_parameter_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SpinHyperbolicDynamics
open private dynamicsPair swappedPair from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
open private conjugationLinear from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private centralizes_onAlgebras centralizes_hasLimit
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable {G : AffineAlgebraicGroup F}
variable (q : QuadraticForm F V)
variable {I : Type u} [LinearOrder I] (b : Module.Basis I F V)
variable (ρ : ∀ R : TestAlgebra F, GroupPoints G.val R →* (ScalarClifford q R)ˣ)
variable (hρ : IsSpinPointRepresentation q G.val ρ)

private theorem weightedProduct_fixed {c : Cocharacter G.val} {i j : ℤ} {v w : V}
    (hv : HasSpinWeight q ρ c i v) (hw : HasSpinWeight q ρ c j w) (hz : i + j = 0)
    (R : TestAlgebra F) (s : Rˣ) :
    conjugate q R (ρ R (cocharacterPoint c R s))
      (vectors q R (vectorOver R v) * vectors q R (vectorOver R w)) =
        vectors q R (vectorOver R v) * vectors q R (vectorOver R w) := by
  rw [conjugationMul, hv R s, hw R s, smul_mul_assoc, mul_smul_comm,
    smul_smul, ← Units.val_mul, ← zpow_add, hz, zpow_zero, Units.val_one, one_smul]

include hρ in
private theorem commute_of_clifford_fixed (R : TestAlgebra F) (p g : GroupPoints G.val R)
    (h : conjugate q R (ρ R g) (ρ R p).val = (ρ R p).val) : Commute p g := by
  have H : ρ R g * ρ R p * (ρ R g)⁻¹ = ρ R p := Units.ext h
  exact (hρ.1 R).1 ((map_mul (ρ R) p g).trans
    ((mul_inv_eq_iff_eq_mul.mp H).symm.trans (map_mul (ρ R) g p).symm))

include hρ in
private theorem planeDiagonal_commutes {c d : Cocharacter G.val} (h : HyperbolicPair q)
    (hd : IsDiagonal q (dynamicsPair h) ρ d) {n : ℤ}
    (he : HasSpinWeight q ρ c n h.e) (hf : HasSpinWeight q ρ c (-n) h.f)
    (R : TestAlgebra F) (t s : Rˣ) :
    Commute (cocharacterPoint d R t) (cocharacterPoint c R s) := by
  apply commute_of_clifford_fixed q ρ hρ R
  let a := ρ R (cocharacterPoint c R s)
  rw [hd R t]
  change conjugationLinear q R a ((t : R) • (eVector q h R * fVector q h R) +
    (t⁻¹ : Rˣ).val • (fVector q h R * eVector q h R)) = _
  simp only [map_add, map_smul]
  change (t : R) • conjugate q R a (eVector q h R * fVector q h R) +
    (t⁻¹ : Rˣ).val • conjugate q R a (fVector q h R * eVector q h R) = _
  rw [weightedProduct_fixed q ρ he hf (by omega) R s,
    weightedProduct_fixed q ρ hf he (by omega) R s]
  rfl

include b hρ in
private theorem perpendicularWeight_eq_zero
    (hG : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G)
    (S : Specs.ClosedSubgroup G.val) (hS : Specs.Relative.MaximalSplitTori.IsMaximalSplitTorus S)
    (c : Cocharacter S.group) (hc : Specs.Relative.RelativeChambers.IsRegular S c)
    (h : HyperbolicPair q) (w : h.perpendicular) {n : ℤ}
    (he : HasSpinWeight q ρ (c ≫ S.inclusion) n h.e)
    (hf : HasSpinWeight q ρ (c ≫ S.inclusion) (-n) h.f)
    (hw : HasSpinWeight q ρ (c ≫ S.inclusion) (-n) w.val) :
    w.val = 0 := by
  let R := CommAlgCat.of F F
  let H := dynamicsPair h
  let W : perpendicularOver q H b R := ⟨vectorOver R w.val, by
    constructor
    · change (ExtendedForm q R b).polarBilin (vectorOver R h.e) (vectorOver R w.val) = 0
      rw [polar_over, show q.polarBilin h.e w.val = 0 from w.property.1, map_zero]
    · change (ExtendedForm q R b).polarBilin (vectorOver R h.f) (vectorOver R w.val) = 0
      rw [polar_over, show q.polarBilin h.f w.val = 0 from w.property.2, map_zero]⟩
  obtain ⟨d, hd⟩ := SpinHyperbolicDynamics.cocharacterExists q b H ρ hρ
  obtain ⟨g, hg, hdlim, _⟩ := (SpinHyperbolicDynamics.shearsContract q b H ρ d hρ hd).1 R W
  have hgC : Centralizes (c ≫ S.inclusion) g := by
    apply (centralizes_onAlgebras (c ≫ S.inclusion) g).2
    intro T f s
    apply commute_of_clifford_fixed q ρ hρ T
    rw [rep_value_natural q ρ hρ, hg]
    have hmap : coefficientMap q R f.hom (shearValue q H R W.val) =
        1 + vectors q T (vectorOver T h.e) * vectors q T (vectorOver T w.val) := by
      change coefficientMap q R f.hom
        (1 + vectors q R (vectorOver R h.e) * vectors q R (vectorOver R w.val)) = _
      simp only [map_add, map_one, map_mul, change_vector, change_vectorOver]
    rw [hmap]
    let a := ρ T (cocharacterPoint (c ≫ S.inclusion) T s)
    change conjugationLinear q T a (1 + _) = _
    rw [map_add]
    change conjugate q T a 1 +
      conjugate q T a (vectors q T (vectorOver T h.e) * vectors q T (vectorOver T w.val)) = _
    rw [conjugationOne, weightedProduct_fixed q ρ he hw (by omega) T s]
  have hgD := commutes_in_regularCentralizer hG S hS c hc d
    (planeDiagonal_commutes q ρ hρ h hd he hf) g hgC
  have := G.property.1
  have h1 : g = 1 := limitIsUnique d (centralizes_hasLimit d hgD) hdlim
  rw [h1, map_one, Units.val_one] at hg
  have hs : shearValue q H R W.val = shearValue q H R (0 : perpendicularOver q H b R).val := by
    rw [hg.symm]
    simp [shearValue]
  have hz := shear_parameter_injective q H b R hs
  have hz' : vectorOver R w.val = 0 := congrArg Subtype.val hz
  simpa [vectorOver] using congrArg (TensorProduct.lid F V) hz'

include b hρ in
private theorem nonisotropicPerpendicular [Infinite F] [Fintype I]
    (hG : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G)
    (hreg : Specs.Arithmetic.IsotropicSpinGeneration.IsRegular q) (h : HyperbolicPair q) :
    ∃ w : h.perpendicular, q w.val ≠ 0 := by
  let H := dynamicsPair h
  obtain ⟨d, hd⟩ := SpinHyperbolicDynamics.cocharacterExists q b H ρ hρ
  exact (SpinHyperbolicDynamics.noncentrality q b H hreg G ρ d hρ hd hG).1

end ZeroWeightShears

section AdaptedPlane

open scoped BigOperators
open private swappedPair perpendicularComponent
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
open Specs.Arithmetic.SpinHyperbolicDynamics (vectorOver)

variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable {G : AffineAlgebraicGroup F}
variable (q : QuadraticForm F V)
variable {I : Type u} [LinearOrder I] (b : Module.Basis I F V)
variable (ρ : ∀ R : TestAlgebra F, GroupPoints G.val R →* (ScalarClifford q R)ˣ)
variable (hρ : IsSpinPointRepresentation q G.val ρ)
variable {cG : Cocharacter G.val}

private theorem HasSpinWeight.sum {J : Type u} (indices : Finset J) {n : ℤ} (v : J → V)
    (hv : ∀ j ∈ indices, HasSpinWeight q ρ cG n (v j)) :
    HasSpinWeight q ρ cG n (∑ j ∈ indices, v j) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using HasSpinWeight.zero q ρ cG n
  | insert j indices hj ih =>
    rw [Finset.sum_insert hj]
    exact HasSpinWeight.add q ρ (hv j (Finset.mem_insert_self _ _))
      (ih (fun k hk => hv k (Finset.mem_insert_of_mem hk)))

private theorem HasSpinWeight.sub {n : ℤ} {v w : V}
    (hv : HasSpinWeight q ρ cG n v) (hw : HasSpinWeight q ρ cG n w) :
    HasSpinWeight q ρ cG n (v - w) := by
  simpa only [neg_one_smul, sub_eq_add_neg] using
    HasSpinWeight.add q ρ hv (HasSpinWeight.smul q ρ hw (-1))

include b hρ in
private theorem exists_spinWeightBasis (cG : Cocharacter G.val) :
    ∃ (J : Type u) (B : Module.Basis J F V) (ν : J → ℤ),
      ∀ j, HasSpinWeight q ρ cG (ν j) (B j) := by
  let E : Set V := {v | ∃ n : ℤ, HasSpinWeight q ρ cG n v}
  have span : (⊤ : Submodule F V) ≤ Submodule.span F E := by
    intro v _
    obtain ⟨w, hsum, hw⟩ := spinWeight_decomposition q b ρ hρ cG v
    rw [hsum]
    exact Submodule.sum_mem _ fun j hj => Submodule.subset_span ⟨j, hw j hj⟩
  let B := Module.Basis.ofSpan span
  choose ν hν using (fun j => show ∃ n, HasSpinWeight q ρ cG n (B j) from
    Module.Basis.ofSpan_subset span (Set.mem_range_self j))
  exact ⟨_, B, ν, hν⟩

include b hρ in
private theorem maximalWeightPair {J : Type u} [Fintype J]
    (hreg : Specs.Arithmetic.IsotropicSpinGeneration.IsRegular q)
    (B : Module.Basis J F V) (ν : J → ℤ)
    (hν : ∀ j, HasSpinWeight q ρ cG (ν j) (B j)) (hnz : ∃ j, ν j ≠ 0)
    (s : Fˣ) (hs : Function.Injective (fun n : ℤ => (s ^ n).val)) :
    ∃ (h : HyperbolicPair q) (n : ℤ), 0 < n ∧ (∀ j, ν j ≤ n) ∧
      HasSpinWeight q ρ cG n h.e ∧ HasSpinWeight q ρ cG (-n) h.f := by
  classical
  obtain ⟨k, hk⟩ := hnz
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => (ν j).natAbs)
    ⟨k, Finset.mem_univ k⟩
  have habs (j : J) : (ν j).natAbs ≤ (ν i).natAbs := hmax j (Finset.mem_univ j)
  have hi : ν i ≠ 0 := by
    intro hi
    have h := habs k
    rw [hi, Int.natAbs_zero, Nat.le_zero, Int.natAbs_eq_zero] at h
    exact hk h
  have hei : q (B i) = 0 := spinWeight_isotropic q b ρ hρ (hν i) s hs hi
  obtain ⟨H, hE⟩ := IsotropicSpinGeneration.hyperbolicPairExistence q hreg (B i)
    (B.ne_zero i) hei
  have hp : ∃ j, q.polarBilin (B i) (B j) ≠ 0 := by
    by_contra! hz
    have hh : q.polarBilin (B i) = 0 := B.ext (fun j => hz j)
    have hf := congrArg (fun l : V →ₗ[F] F => l H.f) hh
    change q.polarBilin (B i) H.f = 0 at hf
    rw [← hE, H.polar_ef] at hf
    exact one_ne_zero hf
  obtain ⟨j, hj⟩ := hp
  have hji : ν j = -(ν i) := by
    by_contra h
    exact hj (spinWeights_polar q b ρ hρ (hν i) (hν j) s hs (by omega))
  have hfj : q (B j) = 0 :=
    spinWeight_isotropic q b ρ hρ (hν j) s hs (by omega)
  let a := q.polarBilin (B i) (B j)
  let h : HyperbolicPair q := ⟨B i, a⁻¹ • B j, hei,
    by rw [QuadraticMap.map_smul, hfj, smul_zero],
    by rw [map_smul, smul_eq_mul, show q.polarBilin (B i) (B j) = a from rfl, inv_mul_cancel₀ hj]⟩
  have he : HasSpinWeight q ρ cG (ν i) h.e := hν i
  have hf : HasSpinWeight q ρ cG (-(ν i)) h.f := by
    rw [← hji]
    exact HasSpinWeight.smul q ρ (hν j) a⁻¹
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · refine ⟨swappedPair h, -(ν i), neg_pos.mpr hneg, fun j' => ?_, hf, ?_⟩
    · exact Int.le_natAbs.trans (by
        rw [← Int.ofNat_natAbs_of_nonpos hneg.le]
        exact_mod_cast habs j')
    · change HasSpinWeight q ρ cG (-(-(ν i))) h.e
      rwa [neg_neg]
  · refine ⟨h, ν i, hpos, fun j' => ?_, he, hf⟩
    exact Int.le_natAbs.trans (by
      rw [← Int.natAbs_of_nonneg hpos.le]
      exact_mod_cast habs j')

include b hρ in
private theorem perpendicularComponent_weight (h : HyperbolicPair q) {n m : ℤ} {v : V}
    (he : HasSpinWeight q ρ cG n h.e) (hf : HasSpinWeight q ρ cG (-n) h.f)
    (hv : HasSpinWeight q ρ cG m v)
    (s : Fˣ) (hs : Function.Injective (fun n : ℤ => (s ^ n).val)) :
    HasSpinWeight q ρ cG m (perpendicularComponent q h v).val := by
  change HasSpinWeight q ρ cG m
    (v - q.polarBilin h.f v • h.e - q.polarBilin h.e v • h.f)
  have he' : HasSpinWeight q ρ cG m (q.polarBilin h.f v • h.e) := by
    by_cases hn : m = n
    · exact hn.symm ▸ HasSpinWeight.smul q ρ he _
    · have hz := spinWeights_polar q b ρ hρ hf hv s hs (by omega)
      rw [hz, zero_smul]
      exact HasSpinWeight.zero q ρ cG m
  have hf' : HasSpinWeight q ρ cG m (q.polarBilin h.e v • h.f) := by
    by_cases hn : m = -n
    · exact hn.symm ▸ HasSpinWeight.smul q ρ hf _
    · have hz := spinWeights_polar q b ρ hρ he hv s hs (by omega)
      rw [hz, zero_smul]
      exact HasSpinWeight.zero q ρ cG m
  exact HasSpinWeight.sub q ρ (HasSpinWeight.sub q ρ hv he') hf'

end AdaptedPlane

section ContractingLine

open scoped BigOperators
open Specs.Arithmetic.SpinHyperbolicDynamics (vectorOver)
open private swappedPair perpendicularComponent
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration

set_option maxHeartbeats 1000000 in
private theorem adaptedHyperbolicPair {F V : Type u}
    [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {G : AffineAlgebraicGroup F}
    (q : QuadraticForm F V)
    {I : Type u} [LinearOrder I] [Fintype I] (b : Module.Basis I F V)
    (ρ : ∀ R : TestAlgebra F, GroupPoints G.val R →* (ScalarClifford q R)ˣ)
    (hG : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G)
    (hreg : Specs.Arithmetic.IsotropicSpinGeneration.IsRegular q)
    (hiso : Specs.Arithmetic.IsotropicSpinGeneration.IsIsotropic q)
    (hρ : IsSpinPointRepresentation q G.val ρ)
    (S : Specs.ClosedSubgroup G.val) (hS : Specs.Relative.MaximalSplitTori.IsMaximalSplitTorus S)
    (c : Cocharacter S.group) (hc : Specs.Relative.RelativeChambers.IsRegular S c) :
    ∃ (h : HyperbolicPair q) (w : h.perpendicular), q w.val ≠ 0 ∧
      ∀ (x : F) (g : GroupPoints G.val (CommAlgCat.of F F)),
        (ρ (CommAlgCat.of F F) g).val =
          cliffordMatrix q h w (CommAlgCat.of F F) (lower x).val →
        HasLimit (oppositeCocharacter (c ≫ S.inclusion)) g 1 := by
  classical
  let := localField_infinite F
  let cG := c ≫ S.inclusion
  obtain ⟨s, hs⟩ := exists_distinct_unit_powers (F := F)
  obtain ⟨J, B, ν, hν⟩ := exists_spinWeightBasis q b ρ hρ cG
  let : Fintype J := FiniteDimensional.fintypeBasisIndex B
  have hnz : ∃ j, ν j ≠ 0 := by
    by_contra! hz
    have hv (v : V) : HasSpinWeight q ρ cG 0 v := by
      rw [← B.sum_repr v]
      apply HasSpinWeight.sum q ρ
      intro j _
      exact HasSpinWeight.smul q ρ (by simpa only [hz j] using hν j) (B.repr v j)
    obtain ⟨e, he0, heq⟩ := hiso
    obtain ⟨h, _⟩ := IsotropicSpinGeneration.hyperbolicPairExistence q hreg e he0 heq
    obtain ⟨w, hw⟩ := nonisotropicPerpendicular q b ρ hρ hG hreg h
    have hw0 := perpendicularWeight_eq_zero q b ρ hρ hG S hS c hc h w
      (n := 0) (hv _) (by simpa only [neg_zero] using hv h.f)
      (by simpa only [neg_zero] using hv w.val)
    exact hw (by simp [hw0])
  obtain ⟨h, n, hn, hνle, he, hf⟩ := maximalWeightPair q b ρ hρ hreg B ν hν hnz s hs
  obtain ⟨w, hw⟩ := nonisotropicPerpendicular q b ρ hρ hG hreg h
  let π : V →ₗ[F] V :=
    LinearMap.id - (q.polarBilin h.f).smulRight h.e - (q.polarBilin h.e).smulRight h.f
  let component (j : J) : h.perpendicular := perpendicularComponent q h ((B.repr w.val j) • B j)
  have hcomponent (j : J) : HasSpinWeight q ρ cG (ν j) (component j).val :=
    perpendicularComponent_weight q b ρ hρ h he hf
      (HasSpinWeight.smul q ρ (hν j) (B.repr w.val j)) s hs
  have hzero (j : J) (hj : ν j = n) : (component j).val = 0 := by
    let h' := swappedPair h
    let w' : h'.perpendicular :=
      ⟨(component j).val, (component j).property.2, (component j).property.1⟩
    exact perpendicularWeight_eq_zero q b ρ hρ hG S hS c hc h' w' (n := -n)
      hf (by
        change HasSpinWeight q ρ cG (-(-n)) h.e
        rwa [neg_neg])
      (by
        change HasSpinWeight q ρ cG (-(-n)) (component j).val
        rw [neg_neg, ← hj]
        exact hcomponent j)
  let indices : Finset J := Finset.univ.filter fun j => ν j < n
  have hsum : w.val = ∑ j ∈ indices, (component j).val := by
    have hwπ : w.val = π w.val := by
      change w.val = w.val - q.polarBilin h.f w.val • h.e - q.polarBilin h.e w.val • h.f
      rw [show q.polarBilin h.f w.val = 0 from w.property.2,
        show q.polarBilin h.e w.val = 0 from w.property.1, zero_smul, zero_smul, sub_zero, sub_zero]
    calc
      w.val = π w.val := hwπ
      _ = ∑ j, (component j).val := by
        change π w.val = ∑ j, π ((B.repr w.val j) • B j)
        rw [← map_sum, B.sum_repr]
      _ = ∑ j ∈ indices, (component j).val := by
        dsimp only [indices]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs with hj
        · rfl
        · exact hzero j (by have hle := hνle j; omega)
  refine ⟨h, w, hw, fun x g hg => ?_⟩
  let K := CommAlgCat.of F F
  let a : F := x * (-((q w.val)⁻¹))
  let u (j : J) := a • (component j).val
  have hw' : (ρ K g).val = 1 + fVector q h K * vectors q K
      (vectorOver K (∑ j ∈ indices, u j)) := by
    have h := hg.trans (lowerCliffordValue q h w b K x)
    have hsum' : (∑ j ∈ indices, u j) = a • w.val := by
      change (∑ j ∈ indices, a • (component j).val) = _
      rw [← Finset.smul_sum]
      exact congrArg (a • ·) hsum.symm
    rw [hsum', constantVector_smul]
    exact h
  have hF : HasSpinWeight q ρ (oppositeCocharacter cG) n h.f := by
    simpa only [neg_neg] using HasSpinWeight.opposite q ρ hf
  apply weightedShear_hasLimit q b ρ hρ (oppositeCocharacter cG) h.q_f hF
    indices (fun j => -(ν j)) u _ _ _ hw'
  · intro j hj
    change q.polarBilin h.f (a • (component j).val) = 0
    rw [map_smul, show q.polarBilin h.f (component j).val = 0 from (component j).property.2,
      smul_zero]
  · intro j _
    exact HasSpinWeight.smul q ρ (HasSpinWeight.opposite q ρ (hcomponent j)) a
  · intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    omega

end ContractingLine

theorem quadraticSpinRankOne :
    Specs.Arithmetic.LocalMixingQuadraticSpinRankOne.Statement.{u} := by
  classical
  intro F _ _ _ _ G hG V _ _ _ q ρ _hdim hreg hiso hρ S hS c hc
  let := localField_infinite F
  let b := (Module.finBasis F V).reindex
    (Equiv.ulift.symm : Fin (Module.finrank F V) ≃ ULift.{u} (Fin (Module.finrank F V)))
  obtain ⟨h, w, hw, hcontract⟩ :=
    adaptedHyperbolicPair q b ρ hG hreg hiso hρ S hS c hc
  obtain ⟨A, j, hj, e, hm⟩ := cliffordRankOneEmbedding q h w b ρ hw hρ
  obtain ⟨d, hd, _, _, hgen⟩ :=
    IsotropicSpinGeneration.localSpinGeneration q b G ρ hρ hreg hG h
  obtain ⟨dA, hdA, hdiagonal⟩ := diagonalLift q h w b ρ j hj e hw hρ hm d hd
  refine ⟨h, w, hw, A, j, hj, e, dA, hm, ?_, ?_, Or.inr ?_, ?_⟩
  · intro R t
    exact congrArg (fun M : SLTwo R => M.val) (hdiagonal R t)
  · intro R x
    rw [hdA]
    obtain ⟨D⟩ := existsLimitDecomposition G d
    obtain ⟨E⟩ := existsLimitDecomposition G (oppositeCocharacter d)
    exact ⟨((hgen D E).1 R _).1 (upperShearPoint q h w b ρ R x (hm R (upper x))),
      ((hgen D E).1 R _).2 (lowerShearPoint q h w b ρ R x (hm R (lower x)))⟩
  · exact fun x => hcontract x _ (hm (CommAlgCat.of F F) (lower x))
  · let R := CommAlgCat.of F F
    let : TopologicalSpace (GroupPoints G.val R) :=
      LocalAlgebraicTransport.pointTopology G.val.X
    change Dense (Subgroup.closure ({g : GroupPoints G.val R | HasLimit (dA ≫ j) g 1} ∪
      {g : GroupPoints G.val R | HasLimit (oppositeCocharacter (dA ≫ j)) g 1}) :
        Set (GroupPoints G.val R))
    rw [hdA, oppositeLimits_generate d (fun D E => (hgen D E).2.2), Subgroup.coe_top]
    exact dense_univ

end

end LinearAlgebraicGroups.Arithmetic.LocalMixingQuadraticSpinRankOne
