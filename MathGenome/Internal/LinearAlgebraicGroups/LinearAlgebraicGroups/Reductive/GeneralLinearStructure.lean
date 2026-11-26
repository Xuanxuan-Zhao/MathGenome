import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeneralLinearStructure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DerivedSubgroup
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.LieKolchin
import Mathlib.RingTheory.Localization.BaseChange
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Basis.Flag

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct commutatorElement

universe u

namespace LinearAlgebraicGroups.GeneralLinearStructure

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option maxHeartbeats 260000

open _root_.LinearAlgebraicGroups.Specs Specs.GeneralLinearStructure
open Specs.Unipotent (Index)
open Matrix

private theorem eq_diagonal_of_isDiagonal {R : Type u} [CommRing R] {n : ℕ}
    {g : Matrix.GeneralLinearGroup (Index.{u} n) R} (h : IsDiagonal g) :
    g.val = diagonal (fun i => g.val i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [h i j hij, diagonal_apply_ne _ hij]

/-- Test an off-diagonal entry using a diagonal unit with a Laurent variable at one index. -/
theorem diagonalCentralizerMatrices : DiagonalCentralizerMatrices.{u} := by
  intro k _ n R g
  constructor
  · intro h A f d hd
    apply Units.ext
    change g.val.map f.hom * d.val = d.val * g.val.map f.hom
    rw [eq_diagonal_of_isDiagonal h, eq_diagonal_of_isDiagonal hd, diagonal_map (map_zero f.hom)]
    exact (commute_diagonal _ _).eq
  · intro h i j hij
    let B := LaurentPolynomial R
    letI : Algebra R B := inferInstance
    letI : Algebra k B := ((algebraMap R B).comp (algebraMap k R)).toAlgebra
    let A : TestAlgebra k := CommAlgCat.of k B
    let f : R ⟶ A := CommAlgCat.ofHom
      { toRingHom := LaurentPolynomial.C
        commutes' := fun _ => rfl }
    let t : Bˣ := (LaurentPolynomial.isUnit_T (R := R) 1).unit
    let d : Matrix.GeneralLinearGroup (Index.{u} n) B :=
      Units.map (diagonalRingHom _ _).toMonoidHom
        ((MulEquiv.piUnits).symm (fun a => if a = j then t else 1))
    have hd : d.val = diagonal (fun a => if a = j then (t : B) else 1) := by
      apply congrArg diagonal
      funext a
      by_cases ha : a = j <;> simp [ha]
    have hz : IsDiagonal d := fun a b hab => by rw [hd, diagonal_apply_ne _ hab]
    have hcomm := congrArg (fun M : Matrix.GeneralLinearGroup (Index.{u} n) B => M.val i j)
      (h A f d hz)
    change ((g.val.map LaurentPolynomial.C) * d.val) i j =
      (d.val * (g.val.map LaurentPolynomial.C)) i j at hcomm
    rw [hd, mul_diagonal, diagonal_mul] at hcomm
    simp only [ite_true, ite_eq_right hij, Matrix.map_apply, one_mul] at hcomm
    rw [IsUnit.unit_spec, ← LaurentPolynomial.single_eq_C_mul_T] at hcomm
    have hc := congrArg (fun x : B => x.coeff 1) hcomm
    change (AddMonoidAlgebra.single (1 : ℤ) (g.val i j)).coeff 1 =
      (LaurentPolynomial.C (g.val i j)).coeff 1 at hc
    simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
      LaurentPolynomial.C_apply, one_ne_zero, ite_false] using hc

/-- Commuting with elementary transvections determines the scalar matrices over any ring. -/
theorem scalarCenterMatrices : ScalarCenterMatrices.{u} := by
  intro n hn R _ g
  constructor
  · intro h
    have he (i j : Index.{u} n) (hij : i ≠ j) :
        g.val * single i j (1 : R) = single i j 1 * g.val := by
      let a : Matrix.SpecialLinearGroup (Index.{u} n) R :=
        Matrix.SpecialLinearGroup.transvection hij 1
      have hm := congrArg Units.val (h (Matrix.SpecialLinearGroup.toGL a))
      change g.val * (1 + single i j 1) = (1 + single i j 1) * g.val at hm
      exact add_left_cancel (by simpa only [mul_add, add_mul, mul_one, one_mul] using hm)
    have hoff : IsDiagonal g := by
      intro i j hij
      have hh := congrArg (fun M : Matrix (Index.{u} n) (Index.{u} n) R => M i i)
        (he j i hij.symm)
      simpa [mul_single_apply_same, single_mul_apply_of_ne _ j i i i hij] using hh
    have hdiag (i j : Index.{u} n) : g.val i i = g.val j j := by
      by_cases hij : i = j
      · subst j
        rfl
      · have hh := congrArg (fun M : Matrix (Index.{u} n) (Index.{u} n) R => M i j)
          (he i j hij)
        simpa [mul_single_apply_same, single_mul_apply_same] using hh
    let i : Index.{u} n := ⟨⟨0, hn⟩⟩
    have hs : g.val = scalar _ (g.val i i) := by
      rw [eq_diagonal_of_isDiagonal hoff, scalar_apply]
      exact congrArg diagonal (funext fun j => hdiag j i)
    have hu : IsUnit (g.val i i) := by
      have hh := congrArg (fun M : Matrix (Index.{u} n) (Index.{u} n) R => M i i)
        g.val_inv
      rw [hs, scalar_apply, diagonal_mul, one_apply_eq] at hh
      exact IsUnit.of_mul_eq_one _ hh
    exact ⟨hu.unit, by rw [hu.unit_spec, ← hs]⟩
  · rintro ⟨a, ha⟩ h
    apply Units.ext
    change g.val * h.val = h.val * g.val
    rw [ha]
    exact (scalar_commute _ (fun _ => Commute.all _ _) _).eq

private theorem principal_open_geometry {k : Type u} [Field k] {σ : Type u} [Finite σ]
    (d : MvPolynomial σ k) (hd : d ≠ 0) :
    let X := (testSpec k).obj (op (CommAlgCat.of k (Localization.Away d)))
    Smooth X.hom ∧ GeometricallyConnected X.hom := by
  let P := MvPolynomial σ k
  let A := Localization.Away d
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A))) ∧
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  constructor
  · apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    apply RingHom.smooth_algebraMap.mpr
    change Algebra.Smooth k (Localization.Away d)
    haveI : Algebra.Smooth k P := inferInstance
    haveI : Algebra.Smooth P (Localization.Away d) := inferInstance
    exact Algebra.Smooth.comp k P (Localization.Away d)
  · constructor
    apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
      (P := fun X : Scheme.{u} => ConnectedSpace X)).mpr
    intro K _ _
    let e : K ⊗[k] P ≃ₐ[K] MvPolynomial σ K :=
      MvPolynomial.algebraTensorAlgEquiv k K
    letI : IsDomain (K ⊗[k] P) := MulEquiv.isDomain _ e.toRingEquiv.toMulEquiv
    have hd' : ((1 : K) ⊗ₜ[k] d) ≠ 0 := by
      intro h
      have he : e (1 ⊗ₜ[k] d) = MvPolynomial.map (algebraMap k K) d := by
        rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
      apply hd
      apply MvPolynomial.map_injective _ (algebraMap k K).injective
      rw [← he, h, map_zero, map_zero]
    let l : K ⊗[k] A ≃ₐ[K] Localization.Away ((1 : K) ⊗ₜ[k] d) :=
      IsLocalization.Away.tensorProductEquivTMulRight k K d A
    haveI : IsDomain (Localization.Away ((1 : K) ⊗ₜ[k] d)) := Localization.Away.isDomain hd'
    letI : IsDomain (K ⊗[k] A) := MulEquiv.isDomain _ l.toRingEquiv.toMulEquiv
    let h := (CommRingCat.isPushout_tensorProduct k K A).op.map Scheme.Spec
    exact (h.isoPullback.hom.homeomorph.connectedSpace_iff).mp
      (inferInstance : ConnectedSpace (Spec (CommRingCat.of (K ⊗[k] A))))

/-- The determinant principal open is smooth and geometrically connected. -/
theorem generalLinearGeometry : GeneralLinearGeometry.{u} := by
  intro k _ n
  let ι := Index.{u} n
  let d := StandardGroups.genericDeterminant k ι
  let P := MvPolynomial (ι × ι) k
  apply principal_open_geometry d
  intro hd
  let f : P →ₐ[k] k := MvPolynomial.aeval (fun ij : ι × ι => (1 : Matrix ι ι k) ij.1 ij.2)
  have heval : f.mapMatrix (StandardGroups.genericMatrix k ι) = 1 := by
    ext i j
    exact MvPolynomial.aeval_X _ (i, j)
  have hd1 : f d = 1 := by
    change f (StandardGroups.genericMatrix k ι).det = 1
    rw [AlgHom.map_det, heval, det_one]
  have hzero : f d = 0 := by rw [hd, map_zero]
  exact one_ne_zero (hd1.symm.trans hzero)

section DerivedMatrices

variable {K : Type u} [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι]

open Matrix.SpecialLinearGroup (diag2n diag2n_coe)

private abbrev elementary (i j : ι) (hij : i ≠ j) (a : K) :
    Matrix.SpecialLinearGroup ι K :=
  Matrix.SpecialLinearGroup.transvection hij a

private def transvectionWord (i j : ι) (hij : i ≠ j) (a : K) :
    Matrix.SpecialLinearGroup ι K :=
  elementary i j hij a * elementary j i hij.symm (-a⁻¹) * elementary i j hij a

private theorem transvectionWord_entry (i j : ι) (hij : i ≠ j) (a : K) (ha : a ≠ 0) :
    (transvectionWord i j hij a).val =
      diagonal (fun r => if r = i ∨ r = j then 0 else 1) +
        single i j a + single j i (-a⁻¹) := by
  change ((1 + single i j a) * (1 + single j i (-a⁻¹)) *
    (1 + single i j a)) = _
  have h1 : a * (-a⁻¹) = -1 := by simp [ha]
  have h2 : (-a⁻¹) * a = -1 := by simp [ha]
  have hzero : single i j a * single i j a = 0 :=
    single_mul_single_of_ne a i j i hij.symm a
  simp only [Matrix.mul_add, Matrix.add_mul, one_mul, mul_one, single_mul_single_same,
    hzero, h1, h2, neg_one_mul, add_zero]
  have hdiag : (1 : Matrix ι ι K) + single i i (-1) + single j j (-1) =
      diagonal (fun r => if r = i ∨ r = j then 0 else 1) := by
    ext r c
    by_cases hrc : r = c
    · subst c
      by_cases hr : r = i <;> by_cases hr' : r = j
      <;> simp_all [Matrix.single, eq_comm]
    · have hi : ¬(i = r ∧ i = c) := fun ⟨h, h'⟩ => h.symm.trans h' |> hrc
      have hj : ¬(j = r ∧ j = c) := fun ⟨h, h'⟩ => h.symm.trans h' |> hrc
      simp [Matrix.single, one_apply, hrc, hi, hj]
  rw [← hdiag, ← single_neg i j a]
  abel

private theorem diag2n_mul_word (i j : ι) (hij : i ≠ j) (a : K) (ha : a ≠ 0) :
    diag2n hij a ha * transvectionWord i j hij (1 : K) = transvectionWord i j hij a := by
  apply Subtype.ext
  change (diag2n hij a ha).val * (transvectionWord i j hij (1 : K)).val = _
  rw [diag2n_coe, transvectionWord_entry _ _ _ 1 one_ne_zero,
    transvectionWord_entry _ _ _ a ha]
  ext r c
  rw [diagonal_mul]
  by_cases hr : r = i
  · subst r
    by_cases hc : c = j <;> simp [hij, hij.symm, hc, Ne.symm, Matrix.single, diagonal_apply]
  · by_cases hr' : r = j
    · subst r
      by_cases hc : c = i <;> simp [hij, hij.symm, hc, Ne.symm, Matrix.single, diagonal_apply]
    · simp [hr, hr', Ne.symm, Matrix.single, diagonal_apply]

private theorem elementary_mem_commutator [IsAlgClosed K] (i j : ι) (hij : i ≠ j) (a : K) :
    Matrix.SpecialLinearGroup.toGL (elementary i j hij a) ∈
      commutator (Matrix.GeneralLinearGroup ι K) := by
  classical
  obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset K)
  have hr0 : r ≠ 0 := fun h => hr (h ▸ Finset.mem_insert_self _ _)
  have hr1 : r ≠ 1 := fun h => hr (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  let d : ι → Kˣ := fun s => if s = i then Units.mk0 r hr0 else 1
  let D : Matrix.GeneralLinearGroup ι K :=
    Units.map (diagonalRingHom ι K).toMonoidHom ((MulEquiv.piUnits).symm d)
  let b := a / (r - 1)
  let T := Matrix.SpecialLinearGroup.toGL (elementary i j hij b)
  let U := Matrix.SpecialLinearGroup.toGL (elementary i j hij a)
  have hb : r * b = a + b := by
    have hb' : (r - 1) * b = a := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ (sub_ne_zero.mpr hr1)
    rw [sub_mul, one_mul, sub_eq_iff_eq_add] at hb'
    exact hb'
  have hDT : D * T = (U * T) * D := by
    rw [← map_mul, show elementary i j hij a * elementary i j hij b =
      elementary i j hij (a + b) from Subtype.ext (transvection_mul_transvection_same i j hij a b)]
    apply Units.ext
    change diagonal (fun s => (d s : K)) * (1 + single i j b) =
      (1 + single i j (a + b)) * diagonal (fun s => (d s : K))
    rw [Matrix.mul_add, Matrix.add_mul, mul_one, one_mul]
    congr 1
    ext s t
    rw [diagonal_mul, mul_diagonal]
    by_cases hs : s = i
    · subst s
      by_cases ht : t = j
      · subst t
        simpa [d, Matrix.single, hij.symm] using hb
      · simp [Matrix.single, Ne.symm ht]
    · simp [Matrix.single, Ne.symm hs]
  change U ∈ commutator _
  rw [← show ⁅D, T⁆ = U by
    rw [commutatorElement_def, hDT, mul_inv_cancel_right, mul_inv_cancel_right]]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem determinantOne_mem_commutator [IsAlgClosed K]
    (g : Matrix.SpecialLinearGroup ι K) :
    Matrix.SpecialLinearGroup.toGL g ∈ commutator (Matrix.GeneralLinearGroup ι K) := by
  by_cases hi : Subsingleton ι
  · have hg : g = 1 := by
      apply Subtype.ext
      ext i j
      obtain rfl := Subsingleton.elim i j
      haveI : Unique ι := ⟨⟨i⟩, fun b => Subsingleton.elim b i⟩
      simpa [Matrix.det_unique, show (default : ι) = i from Subsingleton.elim _ _] using g.property
    rw [hg, map_one]
    exact one_mem _
  · letI : Nontrivial ι := not_subsingleton_iff_nontrivial.mp hi
    let H := commutator (Matrix.GeneralLinearGroup ι K)
    have hword (i j : ι) (hij : i ≠ j) (a : K) :
        Matrix.SpecialLinearGroup.toGL (transvectionWord i j hij a) ∈ H := by
      rw [transvectionWord, map_mul, map_mul]
      exact H.mul_mem (H.mul_mem (elementary_mem_commutator _ _ hij _)
        (elementary_mem_commutator _ _ hij.symm _)) (elementary_mem_commutator _ _ hij _)
    apply Matrix.SpecialLinearGroup.diagonal_transvection_induction'
      (fun x => Matrix.SpecialLinearGroup.toGL x ∈ H) g
    · intro i j hij a ha
      have hh := congrArg Matrix.SpecialLinearGroup.toGL (diag2n_mul_word i j hij a ha)
      rw [map_mul] at hh
      rw [← mul_inv_cancel_right (Matrix.SpecialLinearGroup.toGL (diag2n hij a ha))
        (Matrix.SpecialLinearGroup.toGL (transvectionWord i j hij 1)), hh]
      exact H.mul_mem (hword i j hij a) (H.inv_mem (hword i j hij 1))
    · exact elementary_mem_commutator
    · intro x y hx hy
      rw [map_mul]
      exact H.mul_mem hx hy

theorem generalLinearGeometricCommutator : GeneralLinearGeometricCommutator.{u} := by
  intro K _ _ n _
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  · intro g hg
    let x : Matrix.SpecialLinearGroup (Index.{u} n) K :=
      ⟨g.val, congrArg Units.val (MonoidHom.mem_ker.mp hg)⟩
    have hx : Matrix.SpecialLinearGroup.toGL x = g := Units.ext rfl
    rw [← hx]
    exact determinantOne_mem_commutator x

end DerivedMatrices


section SchemeGeometry

variable {k : Type u} [Field k]

open private StandardGroups.universalGeneralLinear StandardGroups.slEvaluation
  StandardGroups.slEvaluation_entry StandardGroups.glCoordinates_ext StandardGroups.quotient_det
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private Unipotent.groupIsoOfPoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Criteria

private theorem smooth_of_groupIso {G H : GroupScheme k} (e : G ≅ H)
    (h : Smooth H.X.hom) : Smooth G.X.hom := by
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget _
  have he : IsIso e.hom.hom.hom.left := inferInstanceAs (IsIso (F.map e.hom))
  rw [← e.hom.hom.hom.w]
  exact smooth_comp _ _

private theorem geometricallyConnected_of_groupIso {G H : GroupScheme k} (e : G ≅ H)
    (h : GeometricallyConnected H.X.hom) : GeometricallyConnected G.X.hom := by
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget _
  have he : IsIso e.hom.hom.hom.left := inferInstanceAs (IsIso (F.map e.hom))
  rw [← e.hom.hom.hom.w]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyConnected)
    e.hom.hom.hom.left H.X.hom).mpr h

private theorem gl_geometry {n : ℕ} {G : AffineAlgebraicGroup k} (e : MatrixPoints G n) :
    Smooth G.val.X.hom ∧ GeometricallyConnected G.val.X.hom := by
  let c := StandardGroups.generalLinearGroupPointsIso k (Index.{u} n)
  let i : G.val ≅ (StandardGroups.generalLinearGroup k (Index.{u} n)).val :=
    Unipotent.groupIsoOfPoints (e ≪≫ c.symm)
  have h := generalLinearGeometry k n
  exact ⟨smooth_of_groupIso i h.1, geometricallyConnected_of_groupIso i h.2⟩

private def diagonalAt {ι R : Type u} [Fintype ι] [DecidableEq ι] [CommRing R]
    (i : ι) (a : Rˣ) : Matrix.GeneralLinearGroup ι R :=
  Units.map (diagonalRingHom ι R).toMonoidHom
    ((MulEquiv.piUnits).symm (fun j => if j = i then a else 1))

private theorem diagonalAt_val {ι R : Type u} [Fintype ι] [DecidableEq ι] [CommRing R]
    (i : ι) (a : Rˣ) : (diagonalAt i a).val = diagonal (fun j => if j = i then (a : R) else 1) := by
  apply congrArg diagonal
  funext j
  by_cases h : j = i <;> simp [h]

private theorem det_diagonalAt {ι R : Type u} [Fintype ι] [DecidableEq ι] [CommRing R]
    (i : ι) (a : Rˣ) : Matrix.GeneralLinearGroup.det (diagonalAt i a) = a := by
  apply Units.ext
  change (diagonalAt i a).val.det = (a : R)
  rw [diagonalAt_val, det_diagonal, Finset.prod_ite_eq', ite_eq_left (Finset.mem_univ _)]

/-- Dividing one row by the determinant retracts the determinant open onto its
determinant-one fibre. The split quotient inherits infinitesimal lifting. -/
private theorem sl_coordinates_smooth (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Algebra.Smooth k (StandardGroups.SLCoordinates k ι) := by
  classical
  let A := StandardGroups.GLCoordinates k ι
  let S := StandardGroups.SLCoordinates k ι
  let q : A →ₐ[k] S := Ideal.Quotient.mkₐ k (StandardGroups.determinantOneIdeal k ι)
  let i : ι := Classical.choice ‹Nonempty ι›
  let M : Matrix.GeneralLinearGroup ι A := StandardGroups.universalGeneralLinear
  let t := Matrix.GeneralLinearGroup.det M
  let D := diagonalAt i t⁻¹
  have hW : Matrix.GeneralLinearGroup.det (D * M) = 1 := by
    rw [map_mul, det_diagonalAt, inv_mul_cancel]
  let w : Matrix.SpecialLinearGroup ι A := ⟨(D * M).val, congrArg Units.val hW⟩
  let l : S →ₐ[k] A := StandardGroups.slEvaluation w
  have hq : q.comp l = AlgHom.id k S := by
    apply Ideal.Quotient.algHom_ext k
    apply StandardGroups.glCoordinates_ext
    intro a b
    change q (l (q (Specs.StandardGroups.universalMatrix k ι a b))) =
      q (Specs.StandardGroups.universalMatrix k ι a b)
    rw [StandardGroups.slEvaluation_entry]
    change q ((D.val * M.val) a b) = q (M.val a b)
    rw [diagonalAt_val, diagonal_mul, map_mul]
    have hqt : q (t : A) = 1 := StandardGroups.quotient_det
    have hqi : q ((t⁻¹ : Aˣ) : A) = 1 := by
      change q t.inv = 1
      have hh := congrArg q t.val_inv
      simpa only [map_mul, hqt, one_mul, map_one] using hh
    by_cases ha : a = i <;> simp [ha, hqi]
  let P := MvPolynomial (ι × ι) k
  let d := Specs.StandardGroups.genericDeterminant k ι
  have hsA : Algebra.Smooth k A :=
    Algebra.Smooth.comp k P (Localization.Away d)
  have hfin : Algebra.FiniteType k S :=
    Algebra.FiniteType.of_surjective q Ideal.Quotient.mk_surjective
  refine ⟨Algebra.FormallySmooth.of_comp_surjective (fun B _ _ I hI f => ?_), (Algebra.FinitePresentation.of_finiteType.mp hfin)⟩
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective k A I hI (f.comp q)
  refine ⟨g.comp l, ?_⟩
  rw [← AlgHom.comp_assoc, hg, AlgHom.comp_assoc, hq, AlgHom.comp_id]

private theorem sl_geometry {n : ℕ} (hn : 0 < n) {S : AffineAlgebraicGroup k}
    (s : SpecialMatrixPoints S n) : Smooth S.val.X.hom := by
  let c := StandardGroups.specialLinearGroupPointsIso k (Index.{u} n)
  let i : S.val ≅ (StandardGroups.specialLinearGroup k (Index.{u} n)).val :=
    Unipotent.groupIsoOfPoints (s ≪≫ c.symm)
  apply smooth_of_groupIso i
  letI : Nonempty (Index.{u} n) := ⟨⟨⟨0, hn⟩⟩⟩
  change Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap k (Specs.StandardGroups.SLCoordinates k (Index.{u} n)))))
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr (sl_coordinates_smooth _))

end SchemeGeometry


/-- The canonical determinant-one point functor determines a smooth affine group. -/
theorem specialLinearGeometry : SpecialLinearGeometry.{u} :=
  fun _ _ _ hn _ s => sl_geometry hn s

/-- The determinant-open geometry is invariant under the natural matrix point comparison. -/
theorem generalLinearGroupGeometry : GeneralLinearGroupGeometry.{u} :=
  fun _ _ _ _ e => gl_geometry e

open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
section SchemeCenter

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open private centralizes_iff comp_conjugateFamily from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private Unipotent.onPoints Unipotent.onPoints_injective Unipotent.scheme_hom_spec
  Unipotent.factor_through_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries

variable {k : Type u} [Field k]

private theorem isIso_of_bijective_points {G H : AffineAlgebraicGroup k}
    (f : G.val ⟶ H.val) (h : ∀ R : TestAlgebra k, Function.Bijective (Unipotent.onPoints f R)) :
    IsIso f := by
  let α := (groupPointsFunctor k).map f
  let e : _ ≅ _ := NatIso.ofComponents
    (fun R => (MulEquiv.ofBijective (α.app R).hom (h R)).toGrpIso) (by
      intro R A a
      apply GrpCat.ext
      intro x
      exact congrArg (fun τ => τ x) (α.naturality a))
  let g : H.val ⟶ G.val := (AffineAlgebraicGroup.groupHomEquiv H G).symm e.inv
  have hg : (groupPointsFunctor k).map g = e.inv :=
    (AffineAlgebraicGroup.groupHomEquiv H G).apply_symm_apply e.inv
  have hf : (groupPointsFunctor k).map f = e.hom := by
    ext R x
    rfl
  refine ⟨g, ?_, ?_⟩
  · apply (groupHomComparison k _ _ G.property.1).1
    change (groupPointsFunctor k).map (f ≫ g) = (groupPointsFunctor k).map (𝟙 G.val)
    rw [Functor.map_comp, hf, hg, e.hom_inv_id]
    exact ((groupPointsFunctor k).map_id G.val).symm
  · apply (groupHomComparison k _ _ H.property.1).1
    change (groupPointsFunctor k).map (g ≫ f) = (groupPointsFunctor k).map (𝟙 H.val)
    rw [Functor.map_comp, hf, hg, e.inv_hom_id]
    exact ((groupPointsFunctor k).map_id H.val).symm



private theorem centralizes_iff_testAlgebras {G H : GroupScheme k}
    (i : H ⟶ G) (hH : IsAffine H.X.left)
    (R : TestAlgebra k) (g : Points G.X R) :
    Centralizes i g ↔
      ∀ (A : TestAlgebra k) (f : R ⟶ A) (a : Points H.X A),
        Commute (mapPoints f g) (Unipotent.onPoints i A a) := by
  constructor
  · intro h A f a
    exact (centralizes_iff i g).mp h _ ((testSpec k).map f.op) a
  · intro h
    have hR : IsAffine ((testSpec k).obj (op R)).left := inferInstanceAs
      (IsAffine (Spec (CommRingCat.of R)))
    apply hom_ext_of_points (X := H.X ⊗ (testSpec k).obj (op R)) (by
      change IsAffine (pullback H.X.hom ((testSpec k).obj (op R)).hom)
      infer_instance)
    intro A p
    rw [comp_conjugateFamily]
    let t := p ≫ snd H.X ((testSpec k).obj (op R))
    obtain ⟨f, hf⟩ := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_surjective t
    have hc := h A f.unop (p ≫ fst H.X ((testSpec k).obj (op R)))
    change Commute ((testSpec k).map f ≫ g) ((p ≫ fst _ _) ≫ i.hom.hom) at hc
    rw [hf] at hc
    exact mul_inv_eq_iff_eq_mul.mpr hc.eq

private def scalarPoints (k : Type u) [Field k] (n : ℕ) :
    Specs.StandardGroups.multiplicativePoints k ⟶
      Specs.StandardGroups.generalLinearPoints k (Index.{u} n) where
  app _ := GrpCat.ofHom (Matrix.GeneralLinearGroup.scalar (Index.{u} n))
  naturality R A f := by
    apply GrpCat.ext
    intro g
    apply Units.ext
    ext i j
    change (Matrix.GeneralLinearGroup.scalar (Index.{u} n) (Units.map f.hom.toMonoidHom g)).val i j =
      f.hom ((Matrix.GeneralLinearGroup.scalar (Index.{u} n) g).val i j)
    by_cases h : i = j <;> simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, h]

theorem generalLinearCenter : GeneralLinearCenter.{u} := by
  intro k _ n hn G e M m
  let I : ClosedSubgroup G.val := ⟨G.val, 𝟙 _, by
    change IsClosedImmersion (𝟙 G.val.X.left)
    infer_instance⟩
  obtain ⟨C, hC⟩ := centralizerScheme k G I
  let Z := Specs.Unipotent.closedSubgroupAlgebraicGroup C
  have hCtest (R : TestAlgebra k) (g : Points G.val.X R) :
      (∃ z : Points C.group.X R, Unipotent.onPoints C.inclusion R z = g) ↔
        ∃ a : Rˣ, (e.hom.app R g).val = scalar (Index.{u} n) (a : R) := by
    change (∃ z : Points C.group.X R, z ≫ C.inclusion.hom.hom = g) ↔ _
    rw [← hC _ g]
    change Centralizes I.inclusion g ↔ _
    rw [centralizes_iff_testAlgebras I.inclusion G.property.1]
    constructor
    · intro h
      apply (scalarCenterMatrices n hn R (e.hom.app R g)).mp
      intro y
      let x := (e.app R).groupIsoToMulEquiv.symm y
      have hh := h R (𝟙 R) x
      change Commute (mapPoints (𝟙 R) g) (x ≫ (𝟙 G.val.X)) at hh
      have hleft : mapPoints (𝟙 R) g = g := by
        change (testSpec k).map ((𝟙 R).op) ≫ g = g
        rw [op_id, (testSpec k).map_id, Category.id_comp]
      rw [hleft, Category.comp_id] at hh
      have hm := (hh.map (e.app R).groupIsoToMulEquiv).eq
      change (e.app R).groupIsoToMulEquiv g * (e.app R).groupIsoToMulEquiv x =
        (e.app R).groupIsoToMulEquiv x * (e.app R).groupIsoToMulEquiv g at hm
      rw [show (e.app R).groupIsoToMulEquiv x = y from (e.app R).groupIsoToMulEquiv.apply_symm_apply y] at hm
      exact hm
    · rintro ⟨a, ha⟩ A f x
      change Commute (mapPoints f g) (x ≫ 𝟙 G.val.X)
      rw [Category.comp_id]
      apply (e.app A).groupIsoToMulEquiv.injective
      rw [map_mul, map_mul]
      change e.hom.app A (mapPoints f g) * e.hom.app A x =
        e.hom.app A x * e.hom.app A (mapPoints f g)
      have hnaturality := congrArg (fun z => z g) (e.hom.naturality f)
      change e.hom.app A (mapPoints f g) =
        Matrix.GeneralLinearGroup.map f.hom.toRingHom (e.hom.app R g) at hnaturality
      rw [hnaturality]
      apply (scalarCenterMatrices n hn A _).mpr
      refine ⟨Units.map f.hom.toMonoidHom a, ?_⟩
      ext i j
      by_cases hij : i = j <;> simp [Matrix.GeneralLinearGroup.map_apply, ha, scalar_apply,
        hij]
  let α := m.hom ≫ scalarPoints k n ≫ e.inv
  let f : M.val ⟶ G.val := (AffineAlgebraicGroup.groupHomEquiv M G).symm α
  have hf (R : TestAlgebra k) (x : Points M.val.X R) :
      e.hom.app R (Unipotent.onPoints f R x) = Matrix.GeneralLinearGroup.scalar _ (m.hom.app R x) := by
    rw [Unipotent.scheme_hom_spec α]
    exact (e.app R).groupIsoToMulEquiv.apply_symm_apply _
  obtain ⟨j, hj⟩ := Unipotent.factor_through_closed (A := M) (B := Z) (C := G) f C.inclusion
    C.isClosedImmersion (fun R x => (hCtest R _).mpr
      ⟨m.hom.app R x, congrArg Units.val (hf R x)⟩)
  have hjp (R : TestAlgebra k) (x : Points M.val.X R) :
      Unipotent.onPoints C.inclusion R (Unipotent.onPoints j R x) = Unipotent.onPoints f R x :=
    congrArg (fun a => Unipotent.onPoints a R x) hj
  have hjIso : IsIso j := by
    apply isIso_of_bijective_points
    intro R
    constructor
    · intro x y he
      let i : Index.{u} n := ⟨⟨0, hn⟩⟩
      have hxy := congrArg (fun t => (e.hom.app R (Unipotent.onPoints C.inclusion R t)).val i i) he
      simp only [hjp, hf, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at hxy
      exact (m.app R).groupIsoToMulEquiv.injective (Units.ext hxy)
    · intro z
      obtain ⟨a, ha⟩ := (hCtest R _).mp ⟨z, rfl⟩
      let x := (m.app R).groupIsoToMulEquiv.symm a
      refine ⟨x, Unipotent.onPoints_injective C.inclusion C.isClosedImmersion R ?_⟩
      rw [hjp]
      apply (e.app R).groupIsoToMulEquiv.injective
      change e.hom.app R (Unipotent.onPoints f R x) = e.hom.app R (Unipotent.onPoints C.inclusion R z)
      have hx : m.hom.app R x = a := (m.app R).groupIsoToMulEquiv.apply_symm_apply _
      exact (hf R x).trans (hx ▸ Units.ext ha.symm)
  exact ⟨C, hC, asIso j, fun R x => by
    change (e.hom.app R (Unipotent.onPoints (j ≫ C.inclusion) R x)).val = _
    rw [hj, hf]
    rfl⟩

end SchemeCenter

section GeometricPoints

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open private Unipotent.onPoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
open private isMonHom_of_comp_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

variable {k : Type u} [Field k]

open private LieKolchin.baseIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.LieKolchin

private abbrev fieldTestSpecIso (K : Type u) [Field K] :=
  LieKolchin.baseIso (k := K)

private theorem factor_on_geometric_points (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K]
    {A : AffineAlgebraicGroup k} {G : GroupScheme k} (f : A.val ⟶ G)
    (D : ClosedSubgroup G) (hs : Smooth A.val.X.hom)
    (h : ∀ p : Points A.val.X ((restrictTestAlgebra k K).obj (CommAlgCat.of K K)),
      Unipotent.onPoints f _ p ∈
        SubgroupSections D ((testSpec k).obj (op ((restrictTestAlgebra k K).obj (CommAlgCat.of K K))))) :
    ∃ z : A.val ⟶ D.group, z ≫ D.inclusion = f := by
  let R : TestAlgebra K := CommAlgCat.of K K
  let F := baseChange k K
  let a := fieldTestSpecIso K
  have hg : ∃ z : A.val.X ⟶ D.group.X, z ≫ D.inclusion.hom.hom = f.hom.hom := by
    apply (geometricClosedImmersionTest k K f.hom.hom D.inclusion.hom.hom
      ((affineGroupSmoothnessCriteria k A).1.mp hs) A.property.2.1 D.isClosedImmersion).mpr
    intro p
    let x : Points (F.obj A.val.X) R := a.hom ≫ p
    obtain ⟨y, hy⟩ := h (baseChangePoint k K A.val.X R x)
    obtain ⟨z, hz⟩ := (baseChangePoints k K D.group.X R).surjective y
    have hcomp : z ≫ F.map D.inclusion.hom.hom = x ≫ F.map f.hom.hom := by
      apply (baseChangePoints k K G.X R).injective
      rw [baseChangePointsSchemeNaturality, baseChangePointsSchemeNaturality, hz]
      exact hy
    refine ⟨a.inv ≫ z, ?_⟩
    simpa only [Category.assoc, x, Iso.inv_hom_id_assoc] using congrArg (a.inv ≫ ·) hcomp
  obtain ⟨z, hz⟩ := hg
  haveI := D.isClosedImmersion
  have hzmon : IsMonHom z := isMonHom_of_comp_closed z f D.inclusion hz
  exact ⟨Grp.homMk z, Grp.hom_ext _ _ hz⟩

private def matrixPointGroupEquiv (K : Type u) [Field K] [Algebra k K]
    {G : AffineAlgebraicGroup k} {n : ℕ} (e : MatrixPoints G n) (R : TestAlgebra K) :
    Points ((groupBaseChange k K).obj G.val).X R ≃*
      Matrix.GeneralLinearGroup (Index.{u} n) R :=
  (baseChangePointGroupEquiv K G.val R).trans
    ((e.app ((restrictTestAlgebra k K).obj R)).groupIsoToMulEquiv)

private def baseChangeMatrixPoints (K : Type u) [Field K] [Algebra k K]
    {G : AffineAlgebraicGroup k} {n : ℕ} (e : MatrixPoints G n) :
    MatrixPoints (Specs.Unipotent.baseChangedAlgebraicGroup K G) n :=
  NatIso.ofComponents (fun R => (matrixPointGroupEquiv K e R).toGrpIso) (by
    intro R A f
    apply GrpCat.ext
    intro x
    change e.hom.app ((restrictTestAlgebra k K).obj A)
      (baseChangePoint k K G.val.X A (mapPoints f x)) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom
        (e.hom.app ((restrictTestAlgebra k K).obj R) (baseChangePoint k K G.val.X R x))
    rw [baseChangePointsNaturality]
    exact congrArg (fun a => a (baseChangePoint k K G.val.X R x))
      (e.hom.naturality ((restrictTestAlgebra k K).map f)))

end GeometricPoints

section SchemeDerived

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open private Unipotent.onPoints Unipotent.onPoints_comp Unipotent.onPoints_injective
  Unipotent.group_hom_ext Unipotent.scheme_hom_spec Unipotent.factor_through_closed
  Unipotent.kernel_points Unipotent.scheme_kernel_of_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
open private schemeKernel_exists schemeKernel_sections isMonHom_of_comp_closed
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private SchemeDerivedGroup.comp_commutatorMap_projections SchemeDerivedGroup.kernel_normal
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup

variable {k : Type u} [Field k]

private def detPoints (k : Type u) [Field k] (n : ℕ) :
    Specs.StandardGroups.generalLinearPoints k (Index.{u} n) ⟶
      Specs.StandardGroups.multiplicativePoints k where
  app R := GrpCat.ofHom Matrix.GeneralLinearGroup.det
  naturality R A f := by
    apply GrpCat.ext
    intro g
    exact (Matrix.GeneralLinearGroup.map_det f.hom.toRingHom g)

private def slToGlPoints (k : Type u) [Field k] (n : ℕ) :
    Specs.StandardGroups.specialLinearPoints k (Index.{u} n) ⟶
      Specs.StandardGroups.generalLinearPoints k (Index.{u} n) where
  app R := GrpCat.ofHom Matrix.SpecialLinearGroup.toGL
  naturality R A f := by
    apply GrpCat.ext
    intro g
    apply Units.ext
    rfl

private theorem sl_is_det_kernel {n : ℕ} {G S : AffineAlgebraicGroup k}
    (e : MatrixPoints G n) (s : SpecialMatrixPoints S n) :
    ∃ (q : G.val ⟶ (StandardGroups.multiplicativeGroup k).val)
      (f : S.val ⟶ G.val) (hf : IsClosedImmersion f.hom.hom.left),
      IsSchemeKernel q (⟨S.val, f, hf⟩ : ClosedSubgroup G.val) ∧
        ∀ (R : TestAlgebra k) (x : Points S.val.X R),
          e.hom.app R (((groupPointsFunctor k).map f).app R x) =
          Matrix.SpecialLinearGroup.toGL (n := Index.{u} n) (R := R) (s.hom.app R x) := by
  let M := StandardGroups.multiplicativeGroup k
  let m := StandardGroups.multiplicativeGroupPointsIso k
  let α := e.hom ≫ detPoints k n ≫ m.inv
  let β := s.hom ≫ slToGlPoints k n ≫ e.inv
  let q := (AffineAlgebraicGroup.groupHomEquiv G M).symm α
  let f := (AffineAlgebraicGroup.groupHomEquiv S G).symm β
  have hq (R : TestAlgebra k) (x : Points G.val.X R) :
      m.hom.app R (Unipotent.onPoints q R x) = Matrix.GeneralLinearGroup.det (e.hom.app R x) := by
    rw [Unipotent.scheme_hom_spec α]
    exact (m.app R).groupIsoToMulEquiv.apply_symm_apply _
  have hf (R : TestAlgebra k) (x : Points S.val.X R) :
      e.hom.app R (Unipotent.onPoints f R x) = Matrix.SpecialLinearGroup.toGL (s.hom.app R x) := by
    rw [Unipotent.scheme_hom_spec β]
    exact (e.app R).groupIsoToMulEquiv.apply_symm_apply _
  have hker (R : TestAlgebra k) (x : Points G.val.X R) :
      Unipotent.onPoints q R x = 1 ↔ ∃ y : Points S.val.X R, Unipotent.onPoints f R y = x := by
    constructor
    · intro hx
      have hd : Matrix.GeneralLinearGroup.det (e.hom.app R x) = 1 := by
        rw [← hq R x, hx]
        exact (m.hom.app R).hom.map_one
      let g : (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Index.{u} n) R →* Rˣ).ker :=
        ⟨e.hom.app R x, hd⟩
      let v := (Matrix.SpecialLinearGroup.toGLKerEquiv (n := Index.{u} n) (R := R)).symm g
      let y : Points S.val.X R := (s.app R).groupIsoToMulEquiv.symm v
      have hy : s.hom.app R y = v := (s.app R).groupIsoToMulEquiv.apply_symm_apply v
      refine ⟨y, (e.app R).groupIsoToMulEquiv.injective ?_⟩
      exact (hf R y).trans (hy ▸ congrArg Subtype.val
        (Matrix.SpecialLinearGroup.toGLKerEquiv.apply_symm_apply g))
    · rintro ⟨y, rfl⟩
      apply (m.app R).groupIsoToMulEquiv.injective
      change m.hom.app R (Unipotent.onPoints q R (Unipotent.onPoints f R y)) =
        m.hom.app R 1
      rw [hq, hf, Matrix.SpecialLinearGroup.coeToGL_det, map_one]
  have hMa := M.property.1
  obtain ⟨N, hN⟩ := schemeKernel_exists q
  let B := Specs.Unipotent.closedSubgroupAlgebraicGroup N
  obtain ⟨j, hj⟩ := Unipotent.factor_through_closed (A := S) (B := B) (C := G) f
    N.inclusion N.isClosedImmersion (fun R x => (Unipotent.kernel_points q N hN R _).mp
      ((hker R _).mpr ⟨x, rfl⟩))
  have hjp (R : TestAlgebra k) (x : Points S.val.X R) :
      Unipotent.onPoints N.inclusion R (Unipotent.onPoints j R x) = Unipotent.onPoints f R x :=
    congrArg (fun a => Unipotent.onPoints a R x) hj
  have hjIso : IsIso j := by
    apply isIso_of_bijective_points
    intro R
    constructor
    · intro x y he
      apply (s.app R).groupIsoToMulEquiv.injective
      apply Matrix.SpecialLinearGroup.toGL_injective
      have hh : Unipotent.onPoints f R x = Unipotent.onPoints f R y :=
        (hjp R x).symm.trans ((congrArg (Unipotent.onPoints N.inclusion R) he).trans (hjp R y))
      exact (hf R x).symm.trans ((congrArg (fun p => e.hom.app R p) hh).trans (hf R y))
    · intro z
      obtain ⟨y, hy⟩ := (hker R _).mp
        ((Unipotent.kernel_points q N hN R _).mpr ⟨z, rfl⟩)
      exact ⟨y, Unipotent.onPoints_injective N.inclusion N.isClosedImmersion R
        ((hjp R y).trans hy)⟩
  have hclosed : IsClosedImmersion f.hom.hom.left := by
    rw [← hj]
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget _
    haveI : IsIso j.hom.hom.left := inferInstanceAs (IsIso (F.map j))
    haveI := N.isClosedImmersion
    exact IsClosedImmersion.comp _ _
  exact ⟨q, f, hclosed, Unipotent.scheme_kernel_of_iso q f hclosed N hN (asIso j) hj, hf⟩

/-- The determinant-one group has the universal property of the scheme derived group. -/
theorem generalLinearDerived : GeneralLinearDerived.{u} := by
  intro k _ n hn G S e s
  obtain ⟨q, f, hf, hker, hmat⟩ := sl_is_det_kernel e s
  let N : ClosedSubgroup G.val := ⟨S.val, f, hf⟩
  have hs := sl_geometry hn s
  refine ⟨f, hf, hmat, hs, SchemeDerivedGroup.kernel_normal hker, ?_, ?_⟩
  · apply (schemeKernel_sections hker _).mpr
    have hA := G.property.1
    apply hom_ext_of_points (X := G.val.X ⊗ G.val.X) (by
      change IsAffine (pullback G.val.X.hom G.val.X.hom)
      infer_instance)
    intro R p
    rw [← Category.assoc, SchemeDerivedGroup.comp_commutatorMap_projections, MonObj.comp_one]
    have hid : (𝟙 G.val : G.val ⟶ G.val).hom.hom = 𝟙 G.val.X := rfl
    simp only [hid, Category.comp_id]
    let x : Points G.val.X R := p ≫ fst G.val.X G.val.X
    let y : Points G.val.X R := p ≫ snd G.val.X G.val.X
    change Unipotent.onPoints q R (⁅x, y⁆ : Points G.val.X R) = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    let m := StandardGroups.multiplicativeGroupPointsIso k
    exact (m.app R).groupIsoToMulEquiv.injective (by
      simp only [map_mul]
      change Commute (m.hom.app R (Unipotent.onPoints q R x) : Rˣ)
        (m.hom.app R (Unipotent.onPoints q R y) : Rˣ)
      exact @mul_comm (Rˣ) inferInstance (m.hom.app R (Unipotent.onPoints q R x))
        (m.hom.app R (Unipotent.onPoints q R y) : Rˣ))
  · intro B _ hB
    refine factor_on_geometric_points (AlgebraicClosure k) f B hs ?_
    let K := AlgebraicClosure k
    let R : TestAlgebra k := (restrictTestAlgebra k K).obj (CommAlgCat.of K K)
    have hle : commutator (Points G.val.X R) ≤ SubgroupSections B ((testSpec k).obj (op R)) := by
      rw [commutator, Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨z, hz⟩ := hB
      change z ≫ B.inclusion.hom.hom =
        Specs.SchemeDerivedGroup.commutatorMap (𝟙 G.val) (𝟙 G.val) at hz
      refine ⟨lift x y ≫ z, ?_⟩
      change (lift x y ≫ z) ≫ B.inclusion.hom.hom = ⁅x, y⁆
      rw [Category.assoc, hz, SchemeDerivedGroup.comp_commutatorMap_projections]
      simp
    intro x
    change Points S.val.X R at x
    change Unipotent.onPoints f R x ∈ _
    apply hle
    let m : Points G.val.X R ≃* Matrix.GeneralLinearGroup (Index.{u} n) K :=
      (e.app R).groupIsoToMulEquiv
    have hmx : m (Unipotent.onPoints f R x) ∈
        commutator (Matrix.GeneralLinearGroup (Index.{u} n) K) := by
      rw [generalLinearGeometricCommutator K n hn]
      change Matrix.GeneralLinearGroup.det (e.hom.app R (Unipotent.onPoints f R x)) = 1
      rw [hmat R x, Matrix.SpecialLinearGroup.coeToGL_det]
    rw [← map_commutator_of_surjective (f := m.toMonoidHom) m.surjective] at hmx
    obtain ⟨y, hy, he⟩ := hmx
    exact (m.injective he) ▸ hy

end SchemeDerived

section NaturalModule

open WithConv
open LinearAlgebraicGroups.RationalRepresentations
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open private GeometricRadicals.sections_normal GeometricRadicals.trivial_of_subsingleton_sections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private Unipotent.onPoints Unipotent.onPoints_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ}

omit [IsAlgClosed K] in
private theorem evaluate_column_action (A : HopfAlgebraCategory K)
    (ρ : RightComodule K A (Index.{u} n → K)) (g : A →ₐ[K] K) (v : Index.{u} n → K) :
    TensorProduct.rid K (Index.{u} n → K) (evaluate A ρ g v) =
      (g.mapMatrix (coefficients A (Pi.basisFun K (Index.{u} n)) ρ)) *ᵥ v := by
  let b := Pi.basisFun K (Index.{u} n)
  let L := (TensorProduct.rid K (Index.{u} n → K)).toLinearMap.comp (evaluate A ρ g)
  have hL : L = Matrix.toLin' (g.mapMatrix (coefficients A b ρ)) := by
    apply b.ext
    intro j
    change TensorProduct.rid K (Index.{u} n → K) (evaluate A ρ g (b j)) =
      (g.mapMatrix (coefficients A b ρ)) *ᵥ (b j)
    rw [evaluate, LinearMap.comp_apply, coaction_apply_basis, map_sum, map_sum]
    simp only [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, TensorProduct.rid_tmul]
    ext l
    simp [b, Pi.basisFun_apply, Pi.single_apply, mul_ite]
  exact LinearMap.congr_fun hL v

omit [IsAlgClosed K] in
private theorem fixed_vector_of_unipotent (hn : 0 < n)
    {U G : AffineAlgebraicGroup K} (hU : Specs.Unipotent.IsUnipotent U)
    (e : MatrixPoints G n) (i : U.val ⟶ G.val) :
    ∃ v : Index.{u} n → K, v ≠ 0 ∧
      ∀ p : Points U.val.X (CommAlgCat.of K K),
        (e.hom.app _ (Unipotent.onPoints i _ p)).val *ᵥ v = v := by
  obtain ⟨A, ⟨h⟩, hA⟩ := hU
  let R := CommAlgCat.of K K
  let b := Pi.basisFun K (Index.{u} n)
  let c := hopfSpecPointIso A ≪≫ (groupPointsFunctor K).mapIso h
  let α := c.hom ≫ (groupPointsFunctor K).map i ≫ e.hom
  let E := pointsCoactionEquiv A b
  let ρ := E α
  letI : Nonempty (Index.{u} n) := ⟨⟨⟨0, hn⟩⟩⟩
  obtain ⟨v, hv, hi⟩ := hA (Index.{u} n → K) ρ
  refine ⟨v, hv, fun p => ?_⟩
  let g := (c.app R).groupIsoToMulEquiv.symm p
  have hgp : c.hom.app R g = p := (c.app R).groupIsoToMulEquiv.apply_symm_apply p
  let M := (e.hom.app R (Unipotent.onPoints i R p)).val
  have hM : g.ofConv.mapMatrix (RationalRepresentations.coefficients A b ρ) = M := by
    have he := congrArg (fun β => (β.app R g).val) (E.symm_apply_apply α)
    change g.ofConv.mapMatrix _ = (e.hom.app R (Unipotent.onPoints i R (c.hom.app R g))).val at he
    rw [hgp] at he
    exact he
  have he := evaluate_column_action A ρ g.ofConv v
  change TensorProduct.rid K (Index.{u} n → K) (evaluate A ρ g.ofConv v) =
    (g.ofConv.mapMatrix (coefficients A b ρ)) *ᵥ v at he
  rw [hM] at he
  have hv' := (invariantKernel A ρ v).mpr hi R g.ofConv
  rw [hv', TensorProduct.rid_tmul, one_smul] at he
  exact he.symm

private theorem exists_ne_zero_ne_one (K : Type u) [Field K] [Infinite K] :
    ∃ r : K, r ≠ 0 ∧ r ≠ 1 := by
  classical
  obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset K)
  exact ⟨r, fun h => hr (h ▸ Finset.mem_insert_self _ _),
    fun h => hr (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩

private theorem coordinate_vector_mem_of_stable_diagonal
    (W : Submodule K (Index.{u} n → K)) {v : Index.{u} n → K}
    (hv : v ∈ W) (j : Index.{u} n) (hj : v j ≠ 0)
    (h : ∀ a : Kˣ, (diagonalAt j a).val *ᵥ v ∈ W) :
    Pi.single j 1 ∈ W := by
  obtain ⟨r, hr₀, hr₁⟩ := exists_ne_zero_ne_one K
  let d := diagonalAt j (Units.mk0 r hr₀)
  let a := (r - 1) * v j
  have ha : a ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hr₁) hj
  have he : d.val *ᵥ v - v = a • Pi.single j 1 := by
    rw [diagonalAt_val]
    ext t
    rw [Pi.sub_apply, Matrix.mulVec_diagonal, Pi.smul_apply]
    by_cases ht : t = j
    · subst t
      simp only [ite_true, Pi.single_eq_same, smul_eq_mul, mul_one, a, sub_mul, one_mul]
      rfl
    · simp only [ite_eq_right ht, one_mul, sub_self, Pi.single_eq_of_ne ht, smul_zero]
  have hw := W.sub_mem (h (Units.mk0 r hr₀)) hv
  change d.val *ᵥ v - v ∈ W at hw
  rw [he] at hw
  simpa [smul_smul, inv_mul_cancel₀ ha] using W.smul_mem a⁻¹ hw

omit [IsAlgClosed K] in
private theorem coordinate_vector_mem_of_stable_transvection
    (W : Submodule K (Index.{u} n → K)) (i j : Index.{u} n) (hij : i ≠ j)
    (hj : Pi.single j 1 ∈ W)
    (h : (Matrix.SpecialLinearGroup.toGL (elementary i j hij (1 : K))).val *ᵥ Pi.single j 1 ∈ W) :
    Pi.single i 1 ∈ W := by
  change (1 + single i j 1 : Matrix _ _ K) *ᵥ Pi.single j 1 ∈ W at h
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq] at h
  simp only [Pi.single_eq_same, mul_one] at h
  simpa only [add_sub_cancel_left, one_smul] using W.sub_mem h hj

private theorem trivial_of_normal_unipotent {G : AffineAlgebraicGroup K}
    (hn : 0 < n) (e : MatrixPoints G n) (N : ClosedSubgroup G.val)
    (hN : Specs.GeometricRadicals.IsSmoothConnectedNormal N)
    (hu : Specs.Unipotent.IsUnipotent (Specs.Unipotent.closedSubgroupAlgebraicGroup N)) :
    Specs.GeometricRadicals.IsTrivialSubgroup N := by
  let U := Specs.Unipotent.closedSubgroupAlgebraicGroup N
  let R := CommAlgCat.of K K
  let m : Points G.val.X R ≃* Matrix.GeneralLinearGroup (Index.{u} n) K :=
    (e.app R).groupIsoToMulEquiv
  let H := SubgroupSections N ((testSpec K).obj (op R))
  have hNormal : H.Normal := GeometricRadicals.sections_normal hN.2.2 _
  obtain ⟨v, hv, hvf⟩ := fixed_vector_of_unipotent hn hu e N.inclusion
  let W : Submodule K (Index.{u} n → K) :=
    { carrier := { w | ∀ y ∈ H, (m y).val *ᵥ w = w }
      zero_mem' := fun y _ => Matrix.mulVec_zero _
      add_mem' := fun {x z} hx hz y hy => by
        rw [Matrix.mulVec_add, hx y hy, hz y hy]
      smul_mem' := fun c x hx y hy => by
        rw [Matrix.mulVec_smul, hx y hy] }
  have hvW : v ∈ W := by
    rintro y ⟨p, rfl⟩
    exact hvf p
  have hstable (g : Matrix.GeneralLinearGroup (Index.{u} n) K) {w} (hw : w ∈ W) :
      g.val *ᵥ w ∈ W := by
    intro y hy
    let a : Points G.val.X R := m.symm g
    have ha : m a = g := m.apply_symm_apply g
    have hc := hw (a⁻¹ * y * (a⁻¹)⁻¹) (hNormal.conj_mem y hy a⁻¹)
    change (m (a⁻¹ * y * (a⁻¹)⁻¹)).val *ᵥ w = w at hc
    rw [map_mul, map_mul, map_inv, inv_inv, ha] at hc
    change (m y).val *ᵥ (g.val *ᵥ w) = _
    calc
      _ = (m y * g).val *ᵥ w := Matrix.mulVec_mulVec _ _ _
      _ = (g * (g⁻¹ * m y * g)).val *ᵥ w := by
        have hg : g * (g⁻¹ * m y * g) = m y * g := by group
        rw [hg]
      _ = g.val *ᵥ w := by rw [Units.val_mul, ← Matrix.mulVec_mulVec, hc]
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! hh
    exact hv (funext hh)
  have hej := coordinate_vector_mem_of_stable_diagonal W hvW j hj
    (fun a => hstable (diagonalAt j a) hvW)
  have hcoord (i : Index.{u} n) : Pi.single i 1 ∈ W := by
    by_cases h : i = j
    · rwa [h]
    · exact coordinate_vector_mem_of_stable_transvection W i j h hej (hstable _ hej)
  have hp (x : Points N.group.X R) : Unipotent.onPoints N.inclusion R x = 1 := by
    apply m.injective
    rw [map_one]
    apply Units.ext
    ext i j
    have h := hcoord j (Unipotent.onPoints N.inclusion R x) ⟨x, rfl⟩
    have hh := congrFun h i
    rw [Matrix.mulVec_single_one] at hh
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using hh
  have hsub : Subsingleton (Points N.group.X R) := ⟨fun p q =>
    Unipotent.onPoints_injective N.inclusion N.isClosedImmersion R ((hp p).trans (hp q).symm)⟩
  haveI : Subsingleton ((𝟙_ (SchemeOver K)) ⟶ U.val.X) := ⟨fun p q =>
    (cancel_epi (fieldTestSpecIso K).hom).mp (hsub.elim _ _)⟩
  exact GeometricRadicals.trivial_of_subsingleton_sections U hN.1

theorem generalLinearReductive : GeneralLinearReductive.{u} := by
  intro k _ n hn G e
  obtain ⟨hs, hc⟩ := gl_geometry e
  let K := AlgebraicClosure k
  let GK := Specs.GeometricRadicals.GeometricGroup G
  let N := Specs.GeometricRadicals.geometricUnipotentRadical G
  have hN := GeometricRadicals.geometricUnipotentRadicalLargest G
  let eK : MatrixPoints GK n := baseChangeMatrixPoints K e
  exact ⟨hs, hc, trivial_of_normal_unipotent hn eK N hN.1 hN.2.1⟩

end NaturalModule

section UpperTriangular
open Specs.Triangularization (upperTriangular)

open Specs.StandardGroups (universalMatrix)
open private Unipotent.onPoints Unipotent.scheme_hom_spec Unipotent.group_hom_ext
  Unipotent.onPoints_comp Unipotent.factor_through_closed
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
open private Triangularization.lowerEntryIdeal Triangularization.UpperCoordinates
  Triangularization.quotientCoordinates Triangularization.upperEvaluation
  Triangularization.upperEvaluation_entry Triangularization.upperHopfAlgebra
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.Triangularization
open private StandardGroups.glCoordinates_ext StandardGroups.evaluatedGeneralLinear
  StandardGroups.spectrumPointsIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private Triangularization.evaluatedUpperTriangular
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.Triangularization
open WithConv

private abbrev UpperPosition (n : ℕ) :=
  {p : Index.{u} n × Index.{u} n // p.1 ≤ p.2}

private def upperGeneric (k : Type u) [Field k] (n : ℕ) :
    Matrix (Index.{u} n) (Index.{u} n) (MvPolynomial (UpperPosition n) k) :=
  fun i j => if h : i ≤ j then MvPolynomial.X ⟨(i, j), h⟩ else 0

private theorem upperGeneric_det_ne_zero (k : Type u) [Field k] (n : ℕ) :
    (upperGeneric k n).det ≠ 0 := by
  let f := MvPolynomial.aeval (R := k)
    (fun p : UpperPosition n => (1 : Matrix (Index.{u} n) (Index.{u} n) k) p.1.1 p.1.2)
  have hf : f.mapMatrix (upperGeneric k n) = 1 := by
    ext i j
    by_cases h : i ≤ j
    · simp [upperGeneric, h, f, AlgHom.mapMatrix_apply]
    · simp [upperGeneric, h, (lt_of_not_ge h).ne',
        AlgHom.mapMatrix_apply]
  intro hd
  have he := congrArg f hd
  rw [AlgHom.map_det, hf, det_one, map_zero] at he
  exact one_ne_zero he

private theorem upperQuotient_entry_zero (k : Type u) [Field k] (n : ℕ)
    {i j : Index.{u} n} (h : j < i) :
    Triangularization.quotientCoordinates k n (universalMatrix k _ i j) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨⟨(j, i), h⟩, rfl⟩)

private def upperCoordinatesEquiv (k : Type u) [Field k] (n : ℕ) :
    Triangularization.UpperCoordinates k n ≃ₐ[k] Localization.Away (upperGeneric k n).det := by
  let P := MvPolynomial (UpperPosition n) k
  let d := (upperGeneric k n).det
  let L := Localization.Away d
  let S := Triangularization.UpperCoordinates k n
  let q := Triangularization.quotientCoordinates k n
  let w : UpperPosition n → S := fun p => q (universalMatrix k _ p.1.1 p.1.2)
  let a : P →ₐ[k] S := MvPolynomial.aeval w
  have hA : a.mapMatrix (upperGeneric k n) = q.mapMatrix (universalMatrix k _) := by
    ext i j
    by_cases h : i ≤ j
    · change a (upperGeneric k n i j) = q (universalMatrix k _ i j)
      have hx : upperGeneric k n i j = MvPolynomial.X ⟨(i,j), h⟩ := dite_eq_left h
      rw [hx]
      exact MvPolynomial.aeval_X w ⟨(i,j), h⟩
    · change a (upperGeneric k n i j) = q (universalMatrix k _ i j)
      rw [show upperGeneric k n i j = 0 from dite_eq_right h]
      exact (map_zero a).trans (upperQuotient_entry_zero k n (lt_of_not_ge h)).symm
  have hd : IsUnit (a d) := by
    change IsUnit (a (upperGeneric k n).det)
    rw [AlgHom.map_det, hA, ← AlgHom.map_det]
    exact (StandardGroups.isUnit_universalDeterminant k (Index.{u} n)).map q
  let t : L →ₐ[k] S := IsLocalization.Away.liftAlgHom d hd
  have ht (p : UpperPosition n) :
      t (algebraMap P L (MvPolynomial.X p)) = q (universalMatrix k _ p.1.1 p.1.2) :=
    (IsLocalization.Away.lift_eq d hd _).trans (MvPolynomial.aeval_X w p)
  let M : Matrix (Index.{u} n) (Index.{u} n) L := (upperGeneric k n).map (algebraMap P L)
  have hM : IsUnit M.det := by
    change IsUnit (((algebraMap P L).mapMatrix (upperGeneric k n)).det)
    rw [← RingHom.map_det]
    exact IsLocalization.Away.algebraMap_isUnit d
  let g : Matrix.GeneralLinearGroup (Index.{u} n) L := Matrix.GeneralLinearGroup.mk'' M hM
  let R := CommAlgCat.of k L
  let x : (Specs.Triangularization.upperTriangularPoints k n).obj R :=
    ⟨g, fun i j hij => by
      change j < i at hij
      change algebraMap P L (upperGeneric k n i j) = 0
      rw [show upperGeneric k n i j = 0 from dite_eq_right (not_le.mpr hij), map_zero]⟩
  let f : S →ₐ[k] L := Triangularization.upperEvaluation k n R x
  have hf (i j : Index.{u} n) :
      f (q (universalMatrix k _ i j)) = algebraMap P L (upperGeneric k n i j) :=
    Triangularization.upperEvaluation_entry k n R x i j
  refine AlgEquiv.ofAlgHom f t ?_ ?_
  · apply IsLocalization.algHom_ext (Submonoid.powers d)
    apply MvPolynomial.algHom_ext
    rintro ⟨⟨i, j⟩, hij⟩
    change f (t (algebraMap P L (MvPolynomial.X ⟨(i, j), hij⟩))) = _
    rw [ht, hf]
    exact congrArg (algebraMap P L) (dite_eq_left hij)
  · apply Ideal.Quotient.algHom_ext k
    apply StandardGroups.glCoordinates_ext
    intro i j
    change t (f (q (universalMatrix k _ i j))) = q (universalMatrix k _ i j)
    rw [hf]
    by_cases hij : i ≤ j
    · have hh : upperGeneric k n i j = MvPolynomial.X ⟨(i, j), hij⟩ := dite_eq_left hij
      rw [hh]
      exact ht ⟨(i, j), hij⟩
    · calc
        t (algebraMap P L (upperGeneric k n i j)) = t (algebraMap P L 0) :=
          congrArg (fun z : P => t (algebraMap P L z)) (dite_eq_right hij)
        _ = t 0 := congrArg t (map_zero (algebraMap P L))
        _ = 0 := map_zero t
        _ = _ := (upperQuotient_entry_zero k n (lt_of_not_ge hij)).symm

private theorem upper_geometry (k : Type u) [Field k] (n : ℕ) :
    Smooth (Triangularization.upperTriangularGroup k n).val.X.hom ∧
      GeometricallyConnected (Triangularization.upperTriangularGroup k n).val.X.hom := by
  let S := Triangularization.UpperCoordinates k n
  let d := (upperGeneric k n).det
  let L := Localization.Away d
  let a := upperCoordinatesEquiv k n
  let e : CommAlgCat.of k S ≅ CommAlgCat.of k L := by
    refine ⟨CommAlgCat.ofHom a.toAlgHom, CommAlgCat.ofHom a.symm.toAlgHom, ?_, ?_⟩
    · apply CommAlgCat.hom_ext
      apply AlgHom.ext
      exact a.symm_apply_apply
    · apply CommAlgCat.hom_ext
      apply AlgHom.ext
      exact a.apply_symm_apply
  let i := (testSpec k).mapIso e.symm.op
  have h := principal_open_geometry d (upperGeneric_det_ne_zero k n)
  haveI := h.1
  change Smooth ((testSpec k).obj (op (CommAlgCat.of k S))).hom ∧
    GeometricallyConnected ((testSpec k).obj (op (CommAlgCat.of k S))).hom
  have hi : IsIso i.hom.left := (Over.forget _).map_isIso i.hom
  rw [← i.hom.w]
  exact ⟨smooth_comp _ _, (MorphismProperty.cancel_left_of_respectsIso
    (P := @GeometricallyConnected) i.hom.left _).mpr h.2⟩

private def upperPointsInclusion (k : Type u) [Field k] (n : ℕ) :
    Specs.Triangularization.upperTriangularPoints k n ⟶
      Specs.StandardGroups.generalLinearPoints k (Index.{u} n) where
  app R := GrpCat.ofHom (upperTriangular (Index.{u} n) R).subtype
  naturality R S f := by ext; rfl

private theorem upper_inclusion {k : Type u} [Field k] {n : ℕ}
    {G : AffineAlgebraicGroup k} (e : MatrixPoints G n) :
    ∃ (f : (Triangularization.upperTriangularGroup k n).val ⟶ G.val)
      (_ : IsClosedImmersion f.hom.hom.left),
      ∀ (R : TestAlgebra k) (x : Points (Triangularization.upperTriangularGroup k n).val.X R),
        e.hom.app R (Unipotent.onPoints f R x) =
          ((Triangularization.upperTriangularGroupPointsIso k n).hom.app R x).val := by
  let B := Triangularization.upperTriangularGroup k n
  let b := Triangularization.upperTriangularGroupPointsIso k n
  let G₀ := StandardGroups.generalLinearGroup k (Index.{u} n)
  let c := StandardGroups.generalLinearGroupPointsIso k (Index.{u} n)
  let α := b.hom ≫ upperPointsInclusion k n ≫ c.inv
  let f := (AffineAlgebraicGroup.groupHomEquiv B G₀).symm α
  let β := c.hom ≫ e.inv
  let i := (AffineAlgebraicGroup.groupHomEquiv G₀ G).symm β
  have hi : IsIso i := by
    apply isIso_of_bijective_points (G := G₀) (H := G)
    intro R
    have hh : (Unipotent.onPoints i R : Points G₀.val.X R → Points G.val.X R) =
        (c.app R).groupIsoToMulEquiv.trans (e.app R).groupIsoToMulEquiv.symm :=
      funext (Unipotent.scheme_hom_spec β R)
    rw [hh]
    exact MulEquiv.bijective _
  have hf (R : TestAlgebra k) (x : Points B.val.X R) :
      c.hom.app R (Unipotent.onPoints f R x) = (b.hom.app R x).val := by
    rw [Unipotent.scheme_hom_spec α]
    exact (c.app R).groupIsoToMulEquiv.apply_symm_apply _
  have hclosed : IsClosedImmersion f.hom.hom.left := by
    let R := CommAlgCat.of k (Triangularization.UpperCoordinates k n)
    let q := Triangularization.quotientCoordinates k n
    let C := Triangularization.upperHopfAlgebra k n
    letI : HopfAlgebra k (Specs.StandardGroups.GLCoordinates k (Index.{u} n)) :=
      StandardGroups.generalLinearHopf k (Index.{u} n)
    let E := CommHopfAlgCat.of k (Specs.StandardGroups.GLCoordinates k (Index.{u} n))
    let x : Points B.val.X R := (hopfSpecPointIso C).hom.app R (toConv (AlgHom.id k C))
    let y : Points G₀.val.X R := (hopfSpecPointIso E).hom.app R (toConv q)
    have hx : x = 𝟙 B.val.X := by
      apply Over.OverMorphism.ext
      change Spec.map (CommRingCat.ofHom (AlgHom.id k C).toRingHom) = 𝟙 _
      exact Spec.map_id _
    have hbx : b.hom.app R x = Triangularization.evaluatedUpperTriangular k n R (AlgHom.id k C) := by
      let θ := hopfSpecPointIso C
      have hθ : θ.inv.app R (θ.hom.app R (toConv (AlgHom.id k C))) =
          toConv (AlgHom.id k C) := (θ.app R).groupIsoToMulEquiv.symm_apply_apply _
      change (Triangularization.evaluatedUpperTriangular k n R
        (θ.inv.app R (θ.hom.app R (toConv (AlgHom.id k C)))).ofConv) = _
      rw [hθ]
    have hcy : c.hom.app R y = StandardGroups.evaluatedGeneralLinear q := by
      let θ := hopfSpecPointIso E
      have hθ : θ.inv.app R (θ.hom.app R (toConv q)) = toConv q :=
        (θ.app R).groupIsoToMulEquiv.symm_apply_apply _
      change StandardGroups.evaluatedGeneralLinear
        (θ.inv.app R (θ.hom.app R (toConv q))).ofConv = _
      rw [hθ]
    have hy : (b.hom.app R x).val = c.hom.app R y := by
      rw [hbx, hcy]
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      rfl
    have hh : Unipotent.onPoints f R x = y :=
      (c.app R).groupIsoToMulEquiv.injective ((hf R x).trans hy)
    change x ≫ f.hom.hom = y at hh
    have hx' : x.left = 𝟙 B.val.X.left :=
      congrArg (fun z : B.val.X ⟶ B.val.X => z.left) hx
    have h : f.hom.hom.left = Spec.map (CommRingCat.ofHom q.toRingHom) := by
      have hh' := congrArg (fun z => z.left) hh
      change x.left ≫ f.hom.hom.left = _ at hh'
      rw [hx'] at hh'
      change 𝟙 B.val.X.left ≫ f.hom.hom.left = Spec.map (CommRingCat.ofHom q.toRingHom) at hh'
      exact (Category.id_comp _).symm.trans hh'
    rw [h]
    exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨f ≫ i, ?_, fun R x => ?_⟩
  · let F := Grp.forget (SchemeOver k) ⋙ Over.forget _
    have : IsIso i.hom.hom.left := F.map_isIso i
    have := hclosed
    exact IsClosedImmersion.comp _ _
  · rw [Unipotent.onPoints_comp, Unipotent.scheme_hom_spec β]
    exact ((e.app R).groupIsoToMulEquiv.apply_symm_apply _).trans (hf R x)

end UpperTriangular

section DiagonalSubgroup

open Specs.Triangularization (upperTriangular)

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open private Unipotent.onPoints Unipotent.onPoints_comp Unipotent.group_hom_ext
  Unipotent.scheme_hom_spec Unipotent.factor_through_closed
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
open private Triangularization.diagonalUnit Triangularization.diagonalHom
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.Triangularization
open private Unipotent.groupIsoOfPoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Criteria
open private isMonHom_of_comp_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private fieldSpecMap_surjective centralizes_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

variable {k : Type u} [Field k]

private def diagonalMatrixHom (Idx R : Type u) [Fintype Idx] [DecidableEq Idx] [CommRing R] :
    (Idx → Rˣ) →* Matrix.GeneralLinearGroup Idx R :=
  (Units.map (diagonalRingHom Idx R).toMonoidHom).comp (MulEquiv.piUnits).symm.toMonoidHom

private theorem diagonalMatrixHom_val {Idx R : Type u} [Fintype Idx] [DecidableEq Idx] [CommRing R]
    (a : Idx → Rˣ) : (diagonalMatrixHom Idx R a).val = diagonal (fun i => (a i : R)) := rfl

private def diagonalUpperPoints (k : Type u) [Field k] (n : ℕ) :
    Specs.StandardGroups.multiplicativePowerPoints k (Index.{u} n) ⟶
      Specs.Triangularization.upperTriangularPoints k n where
  app R := GrpCat.ofHom ((diagonalMatrixHom (Index.{u} n) R).codRestrict _ (fun a => by
    intro i j h
    change j < i at h
    rw [diagonalMatrixHom_val, diagonal_apply_ne _ (ne_of_gt h)]))
  naturality R S f := by
    apply GrpCat.ext
    intro a
    apply Subtype.ext
    apply Units.ext
    change diagonal (fun i => (f.hom (a i))) = (diagonal (fun i => (a i : R))).map f.hom
    rw [diagonal_map (map_zero f.hom)]

private theorem diagonal_units_surjective {R : Type u} [CommRing R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Index.{u} n) R) (h : IsDiagonal g) :
    ∃ a : Index.{u} n → Rˣ, diagonalMatrixHom _ _ a = g := by
  let x : upperTriangular (Index.{u} n) R := ⟨g, fun _ _ hij => h _ _ (ne_of_gt hij)⟩
  refine ⟨Triangularization.diagonalUnit x, Units.ext ?_⟩
  exact (eq_diagonal_of_isDiagonal h).symm

private theorem diagonal_in_upper (k : Type u) [Field k] (n : ℕ) :
    ∃ (j : (StandardGroups.multiplicativePowerGroup k (Index.{u} n)).val ⟶
        (Triangularization.upperTriangularGroup k n).val) (_ : IsClosedImmersion j.hom.hom.left),
      ∀ (R : TestAlgebra k) (x : Points (StandardGroups.multiplicativePowerGroup k
          (Index.{u} n)).val.X R),
        ((Triangularization.upperTriangularGroupPointsIso k n).hom.app R
          (Unipotent.onPoints j R x)).val =
          diagonalMatrixHom _ _ ((StandardGroups.multiplicativePowerGroupPointsIso k
            (Index.{u} n)).hom.app R x) := by
  let T := StandardGroups.multiplicativePowerGroup k (Index.{u} n)
  let B := Triangularization.upperTriangularGroup k n
  let t := StandardGroups.multiplicativePowerGroupPointsIso k (Index.{u} n)
  let b := Triangularization.upperTriangularGroupPointsIso k n
  let β := b.hom ≫ Triangularization.diagonalHom k n ≫ t.inv
  let q := (AffineAlgebraicGroup.groupHomEquiv B T).symm β
  let α := t.hom ≫ diagonalUpperPoints k n ≫ b.inv
  let j := (AffineAlgebraicGroup.groupHomEquiv T B).symm α
  have hj (R : TestAlgebra k) (x : Points T.val.X R) :
      b.hom.app R (Unipotent.onPoints j R x) = (diagonalUpperPoints k n).app R (t.hom.app R x) := by
    rw [Unipotent.scheme_hom_spec α]
    exact (b.app R).groupIsoToMulEquiv.apply_symm_apply _
  have hsec : j ≫ q = 𝟙 T.val := by
    apply Unipotent.group_hom_ext T.property.1
    intro R x
    have hq (y : Points B.val.X R) :
        t.hom.app R (Unipotent.onPoints q R y) =
          (Triangularization.diagonalHom k n).app R (b.hom.app R y) := by
      rw [Unipotent.scheme_hom_spec β]
      exact (t.app R).groupIsoToMulEquiv.apply_symm_apply _
    apply (t.app R).groupIsoToMulEquiv.injective
    change t.hom.app R (Unipotent.onPoints q R (Unipotent.onPoints j R x)) = t.hom.app R x
    rw [hq, hj]
    funext i
    apply Units.ext
    change (diagonalMatrixHom (Index.{u} n) R (t.hom.app R x)).val i i = _
    rw [diagonalMatrixHom_val, diagonal_apply_eq]
  have hclosed : IsClosedImmersion j.hom.hom.left := by
    haveI : IsAffine B.val.X.left := B.property.1
    haveI : IsSeparated B.val.X.hom := IsSeparated.of_isAffineHom _
    haveI : IsSeparated (q.hom.hom.left ≫ T.val.X.hom) := Over.w q.hom.hom ▸ inferInstance
    haveI : IsSeparated q.hom.hom.left := IsSeparated.of_comp (g := T.val.X.hom) _
    haveI : IsClosedImmersion (j.hom.hom.left ≫ q.hom.hom.left) := by
      change IsClosedImmersion (j ≫ q).hom.hom.left
      rw [hsec]
      exact inferInstanceAs (IsClosedImmersion (𝟙 T.val.X.left))
    exact IsClosedImmersion.of_comp j.hom.hom.left q.hom.hom.left
  exact ⟨j, hclosed, fun R x => congrArg Subtype.val (hj R x)⟩

private theorem diagonal_self_centralizer {n : ℕ} {G : AffineAlgebraicGroup k}
    (e : MatrixPoints G n) (T : ClosedSubgroup G.val)
    (hT : ∀ (R : TestAlgebra k) (g : Points G.val.X R),
        g ∈ SubgroupSections T ((testSpec k).obj (op R)) ↔ IsDiagonal (e.hom.app R g)) :
    RepresentsSubgroup T (fun _ g => Centralizes T.inclusion g) := by
  obtain ⟨C, hC⟩ := centralizerScheme k G T
  let A := Specs.Unipotent.closedSubgroupAlgebraicGroup T
  let B := Specs.Unipotent.closedSubgroupAlgebraicGroup C
  have htest (R : TestAlgebra k) (g : Points G.val.X R) :
      g ∈ SubgroupSections C ((testSpec k).obj (op R)) ↔
        g ∈ SubgroupSections T ((testSpec k).obj (op R)) := by
    rw [hT]
    change (∃ c : Points C.group.X R, c ≫ C.inclusion.hom.hom = g) ↔ _
    rw [← hC]
    change Centralizes T.inclusion g ↔ _
    rw [centralizes_iff_testAlgebras T.inclusion A.property.1]
    rw [diagonalCentralizerMatrices k n R (e.hom.app R g)]
    have heval (S : TestAlgebra k) (a : R ⟶ S) :
        e.hom.app S (mapPoints a g) = Matrix.GeneralLinearGroup.map a.hom.toRingHom
          (e.hom.app R g) := congrArg (fun τ => τ g) (e.hom.naturality a)
    constructor
    · intro hg S a d hd
      let y := (e.app S).groupIsoToMulEquiv.symm d
      have hy : e.hom.app S y = d := (e.app S).groupIsoToMulEquiv.apply_symm_apply _
      obtain ⟨z, hz⟩ := (hT S y).mpr (hy ▸ hd)
      change Unipotent.onPoints T.inclusion S z = y at hz
      have hh := ((hg S a z).map (e.app S).groupIsoToMulEquiv).eq
      change e.hom.app S (mapPoints a g) * e.hom.app S (Unipotent.onPoints T.inclusion S z) =
        e.hom.app S (Unipotent.onPoints T.inclusion S z) * e.hom.app S (mapPoints a g) at hh
      rw [hz, hy, heval] at hh
      exact hh
    · intro hg S a z
      let y := Unipotent.onPoints T.inclusion S z
      have hy : IsDiagonal (e.hom.app S y) := (hT S y).mp ⟨z, rfl⟩
      apply (e.app S).groupIsoToMulEquiv.injective
      simp only [map_mul]
      change e.hom.app S (mapPoints a g) * e.hom.app S y = e.hom.app S y * e.hom.app S (mapPoints a g)
      rw [heval]
      exact hg S a _ hy
  obtain ⟨p, hp⟩ := Unipotent.factor_through_closed (A := B) (B := A) (C := G)
    C.inclusion T.inclusion T.isClosedImmersion (fun R x => (htest R _).mp ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Unipotent.factor_through_closed (A := A) (B := B) (C := G)
    T.inclusion C.inclusion C.isClosedImmersion (fun R x => (htest R _).mpr ⟨x, rfl⟩)
  intro U g
  rw [hC]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x ≫ p.hom.hom, (Category.assoc _ _ _).trans
      (congrArg (fun f : C.group ⟶ G.val => x ≫ f.hom.hom) hp)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x ≫ q.hom.hom, (Category.assoc _ _ _).trans
      (congrArg (fun f : T.group ⟶ G.val => x ≫ f.hom.hom) hq)⟩

private theorem splitTorus_commutative {T : GroupScheme k}
    (h : Specs.GeometricRadicals.IsSplitTorus T) : Specs.SchemeDerivedGroup.IsCommutative T := by
  obtain ⟨r, ⟨e⟩⟩ := h
  let D := StandardGroups.multiplicativePowerGroup k (Index.{u} r)
  let c := StandardGroups.multiplicativePowerGroupPointsIso k (Index.{u} r)
  have hD : Specs.SchemeDerivedGroup.IsCommutative D.val := by
    have ha := D.property.1
    have he : fst D.val.X D.val.X * snd D.val.X D.val.X =
        snd D.val.X D.val.X * fst D.val.X D.val.X := by
      apply hom_ext_of_points (X := D.val.X ⊗ D.val.X) (by
        change IsAffine (pullback D.val.X.hom D.val.X.hom)
        infer_instance)
      intro R p
      rw [MonObj.comp_mul, MonObj.comp_mul]
      apply (c.app R).groupIsoToMulEquiv.injective
      simp only [map_mul]
      change Commute
        (c.hom.app R (p ≫ fst D.val.X D.val.X) : Index.{u} r → Rˣ)
        (c.hom.app R (p ≫ snd D.val.X D.val.X) : Index.{u} r → Rˣ)
      exact @mul_comm (Index.{u} r → Rˣ) inferInstance
        (c.hom.app R (p ≫ fst D.val.X D.val.X) : Index.{u} r → Rˣ)
        (c.hom.app R (p ≫ snd D.val.X D.val.X) : Index.{u} r → Rˣ)
    intro U x y
    simpa only [MonObj.comp_mul, lift_fst, lift_snd] using congrArg (lift x y ≫ ·) he
  intro U x y
  let f := (Grp.forget (SchemeOver k)).map e.hom
  haveI : Mono f := inferInstance
  apply (cancel_mono f).mp
  change (x * y) ≫ e.hom.hom.hom = (y * x) ≫ e.hom.hom.hom
  rw [MonObj.mul_comp, MonObj.mul_comp]
  exact hD U _ _

private theorem torus_commutative {T : GroupScheme k}
    (h : Specs.GeometricRadicals.IsTorus T) : Specs.SchemeDerivedGroup.IsCommutative T := by
  obtain ⟨E, _, _, _, hE⟩ := h
  let F := baseChange k E
  let a := fieldSpecMap k E
  have hflat : Flat a := by
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap k E)))
    rw [Flat.SpecMap_iff]
    let : Algebra k E := (CommRingCat.ofHom (algebraMap k E)).hom.toAlgebra
    exact Module.Flat.of_free (R := k) (M := E)
  have hsurj : Surjective a := fieldSpecMap_surjective E
  have hqc : QuasiCompact a := inferInstanceAs (QuasiCompact (Spec.map _))
  have hff : F.Faithful := inferInstanceAs ((Over.pullback a).Faithful)
  intro U x y
  apply hff.map_injective
  rw [F.map_mul, F.map_mul]
  exact splitTorus_commutative hE (F.obj U) (F.map x) (F.map y)

private theorem maxTorus_of_self_centralizer {G : GroupScheme k} (T : ClosedSubgroup G)
    (hT : Specs.GeometricRadicals.IsTorus T.group)
    (hC : RepresentsSubgroup T (fun _ g => Centralizes T.inclusion g)) :
    Specs.GeometricRadicals.IsMaximalTorus T := by
  refine ⟨hT, ?_⟩
  intro S hS hTS
  obtain ⟨j, hj⟩ := hTS
  have hc : Centralizes T.inclusion S.inclusion.hom.hom := by
    apply (centralizes_iff T.inclusion _).mpr
    intro U f x
    have hp : j.hom.hom ≫ S.inclusion.hom.hom = T.inclusion.hom.hom :=
      congrArg (fun a : T.group ⟶ G => a.hom.hom) hj
    rw [← hp, ← Category.assoc]
    exact (show Commute f (x ≫ j.hom.hom) from torus_commutative hS U _ _).map
      (((yonedaGrp.map S.inclusion).app (op U)).hom)
  obtain ⟨z, hz⟩ := (hC _ _).mp hc
  haveI := T.isClosedImmersion
  letI : IsMonHom z := isMonHom_of_comp_closed z S.inclusion T.inclusion hz
  exact ⟨Grp.homMk z, Grp.hom_ext _ _ hz⟩

private def baseChangePowerTorusIso (K : Type u) [Field K] [Algebra k K] (n : ℕ) :
    (groupBaseChange k K).obj (StandardGroups.multiplicativePowerGroup k (Index.{u} n)).val ≅
      (StandardGroups.multiplicativePowerGroup K (Index.{u} n)).val := by
  let D := StandardGroups.multiplicativePowerGroup k (Index.{u} n)
  let c := StandardGroups.multiplicativePowerGroupPointsIso k (Index.{u} n)
  let e : (groupPointsFunctor K).obj (groupBaseChange k K |>.obj D.val) ≅
      Specs.StandardGroups.multiplicativePowerPoints K (Index.{u} n) :=
    NatIso.ofComponents (fun R =>
      ((baseChangePointGroupEquiv K D.val R).trans
        (c.app ((restrictTestAlgebra k K).obj R)).groupIsoToMulEquiv).toGrpIso) (by
      intro R S f
      apply GrpCat.ext
      intro x
      change c.hom.app ((restrictTestAlgebra k K).obj S)
        (baseChangePoint k K D.val.X S (mapPoints f x)) = _
      rw [baseChangePointsNaturality]
      exact congrArg (fun τ => τ (baseChangePoint k K D.val.X R x))
        (c.hom.naturality ((restrictTestAlgebra k K).map f)))
  exact Unipotent.groupIsoOfPoints
    (G := Specs.Unipotent.baseChangedAlgebraicGroup K D)
    (e ≪≫ (StandardGroups.multiplicativePowerGroupPointsIso K (Index.{u} n)).symm)

end DiagonalSubgroup

section CoordinateFlag

open Specs.Triangularization (upperTriangular)
open WithConv LinearAlgebraicGroups.RationalRepresentations

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ}

private def coordinateBasis (K : Type u) [Field K] (n : ℕ) :
    Module.Basis (Fin n) K (Index.{u} n → K) :=
  (Pi.basisFun K (Index.{u} n)).reindex Equiv.ulift

omit [IsAlgClosed K] in
private theorem coordinateBasis_apply (i : Fin n) :
    coordinateBasis K n i = Pi.single (⟨i⟩ : Index.{u} n) 1 := by
  rw [coordinateBasis, Module.Basis.reindex_apply, Pi.basisFun_apply]
  rfl

omit [IsAlgClosed K] in
private theorem coordinateBasis_repr (v : Index.{u} n → K) (i : Fin n) :
    (coordinateBasis K n).repr v i = v ⟨i⟩ := by
  rw [coordinateBasis, Module.Basis.repr_reindex_apply, Pi.basisFun_repr]
  rfl

omit [IsAlgClosed K] in
private theorem diagonalAt_upper (j : Index.{u} n) (a : Kˣ) :
    (diagonalAt j a).val.IsUpperTriangular := by
  intro i l h
  change l < i at h
  rw [diagonalAt_val, diagonal_apply_ne _ h.ne']

omit [IsAlgClosed K] in
private theorem elementary_upper {i j : Index.{u} n} (hij : i < j) (a : K) :
    (Matrix.SpecialLinearGroup.toGL (elementary i j hij.ne a)).val.IsUpperTriangular := by
  intro l m h
  change m < l at h
  change (1 + Matrix.single i j a : Matrix (Index.{u} n) (Index.{u} n) K) l m = 0
  have hne : ¬ (i = l ∧ j = m) := fun ⟨hi, hj⟩ => hij.not_gt (hi ▸ hj ▸ h)
  simp [h.ne', Matrix.single, hne]

/-- A subspace invariant under the upper triangular matrices is a term of the
coordinate flag. Diagonal scalings detect the support and transvections force a prefix. -/
private theorem upper_invariant_subspace
    (W : Submodule K (Index.{u} n → K))
    (hW : ∀ (g : Matrix.GeneralLinearGroup (Index.{u} n) K), g.val.IsUpperTriangular →
      ∀ v ∈ W, g.val *ᵥ v ∈ W) :
    ∃ r : Fin (n + 1), (coordinateBasis K n).flag r = W := by
  classical
  let b := coordinateBasis K n
  let S : Set (Fin n) := {i | b i ∈ W}
  have hs : Submodule.span K (b '' S) = W := by
    apply le_antisymm
    · exact Submodule.span_le.mpr (by rintro _ ⟨i, hi, rfl⟩; exact hi)
    · intro v hv
      apply b.mem_span_image.mpr
      intro i hi
      change b i ∈ W
      rw [coordinateBasis_apply]
      have hv₀ := Finsupp.mem_support_iff.mp hi
      rw [coordinateBasis_repr] at hv₀
      exact coordinate_vector_mem_of_stable_diagonal W hv ⟨i⟩ hv₀
        (fun a => hW _ (diagonalAt_upper ⟨i⟩ a) v hv)
  have hdown {i j : Fin n} (hij : i ≤ j) (hj : j ∈ S) : i ∈ S := by
    rcases hij.eq_or_lt with rfl | hij
    · exact hj
    have hh : (⟨i⟩ : Index.{u} n) < ⟨j⟩ := hij
    change b j ∈ W at hj
    change b i ∈ W
    rw [coordinateBasis_apply] at hj ⊢
    exact coordinate_vector_mem_of_stable_transvection W _ _ hh.ne hj
      (hW _ (elementary_upper hh 1) _ hj)
  by_cases hall : ∀ i, i ∈ S
  · refine ⟨Fin.last n, ?_⟩
    have hS : S = Set.univ := Set.eq_univ_iff_forall.mpr hall
    rw [hS, Set.image_univ, b.span_eq] at hs
    exact b.flag_last.trans hs
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    let F : Finset (Fin n) := Finset.univ.filter (fun j => j ∉ S)
    have hF : F.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    let j := F.min' hF
    have hj : j ∉ S := (Finset.mem_filter.mp (F.min'_mem hF)).2
    refine ⟨j.castSucc, ?_⟩
    have he : {i : Fin n | i.castSucc < j.castSucc} = S := by
      ext l
      change l.castSucc < j.castSucc ↔ l ∈ S
      rw [Fin.castSucc_lt_castSucc_iff]
      constructor
      · intro hl
        by_contra h
        exact hl.not_ge (F.min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      · intro hl
        exact lt_of_not_ge (fun h => hj (hdown h hl))
    exact (congrArg (fun U : Set (Fin n) => Submodule.span K (b '' U)) he).trans hs

private theorem flag_unique_of_upper_invariance
    (b : Module.Basis (Fin n) K (Index.{u} n → K))
    (h : ∀ j (g : Matrix.GeneralLinearGroup (Index.{u} n) K), g.val.IsUpperTriangular →
      ∀ v ∈ b.flag j, g.val *ᵥ v ∈ b.flag j) :
    b.flag = (coordinateBasis K n).flag := by
  choose f hf using fun j => upper_invariant_subspace (b.flag j) (h j)
  have hm : StrictMono f := by
    intro i j hij
    exact (coordinateBasis K n).flag_strictMono.lt_iff_lt.mp
      (by rw [hf i, hf j]; exact b.flag_strictMono hij)
  have hf' : f = id := hm.eq_id
  funext j
  simpa only [hf', id_eq] using (hf j).symm

omit [IsAlgClosed K] in
private theorem upper_of_preserves_coordinateFlag (g : Matrix.GeneralLinearGroup (Index.{u} n) K)
    (h : ∀ j v, v ∈ (coordinateBasis K n).flag j → g.val *ᵥ v ∈ (coordinateBasis K n).flag j) :
    g.val.IsUpperTriangular := by
  intro i j hij
  change j < i at hij
  let b := coordinateBasis K n
  have hmem : b j.down ∈ b.flag j.down.succ :=
    b.self_mem_flag (by exact Nat.lt_succ_self _)
  have hh := (b.mem_flag_iff_repr_eq_zero.mp (h j.down.succ (b j.down) hmem)) i.down
    (show j.down.succ ≤ i.down.castSucc from Nat.succ_le_of_lt hij)
  rw [coordinateBasis_repr, coordinateBasis_apply, mulVec_single_one] at hh
  exact hh

end CoordinateFlag

section Solvability

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open Specs.SchemeDerivedGroup (DerivedSeries IsSplitSolvable)
open private Unipotent.onPoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
open private GeometricRadicals.derivedSeries_sections GeometricRadicals.rationalMap
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals

variable {k : Type u} [Field k]

private theorem points_solvable_of_split {G : GroupScheme k}
    (hG : IsSplitSolvable G) (R : TestAlgebra k) : Group.IsSolvable (Points G.X R) := by
  let X := (testSpec k).obj (op R)
  induction hG with
  | @trivial G h =>
    obtain ⟨e⟩ := h
    haveI : Subsingleton (Points G.X R) := ⟨fun x y => by
      let φ := (Grp.forget (SchemeOver k)).map e.hom
      apply (cancel_mono φ).mp
      exact isTerminalTensorUnit.hom_ext _ _⟩
    infer_instance
  | @step G D _ _ Q q hq htype ih =>
    haveI : Group.IsSolvable (((groupPointsFunctor k).obj D.group).obj R) := ih
    haveI : IsMulCommutative (Points Q.val.X R) := by
      rcases htype with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
      · refine ⟨⟨fun x y => (e.app R).groupIsoToMulEquiv.injective ?_⟩⟩
        simp only [map_mul]
        change (e.hom.app R x : Multiplicative R) * e.hom.app R y =
          (e.hom.app R y : Multiplicative R) * e.hom.app R x
        exact @mul_comm (Multiplicative R) inferInstance _ _
      · refine ⟨⟨fun x y => (e.app R).groupIsoToMulEquiv.injective ?_⟩⟩
        simp only [map_mul]
        change (e.hom.app R x : Rˣ) * e.hom.app R y =
          (e.hom.app R y : Rˣ) * e.hom.app R x
        exact @mul_comm (Rˣ) inferInstance _ _
    haveI : Group.IsSolvable (Points Q.val.X R) := inferInstance
    haveI : Group.IsSolvable ((groupPointsFunctor k).obj Q.val |>.obj R) :=
      (inferInstance : Group.IsSolvable (Points Q.val.X R))
    apply Group.isSolvable_of_ker_le_range
      (f := Unipotent.onPoints D.inclusion R) (g := Unipotent.onPoints q R)
    intro g hg
    obtain ⟨e, he⟩ := hq
    have heval (p : Points G.X R) :
        e.hom.hom.app (op X) (projectSection D p) = ULift.up (Unipotent.onPoints q R p) :=
      congrArg (fun a => a.hom.app (op X) (ULift.up p)) he
    have hinj : Function.Injective (e.hom.hom.app (op X)) := by
      let F := sheafToPresheaf (fppfOver k) (Type (u + 1)) ⋙
        (evaluation _ _).obj (op X)
      haveI : IsIso (e.hom.hom.app (op X)) := F.map_isIso e.hom
      exact (ConcreteCategory.bijective_of_isIso _).1
    obtain ⟨p, hp⟩ := (rightQuotientProjectionEquality D (1 : Points G.X R) g).mp
      (hinj (by rw [heval, heval, map_one, MonoidHom.mem_ker.mp hg]))
    exact ⟨p, hp.trans (by rw [inv_one, one_mul])⟩

private def rationalPointsEquiv (K : Type u) [Field K] (G : GroupScheme K) :
    ((𝟙_ (SchemeOver K)) ⟶ G.X) ≃* Points G.X (CommAlgCat.of K K) :=
  ((yonedaGrp.obj G).mapIso (fieldTestSpecIso K).op).groupIsoToMulEquiv

private theorem geometric_series (K : Type u) [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom) (hc : GeometricallyConnected G.val.X.hom)
    {n : ℕ} {H : GroupScheme k} (h : DerivedSeries G.val n H) :
    ∃ (i : H ⟶ G.val) (_ : IsClosedImmersion i.hom.hom.left),
      Smooth H.X.hom ∧ GeometricallyConnected H.X.hom ∧
      DerivedSeries ((groupBaseChange k K).obj G.val) n ((groupBaseChange k K).obj H) := by
  let F := groupBaseChange k K
  induction h with
  | zero =>
    exact ⟨𝟙 G.val, inferInstanceAs (IsClosedImmersion (𝟙 G.val.X.left)), hs, hc,
      DerivedSeries.zero⟩
  | @succ n H _ D hD ih =>
    obtain ⟨i, hi, hHs, hHc, hseries⟩ := ih
    let A := Specs.Unipotent.closedSubgroupAlgebraicGroup (⟨H, i, hi⟩ : ClosedSubgroup G.val)
    obtain ⟨hsD, hcD⟩ :=
      Reductive.DerivedSubgroup.derivedSubgroupGeometry A D hD hHs hHc
    obtain ⟨hDK, hd, _⟩ :=
      Reductive.DerivedSubgroup.derivedSubgroupBaseChange K A D hD hHs hHc
    letI := hi
    letI := D.isClosedImmersion
    exact ⟨D.inclusion ≫ i, IsClosedImmersion.comp _ _, hsD, hcD,
      DerivedSeries.succ hseries ⟨F.obj D.group, F.map D.inclusion, hDK⟩ hd⟩

private theorem smooth_baseChanged (K : Type u) [Field K] [Algebra k K] {G : GroupScheme k}
    (h : Smooth G.X.hom) : Smooth ((groupBaseChange k K).obj G).X.hom :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.X.hom (fieldSpecMap k K)) h

private theorem connected_baseChanged (K : Type u) [Field K] [Algebra k K] {G : GroupScheme k}
    (h : GeometricallyConnected G.X.hom) : ConnectedSpace ((groupBaseChange k K).obj G).X.left :=
  h.geometrically_connectedSpace _ _ _ (IsPullback.of_hasPullback G.X.hom (fieldSpecMap k K))

private theorem solvable_of_geometric_sections (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom) (hc : GeometricallyConnected G.val.X.hom)
    (h : Group.IsSolvable ((𝟙_ (SchemeOver K)) ⟶ ((groupBaseChange k K).obj G.val).X)) :
    Specs.SchemeDerivedGroup.IsSolvable G.val := by
  obtain ⟨⟨n, hn⟩⟩ := h
  obtain ⟨H, hH⟩ := SchemeDerivedGroup.derivedSeriesExists G n
  obtain ⟨i, hi, hHs, _, hser⟩ := geometric_series K G hs hc hH
  let F := groupBaseChange k K
  let GK := Specs.Unipotent.baseChangedAlgebraicGroup K G
  obtain ⟨j, hj, _, _, hJ⟩ := GeometricRadicals.derivedSeries_sections GK
    (smooth_baseChanged K hs) (connected_baseChanged K hc) hser
  have hJ' : (GeometricRadicals.rationalMap j).range = ⊥ := hJ.trans hn
  have hp (p : (𝟙_ (SchemeOver K)) ⟶ (F.obj H.val).X) :
      GeometricRadicals.rationalMap j p = 1 := by
    have hm : GeometricRadicals.rationalMap j p ∈ (GeometricRadicals.rationalMap j).range := ⟨p, rfl⟩
    exact Subgroup.mem_bot.mp (hJ' ▸ hm)
  haveI : Mono j.hom.hom := Over.mono_of_mono_left j.hom.hom
  letI hSub : Subsingleton ((𝟙_ (SchemeOver K)) ⟶ (F.obj H.val).X) :=
    ⟨fun p q => (cancel_mono j.hom.hom).mp ((hp p).trans (hp q).symm)⟩
  let R := CommAlgCat.of K K
  let eq := (rationalPointsEquiv K (F.obj H.val)).trans (baseChangePointGroupEquiv K H.val R)
  have hRest : Subsingleton (Points H.val.X ((restrictTestAlgebra k K).obj R)) :=
    eq.symm.injective.subsingleton
  let I := Specs.GeometricRadicals.identitySubgroup H
  obtain ⟨g, hg⟩ := factor_on_geometric_points K (𝟙 H.val) I hHs (fun p => by
    have he : Unipotent.onPoints (𝟙 H.val) ((restrictTestAlgebra k K).obj R) p = 1 :=
      hRest.elim _ _
    rw [he]
    exact (SubgroupSections I _).one_mem)
  haveI := I.isClosedImmersion
  haveI : Mono I.inclusion := (Grp.forget (SchemeOver k)).mono_of_mono_map
    (Over.mono_of_mono_left I.inclusion.hom.hom)
  refine ⟨n, H.val, hH, ⟨⟨g, I.inclusion, hg, ?_⟩⟩⟩
  apply (cancel_mono I.inclusion).mp
  rw [Category.assoc, hg, Category.comp_id, Category.id_comp]

end Solvability

section SchemeBorel

open WithConv LinearAlgebraicGroups.RationalRepresentations
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Specs.GeometricRadicals (baseChangedSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Triangularization (upperTriangular)
open private groupPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private GeometricRadicals.solvable_iff_sections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private Unipotent.onPoints Unipotent.onPoints_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries

variable {K : Type u} [Field K] {n : ℕ}

private theorem stable_under_eval (A : HopfAlgebraCategory K)
    (ρ : RightComodule K A (Index.{u} n → K)) (W : Submodule K (Index.{u} n → K))
    (hW : ρ.IsSubcomodule W) (g : A →ₐ[K] K) (v : Index.{u} n → K) (hv : v ∈ W) :
    TensorProduct.rid K (Index.{u} n → K) (evaluate A ρ g v) ∈ W := by
  obtain ⟨z, hz⟩ := hW ⟨v, hv⟩
  change W.subtype.rTensor A z = ρ.coaction v at hz
  rw [evaluate, LinearMap.comp_apply, ← hz]
  clear hz
  refine TensorProduct.inductionOn z (fun w a => ?_) (fun z t hz ht => ?_)
  · rw [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    exact W.smul_mem _ w.property
  · simp only [map_add]
    exact W.add_mem hz ht

private theorem restrict_self_field (K : Type u) [Field K] :
    (restrictTestAlgebra K K).obj (CommAlgCat.of K K) = CommAlgCat.of K K := by
  let a : Algebra K K := ((algebraMap K K).comp (algebraMap K K)).toAlgebra
  have h : a = (inferInstance : Algebra K K) := Algebra.algebra_ext _ _ (by intro x; rfl)
  change @CommAlgCat.of K _ K _ a = CommAlgCat.of K K
  rw [h]

private theorem borel_maximal_of_upper [IsAlgClosed K] {G : AffineAlgebraicGroup K}
    (e : MatrixPoints G n) (B : ClosedSubgroup G.val)
    (hB : ∀ (R : TestAlgebra K) (g : Points G.val.X R),
      g ∈ SubgroupSections B ((testSpec K).obj (op R)) ↔ (e.hom.app R g).val.IsUpperTriangular)
    (H : ClosedSubgroup G.val) (hs : Smooth H.group.X.hom) (hc : ConnectedSpace H.group.X.left)
    (hsol : Specs.SchemeDerivedGroup.IsSolvable H.group)
    (hBH : IsSubgroupOf B H) : IsSubgroupOf H B := by
  let R : TestAlgebra K := CommAlgCat.of K K
  let V := Index.{u} n → K
  let J := Specs.Unipotent.closedSubgroupAlgebraicGroup H
  obtain ⟨A, _, ⟨i⟩⟩ := groupPresentation J
  let c := hopfSpecPointIso A ≪≫ (groupPointsFunctor K).mapIso i
  let α := c.hom ≫ (groupPointsFunctor K).map H.inclusion ≫ e.hom
  let E := pointsCoactionEquiv A (Pi.basisFun K (Index.{u} n))
  let ρ := E α
  have hsAct (W : Submodule K V) (hW : ρ.IsSubcomodule W) (p : Points H.group.X R)
      (v : V) (hv : v ∈ W) :
      (e.hom.app R (Unipotent.onPoints H.inclusion R p)).val *ᵥ v ∈ W := by
    let g := (c.app R).groupIsoToMulEquiv.symm p
    have hg : c.hom.app R g = p := (c.app R).groupIsoToMulEquiv.apply_symm_apply p
    have he := congrArg (fun β => (β.app R g).val) (E.symm_apply_apply α)
    change g.ofConv.mapMatrix (coefficients A (Pi.basisFun K _) ρ) =
      (e.hom.app R (Unipotent.onPoints H.inclusion R (c.hom.app R g))).val at he
    rw [hg] at he
    rw [← he, ← evaluate_column_action A ρ g.ofConv]
    exact stable_under_eval A ρ W hW g.ofConv v hv
  have hflag := (LieKolchin.invariantFullFlag J A i hs hc hsol) V ρ
  have hdim : Module.finrank K V = n := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [Index]
  rw [hdim] at hflag
  obtain ⟨b, hb⟩ := hflag
  let b' := b.reindex Equiv.ulift
  have hb' (j : Fin (n + 1)) : ρ.IsSubcomodule (b'.flag j) := by
    have he : b' '' {l : Fin n | l.castSucc < j} = b '' {l : Index.{u} n | l.down.val < j.val} := by
      ext v
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact ⟨⟨l⟩, hl, by simp [b', Module.Basis.reindex_apply]⟩
      · rintro ⟨l, hl, rfl⟩
        exact ⟨l.down, hl, by simp [b', Module.Basis.reindex_apply]⟩
    rw [Module.Basis.flag, he]
    exact hb j
  have hstable (p : Points H.group.X R) (j : Fin (n + 1)) (v : V) (hv : v ∈ b'.flag j) :
      (e.hom.app R (Unipotent.onPoints H.inclusion R p)).val *ᵥ v ∈ b'.flag j :=
    hsAct _ (hb' j) p v hv
  obtain ⟨j, hj⟩ := hBH
  have hBstable (r : Fin (n + 1)) (g : Matrix.GeneralLinearGroup (Index.{u} n) K)
      (hg : g.val.IsUpperTriangular) (v : V) (hv : v ∈ b'.flag r) :
      g.val *ᵥ v ∈ b'.flag r := by
    let p := (e.app R).groupIsoToMulEquiv.symm g
    have hp : e.hom.app R p = g := (e.app R).groupIsoToMulEquiv.apply_symm_apply _
    obtain ⟨q, hq⟩ := (hB R p).mpr (hp ▸ hg)
    change Unipotent.onPoints B.inclusion R q = p at hq
    have hh : Unipotent.onPoints H.inclusion R (Unipotent.onPoints j R q) = p :=
      (congrArg (fun f => Unipotent.onPoints f R q) hj).trans hq
    have hm := hstable (Unipotent.onPoints j R q) r v hv
    rw [hh, hp] at hm
    exact hm
  have heq := flag_unique_of_upper_invariance b' hBstable
  apply factor_on_geometric_points K (A := J) H.inclusion B hs
  rw [restrict_self_field K]
  intro p
  apply (hB R _).mpr
  apply upper_of_preserves_coordinateFlag (K := K)
  intro r v hv
  change (e.hom.app R (Unipotent.onPoints H.inclusion R p)).val *ᵥ v ∈
    (coordinateBasis K n).flag r
  rw [← heq]
  exact hstable p r v (by rwa [heq])

private theorem baseChange_subgroup_points {k : Type u} [Field k] (K : Type u) [Field K]
    [Algebra k K] {G : GroupScheme k} (D : ClosedSubgroup G)
    (hD : IsClosedImmersion ((groupBaseChange k K).map D.inclusion).hom.hom.left)
    (R : TestAlgebra K) (p : Points ((groupBaseChange k K).obj G).X R) :
    p ∈ SubgroupSections (baseChangedSubgroup K D hD) ((testSpec K).obj (op R)) ↔
      baseChangePoint k K G.X R p ∈
        SubgroupSections D ((testSpec k).obj (op ((restrictTestAlgebra k K).obj R))) := by
  let F := baseChange k K
  constructor
  · rintro ⟨x, hx⟩
    change x ≫ F.map D.inclusion.hom.hom = p at hx
    refine ⟨baseChangePoint k K D.group.X R x, ?_⟩
    change baseChangePoint k K D.group.X R x ≫ D.inclusion.hom.hom = _
    rw [← baseChangePointsSchemeNaturality, hx]
  · rintro ⟨x, hx⟩
    change x ≫ D.inclusion.hom.hom = _ at hx
    obtain ⟨y, hy⟩ := (baseChangePoints k K D.group.X R).surjective x
    refine ⟨y, (baseChangePoints k K G.X R).injective ?_⟩
    change baseChangePoint k K G.X R (y ≫ F.map D.inclusion.hom.hom) = _
    rw [baseChangePointsSchemeNaturality, hy, hx]

/-- The diagonal split torus and the upper triangular Borel in the general linear group. -/
theorem generalLinearBorelPair : GeneralLinearBorelPair.{u} := by
  intro k _ n _ G e
  let B₀ := Triangularization.upperTriangularGroup k n
  let T₀ := StandardGroups.multiplicativePowerGroup k (Index.{u} n)
  let b := Triangularization.upperTriangularGroupPointsIso k n
  let t := StandardGroups.multiplicativePowerGroupPointsIso k (Index.{u} n)
  obtain ⟨i, hi, hib⟩ := upper_inclusion e
  obtain ⟨j, hj, hjt⟩ := diagonal_in_upper k n
  let B : ClosedSubgroup G.val := ⟨B₀.val, i, hi⟩
  have htclose : IsClosedImmersion (j ≫ i).hom.hom.left := by
    letI := hi
    letI := hj
    exact IsClosedImmersion.comp _ _
  let T : ClosedSubgroup G.val := ⟨T₀.val, j ≫ i, htclose⟩
  have hB (R : TestAlgebra k) (g : Points G.val.X R) :
      g ∈ SubgroupSections B ((testSpec k).obj (op R)) ↔ (e.hom.app R g).val.IsUpperTriangular := by
    change (∃ x : Points B₀.val.X R, Unipotent.onPoints i R x = g) ↔ _
    constructor
    · rintro ⟨x, rfl⟩
      rw [hib]
      exact (b.hom.app R x).property
    · intro hg
      let z : upperTriangular (Index.{u} n) R := ⟨e.hom.app R g, hg⟩
      let x := (b.app R).groupIsoToMulEquiv.symm z
      refine ⟨x, (e.app R).groupIsoToMulEquiv.injective ?_⟩
      change e.hom.app R (Unipotent.onPoints i R x) = e.hom.app R g
      rw [hib, show b.hom.app R x = z from (b.app R).groupIsoToMulEquiv.apply_symm_apply _]
  have hjti (R : TestAlgebra k) (x : Points T₀.val.X R) :
      e.hom.app R (Unipotent.onPoints (j ≫ i) R x) =
        diagonalMatrixHom _ _ (t.hom.app R x) := by
    rw [Unipotent.onPoints_comp, hib]
    exact hjt R x
  have hT (R : TestAlgebra k) (g : Points G.val.X R) :
      g ∈ SubgroupSections T ((testSpec k).obj (op R)) ↔ IsDiagonal (e.hom.app R g) := by
    change (∃ x : Points T₀.val.X R, Unipotent.onPoints (j ≫ i) R x = g) ↔ _
    constructor
    · rintro ⟨x, rfl⟩
      rw [hjti]
      intro a b hab
      rw [diagonalMatrixHom_val, diagonal_apply_ne _ hab]
    · intro hg
      obtain ⟨z, hz⟩ := diagonal_units_surjective _ hg
      let x := (t.app R).groupIsoToMulEquiv.symm z
      refine ⟨x, (e.app R).groupIsoToMulEquiv.injective ?_⟩
      change e.hom.app R (Unipotent.onPoints (j ≫ i) R x) = e.hom.app R g
      rw [hjti, show t.hom.app R x = z from (t.app R).groupIsoToMulEquiv.apply_symm_apply _, hz]
  have hC := diagonal_self_centralizer e T hT
  obtain ⟨hs, hc⟩ := upper_geometry k n
  have hsplit := Triangularization.upperTriangularSplitSolvable k n B₀ b
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let GK := Specs.Unipotent.baseChangedAlgebraicGroup K G
  let eK : MatrixPoints GK n := baseChangeMatrixPoints K e
  let R := CommAlgCat.of K K
  let m := (rationalPointsEquiv K (F.obj B.group)).trans (baseChangePointGroupEquiv K B.group R)
  haveI : Group.IsSolvable (Points B.group.X ((restrictTestAlgebra k K).obj R)) :=
    points_solvable_of_split hsplit _
  have hsolK : Group.IsSolvable ((𝟙_ (SchemeOver K)) ⟶ (F.obj B.group).X) :=
    Group.isSolvable_of_isSolvable_injective (f := m.toMonoidHom) m.injective
  have hsol := solvable_of_geometric_sections K B₀ hs hc hsolK
  obtain ⟨hTK, hCK⟩ := centralizerSchemeBaseChange k K T.inclusion T hC
  have hBK := baseChangeClosedSubgroup k K B.inclusion B.isClosedImmersion
  let TK := baseChangedSubgroup K T hTK
  let BK := baseChangedSubgroup K B hBK
  refine ⟨T, B, hT, hB, ⟨n, ⟨Iso.refl _⟩⟩, ⟨j, rfl⟩, hC, hs, hc, hsol, hTK, hBK, ?_, ?_⟩
  · apply maxTorus_of_self_centralizer TK _ hCK
    let f : TK.group ≅ (StandardGroups.multiplicativePowerGroup K (Index.{u} n)).val :=
      baseChangePowerTorusIso K n
    exact ⟨K, inferInstance, inferInstance, inferInstance,
      ⟨n, ⟨(groupBaseChange K K).mapIso f ≪≫ baseChangePowerTorusIso K n⟩⟩⟩
  · have hBs := smooth_baseChanged K (G := B.group) hs
    have hBc := connected_baseChanged K (G := B.group) hc
    let BKₐ := Specs.Unipotent.closedSubgroupAlgebraicGroup (G := GK) BK
    have hBsol := (GeometricRadicals.solvable_iff_sections BKₐ hBs hBc).mpr hsolK
    refine ⟨hBs, hBc, hBsol, borel_maximal_of_upper eK BK ?_⟩
    intro A p
    rw [baseChange_subgroup_points K B hBK, hB]
    rfl

end SchemeBorel

section RankOne

open CategoryTheory.MonoidalCategory
open private Unipotent.onPoints Unipotent.scheme_hom_spec Unipotent.closed_surjective_points_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries

private theorem rankOne_diagonal {R : Type u} [CommRing R]
    (g : Matrix.GeneralLinearGroup (Index.{u} 1) R) : IsDiagonal g :=
  fun _ _ h => (h (Subsingleton.elim _ _)).elim

private theorem rankOne_scalar_bijective (R : Type u) [CommRing R] :
    Function.Bijective (Matrix.GeneralLinearGroup.scalar (Index.{u} 1) : Rˣ →
      Matrix.GeneralLinearGroup (Index.{u} 1) R) := by
  constructor
  · intro a b h
    let i : Index.{u} 1 := ⟨0⟩
    have hi := congrArg (fun g : Matrix.GeneralLinearGroup (Index.{u} 1) R => g.val i i) h
    apply Units.ext
    simpa only [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] using hi
  · intro g
    have hg (h : Matrix.GeneralLinearGroup (Index.{u} 1) R) : g * h = h * g := by
      apply Units.ext
      change g.val * h.val = h.val * g.val
      rw [eq_diagonal_of_isDiagonal (rankOne_diagonal g), eq_diagonal_of_isDiagonal (rankOne_diagonal h)]
      exact (commute_diagonal _ _).eq
    obtain ⟨a, ha⟩ := (scalarCenterMatrices 1 Nat.zero_lt_one R g).mp hg
    exact ⟨a, Units.ext ((Matrix.GeneralLinearGroup.coe_scalar a).trans ha.symm)⟩

private theorem rankOne_special_eq_one {R : Type u} [CommRing R]
    (a : Matrix.SpecialLinearGroup (Index.{u} 1) R) : a = 1 := by
  apply Subtype.ext
  ext i j
  obtain rfl := Subsingleton.elim i j
  change a.val i i = (1 : Matrix (Index.{u} 1) (Index.{u} 1) R) i i
  rw [Matrix.one_apply_eq, ← Matrix.det_eq_elem_of_subsingleton a.val i]
  exact a.property

/-- The matrix identifications at (n=1) hold over the original ground field. -/
theorem generalLinearRankOne : GeneralLinearRankOne.{u} := by
  intro k _ G S M e s m
  have eG : Nonempty (G.val ≅ M.val) := by
    let α := m.hom ≫ scalarPoints k 1 ≫ e.inv
    let f := (AffineAlgebraicGroup.groupHomEquiv M G).symm α
    have : IsIso f := isIso_of_bijective_points (G := M) (H := G) f (fun R => by
      have he : (Unipotent.onPoints f R : Points M.val.X R → Points G.val.X R) =
          (e.app R).groupIsoToMulEquiv.symm ∘
            Matrix.GeneralLinearGroup.scalar (Index.{u} 1) ∘ (m.app R).groupIsoToMulEquiv :=
        funext (Unipotent.scheme_hom_spec α R)
      rw [he]
      exact (e.app R).groupIsoToMulEquiv.symm.bijective.comp
        ((rankOne_scalar_bijective R).comp (m.app R).groupIsoToMulEquiv.bijective))
    exact ⟨(asIso f).symm⟩
  have eS : Nonempty (S.val ≅ Grp.trivial (SchemeOver k)) := by
    let D := Specs.GeometricRadicals.identitySubgroup S
    let A := Specs.Unipotent.closedSubgroupAlgebraicGroup (G := S) D
    have h : IsIso D.inclusion := Unipotent.closed_surjective_points_iso (A := A) (B := S)
      D.inclusion D.isClosedImmersion (fun R x => by
        have hₓ : x = 1 := (s.app R).groupIsoToMulEquiv.injective (by
          rw [map_one]
          exact rankOne_special_eq_one _)
        exact ⟨1, (map_one _).trans hₓ.symm⟩)
    exact ⟨(asIso D.inclusion).symm⟩
  refine ⟨eG, eS, fun D hD => ?_⟩
  apply Unipotent.closed_surjective_points_iso
    (A := Specs.Unipotent.closedSubgroupAlgebraicGroup (G := G) D) (B := G)
    D.inclusion D.isClosedImmersion
  intro R g
  rcases hD with hD | hD
  · exact (hD R g).mpr (rankOne_diagonal _)
  · apply (hD R g).mpr
    intro i j hij
    change j < i at hij
    exact (hij.ne (Subsingleton.elim _ _)).elim

end RankOne

end

end LinearAlgebraicGroups.GeneralLinearStructure
