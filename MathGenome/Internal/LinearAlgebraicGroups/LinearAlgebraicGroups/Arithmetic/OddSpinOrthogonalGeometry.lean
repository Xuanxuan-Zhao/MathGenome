import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OddSpinOrthogonalGeometry
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open WithConv

universe u

namespace LinearAlgebraicGroups.OddSpinOrthogonalGeometry

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme)
open Specs.OddSpinOrthogonalGeometry
open Specs.GeometricRadicals
open private centralizes_iff mono_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private hom_ext_on_affine_tests from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private groupBaseChangePointIso pointMatrix pointMatrix_evaluation pointMatrix_isCoactionMatrix
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
open private affineBaseTerminal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SplitFixedPoint
open private trivial_of_subsingleton_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private torus_commutative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private factor_group_through_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private torus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private isTorus_iff_coordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {n : ℕ}

@[simp] private theorem partner_e (i : Fin n) : partner (e i) = f i := rfl
@[simp] private theorem partner_f (i : Fin n) : partner (f i) = e i := rfl
@[simp] private theorem partner_r : partner (r n) = r n := rfl
@[simp] private theorem e_ne_r (i : Fin n) : e i ≠ r n := by simp [e, r]
@[simp] private theorem f_ne_r (i : Fin n) : f i ≠ r n := by simp [f, r]
@[simp] private theorem r_ne_e (i : Fin n) : r n ≠ e i := (e_ne_r i).symm
@[simp] private theorem r_ne_f (i : Fin n) : r n ≠ f i := (f_ne_r i).symm
@[simp] private theorem e_ne_f (i j : Fin n) : e i ≠ f j := by simp [e, f]
@[simp] private theorem f_ne_e (i j : Fin n) : f i ≠ e j := (e_ne_f j i).symm
@[simp] private theorem e_inj (i j : Fin n) : e i = e j ↔ i = j := by simp [e]
@[simp] private theorem f_inj (i j : Fin n) : f i = f j ↔ i = j := by simp [f]

private theorem index_cases (j : Index n) : (∃ i, j = e i) ∨ (∃ i, j = f i) ∨ j = r n := by
  rcases j with ⟨(i | ⟨⟩)⟩
  · rcases i with (i | i)
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
  · exact Or.inr (Or.inr rfl)

@[simp] private theorem entry_e {A : Type u} [CommRing A] (t : Fin n → Aˣ) (i : Fin n) :
    diagonalEntry t (e i) = t i := rfl

@[simp] private theorem entry_f {A : Type u} [CommRing A] (t : Fin n → Aˣ) (i : Fin n) :
    diagonalEntry t (f i) = ↑((t i)⁻¹) := rfl

@[simp] private theorem entry_r {A : Type u} [CommRing A] (t : Fin n → Aˣ) :
    diagonalEntry t (r n) = 1 := rfl

private abbrev Mat (n : ℕ) (A : Type u) := Matrix (Index.{u} n) (Index.{u} n) A

private abbrev mat {A : Type u} [CommRing A] (g : orthogonalMatrices n A) : Mat n A :=
  g.val.val

private theorem mat_injective {A : Type u} [CommRing A] :
    Function.Injective (mat (n := n) (A := A)) :=
  Subtype.val_injective.comp Subtype.val_injective

section Shear

variable {A : Type u} [CommRing A]

private theorem gram_mul_single (a b : Index n) (c : A) :
    gram n A * single a b c = single (partner a) b ((if partner a = r n then 2 else 1) * c) := by
  have h (a : Index n) : partner (partner a) = a := by
    rcases index_cases a with ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl <;> rfl
  ext x y
  by_cases hy : y = b
  · subst y
    rw [mul_single_apply_same, single_apply, gram]
    have hh : a = partner x ↔ partner a = x := by
      constructor
      · intro hx
        rcases index_cases x with ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl <;> simp_all
      · intro hx
        rw [← hx, h]
    by_cases hx : x = partner a
    · subst x
      simp [h]
    · simp [hh, Ne.symm hx]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hy, single_apply_of_col_ne _ _ (Ne.symm hy) _]

private theorem single_mul_gram (a b : Index n) (c : A) :
    single a b c * gram n A = single a (partner b) (c * (if b = r n then 2 else 1)) := by
  ext x y
  by_cases hx : x = a
  · subst x
    rw [single_mul_apply_same, single_apply, gram]
    by_cases hy : y = partner b <;> simp [hy, eq_comm]
  · rw [single_mul_apply_of_ne _ _ _ _ _ hx, single_apply_of_row_ne (Ne.symm hx)]

private theorem gram_at_pair {a b : Index n} (ha : partner a = b)
    (har : a ≠ r n) (hbr : b ≠ r n) (hab : a ≠ b) :
    (1 + single a (r n) (2 : A) + single (r n) b (-1) + single a b (-1))ᵀ *
        gram n A * (1 + single a (r n) 2 + single (r n) b (-1) + single a b (-1)) =
      gram n A := by
  have hl :
      (1 + single a (r n) (2 : A) + single (r n) b (-1) + single a b (-1))ᵀ * gram n A =
        gram n A + single (r n) b 2 + single b (r n) ((-1 : A) * 2) + single b b (-1) := by
    simp [transpose_add, add_mul, single_mul_gram, ha, har]
  rw [hl]
  simp [mul_add, add_mul, gram_mul_single, ha, hbr, Ne.symm har, Ne.symm hab]
  ext x y
  simp only [Matrix.add_apply, single_apply]
  split_ifs <;> ring

private def shear (a b : Index n) (ha : partner a = b) (_hb : partner b = a)
    (har : a ≠ r n) (hbr : b ≠ r n) (hab : a ≠ b) : orthogonalMatrices n A := by
  let M : Mat n A := 1 + single a (r n) 2 + single (r n) b (-1) + single a b (-1)
  refine ⟨⟨M, ?_⟩, gram_at_pair ha har hbr hab⟩
  have hM : M = transvection (r n) b (-1) * transvection a (r n) 2 *
      transvection a b (-1) := by
    simp only [M, transvection, add_mul, mul_add, mul_one, one_mul]
    simp [Ne.symm hab, Ne.symm har, add_assoc, add_comm, add_left_comm]
  simp only [hM, det_mul, det_transvection_of_ne (r n) b (Ne.symm hbr) (-1 : A),
    det_transvection_of_ne a (r n) har (2 : A), det_transvection_of_ne a b hab (-1 : A), one_mul]

private abbrev shearE (i : Fin n) : orthogonalMatrices n A :=
  shear (e i) (f i) rfl rfl (e_ne_r i) (f_ne_r i) (e_ne_f i i)

private abbrev shearF (i : Fin n) : orthogonalMatrices n A :=
  shear (f i) (e i) rfl rfl (f_ne_r i) (e_ne_r i) (f_ne_e i i)

end Shear

section Diagonal

variable {k : Type u} [Field k] {O : AffineAlgebraicGroup k} {T : ClosedSubgroup O.val}
    (m : MarkedModel n O T)

private def matrixPoints (A : TestAlgebra k) :
    Points O.val.X A ≃* orthogonalMatrices n A :=
  (m.orthogonal.app A).groupIsoToMulEquiv

private def unitsPoints (A : TestAlgebra k) :
    Points T.group.X A ≃* (Fin n → Aˣ) :=
  (m.torus.app A).groupIsoToMulEquiv

private theorem matrixPoints_map {A B : TestAlgebra k} (s : A ⟶ B) (g : Points O.val.X A) :
    mat (matrixPoints m B (mapPoints s g)) =
      s.hom.toRingHom.mapMatrix (mat (matrixPoints m A g)) := by
  exact congrArg mat (DFunLike.congr_fun (congrArg GrpCat.Hom.hom (m.orthogonal.hom.naturality s)) g)

private theorem matrixPoints_torus (A : TestAlgebra k) (t : Points T.group.X A) :
    mat (matrixPoints m A (t ≫ T.inclusion.hom.hom)) =
      diagonal (diagonalEntry (unitsPoints m A t)) :=
  m.inclusion_matrix _ _

private def weight : Index n → (Fin n → ℤ)
  | ⟨.inl (.inl i)⟩ => Pi.single i 1
  | ⟨.inl (.inr i)⟩ => Pi.single i (-1)
  | ⟨.inr ()⟩ => 0

private theorem weight_injective : Function.Injective (weight (n := n)) := by
  intro i j h
  rcases index_cases i with ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl <;>
    rcases index_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ | rfl
  · by_contra hn
    have hij : i ≠ j := fun he ↦ hn (congrArg e he)
    simpa [weight, e, Pi.single_eq_of_ne hij] using congrFun h i
  · by_cases hij : i = j
    · subst j
      simpa [weight, e, f] using congrFun h i
    · simpa [weight, e, f, Pi.single_eq_of_ne hij] using congrFun h i
  · simpa [weight, e, r] using congrFun h i
  · by_cases hij : i = j
    · subst j
      simpa [weight, e, f] using congrFun h i
    · simpa [weight, e, f, Pi.single_eq_of_ne hij] using congrFun h i
  · by_contra hn
    have hij : i ≠ j := fun he ↦ hn (congrArg f he)
    simpa [weight, f, Pi.single_eq_of_ne hij] using congrFun h i
  · simpa [weight, f, r] using congrFun h i
  · simpa [weight, e, r] using congrFun h j
  · simpa [weight, f, r] using congrFun h j
  · rfl

private abbrev Laurent (n : ℕ) (A : Type u) [Semiring A] := AddMonoidAlgebra A (Fin n → ℤ)

private def universalScale (n : ℕ) (A : Type u) [CommRing A] (i : Fin n) : (Laurent n A)ˣ :=
  ⟨AddMonoidAlgebra.single (Pi.single i 1) (1 : A), AddMonoidAlgebra.single (Pi.single i (-1)) (1 : A),
    by rw [AddMonoidAlgebra.single_mul_single, ← Pi.single_add]; norm_num; rfl,
    by rw [AddMonoidAlgebra.single_mul_single, ← Pi.single_add]; norm_num; rfl⟩

private theorem universalEntry (A : Type u) [CommRing A] (i : Index n) :
    diagonalEntry (universalScale n A) i = AddMonoidAlgebra.single (weight i) (1 : A) := by
  rcases index_cases i with ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl <;> rfl

private theorem diagonal_of_commutes (A : TestAlgebra k) (g : Points O.val.X A)
    (h : ∀ (B : TestAlgebra k) (s : A ⟶ B) (t : Points T.group.X B),
      Commute (mapPoints s g) (t ≫ T.inclusion.hom.hom)) :
    ∀ i j : Index n, i ≠ j → mat (matrixPoints m A g) i j = 0 := by
  let B : TestAlgebra k := CommAlgCat.of k (Laurent n A)
  let s : A ⟶ B := CommAlgCat.ofHom (AddMonoidAlgebra.singleZeroAlgHom (R := k))
  let t : Points T.group.X B := (unitsPoints m B).symm (universalScale n A)
  have ht : unitsPoints m B t = universalScale n A := (unitsPoints m B).apply_symm_apply _
  have hc := (h B s t).map (matrixPoints m B).toMonoidHom
  have hM := congrArg (fun x : orthogonalMatrices n B ↦ mat x) hc.eq
  change mat (matrixPoints m B (mapPoints s g)) * mat (matrixPoints m B (t ≫ T.inclusion.hom.hom)) =
    mat (matrixPoints m B (t ≫ T.inclusion.hom.hom)) * mat (matrixPoints m B (mapPoints s g)) at hM
  rw [matrixPoints_map m, matrixPoints_torus m, ht] at hM
  intro i j hij
  have hE := congrFun (congrFun hM i) j
  simp only [mul_diagonal, diagonal_mul, RingHom.mapMatrix_apply, map_apply] at hE
  rw [universalEntry, universalEntry] at hE
  let c : A := mat (matrixPoints m A g) i j
  change (AddMonoidAlgebra.single 0 c : Laurent n A) * AddMonoidAlgebra.single (weight j) 1 =
    AddMonoidAlgebra.single (weight i) 1 * AddMonoidAlgebra.single 0 c at hE
  have hW : weight j ≠ weight i := fun hh ↦ hij (weight_injective hh).symm
  have hcoeff := congrArg (fun a : Laurent n A ↦ a.coeff (weight i)) hE
  change ((AddMonoidAlgebra.single 0 c : Laurent n A) *
    AddMonoidAlgebra.single (weight j) 1).coeff (weight i) =
      (AddMonoidAlgebra.single (weight i) (1 : A) *
        AddMonoidAlgebra.single 0 c).coeff (weight i) at hcoeff
  rw [AddMonoidAlgebra.coeff_single_zero_mul, AddMonoidAlgebra.coeff_mul_single_zero,
    AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single,
    Finsupp.single_eq_of_ne hW.symm, Finsupp.single_eq_same, mul_zero, one_mul] at hcoeff
  exact hcoeff.symm

private theorem diag_det (A : Type u) [CommRing A] (d : Index n → A)
    (h : ∀ i, d (e i) * d (f i) = 1) : (diagonal d).det = d (r n) := by
  rw [det_diagonal, Fintype.prod_equiv (Equiv.ulift : Index n ≃ (Fin n ⊕ Fin n) ⊕ Unit)
    d (fun i ↦ d ⟨i⟩) (fun _ ↦ rfl), Fintype.prod_sum_type, Fintype.prod_sum_type]
  change ((∏ i : Fin n, d (e i)) * (∏ i : Fin n, d (f i))) * (∏ i : Unit, d ⟨.inr i⟩) = _
  rw [← Finset.prod_mul_distrib]
  simp [h, r]

private theorem diagonal_is_torus (A : TestAlgebra k) (g : Points O.val.X A)
    (h : ∀ i j : Index n, i ≠ j → mat (matrixPoints m A g) i j = 0) :
    ∃ t : Points T.group.X A, t ≫ T.inclusion.hom.hom = g := by
  let M := mat (matrixPoints m A g)
  let d : Index n → A := fun i ↦ M i i
  have hd : M = diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [d]
    · simp [hij, M, h _ _ hij]
  have hG : Mᵀ * gram n A * M = gram n A := (matrixPoints m A g).property
  rw [hd, diagonal_transpose] at hG
  have hp (i : Fin n) : d (e i) * d (f i) = 1 := by
    have hi := congrFun (congrFun hG (e i)) (f i)
    simpa [gram, mul_diagonal, diagonal_mul] using hi
  have hdet : M.det = 1 := (matrixPoints m A g).val.property
  rw [hd, diag_det A d hp] at hdet
  let t : Fin n → Aˣ := fun i ↦ ⟨d (e i), d (f i), hp i, (mul_comm _ _).trans (hp i)⟩
  have htd : diagonalEntry t = d := by
    funext j
    rcases index_cases j with ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl
    · rfl
    · rfl
    · exact hdet.symm
  refine ⟨(unitsPoints m A).symm t, (matrixPoints m A).injective (mat_injective ?_)⟩
  rw [matrixPoints_torus m, (unitsPoints m A).apply_symm_apply, htd]
  exact hd.symm

include m in
private theorem factors_centralizing_affine (A : TestAlgebra k) (g : Points O.val.X A)
    (h : Centralizes T.inclusion g) :
    ∃ t : Points T.group.X A, t ≫ T.inclusion.hom.hom = g := by
  apply diagonal_is_torus m A g
  apply diagonal_of_commutes m A g
  intro B s t
  exact (centralizes_iff T.inclusion g).mp h _ ((testSpec k).map s.op) t

include m in
private theorem centralizes_torus (Y : SchemeOver k) (g : Y ⟶ T.group.X) :
    Centralizes T.inclusion (g ≫ T.inclusion.hom.hom) := by
  apply (centralizes_iff _ _).mpr
  intro U x y
  have hc : Commute (x ≫ g) y := by
    apply Commute.eq
    apply hom_ext_on_affine_tests
    intro A z
    simp only [MonObj.comp_mul]
    apply (unitsPoints m A).injective
    simp only [map_mul, mul_comm]
  simpa only [IsMonHom.monoidHom_apply, Category.assoc] using hc.map (IsMonHom.monoidHom T.inclusion.hom.hom U)

include m in
/-- The given diagonal inclusion represents its scheme centralizer. -/
private theorem torusCentralizer :
    RepresentsSubgroup T (fun _ g ↦ Centralizes T.inclusion g) := by
  obtain ⟨C, hC⟩ := centralizerScheme k O T
  let C' := Specs.Unipotent.closedSubgroupAlgebraicGroup C
  obtain ⟨A, ⟨a⟩⟩ := essImage_algSpec.mpr C'.property.1
  have hCa : Centralizes T.inclusion (a.hom ≫ C.inclusion.hom.hom) :=
    (hC _ _).mpr ⟨a.hom, rfl⟩
  obtain ⟨t, ht⟩ := factors_centralizing_affine m A.unop
    (a.hom ≫ C.inclusion.hom.hom) hCa
  have ht' : (a.inv ≫ t) ≫ T.inclusion.hom.hom = C.inclusion.hom.hom := by
    simp [Category.assoc, ht]
  intro Y g
  constructor
  · intro hg
    obtain ⟨c, hc⟩ := (hC Y g).mp hg
    exact ⟨c ≫ (a.inv ≫ t), by rw [Category.assoc, ht', hc]⟩
  · rintro ⟨t, rfl⟩
    exact centralizes_torus m Y t

include m in
private theorem affine_central_eq_one (A : TestAlgebra k) (g : Points O.val.X A)
    (h : Centralizes (𝟙 O.val) g) : g = 1 := by
  have hT : Centralizes T.inclusion g := by
    apply (centralizes_iff _ _).mpr
    intro U x y
    simpa using (centralizes_iff _ _).mp h U x (y ≫ T.inclusion.hom.hom)
  obtain ⟨t, rfl⟩ := factors_centralizing_affine m A g hT
  let d := diagonalEntry (unitsPoints m A t)
  have hd (i : Fin n) : (unitsPoints m A t) i = 1 := by
    let a := (matrixPoints m A).symm (shearE (A := A) i)
    have ha := (matrixPoints m A).apply_symm_apply (shearE (A := A) i)
    have hcomm : Commute (t ≫ T.inclusion.hom.hom) a := by
      simpa using (centralizes_iff _ _).mp h _ (𝟙 _) a
    have heq := congrArg (fun x : orthogonalMatrices n A ↦ mat x (r n) (f i))
      (hcomm.map (matrixPoints m A).toMonoidHom).eq
    change (mat (matrixPoints m A (t ≫ T.inclusion.hom.hom)) *
      mat (matrixPoints m A a)) (r n) (f i) =
      (mat (matrixPoints m A a) *
      mat (matrixPoints m A (t ≫ T.inclusion.hom.hom))) (r n) (f i) at heq
    rw [matrixPoints_torus m, ha, diagonal_mul, mul_diagonal] at heq
    have hentry : mat (shearE (A := A) i) (r n) (f i) = -1 := by
      change (1 + single (e i) (r n) (2 : A) + single (r n) (f i) (-1) +
        single (e i) (f i) (-1) : Mat n A) (r n) (f i) = -1
      simp [Matrix.add_apply, one_apply]
    rw [hentry, entry_r, entry_f, one_mul, neg_one_mul] at heq
    have hi : (((unitsPoints m A t) i)⁻¹ : Aˣ) = 1 :=
      Units.ext (neg_injective (by simpa using heq.symm))
    simpa using congrArg Inv.inv hi
  have ht : t = 1 := by
    apply (unitsPoints m A).injective
    rw [map_one]
    funext i
    exact hd i
  rw [ht, MonObj.one_comp]

include m in
private theorem central_eq_one (Y : SchemeOver k) (g : Y ⟶ O.val.X)
    (h : Centralizes (𝟙 O.val) g) : g = 1 := by
  apply hom_ext_on_affine_tests
  intro A x
  rw [MonObj.comp_one]
  apply affine_central_eq_one m A
  apply (centralizes_iff _ _).mpr
  intro U p q
  simpa only [Category.assoc] using (centralizes_iff _ _).mp h U (p ≫ x) q

include m in
private theorem identity_centre :
    Specs.CentralTorus.IsSchemeCentre (identitySubgroup O) := by
  intro Y g
  constructor
  · intro h
    rw [central_eq_one m Y g h]
    exact ⟨1, MonObj.one_comp _⟩
  · rintro ⟨x, rfl⟩
    have h : x = 1 := isTerminalTensorUnit.hom_ext _ _
    rw [h, MonObj.one_comp]
    exact (centralizes_iff _ _).mpr (fun U p q ↦ by rw [MonObj.comp_one]; exact Commute.one_left _)

end Diagonal

section BaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {O : AffineAlgebraicGroup k} {T : ClosedSubgroup O.val}

private def baseChangedModel (m : MarkedModel n O T)
    (h : IsClosedImmersion ((groupBaseChange k K).map T.inclusion).hom.hom.left) :
    MarkedModel n (Specs.Unipotent.baseChangedAlgebraicGroup K O) (baseChangedSubgroup K T h) where
  orthogonal := groupBaseChangePointIso (K := K) O.val ≪≫
    ((Functor.whiskeringLeft _ _ _).obj (restrictTestAlgebra k K)).mapIso m.orthogonal
  torus := groupBaseChangePointIso (K := K) T.group ≪≫
    ((Functor.whiskeringLeft _ _ _).obj (restrictTestAlgebra k K)).mapIso m.torus
  inclusion_matrix A t := by
    change mat (matrixPoints m ((restrictTestAlgebra k K).obj A)
      (baseChangePoint k K O.val.X A (t ≫ (baseChange k K).map T.inclusion.hom.hom))) =
        diagonal (diagonalEntry (unitsPoints m ((restrictTestAlgebra k K).obj A)
          (baseChangePoint k K T.group.X A t)))
    rw [baseChangePointsSchemeNaturality]
    exact matrixPoints_torus m _ _

private def reindexTorusPoints (k : Type u) [Field k] (n : ℕ) :
    Specs.StandardGroups.multiplicativePowerPoints k (ULift.{u} (Fin n)) ≅ torusPoints k n :=
  NatIso.ofComponents (fun A ↦
    ({ toFun := fun t i ↦ t ⟨i⟩
       invFun := fun t i ↦ t i.down
       left_inv := fun t ↦ rfl
       right_inv := fun t ↦ rfl
       map_mul' := fun a b ↦ rfl } :
       (ULift.{u} (Fin n) → Aˣ) ≃* (Fin n → Aˣ)).toGrpIso) (by
    intro A B a
    apply GrpCat.ext
    intro t
    rfl)

private theorem split_of_model (m : MarkedModel n O T) : IsSplitTorus T.group := by
  let G := (Specs.StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin n))).val
  let iso := m.torus ≪≫ (reindexTorusPoints k n).symm ≪≫
    (StandardGroups.multiplicativePowerGroupPointsIso k (ULift.{u} (Fin n))).symm
  let hT := (Specs.Unipotent.closedSubgroupAlgebraicGroup T).property.1
  have hG : IsAffine G.X.left :=
    (Specs.StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin n))).property.1
  let a := groupHomEquiv T.group G hT
  let b := groupHomEquiv G T.group hG
  refine ⟨n, ⟨⟨a.symm iso.hom, b.symm iso.inv, ?_, ?_⟩⟩⟩
  · apply (groupHomComparison k T.group T.group hT).1
    change (groupPointsFunctor k).map (_ ≫ _) = (groupPointsFunctor k).map (𝟙 T.group)
    rw [Functor.map_comp, (groupPointsFunctor k).map_id]
    change a (a.symm iso.hom) ≫ b (b.symm iso.inv) = _
    simp
  · apply (groupHomComparison k G G hG).1
    change (groupPointsFunctor k).map (_ ≫ _) = (groupPointsFunctor k).map (𝟙 G)
    rw [Functor.map_comp, (groupPointsFunctor k).map_id]
    change b (b.symm iso.inv) ≫ a (a.symm iso.hom) = _
    simp

open scoped IsMulCommutative in
private theorem maximal_of_self_centralizing {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} (hT : IsSplitTorus T.group)
    (hc : RepresentsSubgroup T (fun _ g ↦ Centralizes T.inclusion g)) :
    IsMaximalTorus T := by
  refine ⟨(isTorus_iff_coordinates (Specs.Unipotent.closedSubgroupAlgebraicGroup T)).mpr
    (torus_of_split hT), ?_⟩
  intro S hS hTS
  obtain ⟨i, hi⟩ := hTS
  have hComm := torus_commutative (Specs.Unipotent.closedSubgroupAlgebraicGroup S) hS
  have hci : Centralizes T.inclusion S.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro U a b
    let : IsMulCommutative (U ⟶ S.group.X) :=
      (isCommMonObj_iff_isMulCommutative S.group.X).mp hComm U
    have hc : Commute a (b ≫ i.hom.hom) := mul_comm a _
    have h := hc.map (IsMonHom.monoidHom S.inclusion.hom.hom U)
    have hi' : i.hom.hom ≫ S.inclusion.hom.hom = T.inclusion.hom.hom :=
      congrArg (fun a : T.group ⟶ G.val ↦ a.hom.hom) hi
    change Commute (a ≫ S.inclusion.hom.hom) ((b ≫ i.hom.hom) ≫ S.inclusion.hom.hom) at h
    rwa [Category.assoc, hi'] at h
  obtain ⟨f, hf⟩ := (hc _ _).mp hci
  exact factor_group_through_subgroup T S.inclusion f hf

end BaseChange

section Irreducibility

variable {L : Type u} [Field L]

private abbrev Vector (n : ℕ) (L : Type u) := Index.{u} n → L
private def basisVector (L : Type u) [Field L] (j : Index n) : Vector n L := Pi.single j 1

private def coordinateScale (i : Fin n) (a : Lˣ) : Index.{u} n → L :=
  diagonalEntry (Pi.mulSingle i a)

private theorem coordinateScale_apply (i : Fin n) (a : Lˣ) (j : Index n) :
    coordinateScale i a j = if j = e i then (a : L) else if j = f i then ↑a⁻¹ else 1 := by
  rcases index_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ | rfl
  · by_cases h : j = i <;> simp [coordinateScale, h, Pi.mulSingle_eq_of_ne]
  · by_cases h : j = i <;> simp [coordinateScale, h, Pi.mulSingle_eq_of_ne]
  · simp [coordinateScale]

private theorem line_of_coordinate (W : Submodule L (Vector n L))
    (hD : ∀ (i : Fin n) (a : Lˣ) (v : Vector n L), v ∈ W →
      (diagonal (coordinateScale i a)).mulVec v ∈ W)
    (i : Fin n) (a : Lˣ) {j l : Index n}
    (hj : j = e i ∧ l = f i ∨ j = f i ∧ l = e i)
    (hs : coordinateScale i a j ≠ 1)
    (hd : coordinateScale i a j ≠ coordinateScale i a l)
    (v : Vector n L) (hv : v ∈ W) (hval : v j ≠ 0) :
    basisVector L j ∈ W := by
  let D := diagonal (coordinateScale i a)
  let w := D.mulVec v - v
  let z := D.mulVec w - coordinateScale i a l • w
  have hw : w ∈ W := W.sub_mem (hD i a v hv) hv
  have hz : z ∈ W := W.sub_mem (hD i a w hw) (W.smul_mem _ hw)
  let c := (coordinateScale i a j - coordinateScale i a l) *
    (coordinateScale i a j - 1) * v j
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hd) (sub_ne_zero.mpr hs)) hval
  have hzc : z = c • basisVector L j := by
    funext x
    change (D.mulVec (D.mulVec v - v) - coordinateScale i a l • (D.mulVec v - v)) x = _
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, D, mulVec_diagonal]
    by_cases hx : x = j
    · subst x
      simp [c, basisVector]
      ring
    · by_cases hx' : x = l
      · subst x
        simp [basisVector, Pi.single_eq_of_ne hx]
      · have he : x ≠ e i := by rcases hj with ⟨hj, hl⟩ | ⟨hj, hl⟩ <;> aesop
        have hf : x ≠ f i := by rcases hj with ⟨hj, hl⟩ | ⟨hj, hl⟩ <;> aesop
        simp [basisVector, Pi.single_eq_of_ne hx, coordinateScale_apply i a x, he, hf]
  rw [hzc] at hz
  simpa [smul_smul, hc] using W.smul_mem c⁻¹ hz

private theorem shear_on_line {a b : Index n} (ha : partner a = b) (hb : partner b = a)
    (har : a ≠ r n) (hbr : b ≠ r n) (hab : a ≠ b) :
    (mat (shear (A := L) a b ha hb har hbr hab)).mulVec (basisVector L (r n)) =
      basisVector L (r n) + (2 : L) • basisVector L a := by
  change (1 + single a (r n) (2 : L) + single (r n) b (-1) + single a b (-1)).mulVec
    (Pi.single (r n) 1) = _
  rw [add_mulVec, add_mulVec, add_mulVec, one_mulVec, single_mulVec_eq, single_mulVec_eq,
    single_mulVec_eq]
  simp [Pi.single_eq_of_ne hbr, basisVector, ← Pi.single_smul]

private theorem shear_on_partner {a b : Index n} (ha : partner a = b) (hb : partner b = a)
    (har : a ≠ r n) (hbr : b ≠ r n) (hab : a ≠ b) :
    (mat (shear (A := L) a b ha hb har hbr hab)).mulVec (basisVector L b) =
      basisVector L b - basisVector L (r n) - basisVector L a := by
  change (1 + single a (r n) (2 : L) + single (r n) b (-1) + single a b (-1)).mulVec
    (Pi.single b 1) = _
  rw [add_mulVec, add_mulVec, add_mulVec, one_mulVec, single_mulVec_eq, single_mulVec_eq,
    single_mulVec_eq]
  simp [Pi.single_eq_of_ne (Ne.symm hbr), basisVector, sub_eq_add_neg]

private theorem invariant_submodule_eq_top [Infinite L] (h₂ : (2 : L) ≠ 0)
    (W : Submodule L (Vector n L))
    (hM : ∀ (g : orthogonalMatrices n L) (v : Vector n L), v ∈ W → (mat g).mulVec v ∈ W)
    (hD : ∀ (i : Fin n) (a : Lˣ) (v : Vector n L), v ∈ W →
      (diagonal (coordinateScale i a)).mulVec v ∈ W)
    (v : Vector n L) (hv : v ∈ W) (hv0 : v ≠ 0) : W = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
  have hs0 : s ≠ 0 := fun h ↦ hs (by simp [h])
  have hs1 : s ≠ 1 := fun h ↦ hs (by simp [h])
  have hsn : s ≠ -1 := fun h ↦ hs (by simp [h])
  let a := Units.mk0 s hs0
  have ha : (a : L) ≠ (↑a⁻¹ : L) := by
    change s ≠ s⁻¹
    intro h
    have hp : s * s = 1 := by rw [← mul_inv_cancel₀ hs0, ← h]
    have hz : (s - 1) * (s + 1) = 0 := by linear_combination hp
    exact (mul_ne_zero (sub_ne_zero.mpr hs1) (fun h ↦ hsn (eq_neg_of_add_eq_zero_left h))) hz
  have ha' : (↑a⁻¹ : L) ≠ 1 := by
    change s⁻¹ ≠ 1
    simpa using hs1
  have e_mem (i : Fin n) (w : Vector n L) (hw : w ∈ W) (h : w (e i) ≠ 0) :
      basisVector L (e i) ∈ W :=
    line_of_coordinate W hD i a (Or.inl ⟨rfl, rfl⟩)
      (by simpa [coordinateScale_apply, a] using hs1)
      (by simpa [coordinateScale_apply] using ha) w hw h
  have f_mem (i : Fin n) (w : Vector n L) (hw : w ∈ W) (h : w (f i) ≠ 0) :
      basisVector L (f i) ∈ W :=
    line_of_coordinate W hD i a (Or.inr ⟨rfl, rfl⟩)
      (by simpa [coordinateScale_apply] using ha')
      (by simpa [coordinateScale_apply] using Ne.symm ha) w hw h
  have r_mem : basisVector L (r n) ∈ W := by
    have from_pair (i : Fin n) (he : basisVector L (e i) ∈ W)
        (hf : basisVector L (f i) ∈ W) : basisVector L (r n) ∈ W := by
      have h := hM (shearE i) (basisVector L (f i)) hf
      rw [shear_on_partner] at h
      convert W.sub_mem hf (W.add_mem h he) using 1
      abel
    by_cases h : ∃ i, v (e i) ≠ 0 ∨ v (f i) ≠ 0
    · obtain ⟨i, he | hf⟩ := h
      · have we := e_mem i v hv he
        let w := (mat (shearF (A := L) i)).mulVec (basisVector L (e i))
        have hw := hM (shearF i) _ we
        apply from_pair i we (f_mem i w hw ?_)
        dsimp only [w]
        rw [shear_on_partner]
        simp [basisVector, Pi.single_eq_of_ne]
      · have wf := f_mem i v hv hf
        let w := (mat (shearE (A := L) i)).mulVec (basisVector L (f i))
        have hw := hM (shearE i) _ wf
        apply from_pair i (e_mem i w hw ?_) wf
        dsimp only [w]
        rw [shear_on_partner]
        simp [basisVector, Pi.single_eq_of_ne]
    · have hzero (i : Fin n) : v (e i) = 0 ∧ v (f i) = 0 :=
        ⟨not_not.mp (fun he ↦ h ⟨i, Or.inl he⟩), not_not.mp (fun hf ↦ h ⟨i, Or.inr hf⟩)⟩
      have heq : v = v (r n) • basisVector L (r n) := by
        funext j
        rcases index_cases j with ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl <;>
          simp [basisVector, Pi.single_eq_of_ne, hzero]
      have hn : v (r n) ≠ 0 := fun hn ↦ hv0 (by nth_rw 1 [heq]; simp [hn])
      rw [heq] at hv
      simpa [smul_smul, hn] using W.smul_mem (v (r n))⁻¹ hv
  have other_mem {a b : Index n} (ha : partner a = b) (hb : partner b = a)
      (har : a ≠ r n) (hbr : b ≠ r n) (hab : a ≠ b) : basisVector L a ∈ W := by
    have h := hM (shear a b ha hb har hbr hab) _ r_mem
    rw [shear_on_line] at h
    have h' := W.sub_mem h r_mem
    rw [add_sub_cancel_left] at h'
    simpa [smul_smul, h₂] using W.smul_mem (2 : L)⁻¹ h'
  apply top_unique
  intro w _
  rw [← (Pi.basisFun L (Index n)).sum_repr w]
  apply Submodule.sum_mem W
  intro j _
  apply W.smul_mem
  rw [Pi.basisFun_apply]
  change basisVector L j ∈ W
  rcases index_cases j with ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl
  · exact other_mem rfl rfl (e_ne_r i) (f_ne_r i) (e_ne_f i i)
  · exact other_mem rfl rfl (f_ne_r i) (e_ne_r i) (f_ne_e i i)
  · exact r_mem

end Irreducibility

section Radical

open RationalRepresentations (coefficients evaluate coactionOfMatrix coaction_apply_basis coefficients_coactionOfMatrix
  invariantKernel)
open Specs.Unipotent (IsUnipotent closedSubgroupAlgebraicGroup)

variable {L : Type u} [Field L] {O : AffineAlgebraicGroup L}
  {T : ClosedSubgroup O.val} (m : MarkedModel n O T)

private def matrixRepresentation :
    (groupPointsFunctor L).obj O.val ⟶ Specs.StandardGroups.generalLinearPoints L (Index n) where
  app A := GrpCat.ofHom (SpecialLinearGroup.toGL.comp
    ((orthogonalMatrices n A).subtype.comp (matrixPoints m A).toMonoidHom))
  naturality := by
    intro A B s
    apply GrpCat.ext
    intro x
    apply Units.ext
    exact matrixPoints_map m s x

private def fixedSpace (N : ClosedSubgroup O.val) : Submodule L (Vector n L) :=
  ⨅ p : Points N.group.X (CommAlgCat.of L L),
    LinearMap.ker ((mat (matrixPoints m (CommAlgCat.of L L)
      (p ≫ N.inclusion.hom.hom))).mulVecLin - LinearMap.id)

private theorem mem_fixedSpace (N : ClosedSubgroup O.val) (v : Vector n L) :
    v ∈ fixedSpace m N ↔ ∀ p : Points N.group.X (CommAlgCat.of L L),
      (mat (matrixPoints m (CommAlgCat.of L L) (p ≫ N.inclusion.hom.hom))).mulVec v = v := by
  simp [fixedSpace, sub_eq_zero]

private theorem fixedSpace_invariant (N : ClosedSubgroup O.val) (hN : IsNormalSubgroup N.inclusion)
    (g : orthogonalMatrices n L) (v : Vector n L) (hv : v ∈ fixedSpace m N) :
    (mat g).mulVec v ∈ fixedSpace m N := by
  let A := CommAlgCat.of L L
  let p := (matrixPoints m A).symm g
  have hp : matrixPoints m A p = g := (matrixPoints m A).apply_symm_apply g
  apply (mem_fixedSpace m N _).mpr
  intro x
  obtain ⟨y, hy⟩ := normalSubgroup_conjugate_sections hN p⁻¹ x
  rw [inv_inv] at hy
  have h := congrArg (matrixPoints m A) hy
  rw [map_mul, map_mul, map_inv, hp] at h
  have hc : matrixPoints m A (x ≫ N.inclusion.hom.hom) * g =
      g * matrixPoints m A (y ≫ N.inclusion.hom.hom) := by
    rw [h]
    group
  have hv' := (mem_fixedSpace m N _).mp hv y
  rw [mulVec_mulVec]
  change (mat (matrixPoints m A (x ≫ N.inclusion.hom.hom) * g)).mulVec v = _
  rw [hc]
  change (mat g * mat (matrixPoints m A (y ≫ N.inclusion.hom.hom))).mulVec v = _
  rw [← mulVec_mulVec, hv']

private theorem nonzero_fixedSpace (N : ClosedSubgroup O.val)
    (hN : IsUnipotent (closedSubgroupAlgebraicGroup N)) :
    ∃ v : Vector n L, v ≠ 0 ∧ v ∈ fixedSpace m N := by
  obtain ⟨H, ⟨j⟩, h⟩ := hN
  let eN := hopfSpecPointIso H ≪≫ (groupPointsFunctor L).mapIso j
  let α := eN.hom ≫ (groupPointsFunctor L).map N.inclusion ≫ matrixRepresentation m
  let b := Pi.basisFun L (Index n)
  let U := pointMatrix H α
  let ρ := coactionOfMatrix H b U (pointMatrix_isCoactionMatrix H α)
  have hρ : coefficients H b ρ = U := coefficients_coactionOfMatrix H b _ _
  have : Nonempty (Index n) := ⟨r n⟩
  obtain ⟨v, hv0, hv⟩ := h (Vector n L) ρ
  refine ⟨v, hv0, (mem_fixedSpace m N v).2 ?_⟩
  intro p
  let A := CommAlgCat.of L L
  let a : WithConv (H →ₐ[L] A) := eN.inv.app A p
  have ha : eN.hom.app A a = p := (eN.app A).groupIsoToMulEquiv.apply_symm_apply p
  have hEval := (invariantKernel H ρ v).2 hv A a.ofConv
  have hMat := pointMatrix_evaluation H α A a
  have hMat' : (mat (matrixPoints m A (p ≫ N.inclusion.hom.hom))) = a.ofConv.mapMatrix U := by
    change mat (matrixPoints m A (eN.hom.app A a ≫ N.inclusion.hom.hom)) =
      a.ofConv.mapMatrix U at hMat
    rwa [ha] at hMat
  let φ := TensorProduct.rid L (Vector n L)
  have hAction :
      φ.toLinearMap.comp (evaluate H ρ a.ofConv) =
        (mat (matrixPoints m A (p ≫ N.inclusion.hom.hom))).mulVecLin := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply, RationalRepresentations.evaluate]
    rw [coaction_apply_basis H b ρ, hρ, hMat']
    simp only [map_sum, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply]
    change (∑ l, φ (b l ⊗ₜ[L] (a.ofConv (U l j) : L))) = (a.ofConv.mapMatrix U).mulVec (b j)
    have hφ (x : Vector n L) (c : L) : φ (x ⊗ₜ[L] c) = c • x := TensorProduct.rid_tmul _ _
    simp only [hφ, b, Pi.basisFun_apply, mulVec_single_one]
    funext i
    simp [Pi.single_apply]
  have hcong := congrArg φ hEval
  change (φ.toLinearMap.comp (evaluate H ρ a.ofConv)) v = φ (v ⊗ₜ[L] (1 : L)) at hcong
  rw [hAction] at hcong
  have hrid : φ (v ⊗ₜ[L] (1 : L)) = v := (TensorProduct.rid_tmul v 1).trans (one_smul _ _)
  rw [hrid] at hcong
  exact hcong

include m in
private theorem trivial_radical [IsAlgClosed L] (h₂ : (2 : L) ≠ 0)
    (N : ClosedSubgroup O.val) (hN : IsUnipotentRadical O N) : IsTrivialSubgroup N := by
  let A := CommAlgCat.of L L
  obtain ⟨v, hv0, hv⟩ := nonzero_fixedSpace m N hN.2.1
  have hM := fixedSpace_invariant m N hN.1.2.2
  have hD (i : Fin n) (a : Lˣ) (w : Vector n L) (hw : w ∈ fixedSpace m N) :
      (diagonal (coordinateScale i a)).mulVec w ∈ fixedSpace m N := by
    let t := (unitsPoints m A).symm (Pi.mulSingle i a)
    have ht := (unitsPoints m A).apply_symm_apply (Pi.mulSingle i a)
    have h := hM (matrixPoints m A (t ≫ T.inclusion.hom.hom)) w hw
    rw [matrixPoints_torus m, ht] at h
    exact h
  have hW := invariant_submodule_eq_top h₂ _ hM hD v hv hv0
  have hpoints (p : Points N.group.X A) : p = 1 := by
    have hp : mat (matrixPoints m A (p ≫ N.inclusion.hom.hom)) = 1 := by
      ext i j
      have hvj : basisVector L j ∈ fixedSpace m N := by rw [hW]; trivial
      have he : (mat (matrixPoints m A (p ≫ N.inclusion.hom.hom))).mulVec (Pi.single j 1) =
          (1 : Mat n L).mulVec (Pi.single j 1) :=
        ((mem_fixedSpace m N _).mp hvj p).trans (one_mulVec _).symm
      rw [mulVec_single_one, mulVec_single_one] at he
      exact congrFun he i
    let := mono_over N.inclusion.hom.hom N.isClosedImmersion
    apply (cancel_mono N.inclusion.hom.hom).mp
    rw [MonObj.one_comp]
    apply (matrixPoints m A).injective
    rw [map_one]
    exact mat_injective hp
  let a : (testSpec L).obj (op A) ≅ 𝟙_ (SchemeOver L) :=
    (affineBaseTerminal L).uniqueUpToIso isTerminalTensorUnit
  let C := closedSubgroupAlgebraicGroup N
  let : Subsingleton (𝟙_ (SchemeOver L) ⟶ C.val.X) :=
    ⟨fun x y ↦ (cancel_epi a.hom).mp ((hpoints (a.hom ≫ x)).trans (hpoints (a.hom ≫ y)).symm)⟩
  exact trivial_of_subsingleton_sections C hN.1.1

end Radical

/-- The split odd special orthogonal model has trivial scheme centre and a
self-centralizing geometrically maximal diagonal torus. -/
theorem geometry : Geometry.{u} := by
  intro k _ n _ h₂ O T _ m hs hc
  have hZ := identity_centre m
  have hT := torusCentralizer m
  have hExt (K : Type u) [Field K] [Algebra k K] :
      ∃ h : IsClosedImmersion ((groupBaseChange k K).map T.inclusion).hom.hom.left,
        RepresentsSubgroup (baseChangedSubgroup K T h)
          (fun _ g ↦ Centralizes ((groupBaseChange k K).map T.inclusion) g) :=
    centralizerSchemeBaseChange k K T.inclusion T hT
  obtain ⟨hi, hTi⟩ := hExt (AlgebraicClosure k)
  let mK := baseChangedModel (K := AlgebraicClosure k) m hi
  have h₂K : (2 : AlgebraicClosure k) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap k (AlgebraicClosure k))).mpr h₂
  have hRed : IsReductive O :=
    ⟨hs, hc, trivial_radical mK h₂K _ (GeometricRadicals.geometricUnipotentRadicalLargest O)⟩
  have hFinite : IsFinite (identitySubgroup O).group.X.hom := by
    change IsFinite (𝟙 (Spec (CommRingCat.of k)))
    infer_instance
  exact ⟨(Reductive.CentralDerived.semisimpleIffFiniteCentre O hRed _ hZ).2 hFinite,
    hZ, central_eq_one m, hT, hExt, hi,
    maximal_of_self_centralizing (split_of_model mK) hTi⟩

end
end LinearAlgebraicGroups.OddSpinOrthogonalGeometry
