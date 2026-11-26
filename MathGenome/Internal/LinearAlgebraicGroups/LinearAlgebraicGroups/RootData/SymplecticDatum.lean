import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SymplecticDatum
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SymplecticDatumTorusAndBorel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SymplecticDatumRankOneAndPinning
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SymplecticDatumAdjointDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.FinCases

open AlgebraicGeometry CategoryTheory Matrix
open scoped CategoryTheory.MonObj Matrix BigOperators

universe u

namespace LinearAlgebraicGroups.RootData.SymplecticDatum

open _root_.LinearAlgebraicGroups.Specs
open Specs.SymplecticDatum
open Specs.SymplecticDatumTorusAndBorel
  (RootLabel coordinate sign rootVector simpleLabel HyperbolicIndex signedIndex elementaryDirection)
open Specs.SymplecticMatrixStructure
open LinearAlgebraicGroups.SymplecticMatrixStructure
  (diagonalCentralizer hyperbolicDiagonal_mem upperShear)

noncomputable section

variable {I R : Type u} [Fintype I] [DecidableEq I] [CommRing R]

theorem adjointIdentities : AdjointIdentities.{u} :=
  SymplecticDatumAdjointDescent.adjointIdentities

open private adjoint_scalar isometry_iff scalar_point conjugationHom conjugation_kernel
  conjugateMatrix_adjoint conjugateMatrix_map
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SymplecticDatumAdjointDescent

theorem isometryGroupPoints : IsometryGroupPoints.{u} := by
  intro I _ _
  let e (R : Type u) [CommRing R] : PointGroup I R →* (MatrixAlgebra I R)ˣ :=
    (Matrix.symplecticGroup I R).subtype.toHomUnits
  refine ⟨e, fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro R _ g h eq
    exact Subtype.ext (congrArg Units.val eq)
  · intro R _ g
    constructor
    · intro hg
      exact ⟨⟨g.val, (isometry_iff _).mpr hg⟩, Units.ext rfl⟩
    · rintro ⟨h, eq⟩
      have heq : h.val = g.val := congrArg Units.val eq
      rw [← heq]
      exact (isometry_iff _).mp h.property
  · intro R S _ _ f g
    exact Units.ext rfl

theorem conjugationAction : ConjugationAction.{u} := by
  intro I R _ _ _
  exact ⟨conjugationHom, fun _ _ => rfl, conjugateMatrix_adjoint,
    fun _ _ => conjugateMatrix_map, fun _ _ => rfl, conjugation_kernel⟩

private lemma diagonal_entry_relation (t : I → Rˣ) (i j : I) (B : Matrix I I R)
    (hs : B.IsSymm) (hB : B i j = 1)
    (hc : Commute (hyperbolicDiagonal t) (upperShear B hs).val) :
    (t i : R) = ((t j)⁻¹ : Rˣ).val := by
  have h := congrArg (fun M : MatrixAlgebra I R => M (Sum.inl i) (Sum.inr j)) hc.eq
  change (Matrix.diagonal _ * _ : MatrixAlgebra I R) (Sum.inl i) (Sum.inr j) =
    (_ * Matrix.diagonal _ : MatrixAlgebra I R) (Sum.inl i) (Sum.inr j) at h
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Sum.elim_inl, Sum.elim_inr] at h
  change (t i : R) * B i j = B i j * ((t j)⁻¹ : Rˣ).val at h
  simpa [hB] using h

private lemma symmetric_single_diag (i : I) :
    (Matrix.single i i (1 : R)).IsSymm := by
  rw [Matrix.IsSymm, Matrix.transpose_single]

private lemma symmetric_single_pair (i j : I) :
    (Matrix.single i j (1 : R) + Matrix.single j i 1).IsSymm := by
  rw [Matrix.IsSymm, Matrix.transpose_add, Matrix.transpose_single, Matrix.transpose_single,
    add_comm]

theorem scalarCentreOnPoints : ScalarCentreOnPoints.{u} := by
  intro I R _ _ _ _ g
  constructor
  · intro h
    obtain ⟨t, ht⟩ := (diagonalCentralizer I R g).mp <| by
      intro S _ f t
      exact congrArg Subtype.val (h S f ⟨_, hyperbolicDiagonal_mem t⟩).eq
    have hcomm (B : Matrix I I R) (hB : B.IsSymm) :
        Commute (hyperbolicDiagonal t) (upperShear B hB).val := by
      rw [← ht]
      exact congrArg Subtype.val (h R (RingHom.id R) (upperShear B hB)).eq
    have his (i : I) : (t i : R) = ((t i)⁻¹ : Rˣ).val :=
      diagonal_entry_relation t i i _ (symmetric_single_diag i) (by simp)
        (hcomm _ (symmetric_single_diag i))
    let i₀ := Classical.choice (inferInstance : Nonempty I)
    have hall (i : I) : (t i : R) = (t i₀ : R) := by
      by_cases hi : i = i₀
      · rw [hi]
      · rw [his i₀]
        exact diagonal_entry_relation t i i₀ _ (symmetric_single_pair i i₀)
          (by simp [Matrix.single_apply, hi, Ne.symm hi])
          (hcomm _ (symmetric_single_pair i i₀))
    have hm : g.val = Matrix.scalar (Indices I) (t i₀ : R) := by
      rw [ht, hyperbolicDiagonal, Matrix.scalar_apply]
      congr 1
      funext j
      cases j with
      | inl j => exact hall j
      | inr j => exact (his j).symm.trans (hall j)
    exact ⟨_, scalar_point g hm, hm⟩
  · rintro ⟨a, -, ha⟩ S _ f h
    apply Subtype.ext
    change (g.val.map f) * h.val = h.val * (g.val.map f)
    rw [ha, Matrix.scalar_apply, Matrix.diagonal_map (map_zero f), ← Matrix.scalar_apply]
    exact Algebra.commutes (R := S) (f a) h.val

private def hyperbolicPlaneIndex : Indices (ULift.{u} Unit) ≃ Fin 2 :=
  Equiv.ofBijective (Sum.elim (fun _ => 0) (fun _ => 1)) (by
    constructor
    · rintro (⟨⟨⟨⟩⟩⟩ | ⟨⟨⟨⟩⟩⟩) (⟨⟨⟨⟩⟩⟩ | ⟨⟨⟨⟩⟩⟩) h
      all_goals first | rfl | contradiction
    · intro j
      fin_cases j
      · exact ⟨Sum.inl ⟨()⟩, rfl⟩
      · exact ⟨Sum.inr ⟨()⟩, rfl⟩)

private lemma reindex_hyperbolicPlane_J (R : Type u) [CommRing R] :
    Matrix.reindex hyperbolicPlaneIndex hyperbolicPlaneIndex (Matrix.J (ULift.{u} Unit) R) =
      !![0, -1; 1, 0] := by
  have h0 : hyperbolicPlaneIndex.{u}.symm 0 = Sum.inl ⟨()⟩ :=
    hyperbolicPlaneIndex.symm_apply_eq.mpr rfl
  have h1 : hyperbolicPlaneIndex.{u}.symm 1 = Sum.inr ⟨()⟩ :=
    hyperbolicPlaneIndex.symm_apply_eq.mpr rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, h0, h1, Matrix.J]

private lemma plane_equation (X : Matrix (Fin 2) (Fin 2) R) :
    Xᵀ * !![0, -1; 1, 0] * X = X.det • (!![0, -1; 1, 0] : Matrix _ _ R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

private lemma plane_mem_iff (R : Type u) [CommRing R]
    (g : MatrixAlgebra (ULift.{u} Unit) R) :
    g ∈ Matrix.symplecticGroup (ULift.{u} Unit) R ↔
      (Matrix.reindex hyperbolicPlaneIndex hyperbolicPlaneIndex g).det = 1 := by
  let e := Matrix.reindexAlgEquiv R R hyperbolicPlaneIndex
  rw [SymplecticGroup.mem_iff', ← e.injective.eq_iff]
  change e (gᵀ * Matrix.J (ULift.{u} Unit) R * g) = e (Matrix.J (ULift.{u} Unit) R) ↔ (e g).det = 1
  have ht : e gᵀ = (e g)ᵀ := rfl
  have hJ : e (Matrix.J (ULift.{u} Unit) R) = !![0, -1; 1, 0] := reindex_hyperbolicPlane_J R
  rw [map_mul, map_mul, ht, hJ, plane_equation]
  constructor
  · intro h
    simpa using congrArg (fun X : Matrix (Fin 2) (Fin 2) R => X 1 0) h
  · intro h
    rw [h, one_smul]

open private schemeIsoOfPointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SymplecticDatumTorusAndBorel

set_option backward.isDefEq.respectTransparency false in
theorem rankOneIdentification : RankOneIdentification.{u} := by
  refine ⟨hyperbolicPlaneIndex, rfl, rfl, plane_mem_iff, ?_⟩
  intro k _
  let f (R : TestAlgebra k) : PointGroup (ULift.{u} Unit) R ≃*
      Matrix.SpecialLinearGroup (Fin 2) R :=
    let e := Matrix.reindexAlgEquiv R R hyperbolicPlaneIndex
    { toFun := fun g => ⟨e g.val, (plane_mem_iff R g.val).mp g.property⟩
      invFun := fun g => ⟨e.symm g.val, (plane_mem_iff R _).mpr (by
        change (e (e.symm g.val)).det = 1
        rw [e.apply_symm_apply]
        exact g.property)⟩
      left_inv := fun g => Subtype.ext (e.symm_apply_apply g.val)
      right_inv := fun g => Subtype.ext (e.apply_symm_apply g.val)
      map_mul' := fun g h => Subtype.ext (e.map_mul g.val h.val) }
  let t : symplecticPoints k (ULift.{u} Unit) ≅
      Specs.SymplecticDatumRankOneAndPinning.determinantOnePoints k :=
    NatIso.ofComponents (fun R => (f R).toGrpIso) (by
      intro R S a
      apply GrpCat.ext
      intro g
      apply Subtype.ext
      rfl)
  refine ⟨t, fun _ _ => rfl, ?_⟩
  intro G S c s
  let p := c ≪≫ t ≪≫ s.symm
  let f := schemeIsoOfPointIso G.property.1 S.property.1 p
  refine ⟨f, ?_⟩
  have hf : (groupPointsFunctor k).map f.hom = p.hom :=
    (groupHomEquiv G.val S.val G.property.1).apply_symm_apply _
  rw [hf]
  simp [p]


private def successiveDifference (n : ℕ) :
    (Fin (n + 1) → ℤ) →ₗ[ℤ] (Fin (n + 1) → ℤ) where
  toFun x := Fin.cases (x 0) (fun i => x i.succ - x i.castSucc)
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [Pi.add_apply]; ring
  map_smul' c x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [Pi.smul_apply, mul_sub]

private lemma successiveDifference_bijective (n : ℕ) :
    Function.Bijective (successiveDifference n) := by
  constructor
  · intro x y h
    funext i
    induction i using Fin.induction with
    | zero =>
      exact congrFun h 0
    | succ i ih =>
      have he := congrFun h i.succ
      change x i.succ - x i.castSucc = y i.succ - y i.castSucc at he
      omega
  · intro y
    let x : Fin (n + 1) → ℤ :=
      Fin.induction (motive := fun _ => ℤ) (y 0) (fun i v => y i.succ + v)
    refine ⟨x, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change x j.succ - x j.castSucc = y j.succ
      simp [x]

theorem simpleCorootBasis : SimpleCorootBasis := by
  intro n
  let e := LinearEquiv.ofBijective (successiveDifference n) (successiveDifference_bijective n)
  refine ⟨(Pi.basisFun ℤ (Fin (n + 1))).map e, ?_⟩
  intro i
  rw [Module.Basis.map_apply, Pi.basisFun_apply]
  change successiveDifference n (coordinate i) = simpleCoroot i
  funext j
  by_cases hi : i.val < n
  · let i' : Fin (n + 1) := ⟨i.val + 1, by omega⟩
    have h0 : i' ≠ 0 := by intro h; have := congrArg Fin.val h; simp [i'] at this
    rw [simpleCoroot, dite_eq_left hi]
    change successiveDifference n (coordinate i) j = coordinate i j - coordinate i' j
    refine Fin.cases ?_ (fun k => ?_) j
    · change coordinate i 0 = coordinate i 0 - coordinate i' 0
      simp [coordinate, Pi.single_eq_of_ne (Ne.symm h0)]
    · change coordinate i k.succ - coordinate i k.castSucc =
        coordinate i k.succ - coordinate i' k.succ
      have he : k.castSucc = i ↔ k.succ = i' := by
        simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
        change k.val = i.val ↔ k.val + 1 = i.val + 1
        omega
      simp [coordinate, Pi.single_apply, he]
  · rw [simpleCoroot, dite_eq_right hi, sub_zero]
    refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · change coordinate i k.succ - coordinate i k.castSucc = coordinate i k.succ
      have he : k.castSucc ≠ i := by
        intro h
        have hh : k.val = i.val := congrArg Fin.val h
        omega
      simp [coordinate, Pi.single_eq_of_ne he]

section SchemeCentre

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory Opposite
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
open private centralizes_iff comp_conjugateFamily from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

variable {k : Type u} [Field k] [Nonempty I]

private lemma points_naturality (G : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I)
    {A B : TestAlgebra k} (f : A ⟶ B) (x : Points G.val.X A) :
    c.hom.app B (mapPoints f x) =
      mapSymplecticPoint f.hom.toRingHom (c.hom.app A x) :=
  DFunLike.congr_fun (congrArg GrpCat.Hom.hom (c.hom.naturality f)) x

private lemma centralizes_iff_scalar (G : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I)
    (A : TestAlgebra k) (x : Points G.val.X A) :
    Centralizes (𝟙 G.val) x ↔ IsScalarMuTwo (show PointGroup I A from c.hom.app A x).val := by
  constructor
  · intro hx
    apply (scalarCentreOnPoints I A (c.hom.app A x)).mp
    intro S _ f y
    letI : Algebra k S := (f.comp (algebraMap k A)).toAlgebra
    let B := CommAlgCat.of k S
    let a : A ⟶ B := CommAlgCat.ofHom { toRingHom := f, commutes' := fun _ => rfl }
    let b : Points G.val.X B := c.inv.app B y
    have h := (centralizes_iff (𝟙 G.val) x).mp hx _ ((testSpec k).map a.op) b
    have h' : Commute (mapPoints a x) b := by simpa using h
    have h'' := h'.map (c.hom.app B).hom
    change Commute (c.hom.app B (mapPoints a x)) (c.hom.app B b) at h''
    rw [points_naturality G c a x] at h''
    have hb : c.hom.app B b = y := by
      change (c.app B).hom ((c.app B).inv y) = y
      exact GrpCat.hom_inv_apply (c.app B) y
    rw [hb] at h''
    exact h''
  · intro hx
    have hc := (scalarCentreOnPoints I A (c.hom.app A x)).mpr hx
    change conjugateFamily (𝟙 G.val) x = _
    apply hom_ext_of_points (by
      letI : IsAffine G.val.X.left := G.property.1
      letI : IsAffine ((testSpec k).obj (op A)).left := by
        change IsAffine (Spec (CommRingCat.of A))
        infer_instance
      change IsAffine (Limits.pullback G.val.X.hom ((testSpec k).obj (op A)).hom)
      infer_instance)
    intro B p
    let t := p ≫ snd G.val.X ((testSpec k).obj (op A))
    let y : Points G.val.X B := p ≫ fst G.val.X ((testSpec k).obj (op A))
    let a := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage t).unop
    have ht : (testSpec k).map a.op = t := by simp [a]
    have h := hc B a.hom.toRingHom (c.hom.app B y)
    rw [← points_naturality G c a x] at h
    let C := ((groupPointsFunctor k).obj G.val).obj B
    let x' : C := mapPoints a x
    let y' : C := y
    let e := (c.app B).groupIsoToMulEquiv
    have hm : x' * y' = y' * x' := e.injective <| calc
      e (x' * y') = e x' * e y' := e.map_mul _ _
      _ = e y' * e x' := h.eq
      _ = e (y' * x') := (e.map_mul _ _).symm
    have hh : Commute (mapPoints a x) y := hm
    rw [comp_conjugateFamily]
    change (t ≫ x) * y * (t ≫ x)⁻¹ = y
    exact mul_inv_eq_iff_eq_mul.mpr (by simpa only [mapPoints, ht] using hh.eq)

theorem scalarSchemeCentre : ScalarSchemeCentre.{u} := by
  intro k I _ _ _ _ G c
  let H : ClosedSubgroup G.val := ⟨G.val, 𝟙 G.val, by
    change IsClosedImmersion (𝟙 G.val.X.left)
    infer_instance⟩
  obtain ⟨Z, hZ⟩ := LinearAlgebraicGroups.centralizerScheme k G H
  refine ⟨Z, hZ, ?_⟩
  intro A g
  exact (hZ _ g).symm.trans (centralizes_iff_scalar G c A g)

end SchemeCentre

theorem matrixWeightEntries : MatrixWeightEntries.{u} :=
  SymplecticDatumTorusAndBorel.matrixWeightEntries

theorem matrixLieWeights : MatrixLieWeights.{u} :=
  SymplecticDatumTorusAndBorel.matrixLieWeights

section MuTwo

open Specs.DiagonalizableGroups

private def rootOfUnityScalar (I R : Type u) [Fintype I] [DecidableEq I] [CommRing R] :
    rootsOfUnity 2 R →* PointGroup I R where
  toFun a := ⟨Matrix.scalar _ (a.val : R), (isometry_iff _).mpr (by
    rw [adjoint_scalar, ← map_mul, ← pow_two, (mem_rootsOfUnity' 2 a.val).mp a.prop, map_one])⟩
  map_one' := Subtype.ext (map_one (Matrix.scalar (Indices I)))
  map_mul' a b := Subtype.ext (map_mul (Matrix.scalar (Indices I)) (a.val : R) (b.val : R))

private lemma rootOfUnityScalar_injective [Nonempty I] :
    Function.Injective (rootOfUnityScalar I R) := by
  let i : Indices I := Sum.inl (Classical.choice (inferInstance : Nonempty I))
  intro a b h
  apply rootsOfUnity.coe_injective
  have h' := congrArg (fun g : PointGroup I R => g.val i i) h
  simpa [rootOfUnityScalar, Matrix.scalar_apply] using h'

private def rootOfUnityScalarNat (k I : Type u) [Field k] [Fintype I] [DecidableEq I] :
    rootsOfUnityPoints k 2 ⟶ symplecticPoints k I where
  app R := GrpCat.ofHom (rootOfUnityScalar I R)
  naturality R S f := by
    apply GrpCat.ext
    intro a
    apply Subtype.ext
    change (Matrix.scalar (Indices I) (f.hom (a.val : R))) =
      (Matrix.scalar (Indices I) (a.val : R)).map f.hom.toRingHom
    simp [Matrix.scalar_apply, Matrix.diagonal_map (map_zero f.hom.toRingHom)]

private lemma muTwo_finite (k : Type u) [Field k] : IsFinite (muTwo k).val.X.hom := by
  let M := ULift.{u} (Multiplicative (ZMod 2))
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k M))))
  rw [IsFinite.SpecMap_iff]
  change (algebraMap k (MonoidAlgebra k M)).Finite
  rw [RingHom.finite_algebraMap]
  exact Module.Finite.of_basis (MonoidAlgebra.basis (ULift.{u} (Multiplicative (ZMod 2))) k)

set_option backward.isDefEq.respectTransparency false in
theorem centreIsMuTwo : CentreIsMuTwo.{u} := by
  intro k I _ _ _ _ G c
  obtain ⟨Z, hZ, hz⟩ := scalarSchemeCentre k I G c
  obtain ⟨d, _⟩ := LinearAlgebraicGroups.DiagonalizableGroups.diagonalCyclic k 2
  let H := muTwo k
  let F := (groupPointsFunctor k).obj H.val
  let P := (groupPointsFunctor k).obj G.val
  let ZP := (groupPointsFunctor k).obj Z.group
  let b : F ⟶ P := d.hom ≫ rootOfUnityScalarNat k I ≫ c.inv
  let j : ZP ⟶ P := (groupPointsFunctor k).map Z.inclusion
  letI : IsClosedImmersion Z.inclusion.hom.hom.left := Z.isClosedImmersion
  haveI : Mono Z.inclusion.hom.hom := Over.mono_of_mono_left _
  have hj (R : TestAlgebra k) : Function.Injective (j.app R) := by
    intro x y h
    exact (cancel_mono Z.inclusion.hom.hom).mp h
  have hμ (R : TestAlgebra k) (a : F.obj R) :
      IsScalarMuTwo (show PointGroup I R from c.hom.app R (b.app R a)).val := by
    let z : rootsOfUnity 2 R := d.hom.app R a
    have he : c.hom.app R (b.app R a) =
        (show (symplecticPoints k I).obj R from rootOfUnityScalar I R z) :=
      GrpCat.hom_inv_apply (c.app R) (rootOfUnityScalar I R z)
    change IsScalarMuTwo (show PointGroup I R from c.hom.app R (b.app R a)).val
    rw [he]
    exact ⟨z.val, by simpa [pow_two] using (mem_rootsOfUnity' 2 z.val).mp z.prop, rfl⟩
  have hex (R : TestAlgebra k) (a : F.obj R) : ∃ z : ZP.obj R, j.app R z = b.app R a :=
    (hz R _).mpr (hμ R a)
  let g (R : TestAlgebra k) (a : F.obj R) : ZP.obj R := Classical.choose (hex R a)
  have hg (R) (a) : j.app R (g R a) = b.app R a := Classical.choose_spec (hex R a)
  let φ : F ⟶ ZP :=
    { app R := GrpCat.ofHom
        { toFun := g R
          map_one' := (hj R) <| (hg R 1).trans
            ((b.app R).hom.map_one.trans (j.app R).hom.map_one.symm)
          map_mul' a a' := (hj R) <| (hg R _).trans <|
            ((b.app R).hom.map_mul a a').trans <| ((hg R a).symm ▸ (hg R a').symm ▸
              ((j.app R).hom.map_mul (g R a) (g R a')).symm) }
      naturality R S f := by
        apply GrpCat.ext
        intro a
        apply hj S
        change j.app S (g S (F.map f a)) = j.app S (ZP.map f (g R a))
        have h₁ := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (b.naturality f)) a
        have h₂ := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (j.naturality f)) (g R a)
        change b.app S (F.map f a) = P.map f (b.app R a) at h₁
        change j.app S (ZP.map f (g R a)) = P.map f (j.app R (g R a)) at h₂
        rw [hg, h₁, h₂, hg] }
  have hφ (R : TestAlgebra k) : Function.Bijective (φ.app R) := by
    constructor
    · intro a a' eq
      have h := congrArg (j.app R : ZP.obj R → P.obj R) eq
      change j.app R (g R a) = j.app R (g R a') at h
      rw [hg, hg] at h
      apply (d.app R).groupIsoToMulEquiv.injective
      apply rootOfUnityScalar_injective (I := I)
      apply (c.app R).symm.groupIsoToMulEquiv.injective
      exact h
    · intro z
      obtain ⟨s, hs, hz'⟩ := (hz R (j.app R z)).mp ⟨z, rfl⟩
      let a := rootsOfUnity.mkOfPowEq s (n := 2) (by rw [pow_two]; exact hs)
      refine ⟨d.inv.app R a, (hj R) ?_⟩
      change j.app R (g R (d.inv.app R a)) = j.app R z
      rw [hg]
      apply (c.app R).groupIsoToMulEquiv.injective
      change (c.app R).hom ((c.app R).inv (rootOfUnityScalar I R
        ((d.app R).hom ((d.app R).inv a)))) = _
      rw [GrpCat.hom_inv_apply, GrpCat.hom_inv_apply]
      exact Subtype.ext hz'.symm
  letI (R : TestAlgebra k) : IsIso (φ.app R) := by
    let e : F.obj R ≃* ZP.obj R := MulEquiv.ofBijective (φ.app R).hom (hφ R)
    change IsIso e.toGrpIso.hom
    infer_instance
  letI : IsIso φ := NatIso.isIso_of_isIso_app φ
  let e := asIso φ
  have hHa : IsAffine H.val.X.left := H.property.1
  have hZa : IsAffine Z.group.X.left := by
    letI : IsAffine G.val.X.left := G.property.1
    exact isAffine_of_isAffineHom Z.inclusion.hom.hom.left
  let ψ := schemeIsoOfPointIso hHa hZa e
  have hf : (groupPointsFunctor k).map ψ.hom = e.hom :=
    (groupHomEquiv H.val Z.group hHa).apply_symm_apply _
  refine ⟨Z, ψ, d, hZ, ?_, ?_⟩
  · let eS := (((Grp.forget (SchemeOver k)) ⋙
        Over.forget (Spec (CommRingCat.of k)))).mapIso ψ
    have hS : eS.inv ≫ H.val.X.hom = Z.group.X.hom := Over.w ψ.inv.hom.hom
    rw [← hS]
    haveI : IsFinite H.val.X.hom := muTwo_finite k
    infer_instance
  · intro R a
    change (show PointGroup I R from c.hom.app R
      (((groupPointsFunctor k).map (ψ.hom ≫ Z.inclusion)).app R (d.inv.app R a))).val = _
    rw [Functor.map_comp, hf]
    change (show PointGroup I R from c.hom.app R (j.app R (g R (d.inv.app R a)))).val = _
    rw [hg]
    change (show PointGroup I R from (c.app R).hom ((c.app R).inv
      (rootOfUnityScalar I R ((d.app R).hom ((d.app R).inv a))))).val = _
    rw [GrpCat.hom_inv_apply, GrpCat.hom_inv_apply]
    rfl

end MuTwo

theorem matrixScalarExtension : MatrixScalarExtension.{u} :=
  SymplecticDatumAdjointDescent.matrixScalarExtension

theorem adjointQuotientAction : AdjointQuotientAction.{u} := by
  intro k I _ _ _ _ G c
  obtain ⟨Z, hZ, hscalar⟩ := scalarSchemeCentre k I G c
  have hs : Specs.SymplecticDatumAdjointDescent.ScalarCentre c Z := hscalar
  obtain ⟨Q, q, hq⟩ := SymplecticDatumAdjointDescent.adjointQuotientAction k I G c Z hs
  exact ⟨Z, Q, q, hZ, hs, hq⟩

section BasedDatum

open Specs.SymplecticDatumTorusAndBorel (LatticeCoordinates descending IsSimpleRoot)
open Specs.SymplecticDatumRankOneAndPinning
  (RootIndex partner pairingSign DiagonalMarking MatchesRoot torusTuple upper lower diagonal)
open Specs.AbstractPairing (Root)
open Specs.CharacterDescent (Character)
open Specs.Pinning (SplitBorelPair)
open CocharacterDynamics (cocharacterPoint)

private theorem partner_signedIndex {n : ℕ} (i : Fin n) (s : Bool) :
    partner (signedIndex.{u} i s) = signedIndex i (!s) := by
  cases s <;> rfl

private theorem signedCoordinate_apply {n : ℕ} (i j : Fin n) (s : Bool) :
    RootIndex.signedCoordinate (signedIndex.{u} i s) ⟨j⟩ = (sign s • coordinate i) j := by
  cases s <;> simp [signedIndex, RootIndex.signedCoordinate, sign, coordinate, Pi.single_apply,
    Pi.smul_apply]

private theorem rankOneIndex_weight {n : ℕ} (a : RootLabel n) (i : Fin n) :
    (rankOneIndex.{u} a).weight ⟨i⟩ = rootVector a i := by
  cases a with
  | long j s =>
    simp only [rankOneIndex, RootIndex.weight, RootIndex.first, RootIndex.second,
      partner_signedIndex, Pi.sub_apply, signedCoordinate_apply, rootVector, Pi.smul_apply,
      zsmul_eq_mul]
    cases s <;> simp [sign] <;> ring
  | short j l h s t =>
    simp only [rankOneIndex, RootIndex.weight, RootIndex.first, RootIndex.second, Pi.sub_apply,
      signedCoordinate_apply, rootVector, Pi.add_apply, Pi.smul_apply, zsmul_eq_mul]
    cases s <;> cases t <;> simp [sign] <;> ring

private theorem rankOneIndex_coroot {n : ℕ} (a : RootLabel n) (i : Fin n) :
    (rankOneIndex.{u} a).coroot ⟨i⟩ = corootVector a i := by
  cases a with
  | long j s => exact signedCoordinate_apply j i s
  | short j l h s t =>
    simp only [rankOneIndex, RootIndex.coroot, Pi.sub_apply, signedCoordinate_apply,
      corootVector, Pi.add_apply, Pi.smul_apply, zsmul_eq_mul]
    cases s <;> cases t <;> simp [sign] <;> ring

private theorem corootVector_simpleLabel {n : ℕ} (i : Fin (n + 1)) :
    corootVector (simpleLabel i) = simpleCoroot i := by
  by_cases h : i.val < n <;> simp [simpleLabel, simpleCoroot, h, corootVector, sign, sub_eq_add_neg]

private theorem rankOneIndex_upper {n : ℕ} (a : RootLabel n) (r : R) :
    (rankOneIndex a).matrix (upper r) = 1 + r • elementaryDirection R a := by
  rw [(SymplecticDatumRankOneAndPinning.matrixValues (HyperbolicIndex.{u} n) R (rankOneIndex a)).1]
  cases a with
  | long i s => simp [rankOneIndex, RootIndex.upperMatrix, partner_signedIndex, elementaryDirection]
  | short i j h s t =>
    cases s <;> cases t <;>
      simp [rankOneIndex, RootIndex.upperMatrix, elementaryDirection, pairingSign,
        partner, signedIndex, sign, smul_add, add_assoc, smul_eq_mul]

private theorem rankOneIndex_lower {n : ℕ} (a : RootLabel n) (r : R) :
    (rankOneIndex a).matrix (lower r) = 1 + r • oppositeDirection R a := by
  rw [(SymplecticDatumRankOneAndPinning.matrixValues (HyperbolicIndex.{u} n) R (rankOneIndex a)).2.1]
  cases a with
  | long i s => simp [rankOneIndex, RootIndex.lowerMatrix, partner_signedIndex, oppositeDirection]
  | short i j h s t =>
    cases s <;> cases t <;>
      simp [rankOneIndex, RootIndex.lowerMatrix, oppositeDirection, pairingSign,
        partner, signedIndex, sign, smul_add, add_assoc, smul_eq_mul]

variable {k : Type u} [Field k] {n : ℕ} {G : AffineAlgebraicGroup k}
  {c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k (HyperbolicIndex.{u} n)}
  {T : ClosedSubgroup G.val}

private theorem matchesRoot_of_coordinates (m : DiagonalMarking c T)
    (L : LatticeCoordinates m.points) (a : RootLabel n) (α : Character T.group)
    (hα : L.X (Additive.ofMul α) = rootVector a) : MatchesRoot m (rankOneIndex a) α := by
  apply (SymplecticDatumRankOneAndPinning.rootMonomialValues m (rankOneIndex a) α).mpr
  intro R t
  let z := m.points.hom.app R t
  have hz : m.points.inv.app R z = t := GrpCat.hom_inv_apply (m.points.app R).symm t
  have h := L.characterEvaluation R z α
  rw [hz, hα] at h
  refine h.trans (congrArg Units.val ?_)
  refine Fintype.prod_equiv (Equiv.ulift : HyperbolicIndex.{u} n ≃ Fin n).symm _ _ (fun i => ?_)
  rw [rankOneIndex_weight]
  rfl

open private laurentCharacter laurentUnit_zpow_eq_one
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SymplecticDatumRankOneAndPinning

private theorem laurentUnit_zpow_injective (k : Type u) [Field k] :
    Function.Injective (fun i : ℤ => (laurentCharacter k (Multiplicative.ofAdd (1 : ℤ))) ^ i) := by
  intro i j h
  dsimp only at h
  apply sub_eq_zero.mp
  apply laurentUnit_zpow_eq_one k
  rw [_root_.zpow_sub, h, mul_inv_cancel]

/-- The computed torus, rank-one homomorphisms, and Borel determine the pinned datum. -/
theorem basedComputation : BasedComputation.{u} := by
  classical
  intro k _ n G c
  obtain ⟨T, d, L, e, label, y, dyn, hsplit, hmax, hd, he, hweight, hroot, hy,
    hreg, _, _, hpositive, hsimple⟩ := SymplecticDatumTorusAndBorel.torusAndBorel k n G c
  let I := HyperbolicIndex.{u} (n + 1)
  have hG := LinearAlgebraicGroups.SymplecticMatrixStructure.reductivity k I G ⟨c⟩
  let m : DiagonalMarking c T := ⟨d, fun R t => by
    have h := hd R (d.hom.app R t)
    change (show PointGroup I R from c.hom.app R
      (d.inv.app R (d.hom.app R t) ≫ T.inclusion.hom.hom)).val = _ at h
    rw [show d.inv.app R (d.hom.app R t) = t from GrpCat.hom_inv_apply (d.app R).symm t] at h
    exact h⟩
  have hmatch (a : RootLabel (n + 1)) : MatchesRoot m (rankOneIndex a) (label a).val :=
    matchesRoot_of_coordinates m L a (label a).val (hroot a).1
  let index (α : Root T) : RootIndex I := rankOneIndex (label.symm α)
  have hindex (α : Root T) : MatchesRoot m (index α) α.val := by
    simpa only [label.apply_symm_apply] using hmatch (label.symm α)
  have hdescending (R : TestAlgebra k) (a : Rˣ) (i : I) :
      (m.points.hom.app R (cocharacterPoint y R a)) i = a ^ (n + 1 - i.down.val) := by
    change (d.hom.app R (cocharacterPoint y R a) : I → Rˣ) ⟨i.down⟩ = _
    rw [L.cocharacterEvaluation, hy, descending, ← zpow_natCast,
      Nat.cast_sub (Nat.le_of_lt i.down.isLt)]
  let A := LinearAlgebraicGroups.Classification.Pinning.standardAdditiveLine k
  obtain ⟨hB, hTB, U, p, hpin⟩ :=
    (SymplecticDatumRankOneAndPinning.simplePinning n m hG hsplit hmax y
      hdescending index hindex).2 dyn A
  let P : SplitBorelPair k := ⟨G, hG, T, hsplit, hmax, dyn.parabolic, hB, hTB⟩
  obtain ⟨D⟩ := LinearAlgebraicGroups.Classification.Pinning.datumExists P
  letI := D.comm
  obtain ⟨S, s, hS⟩ := SymplecticDatumRankOneAndPinning.representedSchemeMaps k
  choose f hf using fun a : RootLabel (n + 1) => hS I G c (rankOneIndex a)
  have hcoroot (a : RootLabel (n + 1)) (R : TestAlgebra k) (z : Rˣ) :
      d.hom.app R (cocharacterPoint (Additive.toMul (D.datum.rootDatum.coroot (label a))) R z) =
        torusTuple (rankOneIndex a).coroot z :=
    (SymplecticDatumRankOneAndPinning.attachedCorootValues m hG hsplit hmax
      (rankOneIndex a) (label a) (hmatch a)).2 _ (D.datum.attached (label a)) R z
  have hcorootVector (a : RootLabel (n + 1)) :
      L.Y (D.datum.rootDatum.coroot (label a)) = corootVector a := by
    funext i
    -- The Laurent variable distinguishes the exponents over every field.
    let R := CommAlgCat.of k (LaurentPolynomial k)
    let z : Rˣ := laurentCharacter k (Multiplicative.ofAdd (1 : ℤ))
    have h := congrFun (hcoroot a R z) (⟨i⟩ : I)
    change (d.hom.app R (cocharacterPoint (Additive.toMul (D.datum.rootDatum.coroot (label a)))
      R z) : I → Rˣ) ⟨i⟩ = z ^ (rankOneIndex a).coroot ⟨i⟩ at h
    rw [L.cocharacterEvaluation, rankOneIndex_coroot] at h
    exact laurentUnit_zpow_injective k h
  obtain ⟨b₀, hb₀⟩ := simpleCorootBasis n
  let b := b₀.map L.Y.symm
  have hb (i : Fin (n + 1)) : b i = D.datum.rootDatum.coroot (label (simpleLabel i)) ∧
      L.Y (b i) = simpleCoroot i := by
    have h : L.Y (b i) = simpleCoroot i := by
      change L.Y (L.Y.symm (b₀ i)) = _
      rw [L.Y.apply_symm_apply, hb₀]
    refine ⟨L.Y.injective (h.trans ?_), h⟩
    rw [hcorootVector, corootVector_simpleLabel]
  obtain ⟨Z, _, _, hZ, hfinite, _⟩ := centreIsMuTwo k I G c
  have hss := (Reductive.CentralDerived.semisimpleIffFiniteCentre G hG Z hZ).mpr hfinite
  have hspan : SimplyConnectedLattice.corootLatticeOf D.datum = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨label (simpleLabel i), (hb i).1.symm⟩
  have hsc := (Classification.SimplyConnectedLattice.latticeCriterion G hss T hsplit hmax D.datum).mpr hspan
  refine ⟨P, rfl, d, D, L.X, L.Y, label, y, dyn, A, U, p, S, s, f, e, b,
    hd, L.characterEvaluation, L.cocharacterEvaluation, L.compositionPairing, he, hweight,
    fun a => (hroot a).2, ?_, hy, hreg, ⟨⟨𝟙 _, Category.id_comp _⟩, ⟨𝟙 _, Category.id_comp _⟩⟩,
    hpositive, ?_, hb, ?_, hf, ?_, ?_, hss, hsc⟩
  · intro a
    exact ⟨(congrArg L.X (D.datum.root_eq (label a))).trans (hroot a).1, hcorootVector a⟩
  · intro a
    rw [D.simple_iff, ← hsimple a]
    constructor
    · rintro ⟨hp, h⟩
      exact ⟨hp, fun ⟨β, δ, hβ, hδ, heq⟩ => h β hβ δ hδ heq⟩
    · rintro ⟨hp, h⟩
      exact ⟨hp, fun β hβ δ hδ heq => h ⟨β, δ, hβ, hδ, heq⟩⟩
  · intro i R r
    apply (c.app R).groupIsoToMulEquiv.injective
    apply Subtype.ext
    exact (hpin i R r).trans (hf (label.symm i.val) R (upper r)).symm
  · intro a R r
    exact ⟨(hf a R (upper r)).trans (rankOneIndex_upper a r),
      (hf a R (lower r)).trans (rankOneIndex_lower a r)⟩
  · intro a R z
    apply (c.app R).groupIsoToMulEquiv.injective
    apply Subtype.ext
    have hdiag := (SymplecticDatumRankOneAndPinning.matrixValues I R (rankOneIndex a)).2.2 z
    have hpoint := (m.diagonal_value R _).trans (congrArg hyperbolicDiagonal (hcoroot a R z))
    exact (hf a R (diagonal z)).trans (hdiag.trans hpoint.symm)

end BasedDatum

end

end LinearAlgebraicGroups.RootData.SymplecticDatum
