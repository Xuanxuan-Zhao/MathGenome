import Specs.LinearAlgebraicGroups.Classification.RationalIsogenyObstruction
import LinearAlgebraicGroups.Affine.StandardGroups
import LinearAlgebraicGroups.Classification.TypeAOneLattices
import LinearAlgebraicGroups.Descent.Hilbert90AndTorsors
import LinearAlgebraicGroups.Flag.TorsorObstruction
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Classification.RationalIsogenyObstruction

open LinearAlgebraicGroups.Specs
open Specs.RationalIsogenyObstruction Specs.Fppf Specs.TorsorObstruction
open Specs.TypeAOneLattices Specs.StandardGroups LinearAlgebraicGroups.StandardGroups
open Specs.GeneralLinearStructure (MatrixPoints SpecialMatrixPoints)
open Specs.QuotientEmbedding (Presentation)
open Specs.Unipotent (Index closedSubgroupAlgebraicGroup)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open private schemeKernel_sections quotientRepresentsImage from
  LinearAlgebraicGroups.Affine.SchemeImageQuotient

variable {k : Type u} [Field k] {n : ℕ}
variable {G S M : AffineAlgebraicGroup k}
variable {g : MatrixPoints G n} {s : SpecialMatrixPoints S n}
variable {a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k}

open Specs.GeneralLinearCentralIsogeny (pointMap)

private abbrev matrixValue (g : MatrixPoints G n) (R : TestAlgebra k) (x : Points G.val.X R) :
    Matrix.GeneralLinearGroup (Index.{u} n) R := g.hom.app R x

private theorem scalar_displacement (Q : ScalarQuotient g s a) (R : TestAlgebra k)
    (x y : Points G.val.X R) :
    pointMap Q.q R y = pointMap Q.q R x ↔
      ∃ t : Rˣ, matrixValue g R y =
        matrixValue g R x * Matrix.GeneralLinearGroup.scalar (Index.{u} n) t := by
  let qR : (Points G.val.X R) →* Points Q.P.val.X R :=
    ((groupPointsFunctor k).map Q.q |>.app R).hom
  let gR : Points G.val.X R →* Matrix.GeneralLinearGroup (Index.{u} n) R := (g.hom.app R).hom
  have hker : qR (x⁻¹ * y) = 1 ↔ qR y = qR x := by
    rw [map_mul, map_inv, inv_mul_eq_one, eq_comm]
  change qR y = qR x ↔ _
  rw [← hker]
  change ((x⁻¹ * y) ≫ Q.q.hom.hom = 1) ↔ _
  rw [← schemeKernel_sections Q.adjoint.2.1]
  constructor
  · rintro ⟨z, hz⟩
    change z ≫ Q.Z.inclusion.hom.hom = x⁻¹ * y at hz
    let w := pointMap Q.scalarIso.inv R z
    have hw : pointMap (Q.scalarIso.hom ≫ Q.Z.inclusion) R w = x⁻¹ * y := by
      change (z ≫ Q.scalarIso.inv.hom.hom) ≫
        (Q.scalarIso.hom.hom.hom ≫ Q.Z.inclusion.hom.hom) = _
      have hi := congrArg (fun f : Q.Z.group ⟶ Q.Z.group ↦ f.hom.hom) Q.scalarIso.inv_hom_id
      change Q.scalarIso.inv.hom.hom ≫ Q.scalarIso.hom.hom.hom = 𝟙 _ at hi
      rw [Category.assoc, ← Category.assoc Q.scalarIso.inv.hom.hom Q.scalarIso.hom.hom.hom,
        hi, Category.id_comp, hz]
    refine ⟨a.hom.app R w, ?_⟩
    have h := Q.scalar_eq R w
    rw [hw] at h
    have hm := gR.map_mul x (x⁻¹ * y)
    change gR _ = _ at h
    change gR y = gR x * Matrix.GeneralLinearGroup.scalar (Index.{u} n) (a.hom.app R w)
    rw [← h, ← hm, mul_inv_cancel_left]
  · rintro ⟨t, ht⟩
    let w : Points M.val.X R := a.inv.app R t
    let z := pointMap Q.scalarIso.hom R w
    refine ⟨z, ?_⟩
    change z ≫ Q.Z.inclusion.hom.hom = x⁻¹ * y
    apply (ConcreteCategory.bijective_of_isIso (g.hom.app R)).1
    change g.hom.app R (pointMap (Q.scalarIso.hom ≫ Q.Z.inclusion) R w) = _
    rw [Q.scalar_eq, show a.hom.app R w = t from
      ConcreteCategory.congr_hom (a.inv_hom_id_app R) t]
    change _ = gR (x⁻¹ * y)
    rw [map_mul, map_inv]
    change gR y = gR x * _ at ht
    rw [ht, inv_mul_cancel_left]

private theorem lift_iff_on_field (Q : ScalarQuotient g s a)
    (A : Matrix.GeneralLinearGroup (Index.{u} n) k) :
    HasSpecialLift Q (projectMatrix Q A) ↔
      ∃ b : Points S.val.X (rationalAlgebra k),
        pointMap Q.q (rationalAlgebra k) (pointMap Q.f (rationalAlgebra k) b) =
          pointMap Q.q (rationalAlgebra k) (g.inv.app (rationalAlgebra k) A) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨(rationalTestIso k).hom ≫ b, ?_⟩
    change ((rationalTestIso k).hom ≫ b) ≫ Q.f.hom.hom ≫ Q.q.hom.hom =
      g.inv.app (rationalAlgebra k) A ≫ Q.q.hom.hom
    change b ≫ Q.f.hom.hom ≫ Q.q.hom.hom =
      (rationalTestIso k).inv ≫ g.inv.app (rationalAlgebra k) A ≫ Q.q.hom.hom at hb
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      congrArg ((rationalTestIso k).hom ≫ ·) hb
  · rintro ⟨b, hb⟩
    refine ⟨(rationalTestIso k).inv ≫ b, ?_⟩
    change ((rationalTestIso k).inv ≫ b) ≫ Q.f.hom.hom ≫ Q.q.hom.hom =
      (rationalTestIso k).inv ≫ g.inv.app (rationalAlgebra k) A ≫ Q.q.hom.hom
    exact (Category.assoc _ _ _).trans (congrArg ((rationalTestIso k).inv ≫ ·) hb)

private theorem determinantCriterion (Q : ScalarQuotient g s a)
    (A : Matrix.GeneralLinearGroup (Index.{u} n) k) :
    HasSpecialLift Q (projectMatrix Q A) ↔
      ∃ t : kˣ, t ^ n = Matrix.GeneralLinearGroup.det A := by
  let R := rationalAlgebra k
  have hA : g.hom.app (rationalAlgebra k) (g.inv.app (rationalAlgebra k) A) = A :=
    ConcreteCategory.congr_hom (g.inv_hom_id_app (rationalAlgebra k)) A
  have hcard : Fintype.card (Index.{u} n) = n := by simp [Index]
  rw [lift_iff_on_field]
  simp only [scalar_displacement, matrixValue, Q.f_eq, hA]
  constructor
  · rintro ⟨b, t, ht⟩
    let B : Matrix.SpecialLinearGroup (Index.{u} n) k := s.hom.app R b
    have hB : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL B) = 1 :=
      Units.ext B.property
    have h := congrArg (Matrix.GeneralLinearGroup.det (n := Index.{u} n) (R := k)) ht
    change Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL B) = _ at h
    rw [hB, map_mul, Matrix.GeneralLinearGroup.det_scalar, hcard] at h
    exact ⟨t⁻¹, by rw [inv_pow, inv_eq_iff_mul_eq_one, mul_comm]; exact h.symm⟩
  · rintro ⟨t, ht⟩
    let B := A * Matrix.GeneralLinearGroup.scalar (Index.{u} n) t⁻¹
    have hB : Matrix.GeneralLinearGroup.det B = 1 := by
      simp only [B, map_mul, Matrix.GeneralLinearGroup.det_scalar, hcard, inv_pow]
      rw [ht, mul_inv_cancel]
    let b : Matrix.SpecialLinearGroup (Index.{u} n) k :=
      ⟨B.val, congrArg Units.val hB⟩
    refine ⟨s.inv.app R b, t⁻¹, ?_⟩
    have hb : s.hom.app R (s.inv.app R b) = b := by
      exact ConcreteCategory.congr_hom (s.inv_hom_id_app R) b
    rw [hb]
    exact Units.ext rfl

/-- Hilbert 90 for the scalar torus is the one-by-one case of matrix Hilbert 90. -/
private def scalarAsOneByOne (k : Type u) [Field k] :
    multiplicativePoints k ≅ generalLinearPoints k PUnit.{u+1} :=
  NatIso.ofComponents (fun R ↦ MulEquiv.toGrpIso
    { toFun := Matrix.GeneralLinearGroup.scalar PUnit
      invFun := Matrix.GeneralLinearGroup.det
      left_inv := fun z ↦ by simp
      right_inv := fun B ↦ by
        apply Units.ext
        ext i j
        cases i
        cases j
        simp [Matrix.GeneralLinearGroup.det, Matrix.det_unique]
      map_mul' := map_mul _ }) (by
      intro R T f
      apply GrpCat.ext
      intro z
      exact (Matrix.GeneralLinearGroup.map_scalar _ _).symm)

private theorem allScalarTorsorsNeutral (Q : ScalarQuotient g s a) :
    ∀ c : H1fppf k Q.Z.group, c = fieldNeutralClass Q.Z.group := by
  let Z := closedSubgroupAlgebraicGroup Q.Z
  let e := (groupPointsFunctor k).mapIso Q.scalarIso.symm ≪≫ a ≪≫ scalarAsOneByOne k
  let h := LinearAlgebraicGroups.Descent.hilbert90AndTorsors.{u}
  have hZ : Smooth Z.val.X.hom := MorphismProperty.of_isPullback (P := @Smooth)
    (Q.adjoint.2.1.map (Over.forget _)) Q.smooth
  obtain ⟨classify, -, -⟩ := h.2.2.2.2.1 (S := SeparableClosure k) Z hZ
  intro c
  apply classify.injective
  exact (h.1 Z.val e _).trans (h.1 Z.val e _).symm

private theorem liftFromCoset {H : ClosedSubgroup G.val} (P : Presentation H)
    (e : RationalPoints H ≃ (fieldBase k ⟶ P.scheme))
    (he : ∀ b : fieldBase k ⟶ G.val.X,
      e (rationalCosetMap H (QuotientGroup.mk b)) = b ≫ P.projection)
    (x : RationalPoints H) :
    x ∈ Set.range (rationalCosetMap H) ↔ ∃ b : fieldBase k ⟶ G.val.X, b ≫ P.projection = e x := by
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective c
    exact ⟨b, (he b).symm⟩
  · rintro ⟨b, hb⟩
    exact ⟨QuotientGroup.mk b, e.injective ((he b).trans hb)⟩

private theorem matrixSurjective (Q : ScalarQuotient g s a) :
    Function.Surjective (projectMatrix Q) := by
  intro x
  obtain ⟨e, he, -⟩ :=
    LinearAlgebraicGroups.TorsorObstruction.rationalPointsOfPresentation Q.presentation
  obtain ⟨δ, _, _, _, _, _, _, hneutral, _, _⟩ :=
    LinearAlgebraicGroups.TorsorObstruction.pointedExactness Q.Z
  let y := e.symm (x ≫ Q.iso.inv)
  have hy : y ∈ Set.range (rationalCosetMap Q.Z) := by
    rw [hneutral]
    exact allScalarTorsorsNeutral Q (δ y)
  obtain ⟨b, hb⟩ := (liftFromCoset Q.presentation e he y).mp hy
  have hq : b ≫ Q.q.hom.hom = x := by
    rw [← Q.projection_eq, ← Category.assoc, hb]
    simp [y]
  let R := rationalAlgebra k
  let A : Matrix.GeneralLinearGroup (Index.{u} n) k :=
    g.hom.app R ((rationalTestIso k).hom ≫ b)
  have hA : g.inv.app R A = (rationalTestIso k).hom ≫ b :=
    ConcreteCategory.congr_hom (g.hom_inv_id_app R) _
  refine ⟨A, ?_⟩
  change (rationalTestIso k).inv ≫ g.inv.app R A ≫ Q.q.hom.hom = x
  rw [hA, Category.assoc, Iso.inv_hom_id_assoc, hq]

private theorem fibreObstruction (Q : ScalarQuotient g s a)
    (hc : Specs.CentralIsogenies.IsCentralIsogeny Q.map)
    (N : ClosedSubgroup S.val) (hN : IsSchemeKernel Q.map N) :
    ∃ δ : (fieldBase k ⟶ Q.P.val.X) → H1fppf k N.group,
      (∀ x, IsSchemeFibreClass Q N x (δ x)) ∧
      ∀ x, HasSpecialLift Q x ↔ δ x = fieldNeutralClass N.group := by
  let : IsFinite Q.map.hom.hom.left := hc.1
  let : IsField (CommRingCat.of k) := ‹Field k›.toIsField
  let : LocallyOfFiniteType Q.P.val.X.hom := Q.P.property.2.1
  have : IsLocallyNoetherian Q.P.val.X.left := LocallyOfFiniteType.isLocallyNoetherian Q.P.val.X.hom
  have hfp : LocallyOfFinitePresentation Q.map.hom.hom.left := inferInstance
  have hp : IsImageFactorization Q.map Q.map (𝟙 Q.P.val) :=
    ⟨Category.comp_id _, hc.2.1, hc.2.2.1, hfp, inferInstance, by
      change IsClosedImmersion (𝟙 Q.P.val.X.left)
      infer_instance⟩
  obtain ⟨e, he⟩ := quotientRepresentsImage hp hN
  obtain ⟨V, hV₁, hV₂, hV₃, j, hj⟩ := Q.presentation.quasiProjective
  let P : Presentation N :=
    ⟨Q.P.val.X, ⟨V, hV₁, hV₂, hV₃, Q.iso.inv ≫ j, by
      have : IsIso Q.iso.inv.left := (Over.forget _).map_isIso Q.iso.inv
      exact MorphismProperty.comp_mem _ _ _ inferInstance hj⟩,
      Q.map.hom.hom, hc.2.1, hc.2.2.1, hfp, e, he⟩
  obtain ⟨E, hE, hSections⟩ :=
    LinearAlgebraicGroups.TorsorObstruction.rationalPointsOfPresentation P
  obtain ⟨δ, _, hFibre, _, _, _, _, hNeutral, _, _⟩ :=
    LinearAlgebraicGroups.TorsorObstruction.pointedExactness N
  refine ⟨fun x ↦ δ (E.symm x), ?_, ?_⟩
  · intro x
    refine ⟨E.symm x, hFibre _, fun U b ↦ ?_⟩
    simpa only [Equiv.apply_symm_apply] using hSections (E.symm x) U b
  · intro x
    have hl := (liftFromCoset P E hE (E.symm x)).symm
    rw [hNeutral] at hl
    rw [Equiv.apply_symm_apply] at hl
    exact hl

theorem rationalLifting : RationalLifting.{u} := by
  intro k _ n hn G S M g s a
  obtain ⟨Q, hc, hkernel, -⟩ :=
    LinearAlgebraicGroups.Classification.TypeAOneLattices.matrixProjectiveIsogeny k n hn G S M g s a
  obtain ⟨N, e, r, hN, _, _, _, hscalar, -⟩ := hkernel
  exact ⟨Q, hc, N, e, r, hN, hscalar, matrixSurjective Q, determinantCriterion Q,
    fibreObstruction Q hc N hN⟩

theorem negativeDeterminantObstructs : NegativeDeterminantObstructs := by
  intro G S M g s a Q A hdet hLift
  obtain ⟨t, ht⟩ := (determinantCriterion Q A).mp hLift
  have ht' : (t : ℝ) ^ 2 = (Matrix.GeneralLinearGroup.det A : ℝ) :=
    congrArg Units.val ht
  rw [← ht'] at hdet
  exact (not_lt_of_ge (sq_nonneg (t : ℝ))) hdet

theorem realCounterexample : RealCounterexample := by
  let I := Index.{0} 2
  obtain ⟨Q, hQ, -⟩ :=
    rationalLifting ℝ 2 (by decide) (generalLinearGroup ℝ I) (specialLinearGroup ℝ I)
      (multiplicativeGroup ℝ) (generalLinearGroupPointsIso ℝ I) (specialLinearGroupPointsIso ℝ I)
      (multiplicativeGroupPointsIso ℝ)
  let D : Matrix I I ℝ := Matrix.diagonal (fun i : I ↦ if i = ⟨0⟩ then -1 else 1)
  have hd : D.det = -1 := by
    classical
    rw [Matrix.det_diagonal, Finset.prod_eq_single (⟨0⟩ : I)]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  let A := Matrix.GeneralLinearGroup.mkOfDetNeZero D (by rw [hd]; norm_num)
  have hA : (Matrix.GeneralLinearGroup.det A : ℝ) < 0 := by
    change D.det < 0
    rw [hd]
    norm_num
  exact ⟨_, _, _, _, _, _, Q, A, hQ, rfl, hA, negativeDeterminantObstructs _ _ _ _ _ _ Q A hA⟩

end
end LinearAlgebraicGroups.Classification.RationalIsogenyObstruction
