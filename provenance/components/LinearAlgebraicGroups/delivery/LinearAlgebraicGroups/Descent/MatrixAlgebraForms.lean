import Specs.LinearAlgebraicGroups.Descent.MatrixAlgebraForms
import LinearAlgebraicGroups.Flag.HomogeneousQuotient
import LinearAlgebraicGroups.Descent.NonabelianCohomology
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ProjectiveClassification
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct MatrixGroups CategoryTheory.MonObj
open CategoryTheory.CartesianMonoidalCategory

namespace LinearAlgebraicGroups.Descent.MatrixAlgebraForms

universe u w

noncomputable section

set_option maxHeartbeats 1100000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency.types false

open Matrix RM03.Brauer
open RM03.Brauer.ProjectiveClassification
  (Mat Form Isomorphic SplitClasses Implements IsTransport)
open RM03.Brauer.SemilinearDescent (AlgebraAction)

open private conjugation conjugation_injective conjugation_surjective
  conjugation_mk coefficient_conjugation from
  MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ProjectiveClassification

theorem conjugationIdentification : ConjugationIdentification.{u} := by
  intro k K _ _ _ n hn
  exact ⟨MulEquiv.ofBijective conjugation ⟨conjugation_injective, conjugation_surjective hn⟩,
    conjugation_mk, coefficient_conjugation⟩

theorem projectivePresentable : ProjectivePresentable.{u} := by
  intro k _ n hn
  letI : Nonempty (ULift.{u} (Fin n)) := ⟨⟨⟨0, hn⟩⟩⟩
  obtain ⟨hm, hl, em, el, s, hs, hscalar, _, P, G, q, e, _, hker, hq⟩ :=
    LinearAlgebraicGroups.HomogeneousQuotient.projectiveLinearQuotient k (ULift.{u} (Fin n))
  exact ⟨⟨_, ⟨_, s, hs⟩, el, em, hscalar, G, q, hker, P, e, hq⟩⟩

open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient

section Points

variable {k : Type u} [Field k] {n : ℕ} (P : ProjectivePresentation k n)

private def matrixProjectionNat :
    Specs.StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)) ⟶
      (groupPointsFunctor k).obj P.projectiveGroup.val :=
  P.linearPoints.inv ≫ (groupPointsFunctor k).map P.projection

private def matrixProjection (R : TestAlgebra k) :
    GL (ULift.{u} (Fin n)) R →* Points P.projectiveGroup.val.X R :=
  ((matrixProjectionNat P).app R).hom

private theorem matrixProjection_apply (R : TestAlgebra k) (G : GL (ULift.{u} (Fin n)) R) :
    matrixProjection P R G =
      P.linearPoints.inv.app R G ≫ P.projection.hom.hom := rfl

private theorem matrixProjection_natural {R S : TestAlgebra k} (a : R ⟶ S) (G : GL (ULift.{u} (Fin n)) R) :
    matrixProjection P S (GeneralLinearGroup.map a.hom.toRingHom G) =
      mapPoints a (matrixProjection P R G) :=
  congrArg (fun f : (Specs.StandardGroups.generalLinearPoints k (ULift.{u} (Fin n))).obj R ⟶
      ((groupPointsFunctor k).obj P.projectiveGroup.val).obj S => f G)
    ((matrixProjectionNat P).naturality a)

private theorem projection_eq_one_iff (R : TestAlgebra k) (G : GL (ULift.{u} (Fin n)) R) :
    matrixProjection P R G = 1 ↔ ∃ a : Rˣ, G = GeneralLinearGroup.scalar (ULift.{u} (Fin n)) a := by
  rw [matrixProjection_apply, ← schemeKernel_sections P.kernel]
  change (∃ x : Points P.scalarGroup.group.X R,
      x ≫ P.scalarGroup.inclusion.hom.hom = P.linearPoints.inv.app R G) ↔ _
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨P.scalarPoints.hom.app R x, ?_⟩
    rw [← P.scalarFormula R x, hx, ← GrpCat.comp_apply, P.linearPoints.inv_hom_id_app]
    rfl
  · rintro ⟨a, rfl⟩
    refine ⟨P.scalarPoints.inv.app R a, ?_⟩
    apply (P.linearPoints.app R).groupIsoToMulEquiv.injective
    change P.linearPoints.hom.app R (_ ≫ _) = P.linearPoints.hom.app R (P.linearPoints.inv.app R _)
    rw [P.scalarFormula]
    have h : P.scalarPoints.hom.app R (P.scalarPoints.inv.app R a) = a :=
      (P.scalarPoints.app R).groupIsoToMulEquiv.apply_symm_apply a
    rw [h]
    exact ((P.linearPoints.app R).groupIsoToMulEquiv.apply_symm_apply
      (GeneralLinearGroup.scalar (ULift.{u} (Fin n)) a)).symm

private theorem projection_eq_iff (R : TestAlgebra k) (G H : GL (ULift.{u} (Fin n)) R) :
    matrixProjection P R G = matrixProjection P R H ↔
      ∃ a : Rˣ, H = G * GeneralLinearGroup.scalar (ULift.{u} (Fin n)) a := by
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul, projection_eq_one_iff]
  exact exists_congr (fun a => inv_mul_eq_iff_eq_mul)

private theorem lift_over_field {X Y : SchemeOver k} (q : X ⟶ Y) [Surjective q.left]
    {K : Type u} [Field K] [Algebra k K] (y : Points Y (CommAlgCat.of k K)) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Algebra k E)
      (_ : IsScalarTower k K E) (x : Points X (CommAlgCat.of k E)),
      x ≫ q = mapPoints (CommAlgCat.ofHom (IsScalarTower.toAlgHom k K E)) y := by
  let y' : Spec (CommRingCat.of K) ⟶ Y.left := y.left
  let B := pullback q.left y'
  let a : B ⟶ X.left := pullback.fst _ _
  let b : B ⟶ Spec (CommRingCat.of K) := pullback.snd _ _
  haveI : Surjective b := MorphismProperty.pullback_snd q.left y' ‹Surjective q.left›
  obtain ⟨z, _⟩ := b.surjective (IsLocalRing.closedPoint K)
  let E := B.residueField z
  let f : CommRingCat.of K ⟶ E := Spec.preimage (B.fromSpecResidueField z ≫ b)
  letI : Algebra K E := f.hom.toAlgebra
  letI : Algebra k E := (f.hom.comp (algebraMap k K)).toAlgebra
  letI : IsScalarTower k K E := IsScalarTower.of_algebraMap_eq' rfl
  have hf : Spec.map (CommRingCat.ofHom (algebraMap K E)) = B.fromSpecResidueField z ≫ b :=
    Spec.map_preimage _
  have hq : a ≫ q.left = b ≫ y' := pullback.condition
  have hx : (B.fromSpecResidueField z ≫ a) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
    have hw : a ≫ X.hom = b ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
      have hy : y' ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap k K)) := y.w
      rw [← q.w, ← Category.assoc, hq, Category.assoc, hy]
    rw [Category.assoc, hw, ← Category.assoc, ← hf]
    exact (Spec.map_comp _ _).symm
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, Over.homMk _ hx, ?_⟩
  apply Over.OverMorphism.ext
  change (B.fromSpecResidueField z ≫ a) ≫ q.left =
    Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ y'
  rw [hf, Category.assoc, hq, Category.assoc]

private theorem mul_scalar_entry {R : Type u} [CommRing R] (A : GL (ULift.{u} (Fin n)) R) (a : Rˣ)
    (i j : (ULift.{u} (Fin n))) : (A * GeneralLinearGroup.scalar (ULift.{u} (Fin n)) a) i j = A i j * a.val := by
  change ((A : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) R) * Matrix.scalar (ULift.{u} (Fin n)) a.val) i j = _
  rw [Matrix.scalar_apply, Matrix.mul_diagonal]

open private spec_precomp_injective from LinearAlgebraicGroups.Descent.NonabelianCohomology

/-- A field-valued point lifts after a field extension. Normalizing one nonzero
entry trivializes its scalar transition function over the tensor square. -/
private theorem matrixProjection_surjective (hn : 0 < n)
    {K : Type u} [Field K] [Algebra k K] :
    Function.Surjective (matrixProjection P (CommAlgCat.of k K)) := by
  classical
  letI : Nonempty (ULift.{u} (Fin n)) := ⟨⟨⟨0, hn⟩⟩⟩
  let R := CommAlgCat.of k K
  letI : IsIso P.comparison.hom.left := Functor.map_isIso (Over.forget _) _
  haveI := P.presentation.surjective
  haveI : Surjective P.projection.hom.hom.left := by
    rw [← P.projectionFormula, Over.comp_left]
    infer_instance
  intro y
  obtain ⟨E, hField, hKE, hkE, hTower, x, hx⟩ := lift_over_field P.projection.hom.hom y
  let S := CommAlgCat.of k E
  let T := CommAlgCat.of k (E ⊗[K] E)
  let f : R ⟶ S := CommAlgCat.ofHom (IsScalarTower.toAlgHom k K E)
  let φ : S ⟶ T := CommAlgCat.ofHom
    ((Algebra.TensorProduct.includeLeft : E →ₐ[K] E ⊗[K] E).restrictScalars k)
  let ψ : S ⟶ T := CommAlgCat.ofHom
    ((Algebra.TensorProduct.includeRight : E →ₐ[K] E ⊗[K] E).restrictScalars k)
  have hφψ : f ≫ φ = f ≫ ψ := by
    ext a
    change (Algebra.TensorProduct.includeLeft : E →ₐ[K] E ⊗[K] E) (algebraMap K E a) =
      (Algebra.TensorProduct.includeRight : E →ₐ[K] E ⊗[K] E) (algebraMap K E a)
    rw [AlgHom.commutes, AlgHom.commutes]
  let A : GL (ULift.{u} (Fin n)) E := P.linearPoints.hom.app S x
  have hA : matrixProjection P S A = mapPoints f y := by
    rw [matrixProjection_apply]
    change P.linearPoints.inv.app S (P.linearPoints.hom.app S x) ≫ P.projection.hom.hom = _
    rw [← GrpCat.comp_apply, P.linearPoints.hom_inv_id_app]
    exact hx
  obtain ⟨i, j, hij⟩ : ∃ i j : (ULift.{u} (Fin n)), A i j ≠ 0 := by
    by_contra! h
    exact A.ne_zero (Matrix.ext h)
  let B : GL (ULift.{u} (Fin n)) E := A * GeneralLinearGroup.scalar (ULift.{u} (Fin n)) (Units.mk0 (A i j) hij)⁻¹
  have hBij : B i j = 1 := by
    rw [show B i j = _ from mul_scalar_entry A _ i j]
    exact (Units.mk0 (A i j) hij).mul_inv
  have hB : matrixProjection P S B = mapPoints f y :=
    ((projection_eq_iff P S A B).mpr ⟨_, rfl⟩).symm.trans hA
  have hBC : matrixProjection P T (GeneralLinearGroup.map φ.hom.toRingHom B) =
      matrixProjection P T (GeneralLinearGroup.map ψ.hom.toRingHom B) := by
    rw [matrixProjection_natural, matrixProjection_natural, hB]
    change (testSpec k).map φ.op ≫ (testSpec k).map f.op ≫ y =
      (testSpec k).map ψ.op ≫ (testSpec k).map f.op ≫ y
    rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      ← op_comp, ← op_comp, hφψ]
  obtain ⟨d, hd⟩ := (projection_eq_iff P T _ _).mp hBC
  have hd1 : d = 1 := by
    have he := congrArg (fun v : GL (ULift.{u} (Fin n)) (E ⊗[K] E) => v i j) hd
    rw [mul_scalar_entry, GeneralLinearGroup.map_apply, GeneralLinearGroup.map_apply,
      hBij, map_one, map_one, one_mul] at he
    exact Units.ext he.symm
  rw [hd1, map_one, mul_one] at hd
  have hEntry (a b : (ULift.{u} (Fin n))) : ∃ t : K, algebraMap K E t = B a b := by
    apply (Algebra.IsEffective.of_faithfullyFlat (R := K) (S := E) (B a b)).mp
    rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]
    exact (congrArg (fun v : GL (ULift.{u} (Fin n)) (E ⊗[K] E) => v a b) hd).symm
  choose C hC using hEntry
  have hCmat : (Matrix.of C).map (algebraMap K E) = (B : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) E) :=
    Matrix.ext hC
  have hCdet : (Matrix.of C).det ≠ 0 := by
    intro h
    apply B.det_ne_zero
    rw [← hCmat]
    change ((algebraMap K E).mapMatrix (Matrix.of C)).det = 0
    rw [← RingHom.map_det, h, map_zero]
  let G := GeneralLinearGroup.mkOfDetNeZero (Matrix.of C) hCdet
  have hG : GeneralLinearGroup.map f.hom.toRingHom G = B := Units.ext hCmat
  refine ⟨G, ?_⟩
  apply Over.OverMorphism.ext
  apply spec_precomp_injective (algebraMap K E)
  change (mapPoints f (matrixProjection P R G)).left = (mapPoints f y).left
  rw [← matrixProjection_natural, hG, hB]

private theorem liftMatrix_scalar {R : Type u} [CommRing R] (a : Rˣ) :
    liftMatrix (GeneralLinearGroup.scalar (Fin n) a) = GeneralLinearGroup.scalar (ULift.{u} (Fin n)) a := by
  apply Units.ext
  ext i j
  change Matrix.scalar (Fin n) a.val i.down j.down = Matrix.scalar (ULift.{u} (Fin n)) a.val i j
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply, ULift.down_inj]

private theorem liftMatrix_map {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (G : GL (Fin n) R) : liftMatrix (GeneralLinearGroup.map f G) =
      GeneralLinearGroup.map f (liftMatrix G) := Units.ext (Matrix.ext fun _ _ => rfl)

theorem projectivePointComparison : ProjectivePointComparison.{u} := by
  intro k K _ _ _ n hn P
  let R := CommAlgCat.of k K
  let f := (matrixProjection P R).comp liftMatrix.toMonoidHom
  have hf : f.comp (GeneralLinearGroup.scalar (Fin n)) = 1 := by
    apply MonoidHom.ext
    intro a
    change matrixProjection P R (liftMatrix (GeneralLinearGroup.scalar (Fin n) a)) = 1
    rw [liftMatrix_scalar]
    exact (projection_eq_one_iff P R _).mpr ⟨a, rfl⟩
  let l := ProjGenLinGroup.lift f hf
  have hi : Function.Injective l := by
    intro g h e
    obtain ⟨G, rfl⟩ := ProjGenLinGroup.mk_surjective g
    obtain ⟨H, rfl⟩ := ProjGenLinGroup.mk_surjective h
    change matrixProjection P R (liftMatrix G) = matrixProjection P R (liftMatrix H) at e
    obtain ⟨a, ha⟩ := (projection_eq_iff P R _ _).mp e
    apply ProjGenLinGroup.mk_eq_mk_iff.mpr
    refine ⟨a, liftMatrix.injective ?_⟩
    simpa only [map_mul, liftMatrix_scalar] using ha.symm
  have hs : Function.Surjective l := by
    intro y
    obtain ⟨G, hG⟩ := matrixProjection_surjective P hn y
    exact ⟨ProjGenLinGroup.mk (liftMatrix.symm G), by
      change matrixProjection P R (liftMatrix (liftMatrix.symm G)) = _
      rw [MulEquiv.apply_symm_apply, hG]⟩
  refine ⟨MulEquiv.ofBijective l ⟨hi, hs⟩, fun _ => rfl, ?_⟩
  intro σ g
  obtain ⟨G, rfl⟩ := ProjGenLinGroup.mk_surjective g
  change matrixProjection P R (liftMatrix (GeneralLinearGroup.map σ.toRingHom G)) = _
  rw [liftMatrix_map]
  exact matrixProjection_natural P (CommAlgCat.ofHom σ.toAlgHom) (liftMatrix G)

end Points

theorem formCriterion : FormCriterion.{u,w} := by
  intro k K _ _ _ n hn A _ _ hA
  exact ProjectiveClassification.form_iff_degree_splits hn hA

theorem effectiveDescent : EffectiveDescent.{u} := by
  intro k K _ _ _ _ _ n hn c
  obtain ⟨e, he⟩ := ProjectiveClassification.action_correspondence (k := k) (K := K) hn
  have h := (he c (e c)).mpr rfl
  exact ⟨e c, h, ProjectiveClassification.descended_form hn c (e c) h⟩

theorem cohomologyComparison : CohomologyComparison.{u} := by
  intro k K _ _ _ _ n M _ ρ m hm
  let : TopologicalSpace M := ⊥
  let j : ProjectiveClassification.Cocycle k K n ≃ GaloisCocycle ρ :=
    { toFun := fun c => ⟨m ∘ c.val, continuous_of_discreteTopology, fun σ τ => by
        change m (c.val (σ * τ)) = m (c.val σ) * ρ σ (m (c.val τ))
        rw [c.law, map_mul]
        exact congrArg (m (c.val σ) * ·) (hm σ (c.val τ))⟩
      invFun := fun c => ⟨m.symm ∘ c.val, fun σ τ => by
        apply m.injective
        change m (m.symm (c.val (σ * τ))) =
          m (m.symm (c.val σ) * projectiveAction n σ (m.symm (c.val τ)))
        simpa only [map_mul, hm, m.apply_symm_apply] using c.property.2 σ τ⟩
      left_inv := fun c => by
        cases c
        simp [Function.comp_def]
      right_inv := fun c => Subtype.ext (funext fun σ => m.apply_symm_apply _) }
  have hj (c d : ProjectiveClassification.Cocycle k K n) :
      ProjectiveClassification.Cohomologous k K n c d ↔
        NonabelianCohomology.Cohomologous (j c) (j d) := by
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨m b, fun σ => ?_⟩
      change m (d.val σ) = (m b)⁻¹ * m (c.val σ) * ρ σ (m b)
      rw [hb, map_mul, map_mul, map_inv]
      exact congrArg ((m b)⁻¹ * m (c.val σ) * ·) (hm σ b)
    · rintro ⟨b, hb⟩
      obtain ⟨b, rfl⟩ := m.surjective b
      refine ⟨b, fun σ => m.injective ?_⟩
      rw [map_mul, map_mul, map_inv]
      exact (hb σ).trans (congrArg ((m b)⁻¹ * m (c.val σ) * ·) (hm σ b)).symm
  let e : ProjectiveClassification.H1 k K n ≃ GaloisH1 ρ :=
    { toFun := Quot.lift (fun c => galoisClass (j c)) (fun c d h => Quotient.sound ((hj c d).mp h))
      invFun := Quotient.lift (fun c => Quot.mk _ (j.symm c)) (fun c d h => by
        change NonabelianCohomology.Cohomologous c d at h
        exact Quot.sound ((hj (j.symm c) (j.symm d)).mpr
          (by simpa only [j.apply_symm_apply] using h)))
      left_inv := fun x => Quot.inductionOn x fun c => by
        change Quot.mk _ (j.symm (j c)) = Quot.mk _ c
        rw [j.symm_apply_apply]
      right_inv := fun x => Quotient.inductionOn x fun c => by
        change galoisClass (j (j.symm c)) = galoisClass c
        rw [j.apply_symm_apply] }
  refine ⟨j, e, fun _ _ => rfl, hj, fun _ => rfl, ?_⟩
  change galoisClass (j _) = galoisClass (NonabelianCohomology.trivial ρ)
  apply congrArg galoisClass
  apply Subtype.ext
  funext σ
  exact map_one m

theorem classificationOnPresentation : ClassificationOnPresentation.{u,w} := by
  intro k K _ _ _ _ _ n hn P
  let ρ := NonabelianCohomology.pointAction k K P.projectiveGroup.val.X
  obtain ⟨m, hm⟩ := projectivePointComparison (K := K) hn P
  obtain ⟨j, t, hj, _, ht, ht₀⟩ := cohomologyComparison ρ m hm.2
  obtain ⟨e, hA, hB, hc, hex, h₀⟩ :=
    ProjectiveClassification.classification (k := k) (K := K) hn
  refine ⟨m, j, e.trans t, hm, hj, ?_, ?_, ?_, ?_, hex, ?_⟩
  · intro A s
    obtain ⟨τ, hτ, c, hc⟩ := ProjectiveClassification.transported_cocycle hn s
    exact ⟨τ, c, hτ, hc, (congrArg t (hA A s τ c hτ hc)).trans (ht c)⟩
  · intro A s τ c hτ h
    exact (congrArg t (hA A s τ c hτ h)).trans (ht c)
  · intro B _ _ s τ c hτ h
    obtain ⟨A, hiso, hclass⟩ := hB s τ c hτ h
    exact ⟨A, hiso, (congrArg t hclass).trans (ht c)⟩
  · intro c τ h
    obtain ⟨A, hiso, hclass⟩ := hc c τ h
    refine ⟨A, hiso, ?_⟩
    rw [← ht c]
    exact (congrArg e.symm (t.symm_apply_apply _)).trans hclass
  · intro A h
    exact (congrArg t (h₀ A h)).trans ht₀

theorem classification : Classification.{u,w} := by
  intro k K _ _ _ _ _ n hn
  obtain ⟨P⟩ := projectivePresentable k hn
  exact ⟨P, classificationOnPresentation (K := K) hn P⟩

end
end LinearAlgebraicGroups.Descent.MatrixAlgebraForms
