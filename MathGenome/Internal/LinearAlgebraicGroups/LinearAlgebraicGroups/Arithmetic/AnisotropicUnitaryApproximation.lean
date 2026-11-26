import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryArchimedeanModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryFiniteModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicUnitarySplitCentreWeakApproximation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.CompactProductIsolation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalCocharacterEvaluation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryApproximation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicTensorQuotients
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.LeviConjugacy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.WeakApproximationByTori
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.RingTheory.MatrixAlgebra
import Batteries.Tactic.OpenPrivate

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme)
open scoped CategoryTheory.MonObj Matrix MatrixGroups TensorProduct RestrictedProduct

universe u v

namespace LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryApproximation

open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open AnisotropicUnitaryTensors (HasClosedSplitTorus)
open Specs.Arithmetic.OppositeRadicals (IsNoncentral MultiplicativeGroup)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (IsSemisimple)
open CocharacterDynamics (unitPoint laurentAlgebra laurentParameter)
open private multiplicative_group_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.LeviConjugacy
open private central_iff_comp_eq_zero cocharacter_into_finite_is_zero from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank
open private liftToSchemeKernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open private unitEquiv unitEquiv_unitPoint from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private theorem multiplicativeGroup_id_ne_zero (K : Type u) [Field K] :
    (𝟙 (MultiplicativeGroup K)) ≠ 0 := by
  intro h
  let R := CommAlgCat.of K K
  let S := laurentAlgebra R
  let t := laurentParameter R
  have hpoint := congrArg
    (fun f : MultiplicativeGroup K ⟶ MultiplicativeGroup K => unitPoint S t ≫ f.hom.hom) h
  change unitPoint S t ≫ 𝟙 _ = unitPoint S t ≫ (1 : (MultiplicativeGroup K).X ⟶ _) at hpoint
  rw [Category.comp_id, MonObj.comp_one] at hpoint
  have ht := congrArg (unitEquiv S) hpoint
  rw [unitEquiv_unitPoint, map_one] at ht
  have hv := congrArg Units.val ht
  change (LaurentPolynomial.T 1 : LaurentPolynomial K) = 1 at hv
  have hd := congrArg LaurentPolynomial.degree (hv.trans LaurentPolynomial.T_zero.symm)
  rw [LaurentPolynomial.degree_T, LaurentPolynomial.degree_T] at hd
  exact one_ne_zero (WithBot.coe_injective hd : (1 : ℤ) = 0)

private theorem semisimpleCentralCocharacter_eq_zero {K : Type u} [Field K]
    {G : AffineAlgebraicGroup K} (hG : IsSemisimple G) (c : Cocharacter G.val)
    (hc : ¬ IsNoncentral c) : c = 0 := by
  have hR := reductive_of_semisimple G hG
  obtain ⟨Z, Q, q, hq, _⟩ := Descent.AdjointCocharacters.adjointQuotientExists G hR
  have hcentral : Specs.RelativeRank.IsCentralCocharacter c := fun X g =>
    Classical.not_not.mp (fun hg => hc ⟨X, g, hg⟩)
  obtain ⟨a, ha⟩ := liftToSchemeKernel hq.2.1 c ((central_iff_comp_eq_zero hq c).mp hcentral)
  have hfin := (Reductive.CentralDerived.semisimpleIffFiniteCentre G hR Z hq.1).mp hG
  have hz := cocharacter_into_finite_is_zero (Specs.Unipotent.closedSubgroupAlgebraicGroup Z) hfin a
  rw [← ha, hz, zero_comp]

/-- A closed split one-dimensional torus supplies a noncentral
cocharacter of a semisimple group. -/
private theorem noClosedSplitTorus {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (hG : IsSemisimple G) (hanis : ¬ ∃ c : Cocharacter G.val, IsNoncentral c) :
    ¬ HasClosedSplitTorus G := by
  rintro ⟨f, hf⟩
  obtain ⟨e⟩ := multiplicative_group_iso (k := K)
  let c : Cocharacter G.val := e.hom ≫ f
  let F := Grp.forget (SchemeOver K) ⋙ Over.forget _
  haveI : Mono (F.map f) := by
    change Mono f.hom.hom.left
    letI := hf
    infer_instance
  haveI : Mono f := F.mono_of_mono_map (f := f) inferInstance
  haveI : Mono c := by dsimp only [c]; infer_instance
  apply hanis
  refine ⟨c, ?_⟩
  by_contra hc
  apply multiplicativeGroup_id_ne_zero K
  apply (cancel_mono c).mp
  rw [Category.id_comp, zero_comp, semisimpleCentralCocharacter_eq_zero hG c hc]


section ColumnRepresentation

open Matrix
open AnisotropicUnitaryTensors (Mat groundColumnAction extendedColumnAction extendedColumnAction_tmul)
open Specs.AnisotropicTensorQuotients (matrixOfUnits unitaryMatrixRepresentation)
open Specs.IntegralModels (MatrixRealization)
open Specs.OuterTypeAModels (RepresentsUnitary)
open Specs.StandardGroups (generalLinearPoints)
open Specs.Unipotent (Index)
open UnitaryNormEquations (SecondKind)
open _root_.Specs.RM03.CSA (isCentralSimple)

open private columnActionFaithful from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryTensors

variable {K E A B : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    [DivisionRing B] [Algebra K B] [Algebra E B] [IsScalarTower K E B]
    {r j : ℕ} {I : Type u} [Fintype I]

private def columnMatrices (e : A ≃ₐ[E] Mat r B)
    (b : Module.Basis (Index.{u} j) K (Fin r → B))
    (R : Type u) [CommRing R] [Algebra K R] :
    (R ⊗[K] A) →ₐ[R] Matrix (Index.{u} j) (Index.{u} j) R :=
  (LinearMap.toMatrixAlgEquiv (b.baseChange R)).toAlgHom.comp (extendedColumnAction e)

private theorem columnMatrices_tmul (e : A ≃ₐ[E] Mat r B)
    (b : Module.Basis (Index.{u} j) K (Fin r → B))
    {R : Type u} [CommRing R] [Algebra K R] (c : R) (a : A) :
    columnMatrices e b R (c ⊗ₜ[K] a) =
      c • (LinearMap.toMatrix b b (groundColumnAction e a)).map (algebraMap K R) := by
  ext l m
  simp only [columnMatrices, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply, Module.Basis.baseChange_apply,
    extendedColumnAction_tmul, mul_one, Module.Basis.baseChange_repr_tmul, Algebra.smul_def,
    Matrix.smul_apply, Matrix.map_apply]
  exact mul_comm _ _

private theorem columnMatrices_injective (e : A ≃ₐ[E] Mat r B)
    (b : Module.Basis (Index.{u} j) K (Fin r → B))
    (R : Type u) [CommRing R] [Algebra K R] :
    Function.Injective (columnMatrices e b R) := by
  let f : A →ₗ[K] Matrix (Index.{u} j) (Index.{u} j) K :=
    (LinearMap.toMatrix b b).toLinearMap.comp (groundColumnAction e).toLinearMap
  have hf : Function.Injective f := by
    intro a a' h
    apply columnActionFaithful e
    have hh := (LinearMap.toMatrix b b).injective h
    exact LinearMap.ext fun x => DFunLike.congr_fun hh x
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  let m := (matrixEquivTensor (Index.{u} j) K R).symm
  have he : (columnMatrices e b R).toLinearMap.restrictScalars K =
      m.toLinearMap.comp ((f.baseChange R).restrictScalars K) := by
    apply TensorProduct.ext
    ext t a l n
    change columnMatrices e b R (t ⊗ₜ[K] a) l n = m (f.baseChange R (t ⊗ₜ[K] a)) l n
    rw [columnMatrices_tmul, LinearMap.baseChange_tmul, matrixEquivTensor_apply_symm]
    rfl
  have hg' : (g.baseChange R).comp (f.baseChange R) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hg, LinearMap.baseChange_id]
  change Function.Injective ((columnMatrices e b R).toLinearMap.restrictScalars K)
  rw [he]
  refine m.injective.comp (Function.LeftInverse.injective (g := g.baseChange R) ?_)
  intro x
  exact LinearMap.congr_fun hg' x

private theorem columnMatrices_natural (e : A ≃ₐ[E] Mat r B)
    (b : Module.Basis (Index.{u} j) K (Fin r → B))
    {R S : Type u} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S] (f : R →ₐ[K] S)
    (x : R ⊗[K] A) :
    columnMatrices e b S (Algebra.TensorProduct.map f (.id K A) x) =
      (columnMatrices e b R x).map f := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [map_add, map_add, map_add, Matrix.map_add, hx, hy]
    exact map_add f
  | tmul c a =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, columnMatrices_tmul, columnMatrices_tmul]
    ext l m
    simp [Matrix.smul_apply, Matrix.map_apply, f.commutes]

private theorem unitaryMatrixRepresentation_eq (e : A ≃ₐ[E] Mat r B)
    (b : Module.Basis (Index.{u} j) K (Fin r → B))
    {L : Type u} [Field L] [Algebra K L] (x : (L ⊗[K] A)ˣ) :
    unitaryMatrixRepresentation e b x = Units.map (columnMatrices e b L).toMonoidHom x := by
  apply Units.ext
  rfl

set_option maxHeartbeats 650000 in
private theorem unitaryColumnRealization (e : A ≃ₐ[E] Mat r B)
    (v₀ : Module.Basis (Index.{u} j) K (Fin r → B))
    (hA : isCentralSimple E A) (b : Module.Basis I E A) (s : SecondKind K E A)
    (G : AffineAlgebraicGroup K) (hG : RepresentsUnitary hA b s G) :
    ∃ i : MatrixRealization G, ∃ h : i.size = j,
      ∀ (L : Type u) [Field L] [Algebra K L],
        Set.range (AdelicGroups.asMatrix i L) =
          {m | ∃ x : (L ⊗[K] A)ˣ, UnitaryNormEquations.IsSpecialUnitary hA b s x ∧
            unitaryMatrixRepresentation e v₀ x = h ▸ m} := by
  classical
  obtain ⟨point, hmul, hnatural⟩ := hG
  let F := (groupPointsFunctor K).obj G.val
  let H := StandardGroups.generalLinearGroup K (Index.{u} j)
  let E₀ := StandardGroups.generalLinearGroupPointsIso K (Index.{u} j)
  let rep (R : TestAlgebra K) : F.obj R →* (generalLinearPoints K (Index.{u} j)).obj R :=
    MonoidHom.mk' (fun x =>
      Units.map (columnMatrices e v₀ R).toMonoidHom (point R x).val) (by
      intro x y
      rw [hmul R x y, map_mul])
  have hrep (R : TestAlgebra K) : Function.Injective (rep R) := by
    intro x y he
    apply (point R).injective
    apply Subtype.ext
    apply Units.ext
    apply columnMatrices_injective e v₀ R
    exact congrArg (fun m : GL (Index.{u} j) R => m.val) he
  let α : F ⟶ generalLinearPoints K (Index.{u} j) :=
    { app := fun R => GrpCat.ofHom (rep R)
      naturality := by
        intro R S f
        apply GrpCat.ext
        intro x
        apply Units.ext
        change columnMatrices e v₀ S (point S (mapPoints f x)).val.val =
          (columnMatrices e v₀ R (point R x).val.val).map f.hom
        rw [hnatural]
        exact columnMatrices_natural e v₀ f.hom _ }
  obtain ⟨ρ, hρ⟩ := (LinearAlgebraicGroups.groupHomComparison K G.val H.val G.prop.1).2
    (α ≫ E₀.inv)
  have hρcoord (R : TestAlgebra K) (x : F.obj R) :
      E₀.hom.app R (x ≫ ρ.hom.hom) = rep R x := by
    have he := DFunLike.congr_fun (congrArg (fun n => (n.app R).hom) hρ) x
    change x ≫ ρ.hom.hom = E₀.inv.app R (rep R x) at he
    rw [he]
    exact GrpCat.hom_inv_apply (E₀.app R) (rep R x)
  have hρclosed : IsClosedImmersion ρ.hom.hom.left :=
    RootData.RootGroups.isClosedImmersion_of_injectivePoints G H ρ (fun R x y hxy =>
      hrep R ((hρcoord R x).symm.trans ((congrArg (E₀.hom.app R) hxy).trans (hρcoord R y))))
  let i : MatrixRealization G := ⟨j, H, E₀, ρ, hρclosed⟩
  refine ⟨i, rfl, fun L _ _ => Set.ext fun m => ?_⟩
  change (∃ x : AdelicGroups.PointsIn i L, AdelicGroups.asMatrix i L x = m) ↔ _
  have hmatrix (x : AdelicGroups.PointsIn i L) :
      AdelicGroups.asMatrix i L x = rep (CommAlgCat.of K L) x := hρcoord _ x
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(point _ x).val, (point _ x).property,
      (unitaryMatrixRepresentation_eq e v₀ _).trans (hmatrix x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    let g := (point (CommAlgCat.of K L)).symm ⟨x, hx⟩
    refine ⟨g, (hmatrix g).trans ?_⟩
    change Units.map (columnMatrices e v₀ L).toMonoidHom (point _ g).val =
      unitaryMatrixRepresentation e v₀ x
    have hg : (point (CommAlgCat.of K L) g).val = x :=
      congrArg Subtype.val ((point (CommAlgCat.of K L)).apply_symm_apply ⟨x, hx⟩)
    rw [hg]
    exact (unitaryMatrixRepresentation_eq e v₀ x).symm

end ColumnRepresentation

section MatrixAdeles

open Filter Matrix
open AdelicGroups (Adeles LocalPoints Outside asMatrix)
open Specs.IntegralModels (MatrixRealization)
open Specs.Unipotent (Index)
open Specs.AnisotropicTensorQuotients (MatrixModel localConditions GlobalMatrixQuotientCompact)
open TensorAdelicReduction (integralMatrices)
open private MatrixAdeles matrixAt continuous_matrixAt adelicMatrixGroup mem_localConditions
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicTensorQuotients
open private restrictedReindex from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TensorAdelicReduction
open private glIntegral_compactOpen from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K}

private abbrev CompletionMatrices (D : GlobalFieldData.{u,v} K) (j : ℕ) (w : D.Place) :=
  GL (Index.{u} j) (D.Completion w)

private abbrev completionMatrixTopology (D : GlobalFieldData.{u,v} K) (j : ℕ) (w : D.Place) :
    TopologicalSpace (CompletionMatrices D j w) := inferInstance

private def integralMatrixFactor (D : GlobalFieldData.{u,v} K) (j : ℕ) (w : D.Place) :
    Subgroup (GL (Index.{u} j) (D.Completion w)) :=
  match w with
  | .inl w => integralMatrices (D.integers w).toSubring
  | .inr _ => ⊤

private theorem integralMatrixFactor_open (D : GlobalFieldData.{u,v} K) (j : ℕ) (w : D.Place) :
    IsOpen (integralMatrixFactor D j w : Set (GL (Index.{u} j) (D.Completion w))) := by
  cases w with
  | inl w =>
    obtain ⟨hc, ho, _⟩ := D.integers_properties w
    exact (@glIntegral_compactOpen _ (Index.{u} j) _ _ _ _ _ _ (D.integers w) hc ho).2
  | inr w => exact isOpen_univ

private abbrev RestrictedMatrices (D : GlobalFieldData.{u,v} K) (j : ℕ) :=
  Πʳ w : D.Place, [GL (Index.{u} j) (D.Completion w), integralMatrixFactor D j w]

set_option synthInstance.maxHeartbeats 70000 in
set_option maxHeartbeats 450000 in
private theorem matrixAdelesCoordinates (D : GlobalFieldData.{u,v} K) (j : ℕ) :
    ∃ e : MatrixAdeles D (Index.{u} j) ≃ₜ RestrictedMatrices D j,
      ∀ x w, e x w = matrixAt D w x := by
  classical
  cases D with
  | function C t =>
    let D := GlobalFieldData.function C t
    let e : D.FinitePlace ≃ D.Place := (Equiv.sumEmpty D.FinitePlace D.InfinitePlace).symm
    letI (w : D.Place) : TopologicalSpace (CompletionMatrices D j w) :=
      completionMatrixTopology D j w
    letI (w : D.FinitePlace) : TopologicalSpace (CompletionMatrices D j (.inl w)) :=
      completionMatrixTopology D j (.inl w)
    obtain ⟨h, hh⟩ := restrictedReindex
      (A := fun w : D.FinitePlace => CompletionMatrices D j (.inl w))
      (B := CompletionMatrices D j)
      e (fun _ => Homeomorph.refl _)
      (fun w : D.FinitePlace =>
        (integralMatrixFactor D j (.inl w) : Set (CompletionMatrices D j (.inl w))))
      (fun w => (integralMatrixFactor D j w : Set _)) (fun _ _ => Iff.rfl)
    refine ⟨h.symm, ?_⟩
    intro x w
    cases w with
    | inl w => exact (hh (h.symm x) w).symm.trans (by rw [h.apply_symm_apply]; rfl)
    | inr w => exact w.elim
  | number hK =>
    letI := hK
    let D : GlobalFieldData.{u,v} K := .number hK
    let F := D.FinitePlace
    let A := D.InfinitePlace
    let T : Set D.Place := Set.range (Sum.inl : F → F ⊕ A)
    letI (w : D.Place) : TopologicalSpace (CompletionMatrices D j w) :=
      completionMatrixTopology D j w
    letI (w : F) : TopologicalSpace (CompletionMatrices D j (.inl w)) :=
      completionMatrixTopology D j (.inl w)
    letI (w : T) : TopologicalSpace (CompletionMatrices D j w.1) :=
      completionMatrixTopology D j w.1
    letI (w : ↑Tᶜ) : TopologicalSpace (CompletionMatrices D j w.1) :=
      completionMatrixTopology D j w.1
    let ef : F ≃ T := Equiv.ofInjective _ Sum.inl_injective
    let ea : A ≃ ↑Tᶜ := Equiv.ofBijective
      (fun w => (⟨Sum.inr w, by rintro ⟨_, h⟩; cases h⟩ : ↑Tᶜ)) (by
        constructor
        · intro w w' hh
          exact Sum.inr_injective (congrArg Subtype.val hh)
        · rintro ⟨w, hw⟩
          cases w with
          | inl w => exact (hw ⟨w, rfl⟩).elim
          | inr w => exact ⟨w, rfl⟩)
    letI : Finite ↑Tᶜ := Finite.of_equiv A ea
    have hT : Tᶜ.Finite := Set.toFinite _
    obtain ⟨h, hf, ha⟩ := TensorAdelicReduction.restrictedProductSplit
      (fun w => (integralMatrixFactor D j w : Set (CompletionMatrices D j w))) T hT (integralMatrixFactor_open D j)
    obtain ⟨f, hf'⟩ := restrictedReindex
      (A := fun w : F => CompletionMatrices D j (.inl w))
      (B := fun w : T => CompletionMatrices D j w.1)
      ef (fun _ => Homeomorph.refl _)
      (fun w : F => (integralMatrixFactor D j (.inl w) : Set _))
      (fun w : T => (integralMatrixFactor D j w.1 : Set _)) (by intros; rfl)
    let a := Homeomorph.piCongrLeft (Y := fun w : ↑Tᶜ => CompletionMatrices D j w.1) ea
    let m := h.trans (f.prodCongr a.symm)
    refine ⟨m.symm, ?_⟩
    intro x w
    have hx : m (m.symm x) = x := m.apply_symm_apply x
    cases w with
    | inl w =>
      have hs := congrArg (fun z => z.1 w) hx
      change f (h (m.symm x)).1 w = x.1 w at hs
      rw [hf'] at hs
      exact (hf (m.symm x) (ef w)).symm.trans hs
    | inr w =>
      have hs := congrArg (fun z => z.2 w) hx
      change (h (m.symm x)).2 (ea w) = x.2 w at hs
      exact (ha (m.symm x) (ea w)).symm.trans hs

open AdelicGroups (localSubgroup localPoint)
open Specs.IntegralModels (RationalPoints)
open ArithmeticLatticeProjection (diagonalSubgroup)
open Specs.AnisotropicTensorQuotients (CompactMatrixQuotient)

private theorem compactQuotientOfSurjection {P Q : Type*} [Group P] [Group Q]
    [TopologicalSpace P] [TopologicalSpace Q] (f : P →* Q)
    (hf : Continuous f) (hs : Function.Surjective f) (H : Subgroup P) (J : Subgroup Q)
    (hHJ : H ≤ J.comap f) (hc : CompactSpace (P ⧸ H)) :
    CompactSpace (Q ⧸ J) := by
  letI := hc
  let F : P ⧸ H → Q ⧸ J := Quotient.map' f (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [← map_inv, ← map_mul]
    exact hHJ hab)
  have hF : Continuous F :=
    (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp hf)
  have hsurj : Function.Surjective F := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨QuotientGroup.mk x, rfl⟩
  exact ⟨(Set.range_eq_univ.mpr hsurj) ▸ isCompact_range hF⟩

private theorem matrixMemIntegral_iff (D : GlobalFieldData.{u,v} K)
    (i : MatrixRealization G) (w : D.Place) (x : LocalPoints D i w) :
    asMatrix i (D.Completion w) x ∈ integralMatrixFactor D i.size w ↔
      x ∈ localSubgroup D i w := by
  cases w with
  | inl w => rfl
  | inr w =>
    change _ ∈ (⊤ : Subgroup _) ↔ x ∈ (⊤ : Subgroup _)
    simp

private theorem matrixModelQuotientTransfer (D : GlobalFieldData.{u,v} K)
    (i : MatrixRealization G) (M : MatrixModel K (Index.{u} i.size))
    (hbase : Set.range i.onPoints = (M K (RingHom.id K) : Set _))
    (hlocal : ∀ w : D.Place, Set.range (asMatrix i (D.Completion w)) =
      (M (D.Completion w) (D.embedding w) : Set _))
    (δ : GL (Index.{u} i.size) K →* MatrixAdeles D (Index.{u} i.size))
    (hδ : ∀ r w, matrixAt D w (δ r) = GeneralLinearGroup.map (D.embedding w) r)
    (hQ : CompactMatrixQuotient (adelicMatrixGroup D M) (M K (RingHom.id K)) δ) :
    CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) := by
  classical
  obtain ⟨e, he⟩ := matrixAdelesCoordinates D i.size
  let P := adelicMatrixGroup D M
  have hmem (x : P) (w : D.Place) :
      matrixAt D w x.val ∈ Set.range (asMatrix i (D.Completion w)) := by
    rw [hlocal]
    exact (mem_localConditions _ _ _).mp x.property w
  let point (x : P) (w : D.Place) : LocalPoints D i w :=
    (MonoidHom.ofInjective (AdelicGroups.localMatrixEmbedding D i w).injective).symm
      ⟨matrixAt D w x.val, hmem x w⟩
  have hpoint (x : P) (w : D.Place) :
      asMatrix i (D.Completion w) (point x w) = matrixAt D w x.val := by
    exact congrArg Subtype.val
      ((MonoidHom.ofInjective (AdelicGroups.localMatrixEmbedding D i w).injective).apply_symm_apply
        ⟨matrixAt D w x.val, hmem x w⟩)
  have point_continuous (w : D.Place) : Continuous (fun x : P => point x w) := by
    apply (AdelicGroups.localMatrixEmbedding D i w).isEmbedding.continuous_iff.mpr
    change Continuous (fun x : P => asMatrix i (D.Completion w) (point x w))
    simp_rw [hpoint]
    exact (continuous_matrixAt (I := Index.{u} i.size) D w).comp continuous_subtype_val
  let f : P →* Adeles D i ∅ :=
    MonoidHom.mk' (fun x =>
      ⟨fun w => point x w.1, by
        have ht : Tendsto (fun w : Outside D ∅ => w.val) cofinite cofinite :=
          Subtype.val_injective.tendsto_cofinite
        have hx := ht.eventually
          ((e x.val).eventually :
            ∀ᶠ w : D.Place in cofinite, e x.val w ∈ integralMatrixFactor D i.size w)
        refine hx.mono (fun w hw => (matrixMemIntegral_iff D i w.1 _).1 ?_)
        rw [hpoint, ← he]
        exact hw⟩) (by
      intro x y
      apply RestrictedProduct.ext
      intro w
      apply (AdelicGroups.localMatrixEmbedding D i w.1).injective
      change asMatrix i (D.Completion w.1) (point (x * y) w.1) =
        asMatrix i (D.Completion w.1) (point x w.1 * point y w.1)
      rw [map_mul, hpoint, hpoint, hpoint]
      exact map_mul (matrixAt D w.1) _ _)
  have hf (x : P) (w : Outside D ∅) : f x w = point x w.1 := rfl
  have hcont : Continuous f := by
    apply (AdelicGroups.adelicBasis D i ∅).continuous_iff.mpr
    rintro U ⟨T, V, hV, heq, rfl⟩
    let W : Set D.Place := Subtype.val '' (↑T : Set (Outside D ∅))
    have hO : IsOpen
        {a : RestrictedMatrices D i.size | ∀ w, w ∉ W → a w ∈ integralMatrixFactor D i.size w} :=
      RestrictedProduct.isOpen_forall_imp_mem (integralMatrixFactor_open D i.size)
    have hpre : f ⁻¹' AdelicGroups.box D i ∅ V =
        {x : P | ∀ w ∈ T, point x w.1 ∈ V w} ∩ (e ∘ Subtype.val) ⁻¹'
          {a : RestrictedMatrices D i.size | ∀ w, w ∉ W → a w ∈ integralMatrixFactor D i.size w} := by
      ext x
      change (∀ w, point x w.1 ∈ V w) ↔
        (∀ w ∈ T, point x w.1 ∈ V w) ∧
          (∀ w, w ∉ W → e x.val w ∈ integralMatrixFactor D i.size w)
      have hW (w : Outside D ∅) : w.val ∈ W ↔ w ∈ T := by
        exact Subtype.val_injective.mem_set_image
      constructor
      · intro hx
        refine ⟨fun w _ => hx w, fun w hw => ?_⟩
        let w' : Outside D ∅ := ⟨w, Finset.notMem_empty _⟩
        have hnot : w' ∉ T := fun h => hw ((hW w').mpr h)
        have h := hx w'
        rw [heq w' hnot] at h
        rw [he, ← hpoint]
        exact (matrixMemIntegral_iff D i w _).2 h
      · rintro ⟨h₁, h₂⟩ w
        by_cases hw : w ∈ T
        · exact h₁ w hw
        · rw [heq w hw]
          have hm := h₂ w.1 (fun h => hw ((hW w).mp h))
          rw [he, ← hpoint] at hm
          exact (matrixMemIntegral_iff D i w.1 _).1 hm
    rw [hpre]
    refine IsOpen.inter ?_ (hO.preimage (e.continuous.comp continuous_subtype_val))
    have he₁ : {x : P | ∀ w ∈ T, point x w.1 ∈ V w} =
        ⋂ w : T, (fun x : P => point x w.1.1) ⁻¹' V w.1 := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
      exact ⟨fun hx w => hx w.1 w.2, fun hx w hw => hx ⟨w, hw⟩⟩
    rw [he₁]
    exact isOpen_iInter_of_finite (fun w : T => (hV w.1).preimage (point_continuous w.1.1))
  have hs : Function.Surjective f := by
    intro x
    let wi (w : D.Place) : Outside D ∅ := ⟨w, Finset.notMem_empty _⟩
    let a : RestrictedMatrices D i.size :=
      ⟨fun w => asMatrix i (D.Completion w) (x (wi w)), by
        have hwi : Function.Injective wi := fun _ _ h => congrArg Subtype.val h
        have ht : Tendsto wi cofinite cofinite := hwi.tendsto_cofinite
        have ha := ht.eventually x.eventually
        exact ha.mono (fun w hw => (matrixMemIntegral_iff D i w _).2 hw)⟩
    let g := e.symm a
    have hg (w : D.Place) : matrixAt D w g = a w := by
      rw [← he, show e g = a from e.apply_symm_apply a]
    have hPg : g ∈ P := by
      apply (mem_localConditions _ _ _).mpr
      intro w
      rw [hg]
      change a w ∈ (M (D.Completion w) (D.embedding w) : Set _)
      rw [← hlocal w]
      exact ⟨x (wi w), rfl⟩
    refine ⟨⟨g, hPg⟩, RestrictedProduct.ext _ _ (fun w => ?_)⟩
    apply (AdelicGroups.localMatrixEmbedding D i w.1).injective
    rw [hf, hpoint]
    exact hg w.1
  refine compactQuotientOfSurjection f hcont hs _ (diagonalSubgroup D i) ?_ hQ.2
  rintro x hx
  change x.val ∈ (M K (RingHom.id K)).map δ at hx
  obtain ⟨r, hr, hxr⟩ := hx
  change r ∈ (M K (RingHom.id K) : Set _) at hr
  rw [← hbase] at hr
  obtain ⟨g, rfl⟩ := hr
  refine ⟨g, fun w => ?_⟩
  apply (AdelicGroups.localMatrixEmbedding D i w.1).injective
  rw [hf, hpoint, ← hxr, hδ, AdelicGroups.localPoint_matrix]

open Specs.AnisotropicTensorQuotients (numberAtPlace functionAtPlace)

private theorem matrixQuotientCompactWitness (D : GlobalFieldData.{u,v} K) (j : ℕ)
    (M : MatrixModel K (Index.{u} j)) (hc : GlobalMatrixQuotientCompact D M) :
    ∃ δ : GL (Index.{u} j) K →* MatrixAdeles D (Index.{u} j),
      (∀ r w, matrixAt D w (δ r) = GeneralLinearGroup.map (D.embedding w) r) ∧
      CompactMatrixQuotient (adelicMatrixGroup D M) (M K (RingHom.id K)) δ := by
  cases D with
  | number h =>
    letI := h
    obtain ⟨δ, hδ, hQ⟩ := hc
    let D : GlobalFieldData.{u,v} K := .number h
    have he : adelicMatrixGroup D M =
        localConditions numberAtPlace (fun (w : NumberPlace K) => M w.Completion w.embedding) := by
      ext x
      simp only [adelicMatrixGroup, mem_localConditions]
      constructor <;> intro hx w <;> cases w
      · exact hx (.inl _)
      · exact hx (.inr _)
      · exact hx (.inl _)
      · exact hx (.inr _)
    refine ⟨δ, fun r w => ?_, he.symm ▸ hQ⟩
    cases w with
    | inl w => exact hδ r (.inl w)
    | inr w => exact hδ r (.inr w)
  | function C t =>
    obtain ⟨δ, hδ, hQ⟩ := hc
    let D : GlobalFieldData.{u,v} K := .function C t
    have he : adelicMatrixGroup D M =
        localConditions functionAtPlace (fun (w : FunctionPlace K) => M w.Completion w.embedding) := by
      ext x
      simp only [adelicMatrixGroup, mem_localConditions]
      exact ⟨fun h w => h (.inl w), fun h w => by
        cases w with
        | inl w => exact h w
        | inr w => exact w.elim⟩
    refine ⟨δ, fun r w => ?_, he.symm ▸ hQ⟩
    cases w with
    | inl w => exact hδ r w
    | inr w => exact w.elim

private theorem compactnessChangeRealization (D : GlobalFieldData.{u,v} K)
    (i j : MatrixRealization G) (h : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i)) :
    CompactSpace (Adeles D j ∅ ⧸ diagonalSubgroup D j) := by
  let e := AdelicGroups.changeRealization D i j ∅
  apply compactQuotientOfSurjection e.toMonoidHom e.continuous e.surjective _ _ _ h
  rintro x ⟨g, hg⟩
  exact ⟨g, fun w => hg w⟩

end MatrixAdeles
open Matrix
open Specs.IntegralModels (MatrixRealization)
open Specs.OuterTypeAModels (RepresentsUnitary)
open Specs.AnisotropicTensorQuotients (unitaryMatrixRepresentation)
open UnitaryNormEquations (SecondKind)
open _root_.Specs.RM03.CSA (isCentralSimple degree)
open ArithmeticLatticeProjection (diagonalSubgroup)

set_option maxHeartbeats 550000 in
/-- Compactness of the full adelic quotient in every closed realization of
the original globally anisotropic special unitary scheme. -/
theorem compactUnitaryAdelicQuotient {K E A : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) [Field E] [Algebra K E] [Algebra.IsSeparable K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    (hKE : Module.finrank K E = 2)
    {I : Type u} [Fintype I] (hA : isCentralSimple E A) (hn : 3 ≤ degree E A)
    (b : Module.Basis I E A) (s : SecondKind K E A) (G : AffineAlgebraicGroup K)
    (hG : IsSemisimple G) (hanis : ¬ ∃ c : Cocharacter G.val, IsNoncentral c)
    (hunitary : RepresentsUnitary hA b s G) (i : MatrixRealization G) :
    CompactSpace (AdelicGroups.Adeles D i ∅ ⧸ diagonalSubgroup D i) := by
  obtain ⟨r, B, hB, hBE, _, e, x, p, l, τ, H, _, _, _, j, bV, M, hM, hc⟩ :=
    AnisotropicTensorQuotients.unitaryCompactness D hKE hA hn b s G hunitary
      (noClosedSplitTorus hG hanis)
  letI : DivisionRing B := hB
  letI : Algebra E B := hBE
  letI : Algebra K B := Algebra.compHom B (algebraMap K E)
  letI : IsScalarTower K E B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨j₀, hj, hrep⟩ := unitaryColumnRealization e bV hA b s G hunitary
  subst j
  have heq (L : Type u) [Field L] (a : K →+* L) :
      letI : Algebra K L := a.toAlgebra
      Set.range (AdelicGroups.asMatrix j₀ L) = (M L a : Set _) := by
    letI : Algebra K L := a.toAlgebra
    rw [hrep L]
    exact Set.ext fun g => ((hM L a).2 g).symm
  obtain ⟨δ, hδ, hQ⟩ := matrixQuotientCompactWitness D j₀.size M hc
  apply compactnessChangeRealization D j₀ i
  apply matrixModelQuotientTransfer D j₀ M _ (fun w => heq _ (D.embedding w)) δ hδ hQ
  exact heq K (RingHom.id K)


section LocalProjection

open Filter
open scoped Classical

open Specs.Arithmetic.LocalProjectedClosure (FiniteCovolumeSubgroup)

open MeasureTheory Topology
open ArithmeticLatticeProjection (FiniteInvariantQuotientMeasure)
open LocalQuotientTransport (RightCosets RightInvariant coset rightTranslate imageSubgroup)

/-- Inversion takes the invariant measure on `P ⧸ H` to a right-invariant
measure on `H ∖ P`. -/
private theorem rightInvariantMeasureOfFiniteQuotient {P : Type u} [Group P]
    [TopologicalSpace P] [IsTopologicalGroup P] (H : Subgroup P)
    (h : FiniteInvariantQuotientMeasure H) :
    ∃ ν : Measure (RightCosets H), IsFiniteMeasure ν ∧ ν ≠ 0 ∧ RightInvariant ν := by
  unfold FiniteInvariantQuotientMeasure at h
  borelize (P ⧸ H)
  obtain ⟨ν, hfin, hpos, hinv⟩ := h
  let q : P ⧸ H → RightCosets H := Quotient.map' Inv.inv (by
    intro x y hxy
    rw [QuotientGroup.rightRel_apply, inv_inv]
    simpa only [_root_.mul_inv_rev, inv_inv] using H.inv_mem (QuotientGroup.leftRel_apply.mp hxy))
  have hq : Continuous q := continuous_quot_map _ continuous_inv
  have hμ : ν ≠ 0 := by
    intro hz
    have hpos' : 0 < ν Set.univ := isOpen_univ.measure_pos ν Set.univ_nonempty
    simp [hz] at hpos'
  refine ⟨ν.map q, inferInstance, (Measure.map_ne_zero_iff hq.measurable.aemeasurable).mpr hμ, ?_⟩
  intro a
  have ha : Measurable (rightTranslate (H := H) a) :=
    ((LocalQuotientTransport.quotient_action H).2.2.comp
      (continuous_id.prodMk continuous_const)).measurable
  have hsmul : Measurable (a⁻¹ • · : P ⧸ H → P ⧸ H) :=
    (continuous_const_smul _).measurable
  have he : rightTranslate a ∘ q = q ∘ (a⁻¹ • ·) := by
    funext z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    change coset H (g⁻¹ * a) = coset H ((a⁻¹ * g)⁻¹)
    rw [_root_.mul_inv_rev, inv_inv]
  refine ⟨ha, ?_⟩
  rw [Measure.map_map ha hq.measurable, he, ← Measure.map_map hq.measurable hsmul]
  congr 1
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hsmul hs, measure_preimage_smul ν a⁻¹ s]

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.Arithmetic.LocalQuotientMixing (MixingCases)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open LocalAlgebraicTransport (pointTopology)
local notation "AffinePoints" => LocalAlgebraicTransport.RationalPoints

/-- Apply the conditional finite-covolume input under a topological group
comparison with the original affine points over the local field. -/
private theorem fullProjectionOfLocalModel (hfull : FiniteCovolumeSubgroup.{u})
    {F P : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    (J : AffineAlgebraicGroup F) (hJ : IsAbsolutelyAlmostSimple J) (hmix : MixingCases J)
    (H : Subgroup P) (hclosed : IsClosed (H : Set P)) (hnd : ¬ DiscreteTopology H)
    (hμ : FiniteInvariantQuotientMeasure H) :
    letI := pointTopology J.val.X
    IsTopologicalGroup (AffinePoints J.val.X) →
    (P ≃ₜ* AffinePoints J.val.X) → H = ⊤ := by
  let _ := pointTopology J.val.X
  intro htop e
  let : IsTopologicalGroup (AffinePoints J.val.X) := htop
  obtain ⟨ν, hfin, hpos, hinv⟩ := rightInvariantMeasureOfFiniteQuotient H hμ
  have := hfin
  obtain ⟨hm, hc, hd⟩ := LocalQuotientTransport.subgroup_transport e H
  obtain ⟨q, _, hq⟩ := LocalQuotientTransport.quotient_transport e H
  obtain ⟨hfin', hpos', hinv', _⟩ :=
    LocalQuotientTransport.measure_transport e q hq ν hinv hpos
  have := hfin'
  have he := hfull F J hJ hmix (imageSubgroup e H) (hc.mp hclosed) (hnd ∘ hd.mpr)
    (ν.map q) hpos' hinv'
  apply top_unique
  intro x _
  exact (hm x).mp (he ▸ Subgroup.mem_top (e x))

open AdelicGroups (Adeles LocalPoints Outside StrongApproximation localSubgroup)
open ArithmeticLatticeProjection (FinitePoints diagonalSubgroup lattice forgetPlaces)
open CompactProductIsolation (Contracted insertFinite diagonalClosure projectedArithmetic)
open Specs.IntegralModels (MatrixRealization)

/-- The projected arithmetic subgroup is dense if its nondiscrete closed
finite-covolume closure is the whole product. The contraction argument then
embeds every element of the product in the adelic diagonal closure. -/
private theorem isolateFactorsOfFullProjection {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (S J : Finset D.Place) (hJ : J.Nonempty) (hd : Disjoint J S)
    (U : Subgroup (Adeles D i (S ∪ J)))
    (hU : IsCompact (U : Set (Adeles D i (S ∪ J))))
    (hU' : IsOpen (U : Set (Adeles D i (S ∪ J))))
    (hcompact : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hnoncompact : ¬ CompactSpace (FinitePoints D i S))
    (hfull : ∀ H : Subgroup (FinitePoints D i J),
      IsClosed (H : Set (FinitePoints D i J)) → ¬ DiscreteTopology H →
      FiniteInvariantQuotientMeasure H → H = ⊤)
    (hcontract : Dense (Subgroup.closure {x : FinitePoints D i J | Contracted x} :
      Set (FinitePoints D i J))) :
    ∀ x : FinitePoints D i J, insertFinite D i S J x ∈ diagonalClosure D i S := by
  obtain ⟨hnd, H, hH, _, hμ⟩ := ArithmeticLatticeProjection.projectionProperties
    D i S (S ∪ J) J U Finset.subset_union_left Finset.subset_union_right
    hcompact hnoncompact hJ hd hU hU'
  have hclosed : IsClosed (H : Set (FinitePoints D i J)) := by rw [hH]; exact isClosed_closure
  have hnd' : ¬ DiscreteTopology H := by
    intro h
    apply hnd
    have hi : (projectedArithmetic D i S J U : Set (FinitePoints D i J)) ⊆ H := by
      rw [hH]
      exact subset_closure
    exact (isDiscrete_iff_discreteTopology.mpr h).mono hi
  have htop := hfull H hclosed hnd' hμ
  have hP : Dense (projectedArithmetic D i S J U : Set (FinitePoints D i J)) := by
    rw [dense_iff_closure_eq]
    calc
      _ = (H : Set (FinitePoints D i J)) := hH.symm
      _ = Set.univ := by rw [htop, Subgroup.coe_top]
  exact (CompactProductIsolation.isolateAdelicFactors D i S J hd U hU hU').2 hP hcontract

/-- With compact archimedean factors outside the omitted set, singleton
arithmetic projections suffice away from a finite set of exceptions. -/
private theorem strongApproximationOfLocalProjections {K : Type u} [Field K]
    {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (S J : Finset D.Place) (hd : Disjoint J S)
    (harch : ∀ w : D.InfinitePlace, Sum.inr w ∉ S → CompactSpace (LocalPoints D i (.inr w)))
    (hcompact : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hnoncompact : ¬ CompactSpace (FinitePoints D i S))
    (hfull : ∀ w : Outside D S, w.1 ∉ J → ∀ H : Subgroup (FinitePoints D i {w.1}),
      IsClosed (H : Set (FinitePoints D i {w.1})) → ¬ DiscreteTopology H →
      FiniteInvariantQuotientMeasure H → H = ⊤)
    (hcontract : ∀ w : Outside D S, w.1 ∉ J →
      Dense (Subgroup.closure {x : FinitePoints D i {w.1} | Contracted x} :
        Set (FinitePoints D i {w.1})))
    (hrem : DenseRange (ArithmeticLatticeProjection.rationalProjection D i J)) :
    StrongApproximation D i S := by
  have hsingle (w : Outside D S) (hw : w.1 ∉ J) (a : LocalPoints D i w.1) :
      RestrictedProduct.mulSingle (fun k : Outside D S => localSubgroup D i k.1) w a ∈
        diagonalClosure D i S := by
    let T : Finset D.Place := {w.1}
    have hT : Disjoint T S := by simpa [T] using w.2
    let U := ArithmeticLatticeProjection.integralOutside D i (S ∪ T)
    obtain ⟨hUc, hUo⟩ := ArithmeticLatticeProjection.compactOpenOutside D i (S ∪ T)
      fun x hx => harch x (fun hx' => hx (Finset.mem_union_left _ hx'))
    have hins := isolateFactorsOfFullProjection D i S T ⟨w.1, Finset.mem_singleton_self _⟩
      hT U hUc hUo hcompact hnoncompact (hfull w hw) (hcontract w hw)
    obtain ⟨x, hx⟩ := CompactProductIsolation.mulSingle_mem_range_insertFinite D i hT w
      (Finset.mem_singleton_self _) a
    exact hx ▸ hins x
  exact ((CompactProductIsolation.projectToRemainingPlaces D i S J hd).2 hsingle).2.2.mp hrem

open Filter

set_option backward.isDefEq.respectTransparency false in
/-- A singleton subproduct of completions is the original local point group. -/
private def singletonLocalPoints {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.Place) :
    FinitePoints D i {w} ≃ₜ* LocalPoints D i w := by
  let w₀ : (↑({w} : Finset D.Place) : Set D.Place) := ⟨w, Finset.mem_singleton_self _⟩
  letI : Unique (↑({w} : Finset D.Place) : Set D.Place) :=
    ⟨⟨w₀⟩, fun x => Subtype.ext (Finset.mem_singleton.mp x.property)⟩
  let A := fun x : (↑({w} : Finset D.Place) : Set D.Place) => LocalPoints D i x.1
  let e := MulEquiv.piUnique A
  let h := Homeomorph.piUnique A
  exact { toMulEquiv := e, continuous_toFun := h.continuous, continuous_invFun := h.symm.continuous }

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct
open Specs.Unipotent (Index baseChangedAlgebraicGroup)

open private coordinateMap coordinateMap_spec from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
open private glEvaluation glEvaluation_entry from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private matrixPresentation glVal_isEmbedding continuous_glEvaluation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
open Specs.StandardGroups (GLCoordinates universalMatrix)
open LocalAlgebraicTransport (evaluation)
open AdelicGroups (PointsIn asMatrix localPoint)
open Opposite

set_option backward.isDefEq.respectTransparency false in
private theorem localPointTopology_eq_matrixTopology {F : Type u} [Field F]
    [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (J : AffineAlgebraicGroup F) (j : MatrixRealization J) :
    pointTopology J.val.X = (inferInstance : TopologicalSpace (PointsIn j F)) := by
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr J.prop.1
  let coords : Γ(J.val.X.left, ⊤) ⟶ CommRingCat.of A.unop :=
    e.hom.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A.unop)).hom
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have hg : Function.Surjective coords := ConcreteCategory.bijective_of_isIso coords |>.2
  let evalAt (p : AffinePoints J.val.X) := (coordinateMap (p ≫ e.inv)).hom
  have heval (p : AffinePoints J.val.X) (a : Γ(J.val.X.left, ⊤)) :
      evaluation p a = evalAt p (coords a) := by
    let f := coordinateMap (p ≫ e.inv)
    have hf := congrArg Over.Hom.left (coordinateMap_spec (p ≫ e.inv))
    rw [algSpec_map_left] at hf
    have hp : (p ≫ e.inv) ≫ e.hom = p := by simp
    have hcomp : e.hom.left.appTop ≫ (p ≫ e.inv).left.appTop = p.left.appTop := by
      rw [← Scheme.Hom.comp_appTop]
      exact congrArg (fun m => m.left.appTop) hp
    change Spec.map (CommRingCat.ofHom f.hom.toRingHom) = (p ≫ e.inv).left at hf
    change (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom) a = f.hom (coords a)
    rw [← hcomp, Category.assoc, ← hf, Scheme.ΓSpecIso_naturality]
    rfl
  obtain ⟨d, hsurj, hd⟩ := matrixPresentation A.unop e j
  let mat := fun p : PointsIn j F => (asMatrix j F p).val
  have hm : IsInducing mat := glVal_isEmbedding.isInducing.comp (IsInducing.induced (asMatrix j F))
  apply le_antisymm
  · rw [hm.eq_induced]
    apply continuous_iff_le_induced.mp
    let _ := pointTopology J.val.X
    apply continuous_matrix
    intro k l
    let z := universalMatrix F (Index.{u} j.size) k l
    obtain ⟨b, hb⟩ := hg (d.hom z)
    have h (p : AffinePoints J.val.X) : (mat p) k l = evaluation p b := by
      rw [heval, hb]
      have hc := congrArg (fun f : GLCoordinates F (Index.{u} j.size) →ₐ[F] F => f z) (hd F p)
      exact (glEvaluation_entry (asMatrix j F p) k l).symm.trans hc
    simp_rw [h]
    exact (continuous_apply b).comp continuous_induced_dom
  · apply continuous_iff_le_induced.mp
    apply continuous_pi
    intro a
    simp_rw [heval]
    obtain ⟨z, hz⟩ := hsurj (coords a)
    have he (p : PointsIn j F) : evalAt p (coords a) = glEvaluation (asMatrix j F p) z := by
      rw [← hz]
      exact congrArg (fun f : GLCoordinates F (Index.{u} j.size) →ₐ[F] F => f z) (hd F p).symm
    simp_rw [he]
    exact (continuous_glEvaluation (R := F) z).comp (IsInducing.induced (asMatrix j F)).continuous


private theorem completionMatrixComparison {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.Place) :
    ∃ j : MatrixRealization (baseChangedAlgebraicGroup (D.Completion w) G),
      Nonempty (PointsIn j (D.Completion w) ≃ₜ* LocalPoints D i w) := by
  let F := D.Completion w
  obtain ⟨j, hj⟩ := LocalCocharacterEvaluation.completionPointTopology (F := F) G i
  let e : PointsIn j F ≃* LocalPoints D i w :=
    baseChangePointGroupEquiv F G.val (CommAlgCat.of F F)
  let l : PointsIn j F ≃ₜ LocalPoints D i w := hj.homeomorph _
  refine ⟨j, ⟨{
    toMulEquiv := e
    continuous_toFun := l.continuous
    continuous_invFun := ?_ }⟩⟩
  have he : (e.symm : LocalPoints D i w → PointsIn j F) = l.symm := by
    funext x
    apply e.injective
    exact (e.apply_symm_apply x).trans (l.apply_symm_apply x).symm
  change Continuous (e.symm : LocalPoints D i w → PointsIn j F)
  rw [he]
  exact l.symm.continuous

/-- The two point topologies used by the arithmetic and local quotient
theorems give a topological group identification over the actual completion. -/
private theorem completionPointsComparison {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.Place) :
    let J := baseChangedAlgebraicGroup (D.Completion w) G
    letI := pointTopology J.val.X
    Nonempty (LocalPoints D i w ≃ₜ* AffinePoints J.val.X) := by
  let F := D.Completion w
  let J := baseChangedAlgebraicGroup F G
  obtain ⟨j, ⟨d⟩⟩ := completionMatrixComparison D i w
  let hasComparison (t : TopologicalSpace (PointsIn j F)) : Prop :=
    letI := t
    Nonempty (LocalPoints D i w ≃ₜ* PointsIn j F)
  have htop := localPointTopology_eq_matrixTopology J j
  have hd : hasComparison (inferInstance : TopologicalSpace (PointsIn j F)) := ⟨d.symm⟩
  exact (congrArg hasComparison htop).mpr hd

/-- For a finite completion satisfying the local mixing hypotheses, apply the
finite-covolume premise to the subgroup obtained by arithmetic projection. -/
private theorem fullProjectionOfFiniteCompletion (hfull : FiniteCovolumeSubgroup.{u})
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.FinitePlace)
    (hG : IsAbsolutelyAlmostSimple G)
    (hmix : MixingCases (baseChangedAlgebraicGroup (D.Completion (.inl w)) G))
    (H : Subgroup (FinitePoints D i {Sum.inl w}))
    (hclosed : IsClosed (H : Set (FinitePoints D i {Sum.inl w})))
    (hnd : ¬ DiscreteTopology H) (hμ : FiniteInvariantQuotientMeasure H) : H = ⊤ := by
  let F := D.Completion (.inl w)
  let _ : Algebra K F := AdelicGroups.completionAlgebra D (.inl w)
  let _ : ValuativeRel F := inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
  let : IsNonarchimedeanLocalField F := GlobalFieldData.finiteCompletion_isLocalField D w
  let L := baseChangedAlgebraicGroup F G
  let _ := pointTopology L.val.X
  obtain ⟨e⟩ := completionPointsComparison D i (.inl w)
  have hL := OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G hG
  have htop := LocalAlgebraicTransport.rationalPointTopologicalGroup L
  exact fullProjectionOfLocalModel hfull L hL hmix H hclosed hnd hμ htop
    ((singletonLocalPoints D i (.inl w)).trans e)


/-- Denseness of the subgroup generated by contracted elements is invariant
under a topological group isomorphism. -/
private theorem denseContractedTransfer {P Q : Type u} [Group P] [Group Q]
    [TopologicalSpace P] [TopologicalSpace Q] (e : P ≃ₜ* Q)
    (hP : Dense (Subgroup.closure {x : P | Contracted x} : Set P)) :
    Dense (Subgroup.closure {x : Q | Contracted x} : Set Q) := by
  apply (e.surjective.denseRange.dense_image e.continuous hP).mono
  change (Subgroup.closure {x : P | Contracted x}).map e.toMonoidHom ≤ _
  rw [MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨x, ⟨a, ha⟩, rfl⟩
  refine ⟨e a, ?_⟩
  have hc : Continuous (e : P → Q) := e.continuous
  have ht : Tendsto (fun n : ℕ => e (a ^ n * x * (a ^ n)⁻¹)) atTop (𝓝 (e 1)) :=
    (hc.tendsto 1).comp ha
  change Tendsto (fun n : ℕ => e a ^ n * e x * (e a ^ n)⁻¹) atTop (𝓝 1)
  simpa only [map_one, map_mul, map_inv, map_pow] using ht

/-- Join the finite-place projection and contraction arguments to the dense
projection on the finite remainder. The omitted set already contains the
noncompact archimedean factors. -/
private theorem strongApproximationOfLocalData
    (hfull : FiniteCovolumeSubgroup.{u})
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (S J : Finset D.Place) (hJ : Disjoint J S)
    (hG : IsAbsolutelyAlmostSimple G)
    (hcompact : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hnoncompact : ¬ CompactSpace (FinitePoints D i S))
    (harch : ∀ w : D.InfinitePlace, Sum.inr w ∉ S →
      Sum.inr w ∈ J ∧ CompactSpace (LocalPoints D i (.inr w)))
    (hfinite : ∀ w : D.FinitePlace, Sum.inl w ∉ S → Sum.inl w ∉ J →
      MixingCases (baseChangedAlgebraicGroup (D.Completion (.inl w)) G) ∧
      Dense (Subgroup.closure {x : LocalPoints D i (.inl w) | Contracted x} :
        Set (LocalPoints D i (.inl w))))
    (hrem : DenseRange (ArithmeticLatticeProjection.rationalProjection D i J)) :
    StrongApproximation D i S := by
  apply strongApproximationOfLocalProjections D i S J hJ (fun w hw => (harch w hw).2)
    hcompact hnoncompact _ _ hrem
  · rintro ⟨w, hw⟩ hwJ H hc hd hμ
    cases w with
    | inl p =>
      exact fullProjectionOfFiniteCompletion hfull D i p hG
        (hfinite p hw hwJ).1 H hc hd hμ
    | inr p => exact (hwJ (harch p hw).1).elim
  · rintro ⟨w, hw⟩ hwJ
    cases w with
    | inl p =>
      exact denseContractedTransfer (singletonLocalPoints D i (.inl p)).symm
        (hfinite p hw hwJ).2
    | inr p => exact (hwJ (harch p hw).1).elim

end LocalProjection

section ArchimedeanProjection

open Filter
open scoped Classical

open Specs.IntegralModels (MatrixRealization)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.Arithmetic.ProjectiveRecurrence
  (cocharacterRadicalPoints localPointSet evaluateArchimedean)
open AdelicGroups (Adeles LocalPoints StrongApproximation)
open ArithmeticLatticeProjection (FinitePoints diagonalSubgroup integralOutside lattice forgetPlaces)
open CompactProductIsolation (Contracted diagonalClosure insertFinite projectedArithmetic)

private theorem contracted_pi_iff {I : Type*} {P : I → Type*}
    [∀ w, Group (P w)] [∀ w, TopologicalSpace (P w)] (x : ∀ w, P w) :
    Contracted x ↔ ∀ w, Contracted (x w) := by
  constructor
  · rintro ⟨a, ha⟩ w
    exact ⟨a w, tendsto_pi_nhds.mp ha w⟩
  · intro hx
    choose a ha using hx
    exact ⟨a, tendsto_pi_nhds.mpr ha⟩

private theorem denseContractedPi {I : Type*} [Finite I] {P : I → Type*}
    [∀ w, Group (P w)] [∀ w, TopologicalSpace (P w)]
    (h : ∀ w, Dense (Subgroup.closure {x : P w | Contracted x} : Set (P w))) :
    Dense (Subgroup.closure {x : ∀ w, P w | Contracted x} : Set (∀ w, P w)) := by
  have heq : {x : ∀ w, P w | Contracted x} = Set.univ.pi (fun w => {x : P w | Contracted x}) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    exact contracted_pi_iff x
  have hone (w : I) : (1 : P w) ∈ {x : P w | Contracted x} :=
    ⟨1, by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : P w)) atTop (𝓝 1))⟩
  rw [heq, Subgroup.closure_pi hone]
  exact dense_pi Set.univ (fun w _ => h w)

private def infinitePlaceInclusion {K : Type u} [Field K] (D : GlobalFieldData.{u,u} K) :
    D.InfinitePlace ↪ D.Place :=
  ⟨Sum.inr, Sum.inr_injective⟩

private theorem isolateArchimedeanFactors {K : Type u} [Field K] [NumberField K]
    {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,u} K) (hD : D = .number inferInstance)
    (i : MatrixRealization G) (S : Finset D.Place) (A : Finset D.InfinitePlace)
    (hdisj : ∀ w ∈ A, Sum.inr w ∉ S)
    (hcomp : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hS : ¬ CompactSpace (FinitePoints D i S))
    (hG : IsAbsolutelyAlmostSimple G)
    (harch : ∀ w : D.InfinitePlace, Sum.inr w ∉ S → w ∉ A →
      CompactSpace (LocalPoints D i (.inr w)))
    (hgen : ∀ w : ↑A, Dense (Subgroup.closure (localPointSet D i (.inr w.val)
      (cocharacterRadicalPoints (baseChangedAlgebraicGroup (D.Completion (.inr w.val)) G))) :
      Set (LocalPoints D i (.inr w.val))))
    (hcontract : ∀ w : ↑A, Dense (Subgroup.closure
      {x : LocalPoints D i (.inr w.val) | Contracted x} :
        Set (LocalPoints D i (.inr w.val)))) :
    let J := A.map (infinitePlaceInclusion D)
    ∀ x : FinitePoints D i J, insertFinite D i S J x ∈ diagonalClosure D i S := by
  let J := A.map (infinitePlaceInclusion D)
  have hd : Disjoint J S := by
    apply Finset.disjoint_left.mpr
    intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hp
    exact hdisj w hw
  let T := S ∪ J
  let U := integralOutside D i T
  have hA (w : ↑A) : Sum.inr w.val ∈ J :=
    Finset.mem_map.mpr ⟨w.val, w.property, rfl⟩
  obtain ⟨hUc, hUo⟩ := ArithmeticLatticeProjection.compactOpenOutside D i T (fun w hw =>
    harch w (fun hs => hw (Finset.mem_union_left _ hs))
      (fun ha => hw (Finset.mem_union_right _ (hA ⟨w, ha⟩))))
  let e : (↑A : Set D.InfinitePlace) ≃ (↑J : Set D.Place) :=
    Equiv.ofBijective (fun w => ⟨.inr w.val, hA w⟩) (by
      constructor
      · intro x y h
        exact Subtype.ext (Sum.inr_injective (congrArg Subtype.val h))
      · intro w
        obtain ⟨p, hp, he⟩ := Finset.mem_map.mp w.property
        exact ⟨⟨p, hp⟩, Subtype.ext he⟩)
  have hprod : Dense (Subgroup.closure {x : FinitePoints D i J | Contracted x} :
      Set (FinitePoints D i J)) := denseContractedPi (fun w => by
    obtain ⟨p, rfl⟩ := e.surjective w
    exact hcontract p)
  have hproj : Dense (projectedArithmetic D i S J U : Set (FinitePoints D i J)) := by
    by_cases hAn : A.Nonempty
    · let X := ∀ w : ↑A, LocalPoints D i (.inr w.val)
      let R : X ≃ₜ FinitePoints D i J :=
        Homeomorph.piCongrLeft (Y := fun w : (↑J : Set D.Place) => LocalPoints D i w.1) e
      have hdense := ProjectiveRecurrence.archimedeanLatticeProjection
        G i D hD S T A U Finset.subset_union_left hAn (fun w => hdisj w.val w.property)
        (fun w => Finset.mem_union_right S (hA w)) hcomp hS hUc hUo hG hgen
      let ev := evaluateArchimedean D i A (fun w => Finset.mem_union_right S (hA w))
      have himage : R '' ((lattice D i T U).map ev : Set X) =
          (projectedArithmetic D i S J U : Set (FinitePoints D i J)) := by
        ext x
        constructor
        · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
          exact ⟨y, hy, by
            apply R.symm.injective
            rw [R.symm_apply_apply]
            rfl⟩
        · rintro ⟨y, hy, rfl⟩
          refine ⟨ev y, ⟨y, hy, rfl⟩, ?_⟩
          apply R.symm.injective
          rw [R.symm_apply_apply]
          rfl
      rw [← himage]
      exact R.surjective.denseRange.dense_image R.continuous hdense
    · have hJ : J = ∅ := by simp [J, Finset.not_nonempty_iff_eq_empty.mp hAn]
      have hempty : ∀ w ∈ J, False := by simp [hJ]
      haveI : Subsingleton (FinitePoints D i J) :=
        ⟨fun x y => funext fun w => (hempty w.val w.2).elim⟩
      have htop : projectedArithmetic D i S J U = ⊤ := Subsingleton.elim _ _
      rw [htop, Subgroup.coe_top]
      exact dense_univ
  exact (CompactProductIsolation.isolateAdelicFactors D i S J hd U hUc hUo).2 hproj hprod


open Specs.GeometricRadicals (IsSemisimple)
open Specs.IntegralModels (MatrixRealization)
open AdelicGroups (Adeles LocalPoints StrongApproximation)
open ArithmeticLatticeProjection (FinitePoints rationalProjection forgetPlaces)
open CompactProductIsolation (diagonalClosure insertFinite)
open private forgetPlaces_continuous extendByOne forgetPlaces_surjective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
open private quotientClosure from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.CompactProductIsolation

private theorem not_compact_largerProduct {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    {S T : Finset D.Place} (h : S ⊆ T) (hnc : ¬ CompactSpace (FinitePoints D i S)) :
    ¬ CompactSpace (FinitePoints D i T) := by
  intro hc
  letI := hc
  exact hnc ⟨(forgetPlaces_surjective D i h).range_eq ▸
    isCompact_range (forgetPlaces_continuous D i h)⟩

private theorem strongApproximationOfIsolatedPlaces {K : Type u} [Field K]
    {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (S J : Finset D.Place) (hd : Disjoint J S)
    (hisol : ∀ x : FinitePoints D i J, insertFinite D i S J x ∈ diagonalClosure D i S)
    (h : StrongApproximation D i (S ∪ J)) : StrongApproximation D i S := by
  have hk := CompactProductIsolation.range_insertFinite_eq_ker D i hd
  have hsub :
      ((CompactProductIsolation.forgetOutside D i (S := S) (T := S ∪ J)
        Finset.subset_union_left).ker : Set (Adeles D i S)) ⊆ diagonalClosure D i S := by
    rw [← hk]
    rintro x ⟨g, rfl⟩
    exact hisol g
  exact ((CompactProductIsolation.enlargeOmittedSet D i S (S ∪ J)
    Finset.subset_union_left).2 hsub).2.2.mp h

set_option maxHeartbeats 350000 in
private theorem forgetFiniteQuotient {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    {J T : Finset D.Place} (h : J ⊆ T) : IsQuotientMap (forgetPlaces D i h) := by
  have hf := forgetPlaces_continuous D i h
  have he : Continuous (extendByOne D i h) := by
    apply continuous_pi
    intro w
    unfold extendByOne
    split
    · apply continuous_apply
    · exact continuous_const
  have hright : (forgetPlaces D i h : FinitePoints D i T → FinitePoints D i J) ∘
      extendByOne D i h = id := by
    funext x w
    change extendByOne D i h x ⟨w.val, h w.property⟩ = x w
    unfold extendByOne
    split
    · rfl
    · rename_i hn
      exact (hn w.property).elim
  refine ⟨isCoinducing_iff.mpr (fun S => ⟨fun hs => ?_, fun hs => hs.preimage hf⟩),
    forgetPlaces_surjective D i h⟩
  have hm := hs.preimage he
  rwa [← Set.preimage_comp, hright, Set.preimage_id] at hm

private theorem denseProjectionWithConnectedArchimedeanRemainder {K : Type u} [Field K]
    [NumberField K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (hD : D = .number inferInstance)
    (i : MatrixRealization G) (hG : IsSemisimple G) {J T : Finset D.Place} (h : J ⊆ T)
    (hfinite : ∀ w : D.FinitePlace, Sum.inl w ∈ T → Sum.inl w ∈ J)
    (harch : ∀ w : D.InfinitePlace, Sum.inr w ∈ T → Sum.inr w ∉ J →
      ConnectedSpace (LocalPoints D i (.inr w)))
    (hd : DenseRange (rationalProjection D i J)) :
    DenseRange (rationalProjection D i T) := by
  let f := forgetPlaces D i h
  let r := rationalProjection D i T
  let H := r.range.topologicalClosure
  have hH : (H : Set (FinitePoints D i T)) = closure (Set.range r) := rfl
  have harchIn : Specs.WeakApproximationByTori.ArchimedeanComponentsFor D :=
    hD.symm ▸ WeakApproximationByTori.archimedeanComponents.{u,v} (K := K)
  have hker : f.ker ≤ H := by
    intro x hx
    apply Subgroup.pi_mem_of_mulSingle_mem
    rintro ⟨w, hw⟩
    have hmem (hJ : w ∈ J) : x ⟨w, hw⟩ = 1 := by
      have hx' : f x = 1 := hx
      exact congrFun hx' ⟨w, hJ⟩
    by_cases hJ : w ∈ J
    · simp only [hmem hJ, Pi.mulSingle_one]
      exact H.one_mem
    · cases w with
      | inl w => exact (hJ (hfinite w hw)).elim
      | inr w =>
        letI := harch w hw hJ
        have ht : x ⟨.inr w, hw⟩ ∈ connectedComponent (1 : LocalPoints D i (.inr w)) := by
          rw [PreconnectedSpace.connectedComponent_eq_univ]
          exact Set.mem_univ _
        exact harchIn G hG i T w hw _ ht
  have himg : f '' Set.range r = Set.range (rationalProjection D i J) := by
    rw [← Set.range_comp]
    rfl
  exact (quotientClosure f (forgetFiniteQuotient D i h) (Set.range r) H hH hker).2.2.mp
    (himg.symm ▸ hd)


end ArchimedeanProjection


section Assembly

open scoped Classical
open Specs.Arithmetic.LocalProjectedClosure (FiniteCovolumeSubgroup)
open Specs.Arithmetic.LocalQuotientMixing (MixingCases)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.Arithmetic.ProjectiveRecurrence (cocharacterRadicalPoints localPointSet)
open ArithmeticLatticeProjection (FinitePoints rationalProjection)
open CompactProductIsolation (Contracted)
open AdelicGroups (Adeles LocalPoints StrongApproximation)

private def finitePlaceInclusion {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K) :
    D.FinitePlace ↪ D.Place := ⟨Sum.inl, Sum.inl_injective⟩

set_option maxHeartbeats 500000 in
/-- Combine the local structure and finite projection density with the compact
full quotient. The local hypotheses refer to the original completion groups. -/
private theorem strongApproximationFromFiniteLocalModels
    (hfull : FiniteCovolumeSubgroup.{u})
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) [IsEmpty D.InfinitePlace] (i : MatrixRealization G) (S : Finset D.Place)
    (hG : IsAbsolutelyAlmostSimple G)
    (hcompact : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hnc : ¬ CompactSpace (FinitePoints D i S))
    (B : Finset D.FinitePlace)
    (hfinite : ∀ w : D.FinitePlace, w ∉ B →
      MixingCases (baseChangedAlgebraicGroup (D.Completion (.inl w)) G) ∧
      Dense (Subgroup.closure {x : LocalPoints D i (.inl w) | Contracted x} :
        Set (LocalPoints D i (.inl w))))
    (hweak : ∀ J : Finset D.Place, (∀ p ∈ J, ∃ w ∈ B, p = Sum.inl w) →
      DenseRange (rationalProjection D i J)) :
    StrongApproximation D i S := by
  let J := B.map (finitePlaceInclusion D) \ S
  have hJ : Disjoint J S := Finset.disjoint_left.mpr fun p hp hs =>
    (Finset.mem_sdiff.mp hp).2 hs
  have hweakJ := hweak J (fun p hp => by
    obtain ⟨w, hw, he⟩ := Finset.mem_map.mp (Finset.mem_sdiff.mp hp).1
    exact ⟨w, hw, he.symm⟩)
  apply strongApproximationOfLocalData hfull D i S J hJ hG hcompact hnc
    (fun w => isEmptyElim w) _ hweakJ
  intro w hwS hwJ
  apply hfinite w
  intro hw
  exact hwJ (Finset.mem_sdiff.mpr ⟨Finset.mem_map.mpr ⟨w, hw, rfl⟩, hwS⟩)

set_option maxHeartbeats 500000 in
/-- Combine the local structure and finite projection density with the compact
full quotient. The local hypotheses refer to the original completion groups. -/
private theorem strongApproximationFromNumberFieldLocalModels
    (hfull : FiniteCovolumeSubgroup.{u})
    {K : Type u} [Field K] [NumberField K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,u} K) (hD : D = .number inferInstance) (i : MatrixRealization G) (S : Finset D.Place)
    (hG : IsAbsolutelyAlmostSimple G)
    (hcompact : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hnc : ¬ CompactSpace (FinitePoints D i S))
    (B : Finset D.FinitePlace)
    (hfinite : ∀ w : D.FinitePlace, w ∉ B →
      MixingCases (baseChangedAlgebraicGroup (D.Completion (.inl w)) G) ∧
      Dense (Subgroup.closure {x : LocalPoints D i (.inl w) | Contracted x} :
        Set (LocalPoints D i (.inl w))))
    (harch : ∀ w : D.InfinitePlace,
      (CompactSpace (LocalPoints D i (.inr w)) ∧ ConnectedSpace (LocalPoints D i (.inr w))) ∨
      (Dense (Subgroup.closure (localPointSet D i (.inr w)
        (cocharacterRadicalPoints (baseChangedAlgebraicGroup (D.Completion (.inr w)) G))) :
        Set (LocalPoints D i (.inr w))) ∧
       Dense (Subgroup.closure {x : LocalPoints D i (.inr w) | Contracted x} :
        Set (LocalPoints D i (.inr w)))))
    (hweak : ∀ J : Finset D.Place, (∀ p ∈ J, ∃ w ∈ B, p = Sum.inl w) →
      DenseRange (rationalProjection D i J)) :
    StrongApproximation D i S := by
  letI : Finite D.InfinitePlace := by
    subst D
    exact inferInstanceAs (Finite (NumberField.InfinitePlace K))
  letI : Fintype D.InfinitePlace := Fintype.ofFinite _
  let A : Finset D.InfinitePlace := Finset.univ.filter fun w =>
    Sum.inr w ∉ S ∧ ¬ (CompactSpace (LocalPoints D i (.inr w)) ∧
      ConnectedSpace (LocalPoints D i (.inr w)))
  let N := A.map (infinitePlaceInclusion D)
  have hNA (w : D.InfinitePlace) : Sum.inr w ∈ N ↔ w ∈ A := by
    refine ⟨fun hw => ?_, fun hw => Finset.mem_map.mpr ⟨w, hw, rfl⟩⟩
    obtain ⟨w', hw', he⟩ := Finset.mem_map.mp hw
    exact (Sum.inr_injective he : w' = w) ▸ hw'
  have hdisjA (w : D.InfinitePlace) (hw : w ∈ A) : Sum.inr w ∉ S :=
    (Finset.mem_filter.mp hw).2.1
  have hgenA (w : D.InfinitePlace) (hw : w ∈ A) :
      (Dense (Subgroup.closure (localPointSet D i (.inr w)
        (cocharacterRadicalPoints (baseChangedAlgebraicGroup (D.Completion (.inr w)) G))) :
        Set (LocalPoints D i (.inr w)))) ∧
      Dense (Subgroup.closure {x : LocalPoints D i (.inr w) | Contracted x} :
        Set (LocalPoints D i (.inr w))) :=
    (harch w).resolve_left (fun h => (Finset.mem_filter.mp hw).2.2 h)
  have hcompA (w : D.InfinitePlace) (hwS : Sum.inr w ∉ S) (hwA : w ∉ A) :
      CompactSpace (LocalPoints D i (.inr w)) ∧ ConnectedSpace (LocalPoints D i (.inr w)) := by
    by_contra hn
    exact hwA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwS, hn⟩)
  have hN : Disjoint N S := by
    apply Finset.disjoint_left.mpr
    intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hp
    exact hdisjA w hw
  have hisolated : ∀ x : FinitePoints D i N,
      CompactProductIsolation.insertFinite D i S N x ∈
        CompactProductIsolation.diagonalClosure D i S :=
    isolateArchimedeanFactors D hD i S A hdisjA hcompact hnc hG (fun w hwS hwA => (hcompA w hwS hwA).1)
      (fun w => (hgenA w.val w.property).1) (fun w => (hgenA w.val w.property).2)
  apply strongApproximationOfIsolatedPlaces D i S N hN hisolated
  let T := S ∪ N
  let Jf := B.map (finitePlaceInclusion D) \ T
  let Ja := (Finset.univ.map (infinitePlaceInclusion D)) \ T
  let J := Jf ∪ Ja
  have hJ : Disjoint J T := by
    apply Finset.disjoint_left.mpr
    intro p hp ht
    rcases Finset.mem_union.mp hp with hf | ha
    · exact (Finset.mem_sdiff.mp hf).2 ht
    · exact (Finset.mem_sdiff.mp ha).2 ht
  have harchT (w : D.InfinitePlace) (hw : Sum.inr w ∉ T) :
      CompactSpace (LocalPoints D i (.inr w)) ∧ ConnectedSpace (LocalPoints D i (.inr w)) := by
    exact hcompA w (fun hs => hw (Finset.mem_union_left _ hs))
      (fun hA => hw (Finset.mem_union_right _ ((hNA w).mpr hA)))
  have hweakJf := hweak Jf (fun p hp => by
    obtain ⟨w, hw, he⟩ := Finset.mem_map.mp (Finset.mem_sdiff.mp hp).1
    exact ⟨w, hw, he.symm⟩)
  have hweakJ : DenseRange (rationalProjection D i J) :=
    denseProjectionWithConnectedArchimedeanRemainder D hD i hG.1 Finset.subset_union_left
      (fun w hw => by
        rcases Finset.mem_union.mp hw with hf | ha
        · exact hf
        · obtain ⟨x, hx, he⟩ := Finset.mem_map.mp (Finset.mem_sdiff.mp ha).1
          cases he)
      (fun w hw _ => (harchT w (Finset.disjoint_left.mp hJ hw)).2) hweakJf
  apply strongApproximationOfLocalData hfull D i T J hJ hG hcompact
    (not_compact_largerProduct D i Finset.subset_union_left hnc) _ _ hweakJ
  · intro w hw
    exact ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mpr
      ⟨Finset.mem_map.mpr ⟨w, Finset.mem_univ _, rfl⟩, hw⟩), (harchT w hw).1⟩
  · intro w hwT hwJ
    apply hfinite w
    intro hwB
    exact hwJ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr
      ⟨Finset.mem_map.mpr ⟨w, hwB, rfl⟩, hwT⟩))

end Assembly

section NumberFieldComparison

open Specs.IntegralModels (RationalPoints)
open AdelicGroups (LocalPoints localSubgroup localPoint StrongApproximation)
open ArithmeticLatticeProjection (FinitePoints)

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K}

/-- The data of one place used by the topology and the rational diagonal. -/
private structure AdelicFactor (P : Type u) where
  points : Type u
  topology : TopologicalSpace points
  integral : Set points
  rationalImage : P → points

private def adelicFactor (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (w : D.Place) : AdelicFactor (RationalPoints G) :=
  ⟨LocalPoints D i w, inferInstance, localSubgroup D i w, localPoint D i w⟩

private def approximationFromFactors {W P : Type u}
    (f : W → AdelicFactor P) (S : Finset W) : Prop :=
  letI (w : W) : TopologicalSpace (f w).points := (f w).topology
  ¬ CompactSpace (∀ w : (↑S : Set W), (f w.1).points) →
    Dense {x : Πʳ w : {w : W // w ∉ S}, [(f w.1).points, (f w.1).integral] |
      ∃ g : P, ∀ w, x w = (f w.1).rationalImage g}

private abbrev ApproximationAt (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (S : Finset D.Place) : Prop :=
  ¬ CompactSpace (FinitePoints D i S) → StrongApproximation D i S

private theorem approximationFromFactors_iff (D : GlobalFieldData.{u,v} K)
    (i : MatrixRealization G) (S : Finset D.Place) :
    approximationFromFactors (adelicFactor D i) S ↔ ApproximationAt D i S :=
  Iff.rfl

private theorem numberFactors_eq [NumberField K] (i : MatrixRealization G) :
    (adelicFactor (.number inferInstance : GlobalFieldData.{u,v} K) i :
      NumberPlace K → AdelicFactor (RationalPoints G)) =
    adelicFactor (.number inferInstance : GlobalFieldData.{u,u} K) i := by
  funext w
  cases w <;> rfl

/-- The two universe presentations of a number field give the same
approximation condition for each omitted set. -/
private theorem numberApproximationOfSameUniverse [NumberField K]
    (i : MatrixRealization G) (S : Finset (NumberPlace K)) :
    ApproximationAt (.number inferInstance : GlobalFieldData.{u,u} K) i S →
    ApproximationAt (.number inferInstance : GlobalFieldData.{u,v} K) i S := by
  intro h
  apply (approximationFromFactors_iff
    (.number inferInstance : GlobalFieldData.{u,v} K) i S).mp
  rw [numberFactors_eq]
  exact (approximationFromFactors_iff
    (.number inferInstance : GlobalFieldData.{u,u} K) i S).mpr h

end NumberFieldComparison

open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.Arithmetic.LocalQuotientMixing (MixingCases)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open AdelicGroups (LocalPoints)
open ArithmeticLatticeProjection (rationalProjection)
open CompactProductIsolation (Contracted)

private theorem unitaryFiniteLocalData {K E A : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) [Field E] [Algebra K E] [Algebra.IsSeparable K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    (hKE : Module.finrank K E = 2)
    {I : Type u} [Fintype I] (hA : isCentralSimple E A) (hn : 3 ≤ degree E A)
    (b : Module.Basis I E A) (s : SecondKind K E A) (G : AffineAlgebraicGroup K)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (hrep : RepresentsUnitary hA b s G) (i : MatrixRealization G) :
    ∃ B : Finset D.FinitePlace,
      (∀ w : D.FinitePlace, w ∉ B →
        MixingCases (baseChangedAlgebraicGroup (D.Completion (.inl w)) G) ∧
        Dense (Subgroup.closure {x : LocalPoints D i (.inl w) | Contracted x} :
          Set (LocalPoints D i (.inl w)))) ∧
      (∀ J : Finset D.Place, (∀ p ∈ J, ∃ w ∈ B, p = Sum.inl w) →
        DenseRange (rationalProjection D i J)) := by
  obtain ⟨B, hB, hgen⟩ := AnisotropicUnitaryFiniteModels.finiteLocalModels
    D hKE hA hn b s G hG hsc hrep i
  refine ⟨B, hgen, ?_⟩
  intro J hJ
  letI : Algebra.IsQuadraticExtension K E := ⟨hKE⟩
  apply AnisotropicUnitarySplitCentreWeakApproximation.splitCentreWeakApproximationOfUnitaryModel
    D hA b s G hrep i J
  intro p hp
  obtain ⟨w, hw, he⟩ := hJ p hp
  exact ⟨w, he, hB w hw⟩

/-- Compactness and strong approximation for globally anisotropic special
unitary groups of outer type A over global fields. -/
theorem outerTypeA : Specs.Arithmetic.AnisotropicUnitaryApproximation.OuterTypeA.{u,v} := by
  intro K E A _ D _ _ _ _ _ _ _ hKE I _ hA hn b s G hG hsc hanis hrep i
  have hcompact := compactUnitaryAdelicQuotient D hKE hA hn b s G hG.1 hanis hrep i
  refine ⟨hcompact, ?_⟩
  cases D with
  | number hK =>
    letI : NumberField K := hK
    let D₀ : GlobalFieldData.{u,u} K := .number hK
    have hc₀ := compactUnitaryAdelicQuotient D₀ hKE hA hn b s G hG.1 hanis hrep i
    obtain ⟨B, hfinite, hweak⟩ := unitaryFiniteLocalData D₀ hKE hA hn b s G hG hsc hrep i
    have harch := AnisotropicUnitaryArchimedeanModels.archimedeanLocalModels
      D₀ hKE hA hn b s G hG hsc hrep i rfl
    intro S _
    apply numberApproximationOfSameUniverse i S
    intro hnc
    exact strongApproximationFromNumberFieldLocalModels
      LocalProjectedClosure.localProjectedClosure D₀ rfl i S hG hc₀ hnc B hfinite harch hweak
  | function F t =>
    let D : GlobalFieldData.{u,v} K := .function F t
    letI : IsEmpty D.InfinitePlace := inferInstanceAs (IsEmpty PEmpty)
    obtain ⟨B, hfinite, hweak⟩ := unitaryFiniteLocalData D hKE hA hn b s G hG hsc hrep i
    intro S _ hnc
    exact strongApproximationFromFiniteLocalModels
      LocalProjectedClosure.localProjectedClosure D i S hG hcompact hnc B hfinite hweak

end LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryApproximation
