import Specs.LinearAlgebraicGroups.Arithmetic.IsotropicSufficiency
import LinearAlgebraicGroups.Arithmetic.OddSpinModels
import LinearAlgebraicGroups.Arithmetic.IsotropicTypeC
import LinearAlgebraicGroups.Arithmetic.OctonionForms
import LinearAlgebraicGroups.Arithmetic.StrongApproximationF4
import LinearAlgebraicGroups.Arithmetic.QuasiSplitApproximation
import LinearAlgebraicGroups.Arithmetic.TrialitarianLocalForms
import LinearAlgebraicGroups.Arithmetic.ExceptionalRealPoints
import LinearAlgebraicGroups.Arithmetic.IsotropicOuterTypeA
import Specs.LinearAlgebraicGroups.Arithmetic.StrongApproximationNontrialitarianD
import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRadicalGeneration
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRadicalGeneration
import LinearAlgebraicGroups.Arithmetic.StrongApproximationNontrialitarianD
open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u v

namespace LinearAlgebraicGroups.Arithmetic.IsotropicSufficiency

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.AbsoluteDynkinTypes (HasDynkinType PreservesCartan)
open LinearAlgebraicGroups.Specs.Arithmetic.OppositeRadicals (IsNoncentral localPlus)
open LinearAlgebraicGroups.Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open LinearAlgebraicGroups.Specs.CharacterDescent (Cocharacter)
open LinearAlgebraicGroups.Specs.GeometricRadicals (GeometricGroup IsSemisimple)
open LinearAlgebraicGroups.Specs.IntegralModels (MatrixRealization)
open LinearAlgebraicGroups.Specs.Pinning (AttachedDatum SplitBorelPair)
open LinearAlgebraicGroups.Specs.RelativeRank (relativeRank)
open LinearAlgebraicGroups.Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open LinearAlgebraicGroups.Specs.Unipotent (baseChangedAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (existsLimitDecomposition oppositeCocharacter)
open LieAlgebrasAndRepresentations (FiniteDynkinType)
open AdelicGroups
open ArithmeticLatticeProjection (FinitePoints)
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private exists_proper_dynamic_of_noncentral from LinearAlgebraicGroups.Descent.RelativeRank
open private infiniteNormedField
  from LinearAlgebraicGroups.Arithmetic.WeakApproximationLocalSmoothImage

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

private theorem absoluteAlmostSimpleForClassification {K : Type u} [Field K]
    (G : AffineAlgebraicGroup K) (hG : IsAbsolutelyAlmostSimple G) :
    Specs.AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G := by
  refine ⟨hG.1, fun h => hG.2.1 ⟨h.iso (Grp.isZero_trivial _)⟩, ?_⟩
  intro N hN
  exact (hG.2.2 N hN).imp (fun ⟨e⟩ => (Grp.isZero_trivial _).of_iso e) id

private theorem positiveRankOfNoncentralCocharacter {K : Type u} [Field K]
    (G : AffineAlgebraicGroup K) (hG : IsSemisimple G)
    (c : Cocharacter G.val) (hc : IsNoncentral c) : 0 < relativeRank G := by
  apply (Descent.RelativeRank.semisimpleParabolicCriterion G hG).mp
  apply exists_proper_dynamic_of_noncentral G (reductive_of_semisimple G hG) c
  intro h
  obtain ⟨X, g, hng⟩ := hc
  exact hng (h X g)

private theorem strongApproximationOfLocalDensity {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (c : Cocharacter G.val) (hc : IsNoncentral c)
    (S : Finset D.Place) (hS : S.Nonempty)
    (hLocal : ∀ w : AdelicGroups.Outside D S, Dense (localPlus D i w.1)) :
    AdelicGroups.StrongApproximation D i S := by
  obtain ⟨P⟩ := existsLimitDecomposition G c
  obtain ⟨Q⟩ := existsLimitDecomposition G (oppositeCocharacter c)
  exact ((OppositeRadicals.approximation D G i hG c hc P Q).2.2.2.2 S hS).2 hLocal

private theorem noncompactOfCompletionRank {K F : Type u} [Field K]
    [NontriviallyNormedField F] [Algebra K F]
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : IsSemisimple (baseChangedAlgebraicGroup F G))
    (hr : 0 < relativeRank (baseChangedAlgebraicGroup F G)) :
    ¬ CompactSpace (PointsIn i F) := by
  obtain ⟨_, j, _, e, _, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison K F G i
  intro h
  letI := h
  exact F4RealCompletion.positiveRankNoncompact _ j hG hr
    (e.symm.surjective.compactSpace e.symm.continuous)

private theorem localNoncompactOfPositiveRank {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (hr : 0 < relativeRank G) (w : D.Place) :
    ¬ CompactSpace (AdelicGroups.LocalPoints D i w) := by
  have hH : IsSemisimple (baseChangedAlgebraicGroup (D.Completion w) G) :=
    (OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := D.Completion w) G hG).1
  have hrH := StrongApproximationF4.positiveRank_at_completion D i hG hr w
  rcases w with w | w
  · let F := D.FiniteCompletion w
    letI := IsTopologicalAddGroup.rightUniformSpace F
    letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
    letI : (Valued.v (R := F)).RankOne :=
      { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := F).comp
          MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    letI : NontriviallyNormedField F :=
      Valued.toNontriviallyNormedField F (ValuativeRel.ValueGroupWithZero F)
    letI : Algebra K F := completionAlgebra D (.inl w)
    exact noncompactOfCompletionRank (F := F) G i hH hrH
  · cases D with
    | function F t => exact w.elim
    | number h =>
      letI : NontriviallyNormedField w.Completion := infiniteNormedField w
      letI : Algebra K w.Completion := completionAlgebra (.number h) (.inr w)
      exact noncompactOfCompletionRank (F := w.Completion) G i hH hrH

private theorem omittedProductNoncompactOfPositiveRank {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (hr : 0 < relativeRank G)
    (S : Finset D.Place) (hS : S.Nonempty) : ¬ CompactSpace (FinitePoints D i S) := by
  intro h
  letI := h
  obtain ⟨w, hw⟩ := hS
  let j : (↑S : Set D.Place) := ⟨w, hw⟩
  have he : Function.Surjective (fun x : FinitePoints D i S => x j) :=
    Function.surjective_eval j
  exact localNoncompactOfPositiveRank D G i hG hr w
    (he.compactSpace (continuous_apply j))

private theorem strongApproximationTypeB {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (hiso : ∃ c : Cocharacter G.val, IsNoncentral c)
    (P : SplitBorelPair (AlgebraicClosure K)) (hP : P.G = GeometricGroup G)
    (E : AttachedDatum P) (n : ℕ) (hn : 2 ≤ n)
    (ht : letI := E.comm; HasDynkinType (RootData.integralCartan E.datum.rootDatum E.base) (.B n hn))
    (S : Finset D.Place) (hS : S.Nonempty) : AdelicGroups.StrongApproximation D i S := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, happrox⟩ :=
    OddSpinModels.typeBApplicability.{u,v} n hn G hG hsc P hP E ht
  exact happrox D hG hiso i S hS

private theorem strongApproximationTypeC {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (c : Cocharacter G.val) (hc : IsNoncentral c)
    (P : SplitBorelPair (AlgebraicClosure K)) (hP : P.G = GeometricGroup G)
    (E : AttachedDatum P) (n : ℕ) (hn : 2 ≤ n)
    (ht : letI := E.comm; HasDynkinType (RootData.integralCartan E.datum.rootDatum E.base) (.C n hn))
    (S : Finset D.Place) (hS : S.Nonempty) : AdelicGroups.StrongApproximation D i S := by
  cases n with
  | zero => omega
  | succ n =>
    letI := E.comm
    change ∃ e : E.toBased.base.support ≃ Fin (n + 1),
      ∀ a b, E.toBased.datum.pairing b.val a.val = CartanMatrix.B (n + 1) (e a) (e b) at ht
    obtain ⟨e, he⟩ := ht
    apply IsotropicTypeC.typeCStrongApproximation (E := SeparableClosure K) D n G i hG hsc _ c hc S hS
    refine ⟨P, E, hP, e.symm, fun a b => ?_⟩
    have h := he (e.symm a) (e.symm b)
    rw [e.apply_symm_apply a, e.apply_symm_apply b] at h
    rw [h]
    simp only [CartanMatrix.B, Matrix.of_apply, Specs.TypeCSplitRecognition.cartanEntry,
      Nat.add_sub_cancel]
    by_cases hab : a = b
    · subst b
      simp
    by_cases hf : a.val + 1 = b.val
    · simp [hab, Ne.symm hab, hf]
    by_cases hr : b.val + 1 = a.val
    · have hb : b.val ≠ n := by omega
      simp [hab, Ne.symm hab, hf, hr, hb]
    · simp [hab, Ne.symm hab, hf, hr]

private theorem strongApproximationTypeG2 {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (c : Cocharacter G.val) (hc : IsNoncentral c)
    (P : SplitBorelPair (AlgebraicClosure K)) (hP : P.G = GeometricGroup G)
    (E : AttachedDatum P)
    (ht : letI := E.comm; HasDynkinType (RootData.integralCartan E.datum.rootDatum E.base) .G2)
    (S : Finset D.Place) (hS : S.Nonempty) : AdelicGroups.StrongApproximation D i S := by
  letI := E.comm
  change ∃ e : E.toBased.base.support ≃ Fin 2,
    ∀ a b, E.toBased.datum.pairing b.val a.val = CartanMatrix.G₂ (e a) (e b) at ht
  obtain ⟨e, he⟩ := ht
  have hType : Specs.OctonionForms.IsAbsoluteG2 G := by
    refine ⟨hG.1, P, hP, E, e.symm, fun a b => ?_⟩
    have h := he (e.symm a) (e.symm b)
    rw [e.apply_symm_apply a, e.apply_symm_apply b] at h
    exact h
  exact OctonionForms.isotropicG2StrongApproximation G hType
    (positiveRankOfNoncentralCocharacter G hG.1 c hc) D i S hS

private theorem strongApproximationTypeF4 {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (c : Cocharacter G.val) (hc : IsNoncentral c)
    (P : SplitBorelPair (AlgebraicClosure K)) (hP : P.G = GeometricGroup G)
    (E : AttachedDatum P)
    (ht : letI := E.comm; HasDynkinType (RootData.integralCartan E.datum.rootDatum E.base) .F4)
    (S : Finset D.Place) (hS : S.Nonempty) : AdelicGroups.StrongApproximation D i S :=
  StrongApproximationF4.strongApproximation G ⟨hG.1, P, hP, E, ht⟩ D i S hS
    (omittedProductNoncompactOfPositiveRank D G i hG
      (positiveRankOfNoncentralCocharacter G hG.1 c hc) S hS)


section BasedData

open Specs.Pinning (BasedIso PinnedGroup)
open Specs.RootGroups (AdditiveLine)
open Specs.RelativeFormComparison (fieldTest transportedAut)
open Specs.AutomorphismSequence (relativePoints SplitSequence)
open Specs.IntegralSemisimpleModel (fibre)
open private basedIsoOfScalarExtension basedIsoOfGroupIso
  from LinearAlgebraicGroups.Arithmetic.TypeCSplitRecognition
open private type_of_based_iso from LinearAlgebraicGroups.Arithmetic.OddSpinModels
open private groupBaseChangeTower from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private fibreTowerIso from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private schemeIsoEquiv schemeIsoEquiv_apply
  from LinearAlgebraicGroups.Descent.RelativeFormComparison
open private basedIso_base_iff from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private fixedVectorVertex from LinearAlgebraicGroups.Arithmetic.TrialitarianLocalForms
open private sepClosedBorelPair sepClosedBorelPair_group from LinearAlgebraicGroups.Arithmetic.OctonionForms

private theorem separablePairOfGeometricType {K : Type u} [Field K]
    (G : AffineAlgebraicGroup K) (hG : IsSemisimple G)
    (t : FiniteDynkinType)
    (P : SplitBorelPair (AlgebraicClosure K)) (hP : P.G = GeometricGroup G)
    (E : AttachedDatum P)
    (ht : letI := E.comm; HasDynkinType (RootData.integralCartan E.datum.rootDatum E.base) t) :
    ∃ (Q : SplitBorelPair (SeparableClosure K))
      (_ : Q.G = baseChangedAlgebraicGroup (SeparableClosure K) G) (C : AttachedDatum Q),
        letI := C.comm; HasDynkinType (RootData.integralCartan C.datum.rootDatum C.base) t := by
  let S := SeparableClosure K
  let L := AlgebraicClosure K
  obtain ⟨Q, hQ⟩ := TypeCSplitRecognition.separableBorelPair (S := S) G
    (reductive_of_semisimple G hG)
  let C := Classification.Pinning.attachedDatum Q
  let q : Q.G.val ≅ (groupBaseChange K S).obj G.val := eqToIso (congrArg Subtype.val hQ)
  let p : (groupBaseChange K L).obj G.val ≅ P.G.val := eqToIso (congrArg Subtype.val hP.symm)
  let f : (groupBaseChange S L).obj Q.G.val ≅ P.G.val :=
    (groupBaseChange S L).mapIso q ≪≫ ((groupBaseChangeTower (K := S) L).app G.val).symm ≪≫ p
  obtain ⟨d⟩ := basedIsoOfScalarExtension Q C P E f
  exact ⟨Q, hQ, C, type_of_based_iso d ht⟩

private theorem splitReferenceOfGeometricType {K : Type u} [Field K]
    (G : AffineAlgebraicGroup K) (hG : IsSemisimple G) (t : FiniteDynkinType)
    (P : SplitBorelPair (AlgebraicClosure K)) (hP : P.G = GeometricGroup G)
    (E : AttachedDatum P)
    (ht : letI := E.comm; HasDynkinType (RootData.integralCartan E.datum.rootDatum E.base) t) :
    ∃ (A : AdditiveLine K) (R : PinnedGroup A) (B : AttachedDatum R.pair),
      Nonempty ((groupBaseChange K (SeparableClosure K)).obj R.pair.G.val ≅
        (groupBaseChange K (SeparableClosure K)).obj G.val) ∧
      (letI := B.comm; HasDynkinType (RootData.integralCartan B.datum.rootDatum B.base) t) := by
  let S := SeparableClosure K
  obtain ⟨Q, hQ, C, hC⟩ := separablePairOfGeometricType G hG t P hP E ht
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization C.toBased
  obtain ⟨A, X, k, _⟩ := M.fieldFibre K
  obtain ⟨_, Y, s, _⟩ := M.fieldFibre S
  obtain ⟨e⟩ := ((Classification.PinnedEquivalence.pinnedEquivalence.2 S).2.1
    Q Y.pinned.pair C Y.attached).mpr ⟨Y.datumIso.val⟩
  let q : Q.G.val ≅ (groupBaseChange K S).obj G.val := eqToIso (congrArg Subtype.val hQ)
  refine ⟨A, X.pinned, X.attached, ⟨?_⟩, ?_⟩
  · exact (groupBaseChange K S).mapIso k.symm ≪≫ ((fibreTowerIso K S).app M.group).symm ≪≫
      s ≪≫ e.symm ≪≫ q
  · let d : BasedIso X.attached.toBased C.toBased :=
      Groupoid.inv (show C.toBased ⟶ X.attached.toBased from X.datumIso)
    exact type_of_based_iso d hC

private theorem geometricTypeAfterExtension {K F : Type u} [Field K] [Field F] [Algebra K F]
    (G : AffineAlgebraicGroup K) (hG : IsAbsolutelyAlmostSimple G) (t : FiniteDynkinType)
    (P : SplitBorelPair (AlgebraicClosure K)) (hP : P.G = GeometricGroup G)
    (E : AttachedDatum P)
    (ht : letI := E.comm; HasDynkinType (RootData.integralCartan E.datum.rootDatum E.base) t) :
    Specs.ExceptionalCompletionGeometry.HasAbsoluteType (baseChangedAlgebraicGroup F G) t := by
  let L := AlgebraicClosure K
  let M := AlgebraicClosure F
  let a : L →ₐ[K] M := IsAlgClosed.lift
  letI : Algebra L M := a.toRingHom.toAlgebra
  letI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' a.comp_algebraMap.symm
  let H := baseChangedAlgebraicGroup F G
  have hs : IsSemisimple (GeometricGroup H) :=
    (OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := M) H
      (OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G hG)).1
  let hR := reductive_of_semisimple (GeometricGroup H) hs
  let Q := sepClosedBorelPair (GeometricGroup H) hR
  have hQ : Q.G = GeometricGroup H := sepClosedBorelPair_group _ hR
  let C := Classification.Pinning.attachedDatum Q
  let p : P.G.val ≅ (groupBaseChange K L).obj G.val := eqToIso (congrArg Subtype.val hP)
  let q : (groupBaseChange F M).obj H.val ≅ Q.G.val := eqToIso (congrArg Subtype.val hQ.symm)
  let e : (groupBaseChange L M).obj P.G.val ≅ Q.G.val :=
    (groupBaseChange L M).mapIso p ≪≫ ((groupBaseChangeTower (K := L) M).app G.val).symm ≪≫
      (groupBaseChangeTower (K := F) M).app G.val ≪≫ q
  obtain ⟨d⟩ := basedIsoOfScalarExtension P E Q C e
  let d' : BasedIso C.toBased E.toBased := Groupoid.inv (show E.toBased ⟶ C.toBased from d)
  exact ⟨Q, hQ, C, type_of_based_iso d' ht⟩


private def diagramPermutation {B : Specs.Pinning.BasedRootDatum.{u}} {n : ℕ}
    (s : Fin n ≃ B.base.support) (a : Aut B) : Equiv.Perm (Fin n) :=
  (s.trans (a.asIso.hom.val.indexEquiv.subtypeEquiv (basedIso_base_iff a.asIso.hom))).trans s.symm

private theorem diagramPermutation_apply {B : Specs.Pinning.BasedRootDatum.{u}} {n : ℕ}
    (s : Fin n ≃ B.base.support) (a : Aut B) (i : Fin n) :
    (s (diagramPermutation s a i)).val = a.asIso.hom.val.indexEquiv (s i).val := by
  simp [diagramPermutation]

private theorem strongApproximationTypeD {K : Type u} [Field K]
    (hD : Specs.Arithmetic.StrongApproximationNontrialitarianD.StrongApproximationNontrialitarian.{u,v})
    (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (hiso : ∃ c : Cocharacter G.val, IsNoncentral c)
    (P : SplitBorelPair (AlgebraicClosure K)) (hP : P.G = GeometricGroup G)
    (E : AttachedDatum P) (n : ℕ) (hn : 4 ≤ n)
    (ht : letI := E.comm; HasDynkinType (RootData.integralCartan E.datum.rootDatum E.base) (.D n hn))
    (S : Finset D.Place) (hS : S.Nonempty) : AdelicGroups.StrongApproximation D i S := by
  classical
  let L := SeparableClosure K
  obtain ⟨A, R, B, ⟨e⟩, hB⟩ := splitReferenceOfGeometricType G hG.1 (.D n hn) P hP E ht
  obtain ⟨C, l, J, seq, _⟩ := Descent.AutomorphismSequence.automorphismSequence R
  obtain ⟨d⟩ := basedIsoOfGroupIso R.pair R.pair C B (Iso.refl _)
  have hC := type_of_based_iso d hB
  change ∃ s : C.toBased.base.support ≃ Fin n, ∀ a b,
    C.toBased.datum.pairing b.val a.val = CartanMatrix.D n (s a) (s b) at hC
  obtain ⟨s, hs⟩ := hC
  let r := schemeIsoEquiv L R.pair.G.val G.val e
  have hr := schemeIsoEquiv_apply e
  have hc (a b : Fin n) : C.toBased.datum.pairing (s.symm b).val (s.symm a).val =
      CartanMatrix.D n a b := by
    rw [hs, s.apply_symm_apply, s.apply_symm_apply]
  have hnoncompact : ¬ CompactSpace (FinitePoints D i S) := by
    obtain ⟨c, h⟩ := hiso
    exact omittedProductNoncompactOfPositiveRank D G i hG
      (positiveRankOfNoncentralCocharacter G hG.1 c h) S hS
  have applyFixed : Specs.Arithmetic.NontrialitarianSpinModels.HasFixedVectorVertex G n →
      AdelicGroups.StrongApproximation D i S :=
    fun h => hD D G n hn (absoluteAlmostSimpleForClassification G hG) hsc h i S hS hnoncompact
  by_cases heq : n = 4
  · subst n
    let T : Specs.Arithmetic.TrialitarianLocalForms.D4Diagram G :=
      ⟨A, R, C, l, J, seq, e, r, hr, s.symm, hc⟩
    by_cases h : T.IsTransitive
    · exact TrialitarianLocalForms.globalStrongApproximation D G hG.1 hsc ⟨T, h⟩ hiso i S hS
    · exact applyFixed (fixedVectorVertex T h)
  · have h5 : 5 ≤ n := by omega
    have hn0 : 0 < n := by omega
    let zero : Fin n := ⟨0, hn0⟩
    apply applyFixed
    refine ⟨A, R, C, l, J, seq, e, r, s.symm, zero, hr, hc, by simp [heq, zero], ?_⟩
    intro σ
    let a := (Specs.QuasiSplitInnerForms.outerHom seq (transportedAut K L r σ))
    let p := diagramPermutation s.symm a
    have hp : PreservesCartan (CartanMatrix.D n) (CartanMatrix.D n) p := by
      intro j k
      rw [← hc, ← hc, diagramPermutation_apply, diagramPermutation_apply]
      exact a.asIso.hom.val.toHom.pairing.symm
    have hp0 : p zero = zero := by
      rcases (RootData.AbsoluteDynkinTypes.typeDPermutations n h5 p).mp hp with h | h
      · rw [h]; rfl
      · rw [h, Equiv.swap_apply_of_ne_of_ne] <;> intro h' <;>
          have hh := congrArg Fin.val h' <;> simp [zero] at hh <;> omega
    change a.asIso.hom.val.indexEquiv (s.symm zero).val = (s.symm zero).val
    rw [← diagramPermutation_apply, hp0]

section TypeA

open Opposite
open scoped TensorProduct
open LinearAlgebraicGroups.Specs (GroupScheme)
open Specs.OuterTypeAModels (HasAbsoluteSimplyConnectedTypeA RepresentsNormOne)
open Specs.Arithmetic.IsotropicNormOneRadicalsDensity (DensityOver)
open LinearAlgebraicGroups.UnitaryNormEquations (factorReducedNorm factorScalarExtension)
open _root_.Specs.RM03.CSA (isCentralSimple)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)
open private density_over_completion from LinearAlgebraicGroups.Arithmetic.IsotropicNormOneRadicalsDensity
open private finiteTrivialization from LinearAlgebraicGroups.Arithmetic.OctonionForms
open private specialMatrixModel representsNormOneOfPoints
  from LinearAlgebraicGroups.Arithmetic.OuterTypeAModels
open private extendMatrixPoints from LinearAlgebraicGroups.Arithmetic.TypeAMatrixDescentData
open private baseChangePointIso from LinearAlgebraicGroups.Descent.InnerTypeA
open private rankOneNormModel normGroupPoints from LinearAlgebraicGroups.Arithmetic.RankOneOddDescent

private theorem normModelAfterExtension {K F A I : Type u} [Field K] [Field F] [Algebra K F]
    [Ring A] [Algebra K A] [Fintype I] (hA : isCentralSimple K A) (b : Module.Basis I K A)
    (G : AffineAlgebraicGroup K) (h : RepresentsNormOne hA b G) :
    ∃ hF : isCentralSimple F (F ⊗[K] A),
      RepresentsNormOne hF (b.baseChange F) (baseChangedAlgebraicGroup F G) := by
  obtain ⟨hF, _, _⟩ := factorReducedNorm (L := F) (R := F) hA b
  obtain ⟨p, hp, hn⟩ := h
  let H := baseChangedAlgebraicGroup F G
  let cmp : (groupPointsFunctor F).obj H.val ≅
      restrictTestAlgebra K F ⋙ (groupPointsFunctor K).obj G.val := baseChangePointIso G.val
  let T (R : TestAlgebra F) := restrictTestAlgebraObj K F R
  let d (R : TestAlgebra F) : T R ⊗[K] A ≃ₐ[R] R ⊗[F] (F ⊗[K] A) :=
    factorScalarExtension (E := K) (L := F) (R := T R)
  have hd (R : TestAlgebra F) (x : T R ⊗[K] A) :
      normAt hF (b.baseChange F) (d R x) = normAt hA b x := by
    obtain ⟨_, _, h⟩ := factorReducedNorm (L := F) (R := T R) hA b
    exact h x
  let q (R : TestAlgebra F) : Points H.val.X R ≃
      {x : R ⊗[F] (F ⊗[K] A) // normAt hF (b.baseChange F) x = 1} :=
    (cmp.app R).groupIsoToMulEquiv.toEquiv.trans ((p (T R)).trans
      ((d R).toEquiv.subtypeEquiv fun x => (hd R x).symm ▸ Iff.rfl))
  have hq (R : TestAlgebra F) (x : Points H.val.X R) :
      (q R x).val = d R (p (T R) (cmp.hom.app R x)).val := rfl
  refine ⟨hF, q, ?_, ?_⟩
  · intro R x y
    change (q R (x * y)).val = (q R x).val * (q R y).val
    have hxy : cmp.hom.app R (x * y) = cmp.hom.app R x * cmp.hom.app R y :=
      map_mul (cmp.hom.app R).hom x y
    rw [hq, hxy, hp, map_mul, hq, hq]
  · intro R S f x
    let f₀ := (restrictTestAlgebra K F).map f
    have hx := NatTrans.naturality_apply cmp.hom f x
    change cmp.hom.app S (mapPoints (X := H.val.X) f x) =
      mapPoints (X := G.val.X) f₀ (cmp.hom.app R x) at hx
    have hdmap (y : T R ⊗[K] A) :
        d S (Algebra.TensorProduct.map f₀.hom (.id K A) y) =
          Algebra.TensorProduct.map f.hom (.id F (F ⊗[K] A)) (d R y) := by
      induction y using TensorProduct.inductionOn with
      | tmul r a => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]; rfl
      | add y z hy hz => simp only [map_add, hy, hz]
    change (q S (mapPoints f x)).val = _
    rw [hq, hx, hq, hn]
    exact hdmap _

private theorem strongApproximationNormModel {K A I : Type u} [Field K] [Ring A]
    [Algebra K A] [Fintype I] (hA : isCentralSimple K A) (b : Module.Basis I K A)
    (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (h : RepresentsNormOne hA b G)
    (c : Cocharacter G.val) (hc : IsNoncentral c) (S : Finset D.Place) (hS : S.Nonempty) :
    AdelicGroups.StrongApproximation D i S := by
  obtain ⟨P⟩ := existsLimitDecomposition G c
  obtain ⟨Q⟩ := existsLimitDecomposition G (oppositeCocharacter c)
  apply ((OppositeRadicals.approximation D G i hG c hc P Q).2.2.2.2 S hS).2
  intro w
  let F := D.Completion w.1
  obtain ⟨hF, hM⟩ := normModelAfterExtension (F := F) hA b G h
  obtain ⟨e, _, hc', _⟩ := OppositeRadicals.localGeneration D G i hG c hc P Q w.1
  exact IsotropicNormOneRadicalsDensity.completionDensityTransfer D G i w.1
    (density_over_completion D w.1) hF (b.baseChange F) hM
    ⟨e.hom ≫ (groupBaseChange K F).map c, hc'⟩

private theorem finiteGaloisSplitComparison {K : Type u} [Field K]
    (G H : AffineAlgebraicGroup K) (h : Specs.AutomorphismSequence.IsSeparableForm G H) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (_ : IsGalois K L),
      Nonempty ((groupBaseChange K L).obj G.val ≅ (groupBaseChange K L).obj H.val) := by
  obtain ⟨S, _, _, _, ⟨j⟩⟩ := h
  obtain ⟨L, ⟨e⟩⟩ := finiteTrivialization G H S j
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨(schemeIsoEquiv L G.val H.val).symm e⟩⟩

private theorem absoluteTypeAOfGeometricType {K : Type u} [Field K]
    (G : AffineAlgebraicGroup K) (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G)
    (P : SplitBorelPair (AlgebraicClosure K)) (hP : P.G = GeometricGroup G)
    (E : AttachedDatum P) (n : ℕ) (hn : 1 ≤ n)
    (ht : letI := E.comm; HasDynkinType (RootData.integralCartan E.datum.rootDatum E.base) (.A n hn)) :
    HasAbsoluteSimplyConnectedTypeA n G := by
  let L := SeparableClosure K
  obtain ⟨Q, hQ, B, hB⟩ := separablePairOfGeometricType G hG (.A n hn) P hP E ht
  have hs : IsSemisimple Q.G := hQ.symm ▸
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := L) G hG.1 hG.2.1).mpr hG
  have hscQ : GeometricallySimplyConnected Q.G := hQ.symm ▸
    QuasiSplitApproximation.simplyConnectedFieldExtension (F := L) hG hsc
  letI := B.comm
  change ∃ e : B.toBased.base.support ≃ Fin n, ∀ i j,
    B.toBased.datum.pairing j.val i.val = CartanMatrix.A n (e i) (e j) at hB
  obtain ⟨e, he⟩ := hB
  refine ⟨L, inferInstance, inferInstance, inferInstance, Q, hQ, hs, hscQ, B, e.symm, fun i j => ?_⟩
  have h := he (e.symm j) (e.symm i)
  rw [e.apply_symm_apply, e.apply_symm_apply] at h
  rw [h]
  simp only [CartanMatrix.A, Matrix.of_apply, eq_comm (a := j) (b := i), or_comm]

private theorem strongApproximationTypeA {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (c : Cocharacter G.val) (hc : IsNoncentral c)
    (P : SplitBorelPair (AlgebraicClosure K)) (hP : P.G = GeometricGroup G)
    (E : AttachedDatum P) (n : ℕ) (hn : 1 ≤ n)
    (ht : letI := E.comm; HasDynkinType (RootData.integralCartan E.datum.rootDatum E.base) (.A n hn))
    (S : Finset D.Place) (hS : S.Nonempty) : AdelicGroups.StrongApproximation D i S := by
  have hA := absoluteTypeAOfGeometricType G hG.1 hsc P hP E n hn ht
  by_cases h : 2 ≤ n
  · obtain ⟨R, s, L, _, _, _, _, e, χ, g, β, hM, _, _, _, _, hχ, hModels⟩ :=
      LinearAlgebraicGroups.OuterTypeAModels.absoluteTypeAForms h G hA
    rcases hχ with hχ | hχ
    · obtain ⟨ρ, _, hZ, _, I, _, b, hNorm⟩ := hModels.1 hχ
      exact strongApproximationNormModel hZ b D G i hG hNorm c hc S hS
    · exact IsotropicOuterTypeA.outerTypeAStrongApproximation D G hG
        ⟨n, h, hA, R, s, L, inferInstance, inferInstance, inferInstance, inferInstance, e, χ, g, hχ, hM⟩
        ⟨c, hc⟩ i S hS
  · have hn : n = 1 := by omega
    subst n
    obtain ⟨R, ⟨s⟩⟩ := specialMatrixModel K 2
    obtain ⟨L, _, _, _, _, ⟨e⟩⟩ := finiteGaloisSplitComparison R G
      (LinearAlgebraicGroups.OuterTypeAModels.absoluteTypeAMatrixForm s hA)
    let sL := extendMatrixPoints (K := L) s
    let e' := baseChangePointIso (K := L) G.val
    let z := e'.symm ≪≫ (groupPointsFunctor L).mapIso e.symm ≪≫ sL
    obtain ⟨A, I, _, _, _, hZ, b, _, ⟨f⟩⟩ := rankOneNormModel G z
    have hNorm := representsNormOneOfPoints hZ b (H := G)
      ((groupPointsFunctor K).mapIso f.symm ≪≫ normGroupPoints hZ b)
    exact strongApproximationNormModel hZ b D G i hG hNorm c hc S hS

end TypeA


section Exceptional

open MonoidalCategory CartesianMonoidalCategory Opposite
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.ExceptionalLocalRadicalGeneration (HasAbsoluteTypeE LocalRadicalGeneration localPointTopology)
open Specs.ExceptionalMarkedRootDescent (coordinatePointEquiv)
open Specs.Arithmetic.ProjectiveRecurrence (cocharacterRadicalPoints localPointSet)
open Specs.QuasiSplitOrbitAmbientWords (groundPointIso)
open private matrixPresentation coordinateMap_of_map from LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private glEvaluation_entry from LinearAlgebraicGroups.Affine.StandardGroups
open Specs.StandardGroups (universalMatrix)
open private coordinateMap from LinearAlgebraicGroups.Arithmetic.IntegralModels
open private radicalClosure_subset_localPlus from LinearAlgebraicGroups.Arithmetic.StrongApproximationF4
open private cocharacterRadicals_are_parabolic splitContractingGeneration
  from LinearAlgebraicGroups.Arithmetic.ExceptionalAdelicApproximation
open private realCompletionProperties from LinearAlgebraicGroups.Arithmetic.ExceptionalRealPoints

private theorem exceptionalCartanComparison (t : FiniteDynkinType)
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) (a b : Fin t.rank) :
    t.cartan b a = Specs.ExceptionalAffineRootSystems.exceptionalCartan t.rank a b := by
  rcases ht with rfl | rfl | rfl
  all_goals
    revert a b
    decide

private theorem absoluteTypeEOfGeometricType {F : Type u} [Field F]
    (G : AffineAlgebraicGroup F) (hG : IsSemisimple G) (t : FiniteDynkinType)
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hType : Specs.ExceptionalCompletionGeometry.HasAbsoluteType G t) :
    HasAbsoluteTypeE G t.rank := by
  obtain ⟨P, hP, E, hE⟩ := hType
  obtain ⟨Q, hQ, C, hC⟩ := separablePairOfGeometricType G hG t P hP E hE
  letI := C.comm
  change ∃ s : C.toBased.base.support ≃ Fin t.rank, ∀ a b,
    C.toBased.datum.pairing b.val a.val = t.cartan (s a) (s b) at hC
  obtain ⟨s, hs⟩ := hC
  refine ⟨Q, C, s.symm, ⟨eqToIso (congrArg Subtype.val hQ)⟩, fun a b => ?_⟩
  rw [hs, s.apply_symm_apply, s.apply_symm_apply]
  exact exceptionalCartanComparison t ht a b

private theorem continuousCoordinateSections {F : Type u} [Field F]
    [TopologicalSpace F] (G : AffineAlgebraicGroup F) (i : MatrixRealization G) :
    letI := localPointTopology G
    Continuous (fun x : (𝟙_ (SchemeOver F) ⟶ G.val.X) =>
      (show PointsIn i F from (groundPointIso F).inv ≫ x)) := by
  letI := localPointTopology G
  let A := Specs.AdjointCocharacters.coordinateHopf G
  let R := CommAlgCat.of F F
  let Z := (𝟙_ (SchemeOver F) ⟶ G.val.X)
  let f : Z → PointsIn i F := fun x => (groundPointIso F).inv ≫ x
  let b := coordinatePointEquiv G R
  let e : (testSpec F).obj (op (CommAlgCat.of F A)) ≅ G.val.X :=
    ((Grp.forget (SchemeOver F)).mapIso (Specs.AdjointCocharacters.coordinateHopfIso G))
  obtain ⟨a, _, ha⟩ := matrixPresentation (CommAlgCat.of F A) e i
  let g : Z → (A →ₐ[F] F) := fun x => (b.symm (f x)).ofConv
  letI := Specs.ExceptionalIwahoriCongruence.affinePointTopology F A F
  have hg (z : A) : Continuous (fun x => g x z) :=
    (continuous_apply z).comp (continuous_induced_dom.comp continuous_induced_dom)
  have hcoord (p : PointsIn i F) :
      (coordinateMap (k := F) (p ≫ e.inv)).hom = (b.symm p).ofConv := by
    let h := CommAlgCat.ofHom (b.symm p).ofConv
    have hp : p = (testSpec F).map h.op ≫ e.hom := by
      change p = b (b.symm p)
      exact (b.apply_symm_apply p).symm
    conv_lhs => rw [hp, Category.assoc, Iso.hom_inv_id, Category.comp_id, coordinateMap_of_map]
    rfl
  have hentry (x : PointsIn i F) (r s : Specs.Unipotent.Index.{u} i.size) :
      (asMatrix i F x).val r s = (b.symm x).ofConv
        (a.hom (universalMatrix F _ r s)) := by
    have h := DFunLike.congr_fun (ha F x) (universalMatrix F _ r s)
    rw [glEvaluation_entry] at h
    exact h.trans (congrArg (fun q : A →ₐ[F] F => q (a.hom (universalMatrix F _ r s))) (hcoord x))
  change Continuous f
  apply continuous_induced_rng.mpr
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_matrix
    intro r s
    change Continuous (fun x : Z => (asMatrix i F (f x)).val r s)
    simp_rw [hentry]
    exact hg _
  · apply continuous_matrix
    intro r s
    change Continuous (fun x => ((asMatrix i F (f x))⁻¹).val r s)
    simp_rw [← map_inv, hentry, map_inv]
    change Continuous (fun x => g x (HopfAlgebra.antipodeAlgHom F A _))
    exact hg _

private theorem denseLocalPlusFromCoordinateSections {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K) (i : MatrixRealization G) (w : D.Place)
    (hd : let F := D.Completion w
      let H := baseChangedAlgebraicGroup F G
      letI := localPointTopology H
      Dense (unipotentGenerated H : Set (𝟙_ (SchemeOver F) ⟶ H.val.X))) :
    Dense (localPlus D i w) := by
  let F := D.Completion w
  let H := baseChangedAlgebraicGroup F G
  letI := localPointTopology H
  obtain ⟨_, j, _, e, he, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison K F G i
  let f : (𝟙_ (SchemeOver F) ⟶ H.val.X) → PointsIn j F := fun x => (groundPointIso F).inv ≫ x
  have hf : Function.Surjective f := by
    intro y
    exact ⟨(groundPointIso F).hom ≫ y, (groundPointIso F).inv_hom_id_assoc y⟩
  have hc := e.continuous.comp (continuousCoordinateSections H j)
  apply ((e.surjective.comp hf).denseRange.dense_image hc hd).mono
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨p, hp, ?_⟩
  apply Over.OverMorphism.ext
  have hu : toUnit ((testSpec F).obj (op (CommAlgCat.of F F))) = (groundPointIso F).inv :=
    toUnit_unique _ _
  rw [hu]
  exact (he (f p)).symm

set_option maxHeartbeats 2500000 in
private theorem exceptionalFiniteDensity {K : Type u} [Field K]
    (hLocal : LocalRadicalGeneration.{u})
    (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (t : FiniteDynkinType) (ht : t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hType : Specs.ExceptionalCompletionGeometry.HasAbsoluteType G t)
    (w : D.FinitePlace) : Dense (localPlus D i (.inl w)) := by
  let F := D.FiniteCompletion w
  letI : ValuativeRel F := GlobalFieldData.instValuativeRelFiniteCompletion D w
  letI : IsNonarchimedeanLocalField F := GlobalFieldData.finiteCompletion_isLocalField D w
  letI : Algebra K F := completionAlgebra D (.inl w)
  let H := baseChangedAlgebraicGroup F G
  have hH : IsAbsolutelyAlmostSimple H :=
    OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G hG
  have hHsc : GeometricallySimplyConnected H :=
    QuasiSplitApproximation.simplyConnectedFieldExtension (F := F) hG.1 hsc
  obtain ⟨P, hP, E, hE⟩ := hType
  have hTypeH := geometricTypeAfterExtension (F := F) G hG t P hP E hE
  have hE' := absoluteTypeEOfGeometricType H hH.1 t ht hTypeH
  have hTypes : HasAbsoluteTypeE H 6 ∨ HasAbsoluteTypeE H 7 ∨ HasAbsoluteTypeE H 8 := by
    rcases ht with rfl | rfl | rfl
    · exact Or.inl hE'
    · exact Or.inr (Or.inl hE')
    · exact Or.inr (Or.inr hE')
  have hDensity : letI := localPointTopology H
      Dense (unipotentGenerated H : Set (𝟙_ (SchemeOver F) ⟶ H.val.X)) :=
    (hLocal F H hH hHsc hTypes).2
  exact denseLocalPlusFromCoordinateSections D G i (Sum.inl w) hDensity

private theorem exceptionalInfiniteDensity {K : Type u} [Field K] [hK : NumberField K]
    (D : GlobalFieldData.{u,v} K) (hD : D = .number hK)
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (hr : 0 < relativeRank G) (hType : Specs.ExceptionalRealPoints.HasAbsoluteExceptionalType G)
    (w : D.InfinitePlace) : Dense (localPlus D i (.inr w)) := by
  subst D
  let D : GlobalFieldData.{u,v} K := .number hK
  let p : D.Place := .inr w
  let F := D.Completion p
  letI : Field F := GlobalFieldData.instFieldCompletion D p
  letI : TopologicalSpace F := GlobalFieldData.instTopologicalSpaceCompletion D p
  letI : Algebra K F := completionAlgebra D p
  let H := baseChangedAlgebraicGroup F G
  have hH : IsSemisimple H :=
    (OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G hG).1
  have hHsc : GeometricallySimplyConnected H :=
    QuasiSplitApproximation.simplyConnectedFieldExtension (F := F) hG.1 hsc
  refine Dense.mono (radicalClosure_subset_localPlus D i p) ?_
  rcases w.isReal_or_isComplex with hw | hw
  · have hd := (realCompletionProperties G i hG hsc hType w hw).2
      (localNoncompactOfPositiveRank D G i hG hr p)
    exact hd.mono (Subgroup.closure_mono (by
      rintro _ ⟨q, hq, h⟩
      exact ⟨q, cocharacterRadicals_are_parabolic hH hq, h⟩))
  · have hsplit := ExceptionalRealPoints.complexCompletionsSplit G hG hsc hType w hw
    have hgen := splitContractingGeneration H hH hHsc hsplit
    let b : Specs.IntegralModels.RationalPoints H ≃* LocalPoints D i p :=
      baseChangePointGroupEquiv F G.val (CommAlgCat.of F F)
    have himage : b.toMonoidHom '' cocharacterRadicalPoints H ⊆
        localPointSet D i p (Specs.Arithmetic.ProjectiveRecurrence.parabolicRadicalPoints H) := by
      rintro _ ⟨q, hq, rfl⟩
      exact ⟨q, cocharacterRadicals_are_parabolic hH hq, rfl⟩
    apply dense_univ.mono
    intro g _
    obtain ⟨q, rfl⟩ := b.surjective g
    have h := Subgroup.mem_map_of_mem b.toMonoidHom (hgen.symm ▸ Subgroup.mem_top q)
    rw [MonoidHom.map_closure] at h
    exact Subgroup.closure_mono himage h

private theorem strongApproximationExceptional {K : Type u} [Field K]
    (hLocal : LocalRadicalGeneration.{u})
    (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (c : Cocharacter G.val) (hc : IsNoncentral c)
    (t : FiniteDynkinType) (ht : t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hType : Specs.ExceptionalCompletionGeometry.HasAbsoluteType G t)
    (S : Finset D.Place) (hS : S.Nonempty) : AdelicGroups.StrongApproximation D i S := by
  apply strongApproximationOfLocalDensity D G i hG c hc S hS
  rintro ⟨w | w, _⟩
  · exact exceptionalFiniteDensity hLocal D G i hG hsc t ht hType w
  · cases D with
    | function C q => exact w.elim
    | number h =>
      letI : NumberField K := h
      exact exceptionalInfiniteDensity (.number h) rfl G i hG hsc
        (positiveRankOfNoncentralCocharacter G hG.1 c hc) ⟨t, ht, hType⟩ w


end Exceptional


end BasedData

/-- The isotropic sufficiency argument with its three frozen upstream premises. -/
theorem strongApproximation_conditional
    (_hLevis : Specs.ExceptionalLocalRadicalGeneration.ExceptionalRootSystemsAndLevis.{u})
    (hLocal : Specs.ExceptionalLocalRadicalGeneration.LocalRadicalGeneration.{u})
    (hD : Specs.Arithmetic.StrongApproximationNontrialitarianD.StrongApproximationNontrialitarian.{u,v}) :
    Specs.Arithmetic.IsotropicSufficiency.IsotropicStrongApproximation.{u,v} := by
  intro K _ D G i hG hsc hIso S hS
  obtain ⟨c, hc⟩ := hIso
  by_cases hq : Specs.GeometricBorelConjugacy.IsQuasiSplit G
  · exact QuasiSplitApproximation.strongApproximationForQuasiSplitGroups D G i hG.1 hsc hq S hS
  let A := Classification.Pinning.standardAdditiveLine (AlgebraicClosure K)
  obtain ⟨P, hP, _, _, E, hE⟩ := RootData.AbsoluteDynkinTypes.absoluteClassification G
    (absoluteAlmostSimpleForClassification G hG) hsc A
  letI := E.comm
  obtain ⟨_, _, _, _, _, t, e, he, _, _⟩ := hE
  have ht : HasDynkinType (RootData.integralCartan E.datum.rootDatum E.base) t := ⟨e, he⟩
  cases t with
  | A n hn => exact strongApproximationTypeA D G i hG hsc c hc P hP E n hn ht S hS
  | B n hn => exact strongApproximationTypeB D G i hG hsc ⟨c, hc⟩ P hP E n hn ht S hS
  | C n hn => exact strongApproximationTypeC D G i hG hsc c hc P hP E n hn ht S hS
  | D n hn => exact strongApproximationTypeD hD D G i hG hsc ⟨c, hc⟩ P hP E n hn ht S hS
  | E6 =>
    exact strongApproximationExceptional hLocal D G i hG hsc c hc .E6 (Or.inl rfl)
      ⟨P, hP, E, ht⟩ S hS
  | E7 =>
    exact strongApproximationExceptional hLocal D G i hG hsc c hc .E7 (Or.inr (Or.inl rfl))
      ⟨P, hP, E, ht⟩ S hS
  | E8 =>
    exact strongApproximationExceptional hLocal D G i hG hsc c hc .E8 (Or.inr (Or.inr rfl))
      ⟨P, hP, E, ht⟩ S hS
  | F4 => exact strongApproximationTypeF4 D G i hG c hc P hP E ht S hS
  | G2 => exact strongApproximationTypeG2 D G i hG c hc P hP E ht S hS


end
end LinearAlgebraicGroups.Arithmetic.IsotropicSufficiency

universe v8_closure_a606a37e639a268a_u0 v8_closure_a606a37e639a268a_u1
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«IsotropicSufficiency».«strongApproximation» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«IsotropicSufficiency».«IsotropicStrongApproximation».{v8_closure_a606a37e639a268a_u0, v8_closure_a606a37e639a268a_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«IsotropicSufficiency».«strongApproximation_conditional».{v8_closure_a606a37e639a268a_u0, v8_closure_a606a37e639a268a_u1} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalLocalRadicalGeneration».«exceptionalRootSystemsAndLevis».{v8_closure_a606a37e639a268a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalLocalRadicalGeneration».«localRadicalGeneration».{v8_closure_a606a37e639a268a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«StrongApproximationNontrialitarianD».«strongApproximation».{v8_closure_a606a37e639a268a_u0, v8_closure_a606a37e639a268a_u1})
