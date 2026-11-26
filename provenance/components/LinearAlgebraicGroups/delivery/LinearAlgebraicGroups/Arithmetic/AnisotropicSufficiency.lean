import Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicSufficiency
import LinearAlgebraicGroups.Arithmetic.FunctionFieldAnisotropicCompactness
import LinearAlgebraicGroups.Arithmetic.InnerTypeASplitRank
import Specs.LinearAlgebraicGroups.Arithmetic.InnerTypeALocalGeneration
import LinearAlgebraicGroups.Arithmetic.ExceptionalCompletionGeometry
import LinearAlgebraicGroups.Arithmetic.ExceptionalCompletionMixingCases
import LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRadicalGeneration
import LinearAlgebraicGroups.Arithmetic.ExceptionalRealPoints
import LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
import LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure
import LinearAlgebraicGroups.Arithmetic.OddSpinModels
import LinearAlgebraicGroups.Arithmetic.OuterTypeAModels
import LinearAlgebraicGroups.Arithmetic.QuaternionSpinCharacteristicTwo
import LinearAlgebraicGroups.Arithmetic.StrongApproximationF4
import LinearAlgebraicGroups.Arithmetic.StrongApproximationNontrialitarianD
import LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
import LinearAlgebraicGroups.Arithmetic.TrialitarianArchimedeanGeneration
import LinearAlgebraicGroups.Arithmetic.TrialitarianCompletionMixingCases
import LinearAlgebraicGroups.Arithmetic.TrialitarianLocalForms
import LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Arithmetic.AnisotropicClassicalApproximation
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Set Topology
open scoped Classical RestrictedProduct TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option Elab.async false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

universe u v

namespace LinearAlgebraicGroups.Arithmetic.AnisotropicSufficiency

open AdelicGroups ArithmeticLatticeProjection CompactProductIsolation
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple HasDynkinType)
open Specs.Arithmetic.AnisotropicClassicalApproximation (GloballyAnisotropic)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (GeometricGroup IsSemisimple)
open Specs.IntegralModels (MatrixRealization)
open Specs.Pinning (SplitBorelPair AttachedDatum)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open LieAlgebrasAndRepresentations (FiniteDynkinType)

open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private basedIsoOfScalarExtension from LinearAlgebraicGroups.Arithmetic.TypeCSplitRecognition
open private type_of_based_iso from LinearAlgebraicGroups.Arithmetic.OddSpinModels
open private groupBaseChangeTower from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private sepClosedBorelPair sepClosedBorelPair_group
  from LinearAlgebraicGroups.Arithmetic.OctonionForms
open private simplyConnectedAfterBaseChange
  from LinearAlgebraicGroups.Arithmetic.LocalCompactnessCriterion

open private cocharacter_of_split_power empty_power_iso
  from LinearAlgebraicGroups.Descent.RelativeRank
open private noncentral_of_ne_zero
  from LinearAlgebraicGroups.Arithmetic.QuaternionSpinCharacteristicTwo
open private arithmetic_absolute_simplicity
  from LinearAlgebraicGroups.Arithmetic.QuaternionSpinCharacteristicTwo
open private numberCompactQuotient_iff compact_quotient_of_coordinate_formula
  from LinearAlgebraicGroups.Arithmetic.StrongApproximationF4

/-- A positive-dimensional closed split torus gives a noncentral cocharacter
in a semisimple group. -/
private theorem noPositiveSplitTorus {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (hG : IsSemisimple G) (ha : GloballyAnisotropic G) :
    Specs.FunctionFieldWeilGroupStructure.IsAnisotropic G := by
  rintro ⟨T, r, hr, ⟨e⟩⟩
  obtain ⟨c, hc⟩ := cocharacter_of_split_power hr e
  letI : Mono T.inclusion := by
    letI := T.isClosedImmersion
    exact CategoryTheory.Functor.mono_of_mono_map
      (Grp.forget (SchemeOver K)) (by
        change Mono T.inclusion.hom.hom
        exact Over.mono_of_mono_left _)
  exact ha ⟨c ≫ T.inclusion,
    noncentral_of_ne_zero G hG _ fun h => hc ((cancel_mono T.inclusion).mp (by
      simpa only [zero_comp] using h))⟩

/-- Compactness uses the same rational diagonal in either kind of global field. -/
theorem compactFullAdelicQuotient {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (hG : IsSemisimple G) (ha : GloballyAnisotropic G) :
    CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) := by
  have hT := noPositiveSplitTorus hG ha
  cases D with
  | number hK =>
    letI : NumberField K := hK
    have han : Specs.AnisotropicAdNilpotents.IsAnisotropic G.val := by
      intro T hsplit
      obtain ⟨r, ⟨e⟩⟩ := hsplit
      have hzero : r = 0 := by
        by_contra hr
        exact hT ⟨T, r, Nat.pos_of_ne_zero hr, ⟨e⟩⟩
      subst r
      exact ⟨e ≪≫ empty_power_iso⟩
    exact compact_quotient_of_coordinate_formula (.number hK) i
      ((numberCompactQuotient_iff.{u,0,v} i).mp
        (CharacteristicZeroCompactness.anisotropicAdelicCompactness G hG han i))
  | function F t =>
    exact FunctionFieldAnisotropicCompactness.functionFieldCompactness t G i hG hT

/-- Cartan type on the geometric group can be read from a Borel pair of
the separable scalar extension, with the same root and coroot coordinates. -/
private theorem existsSeparableCartan
    {K : Type u} [Field K] (G : AffineAlgebraicGroup K) (hs : IsSemisimple G)
    (t : FiniteDynkinType) (ht : Specs.ExceptionalCompletionGeometry.HasAbsoluteType G t) :
    ∃ (Q : SplitBorelPair (SeparableClosure K)) (B : AttachedDatum Q),
      Q.G = baseChangedAlgebraicGroup (SeparableClosure K) G ∧
      letI := B.comm
      HasDynkinType (RootData.integralCartan B.datum.rootDatum B.base) t := by
  obtain ⟨P, hP, A, hA⟩ := ht
  let S := SeparableClosure K
  let L := AlgebraicClosure K
  obtain ⟨Q, hQ⟩ := LinearAlgebraicGroups.TypeCSplitRecognition.separableBorelPair
    (S := S) G (reductive_of_semisimple G hs)
  let B := LinearAlgebraicGroups.Classification.Pinning.attachedDatum Q
  let a : Q.G.val ≅ (groupBaseChange K S).obj G.val := eqToIso (congrArg Subtype.val hQ)
  let b : (groupBaseChange K L).obj G.val ≅ P.G.val := eqToIso (congrArg Subtype.val hP.symm)
  let c := (groupBaseChange S L).mapIso a ≪≫ ((groupBaseChangeTower (K := S) L).app G.val).symm ≪≫ b
  obtain ⟨e⟩ := basedIsoOfScalarExtension Q B P A c
  exact ⟨Q, B, hQ, type_of_based_iso e hA⟩

/-- The absolute Cartan type is preserved by arbitrary ground-field extension. -/
private theorem absoluteCartan_fieldExtension {K F : Type u} [Field K] [Field F] [Algebra K F]
    (G : AffineAlgebraicGroup K) (hG : IsAbsolutelyAlmostSimple G)
    (t : FiniteDynkinType) (ht : Specs.ExceptionalCompletionGeometry.HasAbsoluteType G t) :
    Specs.ExceptionalCompletionGeometry.HasAbsoluteType (baseChangedAlgebraicGroup F G) t := by
  obtain ⟨P, hP, A, hA⟩ := ht
  let J := baseChangedAlgebraicGroup F G
  have hJ := OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G
    (arithmetic_absolute_simplicity hG)
  have hs : IsSemisimple (GeometricGroup J) :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension J hJ.1.1 hJ.1.2.1).mpr hJ.1
  let hR := reductive_of_semisimple (GeometricGroup J) hs
  let Q := sepClosedBorelPair (GeometricGroup J) hR
  have hQ : Q.G = GeometricGroup J := sepClosedBorelPair_group _ hR
  let B := LinearAlgebraicGroups.Classification.Pinning.attachedDatum Q
  obtain ⟨a, htower, ⟨e⟩⟩ :=
    ExceptionalCompletionGeometry.geometricScalarExtensionIso (K := F) G
  letI := a
  letI := htower
  let e₁ : P.G.val ≅ (GeometricGroup G).val := eqToIso (congrArg Subtype.val hP)
  let e₂ : (GeometricGroup J).val ≅ Q.G.val := eqToIso (congrArg Subtype.val hQ.symm)
  obtain ⟨f⟩ := basedIsoOfScalarExtension P A Q B ((groupBaseChange _ _).mapIso e₁ ≪≫ e ≪≫ e₂)
  exact ⟨Q, hQ, B, type_of_based_iso (Groupoid.inv (show A.toBased ⟶ B.toBased from f)) hA⟩

/-- The supplied nontrialitarian theorem applies with the original group,
matrix realization, and omitted places. -/
theorem ofFixedVectorVertex
    (hD : Specs.Arithmetic.StrongApproximationNontrialitarianD.StrongApproximationNontrialitarian.{u,v})
    {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    (G : AffineAlgebraicGroup K) (n : ℕ) (hn : 4 ≤ n)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (hv : Specs.Arithmetic.NontrialitarianSpinModels.HasFixedVectorVertex G n)
    (i : MatrixRealization G) (S : Finset D.Place)
    (hne : S.Nonempty) (hnc : ¬ CompactSpace (FinitePoints D i S)) :
    StrongApproximation D i S :=
  hD D G n hn hG hsc hv i S hne hnc

open private fixedVectorVertex from LinearAlgebraicGroups.Arithmetic.TrialitarianLocalForms

theorem ofNontransitiveD4Diagram
    (hD : Specs.Arithmetic.StrongApproximationNontrialitarianD.StrongApproximationNontrialitarian.{u,v})
    {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    (G : AffineAlgebraicGroup K) (hG : IsAbsolutelyAlmostSimple G)
    (hsc : GeometricallySimplyConnected G)
    (B : Specs.Arithmetic.TrialitarianLocalForms.D4Diagram G) (hB : ¬ B.IsTransitive)
    (i : MatrixRealization G) (S : Finset D.Place)
    (hne : S.Nonempty) (hnc : ¬ CompactSpace (FinitePoints D i S)) :
    StrongApproximation D i S :=
  ofFixedVectorVertex hD D G 4 le_rfl hG hsc (fixedVectorVertex B hB) i S hne hnc

section TypeD

open Specs.Arithmetic.NontrialitarianSpinModels (HasFixedVectorVertex)
open Specs.Arithmetic.TrialitarianLocalForms (D4Diagram)
open Specs.AbsoluteDynkinTypes (D4Cartan)
open Specs.RelativeFormComparison (fieldTest transportedAut)
open Specs.QuasiSplitInnerForms (outerHom)

open private fibreTowerIso from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private vertexPerm vertexPerm_index vertexPerm_preservesCartan
  from LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels

/-- The classified type D datum gives the marked diagram action of the
original form. In rank at least five, all diagram automorphisms fix the
vector vertex of the split matrix model. -/
private theorem typeD_marking {K : Type u} [Field K] (G : AffineAlgebraicGroup K)
    (hG : IsAbsolutelyAlmostSimple G) (n : ℕ) (hn : 4 ≤ n)
    (ht : Specs.ExceptionalCompletionGeometry.HasAbsoluteType G (.D n hn)) :
    HasFixedVectorVertex G n ∨ (n = 4 ∧ Nonempty (D4Diagram G)) := by
  let S := SeparableClosure K
  obtain ⟨Q, B, hQ, hB⟩ := existsSeparableCartan G hG.1 _ ht
  obtain ⟨M⟩ := LinearAlgebraicGroups.Classification.IntegralRealization.integralRealization B.toBased
  obtain ⟨A, P, eK, _⟩ := M.fieldFibre K
  obtain ⟨_, Q', eS, _⟩ := M.fieldFibre S
  obtain ⟨q⟩ := ((LinearAlgebraicGroups.Classification.PinnedEquivalence.pinnedEquivalence.2 S).2.1
    Q Q'.pinned.pair B Q'.attached).mpr ⟨Q'.datumIso.val⟩
  let j : (groupBaseChange K S).obj P.pinned.pair.G.val ≅ (groupBaseChange K S).obj G.val :=
    (groupBaseChange K S).mapIso eK.symm ≪≫ ((fibreTowerIso K S).app M.group).symm ≪≫
      eS ≪≫ q.symm ≪≫ eqToIso (congrArg Subtype.val hQ)
  obtain ⟨D, l, W, E, _, _⟩ :=
    LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.automorphismSequences P.pinned
  let f : B.toBased ⟶ D.toBased := P.datumIso ≫
    LinearAlgebraicGroups.Classification.Pinning.inducedBasedIso
      (Specs.Pinning.PinnedIso.refl P.pinned) P.attached D
  have htD := type_of_based_iso (Groupoid.inv f) hB
  obtain ⟨a, ha⟩ := htD
  let s : Fin n ≃ D.toBased.base.support := a.symm
  change ∀ x y : D.toBased.base.support,
    D.toBased.datum.pairing y.val x.val = CartanMatrix.D n (a x) (a y) at ha
  have hs (i j : Fin n) : D.toBased.datum.pairing (s j).val (s i).val =
      CartanMatrix.D n i j := by
    change D.toBased.datum.pairing (a.symm j).val (a.symm i).val = CartanMatrix.D n i j
    rw [ha, a.apply_symm_apply, a.apply_symm_apply]
  obtain ⟨relative, hr⟩ :=
    LinearAlgebraicGroups.Descent.RelativeFormComparison.schemeIsomorphismComparison
      (k := K) (S := S) P.pinned.pair.G.val G.val
  have hj := (hr j (relative j)).mpr rfl
  by_cases h4 : n = 4
  · subst n
    exact Or.inr ⟨rfl, ⟨⟨A, P.pinned, D, l, W, E, j, relative j, hj, s, hs⟩⟩⟩
  · have hn' : 5 ≤ n := by omega
    let i : Fin n := ⟨0, by omega⟩
    refine Or.inl ⟨A, P.pinned, D, l, W, E, j, relative j, s, i, hj, hs, ?_, ?_⟩
    · simp [h4, i]
    · intro σ
      let b := outerHom E (transportedAut K S (relative j) σ)
      have hfix : vertexPerm s b i = i := by
        rcases (RootData.AbsoluteDynkinTypes.typeDPermutations n hn' _).mp
          (vertexPerm_preservesCartan s hs b) with hp | hp
        · rw [hp, Equiv.refl_apply]
        · rw [hp]
          exact Equiv.swap_apply_of_ne_of_ne (by intro e; have := congrArg Fin.val e; simp [i] at this; omega)
            (by intro e; have := congrArg Fin.val e; simp [i] at this; omega)
      exact (vertexPerm_index s b i).symm.trans (congrArg (fun a => (s a).val) hfix)

end TypeD

/-- The type F₄ branch specializes the proved result on the actual geometric
Cartan datum. -/
theorem ofAbsoluteF4 {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    (G : AffineAlgebraicGroup K) (hG : IsAbsolutelyAlmostSimple G)
    (P : SplitBorelPair (AlgebraicClosure K)) (hP : P.G = GeometricGroup G)
    (B : AttachedDatum P)
    (hB : letI := B.comm; HasDynkinType (RootData.integralCartan B.datum.rootDatum B.base) .F4)
    (i : MatrixRealization G) (S : Finset D.Place)
    (hne : S.Nonempty) (hnc : ¬ CompactSpace (FinitePoints D i S)) :
    StrongApproximation D i S :=
  StrongApproximationF4.strongApproximation G ⟨hG.1, P, hP, B, hB⟩ D i S hne hnc

section ClassicalModels

open Specs.Arithmetic.AnisotropicClassicalApproximation
  (InnerTypeA Octonion OuterTypeA QuadraticSpin TypeC)
open Specs.Arithmetic.AnisotropicSpinQuotients (RegularModel)
open Specs.Arithmetic.IsotropicSpinGeneration (IsRegular)
open Specs.OctonionForms (g2CartanMatrix IsAbsoluteG2)

open private globalField_infinite from LinearAlgebraicGroups.Arithmetic.OppositeRadicals
open private automorphismGroupAlongIso from LinearAlgebraicGroups.Arithmetic.OctonionForms
open private exists_closedFrameTorus frameLatticeEquiv
  from LinearAlgebraicGroups.Composition.OctonionAutomorphisms

private theorem hasRegularModel {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    {q : QuadraticForm K V} (hq : IsRegular q) : ∃ r : Option V, RegularModel q r := by
  rcases hq with h | ⟨r, hr, hker⟩
  · exact ⟨none, h⟩
  · have hm : r ∈ LinearMap.ker q.polarBilin := hker.symm ▸ Submodule.mem_span_singleton_self r
    have hz := congrArg (fun l : V →ₗ[K] K => l r) (LinearMap.mem_ker.mp hm)
    change q.polarBilin r r = 0 at hz
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul] at hz
    exact ⟨some r, (mul_eq_zero.mp hz).resolve_right hr, hr, hker⟩

/-- In type B the descended quadratic form is anisotropic because any
isotropic vector produces a hyperbolic pair and a noncentral cocharacter. -/
theorem ofAbsoluteB
    (hspin : QuadraticSpin.{u,v})
    {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    (G : AffineAlgebraicGroup K) (hG : IsAbsolutelyAlmostSimple G)
    (hsc : GeometricallySimplyConnected G) (ha : GloballyAnisotropic G)
    (P : SplitBorelPair (AlgebraicClosure K)) (hP : P.G = GeometricGroup G)
    (B : AttachedDatum P) (n : ℕ) (hn : 2 ≤ n)
    (hB : letI := B.comm; HasDynkinType (RootData.integralCartan B.datum.rootDatum B.base) (.B n hn))
    (i : MatrixRealization G) (S : Finset D.Place)
    (hne : S.Nonempty) (hnc : ¬ CompactSpace (FinitePoints D i S)) :
    StrongApproximation D i S := by
  letI := globalField_infinite D
  have hsimple := arithmetic_absolute_simplicity hG
  obtain ⟨V, _, _, _, q, e, hdim, hreg, hrep, _, _⟩ :=
    OddSpinModels.typeBApplicability.{u,v} n hn G hsimple hsc P hP B hB
  obtain ⟨r, hr⟩ := hasRegularModel hreg
  have hq (x : V) (hx : q x = 0) : x = 0 := by
    by_contra hne
    obtain ⟨hpair, _⟩ := IsotropicSpinGeneration.hyperbolicPairExistence q hreg x hne hx
    obtain ⟨c, _, hc, _⟩ := IsotropicSpinGeneration.localSpinGeneration q
      ((Module.finBasis K V).reindex Equiv.ulift.symm) G e hrep hreg hsimple hpair
    exact ha ⟨c, hc⟩
  have hd : 5 ≤ Module.finrank K V := by omega
  exact (hspin D q r hr hq hd G e hsimple hsc ha hrep i).2 S hne hnc

/-- For type G₂ the descended octonion norm is anisotropic. Otherwise
the split frame torus would give a positive-dimensional split subgroup. -/
theorem ofAbsoluteG2
    (hoct : Octonion.{u,v})
    {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    (G : AffineAlgebraicGroup K) (hG : IsAbsolutelyAlmostSimple G)
    (hsc : GeometricallySimplyConnected G) (ha : GloballyAnisotropic G)
    (P : SplitBorelPair (AlgebraicClosure K)) (hP : P.G = GeometricGroup G)
    (B : AttachedDatum P)
    (hB : letI := B.comm; HasDynkinType (RootData.integralCartan B.datum.rootDatum B.base) .G2)
    (i : MatrixRealization G) (S : Finset D.Place)
    (hne : S.Nonempty) (hnc : ¬ CompactSpace (FinitePoints D i S)) :
    StrongApproximation D i S := by
  letI := B.comm
  obtain ⟨f, hf⟩ := hB
  have hG2 : IsAbsoluteG2 G := ⟨hG.1, P, hP, B, f.symm, by
    intro a b
    change B.datum.rootDatum.pairing (f.symm b).val (f.symm a).val = g2CartanMatrix a b
    simpa only [Equiv.apply_symm_apply, RootData.integralCartan,
      LieAlgebrasAndRepresentations.FiniteDynkinType.cartan, CartanMatrix.G₂, g2CartanMatrix] using
      hf (f.symm a) (f.symm b)⟩
  obtain ⟨C, _, _, _, _, q, hq, A, ⟨e⟩⟩ := OctonionForms.g2OctonionDescent G hG2
  have hq' (x : C) (hx : q x = 0) : x = 0 := by
    by_contra hne
    obtain ⟨F⟩ := LinearAlgebraicGroups.Composition.Peirce.isotropic_field_split hq ⟨x, hne, hx⟩
    let A' := automorphismGroupAlongIso G A e
    obtain ⟨j, hj, _⟩ := exists_closedFrameTorus F A'
    let T : Specs.ClosedSubgroup G.val := ⟨_, j, hj⟩
    let a := MonoidAlgebra.domCongrBialgEquiv K K frameLatticeEquiv.symm
    obtain ⟨b⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := K) 2
    exact noPositiveSplitTorus hG.1 ha ⟨T, 2, by decide,
      ⟨(hopfSpec (CommRingCat.of K)).mapIso (CommHopfAlgCat.isoMk a).op ≪≫ b⟩⟩
  exact (hoct D q A hq hq' G (arithmetic_absolute_simplicity hG) hsc ha ⟨e⟩ i).2 S hne hnc

open private descendedInvolutionSplit
  from LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels

/-- Apply the type C premise to the actual descended algebra and involution,
including rank one when presented by the one-vertex Cartan datum. -/
theorem ofGeometricCartanTypeC
    (hC : TypeC.{u,v}) {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    (G : AffineAlgebraicGroup K) (hG : IsAbsolutelyAlmostSimple G)
    (hsc : GeometricallySimplyConnected G) (ha : GloballyAnisotropic G)
    (n : ℕ) (htype : Specs.TypeCSplitRecognition.HasGeometricCartanTypeC n G)
    (i : MatrixRealization G) (S : Finset D.Place)
    (hne : S.Nonempty) (hnc : ¬ CompactSpace (FinitePoints D i S)) :
    StrongApproximation D i S := by
  obtain ⟨H, c, L, f, t, d, _⟩ := SymplecticInvolutionModels.globalTypeCModel
    (S := SeparableClosure K) n G hG.1 hsc htype
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  exact (hC (L := L) D d.model.fixed.centralSimple d.model.fixed.involution (n + 1)
    (Nat.succ_pos n) (descendedInvolutionSplit d) G (arithmetic_absolute_simplicity hG)
    hsc ha ⟨d.model.comparison⟩ i).2 S hne hnc

private theorem cartanTypeC_of_classification {K : Type u} [Field K]
    {G : AffineAlgebraicGroup K} (P : SplitBorelPair (AlgebraicClosure K))
    (hP : P.G = GeometricGroup G) (B : AttachedDatum P) (n : ℕ)
    (hB : letI := B.comm; ∃ f : B.base.support ≃ Fin (n + 1),
      Specs.AbsoluteDynkinTypes.PreservesCartan (RootData.integralCartan B.datum.rootDatum B.base)
        (CartanMatrix.B (n + 1)) f) :
    Specs.TypeCSplitRecognition.HasGeometricCartanTypeC n G := by
  letI := B.comm
  obtain ⟨f, hf⟩ := hB
  refine ⟨P, B, hP, f.symm, ?_⟩
  intro i j
  change B.datum.rootDatum.pairing (f.symm j).val (f.symm i).val = _
  have h := hf (f.symm i) (f.symm j)
  simp only [Equiv.apply_symm_apply, RootData.integralCartan] at h
  rw [h]
  simp only [CartanMatrix.B, Matrix.of_apply, Specs.TypeCSplitRecognition.cartanEntry,
    Nat.add_sub_cancel]
  split_ifs <;> first | rfl | omega

open Specs.OuterTypeAModels (HasAbsoluteSimplyConnectedTypeA RepresentsNormOne)
open RM03.CSA (IsCentralSimple degree algEquiv_matrix_algebraicClosure)
open RM03.CSA.NormOneGroup (changeCoefficients extendSplitting extendSplitting_tmul
  normAt_eq_det normAt_natural)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)

private theorem normAt_algEquiv {K A B R I J : Type u} [Field K] [Ring A] [Ring B]
    [Algebra K A] [Algebra K B] [CommRing R] [Algebra K R] [Fintype I] [Fintype J]
    (hA : IsCentralSimple K A) (hB : IsCentralSimple K B) (e : A ≃ₐ[K] B)
    (b : Module.Basis I K A) (c : Module.Basis J K B) (x : R ⊗[K] A) :
    normAt hA b x = normAt hB c (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e x) := by
  let L := AlgebraicClosure K
  let S := L ⊗[K] R
  let f : R →ₐ[K] S := Algebra.TensorProduct.includeRight
  let E (T : Type u) [CommRing T] [Algebra K T] :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T) e
  have hf : Function.Injective f :=
    Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective
  obtain ⟨s⟩ := algEquiv_matrix_algebraicClosure hB
  have hd : degree K B = degree K A := congrArg Nat.sqrt e.toLinearEquiv.finrank_eq.symm
  let sA := ((E L).trans s).trans (Matrix.reindexAlgEquiv L L (finCongr hd))
  have hmat :
      extendSplitting sA (changeCoefficients f x) =
        Matrix.reindexAlgEquiv S S (finCongr hd)
          (extendSplitting s (changeCoefficients f (E R x))) := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      simp only [map_add, hx, hy]
    | tmul r a =>
      change extendSplitting sA (f r ⊗ₜ[K] a) =
        Matrix.reindexAlgEquiv S S (finCongr hd)
          (extendSplitting s (f r ⊗ₜ[K] e a))
      simp only [extendSplitting_tmul, map_smul, sA, AlgEquiv.trans_apply,
        E, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
        AlgEquiv.coe_refl, id_eq, AlgEquiv.coe_toAlgHom]
      ext i j
      rfl
  apply hf
  change f (RM03.CSA.NormOneGroup.normAt hA b x) =
    f (RM03.CSA.NormOneGroup.normAt hB c (E R x))
  rw [← normAt_natural hA b, ← normAt_natural hB c,
    normAt_eq_det hA b sA, normAt_eq_det hB c s, hmat,
    Matrix.det_reindexAlgEquiv]

open scoped CategoryTheory.MonObj in
private theorem representsNormOne_transport {K A B I J : Type u} [Field K] [Ring A] [Ring B]
    [Algebra K A] [Algebra K B] [Fintype I] [Fintype J] {G : AffineAlgebraicGroup K}
    (hA : IsCentralSimple K A) (hB : IsCentralSimple K B) (e : A ≃ₐ[K] B)
    (b : Module.Basis I K A) (c : Module.Basis J K B) (h : RepresentsNormOne hA b G) :
    RepresentsNormOne hB c G := by
  obtain ⟨p, hp, hnat⟩ := h
  let E (R : TestAlgebra K) := Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e
  let q (R : TestAlgebra K) : Points G.val.X R ≃ {x : R ⊗[K] B // normAt hB c x = 1} :=
    (p R).trans ((E R).toEquiv.subtypeEquiv (fun x =>
      show normAt hA b x = 1 ↔ normAt hB c (E R x) = 1 by rw [normAt_algEquiv hA hB e b c]))
  refine ⟨q, ?_, ?_⟩
  · intro R x y
    change E R (p R (x * y)).val = E R (p R x).val * E R (p R y).val
    rw [hp, map_mul]
  · intro R S f x
    change E S (p S (mapPoints f x)).val =
      Algebra.TensorProduct.map f.hom (.id K B) (E R (p R x).val)
    rw [hnat]
    generalize (p R x).val = a
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul r a => simp [E]

/-- The type A matrix model is available on the original group. In the
outer case its degree and quadratic centre meet the approximation premise. -/
private theorem typeA_inner_or_approximation
    (hOuter : OuterTypeA.{u,v}) {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    (G : AffineAlgebraicGroup K) (hG : IsAbsolutelyAlmostSimple G)
    (hsc : GeometricallySimplyConnected G) (ha : GloballyAnisotropic G)
    (r : ℕ) (hr : 2 ≤ r)
    (ht : Specs.ExceptionalCompletionGeometry.HasAbsoluteType G (.A r (by omega)))
    (i : MatrixRealization G) (S : Finset D.Place)
    (hne : S.Nonempty) (hnc : ¬ CompactSpace (FinitePoints D i S)) :
    (∃ (A : Type u) (_ : Ring A) (_ : Algebra K A) (hA : _root_.Specs.RM03.CSA.isCentralSimple K A)
      (I : Type u) (_ : Fintype I) (b : Module.Basis I K A),
      _root_.Specs.RM03.CSA.degree K A = r + 1 ∧ RepresentsNormOne hA b G) ∨
      StrongApproximation D i S := by
  let L := SeparableClosure K
  obtain ⟨Q, B, hQ, hB⟩ := existsSeparableCartan G hG.1 _ ht
  have hsQ : IsSemisimple Q.G := hQ.symm ▸
    (OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := L) G
      (arithmetic_absolute_simplicity hG)).1
  have hscQ : GeometricallySimplyConnected Q.G := hQ.symm ▸ simplyConnectedAfterBaseChange G hG.1 hsc
  have htype : HasAbsoluteSimplyConnectedTypeA r G := by
    letI := B.comm
    obtain ⟨p, hp⟩ := hB
    refine ⟨L, inferInstance, inferInstance, inferInstance, Q, hQ, hsQ, hscQ, B, p.symm, ?_⟩
    intro a b
    change B.datum.rootDatum.pairing (p.symm a).val (p.symm b).val = _
    simpa only [Equiv.apply_symm_apply, RootData.integralCartan, FiniteDynkinType.cartan,
      CartanMatrix.A, Matrix.of_apply, eq_comm, or_comm] using hp (p.symm b) (p.symm a)
  obtain ⟨H, s, M, _, _, _, _, f, data⟩ := LinearAlgebraicGroups.OuterTypeAModels.absoluteTypeAForms
    hr G htype
  obtain ⟨χ, _, β, _, _, _, _, _, hχ, hmodel⟩ := data
  rcases hχ with hχ | hχ
  · obtain ⟨ρ, _, hA, hd, I, _, b, hb⟩ := hmodel.1 hχ
    exact Or.inl ⟨ρ.fixedSubalgebra, inferInstance, inferInstance, hA, I, inferInstance, b, hd, hb⟩
  · obtain ⟨hE, hsep, ρ, _, hA, hd, star, _, _, I, _, b, hb⟩ := hmodel.2 hχ
    letI := hsep
    exact Or.inr ((hOuter D hE hA (by omega) b star G (arithmetic_absolute_simplicity hG)
      hsc ha hb i).2 S hne hnc)

open private groupIsoOfPoints from LinearAlgebraicGroups.Unipotent.Criteria
open private matrixOne from LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting

open scoped CategoryTheory.MonObj in
private theorem normOneModelIso {K B I : Type u} [Field K] [Ring B] [Algebra K B]
    [Fintype I] {m : ℕ} {G H : AffineAlgebraicGroup K}
    (hA : IsCentralSimple K (Matrix (Fin m) (Fin m) B))
    (b : Module.Basis I K (Matrix (Fin m) (Fin m) B))
    (h : RepresentsNormOne hA b G) (P : Specs.InnerTypeARelativeContraction.NormOnePoints hA b H) :
    Nonempty (G.val ≅ H.val) := by
  obtain ⟨p, hmul, hnat⟩ := h
  let e (R : TestAlgebra K) : ((groupPointsFunctor K).obj G.val).obj R ≃*
      ((groupPointsFunctor K).obj H.val).obj R :=
    { (p R).trans (P.point R).symm with
      map_mul' := by
        intro x y
        apply (P.point R).injective
        apply Subtype.ext
        rw [P.mul]
        change (P.point R ((P.point R).symm (p R (x * y)))).val =
          (P.point R ((P.point R).symm (p R x))).val *
            (P.point R ((P.point R).symm (p R y))).val
        simpa only [Equiv.apply_symm_apply] using hmul R x y }
  refine ⟨groupIsoOfPoints (NatIso.ofComponents (fun R => (e R).toGrpIso) ?_)⟩
  intro R S f
  apply GrpCat.ext
  intro g
  apply (P.point S).injective
  apply Subtype.ext
  change (P.point S (e S (mapPoints f g))).val = (P.point S (mapPoints f (e R g))).val
  rw [P.natural]
  change (P.point S ((P.point S).symm (p S (mapPoints f g)))).val =
    Algebra.TensorProduct.map f.hom (.id K _)
      (P.point R ((P.point R).symm (p R g))).val
  simp only [Equiv.apply_symm_apply]
  exact hnat f g

/-- Anisotropy forces the simple algebra of an inner type A model to be
division. A nontrivial matrix size gives the positive-rank scalar diagonal. -/
private theorem innerTypeA_of_normOne
    (hInner : InnerTypeA.{u,v})
    {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
    (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (ha : GloballyAnisotropic G) (hA : IsCentralSimple K A)
    (b : Module.Basis I K A) (hb : RepresentsNormOne hA b G)
    (i : MatrixRealization G) (S : Finset D.Place)
    (hne : S.Nonempty) (hnc : ¬ CompactSpace (FinitePoints D i S)) :
    StrongApproximation D i S := by
  obtain ⟨m, B, _, _, hB, hm, ⟨e⟩⟩ := RM03.CSA.MatrixDivision.exists_presentation K A hA
  have hB' := RM03.CSA.isCentralSimple_of_isCentralDivision K B hB
  letI : FiniteDimensional K B := hB.2
  cases m with
  | zero => omega
  | succ n =>
    by_cases hn : n = 0
    · subst n
      let b₁ := (Module.finBasis K B).reindex Equiv.ulift.symm
      have hb₁ := representsNormOne_transport hA hB' (e.trans matrixOne) b b₁ hb
      exact (hInner D hB' b₁ G (arithmetic_absolute_simplicity hG) hsc ha hb₁ i).2 S hne hnc
    · exfalso
      let M := Matrix (Fin (n + 1)) (Fin (n + 1)) B
      letI : FiniteDimensional K M := inferInstance
      let b₁ := (Module.finBasis K M).reindex Equiv.ulift.symm
      have hM := InnerTypeALocalGeneration.Spec.matrixCentralSimple hB' (Nat.succ_pos n)
      have hb₁ := representsNormOne_transport hA hM e b b₁ hb
      obtain ⟨hHopf, P, T, _, he, _, _, _⟩ := InnerTypeASplitRank.splitRank n hB hM b₁
      obtain ⟨f⟩ := normOneModelIso hM b₁ hb₁ P
      let g := T.inclusion ≫ f.inv
      have hg : IsClosedImmersion g.hom.hom.left := by
        letI := T.isClosedImmersion
        let F := Grp.forget (SchemeOver K) ⋙ Over.forget _
        letI : IsIso f.inv.hom.hom.left := show IsIso (F.map f.inv) from inferInstance
        change IsClosedImmersion (T.inclusion.hom.hom.left ≫ f.inv.hom.hom.left)
        infer_instance
      exact noPositiveSplitTorus hG.1 ha ⟨⟨T.group, g, hg⟩, n, Nat.pos_of_ne_zero hn, he⟩

theorem ofAbsoluteA
    (hInner : InnerTypeA.{u,v}) (hOuter : OuterTypeA.{u,v}) {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K) (hG : IsAbsolutelyAlmostSimple G)
    (hsc : GeometricallySimplyConnected G) (ha : GloballyAnisotropic G)
    (r : ℕ) (hr : 2 ≤ r)
    (ht : Specs.ExceptionalCompletionGeometry.HasAbsoluteType G (.A r (by omega)))
    (i : MatrixRealization G) (S : Finset D.Place)
    (hne : S.Nonempty) (hnc : ¬ CompactSpace (FinitePoints D i S)) :
    StrongApproximation D i S := by
  rcases typeA_inner_or_approximation hOuter D G hG hsc ha r hr ht i S hne hnc with
    ⟨A, _, _, hA, I, _, b, _, hb⟩ | h
  · exact innerTypeA_of_normOne hInner D G hG hsc ha hA b hb i S hne hnc
  · exact h

private theorem rankOneCartan_of_A1 {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (ht : Specs.ExceptionalCompletionGeometry.HasAbsoluteType G (.A 1 le_rfl)) :
    Specs.TypeCSplitRecognition.HasGeometricCartanTypeC 0 G := by
  obtain ⟨P, hP, B, hB⟩ := ht
  letI := B.comm
  obtain ⟨f, hf⟩ := hB
  refine ⟨P, B, hP, f.symm, ?_⟩
  intro i j
  have h : i = j := Fin.ext (by omega)
  subst j
  change B.datum.rootDatum.pairing (f.symm i).val (f.symm i).val = _
  have he := hf (f.symm i) (f.symm i)
  simp only [RootData.integralCartan, Equiv.apply_symm_apply, FiniteDynkinType.cartan,
    CartanMatrix.A, Matrix.of_apply, ite_true] at he
  simpa only [Specs.TypeCSplitRecognition.cartanEntry, ite_true] using he

end ClassicalModels

section Cases

open Specs.Arithmetic.AnisotropicClassicalApproximation
  (InnerTypeA Octonion OuterTypeA QuadraticSpin TypeC)
open Specs.Arithmetic.StrongApproximationNontrialitarianD (StrongApproximationNontrialitarian)
open Specs.Arithmetic.TrialitarianLocalForms (IsTrialitarian)

/-- The absolute classification and the available classical approximation
inputs reduce the anisotropic criterion to the transitive D₄ and E branches. -/
theorem strongApproximation_or_remainingTypes
    (hInner : InnerTypeA.{u,v}) (hOuter : OuterTypeA.{u,v}) (hSpin : QuadraticSpin.{u,v})
    (hC : TypeC.{u,v}) (hG2 : Octonion.{u,v}) (hD : StrongApproximationNontrialitarian.{u,v})
    {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (ha : GloballyAnisotropic G) (i : MatrixRealization G) (S : Finset D.Place)
    (hne : S.Nonempty) (hnc : ¬ CompactSpace (FinitePoints D i S)) :
    StrongApproximation D i S ∨ IsTrialitarian G ∨
      ∃ t : FiniteDynkinType, (t = .E6 ∨ t = .E7 ∨ t = .E8) ∧
        Specs.ExceptionalCompletionGeometry.HasAbsoluteType G t := by
  obtain ⟨P, hP, _, _, B, hbasis⟩ := RootData.AbsoluteDynkinTypes.absoluteClassification G hG hsc
    (LinearAlgebraicGroups.Classification.Pinning.standardAdditiveLine (AlgebraicClosure K))
  letI := B.comm
  obtain ⟨_, _, _, _, _, t, e, he, _⟩ := hbasis
  have ht : Specs.ExceptionalCompletionGeometry.HasAbsoluteType G t := ⟨P, hP, B, e, he⟩
  cases t with
  | A n hn =>
    by_cases hn₁ : n = 1
    · subst n
      exact Or.inl (ofGeometricCartanTypeC hC D G hG hsc ha 0
        (rankOneCartan_of_A1 ht) i S hne hnc)
    · exact Or.inl (ofAbsoluteA hInner hOuter D G hG hsc ha n (by omega) ht i S hne hnc)
  | B n hn =>
    exact Or.inl (ofAbsoluteB hSpin D G hG hsc ha P hP B n hn ⟨e, he⟩ i S hne hnc)
  | C n hn =>
    cases n with
    | zero => omega
    | succ n =>
      exact Or.inl (ofGeometricCartanTypeC hC D G hG hsc ha n
        (cartanTypeC_of_classification P hP B n ⟨e, he⟩) i S hne hnc)
  | D n hn =>
    rcases typeD_marking G hG n hn ht with hfix | ⟨rfl, ⟨B₄⟩⟩
    · exact Or.inl (ofFixedVectorVertex hD D G n hn hG hsc hfix i S hne hnc)
    · by_cases hh : B₄.IsTransitive
      · exact Or.inr (Or.inl ⟨B₄, hh⟩)
      · exact Or.inl (ofNontransitiveD4Diagram hD D G hG hsc B₄ hh i S hne hnc)
  | E6 => exact Or.inr (Or.inr ⟨.E6, Or.inl rfl, ht⟩)
  | E7 => exact Or.inr (Or.inr ⟨.E7, Or.inr (Or.inl rfl), ht⟩)
  | E8 => exact Or.inr (Or.inr ⟨.E8, Or.inr (Or.inr rfl), ht⟩)
  | F4 => exact Or.inl (ofAbsoluteF4 D G hG P hP B ⟨e, he⟩ i S hne hnc)
  | G2 => exact Or.inl (ofAbsoluteG2 hG2 D G hG hsc ha P hP B ⟨e, he⟩ i S hne hnc)

end Cases

section NumberField

open Specs.Arithmetic.ProjectiveRecurrence (localPointSet parabolicRadicalPoints cocharacterRadicalPoints)
open Specs.RelativeRank (relativeRank)
open Specs.Unipotent (baseChangedAlgebraicGroup)

open private anisotropicNumber_of_local numberStrongApproximation_iff numberOmittedCompact_iff
  from LinearAlgebraicGroups.Arithmetic.StrongApproximationF4

/-- Number-field assembly from local generation at the finite places and
the two archimedean alternatives. The recurrence and isolation lemmas
apply with the same field, group, realization and omitted places. -/
private theorem numberStrongApproximation_of_local
    {K : Type u} [Field K] [hK : NumberField K] {G : AffineAlgebraicGroup K}
    (i : MatrixRealization G) (hG : IsAbsolutelyAlmostSimple G) (ha : GloballyAnisotropic G)
    (D₀ : GlobalFieldData.{u,v} K) (hD₀ : D₀ = .number hK)
    (S : Finset D₀.Place) (hnc : ¬ CompactSpace (FinitePoints D₀ i S))
    (D : GlobalFieldData.{u,u} K) (hD : D = .number hK)
    (hArch : ∀ w : D.InfinitePlace, ¬ CompactSpace (LocalPoints D i (.inr w)) →
      Dense (Subgroup.closure (localPointSet D i (.inr w) (cocharacterRadicalPoints
        (baseChangedAlgebraicGroup (D.Completion (.inr w)) G))) :
        Set (LocalPoints D i (.inr w))) ∧
      Dense (Subgroup.closure {x : LocalPoints D i (.inr w) | Contracted x} :
        Set (LocalPoints D i (.inr w))))
    (hConn : ∀ w : D.InfinitePlace, CompactSpace (LocalPoints D i (.inr w)) →
      ConnectedSpace (LocalPoints D i (.inr w)))
    (hFinite : ∀ w : D.FinitePlace,
      0 < relativeRank (baseChangedAlgebraicGroup (D.Completion (.inl w)) G) ∧
      Dense (Subgroup.closure (localPointSet D i (.inl w)
        (parabolicRadicalPoints (baseChangedAlgebraicGroup (D.Completion (.inl w)) G))) :
        Set (LocalPoints D i (.inl w))) ∧
      Dense (Subgroup.closure {x : LocalPoints D i (.inl w) | Contracted x} :
        Set (LocalPoints D i (.inl w)))) :
    StrongApproximation D₀ i S := by
  subst D₀
  subst D
  let D := GlobalFieldData.number.{u,u} hK
  apply (numberStrongApproximation_iff.{u,u,v} i S).mp
  have hnc' := (numberOmittedCompact_iff.{u,v,u} i (.number hK) rfl D rfl S).not.mp hnc
  exact anisotropicNumber_of_local D i rfl (arithmetic_absolute_simplicity hG)
    (compactFullAdelicQuotient D i hG.1 ha) S hnc' hArch hConn hFinite

end NumberField

section ExceptionalFinitePlaces

open Specs.ExceptionalAffineRootSystems (exceptionalCartan)
open Specs.ExceptionalLocalRadicalGeneration (HasAbsoluteTypeE)

private theorem exceptionalTypeE_of_cartan {F : Type u} [Field F] (J : AffineAlgebraicGroup F)
    (hs : IsSemisimple J) (t : FiniteDynkinType)
    (ht : Specs.ExceptionalCompletionGeometry.HasAbsoluteType J t)
    (hc : ∀ i j : Fin t.rank, t.cartan j i = exceptionalCartan t.rank i j) :
    HasAbsoluteTypeE J t.rank := by
  obtain ⟨Q, B, hQ, hB⟩ := existsSeparableCartan J hs t ht
  letI := B.comm
  obtain ⟨e, he⟩ := hB
  refine ⟨Q, B, e.symm, ⟨eqToIso (congrArg Subtype.val hQ)⟩, ?_⟩
  intro i j
  change B.datum.rootDatum.pairing (e.symm i).val (e.symm j).val = _
  have h := he (e.symm j) (e.symm i)
  simp only [RootData.integralCartan, Equiv.apply_symm_apply] at h
  exact h.trans (hc i j)

private theorem exceptionalCartan_eq {n : ℕ} (hn : n = 6 ∨ n = 7 ∨ n = 8) :
    exceptionalCartan n = CartanMatrix.E n := by
  rcases hn with rfl | rfl | rfl <;> decide +kernel

private theorem exceptionalTypeE_of_absolute {F : Type u} [Field F] (J : AffineAlgebraicGroup F)
    (hs : IsSemisimple J) (t : FiniteDynkinType) (ht : t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hJ : Specs.ExceptionalCompletionGeometry.HasAbsoluteType J t) :
    HasAbsoluteTypeE J 6 ∨ HasAbsoluteTypeE J 7 ∨ HasAbsoluteTypeE J 8 := by
  rcases ht with rfl | rfl | rfl
  · refine Or.inl (exceptionalTypeE_of_cartan J hs .E6 hJ fun i j => ?_)
    change CartanMatrix.E 6 j i = exceptionalCartan 6 i j
    rw [exceptionalCartan_eq (Or.inl rfl), (CartanMatrix.E_isSymm 6).apply]
  · refine Or.inr (Or.inl (exceptionalTypeE_of_cartan J hs .E7 hJ fun i j => ?_))
    change CartanMatrix.E 7 j i = exceptionalCartan 7 i j
    rw [exceptionalCartan_eq (Or.inr (Or.inl rfl)), (CartanMatrix.E_isSymm 7).apply]
  · refine Or.inr (Or.inr (exceptionalTypeE_of_cartan J hs .E8 hJ fun i j => ?_))
    change CartanMatrix.E 8 j i = exceptionalCartan 8 i j
    rw [exceptionalCartan_eq (Or.inr (Or.inr rfl)), (CartanMatrix.E_isSymm 8).apply]

open Specs.Arithmetic.ProjectiveRecurrence (parabolicRadicalPoints)
open scoped Valued

private theorem radicalContraction_at_finitePlace {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (J : AffineAlgebraicGroup F) (j : MatrixRealization J) {x : PointsIn j F}
    (hx : x ∈ parabolicRadicalPoints J) : Contracted x := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := F)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := F).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  exact (@StrongApproximationF4.parabolicPoints_are_contracted F
    (Valued.toNontriviallyNormedField F (ValuativeRel.ValueGroupWithZero F)) J j x hx).2

end ExceptionalFinitePlaces

section CompletionGeneration

open Specs.Arithmetic.LocalQuotientMixing (HasDenseRadicals MixingCases)
open Specs.Arithmetic.ProjectiveRecurrence (localPointSet parabolicRadicalPoints)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.IntegralModels (RationalPoints)
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open private testPointSections from LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private matrixPointTopology mapSectionsToTestPointSubgroup
  from LinearAlgebraicGroups.Arithmetic.StrongApproximationNontrialitarianD
open private mapContracted from LinearAlgebraicGroups.Arithmetic.LocalCompactnessCriterion
open private evaluate_section from LinearAlgebraicGroups.Arithmetic.LocalQuotientMixing

/-- A subgroup containing all rational radical points contains the image of
the subgroup generated by radical sections under evaluation on the field. -/
private theorem radicalSections_le_comap {F : Type u} [Field F]
    (J : AffineAlgebraicGroup F) (M : Subgroup (RationalPoints J))
    (hM : parabolicRadicalPoints J ⊆ M) :
    unipotentGenerated J ≤ M.comap (testPointSections J.val).symm.toMonoidHom := by
  unfold unipotentGenerated
  refine iSup_le fun P => iSup_le fun hP => iSup_le fun U => iSup_le fun hU => ?_
  apply Subgroup.map_le_iff_le_comap.mp
  rw [mapSectionsToTestPointSubgroup]
  rintro _ ⟨p, rfl⟩
  exact hM ⟨P, hP, U, hU, p, rfl⟩

private theorem parabolicDensity_in_coordinateTopology {F : Type u} [Field F]
    [TopologicalSpace F] (J : AffineAlgebraicGroup F) (h : HasDenseRadicals J) :
    @Dense (RationalPoints J) (LocalAlgebraicTransport.pointTopology J.val.X)
      (Subgroup.closure (parabolicRadicalPoints J) : Set (RationalPoints J)) := by
  let t : TopologicalSpace (RationalPoints J) := LocalAlgebraicTransport.pointTopology J.val.X
  let f := (testPointSections J.val).symm.toMonoidHom
  let M : Subgroup (RationalPoints J) := Subgroup.closure (parabolicRadicalPoints J)
  have hM : (unipotentGenerated J).map f ≤ M :=
    Subgroup.map_le_iff_le_comap.mpr (radicalSections_le_comap J M Subgroup.subset_closure)
  change @Dense (RationalPoints J) t (M : Set (RationalPoints J))
  refine @Dense.mono (RationalPoints J) t _ _ ?_ h
  rintro g ⟨s, hs, he⟩
  have hsg : f s = g := (evaluate_section (G := J) s).trans he
  exact hM (Subgroup.mem_map.mpr ⟨s, hs, hsg⟩)

/-- The topology of a closed matrix realization is the topology induced by
the regular coordinates on the same rational points. -/
private theorem parabolicDensity_in_matrixTopology {F : Type u} [Field F]
    [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (J : AffineAlgebraicGroup F) (j : MatrixRealization J) (h : HasDenseRadicals J) :
    @Dense (RationalPoints J) (inferInstanceAs (TopologicalSpace (PointsIn j F)))
      (Subgroup.closure (parabolicRadicalPoints J) : Set (RationalPoints J)) := by
  let A : Set (RationalPoints J) := Subgroup.closure (parabolicRadicalPoints J)
  let P (t : TopologicalSpace (RationalPoints J)) := @Dense (RationalPoints J) t A
  exact Eq.mpr (congrArg P (matrixPointTopology J j)) (parabolicDensity_in_coordinateTopology J h)

/-- The radical generators and their contractions transport to the original
completion. This comparison also applies to function fields. -/
private theorem finiteGeneration_at_completion
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (w : D.FinitePlace)
    (hmix : MixingCases (baseChangedAlgebraicGroup (D.Completion (.inl w)) G)) :
    Dense (Subgroup.closure (localPointSet D i (.inl w)
      (parabolicRadicalPoints (baseChangedAlgebraicGroup (D.Completion (.inl w)) G))) :
      Set (LocalPoints D i (.inl w))) ∧
    Dense (Subgroup.closure {x : LocalPoints D i (.inl w) | Contracted x} :
      Set (LocalPoints D i (.inl w))) := by
  let F := D.FiniteCompletion w
  letI : Algebra K F := completionAlgebra D (.inl w)
  letI : IsTopologicalDivisionRing F := completionTopologicalDivisionRing D (.inl w)
  let J := baseChangedAlgebraicGroup F G
  have hJ := OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G
    (arithmetic_absolute_simplicity hG)
  have hd := LocalProjectedClosure.hasDenseRadicals_of_mixingCases
    ExceptionalLocalRadicalGeneration.localRadicalGeneration J hJ hmix
  obtain ⟨_, j₀, _, e₀, he, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison K F G i
  let j : MatrixRealization J := j₀
  let e : PointsIn j F ≃ₜ* LocalPoints D i (.inl w) := e₀
  let R : Set (PointsIn j F) := parabolicRadicalPoints J
  have hR : localPointSet D i (.inl w) (parabolicRadicalPoints J) = e '' R := by
    ext x
    constructor
    · rintro ⟨p, hp, hpx⟩
      exact ⟨p, hp, Over.OverMorphism.ext ((he p).trans hpx.symm)⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, he p⟩
  have hd' := e.surjective.denseRange.dense_image e.continuous
    (parabolicDensity_in_matrixTopology J j hd)
  change Dense (↑((Subgroup.closure R).map e.toMonoidHom) :
    Set (LocalPoints D i (.inl w))) at hd'
  rw [MonoidHom.map_closure] at hd'
  refine ⟨hR ▸ hd', hd'.mono (Subgroup.closure_mono ?_)⟩
  rintro _ ⟨p, hp, rfl⟩
  exact mapContracted e.toMonoidHom e.continuous (radicalContraction_at_finitePlace J j hp)

end CompletionGeneration

section RemainingTypes

open Specs.Arithmetic.LocalQuotientMixing (MixingCases)
open Specs.Arithmetic.ProjectiveRecurrence (cocharacterRadicalPoints localPointSet)
open Specs.Arithmetic.TrialitarianLocalForms (IsTrialitarian)
open Specs.ExceptionalAdelicApproximation (numberPlaces)
open Specs.ExceptionalRealPoints (HasAbsoluteExceptionalType)
open Specs.RelativeRank (relativeRank)

open private diagramAfterScalarExtension from
  LinearAlgebraicGroups.Arithmetic.TrialitarianLocalForms
open private exists_proper_dynamic_of_noncentral from LinearAlgebraicGroups.Descent.RelativeRank
open private absoluteDynkin_iff realCompletionProperties
  from LinearAlgebraicGroups.Arithmetic.ExceptionalRealPoints
open private archimedeanRadicalContracted splitContractingGeneration
  subsingleton_of_compact_contracted from LinearAlgebraicGroups.Arithmetic.ExceptionalAdelicApproximation

open scoped CategoryTheory.MonObj in
private theorem finiteInputs_of_remainingTypes
    {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (h : IsTrialitarian G ∨ HasAbsoluteExceptionalType G) (w : D.FinitePlace) :
    let J := baseChangedAlgebraicGroup (D.Completion (.inl w)) G
    0 < relativeRank J ∧ MixingCases J := by
  let F := D.FiniteCompletion w
  letI : Algebra K F := completionAlgebra D (.inl w)
  let J := baseChangedAlgebraicGroup F G
  have hJ := OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G
    (arithmetic_absolute_simplicity hG)
  have hscJ := simplyConnectedAfterBaseChange (F := F) G hG.1 hsc
  rcases h with ⟨d, _⟩ | ⟨t, ht, htype⟩
  · obtain ⟨dF⟩ := diagramAfterScalarExtension d F
    obtain ⟨c, hc⟩ := TrialitarianLocalForms.finiteIsotropy F J ⟨hJ.1, hscJ, ⟨dF⟩⟩
    obtain ⟨X, g, hg⟩ := hc
    have hp := exists_proper_dynamic_of_noncentral J (reductive_of_semisimple J hJ.1) c
      (fun hc => hg (hc X g))
    exact ⟨(Descent.RelativeRank.semisimpleParabolicCriterion J hJ.1).mp hp,
      TrialitarianCompletionMixingCases.mixingCases F J hJ.1 hscJ dF⟩
  · have htypeF := absoluteCartan_fieldExtension (F := F) G hG t htype
    have hE := exceptionalTypeE_of_absolute J hJ.1 t ht htypeF
    have hr := (ExceptionalLocalRadicalGeneration.localRadicalGeneration F J hJ hscJ hE).1
    exact ⟨hr, ExceptionalCompletionMixingCases.exceptionalCompletionMixingCases F J hJ hscJ hE⟩

section ExceptionalArchimedean

variable {K : Type u} [Field K] [NumberField K] {G : AffineAlgebraicGroup K}

attribute [local instance] Specs.ExceptionalAdelicApproximation.numberCompletionField
  Specs.ExceptionalAdelicApproximation.numberCompletionTopology
  Specs.ExceptionalAdelicApproximation.numberCompletionAlgebra

open scoped CategoryTheory.MonObj in
/-- The cocharacter radicals at a complex completion generate the whole
point group by split generation, in the original realization. -/
private theorem complexRadicalClosure_eq_top (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (hE : HasAbsoluteExceptionalType G)
    (w : NumberField.InfinitePlace K) (hw : w.IsComplex) :
    Subgroup.closure (localPointSet (numberPlaces K) i (.inr w)
      (cocharacterRadicalPoints (baseChangedAlgebraicGroup
        ((numberPlaces K).Completion (.inr w)) G))) = ⊤ := by
  let D := numberPlaces K
  let F := w.Completion
  letI : Algebra K F := completionAlgebra D (.inr w)
  let J := baseChangedAlgebraicGroup F G
  have hJ := (OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G
    (arithmetic_absolute_simplicity hG)).1
  have hscJ := simplyConnectedAfterBaseChange (F := F) G hG.1 hsc
  have hsplit : Specs.GeometricRadicals.IsSplitReductive J :=
    ExceptionalRealPoints.complexCompletionsSplit G ((absoluteDynkin_iff G).mp hG) hsc hE w hw
  let e : Specs.IntegralModels.RationalPoints J ≃* LocalPoints D i (.inr w) :=
    baseChangePointGroupEquiv F G.val (CommAlgCat.of F F)
  let A := cocharacterRadicalPoints J
  have hset : localPointSet D i (.inr w) A = e.toMonoidHom '' A := by
    ext x
    constructor
    · rintro ⟨p, hp, hpx⟩
      exact ⟨p, hp, Over.OverMorphism.ext hpx.symm⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
  change Subgroup.closure (localPointSet D i (.inr w) A) = ⊤
  rw [hset, ← MonoidHom.map_closure, splitContractingGeneration J hJ hscJ hsplit,
    Subgroup.map_top_of_surjective _ e.surjective]

private theorem exceptionalArchimedeanInputs (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (hE : HasAbsoluteExceptionalType G) (w : NumberField.InfinitePlace K) :
    let D := numberPlaces K
    (¬ CompactSpace (LocalPoints D i (.inr w)) →
      Dense (Subgroup.closure (localPointSet D i (.inr w)
        (cocharacterRadicalPoints (baseChangedAlgebraicGroup (D.Completion (.inr w)) G))) :
        Set (LocalPoints D i (.inr w))) ∧
      Dense (Subgroup.closure {x : LocalPoints D i (.inr w) | Contracted x} :
        Set (LocalPoints D i (.inr w)))) ∧
    (CompactSpace (LocalPoints D i (.inr w)) → ConnectedSpace (LocalPoints D i (.inr w))) := by
  let D := numberPlaces K
  have contractedDensity (h : Dense (Subgroup.closure (localPointSet D i (.inr w)
      (cocharacterRadicalPoints (baseChangedAlgebraicGroup (D.Completion (.inr w)) G))) :
      Set (LocalPoints D i (.inr w)))) :
      Dense (Subgroup.closure {x : LocalPoints D i (.inr w) | Contracted x} :
        Set (LocalPoints D i (.inr w))) :=
    h.mono (Subgroup.closure_mono fun _ hx => archimedeanRadicalContracted G i w hx)
  rcases w.isReal_or_isComplex with hR | hC
  · obtain ⟨hconn, hd⟩ := realCompletionProperties G i ((absoluteDynkin_iff G).mp hG) hsc hE w hR
    exact ⟨fun h => ⟨hd h, contractedDensity (hd h)⟩, fun _ => hconn⟩
  · have hd : Dense (Subgroup.closure (localPointSet D i (.inr w)
        (cocharacterRadicalPoints (baseChangedAlgebraicGroup (D.Completion (.inr w)) G))) :
        Set (LocalPoints D i (.inr w))) := by
      rw [complexRadicalClosure_eq_top i hG hsc hE w hC, Subgroup.coe_top]
      exact dense_univ
    have hc := contractedDensity hd
    refine ⟨fun _ => ⟨hd, hc⟩, fun hcomp => ?_⟩
    letI := hcomp
    letI : T2Space (D.Completion (.inr w)) := inferInstanceAs (T2Space w.Completion)
    letI : T2Space (LocalPoints D i (.inr w)) := (usualLocalTopology D i (.inr w)).t2Space
    letI : IsTopologicalRing (D.Completion (.inr w)) :=
      inferInstanceAs (IsTopologicalRing w.Completion)
    letI : IsTopologicalGroup (LocalPoints D i (.inr w)) :=
      pointsInTopologicalGroup i (D.Completion (.inr w))
    letI := subsingleton_of_compact_contracted hc
    infer_instance

end ExceptionalArchimedean

end RemainingTypes

open Specs.Arithmetic.AnisotropicClassicalApproximation
  (CharacteristicTwoQuadraticNormIndex InnerTypeA LocalSpinIsotropy LocalUnitaryIsotropy Octonion
    OuterTypeA QuadraticSpin RankOneQuadraticSpin TypeC)
open Specs.Arithmetic.AnisotropicSufficiency (StrongApproximationStatement)
open Specs.ExceptionalAdelicApproximation (numberPlaces)
open Specs.ExceptionalRealPoints (HasAbsoluteExceptionalType)
open Specs.Arithmetic.TrialitarianLocalForms (IsTrialitarian)
open LocalAlgebraicTransport (pointTopology)
open private completionPointEquiv strongApproximationOfCompactQuotient
  from LinearAlgebraicGroups.Arithmetic.StrongApproximationNontrialitarianD

/-- Anisotropic strong approximation from the classical approximation inputs
and the local results for the remaining absolute types. -/
theorem strongApproximation_conditional
    (_normIndex : CharacteristicTwoQuadraticNormIndex.{u})
    (hInner : InnerTypeA.{u,v})
    (_localSpin : LocalSpinIsotropy.{u})
    (_localUnitary : LocalUnitaryIsotropy.{u})
    (hOctonion : Octonion.{u,v})
    (hOuter : OuterTypeA.{u,v})
    (hSpin : QuadraticSpin.{u,v})
    (_rankOneSpin : RankOneQuadraticSpin.{u,v})
    (hTypeC : TypeC.{u,v}) :
    StrongApproximationStatement.{u,v} := by
  intro K _ D G hG hsc ha i S hS hnc
  rcases strongApproximation_or_remainingTypes hInner hOuter hSpin hTypeC hOctonion
    StrongApproximationNontrialitarianD.strongApproximation D G hG hsc ha i S hS hnc with h | h
  · exact h
  have hRemaining : IsTrialitarian G ∨ HasAbsoluteExceptionalType G := h
  cases D with
  | number hK =>
    letI := hK
    let D := numberPlaces K
    have hArch w := hRemaining.elim
      (fun ht => TrialitarianArchimedeanGeneration.archimedeanInputs D rfl G hG.1 hsc ht i w)
      (fun hE => exceptionalArchimedeanInputs i hG hsc hE w)
    apply numberStrongApproximation_of_local i hG ha (.number hK) rfl S hnc D rfl
      (fun w => (hArch w).1) (fun w => (hArch w).2)
    intro w
    obtain ⟨hr, hmix⟩ := finiteInputs_of_remainingTypes D G hG hsc hRemaining w
    exact ⟨hr, finiteGeneration_at_completion D i hG w hmix⟩
  | @function C _ _ _ t =>
    let D := GlobalFieldData.function C t
    apply strongApproximationOfCompactQuotient LocalProjectedClosure.localProjectedClosure
      D G i S (fun w => w.elim) (compactFullAdelicQuotient D i hG.1 ha) hnc
    intro w
    let F := D.FiniteCompletion w
    letI : Algebra K F := completionAlgebra D (.inl w)
    letI : IsTopologicalDivisionRing F := completionTopologicalDivisionRing D (.inl w)
    have hJ := OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G
      (arithmetic_absolute_simplicity hG)
    have hmix := (finiteInputs_of_remainingTypes D G hG hsc hRemaining w).2
    exact ⟨hJ, hmix, completionPointEquiv (F := F) G i,
      (finiteGeneration_at_completion D i hG w hmix).2⟩

end LinearAlgebraicGroups.Arithmetic.AnisotropicSufficiency

universe v8_closure_6eb7609f64a6b179_u0 v8_closure_6eb7609f64a6b179_u1
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«AnisotropicSufficiency».«strongApproximation» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«AnisotropicSufficiency».«StrongApproximationStatement».{v8_closure_6eb7609f64a6b179_u0, v8_closure_6eb7609f64a6b179_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«AnisotropicSufficiency».«strongApproximation_conditional».{v8_closure_6eb7609f64a6b179_u0, v8_closure_6eb7609f64a6b179_u1} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«AnisotropicClassicalApproximation».«characteristicTwoQuadraticNormIndex».{v8_closure_6eb7609f64a6b179_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«AnisotropicClassicalApproximation».«innerTypeA».{v8_closure_6eb7609f64a6b179_u0, v8_closure_6eb7609f64a6b179_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«AnisotropicClassicalApproximation».«localSpinIsotropy».{v8_closure_6eb7609f64a6b179_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«AnisotropicClassicalApproximation».«localUnitaryIsotropy».{v8_closure_6eb7609f64a6b179_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«AnisotropicClassicalApproximation».«octonion».{v8_closure_6eb7609f64a6b179_u0, v8_closure_6eb7609f64a6b179_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«AnisotropicClassicalApproximation».«outerTypeA».{v8_closure_6eb7609f64a6b179_u0, v8_closure_6eb7609f64a6b179_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«AnisotropicClassicalApproximation».«quadraticSpin».{v8_closure_6eb7609f64a6b179_u0, v8_closure_6eb7609f64a6b179_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«AnisotropicClassicalApproximation».«rankOneQuadraticSpin».{v8_closure_6eb7609f64a6b179_u0, v8_closure_6eb7609f64a6b179_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«AnisotropicClassicalApproximation».«typeC».{v8_closure_6eb7609f64a6b179_u0, v8_closure_6eb7609f64a6b179_u1})
