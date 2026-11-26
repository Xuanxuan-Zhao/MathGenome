import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.StrongApproximationNontrialitarianD
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.CompactProductIsolation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.CharacteristicZeroCompactness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.WeakApproximationByTori
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.FunctionFieldAnisotropicCompactness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.NontrialitarianArchimedeanIsotropy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.NontrialitarianCompactRealConnectedness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalCocharacterEvaluation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinCharacteristicTwo
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinIsotropy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinOddCharacteristic
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ScalarEvenSpinLocalDensity
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure
open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj Classical

universe u v

namespace LinearAlgebraicGroups.Arithmetic.StrongApproximationNontrialitarianD

open AdelicGroups (StrongApproximation)
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open Specs.Arithmetic.NontrialitarianSpinModels (HasFixedVectorVertex)
open Specs.IntegralModels (MatrixRealization)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open MeasureTheory Set Topology
open scoped RestrictedProduct
open ArithmeticLatticeProjection (FinitePoints FiniteInvariantQuotientMeasure)
open LocalQuotientTransport (RightCosets RightInvariant coset rightTranslate)

noncomputable section
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- Inversion exchanges left invariance on the quotient by right
multiplication with right invariance on the quotient by left multiplication.
The multiplication-group equivalence can also change coordinates. -/
private theorem rightInvariantMeasureOfFiniteCovolume
    {P J : Type*} [Group P] [Group J] [TopologicalSpace P] [TopologicalSpace J]
    [IsTopologicalGroup P] [IsTopologicalGroup J] (e : P ≃ₜ* J) (H : Subgroup P)
    (hH : FiniteInvariantQuotientMeasure H) :
    ∃ ν : Measure (RightCosets (H.map e.toMulEquiv.toMonoidHom)),
      IsFiniteMeasure ν ∧ ν ≠ 0 ∧ RightInvariant ν := by
  letI : MeasurableSpace (P ⧸ H) := borel (P ⧸ H)
  letI : BorelSpace (P ⧸ H) := ⟨rfl⟩
  obtain ⟨m, hmfinite, hmpos, hminv⟩ := hH
  letI : IsFiniteMeasure m := hmfinite
  letI : m.IsOpenPosMeasure := hmpos
  letI : SMulInvariantMeasure P (P ⧸ H) m := hminv
  let H' := H.map e.toMulEquiv.toMonoidHom
  let q : P ⧸ H → RightCosets H' :=
    Quotient.map' (fun x : P => e x⁻¹) fun x y hxy => by
      rw [QuotientGroup.leftRel_apply] at hxy
      rw [QuotientGroup.rightRel_apply, ← map_inv, ← map_mul, inv_inv]
      exact ⟨y⁻¹ * x, by simpa using H.inv_mem hxy, rfl⟩
  have hq_mk (x : P) : q (QuotientGroup.mk x) = coset H' (e x⁻¹) := rfl
  have hq : Continuous q := by
    apply (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr
    exact (show Continuous (coset H') from continuous_quotient_mk').comp
      (e.continuous.comp continuous_inv)
  let ν := m.map q
  have hνfinite : IsFiniteMeasure ν := Measure.isFiniteMeasure_map m q
  have hνzero : ν ≠ 0 := by
    intro hz
    have hu : ν Set.univ = m Set.univ := by
      rw [Measure.map_apply hq.measurable MeasurableSet.univ, preimage_univ]
    have hp : 0 < m Set.univ := isOpen_univ.measure_pos m Set.univ_nonempty
    exact hp.ne' (by simpa [hz] using hu.symm)
  refine ⟨ν, hνfinite, hνzero, ?_⟩
  intro a
  let b := (e.symm a)⁻¹
  have hb : e b⁻¹ = a := by simp [b]
  have hm : MeasurePreserving (b • ·) m m := measurePreserving_smul _ _
  have hcomm : rightTranslate a ∘ q = q ∘ (b • ·) := by
    funext z
    refine Quotient.inductionOn' z fun x => ?_
    change coset H' (e x⁻¹ * a) = q (QuotientGroup.mk (b * x))
    rw [hq_mk, mul_inv_rev, map_mul, hb]
  have ht : Measurable (rightTranslate (H := H') a) := by
    have hquot : IsQuotientMap (coset H') := isQuotientMap_quotient_mk'
    apply Continuous.measurable
    apply hquot.continuous_iff.mpr
    exact hquot.continuous.comp (continuous_id.mul continuous_const)
  refine ⟨ht, ?_⟩
  change (m.map q).map (rightTranslate a) = m.map q
  rw [Measure.map_map ht hq.measurable, hcomm, ← Measure.map_map hq.measurable hm.measurable,
    hm.map_eq]

open Specs.Arithmetic.LocalProjectedClosure (LocalNormalClosure FiniteCovolumeSubgroup)
open LocalAlgebraicTransport (pointTopology)
open Specs.Arithmetic.LocalQuotientMixing (MixingCases)

private theorem localProjection_eq_top
    (localFull : FiniteCovolumeSubgroup.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F)
    (hsimple : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G)
    (hmixing : MixingCases G)
    {P : Type u} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    (H : Subgroup P) (hclosed : IsClosed (H : Set P)) (hdiscrete : ¬ IsDiscrete (H : Set P))
    (hmeasure : FiniteInvariantQuotientMeasure H) :
    letI := pointTopology G.val.X
    (P ≃ₜ* LocalAlgebraicTransport.RationalPoints G.val.X) → H = ⊤ := by
  letI := pointTopology G.val.X
  intro e
  letI : IsTopologicalGroup (LocalAlgebraicTransport.RationalPoints G.val.X) :=
    Topology.IsInducing.isTopologicalGroup e.symm.toMulEquiv.toMonoidHom
      e.symm.toHomeomorph.isInducing
  let H' := H.map e.toMulEquiv.toMonoidHom
  have hImage : (H' : Set (LocalAlgebraicTransport.RationalPoints G.val.X)) = e '' (H : Set P) := rfl
  have hClosed' : IsClosed (H' : Set (LocalAlgebraicTransport.RationalPoints G.val.X)) := by
    rw [hImage]
    exact e.toHomeomorph.isClosedMap _ hclosed
  have hDiscrete' : ¬ DiscreteTopology H' := by
    intro h
    letI := h
    let f : H → H' := fun x => ⟨e x, ⟨x, x.property, rfl⟩⟩
    have hf : Continuous f := (e.continuous.comp continuous_subtype_val).subtype_mk _
    have hi : Function.Injective f := fun a b h => Subtype.ext (e.injective (congrArg Subtype.val h))
    exact hdiscrete (isDiscrete_iff_discreteTopology.mpr
      (DiscreteTopology.of_continuous_injective hf hi))
  obtain ⟨ν, hνfinite, hνzero, hνinv⟩ := rightInvariantMeasureOfFiniteCovolume e H hmeasure
  letI : IsFiniteMeasure ν := hνfinite
  have he := localFull F G hsimple hmixing H' hClosed' hDiscrete' ν hνzero hνinv
  apply top_unique
  intro x _
  have hx : e x ∈ H' := he.symm ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := hx
  exact e.injective hyx ▸ hy

open AdelicGroups (Adeles LocalPoints Outside localSubgroup PointsIn)
open ArithmeticLatticeProjection (diagonalSubgroup)
open CompactProductIsolation (Contracted diagonalClosure diagonalClosedSubgroup insertFinite
  projectedArithmetic support)

private def singletonProjection
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.Place) :
    FinitePoints D i {w} ≃ₜ* LocalPoints D i w := by
  classical
  letI : Unique {x // x ∈ ({w} : Finset D.Place)} :=
    ⟨⟨⟨w, Finset.mem_singleton_self w⟩⟩,
      fun x => Subtype.ext (Finset.mem_singleton.mp x.2)⟩
  exact { MulEquiv.piUnique (fun x : {x // x ∈ ({w} : Finset D.Place)} =>
      LocalPoints D i x.1) with
    continuous_toFun := continuous_apply (default : {x // x ∈ ({w} : Finset D.Place)})
    continuous_invFun := (Homeomorph.piUnique
      (fun x : {x // x ∈ ({w} : Finset D.Place)} => LocalPoints D i x.1)).symm.continuous }

private theorem denseContractedAlong
    {P J : Type*} [Group P] [Group J] [TopologicalSpace P] [TopologicalSpace J]
    (e : P ≃ₜ* J) (hd : Dense ((Subgroup.closure {x : P | Contracted x}) : Set P)) :
    Dense ((Subgroup.closure {x : J | Contracted x}) : Set J) := by
  apply (e.toHomeomorph.isDenseEmbedding.dense_image.mpr hd).mono
  change e.toMulEquiv.toMonoidHom '' ↑(Subgroup.closure {x : P | Contracted x}) ⊆ _
  rw [← Subgroup.coe_map, MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨x, ⟨a, ha⟩, rfl⟩
  refine ⟨e a, ?_⟩
  have he := (e.continuous.tendsto 1).comp ha
  change Filter.Tendsto (fun n : ℕ => e (a ^ n * x * (a ^ n)⁻¹))
    Filter.atTop (𝓝 (e 1)) at he
  change Filter.Tendsto (fun n : ℕ => e a ^ n * e x * (e a ^ n)⁻¹)
    Filter.atTop (𝓝 1)
  simpa only [Function.comp_apply, map_one, map_mul, map_inv, map_pow] using he

/-- A single outside factor embeds in the diagonal closure once its
closed lattice projection is full and its contractions generate densely. -/
private theorem isolateSingleton
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (S : Finset D.Place) (w : Outside D S)
    (U : Subgroup (Adeles D i (S ∪ {w.1})))
    (hcompact : IsCompact (U : Set (Adeles D i (S ∪ {w.1}))))
    (hopen : IsOpen (U : Set (Adeles D i (S ∪ {w.1}))))
    (hfull : Dense (projectedArithmetic D i S {w.1} U : Set (FinitePoints D i {w.1})))
    (hcontract : Dense ((Subgroup.closure {x : LocalPoints D i w.1 | Contracted x}) :
      Set (LocalPoints D i w.1))) :
    ∀ a : LocalPoints D i w.1,
      RestrictedProduct.mulSingle (fun k : Outside D S => localSubgroup D i k.1) w a ∈
        diagonalClosure D i S := by
  classical
  have hd : Disjoint ({w.1} : Finset D.Place) S := Finset.disjoint_singleton_left.mpr w.2
  have hins := (CompactProductIsolation.isolateAdelicFactors D i S {w.1} hd U hcompact hopen).2
    hfull (denseContractedAlong (singletonProjection D i w.1).symm hcontract)
  intro a
  obtain ⟨x, hx⟩ := CompactProductIsolation.mulSingle_mem_range_insertFinite D i hd
    w (Finset.mem_singleton_self w.1) a
  rw [← hx]
  exact hins x

open ArithmeticLatticeProjection (integralOutside)
open Specs.Unipotent (baseChangedAlgebraicGroup)

private theorem isolateFinitePlace
    (localFull : FiniteCovolumeSubgroup.{u})
    {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (S : Finset D.Place)
    (hCompactArch : ∀ z : D.InfinitePlace, Sum.inr z ∉ S → CompactSpace (LocalPoints D i (.inr z)))
    (hQ : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hS : ¬ CompactSpace (FinitePoints D i S))
    (w : D.FinitePlace) (hw : Sum.inl w ∉ S)
    (hlocal :
        let F := D.Completion (.inl w)
        let G' := baseChangedAlgebraicGroup F G
        Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G' ∧
          MixingCases G' ∧
          (letI := pointTopology G'.val.X
           Nonempty (LocalPoints D i (.inl w) ≃ₜ* LocalAlgebraicTransport.RationalPoints G'.val.X)) ∧
          Dense ((Subgroup.closure {x : LocalPoints D i (.inl w) | Contracted x}) :
            Set (LocalPoints D i (.inl w)))) :
    ∀ a : LocalPoints D i (.inl w),
      RestrictedProduct.mulSingle (fun k : Outside D S => localSubgroup D i k.1) ⟨.inl w, hw⟩ a ∈
        diagonalClosure D i S := by
  classical
  let w₀ : Outside D S := ⟨.inl w, hw⟩
  let J : Finset D.Place := {w₀.1}
  let U := integralOutside D i (S ∪ J)
  have hJ : Disjoint J S := Finset.disjoint_singleton_left.mpr hw
  obtain ⟨hUc, hUo⟩ := ArithmeticLatticeProjection.compactOpenOutside D i (S ∪ J)
    (fun z hz => hCompactArch z (fun hm => hz (Finset.mem_union_left J hm)))
  obtain ⟨hDisc, H, hH, _, hm⟩ :=
    ArithmeticLatticeProjection.projectionProperties D i S (S ∪ J) J U
      Finset.subset_union_left Finset.subset_union_right hQ hS
      (Finset.singleton_nonempty _) hJ hUc hUo
  change (H : Set (FinitePoints D i J)) =
    closure (projectedArithmetic D i S J U : Set (FinitePoints D i J)) at hH
  have hClosed : IsClosed (H : Set (FinitePoints D i J)) := hH ▸ isClosed_closure
  have hND : ¬ IsDiscrete (H : Set (FinitePoints D i J)) := fun hd =>
    hDisc (hd.mono (hH.symm ▸ subset_closure))
  obtain ⟨hSimple, hMix, ⟨e⟩, hContract⟩ := hlocal
  let F := D.Completion (.inl w)
  letI : ValuativeRel F := inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
  letI : IsNonarchimedeanLocalField F := GlobalFieldData.finiteCompletion_isLocalField D w
  let G' := baseChangedAlgebraicGroup F G
  letI := pointTopology G'.val.X
  have hTop := localProjection_eq_top localFull G' hSimple hMix H hClosed hND hm
    ((singletonProjection D i w₀.1).trans e)
  refine isolateSingleton D i S w₀ U hUc hUo ?_ hContract
  rw [dense_iff_closure_eq, ← hH, hTop, Subgroup.coe_top]

/-- A compact full adelic quotient reduces approximation outside a set
containing the archimedean places to the local finite-covolume theorem and contractions. -/
private theorem strongApproximationOfCompactQuotient
    (localFull : FiniteCovolumeSubgroup.{u})
    {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (S : Finset D.Place) (hArch : ∀ w : D.InfinitePlace, Sum.inr w ∈ S)
    (hQ : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hS : ¬ CompactSpace (FinitePoints D i S))
    (hlocal :
      ∀ w : D.FinitePlace,
        let F := D.Completion (.inl w)
        let G' := baseChangedAlgebraicGroup F G
        Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G' ∧
          MixingCases G' ∧
          (letI := pointTopology G'.val.X
           Nonempty (LocalPoints D i (.inl w) ≃ₜ* LocalAlgebraicTransport.RationalPoints G'.val.X)) ∧
          Dense ((Subgroup.closure {x : LocalPoints D i (.inl w) | Contracted x}) :
            Set (LocalPoints D i (.inl w)))) :
    StrongApproximation D i S := by
  classical
  change Dense (CompactProductIsolation.diagonalSet D i S)
  rw [dense_iff_closure_eq]
  change diagonalClosure D i S = Set.univ
  have hsingle : ∀ (w : Outside D S) (a : LocalPoints D i w.1),
      RestrictedProduct.mulSingle (fun k : Outside D S => localSubgroup D i k.1) w a ∈
        diagonalClosure D i S := by
    rintro ⟨w | w, hw⟩
    · exact isolateFinitePlace localFull D G i S (fun z hz => (hz (hArch z)).elim)
        hQ hS w hw (hlocal w)
    · exact (hw (hArch w)).elim
  have hClosed : IsClosed (diagonalClosedSubgroup D i S : Set (Adeles D i S)) := by
    rw [CompactProductIsolation.diagonalClosedSubgroup_coe]
    exact isClosed_closure
  have hAll := CompactProductIsolation.isolatedFactorsSpan D i S Set.univ
    (diagonalClosedSubgroup D i S) hClosed
    (fun w _ a => by
      change _ ∈ (diagonalClosedSubgroup D i S : Set (Adeles D i S))
      rw [CompactProductIsolation.diagonalClosedSubgroup_coe]
      exact hsingle w a)
  rw [CompactProductIsolation.diagonalClosedSubgroup_coe] at hAll
  exact Set.eq_univ_of_forall fun a => hAll (Set.subset_univ _)


section LocalTopology

open Opposite
open AdelicGroups (PointsIn asMatrix)
open Specs.StandardGroups (GLCoordinates universalMatrix)
open Specs.Unipotent (Index)
open private matrixPresentation continuous_glEvaluation glVal_isEmbedding
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private coordinateMap coordinateMap_spec
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
open private glEvaluation glEvaluation_entry
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups

private theorem matrixPointTopology
    {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G) :
    (inferInstance : TopologicalSpace (PointsIn i F)) = pointTopology G.val.X := by
  classical
  obtain ⟨B, ⟨b⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.prop.1
  obtain ⟨a, ha, he⟩ := matrixPresentation B.unop b i
  let j : B.unop →+* Γ(G.val.X.left, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of B.unop)).inv ≫ b.inv.left.appTop).hom
  have hj : Function.Surjective j := by
    dsimp [j]
    intro x
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of B.unop)).hom
      (b.hom.left.appTop x), ?_⟩
    change b.inv.left.appTop ((Scheme.ΓSpecIso _).inv ((Scheme.ΓSpecIso _).hom _)) = _
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply,
      ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    have hb : b.inv.left ≫ b.hom.left = 𝟙 _ :=
      congrArg (fun f => f.left) b.inv_hom_id
    rw [hb, Scheme.Hom.id_appTop, CommRingCat.id_apply]
  have hEval (p : LocalAlgebraicTransport.RationalPoints G.val.X) (x : B.unop) :
      LocalAlgebraicTransport.evaluation p (j x) = coordinateMap (k := F) (p ≫ b.inv) x := by
    dsimp only [j, LocalAlgebraicTransport.evaluation]
    change ((Scheme.ΓSpecIso (CommRingCat.of B.unop)).inv ≫
      b.inv.left.appTop ≫ p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom) x = _
    rw [← Scheme.Hom.comp_appTop_assoc]
    let f := coordinateMap (k := F) (p ≫ b.inv)
    have hf : (p ≫ b.inv).left = Spec.map (CommRingCat.ofHom f.hom.toRingHom) :=
      congrArg (fun g => g.left) (coordinateMap_spec (p ≫ b.inv)).symm
    change ((Scheme.ΓSpecIso (CommRingCat.of B.unop)).inv ≫
      (p ≫ b.inv).left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom) x = _
    rw [hf, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    rfl
  have hcoord (p : PointsIn i F) (z : GLCoordinates F (Index.{u} i.size)) :
      glEvaluation (asMatrix i F p) z = LocalAlgebraicTransport.evaluation p (j (a z)) := by
    rw [hEval]
    exact congrArg (fun q : GLCoordinates F (Index.{u} i.size) →ₐ[F] F => q z) (he F p)
  apply le_antisymm
  · apply continuous_iff_le_induced.mp
    apply continuous_pi
    intro x
    obtain ⟨y, rfl⟩ := hj x
    obtain ⟨z, rfl⟩ := ha y
    simp_rw [← hcoord]
    exact (continuous_glEvaluation z).comp continuous_induced_dom
  · change pointTopology G.val.X ≤ TopologicalSpace.induced (asMatrix i F) inferInstance
    apply continuous_iff_le_induced.mp
    letI := pointTopology G.val.X
    have hemb : IsEmbedding (Units.val :
        Matrix.GeneralLinearGroup (Index.{u} i.size) F → Matrix (Index.{u} i.size) (Index.{u} i.size) F) :=
      glVal_isEmbedding
    apply hemb.isInducing.continuous_iff.mpr
    apply continuous_matrix
    intro l r
    have heq : (fun p : LocalAlgebraicTransport.RationalPoints G.val.X =>
          (asMatrix i F (show PointsIn i F from p)).val l r) =
        fun p => LocalAlgebraicTransport.evaluation p (j (a (universalMatrix F _ l r))) :=
      funext fun p =>
        (glEvaluation_entry (asMatrix i F p) l r).symm.trans
          (hcoord p (universalMatrix F _ l r))
    change Continuous (fun p : LocalAlgebraicTransport.RationalPoints G.val.X =>
      (asMatrix i F (show PointsIn i F from p)).val l r)
    rw [heq]
    exact (continuous_apply _).comp continuous_induced_dom

end LocalTopology

/-- Base change identifies the affine-coordinate group at a completion with
the matrix points of the original global group. -/
private theorem completionPointEquiv
    {K F : Type u} [Field K] [Field F] [Algebra K F] [TopologicalSpace F]
    [IsTopologicalDivisionRing F] (G : AffineAlgebraicGroup K) (i : MatrixRealization G) :
    let J := baseChangedAlgebraicGroup F G
    letI := pointTopology J.val.X
    Nonempty (PointsIn i F ≃ₜ* LocalAlgebraicTransport.RationalPoints J.val.X) := by
  let J := baseChangedAlgebraicGroup F G
  letI := pointTopology J.val.X
  obtain ⟨j, hj⟩ := LocalCocharacterEvaluation.completionPointTopology (F := F) G i
  let e := baseChangePointGroupEquiv F G.val (CommAlgCat.of F F)
  have he : @IsHomeomorph (LocalAlgebraicTransport.RationalPoints J.val.X) (PointsIn i F)
      (pointTopology J.val.X) inferInstance e := by
    rw [← matrixPointTopology J j]
    exact hj
  let e' : LocalAlgebraicTransport.RationalPoints J.val.X ≃* PointsIn i F := e
  exact ⟨(e'.toContinuousMulEquiv (fun _ =>
    he.homeomorph.isQuotientMap.isCoinducing.isOpen_preimage)).symm⟩

section FiniteSpinModels

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Opposite
open scoped Matrix TensorProduct
open LinearAlgebraicGroups.Specs (SubgroupSections)
open Specs.Arithmetic.NontrialitarianSpinModels
  (DescendedQuadraticPair EquivariantSpinTrivialization SpinModel IsOrthogonal)
open Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)
open Specs.CharacterDescent (Cocharacter)
open Specs.Arithmetic.OppositeRadicals (IsNoncentral localPlus)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.Arithmetic.LocalQuotientMixing (IsIsotropicQuadraticSpin IsIsotropicQuaternionicSpin)
open LinearAlgebraicGroups.CocharacterDynamics
  (LimitDecomposition oppositeCocharacter existsLimitDecomposition cocharacterPoint)
open Specs.AdjointRepresentation (GroupPoints)
open private finite_galois_field_over_extension extendSpinTrivialization noncentral_of_ne_zero
  arithmetic_absolute_simplicity from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinCharacteristicTwo
open private spinModel_of_trivialization descendedPair_isOrthogonal
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels
open private recoverOrthogonalForm scalarSpinRepresentation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ScalarEvenSpinLocalDensity
open private nonarchimedean_local_infinite
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinOddCharacteristic
open private testPointSections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private rationalSourceIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalDensity
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility

private theorem absoluteSimplicityOfArithmetic
    {F : Type u} [Field F] {G : AffineAlgebraicGroup F}
    (hG : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G) :
    IsAbsolutelyAlmostSimple G := by
  refine ⟨hG.1, ?_, ?_⟩
  · intro hz
    exact hG.2.1 ⟨hz.iso (Grp.isZero_trivial _)⟩
  · intro N hN
    exact (hG.2.2 N hN).imp (fun ⟨e⟩ => (Grp.isZero_trivial _).of_iso e) id

/-- At a finite completion of characteristic different from two the spin
group has an isotropic scalar or quaternionic presentation. -/
private theorem oddSpinIsotropicModels
    {k K F I : Type u} [Field k] [Field K] [Field F] [Algebra k K] [Algebra k F]
    [FiniteDimensional k K] [IsGalois k K] [Fintype I] [DecidableEq I] [Nonempty I]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : AffineAlgebraicGroup k}
    (C : EquivariantSpinTrivialization (K := K) (I := I) G)
    (D : DescendedQuadraticPair C.action) (M : SpinModel G D)
    (hG : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G)
    (hI : 4 ≤ Fintype.card I) (h₂ : (2 : F) ≠ 0) :
    IsIsotropicQuadraticSpin (baseChangedAlgebraicGroup F G) ∨
      IsIsotropicQuaternionicSpin (baseChangedAlgebraicGroup F G) := by
  classical
  let J := baseChangedAlgebraicGroup F G
  have hJ : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple J :=
    OppositeRadicals.absolutelyAlmostSimpleFieldExtension G hG
  obtain ⟨c, hc⟩ := QuaternionSpinIsotropy.finiteSpinIsotropy G D M hI
    (descendedPair_isOrthogonal D) F h₂
  have hnc : IsNoncentral (G := J.val) c := noncentral_of_ne_zero J hJ.1 c hc
  obtain ⟨T, _, _, _, _, _, _, _, hTower⟩ := finite_galois_field_over_extension k K F
  letI : IsScalarTower k K T := hTower
  obtain ⟨C'⟩ := extendSpinTrivialization (L := F) (T := T) C hI
  obtain ⟨D'⟩ := NontrialitarianSpinModels.quadraticPairDescent F T I C'.action
    (fun σ => ⟨C'.g σ, C'.multiplier σ, C'.actionFormula σ, C'.similarity σ⟩)
  obtain ⟨M'⟩ := spinModel_of_trivialization J hJ.1.2.1 hI C' D'
  obtain ⟨B, _, _, r, hB, _, ⟨e⟩, hdiv⟩ :=
    NontrialitarianSpinModels.nonarchimedeanDivision h₂ D'.centralSimple
      (toDivisionInvolution D'.involution)
  rcases hdiv with hsplit | hBdeg
  · obtain ⟨eB⟩ := hsplit
    let es := e.trans eB.mapMatrix
    letI : Infinite F := nonarchimedean_local_infinite F
    letI : LinearOrder (I ⊕ I) :=
      LinearOrder.lift' (Fintype.equivFin (I ⊕ I)) (Fintype.equivFin (I ⊕ I)).injective
    obtain ⟨E, H, q, b, hq, hH, hE⟩ := recoverOrthogonalForm
      NontrialitarianSpinModels.fieldOrthogonalModel D' h₂ (descendedPair_isOrthogonal D') es
    obtain ⟨spin, hspin⟩ := scalarSpinRepresentation b
      NontrialitarianSpinModels.splitProjectiveSpinAction M' (absoluteSimplicityOfArithmetic hJ)
      h₂ E H hH hE hq
    have hi := OddSpinInnerDescent.spinCocharacterIsotropy q b J spin hq hspin c hnc
    have hd : 5 ≤ Module.finrank F (Fin r → F) := by
      rw [Module.finrank_eq_card_basis b, Fintype.card_sum]
      omega
    exact Or.inl ⟨Fin r → F, inferInstance, inferInstance, inferInstance, q, spin, hd, hq, hi, hspin⟩
  · obtain ⟨d, hd, ⟨Q⟩⟩ :=
      QuaternionSpinOddCharacteristic.quaternionPresentationAtIsotropy
        M' hI h₂ hB hBdeg ⟨r, ⟨e⟩⟩ ⟨c, hnc⟩
    exact Or.inr ⟨T, I, B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, C'.action, D', hB, d, hI, hBdeg,
      fun _ => hd, ⟨M'⟩, ⟨Q⟩⟩

private theorem contractingSubgroup_isContracted
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : AffineAlgebraicGroup F} (i : MatrixRealization G) {c : Cocharacter G.val}
    (P : LimitDecomposition c) (x : PointsIn i F)
    (hx : (show GroupPoints G.val (CommAlgCat.of F F) from x) ∈
      SubgroupSections P.contracting ((testSpec F).obj (op (CommAlgCat.of F F)))) :
    Contracted x := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  letI := isUniformAddGroup_of_addCommGroup (G := F)
  letI : (Valued.v : Valuation F (ValuativeRel.ValueGroupWithZero F)).RankOne :=
    inferInstanceAs (ValuativeRel.valuation F).RankOne
  let normed : NontriviallyNormedField F :=
    Valued.toNontriviallyNormedField F (ValuativeRel.ValueGroupWithZero F)
  obtain ⟨t, ht⟩ := @LocalCocharacterEvaluation.contractingScalarExists.{u} F normed
  refine ⟨cocharacterPoint c (CommAlgCat.of F F)
    (Units.map (algebraMap F F).toMonoidHom t), ?_⟩
  have hscalar : @Continuous F F normed.toNormedField.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      inferInstance (algebraMap F F) := continuous_id
  exact @LocalCocharacterEvaluation.contractingEvaluation.{u,u}
    F _ _ _ G i c P F normed.toNormedField (Algebra.id F) hscalar t ht x hx

private theorem denseContractionsOfOppositeRadicals
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : AffineAlgebraicGroup F} (i : MatrixRealization G) {c : Cocharacter G.val}
    (P : LimitDecomposition c) (Q : LimitDecomposition (oppositeCocharacter c))
    (h : Dense {x : PointsIn i F |
      (show GroupPoints G.val (CommAlgCat.of F F) from x) ∈
        SubgroupSections P.contracting ((testSpec F).obj (op (CommAlgCat.of F F))) ⊔
        SubgroupSections Q.contracting ((testSpec F).obj (op (CommAlgCat.of F F)))}) :
    Dense ((Subgroup.closure {x : PointsIn i F | Contracted x}) : Set (PointsIn i F)) := by
  apply h.mono
  let R := (testSpec F).obj (op (CommAlgCat.of F F))
  let A : Subgroup (GroupPoints G.val (CommAlgCat.of F F)) :=
    Subgroup.closure {x : PointsIn i F | Contracted x}
  change SubgroupSections P.contracting R ⊔ SubgroupSections Q.contracting R ≤ A
  apply sup_le
  · intro x hx
    exact Subgroup.subset_closure (contractingSubgroup_isContracted i P x hx)
  · intro x hx
    exact Subgroup.subset_closure (contractingSubgroup_isContracted i Q x hx)

private theorem mapSectionsToTestPointSubgroup
    {F : Type u} [Field F] {G : AffineAlgebraicGroup F} (U : Specs.ClosedSubgroup G.val) :
    (SubgroupSections U (𝟙_ (SchemeOver F))).map (testPointSections G.val).symm.toMonoidHom =
      SubgroupSections U ((testSpec F).obj (op (CommAlgCat.of F F))) := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
    refine ⟨(rationalSourceIso F).inv ≫ y, ?_⟩
    change ((rationalSourceIso F).inv ≫ y) ≫ U.inclusion.hom.hom =
      (rationalSourceIso F).inv ≫ y ≫ U.inclusion.hom.hom
    exact Category.assoc ..
  · rintro _ ⟨y, rfl⟩
    refine ⟨(rationalSourceIso F).hom ≫ y ≫ U.inclusion.hom.hom,
      ⟨(rationalSourceIso F).hom ≫ y, ?_⟩, ?_⟩
    · change ((rationalSourceIso F).hom ≫ y) ≫ U.inclusion.hom.hom = _
      exact Category.assoc ..
    · change (rationalSourceIso F).inv ≫ (rationalSourceIso F).hom ≫
        y ≫ U.inclusion.hom.hom = _
      exact (rationalSourceIso F).inv_hom_id_assoc _

private theorem denseOppositeRadicalsOfOddSpin
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : AffineAlgebraicGroup F} (i : MatrixRealization G)
    (hsimple : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G)
    (h₂ : (2 : F) ≠ 0)
    (h : IsIsotropicQuadraticSpin G ∨ IsIsotropicQuaternionicSpin G) :
    ∃ (c : Cocharacter G.val) (P : LimitDecomposition c)
      (Q : LimitDecomposition (oppositeCocharacter c)),
      Dense {x : PointsIn i F | (show GroupPoints G.val (CommAlgCat.of F F) from x) ∈
        SubgroupSections P.contracting ((testSpec F).obj (op (CommAlgCat.of F F))) ⊔
        SubgroupSections Q.contracting ((testSpec F).obj (op (CommAlgCat.of F F)))} := by
  classical
  letI : Infinite F := nonarchimedean_local_infinite F
  rcases h with hscalar | hquat
  · obtain ⟨V, _, _, _, q, spin, _, hq, ⟨x, hx, hqx⟩, hspin⟩ := hscalar
    let b : Module.Basis (ULift.{u} (Fin (Module.finrank F V))) F V :=
      (Module.finBasis F V).reindex Equiv.ulift.symm
    obtain ⟨h, _⟩ := IsotropicSpinGeneration.hyperbolicPairExistence q hq x hx hqx
    obtain ⟨c, _, _, _, hgen⟩ := IsotropicSpinGeneration.localSpinGeneration q b G spin hspin hq hsimple h
    obtain ⟨P⟩ := existsLimitDecomposition G c
    obtain ⟨Q⟩ := existsLimitDecomposition G (oppositeCocharacter c)
    have htop := congrArg (Subgroup.map (testPointSections G.val).symm.toMonoidHom) (hgen P Q).2.2
    rw [Subgroup.map_sup, mapSectionsToTestPointSubgroup, mapSectionsToTestPointSubgroup,
      Subgroup.map_top_of_surjective _ (testPointSections G.val).symm.surjective] at htop
    refine ⟨c, P, Q, ?_⟩
    simp only [htop, Subgroup.mem_top, Set.ofPred_true, dense_univ]
  · obtain ⟨K, I, B, _, _, _, _, _, _, _, _, ρ, D, hB, d, hI, hd, hd₀, ⟨M⟩, ⟨Q⟩⟩ := hquat
    obtain ⟨c, _, _, _, _, _, ⟨⟨P⟩, ⟨N⟩⟩, hgen⟩ :=
      QuaternionSpinOddCharacteristic.localGeneration.1 M hsimple hI h₂ hB hd d (hd₀ h₂) Q
    exact ⟨c, P, N, (hgen P N i).2.2⟩

private theorem denseLocalPlusOfOppositeRadicals
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K)
    (i : MatrixRealization G) (w : D.Place)
    (hs : Specs.GeometricRadicals.IsSemisimple (baseChangedAlgebraicGroup (D.Completion w) G)) :
    let F := D.Completion w
    let J := baseChangedAlgebraicGroup F G
    ∀ (j : MatrixRealization J),
    @IsHomeomorph (PointsIn j F) (LocalPoints D i w) _ _
      (baseChangePoint K F G.val.X (CommAlgCat.of F F)) →
    ∀ {c : Cocharacter J.val} (P : LimitDecomposition c) (Q : LimitDecomposition (oppositeCocharacter c)),
      Dense {x : PointsIn j F | (show GroupPoints J.val (CommAlgCat.of F F) from x) ∈
        SubgroupSections P.contracting ((testSpec F).obj (op (CommAlgCat.of F F))) ⊔
        SubgroupSections Q.contracting ((testSpec F).obj (op (CommAlgCat.of F F)))} →
      Dense (localPlus D i w) := by
  intro F J j hj c P Q hd
  apply (hj.homeomorph.isDenseEmbedding.dense_image.mpr hd).mono
  let R := CommAlgCat.of F F
  have hle := RelativeRayGeneration.twoRadicals_le_unipotentGenerated
    (reductive_of_semisimple J hs) P Q
  have hle' := Subgroup.map_mono (f := (testPointSections J.val).symm.toMonoidHom) hle
  change (SubgroupSections P.contracting (𝟙_ (SchemeOver F)) ⊔
    SubgroupSections Q.contracting (𝟙_ (SchemeOver F))).map
      (testPointSections J.val).symm.toMonoidHom ≤ _ at hle'
  rw [Subgroup.map_sup, mapSectionsToTestPointSubgroup, mapSectionsToTestPointSubgroup] at hle'
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨s, hs', hsp⟩ := hle' hp
  refine ⟨s, hs', ?_⟩
  have hpoint : toUnit ((testSpec F).obj (op R)) =
      (rationalSourceIso F).inv := toUnit_unique _ _
  change baseChangePoint K F G.val.X R (toUnit ((testSpec F).obj (op R)) ≫ s) =
    baseChangePoint K F G.val.X R p
  rw [hpoint]
  exact congrArg (baseChangePoint K F G.val.X R)
    (show (testPointSections J.val).symm s = p from hsp)

private theorem finiteCompletionData
    {k K I : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Fintype I] [DecidableEq I] [Nonempty I] {G : AffineAlgebraicGroup k}
    (D : GlobalFieldData.{u,v} k) (i : MatrixRealization G) (w : D.FinitePlace)
    (C : EquivariantSpinTrivialization (K := K) (I := I) G)
    (Q : DescendedQuadraticPair C.action) (M : SpinModel G Q)
    (hG : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G)
    (hI : 4 ≤ Fintype.card I) (h₂ : (2 : k) ≠ 0) :
    let F := D.Completion (.inl w)
    let J := baseChangedAlgebraicGroup F G
    Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple J ∧ MixingCases J ∧
      (letI := pointTopology J.val.X
       Nonempty (LocalPoints D i (.inl w) ≃ₜ* LocalAlgebraicTransport.RationalPoints J.val.X)) ∧
      Dense ((Subgroup.closure {x : LocalPoints D i (.inl w) | Contracted x}) :
        Set (LocalPoints D i (.inl w))) ∧ Dense (localPlus D i (.inl w)) := by
  let F := D.Completion (.inl w)
  letI : ValuativeRel F := GlobalFieldData.instValuativeRelFiniteCompletion D w
  letI : IsNonarchimedeanLocalField F := GlobalFieldData.finiteCompletion_isLocalField D w
  let J := baseChangedAlgebraicGroup F G
  have hJ : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple J :=
    OppositeRadicals.absolutelyAlmostSimpleFieldExtension G hG
  have hF₂ : (2 : F) ≠ 0 := fun he =>
    h₂ ((algebraMap k F).injective (by simpa only [map_ofNat, map_zero] using he))
  have hModel := oddSpinIsotropicModels (F := F) C Q M hG hI hF₂
  have hMix : MixingCases J :=
    hModel.elim (fun h => Or.inr (Or.inr (Or.inl h))) (fun h => Or.inr (Or.inr (Or.inr (Or.inl h))))
  obtain ⟨j, hj⟩ := LocalCocharacterEvaluation.completionPointTopology (F := F) G i
  obtain ⟨_, P, N, hdense⟩ := denseOppositeRadicalsOfOddSpin j hJ hF₂ hModel
  refine ⟨hJ, hMix, completionPointEquiv (F := F) G i, ?_,
    denseLocalPlusOfOppositeRadicals D i (.inl w) hJ.1 j hj P N hdense⟩
  let e : PointsIn j F ≃* PointsIn i F := baseChangePointGroupEquiv F G.val (CommAlgCat.of F F)
  let e' : PointsIn j F ≃ₜ* PointsIn i F :=
    e.toContinuousMulEquiv (fun _ => hj.homeomorph.isQuotientMap.isCoinducing.isOpen_preimage)
  exact denseContractedAlong e' (denseContractionsOfOppositeRadicals j P N hdense)

open private cocharacter_of_split_power empty_power_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank
open private inclusion_mono from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private quotientTopology from MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.FunctionFieldAnisotropicCompactness

private abbrev OmittedProductNoncompact
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (S : Finset D.Place) : Prop :=
  ¬ CompactSpace (FinitePoints D i S)

private theorem compactArithmeticQuotient
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K)
    (i : MatrixRealization G)
    (h : @CompactSpace (Specs.FunctionFieldAnisotropicCompactness.AdelicQuotient D i)
      (quotientTopology D i)) :
    CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) := by
  have he : Specs.FunctionFieldAnisotropicCompactness.rationalDiagonal D i =
      diagonalSubgroup D i := Subgroup.ext fun _ => Iff.rfl
  change CompactSpace (Adeles D i ∅ ⧸ Specs.FunctionFieldAnisotropicCompactness.rationalDiagonal D i) at h
  rwa [he] at h

private theorem existsNonzeroCocharacterOfNotAnisotropic
    {K : Type u} [Field K] (G : AffineAlgebraicGroup K)
    (hG : ¬ Specs.FunctionFieldAnisotropicCompactness.IsAnisotropic G) :
    ∃ c : Cocharacter G.val, c ≠ 0 := by
  classical
  obtain ⟨T, r, hr, ⟨e⟩⟩ := not_not.mp hG
  obtain ⟨c, hc⟩ := cocharacter_of_split_power hr e
  letI := inclusion_mono T
  exact ⟨c ≫ T.inclusion, fun he => hc ((cancel_mono T.inclusion).mp (by simpa only [Limits.zero_comp] using he))⟩

private theorem isotropicStrongApproximation
    {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K)
    (hG : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G)
    (hIso : ¬ Specs.FunctionFieldAnisotropicCompactness.IsAnisotropic G)
    (i : MatrixRealization G) (S : Finset D.Place) (hS : S.Nonempty)
    (hloc : ∀ w : Outside D S, Dense (localPlus D i w.1)) :
    StrongApproximation D i S := by
  obtain ⟨c, hc⟩ := existsNonzeroCocharacterOfNotAnisotropic G hIso
  have hc' := noncentral_of_ne_zero G hG.1 c hc
  obtain ⟨P⟩ := existsLimitDecomposition G c
  obtain ⟨Q⟩ := existsLimitDecomposition G (oppositeCocharacter c)
  exact ((OppositeRadicals.approximation D G i hG c hc' P Q).2.2.2.2 S hS).2 hloc

private theorem existsGlobalSpinModel
    {K : Type u} [Field K] (G : AffineAlgebraicGroup K)
    (n : ℕ) (hn : 4 ≤ n) (hG : IsAbsolutelyAlmostSimple G)
    (hsc : GeometricallySimplyConnected G) (hv : HasFixedVectorVertex G n) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (_ : IsGalois K L)
      (C : EquivariantSpinTrivialization (K := L) (I := ULift.{u} (Fin n)) G)
      (D₀ : DescendedQuadraticPair C.action), Nonempty (SpinModel G D₀) := by
  obtain ⟨L, _, _, _, _, ⟨C⟩⟩ :=
    NontrialitarianSpinModels.finiteEquivariantSpinReference K G n hn hG hsc hv
  let I := ULift.{u} (Fin n)
  have hI : 4 ≤ Fintype.card I := by simpa [I] using hn
  letI : Nonempty I := ⟨ULift.up ⟨0, by omega⟩⟩
  obtain ⟨D₀⟩ := NontrialitarianSpinModels.quadraticPairDescent K L I C.action
    (fun σ => ⟨C.g σ, C.multiplier σ, C.actionFormula σ, C.similarity σ⟩)
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, C, D₀,
    spinModel_of_trivialization G hG.1.2.1 hI C D₀⟩

/-- The function-field branch under the local finite-covolume premise. -/
theorem functionFieldStrongApproximation
    (localFull : FiniteCovolumeSubgroup.{u})
    {K : Type u} [Field K] {k : Type v} [Field k] [Finite k] [Algebra k K]
    (t : SeparatingParameter k K) (G : AffineAlgebraicGroup K)
    (n : ℕ) (hn : 4 ≤ n) (hG : IsAbsolutelyAlmostSimple G)
    (hsc : GeometricallySimplyConnected G) (hv : HasFixedVectorVertex G n)
    (i : MatrixRealization G) (S : Finset (GlobalFieldData.function k t).Place)
    (hS : S.Nonempty) (hNoncompact : OmittedProductNoncompact (GlobalFieldData.function k t) i S) :
    StrongApproximation (GlobalFieldData.function k t) i S := by
  classical
  by_cases h₂ : (2 : K) = 0
  · letI : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 h₂
    exact QuaternionSpinCharacteristicTwo.nontrialitarianStrongApproximation K k t G n hn hG hsc hv i S hS
  let D : GlobalFieldData.{u,v} K := .function k t
  obtain ⟨L, _, _, _, _, C, Q, ⟨M⟩⟩ := existsGlobalSpinModel G n hn hG hsc hv
  let I := ULift.{u} (Fin n)
  have hI : 4 ≤ Fintype.card I := by simpa [I] using hn
  letI : Nonempty I := ⟨ULift.up ⟨0, by omega⟩⟩
  have hs := arithmetic_absolute_simplicity hG
  by_cases hAnis : Specs.FunctionFieldAnisotropicCompactness.IsAnisotropic G
  · have hQ := compactArithmeticQuotient D i
      (FunctionFieldAnisotropicCompactness.functionFieldCompactness t G i hG.1 hAnis)
    apply strongApproximationOfCompactQuotient localFull D G i S
      (fun w => PEmpty.elim w) hQ hNoncompact
    intro w
    obtain ⟨hJ, hMix, he, hContract, _⟩ := finiteCompletionData D i w C Q M hs hI h₂
    exact ⟨hJ, hMix, he, hContract⟩
  · apply isotropicStrongApproximation D G hs hAnis i S hS
    rintro ⟨w | w, _⟩
    · exact (finiteCompletionData D i w C Q M hs hI h₂).2.2.2.2
    · exact PEmpty.elim w


private abbrev FullQuotientCompact
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K)
    (i : MatrixRealization G) : Prop :=
  CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i)

private theorem compactOfCanonicalDiagonal
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K)
    (i : MatrixRealization G) (hQ : Specs.CharacteristicZeroCompactness.CompactAdelicQuotient D i) :
    FullQuotientCompact D i := by
  obtain ⟨d, hd, hcompact⟩ := hQ
  have he : d.range = diagonalSubgroup D i := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, hd g⟩
    · rintro ⟨g, hg⟩
      refine ⟨g, RestrictedProduct.ext _ _ (fun w => (hd g w).trans (hg w).symm)⟩
  unfold FullQuotientCompact
  rwa [he] at hcompact

universe v'

private abbrev adelicPointTopology
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K)
    (i : MatrixRealization G) (S : Finset D.Place) :
    TopologicalSpace (Adeles D i S) := inferInstance

/-- Number-field data with different universe parameters have the same
adelic points under the coordinate identifications at each place. -/
private theorem existsNumberAdelesReindex
    {K : Type u} [Field K] [hK : NumberField K] {G : AffineAlgebraicGroup K}
    (i : MatrixRealization G) (S : Finset (NumberPlace K)) :
    let D₀ := GlobalFieldData.number.{u,v} hK
    let D₁ := GlobalFieldData.number.{u,v'} hK
    letI := adelicPointTopology D₀ i S
    letI := adelicPointTopology D₁ i S
    ∃ E : Adeles D₀ i S ≃ₜ* Adeles D₁ i S,
      ∀ g : Specs.IntegralModels.RationalPoints G,
        E (AdelicGroups.diagonal D₀ i S g) = AdelicGroups.diagonal D₁ i S g := by
  let D₀ := GlobalFieldData.number.{u,v} hK
  let D₁ := GlobalFieldData.number.{u,v'} hK
  letI := adelicPointTopology D₀ i S
  letI := adelicPointTopology D₁ i S
  let p : Outside D₁ S ≃ Outside D₀ S := Equiv.refl _
  let A (a : Outside D₀ S) := LocalPoints D₀ i a.1
  let B (a : Outside D₁ S) := LocalPoints D₁ i a.1
  let (a : Outside D₀ S) : TopologicalSpace (A a) :=
    let : Field (D₀.Completion a.1) := GlobalFieldData.instFieldCompletion D₀ a.1
    let : Algebra K (D₀.Completion a.1) := AdelicGroups.completionAlgebra D₀ a.1
    let : TopologicalSpace (D₀.Completion a.1) := GlobalFieldData.instTopologicalSpaceCompletion D₀ a.1
    inferInstanceAs (TopologicalSpace (PointsIn i (D₀.Completion a.1)))
  let (a : Outside D₁ S) : TopologicalSpace (B a) :=
    let : Field (D₁.Completion a.1) := GlobalFieldData.instFieldCompletion D₁ a.1
    let : Algebra K (D₁.Completion a.1) := AdelicGroups.completionAlgebra D₁ a.1
    let : TopologicalSpace (D₁.Completion a.1) := GlobalFieldData.instTopologicalSpaceCompletion D₁ a.1
    inferInstanceAs (TopologicalSpace (PointsIn i (D₁.Completion a.1)))
  let U (w : Outside D₀ S) := localSubgroup D₀ i w.1
  let V (w : Outside D₁ S) := localSubgroup D₁ i w.1
  let e (x : Outside D₀ S) (y : Outside D₁ S) (h : p y = x) : A x ≃ₜ* B y := by
    subst x
    rcases y with ⟨w | w, hw⟩ <;> exact ContinuousMulEquiv.refl _
  have he (x : Outside D₀ S) (y : Outside D₁ S) (h : p y = x) (a : A x) :
      e x y h a ∈ V y ↔ a ∈ U x := by
    subst x
    rcases y with ⟨w | w, hw⟩ <;> rfl
  obtain ⟨E, hE⟩ := FunctionFieldAnisotropicCompactness.exists_reindexRestrictedProduct p U V e he
  refine ⟨E, fun g => ?_⟩
  apply RestrictedProduct.ext _ _
  intro w
  rw [hE]
  rcases w with ⟨w | w, hw⟩ <;> rfl

private theorem transferNumberAdelicQuotientCompactness
    {K : Type u} [Field K] [hK : NumberField K] {G : AffineAlgebraicGroup K}
    (i : MatrixRealization G) (hQ : FullQuotientCompact (GlobalFieldData.number.{u,v} hK) i) :
    FullQuotientCompact (GlobalFieldData.number.{u,v'} hK) i := by
  let D₀ := GlobalFieldData.number.{u,v} hK
  let D₁ := GlobalFieldData.number.{u,v'} hK
  letI := adelicPointTopology D₀ i ∅
  letI := adelicPointTopology D₁ i ∅
  obtain ⟨E, hE⟩ := existsNumberAdelesReindex.{u,v,v'} i ∅
  have diagonal_mem (a : Adeles D₀ i ∅) : E a ∈ diagonalSubgroup D₁ i ↔ a ∈ diagonalSubgroup D₀ i := by
    have h₀ (a : Adeles D₀ i ∅) : a ∈ diagonalSubgroup D₀ i ↔
        ∃ g, AdelicGroups.diagonal D₀ i ∅ g = a := by
      refine ⟨fun ⟨g, hg⟩ => ⟨g, RestrictedProduct.ext _ _ fun z =>
        (AdelicGroups.diagonalCoordinates D₀ i ∅ g z).trans (hg z).symm⟩, ?_⟩
      rintro ⟨g, rfl⟩
      exact ⟨g, AdelicGroups.diagonalCoordinates D₀ i ∅ g⟩
    have h₁ (a : Adeles D₁ i ∅) : a ∈ diagonalSubgroup D₁ i ↔
        ∃ g, AdelicGroups.diagonal D₁ i ∅ g = a := by
      refine ⟨fun ⟨g, hg⟩ => ⟨g, RestrictedProduct.ext _ _ fun z =>
        (AdelicGroups.diagonalCoordinates D₁ i ∅ g z).trans (hg z).symm⟩, ?_⟩
      rintro ⟨g, rfl⟩
      exact ⟨g, AdelicGroups.diagonalCoordinates D₁ i ∅ g⟩
    rw [h₀, h₁]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, E.injective ((hE g).trans hg)⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, (hE g).symm⟩
  letI : FullQuotientCompact D₀ i := hQ
  let e := FunctionFieldAnisotropicCompactness.rightCosetHomeomorph E
    (diagonalSubgroup D₀ i) (diagonalSubgroup D₁ i) diagonal_mem
  exact e.surjective.compactSpace e.continuous



private theorem transferNumberStrongApproximation
    {K : Type u} [Field K] [hK : NumberField K] {G : AffineAlgebraicGroup K}
    (i : MatrixRealization G) (S : Finset (NumberPlace K))
    (h : StrongApproximation (GlobalFieldData.number.{u,v} hK) i S) :
    StrongApproximation (GlobalFieldData.number.{u,v'} hK) i S := by
  let D₀ := GlobalFieldData.number.{u,v} hK
  let D₁ := GlobalFieldData.number.{u,v'} hK
  letI := adelicPointTopology D₀ i S
  letI := adelicPointTopology D₁ i S
  obtain ⟨E, hE⟩ := existsNumberAdelesReindex.{u,v,v'} i S
  have hd := (AdelicGroups.strongApproximationDensity D₀ i S (AdelicGroups.diagonal D₀ i S)
    (AdelicGroups.diagonalCoordinates D₀ i S)).mp h
  apply (AdelicGroups.strongApproximationDensity D₁ i S (AdelicGroups.diagonal D₁ i S)
    (AdelicGroups.diagonalCoordinates D₁ i S)).mpr
  have he := E.surjective.denseRange.comp hd E.continuous
  have hcomp : E ∘ AdelicGroups.diagonal D₀ i S = AdelicGroups.diagonal D₁ i S := funext hE
  exact hcomp ▸ he

private abbrev finitePointTopology
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K)
    (i : MatrixRealization G) (w : D.Place) : TopologicalSpace (LocalPoints D i w) := inferInstance

private theorem transferNumberOmittedProductNoncompact
    {K : Type u} [Field K] [hK : NumberField K] {G : AffineAlgebraicGroup K}
    (i : MatrixRealization G) (S : Finset (NumberPlace K))
    (h : OmittedProductNoncompact (GlobalFieldData.number.{u,v'} hK) i S) :
    OmittedProductNoncompact (GlobalFieldData.number.{u,v} hK) i S := by
  let D₀ := GlobalFieldData.number.{u,v} hK
  let D₁ := GlobalFieldData.number.{u,v'} hK
  let (w : (↑S : Set (NumberPlace K))) : TopologicalSpace (LocalPoints D₀ i w.1) :=
    finitePointTopology D₀ i w.1
  let (w : (↑S : Set (NumberPlace K))) : TopologicalSpace (LocalPoints D₁ i w.1) :=
    finitePointTopology D₁ i w.1
  let e (w : (↑S : Set (NumberPlace K))) : LocalPoints D₀ i w.1 ≃ₜ LocalPoints D₁ i w.1 := by
    rcases w with ⟨w | w, hw⟩ <;> exact Homeomorph.refl _
  intro hc
  letI : CompactSpace (FinitePoints D₀ i S) := hc
  exact h ((Homeomorph.piCongrRight e).surjective.compactSpace (Homeomorph.piCongrRight e).continuous)


private theorem numberFieldArithmeticQuotientIsCompact
    {K : Type u} [Field K] [hK : NumberField K] (G : AffineAlgebraicGroup K)
    (hG : Specs.GeometricRadicals.IsSemisimple G)
    (hAnis : Specs.FunctionFieldAnisotropicCompactness.IsAnisotropic G)
    (i : MatrixRealization G) :
    FullQuotientCompact (GlobalFieldData.number.{u,v} hK) i := by
  have hAnis' : Specs.AnisotropicAdNilpotents.IsAnisotropic G.val := by
    intro T hT
    obtain ⟨r, ⟨e⟩⟩ := hT
    have hr : r = 0 := Nat.eq_zero_of_not_pos (fun hp => hAnis ⟨T, r, hp, ⟨e⟩⟩)
    subst r
    exact ⟨e ≪≫ empty_power_iso⟩
  have hQ := compactOfCanonicalDiagonal (GlobalFieldData.number.{u,0} hK) i
    (CharacteristicZeroCompactness.anisotropicAdelicCompactness G hG hAnis' i)
  exact transferNumberAdelicQuotientCompactness.{u,0,v} i hQ

/-- Over a number field, strong approximation when the omitted set contains
all archimedean places, under the local finite-covolume premise. -/
theorem numberFieldStrongApproximationOfArchimedeanPlacesIncluded
    (localFull : FiniteCovolumeSubgroup.{u})
    {K : Type u} [Field K] [hK : NumberField K]
    (D : GlobalFieldData.{u,v} K) (hD : D = .number hK)
    (G : AffineAlgebraicGroup K) (n : ℕ) (hn : 4 ≤ n)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (hv : HasFixedVectorVertex G n) (i : MatrixRealization G) (S : Finset D.Place)
    (hS : S.Nonempty) (hNoncompact : OmittedProductNoncompact D i S)
    (hArch : ∀ w : D.InfinitePlace, Sum.inr w ∈ S) : StrongApproximation D i S := by
  classical
  obtain ⟨L, _, _, _, _, C, Q, ⟨M⟩⟩ := existsGlobalSpinModel G n hn hG hsc hv
  let I := ULift.{u} (Fin n)
  have hI : 4 ≤ Fintype.card I := by simpa [I] using hn
  letI : Nonempty I := ⟨ULift.up ⟨0, by omega⟩⟩
  have hs := arithmetic_absolute_simplicity hG
  have h₂ : (2 : K) ≠ 0 := two_ne_zero
  by_cases hAnis : Specs.FunctionFieldAnisotropicCompactness.IsAnisotropic G
  · have hQ : FullQuotientCompact D i :=
      hD.symm ▸ numberFieldArithmeticQuotientIsCompact.{u,v} G hG.1 hAnis i
    apply strongApproximationOfCompactQuotient localFull D G i S hArch hQ hNoncompact
    intro w
    obtain ⟨hJ, hMix, he, hContract, _⟩ := finiteCompletionData D i w C Q M hs hI h₂
    exact ⟨hJ, hMix, he, hContract⟩
  · apply isotropicStrongApproximation D G hs hAnis i S hS
    rintro ⟨w | w, hw⟩
    · exact (finiteCompletionData D i w C Q M hs hI h₂).2.2.2.2
    · exact (hw (hArch w)).elim


section NumberFieldAssembly

open Specs.Arithmetic.ProjectiveRecurrence
  (cocharacterRadicalPoints localPointSet evaluateArchimedean)
open ArithmeticLatticeProjection (forgetPlaces rationalProjection)
open private forgetPlaces_surjective forgetPlaces_continuous
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection

private theorem denseContractedProduct
    {X : Type u} [Finite X] {L : X → Type u} [∀ x, Group (L x)] [∀ x, TopologicalSpace (L x)]
    [∀ x, IsTopologicalGroup (L x)]
    (h : ∀ x, Dense ((Subgroup.closure {a : L x | Contracted a}) : Set (L x))) :
    Dense ((Subgroup.closure {a : (x : X) → L x | Contracted a}) : Set ((x : X) → L x)) := by
  classical
  let A := Subgroup.closure {a : (x : X) → L x | Contracted a}
  apply dense_iff_closure_eq.mpr
  rw [← Subgroup.topologicalClosure_coe]
  apply Set.eq_univ_of_forall
  intro f
  apply Subgroup.pi_mem_of_mulSingle_mem
  intro x
  let e := MonoidHom.mulSingle L x
  have he : Continuous e := continuous_mulSingle x
  have hsub : Subgroup.closure {a : L x | Contracted a} ≤ A.topologicalClosure.comap e := by
    apply (Subgroup.closure_le _).mpr
    rintro a ⟨b, hb⟩
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_closure
    refine ⟨e b, ?_⟩
    have h' := (he.tendsto 1).comp hb
    change Filter.Tendsto (fun n : ℕ => e (b ^ n * a * (b ^ n)⁻¹))
      Filter.atTop (𝓝 (e 1)) at h'
    simpa only [Function.comp_apply, map_one, map_pow, map_mul, map_inv] using h'
  exact closure_minimal hsub (A.isClosed_topologicalClosure.preimage he)
    (h x (f x))

private theorem denseContractedArchimedean
    {K : Type u} [Field K] [hK : NumberField K]
    (D : GlobalFieldData.{u,u} K) (hD : D = .number hK)
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G) (w : D.InfinitePlace)
    (h : Dense ((Subgroup.closure
      (localPointSet D i (.inr w) (cocharacterRadicalPoints
        (baseChangedAlgebraicGroup (D.Completion (.inr w)) G)))) : Set (LocalPoints D i (.inr w)))) :
    Dense ((Subgroup.closure {x : LocalPoints D i (.inr w) | Contracted x}) :
      Set (LocalPoints D i (.inr w))) := by
  have hscalar : ∀ w : D.InfinitePlace, ∃ a : Algebra ℝ (D.Completion (.inr w)),
      @Continuous ℝ (D.Completion (.inr w)) _ _ (@algebraMap ℝ (D.Completion (.inr w)) _ _ a) := by
    subst D
    intro w
    obtain ⟨a, _, ha⟩ := LocalCocharacterEvaluation.archimedeanCompletionScalars w
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hscalar w
  let F := D.Completion (.inr w)
  letI : Algebra ℝ F := a
  let J := baseChangedAlgebraicGroup F G
  obtain ⟨j, hj⟩ := LocalCocharacterEvaluation.completionPointTopology (F := F) G i
  let e : PointsIn j F ≃* LocalPoints D i (.inr w) :=
    baseChangePointGroupEquiv F G.val (CommAlgCat.of F F)
  let e' : PointsIn j F ≃ₜ* LocalPoints D i (.inr w) :=
    e.toContinuousMulEquiv (fun _ => hj.homeomorph.isQuotientMap.isCoinducing.isOpen_preimage)
  obtain ⟨t, ht⟩ := LocalCocharacterEvaluation.contractingScalarExists (E := ℝ)
  apply h.mono
  apply Subgroup.closure_mono
  rintro g ⟨p, ⟨c, P, hp⟩, hg⟩
  have hg' : g = e' p := by
    change (show Points G.val.X ((restrictTestAlgebra K F).obj (CommAlgCat.of F F)) from g) = _
    ext
    exact hg
  subst g
  let p' : PointsIn j F := p
  change Contracted (e' p')
  let b : PointsIn j F :=
    cocharacterPoint c (CommAlgCat.of F F) (Units.map (algebraMap ℝ F).toMonoidHom t)
  have hconv := LocalCocharacterEvaluation.contractingEvaluation J j c P ha t ht p' hp
  refine ⟨e' b, ?_⟩
  have hcomp := (e'.continuous.tendsto 1).comp hconv
  change Filter.Tendsto (fun m : ℕ => e' (b ^ m * p' * (b ^ m)⁻¹))
    Filter.atTop (𝓝 (e' 1)) at hcomp
  simpa only [map_one, map_pow, map_mul, map_inv] using hcomp

private theorem weakApproximationAtConnectedFactors
    {K : Type u} [Field K] [hK : NumberField K]
    (D : GlobalFieldData.{u,u} K) (hD : D = .number hK)
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : Specs.GeometricRadicals.IsSemisimple G)
    (T : Finset D.Place) [∀ w : (↑T : Set D.Place), ConnectedSpace (LocalPoints D i w.1)] :
    DenseRange (rationalProjection D i T) := by
  have hopen : IsOpen (closure (range (rationalProjection D i T))) := by
    subst D
    exact WeakApproximationByTori.identityNeighborhood G hG i T
  apply dense_iff_closure_eq.mpr
  let H := (rationalProjection D i T).range.topologicalClosure
  have hclopen : IsClopen (closure (range (rationalProjection D i T))) := ⟨isClosed_closure, hopen⟩
  have h1 : (1 : FinitePoints D i T) ∈ closure (range (rationalProjection D i T)) :=
    subset_closure ⟨1, map_one _⟩
  have h := hclopen.connectedComponent_subset h1
  rw [PreconnectedSpace.connectedComponent_eq_univ] at h
  exact Set.eq_univ_of_univ_subset h


private def archimedeanPlaceEmbedding {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K) :
    D.InfinitePlace ↪ D.Place := ⟨Sum.inr, Sum.inr_injective⟩

private def archimedeanProductEquiv
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K)
    (i : MatrixRealization G) (A : Finset D.InfinitePlace) :
    FinitePoints D i (A.map (archimedeanPlaceEmbedding D)) ≃ₜ*
      ((w : ↑A) → LocalPoints D i (.inr w.val)) := by
  classical
  let f : (↑A : Set D.InfinitePlace) → (↑(A.map (archimedeanPlaceEmbedding D)) : Set D.Place) :=
    fun w => ⟨.inr w.val, Finset.mem_map.mpr ⟨w.val, w.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => Subtype.ext (Sum.inr_injective (congrArg Subtype.val h)), ?_⟩
    intro x
    obtain ⟨w, hw, he⟩ := Finset.mem_map.mp x.property
    exact ⟨⟨w, hw⟩, Subtype.ext he⟩
  let e := Equiv.ofBijective f hf
  exact { (Homeomorph.piCongrLeft (Y := fun z : (↑(A.map (archimedeanPlaceEmbedding D)) :
      Set D.Place) => LocalPoints D i z.1) e).symm with map_mul' := fun _ _ => rfl }

private theorem isolateNoncompactArchimedeanFactors
    {K : Type u} [Field K] [hK : NumberField K]
    (D : GlobalFieldData.{u,u} K) (hD : D = .number hK)
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G)
    (S : Finset D.Place) (A : Finset D.InfinitePlace)
    (hA : ∀ w : D.InfinitePlace, w ∈ A ↔ Sum.inr w ∉ S ∧ ¬ CompactSpace (LocalPoints D i (.inr w)))
    (hQ : FullQuotientCompact D i) (hS : OmittedProductNoncompact D i S)
    (hLocal : ∀ w : ↑A, Dense ((Subgroup.closure
      (localPointSet D i (.inr w.val) (cocharacterRadicalPoints
        (baseChangedAlgebraicGroup (D.Completion (.inr w.val)) G)))) : Set (LocalPoints D i (.inr w.val)))) :
    let J := A.map (archimedeanPlaceEmbedding D)
    ((CompactProductIsolation.forgetOutside D i (S := S) (T := S ∪ J)
      Finset.subset_union_left).ker : Set (Adeles D i S)) ⊆ diagonalClosure D i S := by
  classical
  intro J
  let T := S ∪ J
  have hJS : Disjoint J S := Finset.disjoint_left.mpr fun _ hz hsz => by
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
    exact ((hA w).mp hw).1 hsz
  have hTK : ∀ w : D.InfinitePlace, Sum.inr w ∉ T → CompactSpace (LocalPoints D i (.inr w)) := by
    intro w hw
    by_contra hnc
    have ha := (hA w).mpr ⟨fun h => hw (Finset.mem_union_left _ h), hnc⟩
    exact hw (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨w, ha, rfl⟩))
  let U := integralOutside D i T
  obtain ⟨hUc, hUo⟩ := ArithmeticLatticeProjection.compactOpenOutside D i T hTK
  rw [← CompactProductIsolation.range_insertFinite_eq_ker D i hJS]
  rintro _ ⟨x, rfl⟩
  by_cases hAne : A.Nonempty
  · have hAS (w : ↑A) : Sum.inr w.val ∉ S := ((hA w.val).mp w.property).1
    have hAT (w : ↑A) : Sum.inr w.val ∈ T :=
      Finset.mem_union_right _ (Finset.mem_map.mpr ⟨w.val, w.property, rfl⟩)
    have hProjection := ProjectiveRecurrence.archimedeanLatticeProjection G i D hD
      S T A U Finset.subset_union_left hAne hAS hAT hQ hS hUc hUo hG hLocal
    let e := archimedeanProductEquiv D i A
    have he : e.toMulEquiv.toMonoidHom.comp (forgetPlaces D i (J := J) Finset.subset_union_right) =
        evaluateArchimedean D i A hAT := rfl
    have hFull : Dense (projectedArithmetic D i S J U : Set (FinitePoints D i J)) := by
      apply e.toHomeomorph.isDenseEmbedding.dense_image.mp
      change Dense (e.toMulEquiv.toMonoidHom '' (projectedArithmetic D i S J U : Set (FinitePoints D i J)))
      rw [← Subgroup.coe_map, projectedArithmetic, Subgroup.map_map, he]
      exact hProjection
    have hContract : Dense ((Subgroup.closure {a : FinitePoints D i J | Contracted a}) :
        Set (FinitePoints D i J)) :=
      denseContractedAlong e.symm (denseContractedProduct (fun w =>
        denseContractedArchimedean D hD G i w.val (hLocal w)))
    exact (CompactProductIsolation.isolateAdelicFactors D i S J hJS U hUc hUo).2 hFull hContract x
  · have hx : x = 1 := funext fun z => by
      obtain ⟨w, hw, _⟩ := Finset.mem_map.mp z.property
      exact (hAne ⟨w, hw⟩).elim
    subst x
    have h1 : insertFinite D i S J 1 = 1 := RestrictedProduct.ext _ _ fun w => by
      rw [CompactProductIsolation.insertFinite_apply]
      split_ifs <;> rfl
    rw [← CompactProductIsolation.diagonalClosedSubgroup_coe, h1]
    exact (diagonalClosedSubgroup D i S).one_mem

set_option maxHeartbeats 600000 in
private theorem anisotropicNumberFieldApproximationOfLocalData
    (localFull : FiniteCovolumeSubgroup.{u})
    {K : Type u} [Field K] [hK : NumberField K]
    (D : GlobalFieldData.{u,u} K) (hD : D = .number hK)
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G)
    (S : Finset D.Place) (hS : OmittedProductNoncompact D i S)
    (hQ : FullQuotientCompact D i)
    (hFinite : ∀ w : D.FinitePlace,
        let F := D.Completion (.inl w)
        let J := baseChangedAlgebraicGroup F G
        Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple J ∧
          MixingCases J ∧
          (letI := pointTopology J.val.X
           Nonempty (LocalPoints D i (.inl w) ≃ₜ* LocalAlgebraicTransport.RationalPoints J.val.X)) ∧
          Dense ((Subgroup.closure {x : LocalPoints D i (.inl w) | Contracted x}) :
            Set (LocalPoints D i (.inl w))))
    (hArch : ∀ w : D.InfinitePlace, Sum.inr w ∉ S →
      ¬ CompactSpace (LocalPoints D i (.inr w)) → Dense ((Subgroup.closure
        (localPointSet D i (.inr w) (cocharacterRadicalPoints
          (baseChangedAlgebraicGroup (D.Completion (.inr w)) G)))) : Set (LocalPoints D i (.inr w))))
    (hConnected : ∀ w : D.InfinitePlace, Sum.inr w ∉ S →
      CompactSpace (LocalPoints D i (.inr w)) → ConnectedSpace (LocalPoints D i (.inr w))) :
    StrongApproximation D i S := by
  classical
  have hFin : Finite D.InfinitePlace := by
    subst D
    exact inferInstanceAs (Finite (NumberField.InfinitePlace K))
  letI : Fintype D.InfinitePlace := Fintype.ofFinite _
  let A : Finset D.InfinitePlace := Finset.univ.filter
    (fun w => Sum.inr w ∉ S ∧ ¬ CompactSpace (LocalPoints D i (.inr w)))
  let J := A.map (archimedeanPlaceEmbedding D)
  let T := S ∪ J
  have hA (w : D.InfinitePlace) : w ∈ A ↔ Sum.inr w ∉ S ∧ ¬ CompactSpace (LocalPoints D i (.inr w)) := by
    simp [A]
  have hKer := isolateNoncompactArchimedeanFactors D hD G i hG S A hA hQ hS
    (fun w => hArch w.val ((hA w.val).mp w.property).1 ((hA w.val).mp w.property).2)
  have hST : S ⊆ T := Finset.subset_union_left
  apply ((CompactProductIsolation.enlargeOmittedSet D i S T hST).2 hKer).2.2.mp
  have hNT : ¬ CompactSpace (FinitePoints D i T) := by
    intro h
    exact hS ((forgetPlaces_surjective D i hST).compactSpace (forgetPlaces_continuous D i hST))
  have hCompact (w : D.InfinitePlace) (hw : Sum.inr w ∉ T) : CompactSpace (LocalPoints D i (.inr w)) := by
    by_contra hnc
    have ha := (hA w).mpr ⟨fun hs => hw (hST hs), hnc⟩
    exact hw (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨w, ha, rfl⟩))
  let B := (Finset.univ.filter (fun w : D.InfinitePlace => Sum.inr w ∉ T)).map
    (archimedeanPlaceEmbedding D)
  have hBT : Disjoint B T := Finset.disjoint_left.mpr fun z hz ht => by
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
    exact (Finset.mem_filter.mp hw).2 ht
  letI hConn (z : (↑B : Set D.Place)) : ConnectedSpace (LocalPoints D i z.1) := by
    obtain ⟨w, hw, hzw⟩ := Finset.mem_map.mp z.property
    have hwt := (Finset.mem_filter.mp hw).2
    change Sum.inr w = z.1 at hzw
    rw [← hzw]
    exact hConnected w (fun hs => hwt (hST hs)) (hCompact w hwt)
  have hDensity := weakApproximationAtConnectedFactors D hD G i hG.1 B
  have hFactor : ∀ w : Outside D T, w.1 ∉ B → ∀ a : LocalPoints D i w.1,
      RestrictedProduct.mulSingle (fun k : Outside D T => localSubgroup D i k.1) w a ∈
        diagonalClosure D i T := by
    rintro ⟨w | w, hw⟩ hwB
    · exact isolateFinitePlace localFull D G i T hCompact hQ hNT w hw (hFinite w)
    · exact (hwB (Finset.mem_map.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩, rfl⟩)).elim
  exact ((CompactProductIsolation.projectToRemainingPlaces D i T B hBT).2 hFactor).2.2.mp hDensity

end NumberFieldAssembly


section IsotropicArchimedeanFactors

open scoped TensorProduct
open private transferFieldPresentation cancelFieldEquiv divisionRingOfEquiv
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinIsotropy
open private scalarMatrixBaseChange matrixBaseChange
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms
open private radicalGenerationOfSpinRepresentation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ScalarEvenSpinLocalDensity
open private localPlus_eq_univ from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
open _root_.Specs.RM03.CSA (isCentralSimple degree)

private theorem realOrComplexCompletion
    {K : Type u} [Field K] [hK : NumberField K]
    (D : GlobalFieldData.{u,v} K) (hD : D = .number hK) (w : D.InfinitePlace) :
    let F := D.Completion (.inr w)
    (∃ R : F ≃+* ℝ, IsHomeomorph R) ∨ (∃ C : F ≃+* ℂ, IsHomeomorph C) := by
  revert w
  rw [hD]
  intro w
  change (∃ R : w.Completion ≃+* ℝ, IsHomeomorph R) ∨
    (∃ C : w.Completion ≃+* ℂ, IsHomeomorph C)
  rcases w.isReal_or_isComplex with hw | hw
  · obtain ⟨e, he⟩ := numberRealCompletion w hw
    have hh : IsHomeomorph (e : w.Completion → ℝ) :=
      isHomeomorph_iff_isEmbedding_surjective.mpr ⟨he.isEmbedding, e.surjective⟩
    exact Or.inl ⟨e, hh⟩
  · obtain ⟨e, he⟩ := numberComplexCompletion w hw
    have hh : IsHomeomorph (e : w.Completion → ℂ) :=
      isHomeomorph_iff_isEmbedding_surjective.mpr ⟨he.isEmbedding, e.surjective⟩
    exact Or.inr ⟨e, hh⟩

private theorem splitOrthogonalModelRadicals
    {F K I : Type u} [Field F] [Infinite F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] [Fintype I] [DecidableEq I] [Nonempty I]
    {G : AffineAlgebraicGroup F}
    (C : EquivariantSpinTrivialization (K := K) (I := I) G)
    (D : DescendedQuadraticPair C.action) (M : SpinModel G D)
    (hG : IsAbsolutelyAlmostSimple G) (h₂ : (2 : F) ≠ 0)
    {r : ℕ} (e : C.action.fixedSubalgebra ≃ₐ[F] Matrix (Fin r) (Fin r) F)
    (c : Cocharacter G.val) (hc : IsNoncentral c) :
    unipotentGenerated G = ⊤ := by
  letI : LinearOrder (I ⊕ I) :=
    LinearOrder.lift' (Fintype.equivFin (I ⊕ I)) (Fintype.equivFin (I ⊕ I)).injective
  obtain ⟨E, H, q, b, hq, hH, hE⟩ := recoverOrthogonalForm
    NontrialitarianSpinModels.fieldOrthogonalModel D h₂ (descendedPair_isOrthogonal D) e
  obtain ⟨spin, hspin⟩ := scalarSpinRepresentation b
    NontrialitarianSpinModels.splitProjectiveSpinAction M hG h₂ E H hH hE hq
  exact radicalGenerationOfSpinRepresentation hG q b spin hq hspin c hc

private theorem archimedeanLocalPlusDense
    {k K I : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Fintype I] [DecidableEq I] [Nonempty I] {G : AffineAlgebraicGroup k} [hK : NumberField k]
    (D : GlobalFieldData.{u,v} k) (hD : D = .number hK)
    (i : MatrixRealization G) (w : D.InfinitePlace)
    (C : EquivariantSpinTrivialization (K := K) (I := I) G)
    (hG : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G)
    (hI : 4 ≤ Fintype.card I)
    (hIso : ∃ c : Cocharacter (baseChangedAlgebraicGroup (D.Completion (.inr w)) G).val,
      IsNoncentral c) : Dense (localPlus D i (.inr w)) := by
  let F := D.Completion (.inr w)
  let J := baseChangedAlgebraicGroup F G
  obtain ⟨c, hc⟩ := hIso
  have hJ : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple J :=
    OppositeRadicals.absolutelyAlmostSimpleFieldExtension G hG
  obtain ⟨T, _, _, _, _, _, _, _, hTower⟩ := finite_galois_field_over_extension k K F
  letI : IsScalarTower k K T := hTower
  obtain ⟨C'⟩ := extendSpinTrivialization (L := F) (T := T) C hI
  obtain ⟨Q⟩ := NontrialitarianSpinModels.quadraticPairDescent F T I C'.action
    (fun σ => ⟨C'.g σ, C'.multiplier σ, C'.actionFormula σ, C'.similarity σ⟩)
  obtain ⟨M⟩ := spinModel_of_trivialization J hJ.1.2.1 hI C' Q
  let A := C'.action.fixedSubalgebra
  have h₂ : (2 : F) ≠ 0 := fun h =>
    (two_ne_zero : (2 : k) ≠ 0) ((algebraMap k F).injective
      (by simpa only [map_ofNat, map_zero] using h))
  have hscalar (r : ℕ) (e : A ≃ₐ[F] Matrix (Fin r) (Fin r) F) (hInfinite : Infinite F) :
      Dense (localPlus D i (.inr w)) := by
    letI := hInfinite
    have htop := splitOrthogonalModelRadicals C' Q M (absoluteSimplicityOfArithmetic hJ) h₂ e c hc
    rw [localPlus_eq_univ D i (.inr w) htop]
    exact dense_univ
  rcases realOrComplexCompletion D hD w with ⟨R, hR⟩ | ⟨R, _⟩
  · letI : Algebra F ℝ := R.toRingHom.toAlgebra
    letI : Algebra ℝ F := R.symm.toRingHom.toAlgebra
    have hA : isCentralSimple ℝ (ℝ ⊗[F] A) :=
      _root_.RM03.CSA.isCentralSimple_baseChange Q.centralSimple
    obtain ⟨r, _, h | h⟩ := NontrialitarianSpinModels.archimedeanDivision.1 hA
    · obtain ⟨e⟩ := h
      exact hscalar r ((transferFieldPresentation R e).trans
        (scalarMatrixBaseChange (F := ℝ) (R := F) (Fin r)))
        (Infinite.of_injective R.symm R.symm.injective)
    · obtain ⟨e⟩ := h
      let B := F ⊗[ℝ] Quaternion ℝ
      letI : DivisionRing B := divisionRingOfEquiv (cancelFieldEquiv R.symm).toRingEquiv
      have hH : isCentralSimple ℝ (Quaternion ℝ) := _root_.RM03.CSA.isCentralSimple_of_isCentralDivision
        ℝ (Quaternion ℝ) _root_.RM03.Brauer.QuaternionSplitting.hamilton_central_division
      have hB : isCentralSimple F B := _root_.RM03.CSA.isCentralSimple_baseChange hH
      have hdB : degree F B = 2 := by
        change Nat.sqrt (Module.finrank F B) = 2
        rw [_root_.RM03.CSA.finrank_baseChange hH, Quaternion.finrank_eq_four]
        exact Nat.sqrt_eq' 2
      let e' : A ≃ₐ[F] Matrix (Fin r) (Fin r) B :=
        (transferFieldPresentation R e).trans (matrixBaseChange (F := ℝ) (R := F) (Fin r))
      obtain ⟨d, hd, ⟨Q'⟩⟩ :=
        QuaternionSpinOddCharacteristic.quaternionPresentationAtIsotropy
          M hI h₂ hB hdB ⟨r, ⟨e'⟩⟩ ⟨c, hc⟩
      obtain ⟨_, _, _, _, _, _, ⟨⟨P⟩, ⟨N⟩⟩, hgen⟩ :=
        QuaternionSpinOddCharacteristic.localGeneration.2 R hR M hJ hI hB hdB d hd Q'
      obtain ⟨j, hj⟩ := LocalCocharacterEvaluation.completionPointTopology (F := F) G i
      exact denseLocalPlusOfOppositeRadicals D i (.inr w) hJ.1 j hj P N (hgen P N j).2.2
  · letI : Algebra F ℂ := R.toRingHom.toAlgebra
    letI : Algebra ℂ F := R.symm.toRingHom.toAlgebra
    have hA : isCentralSimple ℂ (ℂ ⊗[F] A) :=
      _root_.RM03.CSA.isCentralSimple_baseChange Q.centralSimple
    obtain ⟨r, _, ⟨e⟩⟩ := NontrialitarianSpinModels.archimedeanDivision.2 hA
    exact hscalar r ((transferFieldPresentation R e).trans
      (scalarMatrixBaseChange (F := ℂ) (R := F) (Fin r)))
      (Infinite.of_injective R.symm R.symm.injective)


private theorem isotropicNumberFieldStrongApproximation
    {K : Type u} [Field K] [hK : NumberField K]
    (D : GlobalFieldData.{u,v} K) (hD : D = .number hK)
    (G : AffineAlgebraicGroup K) (n : ℕ) (hn : 4 ≤ n)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (hv : HasFixedVectorVertex G n)
    (hIso : ¬ Specs.FunctionFieldAnisotropicCompactness.IsAnisotropic G)
    (i : MatrixRealization G) (S : Finset D.Place) (hS : S.Nonempty) :
    StrongApproximation D i S := by
  classical
  obtain ⟨L, _, _, _, _, C, Q, ⟨M⟩⟩ := existsGlobalSpinModel G n hn hG hsc hv
  let I := ULift.{u} (Fin n)
  have hI : 4 ≤ Fintype.card I := by simpa [I] using hn
  letI : Nonempty I := ⟨ULift.up ⟨0, by omega⟩⟩
  have hs := arithmetic_absolute_simplicity hG
  obtain ⟨c, hc⟩ := existsNonzeroCocharacterOfNotAnisotropic G hIso
  have hc' := noncentral_of_ne_zero G hG.1 c hc
  obtain ⟨P⟩ := existsLimitDecomposition G c
  obtain ⟨N⟩ := existsLimitDecomposition G (oppositeCocharacter c)
  apply isotropicStrongApproximation D G hs hIso i S hS
  rintro ⟨w | w, hw⟩
  · exact (finiteCompletionData D i w C Q M hs hI (two_ne_zero : (2 : K) ≠ 0)).2.2.2.2
  · obtain ⟨e, _, hnc, _⟩ := OppositeRadicals.localGeneration D G i hs c hc' P N (.inr w)
    exact archimedeanLocalPlusDense D hD i w C hs hI
      ⟨e.hom ≫ (groupBaseChange K (D.Completion (.inr w))).map c, hnc⟩

set_option maxHeartbeats 650000 in
private theorem archimedeanRadicalsDenseOfIsotropic
    {k K I : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Fintype I] [DecidableEq I] [Nonempty I] {G : AffineAlgebraicGroup k} [hK : NumberField k]
    (D : GlobalFieldData.{u,v} k) (hD : D = .number hK)
    (i : MatrixRealization G) (w : D.InfinitePlace)
    (C : EquivariantSpinTrivialization (K := K) (I := I) G)
    (hG : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G)
    (hI : 4 ≤ Fintype.card I)
    (hIso : ∃ c : Cocharacter (baseChangedAlgebraicGroup (D.Completion (.inr w)) G).val,
      IsNoncentral c) :
    Dense ((Subgroup.closure (Specs.Arithmetic.ProjectiveRecurrence.localPointSet D i (.inr w)
      (Specs.Arithmetic.ProjectiveRecurrence.cocharacterRadicalPoints
        (baseChangedAlgebraicGroup (D.Completion (.inr w)) G)))) : Set (LocalPoints D i (.inr w))) := by
  let F := D.Completion (.inr w)
  let J := baseChangedAlgebraicGroup F G
  let R := CommAlgCat.of F F
  have hJ : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple J :=
    OppositeRadicals.absolutelyAlmostSimpleFieldExtension G hG
  have hInf : Infinite F := by
    rcases realOrComplexCompletion D hD w with ⟨e, _⟩ | ⟨e, _⟩
    · exact Infinite.of_injective e.symm e.symm.injective
    · exact Infinite.of_injective e.symm e.symm.injective
  letI := hInf
  have hDensity := archimedeanLocalPlusDense D hD i w C hG hI hIso
  obtain ⟨c, hc⟩ := hIso
  obtain ⟨P⟩ := existsLimitDecomposition J c
  obtain ⟨Q⟩ := existsLimitDecomposition J (oppositeCocharacter c)
  let p := (testPointSections J.val).symm.trans (baseChangePointGroupEquiv F G.val R)
  let A : Subgroup (LocalPoints D i (.inr w)) :=
    Subgroup.closure (Specs.Arithmetic.ProjectiveRecurrence.localPointSet D i (.inr w)
      (Specs.Arithmetic.ProjectiveRecurrence.cocharacterRadicalPoints J))
  have hp (s : 𝟙_ (SchemeOver F) ⟶ J.val.X) :
      (show LocalPoints D i (.inr w) from p s) =
        baseChangePoint k F G.val.X R (toUnit ((testSpec F).obj (op R)) ≫ s) := by
    change baseChangePoint k F G.val.X R ((rationalSourceIso F).inv ≫ s) = _
    have h := toUnit_unique ((rationalSourceIso F).inv) (toUnit ((testSpec F).obj (op R)))
    rw [h]
  have hRadical {c' : Cocharacter J.val} (L : LimitDecomposition c') :
      (SubgroupSections L.contracting (𝟙_ (SchemeOver F))).map p.toMonoidHom ≤ A := by
    rintro _ ⟨s, hs, rfl⟩
    have hs' : (testPointSections J.val).symm s ∈
        SubgroupSections L.contracting ((testSpec F).obj (op R)) := by
      rw [← mapSectionsToTestPointSubgroup]
      exact ⟨s, hs, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨(testPointSections J.val).symm s, ⟨c', L, hs'⟩, ?_⟩
    rfl
  have hmap : (unipotentGenerated J).map p.toMonoidHom ≤ A := by
    rw [← RelativeRayGeneration.twoRadicalsGenerate J hJ c hc P Q, Subgroup.map_sup]
    exact sup_le (hRadical P) (hRadical Q)
  refine hDensity.mono ?_
  rintro _ ⟨s, hs, hsg⟩
  exact hsg ▸ (hp s ▸ hmap ⟨s, hs, rfl⟩)


/-- Strong approximation for globally anisotropic nontrialitarian groups
over number fields under the local finite-covolume premise. -/
private theorem anisotropicNumberFieldStrongApproximation
    (localFull : FiniteCovolumeSubgroup.{u})
    {K : Type u} [Field K] [hK : NumberField K]
    (D : GlobalFieldData.{u,u} K) (hD : D = .number hK)
    (G : AffineAlgebraicGroup K) (n : ℕ) (hn : 4 ≤ n)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (hv : HasFixedVectorVertex G n)
    (hAnis : Specs.FunctionFieldAnisotropicCompactness.IsAnisotropic G)
    (i : MatrixRealization G) (S : Finset D.Place) (hNoncompact : OmittedProductNoncompact D i S) :
    StrongApproximation D i S := by
  classical
  obtain ⟨L, _, _, _, _, C, Q, ⟨M⟩⟩ := existsGlobalSpinModel G n hn hG hsc hv
  let I := ULift.{u} (Fin n)
  have hI : 4 ≤ Fintype.card I := by simpa [I] using hn
  letI : Nonempty I := ⟨ULift.up ⟨0, by omega⟩⟩
  have hs := arithmetic_absolute_simplicity hG
  have hOrth := descendedPair_isOrthogonal Q
  have hArch (w : D.InfinitePlace) :=
    NontrialitarianArchimedeanIsotropy.archimedeanIsotropy G hG C Q M hI hOrth D hD i w
  have hQ : FullQuotientCompact D i :=
    hD.symm ▸ numberFieldArithmeticQuotientIsCompact.{u,u} G hG.1 hAnis i
  refine anisotropicNumberFieldApproximationOfLocalData localFull D hD G i hs S hNoncompact hQ
    ?_ ?_ ?_
  · intro w
    obtain ⟨hJ, hMix, he, hContract, _⟩ :=
      finiteCompletionData D i w C Q M hs hI (two_ne_zero : (2 : K) ≠ 0)
    exact ⟨hJ, hMix, he, hContract⟩
  · intro w _ hnc
    exact archimedeanRadicalsDenseOfIsotropic D hD i w C hs hI ((hArch w).1 hnc)
  · intro w _ hc
    rcases realOrComplexCompletion D hD w with ⟨R, hR⟩ | ⟨R, hR⟩
    · exact NontrialitarianCompactRealConnectedness.compactRealConnectedness
        hK G hG hI C Q M hOrth D hD i w R hR hc
    · exact ((hArch w).2 R hR hc).elim

end IsotropicArchimedeanFactors

/-- The nontrialitarian type D sufficiency theorem conditional on the two
local closure statements. -/
theorem strongApproximation_conditional (_localNormal : LocalNormalClosure.{u})
    (localFull : FiniteCovolumeSubgroup.{u}) :
    Specs.Arithmetic.StrongApproximationNontrialitarianD.StrongApproximationNontrialitarian.{u,v} := by
  classical
  intro K _ D G n hn hG hsc hv i S hS hNoncompact
  cases D with
  | number hK =>
    letI : NumberField K := hK
    by_cases hAnis : Specs.FunctionFieldAnisotropicCompactness.IsAnisotropic G
    · let D := GlobalFieldData.number.{u,u} hK
      have hNoncompact' : OmittedProductNoncompact D i S :=
        transferNumberOmittedProductNoncompact.{u,u,v} i S hNoncompact
      exact transferNumberStrongApproximation.{u,u,v} i S
        (anisotropicNumberFieldStrongApproximation localFull D rfl
          G n hn hG hsc hv hAnis i S hNoncompact')
    · exact isotropicNumberFieldStrongApproximation (.number hK) rfl
        G n hn hG hsc hv hAnis i S hS
  | @function k _ _ _ t =>
    exact functionFieldStrongApproximation localFull t G n hn hG hsc hv i S hS hNoncompact

end FiniteSpinModels

/-- The characteristic-two branch for the given global field presentation
and matrix realization. -/
theorem characteristicTwoStrongApproximation
    {K : Type u} [Field K] [CharP K 2] (D : GlobalFieldData.{u,v} K)
    (G : AffineAlgebraicGroup K) (n : ℕ) (hn : 4 ≤ n)
    (hsimple : IsAbsolutelyAlmostSimple G)
    (hsc : GeometricallySimplyConnected G) (hvertex : HasFixedVectorVertex G n)
    (i : MatrixRealization G) (S : Finset D.Place) (hS : S.Nonempty) :
    StrongApproximation D i S := by
  cases D with
  | number hK =>
    let : NumberField K := hK
    exact ((two_ne_zero : (2 : K) ≠ 0) (CharP.cast_eq_zero K 2)).elim
  | @function k _ _ _ t =>
    exact QuaternionSpinCharacteristicTwo.nontrialitarianStrongApproximation
      K k t G n hn hsimple hsc hvertex i S hS

end

end LinearAlgebraicGroups.Arithmetic.StrongApproximationNontrialitarianD

universe v8_closure_32686523d6b97579_u0 v8_closure_32686523d6b97579_u1
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«StrongApproximationNontrialitarianD».«strongApproximation» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«StrongApproximationNontrialitarianD».«StrongApproximationNontrialitarian».{v8_closure_32686523d6b97579_u0, v8_closure_32686523d6b97579_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«StrongApproximationNontrialitarianD».«strongApproximation_conditional».{v8_closure_32686523d6b97579_u0, v8_closure_32686523d6b97579_u1} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalProjectedClosure».«localNormalClosure».{v8_closure_32686523d6b97579_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalProjectedClosure».«localProjectedClosure».{v8_closure_32686523d6b97579_u0})
