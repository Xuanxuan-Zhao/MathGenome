import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.Data.Set.Finite.Lattice

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology

universe u

namespace RepTheorySurvey.Geometric.SheafModels

open Analytic

theorem stalkExact : Expected.StalkExact.{u} := by
  intro X x S h
  exact (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mp h x

theorem supportedEssentialImage : Expected.SupportedEssentialImage.{u} := by
  intro X Z hZ F
  constructor
  · rintro ⟨G, ⟨e⟩⟩ x hx
    exact (closedDirectImage_supported hZ G x hx).of_iso ((stalk x).mapIso e).symm
  · intro h
    have := closedInverseDirectUnit_isIso hZ F h
    exact ⟨_, ⟨(asIso ((inverseDirectAdjunction (closedInclusion Z)).unit.app F)).symm⟩⟩

theorem constructibleBounded : Expected.ConstructibleBounded.{u} := by
  classical
  intro X P F hF
  rcases hF.1.bddBelow with ⟨lo, hlo⟩
  rcases hF.1.bddAbove with ⟨hi, hhi⟩
  refine ⟨⟨lo, (DerivedCategory.isGE_iff F lo).mpr ?_⟩,
    ⟨hi, (DerivedCategory.isLE_iff F hi).mpr ?_⟩⟩
  · intro n hn
    by_contra h
    exact (not_le_of_gt hn) (hlo h)
  · intro n hn
    by_contra h
    exact (not_le_of_gt hn) (hhi h)

private def openRestrictionAdjunction {X : TopCat.{u}} (V : Opens X) :
    V.isOpenEmbedding.sheafPullback Coeff.{u} ⊣ directImage (openInclusion V) :=
  (V.isOpenEmbedding.isOpenMap.adjunction.op.whiskerLeft Coeff.{u}).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) _)
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology (TopCat.of V)) _)
    (Iso.refl _) (Iso.refl _)

private theorem openRestrictionAdjunction_unit_sections {X : TopCat.{u}} (V U : Opens X)
    (F : Sheaves X) :
    (sectionsOn U).map ((openRestrictionAdjunction V).unit.app F) =
      F.obj.map (V.isOpenEmbedding.isOpenMap.adjunction.counit.app U).op := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    (L := V.isOpenEmbedding.sheafPullback Coeff.{u}) (R := directImage (openInclusion V))
    (V.isOpenEmbedding.isOpenMap.adjunction.op.whiskerLeft Coeff.{u})
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) Coeff.{u})
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology (TopCat.of V)) Coeff.{u})
    (Iso.refl _) (Iso.refl _) F
  have h' := congrArg (fun t => t.app (op U)) h
  refine h'.trans ?_
  simp

theorem supportSectionsKernel : Expected.SupportSectionsKernel.{u} := by
  intro X Z hZ U F
  dsimp only
  let V := complementOpen Z hZ
  let j := openInclusion V
  let a := inverseDirectAdjunction j
  let b := openRestrictionAdjunction V
  let c := a.leftAdjointUniq b
  let r := a.unit.app F
  let ev := sectionsOn U
  let d := ev.mapIso ((directImage j).mapIso (c.app F))
  let O := V.isOpenEmbedding.functor.obj ((Opens.map j).obj U)
  have hO : O = U ⊓ V := by
    ext x
    change (∃ y : V, y.val ∈ U ∧ y.val = x) ↔ x ∈ U ∧ x ∈ V
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.property⟩
    · intro hx
      exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  let q := F.obj.mapIso (eqToIso (congrArg op hO))
  have hcomp : ev.map r ≫ (d ≪≫ q).hom =
      F.obj.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op := by
    change ev.map r ≫ (d.hom ≫ q.hom) = _
    rw [← Category.assoc]
    have hu := Adjunction.unit_leftAdjointUniq_hom_app a b F
    change r ≫ (directImage j).map (c.hom.app F) = _ at hu
    change (ev.map r ≫ ev.map ((directImage j).map (c.hom.app F))) ≫ q.hom = _
    rw [← Functor.map_comp, hu]
    erw [openRestrictionAdjunction_unit_sections V U F]
    change F.obj.map _ ≫ F.obj.map _ = _
    rw [← Functor.map_comp]
    congr 1
  let t := F.obj.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op
  let h₀ := limit.isLimit (parallelPair (ev.map r) 0)
  let h₁ := PreservesKernel.iso ev r
  let h₂ := kernel.ofCompIso t (ev.map r) (d ≪≫ q) hcomp
  let e' : kernel (ev.map r) ≅ kernel t := IsLimit.conePointUniqueUpToIso h₀ h₂
  have hk : e'.hom ≫ kernel.ι t = kernel.ι (ev.map r) :=
    IsLimit.conePointUniqueUpToIso_hom_comp h₀ h₂ WalkingParallelPair.zero
  refine ⟨h₁ ≪≫ e', ?_⟩
  change (h₁.hom ≫ e'.hom) ≫ kernel.ι t = ev.map (kernel.ι r)
  rw [Category.assoc, hk]
  change (PreservesKernel.iso ev r).hom ≫ kernel.ι (ev.map r) = _
  rw [PreservesKernel.iso_hom, kernelComparison_comp_ι]

abbrev Sheaves : Expected.SheavesType.{u} := @Analytic.Sheaves.{u}
abbrev Derived : Expected.DerivedType.{u} := @Analytic.Derived.{u}
abbrev BoundedBelow : Expected.BoundedBelowType.{u} := @Analytic.BoundedBelow.{u}
abbrev constant : Expected.ConstantType.{u} := @Analytic.constant.{u}
abbrev rational : Expected.RationalType.{u} := @Analytic.rational.{u}
abbrev stalk : Expected.StalkType.{u} := @Analytic.stalk.{u}
abbrev inverseImage : Expected.InverseImageType.{u} := @Analytic.inverseImage.{u}
abbrev directImage : Expected.DirectImageType.{u} := @Analytic.directImage.{u}
abbrev inverseDirectAdjunction : Expected.InverseDirectAdjunctionType.{u} := @Analytic.inverseDirectAdjunction.{u}
abbrev derivedInverseImage : Expected.DerivedInverseImageType.{u} := @Analytic.derivedInverseImage.{u}
abbrev derivedDirectImage : Expected.DerivedDirectImageType.{u} := @Analytic.derivedDirectImage.{u}
abbrev boundedBelowInverseImage : Expected.BoundedBelowInverseImageType.{u} := @Analytic.boundedBelowInverseImage.{u}
abbrev cohomology : Expected.CohomologyType.{u} := @Analytic.cohomology.{u}
abbrev shiftCohomology : Expected.ShiftCohomologyType.{u} := @Analytic.shiftCohomology.{u}
abbrev sectionsWithSupport : Expected.SectionsWithSupportType.{u} := @Analytic.sectionsWithSupport.{u}
abbrev extraordinaryInverseImage : Expected.ExtraordinaryInverseImageType.{u} := @Analytic.extraordinaryInverseImage.{u}
abbrev extraordinaryAdjunction : Expected.ExtraordinaryAdjunctionType.{u} := @Analytic.extraordinaryAdjunction.{u}
abbrev derivedExtraordinaryInverseImage : Expected.DerivedExtraordinaryInverseImageType.{u} := @Analytic.derivedExtraordinaryInverseImage.{u}
abbrev closedExtension : Expected.ClosedExtensionType.{u} := @Analytic.closedExtension.{u}
abbrev stratumStar : Expected.StratumStarType.{u} := @Analytic.Stratum.star.{u}
abbrev stratumShriek : Expected.StratumShriekType.{u} := @Analytic.Stratum.shriek.{u}
abbrev Constructible : Expected.ConstructibleType.{u} := @Analytic.Constructible.{u}
abbrev MiddlePerverse : Expected.MiddlePerverseType.{u} := @Analytic.MiddlePerverse.{u}
abbrev FiniteStagePerverse : Expected.FiniteStagePerverseType.{u} := @Analytic.FiniteStagePerverse.{u}
abbrev Equivariance : Expected.EquivarianceType.{u} := @Analytic.AnalyticAction.Equivariance.{u}
abbrev EquivariantPerverse : Expected.EquivariantPerverseType.{u} := @Analytic.EquivariantSheaf.Perverse.{u}
abbrev JetEquivariantPerverse : Expected.JetEquivariantPerverseType.{u} := @Analytic.JetAction.Perverse.{u}
abbrev JetEquivariantFiniteSupportPerverse : Expected.JetEquivariantFiniteSupportPerverseType.{u} := @Analytic.StageJetActions.FiniteSupportPerverse.{u}

end RepTheorySurvey.Geometric.SheafModels
