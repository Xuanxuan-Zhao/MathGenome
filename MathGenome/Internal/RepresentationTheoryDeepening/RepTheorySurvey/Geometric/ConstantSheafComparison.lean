import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConstantSheafComparison
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedLocalSheaves
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SmallCochainComparison
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.Pairs
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open P202Specs.CohomologyPairs P202Specs.RelativeSingularChains

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace RepTheorySurvey.Geometric.ConstantSheafComparison

open Analytic Analytic.SingularCochains Analytic.ConstantSheafCohomology

private abbrev ordinary := ordinaryCochainFunctor ℚ Values.{u}
private abbrev singularSequence {X : TopCat.{u}} {V U : Opens X} (i : V ⟶ U) :=
  cochainSequence ℚ Values.{u} (openPair i)

private theorem sectionMap_restrict {X : TopCat.{u}} {V U : Opens X} (i : V ⟶ U) :
    ordinary.map ((Opens.toTopCat X).map i).op ≫ sectionMap V =
      sectionMap U ≫ (sectionSequence (sheafComplex X) i).g :=
  SmallCochainComparison.sectionMap_naturality (X := X) i

private lemma subspaceIso_inclusion {X : TopCat.{u}} {V U : Opens X} (i : V ⟶ U) :
    (subspaceIso i).hom ≫ (openPair i).inclusion = (Opens.toTopCat X).map i := by
  ext x
  rfl

private lemma subspaceIso_naturality {X : TopCat.{u}} {V U V' U' : Opens X}
    (i : V ⟶ U) (i' : V' ⟶ U') (j : U ⟶ U') (k : V ⟶ V') :
    (subspaceIso i).hom ≫ (openPairInclusion i i' j k).restrict =
      (Opens.toTopCat X).map k ≫ (subspaceIso i').hom := by
  ext x
  rfl

private def comparePair {X : TopCat.{u}} {V U : Opens X} (i : V ⟶ U) :
    singularSequence i ⟶ sectionSequence (sheafComplex X) i := by
  let S := singularSequence i
  let T := sectionSequence (sheafComplex X) i
  let b := ordinary.map (subspaceIso i).hom.op ≫ sectionMap V
  have right_square : sectionMap U ≫ T.g = S.g ≫ b := by
    change sectionMap U ≫ T.g =
      ordinary.map (openPair i).inclusion.op ≫ (ordinary.map (subspaceIso i).hom.op ≫ sectionMap V)
    rw [← Category.assoc, ← ordinary.map_comp, ← op_comp, subspaceIso_inclusion]
    exact (sectionMap_restrict i).symm
  have vanishes : (S.f ≫ sectionMap U) ≫ T.g = 0 := by
    rw [Category.assoc, right_square, ShortComplex.zero_assoc, zero_comp]
  exact ShortComplex.Hom.mk
    (kernel.lift T.g (S.f ≫ sectionMap U) vanishes) (sectionMap U) b
    (kernel.lift_ι _ _ _) right_square

private theorem comparePair_naturality {X : TopCat.{u}} {V U V' U' : Opens X}
    (i : V ⟶ U) (i' : V' ⟶ U') (j : U ⟶ U') (k : V ⟶ V') :
    cochainSequenceMap ℚ Values.{u} (openPairInclusion i i' j k) ≫ comparePair i =
      comparePair i' ≫ sectionSequenceRestriction (sheafComplex X) i i' j k := by
  let F := LocalSheaf.openSectionComplexes (sheafComplex X)
  let L := cochainSequenceMap ℚ Values.{u} (openPairInclusion i i' j k) ≫ comparePair i
  let R := comparePair i' ≫ sectionSequenceRestriction (sheafComplex X) i i' j k
  have h₂ : L.τ₂ = R.τ₂ := sectionMap_restrict j
  refine ShortComplex.hom_ext L R ?_ h₂ ?_
  · apply (cancel_mono (sectionSequence (sheafComplex X) i).f).mp
    rw [L.comm₁₂, R.comm₁₂, h₂]
  · change ordinary.map (openPairInclusion i i' j k).restrict.op ≫
          (ordinary.map (subspaceIso i).hom.op ≫ sectionMap V) =
        (ordinary.map (subspaceIso i').hom.op ≫ sectionMap V') ≫ F.map k.op
    rw [← Category.assoc, ← ordinary.map_comp, ← op_comp, subspaceIso_naturality,
      op_comp, ordinary.map_comp, Category.assoc, sectionMap_restrict k]
    exact (Category.assoc _ _ _).symm

private theorem singularSequence_shortExact {X : TopCat.{u}} {V U : Opens X} (i : V ⟶ U) :
    (singularSequence i).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (P202.CohomologyPairs.short_exact ℚ Values.{u} (openPair i))

private theorem sectionSequence_shortExact {X : TopCat.{u}}
    (K : CochainComplex (Sheaves X) ℤ)
    (hK : ∀ n : ℤ, TopCat.Sheaf.IsFlasque (K.X n)) {V U : Opens X} (i : V ⟶ U) :
    (sectionSequence K i).ShortExact := by
  refine { exact := ShortComplex.kernelSequence_exact _
           mono_f := inferInstance
           epi_g := ?_ }
  apply HomologicalComplex.epi_of_epi_f
  intro n
  change Epi ((K.X n).obj.map i.op)
  have := hK n
  infer_instance

private theorem quasiIso_first_of_shortExact {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {S T : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (h₂ : QuasiIso φ.τ₂) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₁ := by
  let ψ := DerivedCategory.triangleOfSES.map hS hT φ
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso C φ.τ₁).mp
    (isIso₁_of_isIso₂₃ ψ (DerivedCategory.triangleOfSES_distinguished hS)
      (DerivedCategory.triangleOfSES_distinguished hT)
      ((DerivedCategory.isIso_Q_map_iff_quasiIso C φ.τ₂).mpr h₂)
      ((DerivedCategory.isIso_Q_map_iff_quasiIso C φ.τ₃).mpr h₃))

private theorem sheafComplex_flasque (X : TopCat.{u}) [SecondCountableTopology X]
    [LocallyCompactSpace X] [T2Space X] (n : ℤ) :
    TopCat.Sheaf.IsFlasque ((sheafComplex X).X n) := by
  by_cases h : n < 0
  · have hzero := (CochainComplex.isStrictlyGE_iff _ _).mp
        (SingularCochainSheaves.nonnegativeSupport X) n h
    exact ⟨fun {U V} i => ((sectionsOn V.unop).map_isZero hzero).epi _⟩
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt h)
    exact SingularCochainSheaves.flabby X m

/-- Natural comparison of ordinary and supported constant-sheaf cohomology
with ordinary and relative singular cohomology via the same cochain map. -/
theorem comparison : ConstantSheafCohomology.Expected.Comparison.{u} := by
  intro X _ _ _ hX
  let hn := SingularCochainSheaves.nonnegativeSupport X
  let K : CochainComplex.Plus (Sheaves X) := ⟨sheafComplex X, 0, hn⟩
  have hK (n : ℤ) : TopCat.Sheaf.IsFlasque (K.obj.X n) := sheafComplex_flasque X n
  let a : rationalComplex X ⟶ K := ObjectProperty.homMk (augmentation X)
  have ha : IsIso (DerivedCategory.Plus.Q.map a) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso _) a
      (SingularCochainSheaves.resolution X hX)
  have hSing {V U : Opens X} (i : V ⟶ U) := singularSequence_shortExact i
  have hSh {V U : Opens X} (i : V ⟶ U) := sectionSequence_shortExact K.obj hK i
  refine ⟨hn, ha, ?_, ?_, ?_, hSing, hSh, @comparePair X, ?_, ?_⟩
  · intro U
    have h := DerivedLocalSheaves.supportedSectionsFlasqueResolution
      (Z := (∅ : Set X)) isClosed_empty U K hK
    exact ⟨SmallCochainComparison.sectionMap_quasiIso X U, h.2.2.2.1⟩
  · intro V U i
    exact SmallCochainComparison.sectionMap_naturality (X := X) i
  · intro Z hZ U
    obtain ⟨e, _, hUnit, _, _⟩ :=
      DerivedLocalSheaves.supportedSectionsFlasqueResolution hZ U K hK
    exact ⟨hUnit, e⟩
  · intro V U i
    have h₂ : QuasiIso (comparePair i).τ₂ := SmallCochainComparison.sectionMap_quasiIso X U
    have h₃ : QuasiIso (comparePair i).τ₃ := by
      change QuasiIso (ordinary.map (subspaceIso i).hom.op ≫ sectionMap V)
      have : QuasiIso (sectionMap V) := SmallCochainComparison.sectionMap_quasiIso X V
      infer_instance
    refine ⟨rfl, rfl, quasiIso_first_of_shortExact (hSing i) (hSh i) _ h₂ h₃, h₂, h₃, ?_⟩
    intro q
    exact HomologicalComplex.HomologySequence.δ_naturality
      (comparePair i) (hSing i) (hSh i) q (q + 1) rfl
  · exact comparePair_naturality

open private plusHomologyFactors from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedLocalSheaves

private def derivedSectionsIso {X : TopCat.{u}} (T : Sheaves X ⥤ Coeff.{u}) [T.Additive]
    (K : CochainComplex.Plus (Sheaves X)) {B : BoundedBelow X}
    (e : DerivedCategory.Plus.Q.obj K ≅ B)
    [IsIso (T.rightDerivedFunctorPlusUnit.app K)] :
    DerivedCategory.Plus.Q.obj (T.mapCochainComplexPlus.obj K) ≅
      T.rightDerivedFunctorPlus.obj B :=
  asIso (T.rightDerivedFunctorPlusUnit.app K) ≪≫ T.rightDerivedFunctorPlus.mapIso e

private def sectionsCohomologyIso {X : TopCat.{u}} (T : Sheaves X ⥤ Coeff.{u}) [T.Additive]
    (K : CochainComplex.Plus (Sheaves X)) {B : BoundedBelow X}
    (e : DerivedCategory.Plus.Q.obj K ≅ B)
    [IsIso (T.rightDerivedFunctorPlusUnit.app K)] (q : ℤ) :
    (T.mapCochainComplexPlus.obj K).obj.homology q ≅
      (DerivedCategory.Plus.homologyFunctor _ q).obj (T.rightDerivedFunctorPlus.obj B) :=
  ((plusHomologyFactors Coeff.{u} q).app (T.mapCochainComplexPlus.obj K)).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso (derivedSectionsIso T K e)

private theorem sectionsCohomologyIso_naturality {X : TopCat.{u}}
    {S T : Sheaves X ⥤ Coeff.{u}} [S.Additive] [T.Additive] (r : S ⟶ T)
    (K : CochainComplex.Plus (Sheaves X)) {B : BoundedBelow X}
    (e : DerivedCategory.Plus.Q.obj K ≅ B)
    [IsIso (S.rightDerivedFunctorPlusUnit.app K)] [IsIso (T.rightDerivedFunctorPlusUnit.app K)]
    (q : ℤ) :
    HomologicalComplex.homologyMap (r.mapCochainComplexPlus.app K).hom q ≫
        (sectionsCohomologyIso T K e q).hom =
      (sectionsCohomologyIso S K e q).hom ≫
        (DerivedCategory.Plus.homologyFunctor _ q).map (r.rightDerivedFunctorPlus.app B) := by
  let H := DerivedCategory.Plus.homologyFunctor Coeff.{u} q
  let rK := r.mapCochainComplexPlus.app K
  let η := (plusHomologyFactors Coeff.{u} q).inv
  have hr : DerivedCategory.Plus.Q.map rK ≫ (derivedSectionsIso T K e).hom =
      (derivedSectionsIso S K e).hom ≫ r.rightDerivedFunctorPlus.app B := by
    dsimp only [derivedSectionsIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, rK]
    rw [Category.assoc, ← NatTrans.rightDerivedFunctorPlus_fac_app_assoc,
      r.rightDerivedFunctorPlus.naturality]
  have hη := η.naturality rK
  change HomologicalComplex.homologyMap rK.hom q ≫ η.app (T.mapCochainComplexPlus.obj K) =
      η.app (S.mapCochainComplexPlus.obj K) ≫ H.map (DerivedCategory.Plus.Q.map rK) at hη
  change HomologicalComplex.homologyMap rK.hom q ≫
      (η.app (T.mapCochainComplexPlus.obj K) ≫ H.map (derivedSectionsIso T K e).hom) =
      (η.app (S.mapCochainComplexPlus.obj K) ≫ H.map (derivedSectionsIso S K e).hom) ≫ _
  rw [← Category.assoc, hη, Category.assoc, ← H.map_comp, hr, H.map_comp, Category.assoc]

/-- The absolute comparison as an isomorphism of cohomology presheaves. -/
theorem absoluteCohomology (X : TopCat.{u}) [SecondCountableTopology X]
    [LocallyCompactSpace X] [T2Space X] (hX : HasContractibleOpenBasis X) (q : ℤ) :
    Nonempty (((Opens.toTopCat X).op ⋙ ordinaryCohomologyFunctor ℚ Values.{u} q) ≅
      LocalSheaf.derivedOpenCohomology (𝟭 (Sheaves X))
        (LocalSheaf.sheafInDegreeZero (rational X)) q) := by
  obtain ⟨hn, ha, hU, _⟩ := comparison X hX
  let K : CochainComplex.Plus (Sheaves X) := ⟨sheafComplex X, 0, hn⟩
  let a : rationalComplex X ⟶ K := ObjectProperty.homMk (augmentation X)
  let e : DerivedCategory.Plus.Q.obj K ≅ LocalSheaf.sheafInDegreeZero (rational X) :=
    (asIso (DerivedCategory.Plus.Q.map a)).symm
  have hUnit (U : Opens X) : IsIso ((sectionsOn U).rightDerivedFunctorPlusUnit.app K) :=
    (hU U).2
  let η : ((Opens.toTopCat X).op ⋙ ordinary) ⟶ LocalSheaf.openSectionComplexes K.obj :=
    { app U := sectionMap U.unop
      naturality _ _ i := sectionMap_restrict i.unop }
  let ηq := Functor.whiskerRight η (HomologicalComplex.homologyFunctor Coeff.{u} (.up ℤ) q)
  have (U : (Opens X)ᵒᵖ) : IsIso (ηq.app U) := by
    change IsIso (HomologicalComplex.homologyMap (sectionMap U.unop) q)
    have := (hU U.unop).1
    infer_instance
  let eSing := NatIso.ofComponents (fun U => asIso (ηq.app U)) (fun i => ηq.naturality i)
  refine ⟨eSing ≪≫ NatIso.ofComponents
    (fun U => sectionsCohomologyIso (sectionsOn U.unop) K e q) ?_⟩
  intro U V r
  exact sectionsCohomologyIso_naturality (LocalSheaf.sectionsRestriction r.unop) K e q

/-- The relative comparison as an isomorphism with the right derived
sections supported in the intersection of the closed set with the open. -/
theorem supportedCohomology (X : TopCat.{u}) [SecondCountableTopology X]
    [LocallyCompactSpace X] [T2Space X] (hX : HasContractibleOpenBasis X)
    {Z : Set X} (hZ : IsClosed Z) (U : Opens X) (q : ℤ) :
    Nonempty (relativeCohomology ℚ Values.{u}
        (openPair (homOfLE inf_le_left : U ⊓ complementOpen Z hZ ⟶ U)) q ≅
      (DerivedCategory.Plus.homologyFunctor _ q).obj
        ((LocalSheaf.supportedSectionsOn hZ U).rightDerivedFunctorPlus.obj
          (LocalSheaf.sheafInDegreeZero (rational X)))) := by
  obtain ⟨hn, ha, _, _, hSupport, _, _, φ, hφ, _⟩ := comparison X hX
  let K : CochainComplex.Plus (Sheaves X) := ⟨sheafComplex X, 0, hn⟩
  let a : rationalComplex X ⟶ K := ObjectProperty.homMk (augmentation X)
  let e : DerivedCategory.Plus.Q.obj K ≅ LocalSheaf.sheafInDegreeZero (rational X) :=
    (asIso (DerivedCategory.Plus.Q.map a)).symm
  let i : U ⊓ complementOpen Z hZ ⟶ U := homOfLE inf_le_left
  obtain ⟨hUnit, k, _⟩ := hSupport hZ U
  have : QuasiIso (φ i).τ₁ := (hφ i).2.2.1
  let H := HomologicalComplex.homologyFunctor Coeff.{u} (.up ℤ) q
  exact ⟨asIso (HomologicalComplex.homologyMap (φ i).τ₁ q) ≪≫ H.mapIso k.symm ≪≫
    sectionsCohomologyIso (LocalSheaf.supportedSectionsOn hZ U) K e q⟩

private theorem constantOpenPullback {X : TopCat.{u}} (U : Opens X) :
    Nonempty ((boundedBelowInverseImage (openInclusion U)).obj
        (LocalSheaf.sheafInDegreeZero (rational X)) ≅
      LocalSheaf.sheafInDegreeZero (rational (TopCat.of U))) := by
  obtain ⟨e⟩ := DerivedLocalSheaves.constantOpenRestriction U
  let f := openInclusion U
  refine ⟨(DerivedCategory.Plus.ι (C := Sheaves (TopCat.of U))).preimageIso ?_⟩
  change (derivedInverseImage f).obj ((DerivedCategory.singleFunctor (Sheaves X) 0).obj
      (rational X)) ≅ (DerivedCategory.singleFunctor (Sheaves (TopCat.of U)) 0).obj
      (rational (TopCat.of U))
  exact ((inverseImage f).mapDerivedCategorySingleFunctor 0).app (rational X) ≪≫
    (DerivedCategory.singleFunctor (Sheaves (TopCat.of U)) 0).mapIso e

/-- The absolute comparison for the constant sheaf on the open subspace. -/
theorem absoluteCohomologyOnOpen (X : TopCat.{u}) [SecondCountableTopology X]
    [LocallyCompactSpace X] [T2Space X] (hX : HasContractibleOpenBasis X)
    (U : Opens X) (q : ℤ) :
    Nonempty (ordinaryCohomology ℚ Values.{u} (TopCat.of U) q ≅
      (DerivedCategory.Plus.homologyFunctor _ q).obj
        ((LocalSheaf.globalSections (TopCat.of U)).rightDerivedFunctorPlus.obj
          (LocalSheaf.sheafInDegreeZero (rational (TopCat.of U))))) := by
  obtain ⟨c⟩ := absoluteCohomology X hX q
  obtain ⟨loc⟩ := DerivedLocalSheaves.openSectionsLocality U
  obtain ⟨e⟩ := constantOpenPullback U
  let H := DerivedCategory.Plus.homologyFunctor Coeff.{u} q
  let G := (LocalSheaf.globalSections (TopCat.of U)).rightDerivedFunctorPlus
  exact ⟨c.app (op U) ≪≫
    H.mapIso (loc.app (LocalSheaf.sheafInDegreeZero (rational X)) ≪≫ G.mapIso e)⟩

/-- The relative comparison for an arbitrary closed subset of the open subspace. -/
theorem supportedCohomologyOnOpen (X : TopCat.{u}) [SecondCountableTopology X]
    [LocallyCompactSpace X] [T2Space X] (hX : HasContractibleOpenBasis X)
    (U : Opens X) {Z : Set U} (hZ : IsClosed Z) (q : ℤ) :
    Nonempty (relativeCohomology ℚ Values.{u} (⟨TopCat.of U, Zᶜ⟩ : Pair.{u}) q ≅
      (DerivedCategory.Plus.homologyFunctor _ q).obj
        ((LocalSheaf.supportedSectionsOn (X := TopCat.of U) hZ ⊤).rightDerivedFunctorPlus.obj
          (LocalSheaf.sheafInDegreeZero (rational (TopCat.of U))))) := by
  obtain ⟨W, hW, hZW⟩ := Topology.IsInducing.subtypeVal.isClosed_iff.mp hZ
  change LocalSheaf.closedSetOnOpen U W = Z at hZW
  subst Z
  let i : U ⊓ complementOpen W hW ⟶ U := homOfLE inf_le_left
  have hp : openPair i = ⟨TopCat.of U, (LocalSheaf.closedSetOnOpen U W)ᶜ⟩ := by
    unfold openPair
    congr 1
    ext x
    change (x.val ∈ U ∧ x.val ∉ W) ↔ x.val ∉ W
    exact and_iff_right x.property
  obtain ⟨c⟩ := supportedCohomology X hX hW U q
  change relativeCohomology ℚ Values.{u} (openPair i) q ≅ _ at c
  rw [hp] at c
  obtain ⟨loc⟩ := DerivedLocalSheaves.supportedSectionsLocality hW U
  obtain ⟨e⟩ := constantOpenPullback U
  let H := DerivedCategory.Plus.homologyFunctor Coeff.{u} q
  let G := (LocalSheaf.supportedSectionsOn (X := TopCat.of U)
    (LocalSheaf.closedSetOnOpen_isClosed hW U) ⊤).rightDerivedFunctorPlus
  exact ⟨c ≪≫ H.mapIso (loc.app (LocalSheaf.sheafInDegreeZero (rational X)) ≪≫ G.mapIso e)⟩

end RepTheorySurvey.Geometric.ConstantSheafComparison
