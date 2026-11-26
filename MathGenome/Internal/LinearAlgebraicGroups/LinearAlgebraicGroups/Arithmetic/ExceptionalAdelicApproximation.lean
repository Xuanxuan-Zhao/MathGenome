import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAdelicApproximation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalCompactnessCriterion
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.WeakApproximationByTori
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SplitLocalGeneration
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Set Filter Topology
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped Classical RestrictedProduct CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAdelicApproximation

open Specs.ExceptionalAdelicApproximation
open Specs.IntegralModels (MatrixRealization)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.GeometricRadicals (IsSemisimple)
open Specs.AnisotropicAdNilpotents (IsAnisotropic)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open Specs.Arithmetic.ProjectiveRecurrence (localPointSet parabolicRadicalPoints
  cocharacterRadicalPoints)
open AdelicGroups ArithmeticLatticeProjection CompactProductIsolation
open Specs.Arithmetic.OppositeRadicals (localPlus)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.BorelProper (IsParabolic)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.Specs hiding IsAbsolutelyAlmostSimple

open private simplyConnectedAfterBaseChange borelPairOfQuasiSplit rationalBorelParabolic
  parabolicGenerationOfBorelGeneration localPointSet_generates_of_parabolicRadicals
  localPropertiesOfQuasiSplit compactFullQuotient mapContracted numberFiniteRadicalContracted
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalCompactnessCriterion
open private localPointSet_eq_image from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence
open private completionPointEquiv completionPointEquiv_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
open private testPointSections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

variable {K : Type u} [Field K] [NumberField K]

local instance numberCompletionField (w : NumberPlace K) :
    Field ((numberPlaces K).Completion w) :=
  GlobalFieldData.instFieldCompletion (numberPlaces K) w

local instance numberCompletionTopology (w : NumberPlace K) :
    TopologicalSpace ((numberPlaces K).Completion w) :=
  GlobalFieldData.instTopologicalSpaceCompletion (numberPlaces K) w

local instance numberCompletionAlgebra (w : NumberPlace K) :
    Algebra K ((numberPlaces K).Completion w) :=
  completionAlgebra (numberPlaces K) w

private theorem radicalSections_le_generated {F : Type u} [Field F]
    {G : AffineAlgebraicGroup F} (P : ClosedSubgroup G.val) (hP : IsParabolic G P)
    (U : ClosedSubgroup P.group)
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U) :
    SubgroupSections (subgroupOfSubgroup P U) (𝟙_ (SchemeOver F)) ≤ unipotentGenerated G := by
  let A (Q : ClosedSubgroup G.val) (_ : IsParabolic G Q) (V : ClosedSubgroup Q.group)
      (_ : IsUnipotentRadical (closedSubgroupAlgebraicGroup Q) V) :=
    SubgroupSections (subgroupOfSubgroup Q V) (𝟙_ (SchemeOver F))
  have h₁ := le_iSup (A P hP U) hU
  have h₂ := le_iSup (fun V => ⨆ hV, A P hP V hV) U
  have h₃ := le_iSup (fun h => ⨆ V, ⨆ hV, A P h V hV) hP
  have h₄ := le_iSup (fun Q => ⨆ h, ⨆ V, ⨆ hV, A Q h V hV) P
  exact h₁.trans (h₂.trans (h₃.trans h₄))

private theorem localPlus_eq_radicalClosure {K : Type u} [Field K]
    (D : GlobalFieldData.{u, u} K) (G : AffineAlgebraicGroup K)
    (i : MatrixRealization G) (w : D.Place) :
    localPlus D i w = (Subgroup.closure (localPointSet D i w
      (parabolicRadicalPoints (baseChangedAlgebraicGroup (D.Completion w) G))) :
        Set (LocalPoints D i w)) := by
  let F := D.Completion w
  let G₀ := baseChangedAlgebraicGroup F G
  let φ := completionPointEquiv D i w
  let R := CommAlgCat.of F F
  let A := localPointSet D i w (parabolicRadicalPoints G₀)
  have hpoint (p : GroupPoints G₀.val R) :
      φ (testPointSections G₀.val p) = baseChangePoint K F G.val.X R p := by
    change baseChangePoint K F G.val.X R
      ((testPointSections G₀.val).symm (testPointSections G₀.val p)) = _
    rw [MulEquiv.symm_apply_apply]
  have hsection {P : ClosedSubgroup G₀.val} (U : ClosedSubgroup P.group)
      (p : GroupPoints U.group R) :
      testPointSections G₀.val
        ((((groupPointsFunctor F).map (U.inclusion ≫ P.inclusion)).app R).hom p) =
      testPointSections U.group p ≫ (subgroupOfSubgroup P U).inclusion.hom.hom := by
    change _ ≫ (p ≫ _) = (_ ≫ p) ≫ _
    rw [Category.assoc]
    rfl
  have hEq : localPlus D i w = ↑((unipotentGenerated G₀).map φ.toMonoidHom) := by
    ext g
    change (∃ p ∈ unipotentGenerated G₀,
      baseChangePoint K F G.val.X R (toUnit _ ≫ p) = g) ↔
      ∃ p ∈ unipotentGenerated G₀, φ p = g
    constructor
    · rintro ⟨p, hp, he⟩
      exact ⟨p, hp, (completionPointEquiv_apply D i w p).trans he⟩
    · rintro ⟨p, hp, he⟩
      exact ⟨p, hp, (completionPointEquiv_apply D i w p).symm.trans he⟩
  rw [hEq]
  apply congrArg SetLike.coe
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    unfold unipotentGenerated
    apply iSup_le
    intro P
    apply iSup_le
    intro hP
    apply iSup_le
    intro U
    apply iSup_le
    intro hU q hq
    obtain ⟨y, rfl⟩ := hq
    obtain ⟨p, rfl⟩ := (testPointSections U.group).surjective y
    let z := (((groupPointsFunctor F).map (U.inclusion ≫ P.inclusion)).app R).hom p
    have hz : z ∈ parabolicRadicalPoints G₀ := ⟨P, hP, U, hU, p, rfl⟩
    have he := (congrArg φ (hsection U p)).symm.trans (hpoint z)
    change φ (testPointSections U.group p ≫ _) ∈ Subgroup.closure A
    exact Subgroup.subset_closure ⟨z, hz, congrArg (fun s : Points G.val.X _ => s.left) he⟩
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨z, ⟨P, hP, U, hU, p, hp⟩, hg⟩
    refine ⟨testPointSections G₀.val z, ?_, ?_⟩
    · let q := testPointSections U.group p
      let B := SubgroupSections (subgroupOfSubgroup P U) (𝟙_ (SchemeOver F))
      have hmem : q ≫ (subgroupOfSubgroup P U).inclusion.hom.hom ∈ B := ⟨q, rfl⟩
      have hm := radicalSections_le_generated (G := G₀) P hP U hU hmem
      have he := (congrArg (testPointSections G₀.val) hp).symm.trans (hsection U p)
      exact he.symm ▸ hm
    · exact (hpoint z).trans (Over.OverMorphism.ext hg.symm)

theorem localPlusComparison : LocalPlusComparison.{u} := by
  intro K _ _ G i w D
  exact localPlus_eq_radicalClosure D G i w

private theorem finiteRadicalsGenerate (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (hlocal : CompletionHypotheses G i) (w : (numberPlaces K).FinitePlace) :
    Subgroup.closure (localPointSet (numberPlaces K) i (.inl w)
      (parabolicRadicalPoints
        (baseChangedAlgebraicGroup ((numberPlaces K).Completion (.inl w)) G))) = ⊤ := by
  let D := numberPlaces K
  let F := w.adicCompletion K
  letI : Algebra K F := completionAlgebra D (.inl w)
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let G₀ := baseChangedAlgebraicGroup F G
  have hs := (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := F) G
    hG.1.1 hG.1.2.1).mpr hG.1
  have hsc₀ := simplyConnectedAfterBaseChange (F := F) G hG.1 hsc
  have hqs := hlocal.finiteQuasiSplit w
  obtain ⟨M⟩ := borelPairOfQuasiSplit G₀ hqs
  have hF : Specs.QuasiSplitLocalGeneration.IsLocalField F :=
    Or.inl ⟨inferInstanceAs (ValuativeRel (D.FiniteCompletion w)), inferInstance,
      GlobalFieldData.finiteCompletion_isLocalField D w⟩
  exact localPointSet_generates_of_parabolicRadicals D i (.inl w)
    (parabolicGenerationOfBorelGeneration G₀ M
      (rationalBorelParabolic G₀ hqs.1 M.positive M.positiveBorel)
      (rationalBorelParabolic G₀ hqs.1 M.negative M.negativeBorel)
      (QuasiSplitLocalGeneration.quasiSplitLocalGeneration hF G₀ hs hsc₀ M))

open CocharacterDynamics (LimitDecomposition lieImage)
open Specs.RootGroups (rootPoint)
open private rootPoint_surjective rootPoint_hasLimit
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private cocharacter_parabolic from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility

private theorem cocharacterRadicals_are_parabolic {F : Type u} [Field F]
    {G : AffineAlgebraicGroup F} (hG : IsSemisimple G) :
    cocharacterRadicalPoints G ⊆ parabolicRadicalPoints G := by
  rintro _ ⟨c, L, p, rfl⟩
  let hred := reductive_of_semisimple G hG
  refine ⟨L.parabolic, cocharacter_parabolic hred c L, Specs.BorelsAndChambers.contractingSubgroup L,
    (Relative.SplitContractingRadical.contractingSubgroupIsRadical G hred c L).1, p, ?_⟩
  change ((groupPointsFunctor F).map
    (L.contractingToParabolic ≫ L.parabolic.inclusion)).app _ p = _
  rw [L.contracting_in_G]

private theorem splitContractingGeneration {F : Type u} [Field F]
    (G : AffineAlgebraicGroup F) (hG : IsSemisimple G)
    (hsc : GeometricallySimplyConnected G) (hsplit : GeometricRadicals.IsSplitReductive G) :
    Subgroup.closure (cocharacterRadicalPoints G) = ⊤ := by
  obtain ⟨hred, T, hT, hmax⟩ := hsplit
  apply top_le_iff.mp
  rw [← SplitLocalGeneration.splitLocalGeneration G hG hsc T hT hmax]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨α, hα, U, hU, p, rfl⟩
  obtain ⟨_, c, _, hc, _⟩ :=
    RootData.RootGroups.rankOneRootGroups G hred T hT hmax α hα
  obtain ⟨V, _, _, _, ⟨A, e, hx⟩, hsame⟩ :=
    ((RootData.RootGroups.rootSubgroups G hred T hT hmax).2 α hα).2.2
  obtain ⟨f, hf⟩ := (hsame U hU).2
  let R := CommAlgCat.of F F
  let q : GroupPoints V.group R := p ≫ f.hom.hom
  obtain ⟨a, ha⟩ := rootPoint_surjective e R q
  obtain ⟨L⟩ := CocharacterDynamics.existsLimitDecomposition G (c ≫ T.inclusion)
  have hlim := rootPoint_hasLimit hx c hc R a
  have heq : rootPoint (e.hom ≫ V.inclusion) R a = p ≫ U.inclusion.hom.hom := by
    change rootPoint e.hom R a ≫ V.inclusion.hom.hom = _
    rw [ha]
    change (p ≫ f.hom.hom) ≫ V.inclusion.hom.hom = _
    rw [Category.assoc]
    exact congrArg (p ≫ ·) ((Grp.forget (SchemeOver F)).congr_map hf)
  rw [heq] at hlim
  obtain ⟨z, hz⟩ := (L.contracting_points R _).mp hlim
  exact Subgroup.subset_closure ⟨_, L, z, hz⟩

private theorem finiteRadicalContracted (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (w : (numberPlaces K).FinitePlace) {x : LocalPoints (numberPlaces K) i (.inl w)}
    (hx : x ∈ localPointSet (numberPlaces K) i (.inl w)
      (parabolicRadicalPoints
        (baseChangedAlgebraicGroup ((numberPlaces K).Completion (.inl w)) G))) :
    Contracted x := by
  let D := numberPlaces K
  let F := w.adicCompletion K
  letI : Algebra K F := completionAlgebra D (.inl w)
  let G₀ := baseChangedAlgebraicGroup F G
  obtain ⟨_, j₀, _, e₀, he, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison K F G i
  let j : MatrixRealization G₀ := j₀
  let e : PointsIn j F ≃ₜ* LocalPoints D i (.inl w) := e₀
  rw [localPointSet_eq_image D i (.inl w) j e he] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact mapContracted e.toMonoidHom e.continuous (numberFiniteRadicalContracted w G₀ j hy)

private theorem archimedeanRadicalContracted (G : AffineAlgebraicGroup K)
    (i : MatrixRealization G) (w : NumberField.InfinitePlace K)
    {x : LocalPoints (numberPlaces K) i (.inr w)}
    (hx : x ∈ localPointSet (numberPlaces K) i (.inr w)
      (cocharacterRadicalPoints
        (baseChangedAlgebraicGroup ((numberPlaces K).Completion (.inr w)) G))) :
    Contracted x := by
  let D := numberPlaces K
  let F := w.Completion
  letI : Algebra K F := completionAlgebra D (.inr w)
  let G₀ := baseChangedAlgebraicGroup F G
  obtain ⟨_, j₀, _, e₀, he, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison K F G i
  let j : MatrixRealization G₀ := j₀
  let e : PointsIn j F ≃ₜ* LocalPoints D i (.inr w) := e₀
  rw [localPointSet_eq_image D i (.inr w) j e he] at hx
  obtain ⟨y, ⟨c, L, hy⟩, rfl⟩ := hx
  obtain ⟨scalars, hdim, _, _⟩ := ArchimedeanLieChart.completionRealStructures K w
  letI : NormedField F := inferInstanceAs (NormedField w.Completion)
  letI : NormedAlgebra ℝ F := scalars
  letI : FiniteDimensional ℝ F := hdim
  have h : Continuous (algebraMap ℝ F) :=
    (Algebra.linearMap ℝ F).continuous_of_finiteDimensional
  obtain ⟨t, ht⟩ := LocalCocharacterEvaluation.contractingScalarExists (E := ℝ)
  exact mapContracted e.toMonoidHom e.continuous
    ⟨_, LocalCocharacterEvaluation.contractingEvaluation G₀ j c L h t ht y hy⟩

private theorem complexRadicalsGenerate (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G)
    (hlocal : CompletionHypotheses G i) (w : NumberField.InfinitePlace K) (hw : w.IsComplex) :
    Subgroup.closure (localPointSet (numberPlaces K) i (.inr w)
      (cocharacterRadicalPoints
        (baseChangedAlgebraicGroup ((numberPlaces K).Completion (.inr w)) G))) = ⊤ := by
  let D := numberPlaces K
  let F := w.Completion
  letI : Algebra K F := completionAlgebra D (.inr w)
  let G₀ := baseChangedAlgebraicGroup F G
  have hs := (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := F) G
    hG.1 hG.2.1).mpr hG
  have hsc₀ := simplyConnectedAfterBaseChange (F := F) G hG hsc
  have hgen := splitContractingGeneration G₀ hs hsc₀ (hlocal.complexSplit w hw)
  obtain ⟨_, j₀, _, e₀, he, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison K F G i
  let j : MatrixRealization G₀ := j₀
  let e : PointsIn j F ≃ₜ* LocalPoints D i (.inr w) := e₀
  have hset := localPointSet_eq_image D i (.inr w) j e he (cocharacterRadicalPoints G₀)
  change Subgroup.closure (localPointSet D i (.inr w) (cocharacterRadicalPoints G₀)) = _
  rw [hset]
  change Subgroup.closure (e.toMonoidHom '' (cocharacterRadicalPoints G₀ :
    Set (PointsIn j F))) = _
  rw [← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective _ e.surjective]

theorem localGeneration : LocalGeneration.{u} := by
  intro K _ _ G i hG hsc hlocal D
  constructor
  · intro w
    have hg := finiteRadicalsGenerate G i hG hsc hlocal w
    have hm : Subgroup.closure (localPointSet D i (.inl w)
        (parabolicRadicalPoints (baseChangedAlgebraicGroup (D.Completion (.inl w)) G))) ≤
        Subgroup.closure {x : LocalPoints D i (.inl w) | Contracted x} :=
      Subgroup.closure_mono fun _ hx => finiteRadicalContracted G i w hx
    refine ⟨?_, dense_univ.mono ?_⟩
    · rw [localPlusComparison G i (.inl w), hg, Subgroup.coe_top]
    · rw [hg] at hm
      exact fun _ _ => hm (Subgroup.mem_top _)
  · intro w hw
    let G₀ := baseChangedAlgebraicGroup (D.Completion (.inr w)) G
    have hg : Dense (↑(Subgroup.closure (localPointSet D i (.inr w)
        (cocharacterRadicalPoints G₀))) : Set (LocalPoints D i (.inr w))) := by
      rcases (w.isReal_or_isComplex).symm with hC | hR
      · rw [complexRadicalsGenerate G i hG.1 hsc hlocal w hC, Subgroup.coe_top]
        exact dense_univ
      · exact hlocal.realRadicalDensity w hR
          (hw.resolve_left (NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr hR))
    refine ⟨?_, hg, hg.mono (Subgroup.closure_mono fun _ hx =>
      archimedeanRadicalContracted G i w hx)⟩
    rw [localPlusComparison G i (.inr w)]
    apply hg.mono (Subgroup.closure_mono ?_)
    have hs := (Reductive.RadicalBaseChange.semisimpleFieldExtension
      (K := D.Completion (.inr w)) G hG.1.1 hG.1.2.1).mpr hG.1
    rintro _ ⟨y, hy, hxy⟩
    exact ⟨y, cocharacterRadicals_are_parabolic hs hy, hxy⟩

private theorem contractedGenerateProduct {I : Type*} [Fintype I]
    {A : I → Type*} [∀ j, Group (A j)] [∀ j, TopologicalSpace (A j)]
    (hd : ∀ j, Dense (Subgroup.closure {x : A j | Contracted x} : Set (A j))) :
    Dense (Subgroup.closure {x : ∀ j, A j | Contracted x} : Set (∀ j, A j)) := by
  classical
  let H := Subgroup.closure {x : ∀ j, A j | Contracted x}
  refine (dense_pi univ (fun j _ => hd j)).mono ?_
  intro x hx
  change x ∈ H
  rw [← Finset.noncommProd_mulSingle x]
  apply H.noncommProd_mem
  intro j _
  let f := MonoidHom.mulSingle A j
  have hle : Subgroup.closure {y : A j | Contracted y} ≤ H.comap f := by
    apply (Subgroup.closure_le _).mpr
    intro y hy
    exact Subgroup.subset_closure (mapContracted f (continuous_mulSingle j) hy)
  exact hle (hx j (Set.mem_univ j))

theorem archimedeanIsolation : ArchimedeanIsolation.{u} := by
  classical
  intro K _ _ G i hG hsc hlocal han D S J hS hSnoncompact hJ
  have hJS : Disjoint J S := Finset.disjoint_left.mpr fun w hw hws =>
    ((hJ w).mp hw).choose_spec.2.1 hws
  by_cases hne : J.Nonempty
  · let T := S ∪ J
    let U := integralOutside D i T
    have hArch (w : D.InfinitePlace) (hw : Sum.inr w ∉ T) :
        CompactSpace (LocalPoints D i (.inr w)) := by
      by_contra hc
      exact hw (Finset.mem_union_right S ((hJ (.inr w)).mpr
        ⟨w, rfl, fun h => hw (Finset.mem_union_left J h), hc⟩))
    obtain ⟨hUc, hUo⟩ := compactOpenOutside D i T hArch
    let A := Finset.univ.filter (fun w : D.InfinitePlace => Sum.inr w ∈ J)
    let index (a : ↥A) : ↥J := ⟨Sum.inr a.val, (Finset.mem_filter.mp a.property).2⟩
    have hindex : Function.Bijective index := by
      constructor
      · intro a b hab
        exact Subtype.ext (Sum.inr_injective (congrArg Subtype.val hab))
      · rintro ⟨v, hv⟩
        obtain ⟨w, rfl, _, _⟩ := (hJ v).mp hv
        exact ⟨⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩, rfl⟩
    have hA : A.Nonempty := by
      obtain ⟨v, hv⟩ := hne
      obtain ⟨a, _⟩ := hindex.2 ⟨v, hv⟩
      exact ⟨a.val, a.property⟩
    let hAT (a : ↥A) : Sum.inr a.val ∈ T := Finset.mem_union_right S (index a).property
    have hgens := (localGeneration G i hG hsc hlocal).2
    have hproj := ProjectiveRecurrence.archimedeanLatticeProjection G i D rfl S T A U
      Finset.subset_union_left hA
      (fun a => Finset.disjoint_left.mp hJS (index a).property) hAT
      (compactFullQuotient D rfl G i hG.1 han) hSnoncompact hUc hUo hG
      (fun a => (hgens a.val (Or.inr ((hJ _).mp (index a).property).choose_spec.2.2)).2.1)
    let e : (∀ a : ↥A, LocalPoints D i (.inr a.val)) ≃ₜ FinitePoints D i J :=
      Homeomorph.piCongrLeft (Y := fun w : ↥J => LocalPoints D i w.val)
        (Equiv.ofBijective index hindex)
    have he (x : FinitePoints D i T) :
        e (Specs.Arithmetic.ProjectiveRecurrence.evaluateArchimedean D i A hAT x) =
          forgetPlaces D i Finset.subset_union_right x := by
      funext w
      obtain ⟨a, rfl⟩ := hindex.2 w
      exact Homeomorph.piCongrLeft_apply_apply (Equiv.ofBijective index hindex) _ a
    have hproj' : Dense (projectedArithmetic D i S J U : Set (FinitePoints D i J)) := by
      refine (e.surjective.denseRange.dense_image e.continuous hproj).mono ?_
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (he x).symm⟩
    have hcontracts : Dense (Subgroup.closure {x : FinitePoints D i J | Contracted x} :
        Set (FinitePoints D i J)) := by
      apply contractedGenerateProduct
      rintro ⟨v, hv⟩
      obtain ⟨w, rfl, _, hc⟩ := (hJ v).mp hv
      exact (hgens w (Or.inr hc)).2.2
    exact (isolateAdelicFactors D i S J hJS U hUc hUo).2 hproj' hcontracts
  · have hj : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst J
    intro x
    have he : insertFinite D i S ∅ x = 1 := by
      apply RestrictedProduct.ext
      intro w
      rw [insertFinite_apply]
      simp
    rw [he, ← diagonalClosedSubgroup_coe]
    exact (diagonalClosedSubgroup D i S).one_mem

theorem finiteIsolation : FiniteIsolation.{u} := by
  intro K _ _ G i hG hsc hlocal han D S hS hnc hArch w hw x
  have hncf := (localPropertiesOfQuasiSplit LocalCompactnessCriterion.localCompactness
    D rfl G i hG w (hlocal.finiteQuasiSplit w)).2
  have h := (LocalCompactnessCriterion.isolateParabolicRadicals
    D rfl G i hG han S hS hnc hArch w hw hncf).2
  exact h x ((finiteRadicalsGenerate G i hG hsc hlocal w).symm ▸ Subgroup.mem_top x)

theorem weakApproximationLifting : WeakApproximationLifting.{u} := by
  classical
  intro K _ _ G i hG D S hconnected hisolated
  let J : Finset D.Place := (Finset.univ.filter
    (fun w : D.InfinitePlace => Sum.inr w ∉ S)).map ⟨Sum.inr, Sum.inr_injective⟩
  have hJ (w : D.Place) : w ∈ J ↔ ∃ a : D.InfinitePlace,
      Sum.inr a ∉ S ∧ Sum.inr a = w := by
    simp [J, Finset.mem_map, and_comm]
  have hd : Disjoint J S := Finset.disjoint_left.mpr fun x hx hs => by
    obtain ⟨w, hw, rfl⟩ := (hJ x).mp hx
    exact hw hs
  have hFin : ∀ (w : Outside D S), w.val ∉ J → ∀ x : LocalPoints D i w.val,
      RestrictedProduct.mulSingle (fun v : Outside D S => localSubgroup D i v.val) w x ∈
        diagonalClosure D i S := by
    rintro ⟨w | w, hw⟩ hnot x
    · exact hisolated w hw x
    · exact (hnot ((hJ (.inr w)).mpr ⟨w, hw, rfl⟩)).elim
  apply ((projectToRemainingPlaces D i S J hd).2 hFin).2.2.mp
  letI (w : (↑J : Set D.Place)) : ConnectedSpace (LocalPoints D i w.val) := by
    obtain ⟨b, hb⟩ := w
    obtain ⟨a, ha, rfl⟩ := (hJ b).mp hb
    exact hconnected a ha
  let C := closure (Set.range (rationalProjection D i J))
  have hOpen : IsOpen C := WeakApproximationByTori.identityNeighborhood.{u, u} G hG i J
  have hClopen : IsClopen C := ⟨isClosed_closure, hOpen⟩
  exact dense_iff_closure_eq.mpr (hClopen.eq_univ ⟨1, subset_closure ⟨1, map_one _⟩⟩)

open Specs.CharacterDescent (Cocharacter)
open Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open private forgetPlaces_continuous forgetPlaces_surjective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
open private rankPositiveOfIsotropic from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalCompactnessCriterion
open private centralizes_hasLimit from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private extendSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private trivial_baseChange_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private splitTorus_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers

private theorem noncentral_of_contracting_tangent {F : Type u} [Field F]
    {G : AffineAlgebraicGroup F} {c : Cocharacter G.val} (L : LimitDecomposition c)
    (hv : ∃ v : Lie F G.val, v ∈ lieImage L.contracting ∧ v ≠ 0) :
    IsNoncentral c := by
  classical
  by_contra h
  unfold IsNoncentral at h
  push Not at h
  obtain ⟨v, ⟨z, rfl⟩, hz⟩ := hv
  let R := CommAlgCat.of F (DualNumber F)
  let g : GroupPoints G.val R :=
    ((groupPointsFunctor F).map L.contracting.inclusion).app R z.toMul.val
  have hg := (L.contracting_points R g).mpr ⟨z.toMul.val, rfl⟩
  have hc := centralizes_hasLimit c (h _ g)
  letI := G.property.1
  exact hz (Subtype.ext (CocharacterDynamics.limitIsUnique c hc hg))

omit [NumberField K] in
private theorem isotropic_baseChange {F : Type u} [Field F] [Algebra K F]
    {G : AffineAlgebraicGroup K} (hiso : ¬ IsAnisotropic G.val) :
    ¬ IsAnisotropic (baseChangedAlgebraicGroup F G).val := by
  classical
  obtain ⟨S, h⟩ := not_forall.mp hiso
  obtain ⟨hS, hnt⟩ := not_imp.mp h
  intro han
  exact hnt ((trivial_baseChange_iff (K := F) S.group).mp
    (han (extendSubgroup F S) (splitTorus_baseChange hS)))

private theorem isotropicLocalNoncompact (D : GlobalFieldData.{u, u} K)
    (hD : D = .number inferInstance) (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : IsSemisimple G) (hiso : ¬ IsAnisotropic G.val) (w : D.Place) :
    ¬ CompactSpace (LocalPoints D i w) := by
  let F := D.Completion w
  let G₀ := baseChangedAlgebraicGroup F G
  have hs := (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := F) G
    hG.1 hG.2.1).mpr hG
  obtain ⟨_, j₀, _, e₀, _, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison K F G i
  let j : MatrixRealization G₀ := j₀
  let e : PointsIn j F ≃ₜ* LocalPoints D i w := e₀
  intro hc
  letI := hc
  exact isotropic_baseChange hiso
    ((LocalCompactnessCriterion.localCompactness D hD w G₀ j hs).mp
      (e.symm.surjective.compactSpace e.symm.continuous))

theorem isotropicStrongApproximation : IsotropicStrongApproximation.{u} := by
  intro K _ _ G i hG hsc hlocal hiso D S hS _
  obtain ⟨T, _, a, P, hv⟩ := LocalCocharacterEvaluation.isotropicContractingLie
    G hG.1 (rankPositiveOfIsotropic G hiso)
  let c : Cocharacter G.val := a ≫ T.inclusion
  have hc : IsNoncentral c := noncentral_of_contracting_tangent P hv
  obtain ⟨Q⟩ := CocharacterDynamics.existsLimitDecomposition G
    (CocharacterDynamics.oppositeCocharacter c)
  apply ((OppositeRadicals.approximation D G i hG c hc P Q).2.2.2.2 S hS).2
  obtain ⟨hf, ha⟩ := localGeneration G i hG hsc hlocal
  rintro ⟨w | w, _⟩
  · rw [(hf w).1]
    exact dense_univ
  · exact (ha w (Or.inr (isotropicLocalNoncompact D rfl G i hG.1 hiso _))).1

private theorem subsingleton_of_compact_contracted {A : Type*} [Group A]
    [TopologicalSpace A] [T2Space A] [IsTopologicalGroup A] [CompactSpace A]
    (hd : Dense (Subgroup.closure {x : A | Contracted x} : Set A)) : Subsingleton A := by
  have hgen : Subgroup.closure {x : A | Contracted x} ≤ ⊥ := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨a, ha⟩
    let f (b : A) := b * x * b⁻¹
    have hf : Continuous f := (continuous_id.mul continuous_const).mul continuous_inv
    have hc := (isCompact_range hf).isClosed
    have hmem : 1 ∈ Set.range f :=
      hc.mem_of_tendsto ha (Eventually.of_forall fun n => ⟨a ^ n, rfl⟩)
    obtain ⟨b, hb⟩ := hmem
    have he : x = 1 := by
      calc
        x = b⁻¹ * (b * x * b⁻¹) * b := by group
        _ = 1 := by rw [show b * x * b⁻¹ = 1 from hb, mul_one, inv_mul_cancel]
    exact Subgroup.mem_bot.mpr he
  have hd₁ : Dense ({1} : Set A) :=
    hd.mono (fun x hx => Set.mem_singleton_iff.mpr (Subgroup.mem_bot.mp (hgen hx)))
  have hAll : ({1} : Set A) = univ := isClosed_singleton.closure_eq.symm.trans hd₁.closure_eq
  have hOne (x : A) : x = 1 := Set.mem_singleton_iff.mp (hAll.symm ▸ Set.mem_univ x)
  exact ⟨fun x y => (hOne x).trans (hOne y).symm⟩

theorem anisotropicStrongApproximation : AnisotropicStrongApproximation.{u} := by
  classical
  intro K _ _ G i hG hsc hlocal han D S hS hSn
  let A := Finset.univ.filter (fun w : D.InfinitePlace =>
    Sum.inr w ∉ S ∧ ¬ CompactSpace (LocalPoints D i (.inr w)))
  let J : Finset D.Place := A.map ⟨Sum.inr, Sum.inr_injective⟩
  have hJ (v : D.Place) : v ∈ J ↔ ∃ w : NumberField.InfinitePlace K,
      v = Sum.inr w ∧ v ∉ S ∧ ¬ CompactSpace (LocalPoints D i v) := by
    constructor
    · intro hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
      exact ⟨w, rfl, (Finset.mem_filter.mp hw).2⟩
    · rintro ⟨w, rfl, hw, hc⟩
      exact Finset.mem_map.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw, hc⟩, rfl⟩
  have hJS : Disjoint J S := Finset.disjoint_left.mpr fun w hw hs =>
    ((hJ w).mp hw).choose_spec.2.1 hs
  let T := S ∪ J
  have hST : S ⊆ T := Finset.subset_union_left
  have hker : ((forgetOutside D i hST).ker : Set (Adeles D i S)) ⊆ diagonalClosure D i S := by
    rw [← range_insertFinite_eq_ker D i hJS]
    rintro _ ⟨x, rfl⟩
    exact archimedeanIsolation G i hG hsc hlocal han S J hS hSn hJ x
  apply ((enlargeOmittedSet D i S T hST).2 hker).2.2.mp
  have hTnc : ¬ CompactSpace (FinitePoints D i T) := by
    intro hc
    letI := hc
    exact hSn ((forgetPlaces_surjective D i hST).compactSpace
      (forgetPlaces_continuous D i hST))
  have hCompact (w : D.InfinitePlace) (hw : Sum.inr w ∉ T) :
      CompactSpace (LocalPoints D i (.inr w)) := by
    by_contra hc
    exact hw (Finset.mem_union_right S ((hJ _).mpr ⟨w, rfl, fun h => hw (hST h), hc⟩))
  refine weakApproximationLifting G i hG.1 T (fun w hw => ?_)
    (finiteIsolation G i hG hsc hlocal han T (hS.mono hST) hTnc hCompact)
  rcases w.isReal_or_isComplex with hR | hC
  · exact hlocal.realConnected w hR
  · letI : CompactSpace (LocalPoints D i (.inr w)) := hCompact w hw
    letI : T2Space (D.Completion (.inr w)) := inferInstanceAs (T2Space w.Completion)
    letI : T2Space (LocalPoints D i (.inr w)) := (usualLocalTopology D i (.inr w)).t2Space
    letI : IsTopologicalRing (D.Completion (.inr w)) :=
      inferInstanceAs (IsTopologicalRing w.Completion)
    letI : IsTopologicalGroup (LocalPoints D i (.inr w)) :=
      pointsInTopologicalGroup i (D.Completion (.inr w))
    have hsub : Subsingleton (LocalPoints D i (.inr w)) := subsingleton_of_compact_contracted
      (((localGeneration G i hG hsc hlocal).2 w (Or.inl hC)).2.2)
    exact connectedSpace_iff_univ.mpr
      ⟨⟨1, mem_univ _⟩, (show (univ : Set (LocalPoints D i (.inr w))).Subsingleton from
        fun _ _ _ _ => hsub.allEq _ _).isPreconnected⟩


end

end LinearAlgebraicGroups.Arithmetic.ExceptionalAdelicApproximation
