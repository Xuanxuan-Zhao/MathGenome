import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.CentralIsogenyRationalCosets
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.KummerObstructions
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Batteries.Tactic.OpenPrivate

noncomputable section

open AlgebraicGeometry CategoryTheory Topology
open scoped RestrictedProduct
open LinearAlgebraicGroups.Specs

universe u v

namespace LinearAlgebraicGroups.Arithmetic.CentralIsogenyRationalCosets

open AdelicGroups
open Specs.IntegralModels (MatrixRealization RationalPoints)
open Specs.CentralIsogenyRationalCosets

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

/-- A compact adelic set is uniformly integral outside finitely many places. -/
theorem compact_integralOutside {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    {Q : AffineAlgebraicGroup K} (j : MatrixRealization Q)
    {C : Set (Adeles D j ∅)} (hC : IsCompact C) :
    ∃ S : Finset (Outside D ∅), ∀ c ∈ C, ∀ w ∉ S, c w ∈ localSubgroup D j w.1 := by
  classical
  let 𝓑 := basicBoxes D j ∅
  have h𝓑 : TopologicalSpace.IsTopologicalBasis 𝓑 := adelicBasis D j ∅
  have hCover (c : Adeles D j ∅) : ∃ B : 𝓑, c ∈ B.val := by
    obtain ⟨B, hB, hc, _⟩ := h𝓑.exists_subset_of_mem_open
      (Set.mem_univ c) isOpen_univ
    exact ⟨⟨B, hB⟩, hc⟩
  choose T U hU hS hB using (fun B : 𝓑 => B.property)
  have hOpen (B : 𝓑) : IsOpen B.val := h𝓑.isOpen B.property
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun B : 𝓑 => B.val) hOpen
    (fun c _ => Set.mem_iUnion.mpr (hCover c))
  refine ⟨t.biUnion T, fun c hc w hw => ?_⟩
  obtain ⟨B, hBt, hcB⟩ := Set.mem_iUnion₂.mp (ht hc)
  have hwT : w ∉ T B := fun h => hw (Finset.mem_biUnion.mpr ⟨B, hBt, h⟩)
  rw [hB B] at hcB
  have hh := hcB w
  rw [hS B w hwT] at hh
  exact hh

section Descent

variable {A B L M : Type*} [Group A] [Group B] [Group L] [Group M]
variable (f : A →* B) (iA : A →* L) (iB : B →* M) (p : L →* M)

/-- Finite classes after scalar extension refine to finite rational cosets by
recording the displacement under each Galois automorphism. -/
theorem finiteCosets_of_finiteDisplacements {Γ X Y : Type*} [Finite Γ] [Finite Y]
    [Finite p.ker] (d : X → B) (cls : X → Y)
    (σL : Γ → L →* L) (σM : Γ → M →* M)
    (comm : ∀ a, p (iA a) = iB (f a)) (hinj : Function.Injective iB)
    (equiv : ∀ σ l, p (σL σ l) = σM σ (p l))
    (fixedB : ∀ σ b, σM σ (iB b) = iB b)
    (descend : ∀ l, (∀ σ, σL σ l = l) → ∃ a, iA a = l)
    (lift : ∀ x y, cls x = cls y → ∃ l, p l = iB (d x * (d y)⁻¹)) :
    ∃ F : Finset B, ∀ x, ∃ r ∈ F, ∃ a, d x = f a * r := by
  classical
  let cl (x : X) : Set.range cls := ⟨cls x, ⟨x, rfl⟩⟩
  have hz (j : Set.range cls) : ∃ x, cls x = j.val := j.property
  choose rep hrep using hz
  choose l hl using (fun x => lift x (rep (cl x)) (hrep (cl x)).symm)
  let displacement (x : X) (σ : Γ) : p.ker :=
    ⟨(l x)⁻¹ * σL σ (l x), MonoidHom.mem_ker.mpr (by
      rw [map_mul, map_inv, equiv, hl, fixedB, inv_mul_cancel])⟩
  let data (x : X) := (cl x, displacement x)
  have hs (j : Set.range data) : ∃ x, data x = j.val := j.property
  choose representatives hreps using hs
  let F := (Set.finite_range (fun j => d (representatives j))).toFinset
  refine ⟨F, fun x => ?_⟩
  let j : Set.range data := ⟨data x, ⟨x, rfl⟩⟩
  let y := representatives j
  have hdata : data y = data x := hreps j
  have hcl : cl y = cl x := congrArg Prod.fst hdata
  have hdis (σ : Γ) : (l y)⁻¹ * σL σ (l y) = (l x)⁻¹ * σL σ (l x) :=
    congrArg (fun z => ((z.2 σ : p.ker) : L)) hdata
  have hfixed (σ : Γ) : σL σ (l x * (l y)⁻¹) = l x * (l y)⁻¹ := by
    rw [map_mul, map_inv,
      show σL σ (l y) = l y * ((l x)⁻¹ * σL σ (l x)) by rw [← hdis, mul_inv_cancel_left]]
    group
  obtain ⟨a, ha⟩ := descend _ hfixed
  have hpa : f a = d x * (d y)⁻¹ := by
    apply hinj
    rw [← comm, ha, map_mul, map_inv, hl, hl, hcl, ← map_inv, ← map_mul]
    congr 1
    group
  refine ⟨d y, by simpa [F] using (show d y ∈ Set.range (fun j => d (representatives j)) from ⟨j, rfl⟩), a, ?_⟩
  rw [hpa, inv_mul_cancel_right]

end Descent

section SplitIsogeny

open Specs.CentralCover (SplitCoverData)
open Specs.CentralIsogenies (IsCentralIsogeny)
open Specs.GeometricRadicals (IsSemisimple IsSplitTorus baseChangedSubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open private exists_split_maximalTorus_finiteGalois centralIsogenyFieldExtension
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.CentralCover
open private splitTorusImage from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
open private maximalTorus_finiteImage from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralCentralQuotient
open private baseChangeMapPullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private splitTorus_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private isTorus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies

/-- A given central isogeny acquires split maximal torus coordinates after finite
Galois extension. The split source torus has a split scheme image. -/
theorem splitIsogeny {K : Type u} [Field K] {G Q : AffineAlgebraicGroup K}
    (q : G.val ⟶ Q.val) (hG : IsSemisimple G) (hQ : IsSemisimple Q)
    (hq : IsCentralIsogeny q) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : FiniteDimensional K E) (_ : IsGalois K E),
      let G' := baseChangedAlgebraicGroup E G
      let Q' := baseChangedAlgebraicGroup E Q
      let q' : G'.val ⟶ Q'.val := (groupBaseChange K E).map q
      ∃ N : ClosedSubgroup G'.val, IsCentralIsogeny q' ∧ IsSchemeKernel q' N ∧
        Nonempty (SplitCoverData Q' G' q' N) := by
  obtain ⟨E, _, _, _, _, T, hG', hsT, hmT⟩ :=
    exists_split_maximalTorus_finiteGalois G hG
  let G' := baseChangedAlgebraicGroup E G
  let Q' := baseChangedAlgebraicGroup E Q
  let q' : G'.val ⟶ Q'.val := (groupBaseChange K E).map q
  have hq' : IsCentralIsogeny q' := centralIsogenyFieldExtension hq
  have hQ' : IsSemisimple Q' :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := E) Q hQ.1 hQ.2.1).mpr hQ
  obtain ⟨S, p, hsS, hp⟩ :=
    splitTorusImage (closedSubgroupAlgebraicGroup T) Q' hsT (T.inclusion ≫ q')
  have hmS : IsGeometricallyMaximal S := by
    let L := AlgebraicClosure E
    let F := groupBaseChange E L
    let G'' := baseChangedAlgebraicGroup L G'
    let Q'' := baseChangedAlgebraicGroup L Q'
    let q'' : G''.val ⟶ Q''.val := F.map q'
    let T' := baseChangedSubgroup L T hmT.choose
    have hcS : IsClosedImmersion (F.map S.inclusion).hom.hom.left :=
      MorphismProperty.of_isPullback (baseChangeMapPullback (K := L) S.inclusion.hom.hom).flip
        S.isClosedImmersion
    let S' := baseChangedSubgroup L S hcS
    have hsS' := isTorus_of_split (splitTorus_baseChange L hsS)
    have hq'' : IsCentralIsogeny q'' := centralIsogenyFieldExtension hq'
    letI := hq''.1
    letI := hq''.2.1
    letI := hq''.2.2.1
    letI : LocallyOfFiniteType Q''.val.X.hom := Q''.property.2.1
    haveI : LocallyOfFiniteType (q''.hom.hom.left ≫ Q''.val.X.hom) := by
      rw [Over.w q''.hom.hom]
      exact G''.property.2.1
    letI := LocallyOfFiniteType.isLocallyNoetherian Q''.val.X.hom
    letI := locallyOfFiniteType_of_comp q''.hom.hom.left Q''.val.X.hom
    letI : LocallyOfFinitePresentation q''.hom.hom.left := inferInstance
    have hG'' : IsSemisimple G'' :=
      (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := L) G' hG'.1 hG'.2.1).mpr hG'
    letI := hG''.2.1
    have hcG'' : ConnectedSpace G''.val.X.left :=
      GeometricallyConnected.connectedSpace_of_subsingleton G''.val.X.hom
    have hh : T'.inclusion ≫ q'' = F.map p ≫ S'.inclusion :=
      (F.map_comp T.inclusion q').symm.trans ((congrArg F.map hp.1.symm).trans
        (F.map_comp p S.inclusion))
    exact ⟨hcS, maximalTorus_finiteImage q'' hG''.1 hcG'' T' S' (F.map p)
      hmT.choose_spec hsS' hh⟩
  obtain ⟨N, hN, _⟩ := hq'.2.2.2
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, N, hq', hN, ?_⟩
  exact CentralCover.splitCoverDataExists Q' G' (reductive_of_semisimple Q' hQ')
    (reductive_of_semisimple G' hG') T S hsT hmT hsS hmS q' p hq' ⟨hp.1, hp.2.1, hp.2.2.1⟩ N hN

end SplitIsogeny

section Completions

open NumberField IsDedekindDomain
open scoped WithZero
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]

/-- The finite place of the smaller number field below a given finite place. -/
abbrev below (w : NumberFinitePlace E) : NumberFinitePlace K := w.under (𝓞 K)

variable (w : NumberFinitePlace E)

private instance liesOver_below : w.asIdeal.LiesOver (below (K := K) w).asIdeal :=
  inferInstanceAs (w.asIdeal.LiesOver (w.asIdeal.under (𝓞 K)))

private abbrev rawCompletionMap :
    ((below (K := K) w).valuation K).Completion →+* (w.valuation E).Completion :=
  UniformSpace.Completion.mapRingHom _
    (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (K := K) E (below w) w).continuous

/-- Scalar extension on finite completions over a finite place of the larger field. -/
def completionMap : (below (K := K) w).adicCompletion K →+* w.adicCompletion E :=
  ((HeightOneSpectrum.adicCompletion.equiv E w).symm.toRingHom.comp (rawCompletionMap (K := K) w)).comp
    (HeightOneSpectrum.adicCompletion.equiv K (below w)).toRingHom

theorem completionMap_algebraMap (x : K) :
    completionMap w (algebraMap K ((below (K := K) w).adicCompletion K) x) =
      algebraMap E (w.adicCompletion E) (algebraMap K E x) := by
  apply HeightOneSpectrum.adicCompletion.ext
  change rawCompletionMap (K := K) w
    ((WithVal.equiv ((below (K := K) w).valuation K)).symm x) =
      (↑((WithVal.equiv (w.valuation E)).symm (algebraMap K E x)) : (w.valuation E).Completion)
  rw [rawCompletionMap, UniformSpace.Completion.mapRingHom_coe]
  rfl

theorem completionMap_mem_integers {x : (below (K := K) w).adicCompletion K}
    (hx : x ∈ (below w).adicCompletionIntegers K) :
    completionMap w x ∈ w.adicCompletionIntegers E := by
  have hcont : Continuous (completionMap (K := K) w) := by
    change Continuous (HeightOneSpectrum.adicCompletion.ofCompletion ∘
      UniformSpace.Completion.map (algebraMap (WithVal ((below (K := K) w).valuation K))
        (WithVal (w.valuation E))) ∘ HeightOneSpectrum.adicCompletion.toCompletion)
    exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion E w).comp
      (UniformSpace.Completion.continuous_map.comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion K (below w)))
  revert hx
  refine (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) K (below w)).induction_on x ?_ ?_
  · change IsClosed {x | x ∈ (below w).adicCompletionIntegers K →
        completionMap w x ∈ w.adicCompletionIntegers E}
    have he : {x | x ∈ (below w).adicCompletionIntegers K →
        completionMap w x ∈ w.adicCompletionIntegers E} =
        (SetLike.coe ((below (K := K) w).adicCompletionIntegers K))ᶜ ∪
          completionMap w ⁻¹' (SetLike.coe (w.adicCompletionIntegers E)) := by
      ext a
      simp [imp_iff_not_or]
    rw [he]
    exact (Valued.isOpen_valuationSubring _).isClosed_compl.union
      ((Valued.isClosed_valuationSubring _).preimage hcont)
  · intro y hy
    rw [completionMap_algebraMap]
    change Valued.v (algebraMap K _ y) ≤ (1 : ℤᵐ⁰) at hy
    change Valued.v (algebraMap E _ (algebraMap K E y)) ≤ (1 : ℤᵐ⁰)
    change Valued.v ((y : K) : (below (K := K) w).adicCompletion K) ≤ (1 : ℤᵐ⁰) at hy
    change Valued.v ((algebraMap K E y : E) : w.adicCompletion E) ≤ (1 : ℤᵐ⁰)
    have hy' : (below (K := K) w).valuation K y ≤ 1 := by
      simpa only [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hy
    have hpow := pow_le_one₀ (n := w.asIdeal.ramificationIdx (𝓞 K)) zero_le hy'
    rw [HeightOneSpectrum.valuation_liesOver E (below w) w] at hpow
    simpa only [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hpow

/-- Integral completion points remain integral upon extending the place. -/
def completionIntegersMap :
    (below (K := K) w).adicCompletionIntegers K →+* w.adicCompletionIntegers E :=
  ((completionMap w).comp ((below w).adicCompletionIntegers K).subtype).codRestrict
    (w.adicCompletionIntegers E).toSubring fun x => completionMap_mem_integers w x.property

end Completions

section FieldPoints

open Opposite WithConv
open Specs.IntegralCentralQuotient (HopfSpectrum spectrumOfHopfHom)
open Specs.CentralIsogenies (IsCentralIsogeny)
open private schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open scoped CategoryTheory.MonObj

variable {k : Type u} [Field k] {G Q : AffineAlgebraicGroup k}

/-- Scalar extension on the actual points of any group over a field. -/
def changeScalars (H : GroupScheme k) {S T : Type u} [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] (f : S →ₐ[k] T) :
    ((groupPointsFunctor k).obj H).obj (CommAlgCat.of k S) →*
      ((groupPointsFunctor k).obj H).obj (CommAlgCat.of k T) :=
  (((groupPointsFunctor k).obj H).map (CommAlgCat.ofHom f)).hom

theorem changeScalars_pointMap {S T : Type u} [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] (f : S →ₐ[k] T) (q : G.val ⟶ Q.val)
    (x : ((groupPointsFunctor k).obj G.val).obj (CommAlgCat.of k S)) :
    pointMap q T (changeScalars G.val f x) = changeScalars Q.val f (pointMap q S x) :=
  ConcreteCategory.congr_hom (((groupPointsFunctor k).map q).naturality (CommAlgCat.ofHom f)) x

/-- An affine presentation identifies scheme points with convolution algebra maps. -/
private def pointCoordinates {A : Type u} [CommRing A] [HopfAlgebra k A]
    {H : GroupScheme k} (e : HopfSpectrum k A ≅ H) (S : Type u) [CommRing S] [Algebra k S] :
    ((groupPointsFunctor k).obj H).obj (CommAlgCat.of k S) ≃* WithConv (A →ₐ[k] S) :=
  (((groupPointsFunctor k).mapIso e.symm).app (CommAlgCat.of k S)).groupIsoToMulEquiv.trans
    ((LinearAlgebraicGroups.hopfSpecPointIso (CommHopfAlgCat.of k A)).app
      (CommAlgCat.of k S)).groupIsoToMulEquiv.symm

private theorem pointCoordinates_changeScalars {A : Type u} [CommRing A] [HopfAlgebra k A]
    {H : GroupScheme k} (e : HopfSpectrum k A ≅ H) {S T : Type u}
    [CommRing S] [CommRing T] [Algebra k S] [Algebra k T] (f : S →ₐ[k] T)
    (p : ((groupPointsFunctor k).obj H).obj (CommAlgCat.of k S)) :
    pointCoordinates e T (changeScalars H f p) =
      toConv (f.comp (pointCoordinates e S p).ofConv) := by
  apply (pointCoordinates e T).symm.injective
  rw [MulEquiv.symm_apply_apply]
  have h : changeScalars H f ((pointCoordinates e S).symm (pointCoordinates e S p)) =
      (pointCoordinates e T).symm (toConv (f.comp (pointCoordinates e S p).ofConv)) := by
    generalize pointCoordinates e S p = a
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom a.ofConv.toRingHom) ≫ e.hom.hom.hom.left) =
      Spec.map (CommRingCat.ofHom ((f.comp a.ofConv).toRingHom)) ≫ e.hom.hom.hom.left
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  simpa only [MulEquiv.symm_apply_apply] using h

theorem changeScalars_injective {S T : Type u} [Field S] [Field T] [Algebra k S] [Algebra k T]
    (f : S →ₐ[k] T) (H : AffineAlgebraicGroup k) :
    Function.Injective (changeScalars H.val f) := by
  obtain ⟨A, ⟨e⟩⟩ := essImage_hopfSpec.mpr H.property.1
  intro x y h
  apply (pointCoordinates e S).injective
  apply ofConv_injective
  ext a
  apply f.injective
  have hh := congrArg (pointCoordinates e T) h
  rw [pointCoordinates_changeScalars, pointCoordinates_changeScalars] at hh
  exact congrArg (fun z => z.ofConv a) hh

/-- A point fixed by the Galois group descends to a rational point. -/
theorem descendPoint {E : Type u} [Field E] [Algebra k E] [IsGalois k E]
    (p : ((groupPointsFunctor k).obj G.val).obj (CommAlgCat.of k E))
    (hp : ∀ σ : Gal(E/k), changeScalars G.val σ.toAlgHom p = p) :
    ∃ a : RationalPoints G, changeScalars G.val (Algebra.ofId k E) a = p := by
  obtain ⟨A, ⟨e⟩⟩ := essImage_hopfSpec.mpr G.property.1
  let f := (pointCoordinates e E p).ofConv
  have hf (a : A.unop) : f a ∈ (Algebra.ofId k E).range := by
    change f a ∈ Set.range (algebraMap k E)
    apply (InfiniteGalois.mem_range_algebraMap_iff_fixed (f a)).mpr
    intro σ
    have h := congrArg (pointCoordinates e E) (hp σ)
    rw [pointCoordinates_changeScalars] at h
    exact congrArg (fun z => z.ofConv a) h
  let incl := AlgEquiv.ofInjective (Algebra.ofId k E) (algebraMap k E).injective
  let a := incl.symm.toAlgHom.comp (f.codRestrict (Algebra.ofId k E).range hf)
  refine ⟨(pointCoordinates e k).symm (toConv a), (pointCoordinates e E).injective ?_⟩
  rw [pointCoordinates_changeScalars, MulEquiv.apply_symm_apply]
  apply ofConv_injective
  ext x
  exact congrArg Subtype.val (incl.apply_symm_apply ⟨f x, hf x⟩)

/-- The scheme-theoretic kernel of a finite isogeny has finitely many points
over any extension field. -/
theorem finitePointKernel (q : G.val ⟶ Q.val) (hq : IsCentralIsogeny q)
    (E : Type u) [Field E] [Algebra k E] : Finite (pointMap q E).ker := by
  obtain ⟨hfin, _, _, N, hN, _⟩ := hq
  have hfinN : IsFinite N.group.X.hom :=
    MorphismProperty.of_isPullback (hN.map (Over.forget (Spec (CommRingCat.of k)))) hfin
  letI := hfinN
  have hAffine := isAffine_of_isAffineHom N.group.X.hom
  obtain ⟨A, ⟨e⟩⟩ := essImage_hopfSpec.mpr hAffine
  have hiso : IsIso e.hom.hom.hom.left :=
    ((Grp.forget _) ⋙ (Over.forget _)).map_isIso e.hom
  have hf : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k A.unop))) := by
    have hf' : IsFinite (e.hom.hom.hom.left ≫ N.group.X.hom) := inferInstance
    rwa [Over.w e.hom.hom.hom] at hf'
  rw [IsFinite.SpecMap_iff] at hf
  letI : Module.Finite k A.unop := RingHom.finite_algebraMap.mp hf
  letI : Finite (WithConv (A.unop →ₐ[k] E)) :=
    Finite.of_injective ofConv (ofConv_injective)
  haveI : Finite (((groupPointsFunctor k).obj N.group).obj (CommAlgCat.of k E)) :=
    Finite.of_injective _ (pointCoordinates e E).injective
  have hfactors (p : (pointMap q E).ker) :
      ∃ t : ((groupPointsFunctor k).obj N.group).obj (CommAlgCat.of k E),
        pointMap N.inclusion E t = p.val :=
    (schemeKernel_sections hN p.val).mpr (MonoidHom.mem_ker.mp p.property)
  choose t ht using hfactors
  exact Finite.of_injective t fun x y he => Subtype.ext
    ((ht x).symm.trans ((congrArg (pointMap N.inclusion E) he).trans (ht y)))

end FieldPoints

section KummerPoints

open WithConv Algebra.TensorProduct
open scoped TensorProduct
open Specs.IntegralCentralQuotient (rightCoaction HasDegree HopfSpectrum spectrumOfHopfHom
  IsRightTorsor)
open Specs.CentralCoverSpreading (KernelCoordinates IsFullKernel)
open Kummer

local instance convolutionGroupOverRing {R A T : Type u} [CommRing R] [CommRing A]
    [CommRing T] [HopfAlgebra R A] [Algebra R T] : Group (WithConv (A →ₐ[R] T)) where
  toMonoid := inferInstance
  inv f := toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A))
  inv_mul_cancel f := by
    let s : WithConv (A →ₐ[R] A) := toConv (HopfAlgebra.antipodeAlgHom R A)
    let i : WithConv (A →ₐ[R] A) := toConv (AlgHom.id R A)
    have hs : s * i = 1 := AlgHom.antipode_id_cancel
    have h := AlgHom.comp_convMul_distrib f.ofConv s i
    rw [hs] at h
    have h₁ : f.ofConv.comp (1 : WithConv (A →ₐ[R] A)).ofConv =
        (1 : WithConv (A →ₐ[R] T)).ofConv := by
      ext x
      exact f.ofConv.commutes (Coalgebra.counit x)
    apply ofConv_injective
    change (toConv (f.ofConv.comp s.ofConv) * f).ofConv = _
    simpa [i, h₁] using h.symm

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [HopfAlgebra R A]
  [HopfAlgebra R B]
variable {I : Type} (n : I → ℕ)
variable (q : B →ₐc[R] A) (π : A →ₐc[R] KernelCoordinates R n)

/-- Precomposition by a Hopf map on convolution points. -/
def convolutionMap {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
    [HopfAlgebra R A] [HopfAlgebra R B] [Algebra R T] (f : B →ₐc[R] A) :
    WithConv (A →ₐ[R] T) →* WithConv (B →ₐ[R] T) where
  toFun x := toConv (x.ofConv.comp f.toAlgHom)
  map_one' := by
    apply ofConv_injective
    ext b
    simp [AlgHom.convOne_def]
  map_mul' x y := ofConv_injective (AlgHom.convMul_comp_bialgHom_distrib x y f)

/-- Postcomposition by a scalar map on convolution points. -/
def convolutionScalars {T L : Type u} [CommRing T] [CommRing L] [Algebra R T] [Algebra R L]
    (f : T →ₐ[R] L) : WithConv (A →ₐ[R] T) →* WithConv (A →ₐ[R] L) where
  toFun x := toConv (f.comp x.ofConv)
  map_one' := by
    apply ofConv_injective
    ext a
    simp [AlgHom.convOne_def]
  map_mul' x y := ofConv_injective (AlgHom.comp_convMul_distrib f x y)

private theorem evaluation_translate {L : Type u} [CommRing L] [Algebra R L]
    {b : A} (h : HasDegree π (coordinateCharacter n i) b)
    (x : WithConv (A →ₐ[R] L)) (z : KernelCoordinates R n →ₐ[R] L) :
    (x * convolutionMap π (toConv z)) b =
      x b * z (MonoidAlgebra.of R _ (coordinateCharacter n i)) := by
  have he : (lift x.ofConv z (fun _ _ => Commute.all _ _)).comp
        (Algebra.TensorProduct.map (AlgHom.id R A) π.toAlgHom) =
      lift x.ofConv (z.comp π.toAlgHom) (fun _ _ => Commute.all _ _) := by
    ext <;> simp
  have hv := congrArg (lift x.ofConv z (fun _ _ => Commute.all _ _)) h
  change (lift x.ofConv z (fun _ _ => Commute.all _ _))
      ((Algebra.TensorProduct.map (AlgHom.id R A) π.toAlgHom) (Coalgebra.comul b)) = _ at hv
  rw [← AlgHom.comp_apply, he, lift_tmul] at hv
  rw [AlgHom.convMul_apply]
  exact hv

/-- Evaluate a homogeneous unit on a lift of the point defining the fibre. -/
private theorem evaluateClass {T L : Type u} [Field T] [Field L] [Algebra R T] [Algebra R L]
    [Algebra T L] [IsScalarTower R T L]
    (p : B →ₐ[R] T) (x : A →ₐ[R] L)
    (hx : x.comp q.toAlgHom = (IsScalarTower.toAlgHom R T L).comp p)
    {i : I} {c : Classes T (n i)}
    (hc : letI : Algebra B A := q.toAlgHom.toAlgebra; PullbackHasClass n π p i c) :
    ∃ (b : A) (a : Tˣ), HasDegree π (coordinateCharacter n i) b ∧
      x b ≠ 0 ∧ x b ^ n i = algebraMap T L (a : T) ∧ classOf (n i) a = c := by
  letI : Algebra B A := q.toAlgHom.toAlgebra
  letI : Algebra B T := p.toAlgebra
  letI : Algebra B L := (x.comp q.toAlgHom).toAlgebra
  let xB : A →ₐ[B] L := { x.toRingHom with commutes' := fun _ => rfl }
  let iB : T →ₐ[B] L := { (algebraMap T L) with
    commutes' := fun b => (congrArg (fun f : B →ₐ[R] L => f b) hx).symm }
  let a := Algebra.TensorProduct.lift iB xB (fun _ _ => Commute.all _ _)
  obtain ⟨b, t, hdeg, hu, hp, hc⟩ := hc
  refine ⟨b, t, hdeg, ?_, ?_, hc⟩
  · have hm := hu.map a
    have hh : a ((1 : T) ⊗ₜ[B] b) = x b := by simp [a, iB, xB]
    rw [hh] at hm
    exact hm.ne_zero
  · have hh := congrArg a hp
    change a (((1 : T) ⊗ₜ[B] b) ^ n i) = a ((t.val : T) ⊗ₜ[B] (1 : A)) at hh
    simp [a, iB, xB] at hh
    exact hh

open private finiteProductHomEquiv cyclicHomEquiv
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

private def kernelRootCoordinates {L : Type u} [CommRing L] [Algebra R L]
    [Fintype I] :
    WithConv (KernelCoordinates R n →ₐ[R] L) ≃* (∀ i, rootsOfUnity (n i) L) := by
  classical
  exact (MonoidAlgebra.liftMulEquiv R L _).symm.trans (MonoidHom.toHomUnitsMulEquiv.trans
    (MulEquiv.ulift.monoidHomCongrLeft.trans
      ((finiteProductHomEquiv (fun i => Multiplicative (ZMod (n i))) Lˣ).trans
        (MulEquiv.piCongrRight fun i => cyclicHomEquiv (n i) L))))

private theorem kernelRootCoordinates_apply {L : Type u} [CommRing L] [Algebra R L]
    [Fintype I]
    (z : KernelCoordinates R n →ₐ[R] L) (i : I) :
    ((kernelRootCoordinates (R := R) n (toConv z) i).val : L) =
      z (MonoidAlgebra.of R _ (coordinateCharacter n i)) := by
  classical
  rfl

/-- Over an algebraically closed field a point lifts through the finite flat cover. -/
theorem geometricLift {L : Type u} [Field L] [IsAlgClosed L] [Algebra R L]
    (h : IsRightTorsor q π) (p : B →ₐ[R] L) :
    ∃ x : A →ₐ[R] L, x.comp q.toAlgHom = p := by
  letI : Algebra B A := q.toAlgHom.toAlgebra
  letI : Algebra B L := p.toAlgebra
  let F := L ⊗[B] A
  have hfin : IsFinite (Spec.map (CommRingCat.ofHom q.toAlgHom.toRingHom)) := h.1
  rw [IsFinite.SpecMap_iff] at hfin
  letI : Module.Finite B A := hfin
  have hff :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom q.toAlgHom.toRingHom)).mp
      ⟨h.2.1, h.2.2.1⟩
  letI : Module.FaithfullyFlat B A := RingHom.faithfullyFlat_algebraMap_iff.mp hff
  letI : Module.Finite L F := inferInstanceAs (Module.Finite L (L ⊗[B] A))
  letI : Module.FaithfullyFlat L F := inferInstanceAs (Module.FaithfullyFlat L (L ⊗[B] A))
  letI : Nontrivial F := (FaithfulSMul.algebraMap_injective L F).nontrivial
  obtain ⟨J, hJ⟩ := Ideal.exists_maximal (α := F)
  letI : J.IsMaximal := hJ
  letI : Field (F ⧸ J) := Ideal.Quotient.field J
  let g : F ⧸ J →ₐ[L] L := IsAlgClosed.lift
  let s : F →ₐ[L] L := g.comp (Ideal.Quotient.mkₐ L J)
  let iA : A →+* F := (includeRight : A →ₐ[B] F).toRingHom
  have hs (b : B) : s (iA (q b)) = p b := by
    change s ((includeRight : A →ₐ[B] F) (algebraMap B A b)) = p b
    rw [AlgHom.commutes]
    change s (algebraMap L F (p b)) = p b
    exact s.commutes _
  let x : A →ₐ[R] L := { s.toRingHom.comp iA with
    commutes' := fun r => by
      change s (iA (algebraMap R A r)) = algebraMap R L r
      rw [← q.toAlgHom.commutes r]
      exact (hs (algebraMap R B r)).trans (p.commutes r) }
  exact ⟨x, AlgHom.ext hs⟩

open CategoryTheory.Limits Opposite
open Specs.IntegralCentralQuotient (spectrumOfAlgHom)

/-- The kernel points are exactly the evaluations of the given split kernel coordinates. -/
theorem convolutionKernel {L : Type u} [CommRing L] [Algebra R L]
    (h : IsRightTorsor q π) (x : WithConv (A →ₐ[R] L)) :
    convolutionMap q x = 1 ↔
      ∃ z : KernelCoordinates R n →ₐ[R] L, convolutionMap π (toConv z) = x := by
  let Z := KernelCoordinates R n
  let f := CommRingCat.ofHom q.toAlgHom.toRingHom
  let l := CommRingCat.ofHom (includeLeftRingHom : A →+* A ⊗[R] Z)
  let r := CommRingCat.ofHom (rightCoaction π).toRingHom
  have hp : IsPushout f f l r :=
    (IsPullback.of_map_of_faithful Scheme.Spec h.2.2.2.2.flip).unop
  let e : WithConv (A →ₐ[R] L) := 1
  constructor
  · intro hx
    have he : f ≫ CommRingCat.ofHom e.ofConv.toRingHom =
        f ≫ CommRingCat.ofHom x.ofConv.toRingHom := by
      have hh : convolutionMap q e = convolutionMap q x := (map_one _).trans hx.symm
      exact congrArg (fun y : WithConv (B →ₐ[R] L) => CommRingCat.ofHom y.ofConv.toRingHom) hh
    let g := hp.desc (CommRingCat.ofHom e.ofConv.toRingHom)
      (CommRingCat.ofHom x.ofConv.toRingHom) he
    have hl (a : A) : g ((includeLeft : A →ₐ[R] A ⊗[R] Z) a) = e a :=
      ConcreteCategory.congr_hom (hp.inl_desc _ _ he) a
    have hr (a : A) : g (rightCoaction π a) = x a :=
      ConcreteCategory.congr_hom (hp.inr_desc _ _ he) a
    let gA : A ⊗[R] Z →ₐ[R] L := { g.hom with
      commutes' := fun t => by
        change g ((includeLeft : A →ₐ[R] A ⊗[R] Z) (algebraMap R A t)) = algebraMap R L t
        rw [hl]
        exact e.ofConv.commutes _ }
    let z : Z →ₐ[R] L := gA.comp includeRight
    have hg : gA = lift e.ofConv z (fun _ _ => Commute.all _ _) := by
      ext a
      · simpa [gA] using hl a
      · simp [z]
    have hm : e * convolutionMap π (toConv z) = x := by
      apply ofConv_injective
      ext a
      rw [AlgHom.convMul_apply]
      have heval : (lift e.ofConv z (fun _ _ => Commute.all _ _)).comp
            (Algebra.TensorProduct.map (AlgHom.id R A) π.toAlgHom) =
          lift e.ofConv (z.comp π.toAlgHom) (fun _ _ => Commute.all _ _) := by ext <;> simp
      change lift e.ofConv (z.comp π.toAlgHom) (fun _ _ => Commute.all _ _)
        (Coalgebra.comul a) = x a
      rw [← heval, ← hg]
      exact hr a
    exact ⟨z, (one_mul _).symm.trans hm⟩
  · rintro ⟨z, rfl⟩
    have heval : (lift e.ofConv z (fun _ _ => Commute.all _ _)).comp
          (Algebra.TensorProduct.map (AlgHom.id R A) π.toAlgHom) =
        lift e.ofConv (z.comp π.toAlgHom) (fun _ _ => Commute.all _ _) := by ext <;> simp
    have hmul (a : A) : lift e.ofConv z (fun _ _ => Commute.all _ _) (rightCoaction π a) =
        (convolutionMap π (toConv z)) a := by
      change lift e.ofConv z (fun _ _ => Commute.all _ _)
        ((Algebra.TensorProduct.map (AlgHom.id R A) π.toAlgHom) (Coalgebra.comul a)) = _
      rw [← AlgHom.comp_apply, heval]
      exact (AlgHom.convMul_apply e (convolutionMap π (toConv z)) a).symm.trans
        (congrArg (fun y : WithConv (A →ₐ[R] L) => y a) (one_mul _))
    apply ofConv_injective
    ext b
    have hh := ConcreteCategory.congr_hom hp.w b
    change (includeLeft : A →ₐ[R] A ⊗[R] Z) (q b) = rightCoaction π (q b) at hh
    change (convolutionMap π (toConv z)) (q b) = (1 : WithConv (B →ₐ[R] L)) b
    rw [← hmul, ← hh]
    change lift e.ofConv z (fun _ _ => Commute.all _ _) (q b ⊗ₜ[R] (1 : Z)) = _
    rw [lift_tmul, map_one, mul_one]
    exact congrArg (fun y : WithConv (B →ₐ[R] L) => y b)
      (map_one (convolutionMap q))

section Galois

variable {T L : Type u} [Field T] [Field L] [Algebra R T] [Algebra T L] [Algebra R L]
  [IsScalarTower R T L] [IsGalois T L]

private abbrev scalarInclusion : T →ₐ[R] L := IsScalarTower.toAlgHom R T L

private def act {C : Type u} [CommRing C] [HopfAlgebra R C] (σ : Gal(L/T)) :
    WithConv (C →ₐ[R] L) →* WithConv (C →ₐ[R] L) :=
  convolutionScalars (σ.toAlgHom.restrictScalars R)

omit [IsGalois T L] in
private theorem act_scalarInclusion {C : Type u} [CommRing C] [HopfAlgebra R C]
    (σ : Gal(L/T)) (p : WithConv (C →ₐ[R] T)) :
    act (R := R) σ (convolutionScalars scalarInclusion p) =
      convolutionScalars scalarInclusion p := by
  apply ofConv_injective
  ext c
  exact σ.commutes (p c)

private theorem descendConvolution {C : Type u} [CommRing C] [HopfAlgebra R C]
    (x : WithConv (C →ₐ[R] L)) (hx : ∀ σ : Gal(L/T), act (R := R) σ x = x) :
    ∃ a : WithConv (C →ₐ[R] T), convolutionScalars scalarInclusion a = x := by
  have hr (c : C) : x c ∈ (scalarInclusion (R := R) (T := T) (L := L)).range :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (x c)).mpr fun σ =>
      congrArg (fun y : WithConv (C →ₐ[R] L) => y c) (hx σ)
  let e := AlgEquiv.ofInjective (scalarInclusion (R := R) (T := T) (L := L))
    (algebraMap T L).injective
  let a := e.symm.toAlgHom.comp (x.ofConv.codRestrict _ hr)
  refine ⟨toConv a, ofConv_injective (AlgHom.ext fun c => ?_)⟩
  exact congrArg Subtype.val (e.apply_symm_apply ⟨x c, hr c⟩)

omit [IsGalois T L] in
private theorem displacementKernel (h : IsRightTorsor q π)
    (p : WithConv (B →ₐ[R] T)) (x : WithConv (A →ₐ[R] L))
    (hx : convolutionMap q x = convolutionScalars scalarInclusion p) (σ : Gal(L/T)) :
    ∃ z : KernelCoordinates R n →ₐ[R] L,
      convolutionMap π (toConv z) = x⁻¹ * act (R := R) σ x := by
  apply (convolutionKernel n q π h _).mp
  have he : convolutionMap q (act (R := R) σ x) =
      act (R := R) σ (convolutionMap q x) := rfl
  rw [map_mul, map_inv, he, hx, act_scalarInclusion, inv_mul_cancel]

omit [IsGalois T L] in
private theorem displacement_eval (σ : Gal(L/T)) (x : WithConv (A →ₐ[R] L))
    (z : KernelCoordinates R n →ₐ[R] L)
    (hz : convolutionMap π (toConv z) = x⁻¹ * act (R := R) σ x)
    {b : A} {i : I} (hb : HasDegree π (coordinateCharacter n i) b) :
    σ (x b) = x b * z (MonoidAlgebra.of R _ (coordinateCharacter n i)) := by
  have he : act (R := R) σ x = x * convolutionMap π (toConv z) := by
    rw [hz, mul_inv_cancel_left]
  exact (congrArg (fun y : WithConv (A →ₐ[R] L) => y b) he).trans
    (evaluation_translate n π hb x z)

end Galois

/-- Left multiplication by a rational lift preserves every Kummer coordinate. -/
theorem pullbackClass_eq_of_lift {T : Type u} [Field T] [CharZero T] [Algebra R T]
    (h : IsRightTorsor q π) (p p' : B →ₐ[R] T)
    (x : WithConv (A →ₐ[R] T)) (hx : toConv p' = convolutionMap q x * toConv p)
    {i : I} {c c' : Classes T (n i)}
    (hc : letI : Algebra B A := q.toAlgHom.toAlgebra; PullbackHasClass n π p i c)
    (hc' : letI : Algebra B A := q.toAlgHom.toAlgebra; PullbackHasClass n π p' i c') :
    c = c' := by
  let L := AlgebraicClosure T
  let e : T →ₐ[R] L := scalarInclusion
  obtain ⟨y, hy⟩ := geometricLift n q π h (e.comp p)
  let y₀ := toConv y
  let xL := convolutionScalars e x
  let y₁ := xL * y₀
  have hy₀ : convolutionMap q y₀ = convolutionScalars e (toConv p) :=
    congrArg toConv hy
  have hy₁ : convolutionMap q y₁ = convolutionScalars e (toConv p') := by
    rw [hx, map_mul, map_mul, hy₀]
    rfl
  obtain ⟨b, a, hdeg, hb, hp, ha⟩ := evaluateClass n q π p y hy hc
  obtain ⟨b', a', hdeg', hb', hp', ha'⟩ :=
    evaluateClass n q π p' y₁.ofConv (congrArg ofConv hy₁) hc'
  have hf : y₁ b' / y₀ b ∈ Set.range (algebraMap T L) := by
    apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
    intro σ
    obtain ⟨z, hz⟩ := displacementKernel n q π h (toConv p) y₀ hy₀ σ
    have hz' : convolutionMap π (toConv z) = y₁⁻¹ * act (R := R) σ y₁ := by
      rw [hz, show y₁ = xL * y₀ from rfl, map_mul,
        show act (R := R) σ xL = xL from act_scalarInclusion σ x]
      group
    rw [map_div₀, displacement_eval n π σ y₁ z hz' hdeg',
      displacement_eval n π σ y₀ z hz hdeg]
    apply mul_div_mul_right
    let f := z.toMonoidHom.comp (MonoidAlgebra.of R _)
    exact (f.toHomUnits (coordinateCharacter n i)).isUnit.ne_zero
  obtain ⟨t, ht⟩ := hf
  have ht0 : t ≠ 0 := fun he => (div_ne_zero hb' hb) (by rw [← ht, he, map_zero])
  let v : Tˣ := Units.mk0 t ht0
  have hmul : a * v ^ n i = a' := by
    apply Units.ext
    apply (algebraMap T L).injective
    change algebraMap T L ((a : T) * t ^ n i) = algebraMap T L (a' : T)
    rw [map_mul, map_pow, ht, div_pow, ← hp, ← hp', mul_comm]
    exact div_mul_cancel₀ _ (pow_ne_zero _ hb)
  rw [← ha, ← ha']
  exact (QuotientGroup.mk'_eq_mk' _).mpr ⟨v ^ n i, ⟨v, rfl⟩, hmul⟩

/-- Equal coordinates of two fibres give a lift of the difference over the same field. -/
theorem lift_of_samePullbackClasses {T : Type u} [Field T] [CharZero T] [Algebra R T]
    [Fintype I] (h : IsRightTorsor q π) (p p' : B →ₐ[R] T)
    (hc : letI : Algebra B A := q.toAlgHom.toAlgebra
      ∀ i, ∃ c, PullbackHasClass n π p i c ∧ PullbackHasClass n π p' i c) :
    ∃ x : WithConv (A →ₐ[R] T), convolutionMap q x = toConv p' * (toConv p)⁻¹ := by
  classical
  let L := AlgebraicClosure T
  let e : T →ₐ[R] L := scalarInclusion
  obtain ⟨y, hy⟩ := geometricLift n q π h (e.comp p)
  obtain ⟨y', hy'⟩ := geometricLift n q π h (e.comp p')
  let x := toConv y
  let x' := toConv y'
  have hx : convolutionMap q x = convolutionScalars e (toConv p) := congrArg toConv hy
  have hx' : convolutionMap q x' = convolutionScalars e (toConv p') := congrArg toConv hy'
  choose c hc hc' using hc
  choose b a hd hb hp ha using fun i => evaluateClass n q π p y hy (hc i)
  choose b' a' hd' hb' hp' ha' using fun i => evaluateClass n q π p' y' hy' (hc' i)
  have hclass (i : I) : classOf (n i) (a i) = classOf (n i) (a' i) :=
    (ha i).trans (ha' i).symm
  have hw (i : I) : ∃ t : Tˣ, a i * t ^ n i = a' i := by
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := (QuotientGroup.mk'_eq_mk' _).mp (hclass i)
    exact ⟨t, ht⟩
  choose t ht using hw
  let value (i : I) : L := y' (b' i) / (y (b i) * e (t i : T))
  have hdenom (i : I) : y (b i) * e (t i : T) ≠ 0 :=
    mul_ne_zero (hb i) ((t i).isUnit.map e).ne_zero
  have hvalue (i : I) : value i ≠ 0 := div_ne_zero (hb' i) (hdenom i)
  have hroot (i : I) : value i ^ n i = 1 := by
    change (y' (b' i) / (y (b i) * e (t i : T))) ^ n i = 1
    rw [div_pow, mul_pow, hp i, hp' i, ← map_pow]
    change e (a' i : T) / (e (a i : T) * e ((t i : T) ^ n i)) = 1
    rw [← map_mul]
    have hti := congrArg (fun w : Tˣ => (w : T)) (ht i)
    change (a i : T) * (t i : T) ^ n i = (a' i : T) at hti
    rw [hti, div_self ((a' i).isUnit.map e).ne_zero]
  let ω (i : I) : rootsOfUnity (n i) L := ⟨Units.mk0 (value i) (hvalue i), by
    apply Units.ext
    exact hroot i⟩
  let z := ((kernelRootCoordinates (R := R) (L := L) n).symm ω).ofConv
  have hz (i : I) : z (MonoidAlgebra.of R _ (coordinateCharacter n i)) = value i := by
    rw [← kernelRootCoordinates_apply]
    exact congrArg (fun r : ∀ i, rootsOfUnity (n i) L => ((r i).val : L))
      ((kernelRootCoordinates (R := R) (L := L) n).apply_symm_apply ω)
  let x₀ := x * convolutionMap π (toConv z)
  have hx₀ : convolutionMap q x₀ = convolutionScalars e (toConv p) := by
    rw [map_mul, hx, (convolutionKernel n q π h _).mpr ⟨z, rfl⟩, mul_one]
  have hev (i : I) : x₀ (b i) * e (t i : T) = x' (b' i) := by
    change (x * convolutionMap π (toConv z)) (b i) * e (t i : T) = x' (b' i)
    rw [evaluation_translate n π (hd i), hz i, mul_right_comm]
    change (y (b i) * e (t i : T)) * (y' (b' i) / (y (b i) * e (t i : T))) = y' (b' i)
    exact mul_div_cancel₀ _ (hdenom i)
  have hfixed (σ : Gal(L/T)) : act (R := R) σ (x' * x₀⁻¹) = x' * x₀⁻¹ := by
    obtain ⟨u, hu⟩ := displacementKernel n q π h (toConv p) x₀ hx₀ σ
    obtain ⟨v, hv⟩ := displacementKernel n q π h (toConv p') x' hx' σ
    have hsame (i : I) : u (MonoidAlgebra.of R _ (coordinateCharacter n i)) =
        v (MonoidAlgebra.of R _ (coordinateCharacter n i)) := by
      have hσ := congrArg σ (hev i)
      rw [map_mul, show σ (e (t i : T)) = e (t i : T) from σ.commutes _,
        displacement_eval n π σ x₀ u hu (hd i), displacement_eval n π σ x' v hv (hd' i),
        mul_right_comm, hev i] at hσ
      exact mul_left_cancel₀ (hb' i) hσ
    have huv : u = v := by
      apply toConv_injective (A := KernelCoordinates R n →ₐ[R] L)
      apply (kernelRootCoordinates (R := R) (L := L) n).injective
      funext i
      apply Subtype.ext
      apply Units.ext
      rw [kernelRootCoordinates_apply, kernelRootCoordinates_apply]
      exact hsame i
    have hprod : act (R := R) σ x' = x' * (x₀⁻¹ * act (R := R) σ x₀) := by
      rw [← hu, huv, hv, mul_inv_cancel_left]
    rw [map_mul, map_inv, hprod]
    group
  obtain ⟨a, ha⟩ := descendConvolution (R := R) _ hfixed
  refine ⟨a, ?_⟩
  have hinj : Function.Injective (convolutionScalars (A := B) e) := by
    intro a b he
    apply ofConv_injective
    ext x
    exact e.injective (congrArg (fun c : WithConv (B →ₐ[R] L) => c x) he)
  apply hinj
  have hnaturality : convolutionScalars e (convolutionMap q a) =
      convolutionMap q (convolutionScalars e a) := rfl
  rw [hnaturality, ha, map_mul, map_inv, hx₀, hx', map_mul, map_inv]

end KummerPoints

section ModelPoints

open CategoryTheory.Limits Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Specs.IntegralCentralQuotient (OverBase fibreGroup HopfSpectrum spectrumOfHopfHom spectrumOfAlgHom)
open Specs.CentralCover (matrixCoordinates matrixCoordinateMap matrixScheme MatrixEmbedding)
open Arithmetic.CentralCover (matrixCoordinateMap_algebraMap)
open Specs.StandardGroups (GLCoordinates)

variable {R E L : Type u} [CommRing R] [Field E] [CommRing L] [Algebra R E] [Algebra E L]
  [Algebra R L] [IsScalarTower R E L]

private abbrev scalarSpec : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R E))

private abbrev baseTest (R L : Type u) [CommRing R] [CommRing L] [Algebra R L] :
    OverBase R := (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R L))

private def projectPoint {X : OverBase R}
    (x : baseTest E L ⟶ (Over.pullback (scalarSpec (R := R) (E := E))).obj X) :
    baseTest R L ⟶ X :=
  Over.homMk (x.left ≫ pullback.fst X.hom scalarSpec) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (x.left ≫ ((Over.pullback (scalarSpec (R := R) (E := E))).obj X).hom) ≫
      scalarSpec = _
    rw [Over.w x]
    change Spec.map (CommRingCat.ofHom (algebraMap E L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R E)) = Spec.map (CommRingCat.ofHom (algebraMap R L))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq R E L])

private theorem projectPoint_bijective (X : OverBase R) :
    Function.Bijective (projectPoint (E := E) (L := L) (X := X)) := by
  constructor
  · intro x y h
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congrArg Over.Hom.left h
    · exact (Over.w x).trans (Over.w y).symm
  · intro x
    have h : x.left ≫ X.hom = (baseTest E L).hom ≫ scalarSpec := by
      rw [Over.w x]
      change Spec.map (CommRingCat.ofHom (algebraMap R L)) =
        Spec.map (CommRingCat.ofHom (algebraMap E L)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R E))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq R E L]
    refine ⟨Over.homMk (pullback.lift x.left (baseTest E L).hom h) (pullback.lift_snd ..), ?_⟩
    exact Over.OverMorphism.ext (pullback.lift_fst ..)

private theorem projectPoint_comp {X Y : OverBase R} (f : X ⟶ Y)
    (x : baseTest E L ⟶ (Over.pullback (scalarSpec (R := R) (E := E))).obj X) :
    projectPoint (x ≫ (Over.pullback scalarSpec).map f) = projectPoint x ≫ f := by
  apply Over.OverMorphism.ext
  simp only [projectPoint, Over.homMk_left, Over.comp_left, Category.assoc, Over.pullback_map_left,
    pullback.lift_fst]

private def modelPointEquiv (H : Grp (OverBase R)) :
    (baseTest E L ⟶ ((fibreGroup E).obj H).X) ≃* (baseTest R L ⟶ H.X) where
  toEquiv := Equiv.ofBijective _ (projectPoint_bijective H.X)
  map_mul' p q := by
    let F := Over.pullback (scalarSpec (R := R) (E := E))
    let p' : baseTest E L ⟶ F.obj H.X := p
    let q' : baseTest E L ⟶ F.obj H.X := q
    let t := lift p' q' ≫ Functor.LaxMonoidal.μ F H.X H.X
    have h : projectPoint t = lift (projectPoint p) (projectPoint q) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [← projectPoint_comp, lift_fst]
        change projectPoint ((lift p' q' ≫ Functor.LaxMonoidal.μ F H.X H.X) ≫ F.map (fst H.X H.X)) = _
        rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
      · rw [← projectPoint_comp, lift_snd]
        change projectPoint ((lift p' q' ≫ Functor.LaxMonoidal.μ F H.X H.X) ≫ F.map (snd H.X H.X)) = _
        rw [Category.assoc, Functor.Monoidal.μ_snd, lift_snd]
    change projectPoint (lift p' q' ≫ (Functor.LaxMonoidal.μ F H.X H.X ≫ F.map μ[H.X])) =
      lift (projectPoint p) (projectPoint q) ≫ μ[H.X]
    rw [← Category.assoc, projectPoint_comp]
    change projectPoint t ≫ μ[H.X] = _
    rw [h]

private def modelCoordinates {A : Type u} [CommRing A] [HopfAlgebra R A]
    {H : Grp (OverBase R)} {G : GroupScheme E} (m : (fibreGroup E).obj H ≅ G)
    (a : HopfSpectrum R A ≅ H) :
    ((groupPointsFunctor E).obj G).obj (CommAlgCat.of E L) ≃* WithConv (A →ₐ[R] L) :=
  (((groupPointsFunctor E).mapIso m.symm).app _).groupIsoToMulEquiv.trans
    ((modelPointEquiv H).trans
      (((yonedaGrp.mapIso a.symm).app (op (baseTest R L))).groupIsoToMulEquiv.trans
        (Spec.mapMulEquiv (R := R) (S := A) (T := L)).symm))

variable {A B : Type u} [CommRing A] [CommRing B] [HopfAlgebra R A] [HopfAlgebra R B]
variable {H J : Grp (OverBase R)} {G Q : GroupScheme E}

private theorem modelCoordinates_spec (m : (fibreGroup E).obj H ≅ G)
    (a : HopfSpectrum R A ≅ H) (x : ((groupPointsFunctor E).obj G).obj (CommAlgCat.of E L)) :
    spectrumOfAlgHom (modelCoordinates (R := R) (L := L) m a x).ofConv =
      projectPoint (x ≫ m.inv.hom.hom) ≫ a.inv.hom.hom := by
  exact (Spec.mapMulEquiv (R := R) (S := A) (T := L)).apply_symm_apply _

private theorem modelCoordinates_map (m : (fibreGroup E).obj H ≅ G)
    (m' : (fibreGroup E).obj J ≅ Q) (a : HopfSpectrum R A ≅ H) (b : HopfSpectrum R B ≅ J)
    (f : H ⟶ J) (g : G ⟶ Q) (q : B →ₐc[R] A)
    (hGeneric : (fibreGroup E).map f ≫ m'.hom = m.hom ≫ g)
    (hModel : spectrumOfHopfHom q ≫ b.hom = a.hom ≫ f)
    (x : ((groupPointsFunctor E).obj G).obj (CommAlgCat.of E L)) :
    modelCoordinates (R := R) (L := L) m' b (pointMap g L x) =
      convolutionMap q (modelCoordinates m a x) := by
  have hg : g ≫ m'.inv = m.inv ≫ (fibreGroup E).map f := by
    rw [Iso.comp_inv_eq, Category.assoc, hGeneric, Iso.inv_hom_id_assoc]
  have hq : f ≫ b.inv = a.inv ≫ spectrumOfHopfHom q := by
    rw [Iso.comp_inv_eq, Category.assoc, hModel, Iso.inv_hom_id_assoc]
  let F := Grp.forget (OverBase E)
  let F₀ := Grp.forget (OverBase R)
  have hg' := congrArg F.map hg
  have hq' := congrArg F₀.map hq
  simp only [Functor.map_comp] at hg' hq'
  apply (Spec.mapMulEquiv (R := R) (S := B) (T := L)).injective
  change spectrumOfAlgHom (modelCoordinates m' b (pointMap g L x)).ofConv =
    spectrumOfAlgHom ((modelCoordinates m a x).ofConv.comp q.toAlgHom)
  rw [modelCoordinates_spec]
  have hx : pointMap g L x ≫ m'.inv.hom.hom =
      (x ≫ m.inv.hom.hom) ≫ (Over.pullback scalarSpec).map f.hom.hom := by
    change (x ≫ F.map g) ≫ F.map m'.inv = (x ≫ F.map m.inv) ≫ F.map ((fibreGroup E).map f)
    rw [Category.assoc, hg', Category.assoc]
  rw [hx, projectPoint_comp, Category.assoc]
  change projectPoint (x ≫ m.inv.hom.hom) ≫ F₀.map f ≫ F₀.map b.inv = _
  rw [hq', ← Category.assoc]
  change (projectPoint (x ≫ m.inv.hom.hom) ≫ a.inv.hom.hom) ≫ _ = _
  rw [← modelCoordinates_spec m a x]
  change (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom (modelCoordinates m a x).ofConv).op ≫
      (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom q.toAlgHom).op = _
  rw [← Functor.map_comp, ← op_comp]
  rfl

private theorem modelCoordinates_scalars {U : Type u} [CommRing U] [Algebra E U]
    [Algebra R U] [IsScalarTower R E U]
    (m : (fibreGroup E).obj H ≅ G) (a : HopfSpectrum R A ≅ H)
    (f : L →ₐ[E] U) (x : ((groupPointsFunctor E).obj G).obj (CommAlgCat.of E L)) :
    modelCoordinates (R := R) (L := U) m a (changeScalars G f x) =
      convolutionScalars (f.restrictScalars R) (modelCoordinates m a x) := by
  apply (Spec.mapMulEquiv (R := R) (S := A) (T := U)).injective
  change spectrumOfAlgHom (modelCoordinates m a (changeScalars G f x)).ofConv =
    spectrumOfAlgHom ((f.restrictScalars R).comp (modelCoordinates m a x).ofConv)
  rw [modelCoordinates_spec]
  apply Over.OverMorphism.ext
  have hx := congrArg Over.Hom.left (modelCoordinates_spec m a x)
  change Spec.map (CommRingCat.ofHom (modelCoordinates m a x).ofConv.toRingHom) =
    _ ≫ _ at hx
  change (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ x.left ≫
      m.inv.hom.hom.left) ≫ pullback.fst H.X.hom scalarSpec ≫ a.inv.hom.hom.left = _
  simp only [Category.assoc]
  rw [← show Spec.map (CommRingCat.ofHom (modelCoordinates m a x).ofConv.toRingHom) =
    x.left ≫ m.inv.hom.hom.left ≫ pullback.fst H.X.hom scalarSpec ≫ a.inv.hom.hom.left from by
      simpa only [projectPoint, Over.homMk_left, Category.assoc, Over.comp_left] using hx]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end ModelPoints

section MatrixPoints

open CategoryTheory.Limits Opposite
open Specs.CentralCover (matrixCoordinates matrixCoordinateMap matrixDeterminant matrixScheme MatrixEmbedding)
open Specs.StandardGroups (GLCoordinates)
open Specs.Unipotent (Index)
open Arithmetic.CentralCover (matrixCoordinateMap_algebraMap)
open private affineGroupIsoOfPoints affineGroupIsoOfPoints_map
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
open private glEvaluation glEvaluation_entry from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups

variable {k : Type u} [Field k] {Q : AffineAlgebraicGroup k}

private def matrixEmbedding (i : MatrixRealization Q) : MatrixEmbedding Q i.size := by
  let L := StandardGroups.generalLinearGroup k (Index.{u} i.size)
  let e : i.ambient.val ≅ L.val :=
    affineGroupIsoOfPoints i.ambient.property.1 L.property.1
      (i.matrix ≪≫ (StandardGroups.generalLinearGroupPointsIso k (Index.{u} i.size)).symm)
  refine ⟨i.embedding.hom.hom ≫ e.hom.hom.hom, ?_⟩
  letI := i.closed
  letI : IsIso e.hom.hom.hom.left := ((Grp.forget _) ⋙ Over.forget _).map_isIso e.hom
  change IsClosedImmersion (i.embedding.hom.hom.left ≫ e.hom.hom.hom.left)
  infer_instance

private theorem matrixEmbedding_onPoints (i : MatrixRealization Q) {T : Type u}
    [CommRing T] [Algebra k T] (x : PointsIn i T) :
    x.left ≫ (matrixEmbedding i).inclusion.left =
      Spec.map (CommRingCat.ofHom (glEvaluation (asMatrix i T x)).toRingHom) := by
  let L := StandardGroups.generalLinearGroup k (Index.{u} i.size)
  let m := StandardGroups.generalLinearGroupPointsIso k (Index.{u} i.size)
  let e : i.ambient.val ≅ L.val :=
    affineGroupIsoOfPoints i.ambient.property.1 L.property.1 (i.matrix ≪≫ m.symm)
  let y : Points i.ambient.val.X (CommAlgCat.of k T) := x ≫ i.embedding.hom.hom
  have h := congrArg (fun α => α.app (CommAlgCat.of k T) y)
    (affineGroupIsoOfPoints_map i.ambient.property.1 L.property.1 (i.matrix ≪≫ m.symm))
  change y ≫ e.hom.hom.hom = m.inv.app (CommAlgCat.of k T) (asMatrix i T x) at h
  have hg : m.inv.app (CommAlgCat.of k T) (asMatrix i T x) =
      (testSpec k).map (CommAlgCat.ofHom (glEvaluation (asMatrix i T x))).op := rfl
  have hh := congrArg Over.Hom.left (h.trans hg)
  rw [algSpec_map_left] at hh
  change x.left ≫ (i.embedding.hom.hom ≫ e.hom.hom.hom).left = _
  rw [Over.comp_left, ← Category.assoc]
  exact hh

variable {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]

/-- Evaluation of determinant-localized matrix coordinates over any coefficient ring. -/
private def evaluateMatrix (a : R →+* T) {m : ℕ} (M : Matrix.GeneralLinearGroup (Index.{u} m) T) :
    matrixCoordinates R m →+* T := by
  let f := MvPolynomial.eval₂Hom a (fun p : Index.{u} m × Index.{u} m => M.val p.1 p.2)
  have h : f (matrixDeterminant R m) = M.val.det := by
    rw [matrixDeterminant, RingHom.map_det]
    congr 1
    ext i j
    exact MvPolynomial.eval₂Hom_X' a _ _
  have hunit : IsUnit (f (matrixDeterminant R m)) :=
    h.symm ▸ (Matrix.GeneralLinearGroup.det M).isUnit
  exact IsLocalization.Away.lift (S := matrixCoordinates R m) (matrixDeterminant R m) hunit

private theorem evaluateMatrix_entries (a : R →+* T) {m : ℕ}
    (M : Matrix.GeneralLinearGroup (Index.{u} m) T)
    (x : MvPolynomial (Index.{u} m × Index.{u} m) R) :
    evaluateMatrix a M (algebraMap _ _ x) = MvPolynomial.eval₂Hom a (fun p : Index.{u} m × Index.{u} m => M.val p.1 p.2) x := by
  unfold evaluateMatrix
  apply IsLocalization.Away.lift_eq

private theorem evaluateMatrix_algebraMap (a : R →+* T) {m : ℕ}
    (M : Matrix.GeneralLinearGroup (Index.{u} m) T) (r : R) :
    evaluateMatrix a M (algebraMap R (matrixCoordinates R m) r) = a r := by
  rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Index.{u} m × Index.{u} m) R),
    evaluateMatrix_entries]
  exact MvPolynomial.eval₂Hom_C _ _ _

private theorem evaluateMatrix_scalars (a : R →+* T) (b : T →+* U)
    {m : ℕ} (M : Matrix.GeneralLinearGroup (Index.{u} m) T) :
    b.comp (evaluateMatrix a M) = evaluateMatrix (b.comp a) (Matrix.GeneralLinearGroup.map b M) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (matrixDeterminant R m))
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [evaluateMatrix_entries]
  · intro i
    simp [evaluateMatrix_entries]

private theorem evaluateMatrix_restrict [Algebra R S] (a : S →+* T)
    {m : ℕ} (M : Matrix.GeneralLinearGroup (Index.{u} m) T) :
    (evaluateMatrix a M).comp (matrixCoordinateMap R S m) =
      evaluateMatrix (a.comp (algebraMap R S)) M := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (matrixDeterminant R m))
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [matrixCoordinateMap_algebraMap, evaluateMatrix_entries]
  · intro i
    simp [matrixCoordinateMap_algebraMap, evaluateMatrix_entries]

private theorem evaluateMatrix_eq_glEvaluation {k : Type u} [Field k] [Algebra k T]
    {m : ℕ} (M : Matrix.GeneralLinearGroup (Index.{u} m) T) :
    evaluateMatrix (algebraMap k T) M = (glEvaluation (k := k) M).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (matrixDeterminant k m))
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, evaluateMatrix_entries, MvPolynomial.eval₂Hom_C]
    exact ((glEvaluation (k := k) M).commutes r).symm
  · rintro ⟨i, j⟩
    simp only [RingHom.comp_apply, evaluateMatrix_entries, MvPolynomial.eval₂Hom_X']
    exact (glEvaluation_entry (k := k) M i j).symm

open Specs.IntegralCentralQuotient (OverBase spectrumOfAlgHom)

private def affineCoordinateMap {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (f : baseTest R A ⟶ baseTest R B) : B →ₐ[R] A :=
  ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage f).unop.hom

private theorem affineCoordinateMap_spec {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (f : baseTest R A ⟶ baseTest R B) :
    spectrumOfAlgHom (affineCoordinateMap f) = f :=
  (algSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage f

private theorem scalarExtensionMatrix_onPoints {E L : Type u} [Field E] [Algebra k E] [CommRing L]
    [Algebra E L] (i : MatrixRealization Q)
    (j : MatrixEmbedding (Specs.Unipotent.baseChangedAlgebraicGroup E Q) i.size)
    (hj : j.inclusion.left ≫ Spec.map (CommRingCat.ofHom (matrixCoordinateMap k E i.size)) =
      pullback.fst Q.val.X.hom (fieldSpecMap k E) ≫ (matrixEmbedding i).inclusion.left)
    (p : Points ((groupBaseChange k E).obj Q.val).X (CommAlgCat.of E L)) :
    letI : Algebra k L := ((algebraMap E L).comp (algebraMap k E)).toAlgebra
    p.left ≫ j.inclusion.left =
      Spec.map (CommRingCat.ofHom (evaluateMatrix (algebraMap E L)
        (asMatrix i L (baseChangePoint k E Q.val.X (CommAlgCat.of E L) p)))) := by
  letI : Algebra k L := ((algebraMap E L).comp (algebraMap k E)).toAlgebra
  let a := affineCoordinateMap (p ≫ j.inclusion)
  let x := baseChangePoint k E Q.val.X (CommAlgCat.of E L) p
  let M := asMatrix i L x
  have hSpec : Spec.map (CommRingCat.ofHom a.toRingHom) = p.left ≫ j.inclusion.left :=
    congrArg Over.Hom.left (affineCoordinateMap_spec (p ≫ j.inclusion))
  have hk : a.toRingHom.comp (matrixCoordinateMap k E i.size) = evaluateMatrix (algebraMap k L) M := by
    apply_fun CommRingCat.ofHom
    · apply Spec.map_injective
      rw [CommRingCat.ofHom_comp, Spec.map_comp, hSpec, Category.assoc, hj, ← Category.assoc]
      change x.left ≫ (matrixEmbedding i).inclusion.left = _
      rw [matrixEmbedding_onPoints, evaluateMatrix_eq_glEvaluation]
    · intro f g h
      exact congrArg CommRingCat.Hom.hom h
  have he : a.toRingHom = evaluateMatrix (algebraMap E L) M := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (matrixDeterminant E i.size))
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, evaluateMatrix_entries, MvPolynomial.eval₂Hom_C]
      exact a.commutes r
    · intro ij
      have h := DFunLike.congr_fun hk
        (algebraMap (MvPolynomial (Index.{u} i.size × Index.{u} i.size) k)
          (matrixCoordinates k i.size) (MvPolynomial.X ij))
      simpa only [RingHom.comp_apply, matrixCoordinateMap_algebraMap, MvPolynomial.map_X,
        evaluateMatrix_entries, MvPolynomial.eval₂Hom_X'] using h
  rw [← hSpec, he]

open Specs.CentralCover (IntegralModel SplitCoverData)
open Specs.IntegralCentralQuotient (HopfSpectrum)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open private specMap_surjective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels

private theorem model_integralPoint {E V L : Type u} [Field E] [CommRing V] [CommRing L]
    [Algebra k E] [Algebra E L] [Algebra R E] [Algebra R L] [IsScalarTower R E L] [Algebra R V]
    {G : AffineAlgebraicGroup E} {q : G.val ⟶ (baseChangedAlgebraicGroup E Q).val}
    {N : ClosedSubgroup G.val} {T : SplitCoverData (baseChangedAlgebraicGroup E Q) G q N}
    (i : MatrixRealization Q) (j : MatrixEmbedding (baseChangedAlgebraicGroup E Q) i.size)
    (hj : j.inclusion.left ≫ Spec.map (CommRingCat.ofHom (matrixCoordinateMap k E i.size)) =
      pullback.fst Q.val.X.hom (fieldSpecMap k E) ≫ (matrixEmbedding i).inclusion.left)
    (M : IntegralModel (R := R) T j)
    {B : Type u} [CommRing B] [HopfAlgebra R B] (e : HopfSpectrum R B ≅ M.target.val)
    (x : Points (baseChangedAlgebraicGroup E Q).val.X (CommAlgCat.of E L))
    (ι : V →ₐ[R] L) (hι : Function.Injective ι)
    (y : Matrix.GeneralLinearGroup (Index.{u} i.size) V)
    (hy : letI : Algebra k L := ((algebraMap E L).comp (algebraMap k E)).toAlgebra
      Matrix.GeneralLinearGroup.map ι.toRingHom y =
        asMatrix i L (baseChangePoint k E Q.val.X (CommAlgCat.of E L) x)) :
    ∃ p₀ : B →ₐ[R] V, ι.comp p₀ = (modelCoordinates M.genericTarget e x).ofConv := by
  let j₀ := affineCoordinateMap (e.hom.hom.hom ≫ M.matrixInclusion)
  let p := (modelCoordinates M.genericTarget e x).ofConv
  have j₀_spec := congrArg Over.Hom.left (affineCoordinateMap_spec
    (e.hom.hom.hom ≫ M.matrixInclusion))
  have hj₀ : Function.Surjective j₀ := by
    apply specMap_surjective (CommRingCat.ofHom j₀.toRingHom)
    have hi : IsIso e.hom.hom.hom.left := ((Grp.forget _) ⋙ Over.forget _).map_isIso e.hom
    have hc : IsClosedImmersion M.matrixInclusion.left := M.matrixClosed
    change IsClosedImmersion (Spec.map (CommRingCat.ofHom j₀.toRingHom))
    rw [show Spec.map (CommRingCat.ofHom j₀.toRingHom) =
        e.hom.hom.hom.left ≫ M.matrixInclusion.left from j₀_spec]
    infer_instance
  let P₀ : matrixCoordinates R i.size →ₐ[R] V :=
    { evaluateMatrix (algebraMap R V) y with
      commutes' := evaluateMatrix_algebraMap (algebraMap R V) y }
  apply Kummer.closedModelPointLift j₀ hj₀ ι hι p P₀
  apply AlgHom.toRingHom_injective
  have hinj : Function.Injective (fun f : matrixCoordinates R i.size →+* L => CommRingCat.ofHom f) :=
    fun _ _ h => congrArg CommRingCat.Hom.hom h
  apply hinj
  apply Spec.map_injective
  change Spec.map (CommRingCat.ofHom (p.toRingHom.comp j₀.toRingHom)) =
    Spec.map (CommRingCat.ofHom (ι.toRingHom.comp P₀.toRingHom))
  have hp := congrArg Over.Hom.left (modelCoordinates_spec M.genericTarget e x)
  change Spec.map (CommRingCat.ofHom p.toRingHom) =
    (projectPoint (x ≫ M.genericTarget.inv.hom.hom)).left ≫ e.inv.hom.hom.left at hp
  rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, hp,
    show Spec.map (CommRingCat.ofHom j₀.toRingHom) =
      e.hom.hom.hom.left ≫ M.matrixInclusion.left from j₀_spec]
  have hcancel : e.inv.hom.hom.left ≫ e.hom.hom.hom.left = 𝟙 M.target.val.X.left :=
    ((Grp.forget _) ⋙ Over.forget _).congr_map e.inv_hom_id
  rw [Category.assoc, ← Category.assoc e.inv.hom.hom.left, hcancel, Category.id_comp]
  change (x.left ≫ M.genericTarget.inv.hom.hom.left ≫
      pullback.fst M.target.val.X.hom scalarSpec) ≫ M.matrixInclusion.left = _
  simp only [Category.assoc]
  rw [← M.genericMatrix]
  have hcancel' : M.genericTarget.inv.hom.hom.left ≫ M.genericTarget.hom.hom.hom.left =
      𝟙 (baseChangedAlgebraicGroup E Q).val.X.left :=
    ((Grp.forget _) ⋙ Over.forget _).congr_map M.genericTarget.inv_hom_id
  rw [← Category.assoc M.genericTarget.inv.hom.hom.left, hcancel', Category.id_comp,
    ← Category.assoc, scalarExtensionMatrix_onPoints i j hj x, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, evaluateMatrix_restrict, ← hy, ← IsScalarTower.algebraMap_eq,
    ← show ι.toRingHom.comp (algebraMap R V) = algebraMap R L from ι.comp_algebraMap,
    ← evaluateMatrix_scalars]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

end MatrixPoints

section LocalClasses

open WithConv
open Specs.CentralCover (integersOutside)
open Specs.CentralCoverSpreading (KernelCoordinates)
open Specs.IntegralCentralQuotient (IsRightTorsor)
open Kummer

variable {E : Type u} [Field E]
variable (D : GlobalFieldData.{u, v} E) (S : Set D.FinitePlace)
variable {A B : Type u} [CommRing A] [CommRing B]
  [HopfAlgebra (integersOutside D S) A] [HopfAlgebra (integersOutside D S) B]
variable {I : Type} [Finite I] (n : I → ℕ) (q : B →ₐc[integersOutside D S] A)
  (π : A →ₐc[integersOutside D S] KernelCoordinates (integersOutside D S) n)

/-- The extension of a coordinate point to one completed field. -/
private def completedCoordinate (w : D.FinitePlace) (p : B →ₐ[integersOutside D S] E) :
    let R := ↥(integersOutside D S)
    letI : Algebra R (D.FiniteCompletion w) :=
      ((D.embedding (.inl w)).comp (algebraMap R E)).toAlgebra
    B →ₐ[R] D.FiniteCompletion w := by
  letI : Algebra (integersOutside D S) (D.FiniteCompletion w) :=
    ((D.embedding (.inl w)).comp (algebraMap (integersOutside D S) E)).toAlgebra
  exact { (D.embedding (.inl w)).comp p.toRingHom with
    commutes' := fun r => congrArg (D.embedding (.inl w)) (p.commutes r) }

set_option maxHeartbeats 1300000 in
/-- Kummer classes of points locally differing from integral points by lifts
take only finitely many values. -/
theorem finiteClasses_of_localLifts
    (hS : S.Finite) (hn : ∀ i, 0 < n i) (h : IsRightTorsor q π)
    (coord : let R := ↥(integersOutside D S)
      letI : Algebra B A := q.toAlgHom.toAlgebra
      ∀ {T : Type u} [CommRing T] [Algebra R T] [IsLocalRing T] (p : B →ₐ[R] T) (i : I),
        ∃! c, PullbackHasClass n π p i c)
    {X : Type u} (p : X → B →ₐ[integersOutside D S] E)
    (classes : X → (i : I) → Classes E (n i))
    (hp : letI : Algebra B A := q.toAlgHom.toAlgebra
      ∀ x i, PullbackHasClass n π (p x) i (classes x i))
    (hzero : ∀ w : D.FinitePlace, CharZero (D.FiniteCompletion w))
    (hlocal : ∀ x (w : D.FinitePlace) (hw : w ∉ S),
      let R := ↥(integersOutside D S)
      letI : Algebra R (D.integers w) := (integersOutsideToLocal D S w hw).toAlgebra
      letI : Algebra R (D.FiniteCompletion w) :=
        ((D.embedding (.inl w)).comp (algebraMap R E)).toAlgebra
      ∃ (p₀ : B →ₐ[R] D.integers w) (p₁ : B →ₐ[R] D.FiniteCompletion w)
        (x₁ : WithConv (A →ₐ[R] D.FiniteCompletion w)),
        (D.integers w).subtype.comp p₀.toRingHom = p₁.toRingHom ∧
        toConv p₁ = convolutionMap q x₁ * toConv (completedCoordinate D S w (p x))) :
    (Set.range classes).Finite := by
  let R := ↥(integersOutside D S)
  letI : Algebra B A := q.toAlgHom.toAlgebra
  apply finiteIntegralCoordinates D (Sum.inl '' S) (hS.image _) n hn classes
  intro x i w hw
  have hw' : w ∉ S := fun hw₀ => hw ⟨w, hw₀, rfl⟩
  letI : Algebra R (D.integers w) := (integersOutsideToLocal D S w hw').toAlgebra
  letI : Algebra R (D.FiniteCompletion w) :=
    ((D.embedding (.inl w)).comp (algebraMap R E)).toAlgebra
  letI : CharZero (D.FiniteCompletion w) := hzero w
  obtain ⟨p₀, p₁, x₁, he, hl⟩ := hlocal x w hw'
  obtain ⟨c, hc⟩ := (coord p₀ i).exists
  have hc₀ := pullbackClassNaturality n π p₀ p₁ (D.integers w).subtype he i c hc
  have hc₁ := pullbackClassNaturality n π (p x) (completedCoordinate D S w (p x))
    (D.embedding (.inl w)) rfl i (classes x i) (hp x i)
  exact ⟨c, (pullbackClass_eq_of_lift n q π h _ _ x₁ hl hc₁ hc₀).symm⟩

end LocalClasses

section Assembly

open NumberField IsDedekindDomain
open CategoryTheory.Limits Opposite WithConv
open scoped CategoryTheory.MonObj
open Specs.CentralIsogenies (IsCentralIsogeny)
open Specs.Unipotent (baseChangedAlgebraicGroup)

private theorem below_finite_preimage {K E : Type u} [Field K] [Field E]
    [NumberField K] [NumberField E] [Algebra K E]
    {S : Set (NumberFinitePlace K)} (hS : S.Finite) :
    ((below (K := K) (E := E)) ⁻¹' S).Finite := by
  apply hS.preimage'
  intro v hv
  have he : Set.InjOn (fun w : NumberFinitePlace E => w.asIdeal) (below ⁻¹' {v}) :=
    fun _ _ _ _ h => HeightOneSpectrum.ext h
  refine Set.Finite.of_finite_image ?_ he
  letI : v.asIdeal.IsMaximal := v.isMaximal
  apply (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).subset
  rintro _ ⟨w, hw, rfl⟩
  have hv' : below w = v := hw
  exact ⟨w.isPrime, hv' ▸ liesOver_below w⟩

private theorem changeScalars_comp {K A B C : Type u} [Field K]
    [CommRing A] [CommRing B] [CommRing C] [Algebra K A] [Algebra K B] [Algebra K C]
    (H : GroupScheme K) (f : A →ₐ[K] B) (g : B →ₐ[K] C)
    (x : ((groupPointsFunctor K).obj H).obj (CommAlgCat.of K A)) :
    changeScalars H g (changeScalars H f x) = changeScalars H (g.comp f) x := by
  exact (ConcreteCategory.congr_hom (((groupPointsFunctor K).obj H).map_comp
    (CommAlgCat.ofHom f) (CommAlgCat.ofHom g)) x).symm

private theorem baseChangeEquiv_map {K E L : Type u} [Field K] [Field E] [Algebra K E]
    [CommRing L] [Algebra E L] {G Q : GroupScheme K} (q : G ⟶ Q)
    (x : ((groupPointsFunctor E).obj ((groupBaseChange K E).obj G)).obj (CommAlgCat.of E L)) :
    letI : Algebra K L := ((algebraMap E L).comp (algebraMap K E)).toAlgebra
    baseChangePointGroupEquiv E Q (CommAlgCat.of E L) (pointMap ((groupBaseChange K E).map q) L x) =
      pointMap q L (baseChangePointGroupEquiv E G (CommAlgCat.of E L) x) :=
  baseChangePointsSchemeNaturality K E q.hom.hom _ x

private theorem baseChangeEquiv_scalars {K E L L' : Type u} [Field K] [Field E] [Algebra K E]
    [CommRing L] [CommRing L'] [Algebra E L] [Algebra E L']
    (G : GroupScheme K) (f : L →ₐ[E] L')
    (x : ((groupPointsFunctor E).obj ((groupBaseChange K E).obj G)).obj (CommAlgCat.of E L)) :
    letI : Algebra K L := ((algebraMap E L).comp (algebraMap K E)).toAlgebra
    letI : Algebra K L' := ((algebraMap E L').comp (algebraMap K E)).toAlgebra
    letI : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower K E L' := IsScalarTower.of_algebraMap_eq' rfl
    baseChangePointGroupEquiv E G (CommAlgCat.of E L')
      (changeScalars ((groupBaseChange K E).obj G) f x) =
      changeScalars G (f.restrictScalars K) (baseChangePointGroupEquiv E G (CommAlgCat.of E L) x) :=
  baseChangePointsNaturality K E G.X (CommAlgCat.ofHom f) x

private theorem finiteRationalCosets_of_extension {K E : Type u} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] {G Q : AffineAlgebraicGroup K}
    (q : G.val ⟶ Q.val) (hq : IsCentralIsogeny q)
    {X Y : Type*} (d : X → RationalPoints Q) (c : X → Y) (hc : (Set.range c).Finite)
    (hlift : ∀ x y, c x = c y → ∃ z,
      pointMap q E z = changeScalars Q.val (Algebra.ofId K E) (d x * (d y)⁻¹)) :
    ∃ F : Finset (RationalPoints Q), ∀ x, ∃ r ∈ F, ∃ g : RationalPoints G,
      d x = pointMap q K g * r := by
  letI := hc.to_subtype
  let t (x : X) : Set.range c := ⟨c x, ⟨x, rfl⟩⟩
  letI := finitePointKernel q hq E
  refine finiteCosets_of_finiteDisplacements (pointMap q K) (changeScalars G.val (Algebra.ofId K E))
    (changeScalars Q.val (Algebra.ofId K E)) (pointMap q E) d t
    (fun σ : Gal(E/K) => changeScalars G.val σ.toAlgHom)
    (fun σ => changeScalars Q.val σ.toAlgHom)
    (changeScalars_pointMap _ q) (changeScalars_injective _ Q)
    (fun σ => changeScalars_pointMap σ.toAlgHom q) ?_ (fun z hz => descendPoint z hz) ?_
  · intro σ b
    rw [changeScalars_comp]
    have he : σ.toAlgHom.comp (Algebra.ofId K E) = Algebra.ofId K E :=
      AlgHom.ext σ.commutes
    rw [he]
  · intro x y he
    exact hlift x y (congrArg Subtype.val he)

private theorem asMatrix_changeScalars {K L L' : Type u} [Field K]
    [CommRing L] [CommRing L'] [Algebra K L] [Algebra K L'] {G : AffineAlgebraicGroup K}
    (i : MatrixRealization G) (f : L →ₐ[K] L') (x : PointsIn i L) :
    asMatrix i L' (changeScalars G.val f x) =
      Matrix.GeneralLinearGroup.map f.toRingHom (asMatrix i L x) :=
  congrArg (fun a => a x) ((((groupPointsFunctor K).map i.embedding) ≫ i.matrix.hom).naturality
    (CommAlgCat.ofHom f))

variable {K E : Type u} [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]

private abbrev numberData (F : Type u) [Field F] [NumberField F] : GlobalFieldData.{u, v} F :=
  .number inferInstance

private def belowIndex (w : NumberFinitePlace E) : Outside (numberData.{u, v} K) ∅ :=
  ⟨.inl (below (K := K) w), by simp⟩

private def scalarToCompletion (w : NumberFinitePlace E) :
    letI : Algebra K ((below (K := K) w).adicCompletion K) := (algebraMap K _).toAlgebra
    letI : Algebra K (w.adicCompletion E) :=
      ((algebraMap E (w.adicCompletion E)).comp (algebraMap K E)).toAlgebra
    (below (K := K) w).adicCompletion K →ₐ[K] w.adicCompletion E := by
  letI : Algebra K ((below (K := K) w).adicCompletion K) := (algebraMap K _).toAlgebra
  letI : Algebra K (w.adicCompletion E) :=
    ((algebraMap E (w.adicCompletion E)).comp (algebraMap K E)).toAlgebra
  exact { completionMap w with commutes' := completionMap_algebraMap w }

private theorem scalarToCompletion_diagonal (w : NumberFinitePlace E) :
    letI : Algebra K ((below (K := K) w).adicCompletion K) := (algebraMap K _).toAlgebra
    letI : Algebra K (w.adicCompletion E) :=
      ((algebraMap E (w.adicCompletion E)).comp (algebraMap K E)).toAlgebra
    (scalarToCompletion (K := K) w).comp (Algebra.ofId K _) = Algebra.ofId K _ := by
  letI : Algebra K ((below (K := K) w).adicCompletion K) := (algebraMap K _).toAlgebra
  letI : Algebra K (w.adicCompletion E) :=
    ((algebraMap E (w.adicCompletion E)).comp (algebraMap K E)).toAlgebra
  exact AlgHom.ext (completionMap_algebraMap w)

open Specs.CentralCover (integersOutside)
open Kummer

private abbrev eligiblePoints {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    {G Q : AffineAlgebraicGroup K} (q : G.val ⟶ Q.val) (j : MatrixRealization Q)
    (C : Set (Adeles D j ∅)) :=
  {d : RationalPoints Q // ∃ c ∈ C, ∀ w : Outside D ∅,
    ∃ x : ((groupPointsFunctor K).obj G.val).obj (CommAlgCat.of K (D.Completion w.1)),
      c w = (show LocalPoints D j w.1 from pointMap q (D.Completion w.1) x) * localPoint D j w.1 d}

set_option maxHeartbeats 3000000 in
theorem finiteRationalCosets : FiniteRationalCosets.{u, v} := by
  classical
  intro K _ hK G Q hG hQ q hq j
  unfold FiniteCosetsFor
  intro C hC
  let D := numberData.{u, v} K
  obtain ⟨U, hU⟩ := compact_integralOutside D j hC
  obtain ⟨E, _, _, _, _, N, hq', hN, ⟨T⟩⟩ := splitIsogeny q hG hQ hq
  letI : NumberField E := NumberField.of_module_finite K E
  let DE := numberData.{u, v} E
  let G' := baseChangedAlgebraicGroup E G
  let Q' := baseChangedAlgebraicGroup E Q
  let q' : G'.val ⟶ Q'.val := (groupBaseChange K E).map q
  obtain ⟨j', hj'⟩ := CentralCover.matrixEmbeddingScalarExtension (E := E) (matrixEmbedding j)
  let S₀ : Set (NumberFinitePlace K) :=
    (fun w => (⟨.inl w, by simp⟩ : Outside D ∅)) ⁻¹' (U : Set (Outside D ∅))
  have hS₀ : S₀.Finite := U.finite_toSet.preimage fun x _ y _ h =>
    Sum.inl.inj (congrArg Subtype.val h)
  let B₀ : Set DE.FinitePlace := (below (K := K) (E := E)) ⁻¹' S₀
  obtain ⟨S, hS, hBS, ⟨M⟩⟩ :=
    CentralCover.integralModels DE B₀ (below_finite_preimage hS₀) Q' G' q' N hq' hN T j'
  let R := ↥(integersOutside DE S)
  letI := T.finiteIndices
  obtain ⟨B, A, _, _, _, _, eQ, eG, q₀, π, hq₀, hπ, ht, hcoord, cls, hcls, _⟩ :=
    coverPullbackFiniteness DE S hS T.exponents T.positiveExponents M.map M.kernelInclusion
      M.target.property.1 M.source.property.1 M.torsor M.splitKernel
  let X := eligiblePoints D q j C
  let e (H : GroupScheme K) (L : Type u) [CommRing L] [Algebra E L] :=
    baseChangePointGroupEquiv E H (CommAlgCat.of E L)
  let dE (d : X) : RationalPoints Q' :=
    (e Q.val E).symm (changeScalars Q.val (Algebra.ofId K E) d.val)
  let p (d : X) : B →ₐ[R] E := (modelCoordinates M.genericTarget eQ (dE d)).ofConv
  have hc : (Set.range (cls ∘ p)).Finite := by
    apply finiteClasses_of_localLifts DE S T.exponents q₀ π hS T.positiveExponents ht hcoord p
      (cls ∘ p) (fun d i => (hcls (p d) i).1)
    · intro w
      change CharZero (w.adicCompletion E)
      exact charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
    · intro d w hw
      let L := w.adicCompletion E
      let V := w.adicCompletionIntegers E
      letI : Algebra R L := ((algebraMap E L).comp (algebraMap R E)).toAlgebra
      letI : IsScalarTower R E L := IsScalarTower.of_algebraMap_eq' rfl
      letI : Algebra R V := (integersOutsideToLocal DE S w hw).toAlgebra
      let iV : V →ₐ[R] L := { (DE.integers w).subtype with commutes' := fun _ => rfl }
      letI : Algebra K L := ((algebraMap E L).comp (algebraMap K E)).toAlgebra
      letI : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' rfl
      letI : Algebra K ((below (K := K) w).adicCompletion K) :=
        (algebraMap K ((below (K := K) w).adicCompletion K)).toAlgebra
      let f := scalarToCompletion (K := K) w
      let u := belowIndex.{u, v} (K := K) w
      obtain ⟨c, hcC, hcx⟩ := d.property
      obtain ⟨aK, haK⟩ := hcx u
      have hu : u ∉ U := fun h => hw (hBS (show w ∈ B₀ from h))
      have hcu : c u ∈ integralPoints D j (below w) := hU c hcC u hu
      obtain ⟨y, hy⟩ := hcu
      let cL : ((groupPointsFunctor E).obj Q'.val).obj (CommAlgCat.of E L) :=
        (e Q.val L).symm (changeScalars Q.val f (c u))
      let aL : ((groupPointsFunctor E).obj G'.val).obj (CommAlgCat.of E L) :=
        (e G.val L).symm (changeScalars G.val f aK)
      let dL : ((groupPointsFunctor E).obj Q'.val).obj (CommAlgCat.of E L) :=
        changeScalars Q'.val (Algebra.ofId E L) (dE d)
      let yL := Matrix.GeneralLinearGroup.map (completionIntegersMap (K := K) w) y
      have hyL : Matrix.GeneralLinearGroup.map iV.toRingHom yL =
          asMatrix j L (baseChangePoint K E Q.val.X (CommAlgCat.of E L) cL) := by
        have hy' : Matrix.GeneralLinearGroup.map ((below (K := K) w).adicCompletionIntegers K).subtype y =
            asMatrix j ((below (K := K) w).adicCompletion K) (c u) := hy
        change Matrix.GeneralLinearGroup.map iV.toRingHom yL = asMatrix j L ((e Q.val L) cL)
        rw [show (e Q.val L) cL = changeScalars Q.val f (c u) from
          (e Q.val L).apply_symm_apply _, asMatrix_changeScalars j f (c u)]
        erw [← hy']
        rfl
      have hcl : cL = pointMap q' L aL * dL := by
        apply (e Q.val L).injective
        rw [map_mul]
        rw [show (e Q.val L) cL = changeScalars Q.val f (c u) from (e Q.val L).apply_symm_apply _]
        have ha : (e Q.val L) (pointMap q' L aL) =
            pointMap q L (changeScalars G.val f aK) :=
          (baseChangeEquiv_map (E := E) q aL).trans
            (congrArg (pointMap q L) ((e G.val L).apply_symm_apply _))
        have hd : (e Q.val L) dL = changeScalars Q.val f (localPoint D j u.1 d.val) := by
          change baseChangePointGroupEquiv E Q.val (CommAlgCat.of E L)
            (changeScalars Q'.val (Algebra.ofId E L) (dE d)) = _
          erw [baseChangeEquiv_scalars Q.val (Algebra.ofId E L) (dE d)]
          change changeScalars Q.val ((Algebra.ofId E L).restrictScalars K) ((e Q.val E) (dE d)) = _
          rw [show (e Q.val E) (dE d) = changeScalars Q.val (Algebra.ofId K E) d.val from
            (e Q.val E).apply_symm_apply _, changeScalars_comp]
          change changeScalars Q.val _ d.val =
            changeScalars Q.val f (changeScalars Q.val (Algebra.ofId K _) d.val)
          erw [changeScalars_comp Q.val (Algebra.ofId K _) f d.val,
            scalarToCompletion_diagonal (K := K) w]
          rfl
        rw [ha, hd]
        erw [changeScalars_pointMap f q aK, ← map_mul (changeScalars Q.val f)]
        exact congrArg (changeScalars Q.val f) haK
      obtain ⟨z, hz⟩ := model_integralPoint j j' hj' M eQ cL iV Subtype.val_injective yL hyL
      let pL := modelCoordinates (R := R) (L := L) M.genericTarget eQ
      let aL' := modelCoordinates (R := R) (L := L) M.genericSource eG aL
      refine ⟨z, (pL cL).ofConv, aL', congrArg AlgHom.toRingHom hz, ?_⟩
      calc
        pL cL = pL (pointMap q' L aL * dL) := congrArg pL hcl
        _ = pL (pointMap q' L aL) * pL dL := map_mul pL _ _
        _ = _ := congrArg₂ (· * ·)
          (modelCoordinates_map M.genericSource M.genericTarget eG eQ M.map q' q₀
            M.genericMap hq₀ aL)
          (modelCoordinates_scalars M.genericTarget eQ (Algebra.ofId E L) (dE d))
  letI : Group (WithConv (B →ₐ[R] E)) := convolutionGroupOverRing
  obtain ⟨F, hF⟩ := finiteRationalCosets_of_extension q hq (E := E) (fun d : X => d.val) (cls ∘ p)
    hc (by
      intro x y hxy
      have he : ∀ i, ∃ c, letI : Algebra B A := q₀.toAlgHom.toAlgebra
          PullbackHasClass T.exponents π (p y) i c ∧ PullbackHasClass T.exponents π (p x) i c := by
        intro i
        refine ⟨cls (p y) i, (hcls (p y) i).1, ?_⟩
        rw [← show cls (p x) i = cls (p y) i from congrFun hxy i]
        exact (hcls (p x) i).1
      obtain ⟨z, hz⟩ := lift_of_samePullbackClasses T.exponents q₀ π ht (p y) (p x) he
      let eG' := modelCoordinates (R := R) (L := E) M.genericSource eG
      let eQ' := modelCoordinates (R := R) (L := E) M.genericTarget eQ
      have hz' : pointMap q' E (eG'.symm z) = dE x * (dE y)⁻¹ := by
        apply eQ'.injective
        rw [map_mul, map_inv]
        change modelCoordinates M.genericTarget eQ (pointMap q' E (eG'.symm z)) =
          eQ' (dE x) * (eQ' (dE y))⁻¹
        rw [modelCoordinates_map M.genericSource M.genericTarget eG eQ M.map q' q₀
          M.genericMap hq₀]
        change convolutionMap q₀ (eG' (eG'.symm z)) = _
        rw [eG'.apply_symm_apply]
        exact hz
      refine ⟨(e G.val E) (eG'.symm z), ?_⟩
      calc
        _ = (e Q.val E) (pointMap q' E (eG'.symm z)) :=
          (baseChangeEquiv_map (E := E) q (eG'.symm z)).symm
        _ = (e Q.val E) (dE x * (dE y)⁻¹) := congrArg (e Q.val E) hz'
        _ = _ := by
          rw [map_mul (e Q.val E), map_inv (e Q.val E),
            map_mul (changeScalars Q.val (Algebra.ofId K E)),
            map_inv (changeScalars Q.val (Algebra.ofId K E))]
          exact congrArg₂ (fun a b => a * b⁻¹)
            ((e Q.val E).apply_symm_apply _) ((e Q.val E).apply_symm_apply _))
  exact ⟨F, fun d hd => hF (⟨d, hd⟩ : X)⟩

end Assembly

end LinearAlgebraicGroups.Arithmetic.CentralIsogenyRationalCosets
