import Specs.LinearAlgebraicGroups.Arithmetic.F4LiftedChevalley
import LinearAlgebraicGroups.Arithmetic.SplitAlbertLocalForms
import LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory TensorProduct nonZeroDivisors

universe u v

namespace LinearAlgebraicGroups.Arithmetic.F4LiftedChevalley

open LinearAlgebraicGroups.Specs
open Albert.AutomorphismTypeSpecification (IntegralSplitIdentification)
open IntegralSemisimpleModel
open Pinning (BasedRootDatum BasedIso)
open SplitAlbertLocalFormsSpecification (HasF4Cartan)
open F4LiftedChevalleySpecification (integerLift)

attribute [local instance] integerLift

open private fieldRealization_of_integralMarking from
  LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

open private model_hasF4Cartan model_rootSystem from
  LinearAlgebraicGroups.Arithmetic.SplitAlbertLocalForms

noncomputable section

private abbrev liftIndex (D : BasedRootDatum.{0}) : D.I ≃ ULift.{u} D.I :=
  Equiv.ulift.symm

private abbrev liftLattice (M : Type) [AddCommGroup M] : M ≃ₗ[ℤ] ULift.{u} M :=
  ULift.moduleEquiv.symm

private abbrev liftPairing (D : BasedRootDatum.{0}) :=
  D.datum.map (liftIndex.{u} D) (liftLattice.{u} D.X) (liftLattice.{u} D.Y)

private def pairingLiftIso (D : BasedRootDatum.{0}) : D.datum.Equiv (liftPairing.{u} D) where
  weightMap := (liftLattice D.X).toLinearMap
  coweightMap := (liftLattice D.Y).symm.toLinearMap
  indexEquiv := liftIndex D
  weight_coweight_transpose := by ext y x; rfl
  root_weightMap := rfl
  coroot_coweightMap := rfl
  bijective_weightMap := (liftLattice D.X).bijective
  bijective_coweightMap := (liftLattice D.Y).symm.bijective

private theorem liftReduced (D : BasedRootDatum.{0}) : (liftPairing.{u} D).IsReduced := by
  constructor
  intro ⟨i⟩ ⟨j⟩ h
  have h' : ¬ LinearIndependent ℤ ![D.datum.root i, D.datum.root j] := by
    intro hlin
    apply h
    convert hlin.map'
      (liftLattice.{u} D.X).toLinearMap (LinearMap.ker_eq_bot.mpr (liftLattice D.X).injective) using 1
    ext n
    fin_cases n <;> rfl
  rcases D.reduced.eq_or_eq_neg i j h' with hi | hi
  · left
    exact congrArg ULift.up hi
  · right
    exact congrArg ULift.up hi

private abbrev liftDatum (D : BasedRootDatum.{0}) : BasedRootDatum.{u} := by
  letI := D.freeX
  letI := D.freeY
  letI := D.finiteX
  letI := D.finiteY
  letI := D.finiteRoots
  exact {
    I := ULift.{u} D.I
    X := ULift.{u} D.X
    Y := ULift.{u} D.Y
    finiteRoots := inferInstance
    freeX := inferInstance
    freeY := inferInstance
    finiteX := Module.Finite.of_surjective (liftLattice D.X).toLinearMap
      (liftLattice D.X).surjective
    finiteY := Module.Finite.of_surjective (liftLattice D.Y).toLinearMap
      (liftLattice D.Y).surjective
    datum := liftPairing D
    reduced := liftReduced D
    base := D.base.map (pairingLiftIso D) }

private theorem liftDatum_cartan (S : IntegralSplitIdentification) :
    HasF4Cartan (liftDatum.{u} S.datum) := by
  classical
  obtain ⟨a, ha⟩ := model_hasF4Cartan S
  let e := S.datum.base.supportMapEquiv (pairingLiftIso.{u} S.datum)
  refine ⟨a.trans e, fun i j => ?_⟩
  change (liftPairing S.datum).pairing (e (a i)).val (e (a j)).val = _
  have he (r : S.datum.base.support) :
      (e r).val = (pairingLiftIso.{u} S.datum).indexEquiv r.val := by
    simp [e, RootPairing.Base.supportMapEquiv]
  rw [he, he, (pairingLiftIso S.datum).toHom.pairing, ha]

private theorem liftDatum_rootSystem (S : IntegralSplitIdentification) :
    (liftDatum.{u} S.datum).datum.IsRootSystem := by
  let := model_rootSystem S
  change (liftPairing S.datum).IsRootSystem
  infer_instance

section OpenImmersions

variable {A B : Type} {A' B' : Type u}
  [CommRing A] [CommRing B] [CommRing A'] [CommRing B']

set_option backward.isDefEq.respectTransparency false in
/-- An isomorphism of the rings in a coordinate map, even across universes,
transports the corresponding open immersion. -/
private theorem specMap_open_of_ringEquiv (f : A →+* B) (g : A' →+* B')
    (eA : A ≃+* A') (eB : B ≃+* B')
    (h : g.comp eA.toRingHom = eB.toRingHom.comp f)
    (hf : IsOpenImmersion (Spec.map (CommRingCat.ofHom f))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom g)) := by
  obtain ⟨hopen, hstalk⟩ := IsOpenImmersion.iff_isIso_stalkMap.mp hf
  have hcomap (q : PrimeSpectrum B') :
      PrimeSpectrum.comap eA.toRingHom (PrimeSpectrum.comap g q) =
        PrimeSpectrum.comap f (PrimeSpectrum.comap eB.toRingHom q) := by
    simpa only [PrimeSpectrum.comap_comp, Function.comp_apply] using
      congrArg (fun t : A →+* B' => PrimeSpectrum.comap t q) h
  refine IsOpenImmersion.iff_isIso_stalkMap.mpr ⟨?_, ?_⟩
  · let iA := PrimeSpectrum.homeomorphOfRingEquiv eA
    let iB := PrimeSpectrum.homeomorphOfRingEquiv eB
    have H : PrimeSpectrum.comap g = iA ∘ PrimeSpectrum.comap f ∘ iB.symm := by
      funext q
      apply iA.symm.injective
      exact (hcomap q).trans ((iA.symm_apply_apply _).symm)
    change Topology.IsOpenEmbedding (PrimeSpectrum.comap g)
    rw [H]
    exact iA.isOpenEmbedding.comp (hopen.comp iB.symm.isOpenEmbedding)
  · intro q
    change PrimeSpectrum B' at q
    let p : PrimeSpectrum B := PrimeSpectrum.comap eB.toRingHom q
    let a : PrimeSpectrum A := PrimeSpectrum.comap f p
    let a' : PrimeSpectrum A' := PrimeSpectrum.comap g q
    let e := Localization.localRingEquiv a.asIdeal a'.asIdeal eA
      (congrArg PrimeSpectrum.asIdeal (hcomap q).symm)
    let d := Localization.localRingEquiv p.asIdeal q.asIdeal eB rfl
    let fl := Localization.localRingHom a.asIdeal p.asIdeal f rfl
    let gl := Localization.localRingHom a'.asIdeal q.asIdeal g rfl
    have hloc : gl.comp e.toRingHom = d.toRingHom.comp fl := by
      apply IsLocalization.ringHom_ext a.asIdeal.primeCompl
      ext1 x
      change Localization.localRingHom a'.asIdeal q.asIdeal g rfl
          (Localization.localRingHom a.asIdeal a'.asIdeal eA.toRingHom
            (congrArg PrimeSpectrum.asIdeal (hcomap q).symm)
            (algebraMap A (Localization.AtPrime a.asIdeal) x)) =
        Localization.localRingHom p.asIdeal q.asIdeal eB.toRingHom rfl
          (Localization.localRingHom a.asIdeal p.asIdeal f rfl
            (algebraMap A (Localization.AtPrime a.asIdeal) x))
      simp only [Localization.localRingHom_to_map]
      exact congrArg (fun t : A →+* B' =>
        algebraMap B' (Localization.AtPrime q.asIdeal) (t x)) h
    have hfl : IsIso (CommRingCat.ofHom fl) :=
      (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms CommRingCat)
        (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom f) p)).mp (hstalk p)
    have hgl : IsIso (CommRingCat.ofHom gl) := by
      have hb := (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom fl)).mp hfl
      apply (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom gl)).mpr
      suffices gl = (d.toRingHom.comp fl).comp e.symm.toRingHom by
        rw [this]
        exact d.bijective.comp (hb.comp e.symm.bijective)
      rw [← hloc]
      ext1 x
      change gl x = gl (e (e.symm x))
      rw [e.apply_symm_apply]
    exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms CommRingCat)
      (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom g) q)).mpr hgl

end OpenImmersions

section ConnectedFibres

open Algebra.TensorProduct

variable {R₀ A : Type} [CommRing R₀] [CommRing A] [Algebra R₀ A]

/-- Extending the field in a tensor fibre embeds the original fibre ring. -/
private theorem tensor_fieldMap_injective {L : Type} {K : Type u}
    [Field L] [Field K] [Algebra R₀ L] [Algebra R₀ K] (f : L →ₐ[R₀] K) :
    Function.Injective
      (Algebra.TensorProduct.map f (AlgHom.id R₀ A) : L ⊗[R₀] A →ₐ[R₀] K ⊗[R₀] A) := by
  let : Algebra L K := f.toRingHom.toAlgebra
  let : IsScalarTower R₀ L K := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  let d := cancelBaseChange R₀ L K K A
  let j : L ⊗[R₀] A →ₐ[L] K ⊗[L] (L ⊗[R₀] A) := includeRight
  have hj : Function.Injective j := includeRight_injective f.injective
  have heq : (Algebra.TensorProduct.map f (AlgHom.id R₀ A) :
      L ⊗[R₀] A →ₐ[R₀] K ⊗[R₀] A) =
      (d.toAlgHom.restrictScalars R₀).comp (j.restrictScalars R₀) := by
    apply Algebra.TensorProduct.ext'
    intro l a
    change f l ⊗ₜ[R₀] a = d ((1 : K) ⊗ₜ[L] (l ⊗ₜ[R₀] a))
    rw [cancelBaseChange_tmul, Algebra.smul_def, mul_one]
    rfl
  rw [heq]
  exact d.injective.comp hj

/-- Any particular tensor in a field fibre is defined over a small subfield. -/
private theorem tensor_from_small_field {K : Type u} [Field K] [Algebra R₀ K]
    (x : K ⊗[R₀] A) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra R₀ L) (f : L →ₐ[R₀] K) (y : L ⊗[R₀] A),
      Algebra.TensorProduct.map f (AlgHom.id R₀ A) y = x := by
  classical
  obtain ⟨n, c, b, rfl⟩ := TensorProduct.exists_sum_tmul_eq x
  let E := Algebra.adjoin R₀ (Set.range c)
  let : Small.{0} (Set.range c) := small_range c
  let : Small.{0} E := Algebra.small_adjoin
  let D := Shrink.{0} E
  let e : D →ₐ[R₀] K := E.val.comp (Shrink.algEquiv (R := R₀) (α := E)).toAlgHom
  let L := FractionRing D
  let f : L →ₐ[R₀] K :=
    IsFractionRing.liftAlgHom (g := e) (Subtype.val_injective.comp (Shrink.algEquiv R₀ E).injective)
  let d (i : Fin n) : D :=
    (Shrink.algEquiv R₀ E).symm ⟨c i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  refine ⟨L, inferInstance, inferInstance, f,
    ∑ i, (algebraMap D L (d i)) ⊗ₜ[R₀] b i, ?_⟩
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Algebra.TensorProduct.map_tmul]
  congr 1
  change f (algebraMap D L (d i)) = c i
  rw [show f (algebraMap D L (d i)) = e (d i) from IsLocalization.lift_eq _ _]
  change ((Shrink.algEquiv R₀ (α := E)) (d i)).val = c i
  simp [d]

private theorem idempotent_eq_zero_or_one_of_preconnected {C : Type*} [CommRing C]
    [PreconnectedSpace (PrimeSpectrum C)] (x : C) (hx : IsIdempotentElem x) :
    x = 0 ∨ x = 1 := by
  let e := PrimeSpectrum.isIdempotentElemEquivClopens (R := C)
  let s := e ⟨x, hx⟩
  rcases ((preconnectedSpace_iff_clopen (α := PrimeSpectrum C)).mp inferInstance) (s : Set _) s.isClopen with hs | hs
  · have hs' : s = ⊥ := SetLike.coe_injective hs
    left
    have h := congrArg e.symm hs'
    change e.symm (e ⟨x, hx⟩) = e.symm ⊥ at h
    rw [e.symm_apply_apply] at h
    exact congrArg Subtype.val (h.trans (PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot (R := C)))
  · have hs' : s = ⊤ := SetLike.coe_injective hs
    right
    have h := congrArg e.symm hs'
    change e.symm (e ⟨x, hx⟩) = e.symm ⊤ at h
    rw [e.symm_apply_apply] at h
    exact congrArg Subtype.val (h.trans (PrimeSpectrum.isIdempotentElemEquivClopens_symm_top (R := C)))

/-- Connectedness of every small field fibre gives connectedness over a
field of any universe, by descending each idempotent of the fibre ring. -/
private theorem connected_tensor_of_small_fields
    (h : ∀ (L : Type) [Field L] [Algebra R₀ L], ConnectedSpace (PrimeSpectrum (L ⊗[R₀] A)))
    {K : Type u} [Field K] [Algebra R₀ K] :
    ConnectedSpace (PrimeSpectrum (K ⊗[R₀] A)) := by
  have ht (z : K ⊗[R₀] A) (hz : IsIdempotentElem z) : z = 0 ∨ z = 1 := by
    obtain ⟨L, hL, hAlg, f, y, rfl⟩ := tensor_from_small_field z
    let : PreconnectedSpace (PrimeSpectrum (L ⊗[R₀] A)) := (h L).toPreconnectedSpace
    have hy : IsIdempotentElem y := by
      apply tensor_fieldMap_injective (A := A) f
      exact (map_mul _ y y).trans hz
    exact (idempotent_eq_zero_or_one_of_preconnected y hy).imp
      (fun he => by rw [he, map_zero]) (fun he => by rw [he, map_one])
  have hpre : PreconnectedSpace (PrimeSpectrum (K ⊗[R₀] A)) := by
    rw [preconnectedSpace_iff_clopen]
    intro s hs
    let t : TopologicalSpace.Clopens (PrimeSpectrum (K ⊗[R₀] A)) := ⟨s, hs⟩
    let e := PrimeSpectrum.isIdempotentElemEquivClopens (R := K ⊗[R₀] A)
    let y := e.symm t
    rcases ht y.val y.property with h0 | h1
    · left
      have hy : y = e.symm ⊥ := Subtype.ext (by
        rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot]
        exact h0)
      exact congrArg (fun c : TopologicalSpace.Clopens (PrimeSpectrum (K ⊗[R₀] A)) =>
        (c : Set (PrimeSpectrum (K ⊗[R₀] A)))) (e.symm.injective hy)
    · right
      have hy : y = e.symm ⊤ := Subtype.ext (by
        rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_top]
        exact h1)
      exact congrArg (fun c : TopologicalSpace.Clopens (PrimeSpectrum (K ⊗[R₀] A)) =>
        (c : Set (PrimeSpectrum (K ⊗[R₀] A)))) (e.symm.injective hy)
  have hn : Nontrivial (K ⊗[R₀] A) := by
    obtain ⟨L, _, _, f, _, _⟩ := tensor_from_small_field (0 : K ⊗[R₀] A)
    let : Nontrivial (L ⊗[R₀] A) :=
      PrimeSpectrum.nonempty_iff_nontrivial.mp (h L).toNonempty
    exact (tensor_fieldMap_injective (A := A) f).nontrivial
  exact ⟨PrimeSpectrum.nonempty_iff_nontrivial.mpr hn⟩

end ConnectedFibres

section FieldRealization

open OrderedRootProducts (Enumerates)
open Pinning (SplitBorelPair AttachedDatum)

private theorem rationalAnnihilator_eq_bot (D : BasedRootDatum.{u})
    (hD : D.datum.IsRootSystem) : RootData.rationalRootAnnihilator D.datum = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  let f : D.Y →ₗ[ℤ] ℚ ⊗[ℤ] D.Y := TensorProduct.mk ℤ ℚ D.Y 1
  let : IsLocalizedModule ℤ⁰ f :=
    IsLocalization.tensorProduct_isLocalizedModule ℤ⁰ ℚ (M := D.Y)
  obtain ⟨⟨x, n⟩, hn⟩ := IsLocalizedModule.surj ℤ⁰ f y
  have hx (i : D.I) : D.datum.root' i x = 0 := by
    let l := D.datum.root' i
    have hyi : RootData.extendFunctional ℚ l y = 0 :=
      LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hy i)
    have h := congrArg (RootData.extendFunctional ℚ l) hn
    change RootData.extendFunctional ℚ l (n.val • y) =
      RootData.extendFunctional ℚ l (1 ⊗ₜ[ℤ] x) at h
    rw [RootData.extendFunctional_one_tmul, LinearMap.map_smul_of_tower, hyi, smul_zero] at h
    exact_mod_cast h.symm
  let l : D.X →ₗ[ℤ] ℤ := D.datum.flip.toPerfPair x
  have hl : Submodule.span ℤ (Set.range D.datum.root) ≤ l.ker := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hx i
  have hz : x = 0 := by
    apply D.datum.flip.toPerfPair.injective
    ext w
    have hw : w ∈ l.ker := hl (hD.span_root_eq_top.symm ▸ Submodule.mem_top)
    have hzero : D.datum.flip.toPerfPair x w = 0 := LinearMap.mem_ker.mp hw
    simpa using hzero
  have hfx : f x = 0 := by rw [hz, map_zero]
  apply (smul_right_injective (ℚ ⊗[ℤ] D.Y)
    (show (n.val : ℚ) ≠ 0 by exact_mod_cast nonZeroDivisors.coe_ne_zero n))
  change (n.val : ℚ) • y = (n.val : ℚ) • 0
  rw [Int.cast_smul_eq_zsmul, smul_zero]
  exact hn.trans hfx

private theorem span_eq_top_transport {I J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    (f : I → X) (g : J → Y) (e : I ≃ J) (l : X ≃ₗ[ℤ] Y)
    (h : ∀ i, l (f i) = g (e i)) (hf : Submodule.span ℤ (Set.range f) = ⊤) :
    Submodule.span ℤ (Set.range g) = ⊤ := by
  have hset : l '' Set.range f = Set.range g := by
    rw [← Set.range_comp, show l ∘ f = g ∘ e from funext h, Set.range_comp]
    simp [e.surjective.range_eq]
  rw [← hset]
  change Submodule.span ℤ (l.toLinearMap '' Set.range f) = ⊤
  rw [← Submodule.map_span, hf, Submodule.map_top, LinearMap.range_eq_top.mpr l.surjective]

private theorem basedIso_rootSystem {D E : BasedRootDatum.{u}}
    (i : BasedIso D E) (h : D.datum.IsRootSystem) : E.datum.IsRootSystem := by
  let e := i.val
  constructor
  · apply span_eq_top_transport _ _ e.indexEquiv e.weightEquiv _ h.span_root_eq_top
    intro a
    exact RootPairing.Hom.root_weightMap_apply D.datum E.datum a e.toHom
  · apply span_eq_top_transport _ _ e.indexEquiv e.coweightEquiv.symm _ h.span_coroot_eq_top
    intro a
    apply e.coweightEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (by simp [RootPairing.Hom.coroot_coweightMap_apply] :
      e.coweightEquiv (E.datum.coroot (e.indexEquiv a)) = D.datum.coroot a).symm

private theorem basedIso_cartan {D E : BasedRootDatum.{u}}
    (i : BasedIso D E) (h : HasF4Cartan D) : HasF4Cartan E := by
  obtain ⟨a, ha⟩ := h
  let b : D.base.support ≃ E.base.support :=
    (i.val.indexEquiv.image (D.base.support : Set D.I)).trans (Set.equivOfEq i.property)
  refine ⟨a.trans b, fun j k => ?_⟩
  exact i.val.toHom.pairing.trans (ha j k)

private theorem exists_ordering {I : Type u} [Finite I] (T : Set I) :
    ∃ l : List I, Enumerates l T := by
  classical
  let := Fintype.ofFinite I
  let s := Finset.univ.filter (· ∈ T)
  exact ⟨s.toList, s.nodup_toList, fun i => by simp [s]⟩

/-- A marking of the actual lifted model gives the required split pair on its field fibre. -/
private theorem fieldPair_of_lifted_marking (S : IntegralSplitIdentification)
    (M : IntegralMarking (liftDatum.{u} S.datum)) {H : IntegralGroup.{u}} (e : M.group ≅ H)
    (k : Type u) [Field k] :
    ∃ (P : SplitBorelPair k) (D : AttachedDatum P),
      HasF4Cartan D.toBased ∧ D.toBased.datum.IsRootSystem ∧
        Nonempty (P.G.val ≅ (fibre k).obj H) := by
  let D := liftDatum.{u} S.datum
  let := D.finiteRoots
  obtain ⟨l, hl⟩ := exists_ordering {a | ¬ D.base.IsPos a}
  obtain ⟨r, hr⟩ := exists_ordering {a | D.base.IsPos a}
  have hD : D.datum.IsRootSystem := liftDatum_rootSystem S
  obtain ⟨_, F, f, _⟩ := fieldRealization_of_integralMarking (k := k) D
    (rationalAnnihilator_eq_bot D hD) hD.span_coroot_eq_top M l r hl hr
  exact ⟨F.pinned.pair, F.attached, basedIso_cartan F.datumIso (liftDatum_cartan S),
    basedIso_rootSystem F.datumIso hD, ⟨f.symm ≪≫ (fibre k).mapIso e⟩⟩

end FieldRealization

section RankOneExtension

open WithConv Algebra.TensorProduct
open IntegralCentralQuotient (RankOneMap)

variable (R₀ : Type) [CommRing R₀]

private abbrev SLVariables := Fin 2 × Fin 2

private def universalMatrix : Matrix (Fin 2) (Fin 2) (MvPolynomial SLVariables R₀) :=
  fun i j => MvPolynomial.X (i, j)

private def determinantIdeal : Ideal (MvPolynomial SLVariables R₀) :=
  Ideal.span { (universalMatrix R₀).det - 1 }

private abbrev SLCoordinates := MvPolynomial SLVariables R₀ ⧸ determinantIdeal R₀

private def determinantOneMatrix : Matrix.SpecialLinearGroup (Fin 2) (SLCoordinates R₀) :=
  ⟨(Ideal.Quotient.mkₐ R₀ (determinantIdeal R₀)).mapMatrix (universalMatrix R₀), by
    let q := Ideal.Quotient.mkₐ R₀ (determinantIdeal R₀)
    rw [← AlgHom.map_det]
    exact sub_eq_zero.mp (by
      rw [← map_one q, ← map_sub]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.mem_span_singleton_self _)⟩

variable {R₀} {C : Type u} [CommRing C] [Algebra R₀ C]

private def evaluateSL (s : Matrix.SpecialLinearGroup (Fin 2) C) :
    SLCoordinates R₀ →ₐ[R₀] C :=
  Ideal.Quotient.liftₐ (determinantIdeal R₀)
    (MvPolynomial.aeval (fun p : SLVariables => s.val p.1 p.2))
    (by
      intro z hz
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hz
      rw [map_mul, map_sub, map_one, AlgHom.map_det]
      have he : (MvPolynomial.aeval (fun p : SLVariables => s.val p.1 p.2) :
          MvPolynomial SLVariables R₀ →ₐ[R₀] C).mapMatrix (universalMatrix R₀) = s.val := by
        ext i j
        exact MvPolynomial.aeval_X _ _
      rw [he, s.property, sub_self, zero_mul])

private theorem evaluateSL_apply (s : Matrix.SpecialLinearGroup (Fin 2) C) (i j : Fin 2) :
    evaluateSL s ((determinantOneMatrix R₀).val i j) = s.val i j := by
  change evaluateSL s ((Ideal.Quotient.mkₐ R₀ (determinantIdeal R₀))
      (MvPolynomial.X (i, j))) = _
  exact MvPolynomial.aeval_X _ _

private theorem map_determinantOneMatrix (s : Matrix.SpecialLinearGroup (Fin 2) C) :
    Matrix.SpecialLinearGroup.map (evaluateSL s).toRingHom (determinantOneMatrix R₀) = s :=
  Matrix.SpecialLinearGroup.ext _ _ (evaluateSL_apply s)

private theorem evaluateSL_natural {C' : Type v} [CommRing C'] [Algebra R₀ C']
    (f : C →ₐ[R₀] C') (s : Matrix.SpecialLinearGroup (Fin 2) C) :
    evaluateSL (Matrix.SpecialLinearGroup.map f.toRingHom s) = f.comp (evaluateSL s) := by
  apply Ideal.Quotient.algHom_ext R₀
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  exact (evaluateSL_apply (Matrix.SpecialLinearGroup.map f.toRingHom s) i j).trans
    (congrArg f (evaluateSL_apply s i j)).symm

variable {A : Type} [CommRing A] [HopfAlgebra R₀ A]

/-- Evaluate the original rank-one map at the universal matrix, then evaluate
that coordinate map over the requested algebra. -/
private def rankOneEvaluation (r : RankOneMap R₀ A)
    (s : Matrix.SpecialLinearGroup (Fin 2) C) : WithConv (A →ₐ[R₀] C) :=
  toConv ((evaluateSL s).comp
    (r.hom (CommAlgCat.of R₀ (SLCoordinates R₀)) (determinantOneMatrix R₀)).ofConv)

private theorem rankOneEvaluation_low (r : RankOneMap R₀ A)
    (C : CommAlgCat.{0} R₀) (s : Matrix.SpecialLinearGroup (Fin 2) C) :
    rankOneEvaluation r s = r.hom C s := by
  have h := r.naturality (CommAlgCat.ofHom (evaluateSL s)) (determinantOneMatrix R₀)
  change (r.hom (CommAlgCat.of R₀ C)
    (Matrix.SpecialLinearGroup.map (evaluateSL s).toRingHom (determinantOneMatrix R₀))).ofConv =
      (rankOneEvaluation r s).ofConv at h
  rw [map_determinantOneMatrix] at h
  exact ofConv_injective h.symm

private theorem rankOneEvaluation_natural {C' : Type v} [CommRing C'] [Algebra R₀ C']
    (r : RankOneMap R₀ A) (f : C →ₐ[R₀] C') (s : Matrix.SpecialLinearGroup (Fin 2) C) :
    (rankOneEvaluation r (Matrix.SpecialLinearGroup.map f.toRingHom s)).ofConv =
      f.comp (rankOneEvaluation r s).ofConv := by
  unfold rankOneEvaluation
  rw [evaluateSL_natural, AlgHom.comp_assoc]

/-- The same rank-one map is multiplicative over every test algebra, as checked
by substitution from the pair of universal matrices. -/
private def extendRankOne (r : RankOneMap R₀ A) :
    Matrix.SpecialLinearGroup (Fin 2) C →* WithConv (A →ₐ[R₀] C) := by
  refine { toFun := rankOneEvaluation (C := C) r, map_one' := ?_, map_mul' := ?_ }
  · have h := rankOneEvaluation_natural r (Algebra.ofId R₀ C)
      (1 : Matrix.SpecialLinearGroup (Fin 2) R₀)
    rw [map_one, rankOneEvaluation_low r (CommAlgCat.of R₀ R₀), map_one] at h
    apply ofConv_injective
    rw [h]
    ext1 a
    rfl
  intro s t
  let B := SLCoordinates R₀
  let l : B →ₐ[R₀] B ⊗[R₀] B := includeLeft
  let q : B →ₐ[R₀] B ⊗[R₀] B := includeRight
  let S : Matrix.SpecialLinearGroup (Fin 2) (B ⊗[R₀] B) :=
    Matrix.SpecialLinearGroup.map (n := Fin 2) (R := B) l.toRingHom (determinantOneMatrix R₀)
  let T : Matrix.SpecialLinearGroup (Fin 2) (B ⊗[R₀] B) :=
    Matrix.SpecialLinearGroup.map (n := Fin 2) (R := B) q.toRingHom (determinantOneMatrix R₀)
  let f : B ⊗[R₀] B →ₐ[R₀] C :=
    Algebra.TensorProduct.lift (evaluateSL s) (evaluateSL t) fun _ _ => Commute.all _ _
  have hs : Matrix.SpecialLinearGroup.map f.toRingHom S = s := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (f.comp l) ((determinantOneMatrix R₀).val i j) = _
    rw [show f.comp l = evaluateSL s from lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)]
    exact evaluateSL_apply s i j
  have ht : Matrix.SpecialLinearGroup.map f.toRingHom T = t := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (f.comp q) ((determinantOneMatrix R₀).val i j) = _
    rw [show f.comp q = evaluateSL t from lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)]
    exact evaluateSL_apply t i j
  have hST : Matrix.SpecialLinearGroup.map f.toRingHom (S * T) = s * t := by
    rw [map_mul, hs, ht]
  apply ofConv_injective
  have eqS := rankOneEvaluation_natural r f S
  have eqT := rankOneEvaluation_natural r f T
  have eqST := rankOneEvaluation_natural r f (S * T)
  rw [hs] at eqS
  rw [ht] at eqT
  rw [hST] at eqST
  let B' := CommAlgCat.of R₀ (B ⊗[R₀] B)
  have eS := rankOneEvaluation_low r B' S
  have eT := rankOneEvaluation_low r B' T
  have eST := rankOneEvaluation_low r B' (S * T)
  rw [eqST, eST, map_mul]
  change f.comp ((r.hom B' S : WithConv (A →ₐ[R₀] (B ⊗[R₀] B))) * r.hom B' T).ofConv = _
  rw [← eS, ← eT]
  exact (AlgHom.comp_convMul_distrib f (rankOneEvaluation r S) (rankOneEvaluation r T)).trans
    (congrArg₂ (fun (x y : WithConv (A →ₐ[R₀] C)) => (x * y).ofConv)
      (ofConv_injective eqS.symm) (ofConv_injective eqT.symm))

end RankOneExtension

section GeometryOfScalarExtension

open Algebra.TensorProduct
open IntegralCentralQuotient (HopfSpectrum)

variable {R₀ A : Type} {R : Type u} [CommRing R₀] [CommRing A] [Algebra R₀ A]
  [CommRing R] [Algebra R₀ R]

private theorem smooth_extendSpec
    (h : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R₀ A)))) :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[R₀] A)))) := by
  let : Algebra.Smooth R₀ A := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp h)
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr (Algebra.Smooth.baseChange R₀ A R))

private theorem connected_extendSpec
    (h : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap R₀ A)))) :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[R₀] A)))) := by
  have hsmall (L : Type) [Field L] [Algebra R₀ L] : ConnectedSpace (PrimeSpectrum (L ⊗[R₀] A)) := by
    have hpb := h.geometrically_connectedSpace _ _ _ (.of_hasPullback _ (Spec.map
      (CommRingCat.ofHom (algebraMap R₀ L))))
    let e := pullbackSpecIso R₀ A L ≪≫ Scheme.Spec.mapIso
      ((Algebra.TensorProduct.comm R₀ L A).toRingEquiv.toCommRingCatIso.op)
    exact e.hom.homeomorph.connectedSpace_iff.mp hpb
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun X : Scheme.{u} => ConnectedSpace X) (R := R)).mpr
  intro K _ _
  let : Algebra R₀ K := ((algebraMap R K).comp (algebraMap R₀ R)).toAlgebra
  let : IsScalarTower R₀ R K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e := pullbackSpecIso R (R ⊗[R₀] A) K ≪≫
    Scheme.Spec.mapIso ((((Algebra.TensorProduct.comm R (R ⊗[R₀] A) K).toRingEquiv).trans
      (cancelBaseChange R₀ R K K A).toRingEquiv).symm.toCommRingCatIso.op)
  exact e.hom.homeomorph.connectedSpace_iff.mpr (connected_tensor_of_small_fields hsmall)

end GeometryOfScalarExtension

section HopfPoints

open WithConv Algebra.TensorProduct

variable {R₀ A : Type} {R C : Type u}
  [CommRing R₀] [CommRing R] [Algebra R₀ R]
  [CommRing A] [HopfAlgebra R₀ A]
  [CommRing C] [Algebra R₀ C] [Algebra R C] [IsScalarTower R₀ R C]

/-- Points of the extended Hopf algebra are the points of the original
coordinate equations, evaluated with the restricted scalar structure. -/
private def restrictHopfPoint :
    WithConv ((R ⊗[R₀] A) →ₐ[R] C) ≃* WithConv (A →ₐ[R₀] C) where
  toEquiv := (WithConv.equiv _).trans
    ((liftEquivRight R₀ R A C).symm.trans (WithConv.equiv _).symm)
  map_mul' p q := by
    apply ofConv_injective
    ext1 a
    change (p * q) ((1 : R) ⊗ₜ[R₀] a) =
      ((toConv ((p.ofConv.restrictScalars R₀).comp includeRight) : WithConv (A →ₐ[R₀] C)) *
        toConv ((q.ofConv.restrictScalars R₀).comp includeRight)) a
    let b := Coalgebra.Repr.arbitrary R₀ a
    rw [AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul,
      Bialgebra.comul_one, ← b.eq]
    simp [TensorProduct.tmul_sum, Algebra.TensorProduct.one_def]

end HopfPoints

section EquivalentCoordinateRings

open Algebra.TensorProduct

variable {R₀ : Type} {R : Type u} [CommRing R₀] [CommRing R] [Algebra R₀ R]

private def extendRingEquiv (e : R ≃ₐ[R₀] R₀) (A : CommAlgCat.{0} R₀) :
    A ≃+* R ⊗[R₀] A :=
  ((Algebra.TensorProduct.congr e (AlgEquiv.refl : A ≃ₐ[R₀] A)).trans
    (Algebra.TensorProduct.lid R₀ A)).symm.toRingEquiv

private theorem extendRingEquiv_apply (e : R ≃ₐ[R₀] R₀) (A : CommAlgCat.{0} R₀) (a : A) :
    extendRingEquiv e A a = (1 : R) ⊗ₜ[R₀] a := by
  change (Algebra.TensorProduct.congr e (AlgEquiv.refl : A ≃ₐ[R₀] A)).symm
    ((Algebra.TensorProduct.lid R₀ A).symm a) = _
  simp

end EquivalentCoordinateRings

section CoordinateRestriction

open WithConv Algebra.TensorProduct
open IntegralCentralQuotient (HopfSpectrum spectrumOfAlgHom)
open private affineMap_comp from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

/-- Turn scheme points into coordinate evaluations in both universes. -/
private abbrev convToPoint {K B C : Type v} [CommRing K] [CommRing B] [HopfAlgebra K B]
    [CommRing C] [Algebra K C] :
    WithConv (B →ₐ[K] C) ≃* ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K C)) ⟶
      (HopfSpectrum K B).X) :=
  Spec.mapMulEquiv

private theorem convToPoint_comp {K B C E : Type v} [CommRing K] [CommRing B] [HopfAlgebra K B]
    [CommRing C] [Algebra K C] [CommRing E] [Algebra K E]
    (f : C →ₐ[K] E) (p : WithConv (B →ₐ[K] C)) :
    convToPoint (toConv (f.comp p.ofConv)) = spectrumOfAlgHom f ≫ convToPoint p :=
  (affineMap_comp p.ofConv f).symm

private def mapConv {K B : Type*} {C E : Type*} [CommRing K] [CommRing B]
    [HopfAlgebra K B] [CommRing C] [Algebra K C] [CommRing E] [Algebra K E]
    (f : C →ₐ[K] E) : WithConv (B →ₐ[K] C) →* WithConv (B →ₐ[K] E) where
  toFun p := toConv (f.comp p.ofConv)
  map_one' := ofConv_injective (AlgHom.ext fun _ => f.commutes _)
  map_mul' p q := ofConv_injective (AlgHom.comp_convMul_distrib f p q)

private abbrev pointCoordinate {K B C : Type v} [CommRing K] [CommRing B] [HopfAlgebra K B]
    [CommRing C] [Algebra K C] (f : (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K C)) ⟶
      (HopfSpectrum K B).X) : B →ₐ[K] C :=
  (convToPoint.symm f).ofConv

private theorem spectrumOf_pointCoordinate {K B C : Type v} [CommRing K] [CommRing B]
    [HopfAlgebra K B] [CommRing C] [Algebra K C]
    (f : (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K C)) ⟶ (HopfSpectrum K B).X) :
    spectrumOfAlgHom (pointCoordinate f) = f := convToPoint.apply_symm_apply f

variable {K₀ A : Type} {K : Type u} [CommRing K₀] [CommRing K] [Algebra K₀ K]
  [CommRing A] [HopfAlgebra K₀ A]

private abbrev baseTest (C : CommAlgCat.{u} K) : Algebra K₀ C :=
  ((algebraMap K C).comp (algebraMap K₀ K)).toAlgebra

attribute [local instance] baseTest

private instance testScalarTower (C : CommAlgCat.{u} K) : IsScalarTower K₀ K C :=
  IsScalarTower.of_algebraMap_eq (R := K₀) (S := K) (A := C) fun _ => rfl

/-- Restriction of points along the coordinate inclusion into the tensor Hopf algebra. -/
private def highPoint (C : CommAlgCat.{u} K) :
    ((algSpec (CommRingCat.of K)).obj (op C) ⟶ (HopfSpectrum K (K ⊗[K₀] A)).X) ≃*
      WithConv (A →ₐ[K₀] C) :=
  convToPoint.symm.trans restrictHopfPoint

private theorem highPoint_apply (C : CommAlgCat.{u} K)
    (f : (K ⊗[K₀] A) →ₐ[K] C) (a : A) :
    highPoint (K₀ := K₀) C (spectrumOfAlgHom f) a = f (1 ⊗ₜ[K₀] a) := by
  change (convToPoint.symm.trans restrictHopfPoint) (convToPoint (toConv f)) a = _
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

private def extendCoordinate (C : CommAlgCat.{u} K) (f : A →ₐ[K₀] C) :
    (K ⊗[K₀] A) →ₐ[K] C :=
  liftEquivRight K₀ K A C f

private theorem extendCoordinate_apply (C : CommAlgCat.{u} K) (f : A →ₐ[K₀] C) (a : A) :
    extendCoordinate C f (1 ⊗ₜ[K₀] a) = f a := by simp [extendCoordinate, liftEquivRight]

private theorem extendCoordinate_ringEquiv (e : K ≃ₐ[K₀] K₀)
    (C : CommAlgCat.{u} K) (f : A →ₐ[K₀] C) (a : A) :
    extendCoordinate C f (extendRingEquiv e (CommAlgCat.of K₀ A) a) = f a := by
  rw [extendRingEquiv_apply, extendCoordinate_apply]

private theorem highPoint_ringEquiv (e : K ≃ₐ[K₀] K₀)
    (C : CommAlgCat.{u} K) (f : (K ⊗[K₀] A) →ₐ[K] C) (a : A) :
    highPoint (K₀ := K₀) C (spectrumOfAlgHom f) a =
      f (extendRingEquiv e (CommAlgCat.of K₀ A) a) := by
  rw [extendRingEquiv_apply, highPoint_apply]

end CoordinateRestriction

private abbrev liftRing (K₀ : Type) [CommRing K₀] (K : Type u) [CommRing K] [Algebra K₀ K]
    (A : Type) [CommRing A] [Algebra K₀ A] := K ⊗[K₀] A

section Marking

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 950000

open WithConv Algebra.TensorProduct
open IntegralCentralQuotient (HopfSpectrum spectrumOfAlgHom RankOneMap)
open private affineHomEquiv affineMap_comp isMonHom_of_affine_points
  integralCellParameters integralCellCoordinateMap integralCellCoordinateMap_isIso
  integralCellMap_point additivePoint_zero affineTorusPointEquiv torusEvaluation torusEvaluation_single
  from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private abbrev R₀ := Integers.{0}
private abbrev R := Integers.{u}

private abbrev integerRingEquiv : R₀ ≃+* R.{u} :=
  (ULift.ringEquiv : R₀ ≃+* ℤ).trans (ULift.ringEquiv : R.{u} ≃+* ℤ).symm

private def integerAlgEquiv : R.{u} ≃ₐ[R₀] R₀ where
  __ := integerRingEquiv.symm
  commutes' _ := rfl

private abbrev TorusRing (D : BasedRootDatum.{v}) :=
  MonoidAlgebra Integers.{v} (Multiplicative D.X)

private abbrev CellRing (D : BasedRootDatum.{v}) := MvPolynomial D.I (TorusRing D)

private abbrev latticeMonoidEquiv (D : BasedRootDatum.{0}) :
    Multiplicative D.X ≃* Multiplicative (liftDatum.{u} D).X :=
  (liftLattice D.X).toAddEquiv.toMultiplicative

private def polynomialEquiv : Polynomial R₀ ≃+* Polynomial R.{u} :=
  Polynomial.mapEquiv integerRingEquiv

private def torusRingEquiv (D : BasedRootDatum.{0}) :
    TorusRing D ≃+* TorusRing (liftDatum.{u} D) :=
  (MonoidAlgebra.mapRingEquiv _ integerRingEquiv).trans
    (MonoidAlgebra.mapDomainRingEquiv _ (latticeMonoidEquiv D))

private def cellRingEquiv (D : BasedRootDatum.{0}) :
    CellRing D ≃+* CellRing (liftDatum.{u} D) :=
  (MvPolynomial.mapEquiv D.I (torusRingEquiv D)).trans
    (MvPolynomial.renameEquiv _ (liftIndex D)).toRingEquiv

private theorem torusRingEquiv_single (D : BasedRootDatum.{0})
    (x : Multiplicative D.X) (n : R₀) :
    torusRingEquiv.{u} D (MonoidAlgebra.single x n) =
      MonoidAlgebra.single (latticeMonoidEquiv D x) (integerRingEquiv n) := by
  simp [torusRingEquiv]

private theorem cellRingEquiv_X (D : BasedRootDatum.{0}) (a : D.I) :
    cellRingEquiv.{u} D (MvPolynomial.X a) = MvPolynomial.X (liftIndex D a) := by
  change MvPolynomial.renameEquiv _ (liftIndex D)
    (MvPolynomial.mapEquiv D.I (torusRingEquiv D) (MvPolynomial.X a)) = _
  simp

variable {A : Type} [CommRing A] [HopfAlgebra R₀ A]

private abbrev lowPoint (C : IntegralAlgebra.{0}) :
    IntegralPoints (HopfSpectrum R₀ A) C ≃* WithConv (A →ₐ[R₀] C) :=
  convToPoint.symm

attribute [local instance 50] baseTest

private def intAlgHom {B : Type} {C : IntegralAlgebra.{u}} [CommRing B] [Algebra R₀ B] (f : B →+* C) : B →ₐ[R₀] C where
  __ := f
  commutes' r := by
    have h : (f.comp (algebraMap R₀ B)).comp (ULift.ringEquiv : R₀ ≃+* ℤ).symm.toRingHom =
        (algebraMap R₀ C).comp (ULift.ringEquiv : R₀ ≃+* ℤ).symm.toRingHom := Subsingleton.elim _ _
    exact DFunLike.congr_fun h r.down

private def liftCoordinate {B : Type} (C : IntegralAlgebra.{u}) [CommRing B] [Algebra R₀ B] (e : B ≃+* C) (f : A →ₐ[R₀] B) :
    (liftRing R₀ R.{u} A) →ₐ[R.{u}] C :=
  extendCoordinate C ((intAlgHom e.toRingHom).comp f)

private abbrev coordinateInclusion (A : Type) [CommRing A] [Algebra R₀ A] :
    A ≃+* liftRing R₀ R.{u} A :=
  extendRingEquiv integerAlgEquiv.{u} (CommAlgCat.of R₀ A)

private theorem liftCoordinate_apply {B : Type} {C : IntegralAlgebra.{u}} [CommRing B] [Algebra R₀ B] (e : B ≃+* C) (f : A →ₐ[R₀] B) (a : A) :
    liftCoordinate C e f (coordinateInclusion A a) = e (f a) :=
  extendCoordinate_ringEquiv integerAlgEquiv.{u} C ((intAlgHom e.toRingHom).comp f) a

private theorem liftCoordinate_closed {B : Type} {C : IntegralAlgebra.{u}} [CommRing B] [Algebra R₀ B] (e : B ≃+* C) (f : A →ₐ[R₀] B)
    (h : IsClosedImmersion (spectrumOfAlgHom f).left) :
    IsClosedImmersion (spectrumOfAlgHom (liftCoordinate C e f)).left := by
  apply IsClosedImmersion.spec_of_surjective
  have hf : Function.Surjective f := by
    let h' : IsClosedImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := h
    have hh := (IsClosedImmersion.isAffine_surjective_of_isAffine
      (Spec.map (CommRingCat.ofHom f.toRingHom))).2
    let g := CommRingCat.ofHom f.toRingHom
    let i := (Scheme.ΓSpecIso (CommRingCat.of A)).inv
    let j := (Scheme.ΓSpecIso (CommRingCat.of B)).hom
    have hh' : Function.Surjective ((i ≫ (Spec.map g).appTop) ≫ j) :=
      (ConcreteCategory.bijective_of_isIso j).2.comp
        (hh.comp (ConcreteCategory.bijective_of_isIso i).2)
    have hgj : (i ≫ (Spec.map g).appTop) ≫ j = g := by
      dsimp only [i, j]
      rw [Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    rw [hgj] at hh'
    exact hh'
  have hs := e.surjective.comp hf
  intro c
  obtain ⟨a, ha⟩ := hs c
  exact ⟨coordinateInclusion A a, (liftCoordinate_apply e f a).trans ha⟩

private abbrev HighGroup (A : Type) [CommRing A] [HopfAlgebra R₀ A] :=
  F4LiftedChevalleySpecification.liftedGroup.{u} A

private abbrev liftedLine : AdditiveLine.{u} :=
  _root_.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel.integralAdditiveLine

variable {D : BasedRootDatum.{0}}
  (M : IntegralMarking D) (e : HopfSpectrum R₀ A ≅ M.group)

private abbrev lowRoot (i : D.I) : M.line.group ⟶ HopfSpectrum R₀ A := M.root i ≫ e.inv

private abbrev lowTorus : splitTorus D ⟶ HopfSpectrum R₀ A := M.torus ≫ e.inv

private def rootScheme (i : D.I) : liftedLine.{u}.group.X ⟶ (HighGroup.{u} A).X :=
  spectrumOfAlgHom (liftCoordinate (CommAlgCat.of R.{u} (Polynomial R.{u})) polynomialEquiv
    (pointCoordinate (lowRoot M e i).hom.hom))

private def torusScheme : (splitTorus (liftDatum.{u} D)).X ⟶ (HighGroup.{u} A).X :=
  spectrumOfAlgHom (liftCoordinate (CommAlgCat.of R.{u} (TorusRing (liftDatum.{u} D)))
    (torusRingEquiv D) (pointCoordinate (lowTorus M e).hom.hom))

private theorem liftCoordinate_point {B E : Type} {C V : IntegralAlgebra.{u}} [CommRing B]
    [Algebra R₀ B] [CommRing E] [Algebra R₀ E]
    (d : B ≃+* V) (f : E →ₐ[R₀] C) (p : B →ₐ[R₀] E) (q : V →ₐ[R.{u}] C)
    (hp : ∀ b, q (d b) = f (p b)) (x : A →ₐ[R₀] B) :
    highPoint (K₀ := R₀) C (spectrumOfAlgHom q ≫ spectrumOfAlgHom (liftCoordinate V d x)) =
      mapConv f (lowPoint (CommAlgCat.of R₀ E) (spectrumOfAlgHom p ≫ spectrumOfAlgHom x)) := by
  have hq : spectrumOfAlgHom q ≫ spectrumOfAlgHom (liftCoordinate V d x) =
      spectrumOfAlgHom (q.comp (liftCoordinate V d x)) := affineMap_comp _ _
  have hp' : spectrumOfAlgHom p ≫ spectrumOfAlgHom x =
      spectrumOfAlgHom (p.comp x) := affineMap_comp _ _
  rw [hq, hp']
  apply ofConv_injective
  ext1 a
  calc
    (highPoint (K₀ := R₀) C (spectrumOfAlgHom (q.comp (liftCoordinate V d x)))).ofConv a =
        q (liftCoordinate V d x (coordinateInclusion A a)) :=
      highPoint_ringEquiv integerAlgEquiv.{u} C _ a
    _ = f (p (x a)) := by rw [liftCoordinate_apply, hp]
    _ = _ := by
      change f (p (x a)) = f ((convToPoint.symm (convToPoint (toConv (p.comp x)))).ofConv a)
      rw [MulEquiv.symm_apply_apply]
      rfl

private theorem rootScheme_point {B : IntegralAlgebra.{0}} {C : IntegralAlgebra.{u}}
    (f : B →ₐ[R₀] C) (i : D.I) (z : B) :
    highPoint (K₀ := R₀) C (additivePoint C (f z) ≫ rootScheme M e i) =
      mapConv f (lowPoint B (additivePoint B z ≫ (lowRoot M e i).hom.hom)) := by
  have hpoly : ∀ b : Polynomial R₀,
      (Polynomial.aeval (f z) : Polynomial R.{u} →ₐ[R.{u}] C) (polynomialEquiv b) =
        f (Polynomial.aeval z b) := by
    let g := intAlgHom (C := C)
      ((Polynomial.aeval (f z) : Polynomial R.{u} →ₐ[R.{u}] C).toRingHom.comp
        polynomialEquiv.toRingHom)
    have hg : g = f.comp (Polynomial.aeval z) := by
      apply Polynomial.algHom_ext
      change (Polynomial.aeval (f z) : Polynomial R.{u} →ₐ[R.{u}] C)
        (Polynomial.map integerRingEquiv.toRingHom Polynomial.X) = f (Polynomial.aeval z Polynomial.X)
      simp
    exact DFunLike.congr_fun hg
  let p := pointCoordinate (lowRoot M e i).hom.hom
  have h := liftCoordinate_point (V := CommAlgCat.of R.{u} (Polynomial R.{u})) polynomialEquiv f (Polynomial.aeval z)
    (Polynomial.aeval (f z)) hpoly p
  have hp : spectrumOfAlgHom p = (lowRoot M e i).hom.hom := spectrumOf_pointCoordinate _
  rw [hp] at h
  exact h

private def mapTorus {B : IntegralAlgebra.{0}} {C : IntegralAlgebra.{u}} (f : B →ₐ[R₀] C)
    (t : TorusValues D B) : TorusValues (liftDatum.{u} D) C :=
  ((Units.map f.toMonoidHom).comp t).comp (latticeMonoidEquiv D).symm.toMonoidHom

private theorem torusScheme_point {B : IntegralAlgebra.{0}} {C : IntegralAlgebra.{u}}
    (f : B →ₐ[R₀] C) (t : TorusValues D B) :
    highPoint (K₀ := R₀) C (torusPoint (liftDatum.{u} D) C (mapTorus f t) ≫ torusScheme M e) =
      mapConv f (lowPoint B (torusPoint D B t ≫ (lowTorus M e).hom.hom)) := by
  let p := torusEvaluation (k := R₀) t
  let q := torusEvaluation (k := R.{u}) (mapTorus f t)
  have htorus : ∀ b : TorusRing D, q (torusRingEquiv D b) = f (p b) := by
    let g := intAlgHom (C := C) (q.toRingHom.comp (torusRingEquiv D).toRingHom)
    have hg : g = f.comp p := by
      apply MonoidAlgebra.algHom_ext
      · intro m
        change q (torusRingEquiv D (MonoidAlgebra.single m 1)) =
          f (p (MonoidAlgebra.single m 1))
        rw [torusRingEquiv_single, map_one, torusEvaluation_single, torusEvaluation_single]
        simp [mapTorus]
      · exact Subsingleton.elim _ _
    exact DFunLike.congr_fun hg
  let x := pointCoordinate (lowTorus M e).hom.hom
  have h := liftCoordinate_point (V := CommAlgCat.of R.{u} (TorusRing (liftDatum.{u} D)))
    (torusRingEquiv D) f p q htorus x
  have hx : spectrumOfAlgHom x = (lowTorus M e).hom.hom := spectrumOf_pointCoordinate _
  rw [hx] at h
  exact h

/-- A small set of coefficients in a test ring is contained in a small test subalgebra. -/
private theorem exists_small_test (C : IntegralAlgebra.{u}) (s : Set C) [Small.{0} s] :
    ∃ (B : IntegralAlgebra.{0}) (f : B →ₐ[R₀] C),
      Function.Injective f ∧ s ⊆ Set.range f := by
  let B := Algebra.adjoin R₀ s
  let : Small.{0} B := Algebra.small_adjoin
  let e := Shrink.algEquiv R₀ B
  let f := B.val.comp e.toAlgHom
  exact ⟨CommAlgCat.of R₀ (Shrink.{0} B), f, Subtype.val_injective.comp e.injective,
    fun x hx => ⟨e.symm ⟨x, Algebra.subset_adjoin hx⟩,
      congrArg Subtype.val (e.apply_symm_apply ⟨x, Algebra.subset_adjoin hx⟩)⟩⟩

private theorem unit_from_small_test {B : IntegralAlgebra.{0}} {C : IntegralAlgebra.{u}}
    (f : B →ₐ[R₀] C) (hf : Function.Injective f) (s : Cˣ)
    (hs : (s : C) ∈ Set.range f) (hs' : ((s⁻¹ : Cˣ) : C) ∈ Set.range f) :
    ∃ t : Bˣ, Units.map f.toMonoidHom t = s := by
  obtain ⟨x, hx⟩ := hs
  obtain ⟨y, hy⟩ := hs'
  refine ⟨⟨x, y, hf ?_, hf ?_⟩, Units.ext hx⟩
  · rw [map_mul, hx, hy, map_one, Units.mul_inv]
  · rw [map_mul, hx, hy, map_one, Units.inv_mul]

private theorem torus_from_small_test {B : IntegralAlgebra.{0}} {C : IntegralAlgebra.{u}}
    (f : B →ₐ[R₀] C) (hf : Function.Injective f) (t : TorusValues (liftDatum.{u} D) C)
    (ht : Set.range (fun a : D.X => (t (latticeMonoidEquiv D (Multiplicative.ofAdd a)) : C))
      ⊆ Set.range f) :
    ∃ z : TorusValues D B, mapTorus f z = t := by
  have h (x : Multiplicative D.X) : ∃ y : Bˣ,
      Units.map f.toMonoidHom y = t (latticeMonoidEquiv D x) := by
    apply unit_from_small_test f hf
    · exact ht (Set.mem_range_self x.toAdd)
    · rw [← map_inv, ← map_inv]
      exact ht (Set.mem_range_self (x⁻¹).toAdd)
  choose z hz using h
  have hu := Units.map_injective (f := f.toMonoidHom) hf
  let z' : TorusValues D B :=
    { toFun := z
      map_one' := hu (by rw [hz, map_one, map_one, map_one])
      map_mul' := fun x y => hu (by simp only [map_mul, hz]) }
  refine ⟨z', ?_⟩
  apply MonoidHom.ext
  intro x
  exact (hz ((latticeMonoidEquiv D).symm x)).trans
    (congrArg t ((latticeMonoidEquiv D).apply_symm_apply x))

private def torusValueEquiv (E : BasedRootDatum.{v}) (B : IntegralAlgebra.{v}) :
    TorusValues E B ≃* IntegralPoints (splitTorus E) B :=
  affineTorusPointEquiv B

private theorem torusValueEquiv_apply (E : BasedRootDatum.{v}) (B : IntegralAlgebra.{v})
    (t : TorusValues E B) : torusValueEquiv E B t = torusPoint E B t := rfl

private theorem additivePoint_surjective (B : IntegralAlgebra.{v}) :
    Function.Surjective (additivePoint B) := by
  intro q
  obtain ⟨f, rfl⟩ := (affineHomEquiv (k := Integers.{v}) (Polynomial Integers.{v}) B).surjective q
  refine ⟨f Polynomial.X, ?_⟩
  change spectrumOfAlgHom (Polynomial.aeval (f Polynomial.X)) = spectrumOfAlgHom f
  congr 1
  exact Polynomial.algHom_ext (Polynomial.aeval_X _)

private def rootValue (B : IntegralAlgebra.{0}) (a : D.I) :
    Multiplicative B →* WithConv (A →ₐ[R₀] B) where
  toFun z := lowPoint B (additivePoint B z.toAdd ≫ (lowRoot M e a).hom.hom)
  map_one' := by
    let := M.line.operations
    change lowPoint B (additivePoint B 0 ≫ (lowRoot M e a).hom.hom) = 1
    rw [additivePoint_zero M.line, MonObj.one_comp, map_one]
  map_mul' x y := by
    let := M.line.operations
    change lowPoint B (additivePoint B (x.toAdd + y.toAdd) ≫ (lowRoot M e a).hom.hom) = _
    rw [← M.line.add B, MonObj.mul_comp, map_mul]

private def torusValue (B : IntegralAlgebra.{0}) :
    TorusValues D B →* WithConv (A →ₐ[R₀] B) where
  toFun t := lowPoint B (torusValueEquiv D B t ≫ (lowTorus M e).hom.hom)
  map_one' := by rw [map_one, MonObj.one_comp, map_one]
  map_mul' x y := by rw [map_mul, MonObj.mul_comp, map_mul]

private theorem rootScheme_point' {B : IntegralAlgebra.{0}} {C : IntegralAlgebra.{u}}
    (f : B →ₐ[R₀] C) (a : D.I) (z : B) :
    highPoint (K₀ := R₀) C (additivePoint C (f z) ≫ rootScheme M e a) =
      mapConv f (rootValue M e B a (Multiplicative.ofAdd z)) :=
  rootScheme_point M e f a z

private theorem torusScheme_point' {B : IntegralAlgebra.{0}} {C : IntegralAlgebra.{u}}
    (f : B →ₐ[R₀] C) (t : TorusValues D B) :
    highPoint (K₀ := R₀) C (torusPoint (liftDatum.{u} D) C (mapTorus f t) ≫ torusScheme M e) =
      mapConv f (torusValue M e B t) :=
  torusScheme_point M e f t

private theorem mapTorus_one {B : IntegralAlgebra.{0}} {C : IntegralAlgebra.{u}}
    (f : B →ₐ[R₀] C) :
    mapTorus (D := D) f 1 = 1 := by
  apply MonoidHom.ext
  intro x
  exact map_one (Units.map f.toMonoidHom)

private theorem mapTorus_mul {B : IntegralAlgebra.{0}} {C : IntegralAlgebra.{u}}
    (f : B →ₐ[R₀] C) (s t : TorusValues D B) :
    mapTorus f (s * t) = mapTorus f s * mapTorus f t := by
  apply MonoidHom.ext
  intro x
  exact map_mul (Units.map f.toMonoidHom) _ _

private def liftedRoot (a : D.I) : liftedLine.{u}.group ⟶ HighGroup.{u} A := by
  letI := liftedLine.{u}.operations
  letI := (HighGroup.{u} A).grp
  haveI : IsMonHom (rootScheme.{u} M e a) := by
    apply isMonHom_of_affine_points (G := liftedLine.{u}.group) (H := HighGroup.{u} A)
      (by
        change IsAffine (Spec (CommRingCat.of (Polynomial R.{u})))
        infer_instance)
    · intro C
      apply (highPoint (K₀ := R₀) C).injective
      let B := CommAlgCat.of R₀ R₀
      let f : B →ₐ[R₀] C := Algebra.ofId R₀ C
      rw [← additivePoint_zero liftedLine C, ← map_zero f, rootScheme_point', map_one]
      change mapConv f (rootValue M e B a 1) = 1
      rw [map_one, map_one]
    · intro C x y
      obtain ⟨r, rfl⟩ := additivePoint_surjective C x
      obtain ⟨s, rfl⟩ := additivePoint_surjective C y
      have : Small.{0} ({r, s} : Set C) := small_pair r s
      obtain ⟨B, f, _, hf⟩ := exists_small_test C {r, s}
      obtain ⟨r', rfl⟩ := hf (by simp : r ∈ ({r, s} : Set C))
      obtain ⟨s', rfl⟩ := hf (by simp : s ∈ ({f r', s} : Set C))
      change (additivePoint C (f r') * additivePoint C (f s')) ≫ rootScheme M e a = _
      rw [liftedLine.add C]
      apply (highPoint (K₀ := R₀) C).injective
      rw [map_mul, ← map_add f, rootScheme_point', rootScheme_point', rootScheme_point']
      change mapConv f (rootValue M e B a (Multiplicative.ofAdd r' * Multiplicative.ofAdd s')) = _
      rw [map_mul, map_mul]
  exact Grp.homMk (rootScheme M e a)

private abbrev torusCoefficients (C : IntegralAlgebra.{u}) (t : TorusValues (liftDatum.{u} D) C) :
    Set C :=
  Set.range (fun a : D.X => (t (latticeMonoidEquiv D (Multiplicative.ofAdd a)) : C))

private def liftedTorus : splitTorus (liftDatum.{u} D) ⟶ HighGroup.{u} A := by
  letI := (splitTorus (liftDatum.{u} D)).grp
  letI := (HighGroup.{u} A).grp
  haveI : IsMonHom (torusScheme.{u} M e) := by
    apply isMonHom_of_affine_points (G := splitTorus (liftDatum.{u} D))
      (H := HighGroup.{u} A) (by
        change IsAffine (Spec (CommRingCat.of (TorusRing (liftDatum.{u} D))))
        infer_instance)
    · intro C
      apply (highPoint (K₀ := R₀) C).injective
      let B := CommAlgCat.of R₀ R₀
      let f : B →ₐ[R₀] C := Algebra.ofId R₀ C
      have ht : torusPoint (liftDatum D) C (mapTorus (D := D) f 1) =
          (1 : IntegralPoints (splitTorus (liftDatum D)) C) := by
        rw [← torusValueEquiv_apply, mapTorus_one, map_one]
      rw [← ht, torusScheme_point', map_one, map_one, map_one]
    · intro C x y
      obtain ⟨s, rfl⟩ := (torusValueEquiv (liftDatum D) C).surjective x
      obtain ⟨t, rfl⟩ := (torusValueEquiv (liftDatum D) C).surjective y
      obtain ⟨B, f, hfi, hf⟩ := exists_small_test C (torusCoefficients C s ∪ torusCoefficients C t)
      obtain ⟨s', rfl⟩ := torus_from_small_test f hfi s (Set.subset_union_left.trans hf)
      obtain ⟨t', rfl⟩ := torus_from_small_test f hfi t (Set.subset_union_right.trans hf)
      apply (highPoint (K₀ := R₀) C).injective
      rw [← map_mul (torusValueEquiv (liftDatum D) C), torusValueEquiv_apply,
        torusValueEquiv_apply, torusValueEquiv_apply, ← mapTorus_mul, map_mul,
        torusScheme_point', torusScheme_point', torusScheme_point', map_mul, map_mul]
  exact Grp.homMk (torusScheme M e)

private theorem liftRoot_closed (a : D.I) : IsClosedImmersion (liftedRoot.{u} M e a).hom.hom.left := by
  change IsClosedImmersion (rootScheme M e a).left
  unfold rootScheme
  apply liftCoordinate_closed
  rw [spectrumOf_pointCoordinate]
  change IsClosedImmersion ((M.root a).hom.hom.left ≫ e.inv.hom.hom.left)
  let : IsClosedImmersion (M.root a).hom.hom.left := M.rootClosed a
  have : IsIso e.inv.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso e.inv
  infer_instance

private theorem liftTorus_closed : IsClosedImmersion (liftedTorus.{u} M e).hom.hom.left := by
  change IsClosedImmersion (torusScheme M e).left
  unfold torusScheme
  apply liftCoordinate_closed
  rw [spectrumOf_pointCoordinate]
  change IsClosedImmersion (M.torus.hom.hom.left ≫ e.inv.hom.hom.left)
  let : IsClosedImmersion M.torus.hom.hom.left := M.torusClosed
  have : IsIso e.inv.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso e.inv
  infer_instance

private abbrev postPoint {K : Type v} [CommRing K] {G H : Grp (Over (Spec (CommRingCat.of K)))}
    (j : G ⟶ H) (B : CommAlgCat.{v} K) :=
  ((yonedaGrp.map j).app (op ((algSpec (CommRingCat.of K)).obj (op B)))).hom

private theorem conjugation_low (B : IntegralAlgebra.{0})
    (t : TorusValues D B) (a : D.I) (z : B) :
    let g := torusValue M e B t
    g * rootValue M e B a (Multiplicative.ofAdd z) =
      rootValue M e B a (Multiplicative.ofAdd ((t (Multiplicative.ofAdd (D.datum.root a)) : B) * z)) * g := by
  let j := (lowPoint B).toMonoidHom.comp (postPoint e.inv B)
  have h := congrArg j (mul_inv_eq_iff_eq_mul.mp (M.conjugation B t a z))
  dsimp only at h ⊢
  simp only [map_mul] at h
  exact h

private theorem liftConjugation (C : IntegralAlgebra.{u})
    (t : TorusValues (liftDatum.{u} D) C) (i : D.I) (z : C) :
    let g := torusPoint (liftDatum D) C t ≫ (liftedTorus M e).hom.hom
    g * (additivePoint C z ≫ (liftedRoot M e i).hom.hom) * g⁻¹ =
      additivePoint C ((t (Multiplicative.ofAdd ((liftDatum.{u} D).datum.root (liftIndex D i))) : C) * z)
        ≫ (liftedRoot M e i).hom.hom := by
  have : Small.{0} (↥(insert z (torusCoefficients C t))) := small_insert z _
  obtain ⟨B, f, hfi, hf⟩ := exists_small_test C (insert z (torusCoefficients C t))
  obtain ⟨z', rfl⟩ := hf (Set.mem_insert z _)
  obtain ⟨t', rfl⟩ := torus_from_small_test f hfi t (Set.subset_insert _ _ |>.trans hf)
  dsimp only
  have hz : ((mapTorus f t') (Multiplicative.ofAdd ((liftDatum.{u} D).datum.root (liftIndex D i))) : C) *
      f z' = f ((t' (Multiplicative.ofAdd (D.datum.root i)) : B) * z') := by
    rw [map_mul]
    rfl
  apply mul_inv_eq_iff_eq_mul.mpr
  apply (highPoint (K₀ := R₀) C).injective
  change (highPoint (K₀ := R₀) C)
      ((torusPoint (liftDatum D) C (mapTorus f t') ≫ torusScheme M e) *
        (additivePoint C (f z') ≫ rootScheme M e i)) =
      (highPoint (K₀ := R₀) C) ((additivePoint C _ ≫ rootScheme M e i) *
        (torusPoint (liftDatum D) C (mapTorus f t') ≫ torusScheme M e))
  rw [(highPoint (K₀ := R₀) C).map_mul, (highPoint (K₀ := R₀) C).map_mul, hz,
    torusScheme_point', rootScheme_point', rootScheme_point']
  simpa only [map_mul] using congrArg (mapConv f) (conjugation_low M e B t' i z')

private theorem lowPoint_comp {B C : IntegralAlgebra.{0}}
    (f : B ⟶ C) (p : IntegralPoints (HopfSpectrum R₀ A) B) :
    lowPoint C (integralSpec.map f.op ≫ p) = mapConv f.hom (lowPoint B p) := by
  apply convToPoint.injective
  change convToPoint (convToPoint.symm (integralSpec.map f.op ≫ p)) =
    convToPoint (toConv (f.hom.comp (lowPoint B p).ofConv))
  rw [convToPoint_comp, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rfl

private def restrictTestHom {B C : IntegralAlgebra.{u}} (f : B ⟶ C) : B →ₐ[R₀] C where
  __ := f.hom.toRingHom
  commutes' r := f.hom.commutes (algebraMap R₀ R.{u} r)

private theorem highPoint_comp {B C : IntegralAlgebra.{u}}
    (f : B ⟶ C) (p : IntegralPoints (HighGroup.{u} A) B) :
    highPoint (K₀ := R₀) C (integralSpec.map f.op ≫ p) =
      mapConv (restrictTestHom f) (highPoint (K₀ := R₀) B p) := by
  let q := pointCoordinate p
  have hq : spectrumOfAlgHom q = p := spectrumOf_pointCoordinate _
  rw [← hq]
  have hcomp : integralSpec.map f.op ≫ spectrumOfAlgHom q =
      spectrumOfAlgHom (f.hom.comp q) := affineMap_comp _ _
  rw [hcomp]
  apply ofConv_injective
  ext1 a
  exact (highPoint_ringEquiv integerAlgEquiv.{u} C (f.hom.comp q) a).trans
    (congrArg f.hom (highPoint_ringEquiv integerAlgEquiv.{u} B q a).symm)

private def lowRankOne (a : D.I) : RankOneMap R₀ A where
  hom B := (lowPoint B).toMonoidHom.comp ((postPoint e.inv B).comp ((M.rankOne a).app B).hom)
  naturality f s := by
    have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom ((M.rankOne a).naturality f)) s
    change (M.rankOne a).app _ (Matrix.SpecialLinearGroup.map f.hom.toRingHom s) =
      integralSpec.map f.op ≫ (M.rankOne a).app _ s at h
    have hcomp := congrArg (fun p => lowPoint _ (p ≫ e.inv.hom.hom)) h
    refine congrArg WithConv.ofConv (hcomp.trans ?_)
    rw [Category.assoc, lowPoint_comp]
    rfl

private def liftedRankOne (a : D.I) :
    rankOnePoints.{u} ⟶ integralPointFunctor (HighGroup.{u} A) where
  app C := GrpCat.ofHom ((highPoint (K₀ := R₀) C).symm.toMonoidHom.comp
    (extendRankOne (lowRankOne M e a)))
  naturality {B C} f := by
    apply GrpCat.ext
    intro s
    apply (highPoint (K₀ := R₀) _).injective
    change (highPoint (K₀ := R₀) _)
        ((highPoint (K₀ := R₀) _).symm (rankOneEvaluation (lowRankOne M e a)
          (Matrix.SpecialLinearGroup.map f.hom.toRingHom s))) =
      highPoint (K₀ := R₀) _ (integralSpec.map f.op ≫
        (highPoint (K₀ := R₀) _).symm (rankOneEvaluation (lowRankOne M e a) s))
    rw [highPoint_comp, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact ofConv_injective (rankOneEvaluation_natural (lowRankOne M e a) (restrictTestHom f) s)

private theorem liftedRankOne_of_small {B : IntegralAlgebra.{0}} {C : IntegralAlgebra.{u}}
    (f : B →ₐ[R₀] C) (a : D.I) (s : Matrix.SpecialLinearGroup (Fin 2) B) :
    highPoint (K₀ := R₀) C ((liftedRankOne M e a).app C (Matrix.SpecialLinearGroup.map f.toRingHom s)) =
      mapConv f ((lowRankOne M e a).hom B s) := by
  change (highPoint (K₀ := R₀) C) ((highPoint (K₀ := R₀) C).symm
    (rankOneEvaluation (lowRankOne M e a) (Matrix.SpecialLinearGroup.map f.toRingHom s))) = _
  rw [MulEquiv.apply_symm_apply]
  apply ofConv_injective
  rw [rankOneEvaluation_natural, rankOneEvaluation_low (lowRankOne M e a) B s]
  rfl

open IntegralRootRelations (upper lower diagonal)

private theorem map_upper {B : IntegralAlgebra.{0}} {C : IntegralAlgebra.{u}}
    (f : B →ₐ[R₀] C) (x : B) :
    Matrix.SpecialLinearGroup.map f.toRingHom (upper x) = upper (f x) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [upper, Matrix.SpecialLinearGroup.map_apply_coe]

private theorem map_lower {B : IntegralAlgebra.{0}} {C : IntegralAlgebra.{u}}
    (f : B →ₐ[R₀] C) (x : B) :
    Matrix.SpecialLinearGroup.map f.toRingHom (lower x) = lower (f x) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [lower, Matrix.SpecialLinearGroup.map_apply_coe]

private theorem map_diagonal {B : IntegralAlgebra.{0}} {C : IntegralAlgebra.{u}}
    (f : B →ₐ[R₀] C) (s : Bˣ) :
    Matrix.SpecialLinearGroup.map f.toRingHom (diagonal s) = diagonal (Units.map f.toMonoidHom s) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [diagonal, Matrix.SpecialLinearGroup.map_apply_coe]

private theorem map_cocharacter {B : IntegralAlgebra.{0}} {C : IntegralAlgebra.{u}}
    (f : B →ₐ[R₀] C) (a : D.I) (s : Bˣ) :
    mapTorus f (cocharacter D (D.datum.coroot a) B s) =
      cocharacter (liftDatum.{u} D) ((liftDatum.{u} D).datum.coroot (liftIndex D a)) C
        (Units.map f.toMonoidHom s) := by
  apply MonoidHom.ext
  intro x
  exact map_zpow (Units.map f.toMonoidHom) s (D.datum.toLinearMap x.toAdd.down (D.datum.coroot a))

private theorem liftRankOneUpper (a : D.I) (C : IntegralAlgebra.{u}) (z : C) :
    (liftedRankOne M e a).app C (upper z) = additivePoint C z ≫ (liftedRoot M e a).hom.hom := by
  let B := CommAlgCat.of R₀ (Polynomial R₀)
  let f : B →ₐ[R₀] C := Polynomial.aeval z
  have hz : f Polynomial.X = z := Polynomial.aeval_X _
  apply (highPoint (K₀ := R₀) C).injective
  change highPoint (K₀ := R₀) C ((liftedRankOne M e a).app C (upper z)) =
    highPoint (K₀ := R₀) C (additivePoint C z ≫ rootScheme M e a)
  rw [← hz, ← map_upper, liftedRankOne_of_small, rootScheme_point]
  congr 1
  change lowPoint B ((M.rankOne a).app B (upper Polynomial.X) ≫ e.inv.hom.hom) =
    lowPoint B (additivePoint B Polynomial.X ≫ (lowRoot M e a).hom.hom)
  rw [M.rankOneUpper]
  exact congrArg (lowPoint B) (Category.assoc _ _ _)

private theorem liftRankOneLower (a : D.I) (C : IntegralAlgebra.{u}) (z : C) :
    (liftedRankOne M e a).app C (lower z) =
      additivePoint C z ≫ (liftedRoot M e (D.datum.reflectionPerm a a)).hom.hom := by
  let B := CommAlgCat.of R₀ (Polynomial R₀)
  let f : B →ₐ[R₀] C := Polynomial.aeval z
  have hz : f Polynomial.X = z := Polynomial.aeval_X _
  apply (highPoint (K₀ := R₀) C).injective
  change highPoint (K₀ := R₀) C ((liftedRankOne M e a).app C (lower z)) =
    highPoint (K₀ := R₀) C (additivePoint C z ≫ rootScheme M e (D.datum.reflectionPerm a a))
  rw [← hz, ← map_lower, liftedRankOne_of_small, rootScheme_point]
  congr 1
  change lowPoint B ((M.rankOne a).app B (lower Polynomial.X) ≫ e.inv.hom.hom) =
    lowPoint B (additivePoint B Polynomial.X ≫ (lowRoot M e (D.datum.reflectionPerm a a)).hom.hom)
  rw [M.rankOneLower]
  exact congrArg (lowPoint B) (Category.assoc _ _ _)

private theorem liftRankOneDiagonal (a : D.I) (C : IntegralAlgebra.{u}) (s : Cˣ) :
    (liftedRankOne M e a).app C (diagonal s) =
      torusPoint (liftDatum.{u} D) C
        (cocharacter (liftDatum.{u} D) ((liftDatum.{u} D).datum.coroot (liftIndex D a)) C s) ≫
      (liftedTorus M e).hom.hom := by
  have : Small.{0} ({(s : C), ((s⁻¹ : Cˣ) : C)} : Set C) := small_pair _ _
  obtain ⟨B, f, hfi, hf⟩ := exists_small_test C {(s : C), ((s⁻¹ : Cˣ) : C)}
  obtain ⟨s', rfl⟩ := unit_from_small_test f hfi s (hf (by simp)) (hf (by simp))
  apply (highPoint (K₀ := R₀) C).injective
  change highPoint (K₀ := R₀) C ((liftedRankOne M e a).app C (diagonal (Units.map f.toMonoidHom s'))) =
    highPoint (K₀ := R₀) C (torusPoint _ C (cocharacter _ _ C (Units.map f.toMonoidHom s')) ≫
      torusScheme M e)
  rw [← map_diagonal, liftedRankOne_of_small, ← map_cocharacter f a, torusScheme_point]
  congr 1
  change lowPoint B ((M.rankOne a).app B (diagonal s') ≫ e.inv.hom.hom) =
    lowPoint B (torusPoint D B (cocharacter D (D.datum.coroot a) B s') ≫ (lowTorus M e).hom.hom)
  rw [M.rankOneDiagonal]
  exact congrArg (lowPoint B) (Category.assoc _ _ _)

private theorem liftDatum_pos (D : BasedRootDatum.{0}) (a : D.I) :
    (liftDatum.{u} D).base.IsPos (liftIndex D a) ↔ D.base.IsPos a := by
  classical
  obtain ⟨f, _, _, ha⟩ := D.base.exists_root_eq_sum_int a
  let E := liftDatum.{u} D
  let j := liftIndex.{u} D
  have hs : E.base.support = D.base.support.image j := by
    ext x
    simp [E, liftDatum, RootPairing.Base.map, j, pairingLiftIso]
  have ha' : E.datum.root (j a) = ∑ x ∈ E.base.support, f (j.symm x) • E.datum.root x := by
    rw [hs, Finset.sum_image j.injective.injOn]
    simp only [Equiv.symm_apply_apply]
    have h := congrArg (liftLattice.{u} D.X) ha
    simp only [map_sum, map_smul] at h
    exact h
  change E.base.IsPos (j a) ↔ _
  rw [RootPairing.Base.isPos_iff, RootPairing.Base.isPos_iff,
    E.base.height_eq_sum ha', D.base.height_eq_sum ha, hs, Finset.sum_image j.injective.injOn]
  simp only [Equiv.symm_apply_apply]

private theorem cellRingEquiv_C (D : BasedRootDatum.{0}) (x : TorusRing D) :
    cellRingEquiv.{u} D (MvPolynomial.C x) = MvPolynomial.C (torusRingEquiv D x) := by
  change MvPolynomial.renameEquiv _ (liftIndex D)
    (MvPolynomial.mapEquiv D.I (torusRingEquiv D) (MvPolynomial.C x)) = _
  simp

private theorem mapCellParameters (D : BasedRootDatum.{0}) :
    mapTorus (intAlgHom (C := CommAlgCat.of R.{u} (CellRing (liftDatum.{u} D)))
      (cellRingEquiv.{u} D).toRingHom) (integralCellParameters D) =
      integralCellParameters (liftDatum.{u} D) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨x, rfl⟩ := (latticeMonoidEquiv.{u} D).surjective x
  apply Units.ext
  change cellRingEquiv.{u} D (MvPolynomial.C
      (MonoidAlgebra.single ((latticeMonoidEquiv.{u} D).symm (latticeMonoidEquiv D x)) 1)) =
    MvPolynomial.C (MonoidAlgebra.single (latticeMonoidEquiv D x) 1)
  rw [MulEquiv.symm_apply_apply, cellRingEquiv_C, torusRingEquiv_single, map_one]

private theorem unlift_enum {S : Set D.I} {T : Set (liftDatum.{u} D).I}
    (h : ∀ a : D.I, liftIndex.{u} D a ∈ T ↔ a ∈ S)
    (l : List (liftDatum.{u} D).I) (hl : OrderedRootProducts.Enumerates l T) :
    OrderedRootProducts.Enumerates (l.map (liftIndex.{u} D).symm) S := by
  refine ⟨hl.1.map (liftIndex D).symm.injective, fun a => ?_⟩
  rw [← (liftIndex.{u} D).symm_apply_apply a, List.mem_map_of_injective (liftIndex D).symm.injective,
    hl.2, h, Equiv.symm_apply_apply]

/-- The open multiplication cell has the same coordinate polynomial after extending scalars
and relabelling the roots and the characters. -/
private theorem liftedCell_open (l r : List D.I)
    (hl : OrderedRootProducts.Enumerates l {a | ¬ D.base.IsPos a})
    (hr : OrderedRootProducts.Enumerates r {a | D.base.IsPos a})
    (hl' : OrderedRootProducts.Enumerates (l.map (liftIndex.{u} D))
      {a | ¬ (liftDatum.{u} D).base.IsPos a})
    (hr' : OrderedRootProducts.Enumerates (r.map (liftIndex.{u} D))
      {a | (liftDatum.{u} D).base.IsPos a}) :
    IsOpenImmersion
      (cellMap liftedLine.{u} (liftedTorus M e) (fun a => liftedRoot M e a.down)
        (l.map (liftIndex D)) (r.map (liftIndex D))).left := by
  let E := liftDatum.{u} D
  let B := CommAlgCat.of R₀ (CellRing D)
  let C := CommAlgCat.of R.{u} (CellRing E)
  let : Algebra R₀ C := baseTest (K₀ := R₀) C
  let f := intAlgHom (B := B) (C := C) (cellRingEquiv.{u} D).toRingHom
  let j := liftIndex.{u} D
  let x : E.I → (liftedLine.{u}.group ⟶ HighGroup.{u} A) := fun a => liftedRoot M e a.down
  let c₀ := integralCellCoordinateMap (D := D) M.line l r
  let c₁ := integralCellCoordinateMap (D := E) liftedLine.{u} (l.map j) (r.map j)
  let p₀ := (c₀ ≫ cellMap M.line M.torus M.root l r) ≫ e.inv.hom.hom
  let p₁ := c₁ ≫ cellMap liftedLine.{u} (liftedTorus M e) x (l.map j) (r.map j)
  let L (a : D.I) : IntegralPoints M.group B := additivePoint B (MvPolynomial.X a) ≫ (M.root a).hom.hom
  let T : IntegralPoints M.group B := torusPoint D B (integralCellParameters D) ≫ M.torus.hom.hom
  let L' (a : E.I) : IntegralPoints (HighGroup.{u} A) C := additivePoint C (MvPolynomial.X a) ≫ (x a).hom.hom
  let T' : IntegralPoints (HighGroup.{u} A) C :=
    torusPoint E C (integralCellParameters E) ≫ (liftedTorus M e).hom.hom
  have hp₀ : lowPoint (A := A) B p₀ =
      (l.map (fun a => rootValue M e B a (Multiplicative.ofAdd (MvPolynomial.X a)))).prod *
        torusValue M e B (integralCellParameters D) *
        (r.map (fun a => rootValue M e B a (Multiplicative.ofAdd (MvPolynomial.X a)))).prod := by
    let g : IntegralPoints M.group B →* WithConv (A →ₐ[R₀] B) :=
      (lowPoint (A := A) B).toMonoidHom.comp (postPoint e.inv B)
    have hh := congrArg g (integralCellMap_point M.line M.torus M.root l r)
    change g (c₀ ≫ cellMap M.line M.torus M.root l r) = g ((l.map L).prod * T * (r.map L).prod) at hh
    simp only [map_mul, map_list_prod, List.map_map] at hh
    exact hh
  have hp₁ : p₁ = ((l.map j).map L').prod * T' * ((r.map j).map L').prod :=
    integralCellMap_point liftedLine (liftedTorus M e) x (l.map j) (r.map j)
  have hL (a : D.I) : highPoint (A := A) (K₀ := R₀) C (L' (j a)) =
      mapConv f (rootValue M e B a (Multiplicative.ofAdd (MvPolynomial.X a))) := by
    have h := rootScheme_point' M e f a (MvPolynomial.X a)
    have he : f (MvPolynomial.X a) = MvPolynomial.X (j a) := cellRingEquiv_X D a
    rw [he] at h
    exact h
  have hT : highPoint (A := A) (K₀ := R₀) C T' =
      mapConv f (torusValue M e B (integralCellParameters D)) := by
    have h := torusScheme_point' M e f (integralCellParameters D)
    rw [mapCellParameters D] at h
    exact h
  have hprod (t : List D.I) :
      highPoint (A := A) (K₀ := R₀) C (((t.map j).map L').prod) =
        mapConv f ((t.map (fun a => rootValue M e B a (Multiplicative.ofAdd (MvPolynomial.X a)))).prod) := by
    rw [map_list_prod, map_list_prod, List.map_map, List.map_map, List.map_map]
    congr 1
    exact List.map_congr_left (fun a _ => hL a)
  have hp : highPoint (A := A) (K₀ := R₀) C p₁ = mapConv f (lowPoint (A := A) B p₀) := by
    rw [hp₀, hp₁]
    simp only [map_mul]
    rw [hprod, hT, hprod]
  let q₀ := pointCoordinate p₀
  let q₁ := pointCoordinate p₁
  have hq₀ : spectrumOfAlgHom q₀ = p₀ := spectrumOf_pointCoordinate p₀
  have hq₁ : spectrumOfAlgHom q₁ = p₁ := spectrumOf_pointCoordinate p₁
  have hs : q₁.toRingHom.comp (coordinateInclusion.{u} A).toRingHom =
      (cellRingEquiv.{u} D).toRingHom.comp q₀.toRingHom := by
    ext1 a
    have ha := congrArg (fun p : WithConv (A →ₐ[R₀] C) => p a) hp
    rw [← hq₁, highPoint_ringEquiv integerAlgEquiv.{u}] at ha
    exact ha
  have hc₀ : IsIso c₀ := integralCellCoordinateMap_isIso (D := D) M.line l r hl hr
  have hcell₀ : IsOpenImmersion p₀.left := by
    have : IsOpenImmersion (cellMap M.line M.torus M.root l r).left := M.openCell l r hl hr
    let : IsIso c₀.left := (Over.forget _).map_isIso c₀
    let : IsIso e.inv.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso e.inv
    change IsOpenImmersion ((c₀.left ≫ (cellMap M.line M.torus M.root l r).left) ≫ e.inv.hom.hom.left)
    infer_instance
  have hcell₁ : IsOpenImmersion p₁.left := by
    rw [← hq₁]
    apply specMap_open_of_ringEquiv q₀.toRingHom q₁.toRingHom
      (coordinateInclusion.{u} A) (cellRingEquiv.{u} D) hs
    rw [← hq₀] at hcell₀
    exact hcell₀
  have hc₁ : IsIso c₁ := integralCellCoordinateMap_isIso (D := E) liftedLine _ _ hl' hr'
  let : IsIso c₁.left := (Over.forget _).map_isIso c₁
  exact (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion c₁.left _).mp hcell₁

private theorem liftedMarking_openCell (l r : List (liftDatum.{u} D).I)
    (hl : OrderedRootProducts.Enumerates l {a | ¬ (liftDatum.{u} D).base.IsPos a})
    (hr : OrderedRootProducts.Enumerates r {a | (liftDatum.{u} D).base.IsPos a}) :
    IsOpenImmersion (cellMap liftedLine.{u} (liftedTorus M e)
      (fun a => liftedRoot M e a.down) l r).left := by
  let j := liftIndex.{u} D
  have h (t : List (liftDatum.{u} D).I) : (t.map j.symm).map (liftIndex.{u} D) = t := by
    change (t.map j.symm).map j = t
    simp [List.map_map]
  have hl' := unlift_enum (fun a => not_congr (liftDatum_pos D a)) l hl
  have hr' := unlift_enum (liftDatum_pos D) r hr
  have h' := liftedCell_open M e (l.map j.symm) (r.map j.symm) hl' hr'
    (by rwa [h]) (by rwa [h])
  have hh := h l
  have hh' := h r
  rw [hh, hh'] at h'
  exact h'

include e in
private theorem highGroup_smooth : Smooth (HighGroup.{u} A).X.hom := by
  apply smooth_extendSpec (R₀ := R₀) (A := A) (R := R.{u})
  have hi : IsIso e.hom.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso e.hom
  have hs : Smooth M.group.X.hom := M.smooth
  have hh : Smooth (e.hom.hom.hom.left ≫ M.group.X.hom) := inferInstance
  change Smooth (HopfSpectrum R₀ A).X.hom
  rw [← Over.w e.hom.hom.hom]
  exact hh

include e in
private theorem highGroup_connected : GeometricallyConnected (HighGroup.{u} A).X.hom := by
  apply connected_extendSpec (R₀ := R₀) (A := A) (R := R.{u})
  have hi : IsIso e.hom.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso e.hom
  have hc : GeometricallyConnected M.group.X.hom := M.connected
  have hh : GeometricallyConnected (e.hom.hom.hom.left ≫ M.group.X.hom) :=
    MorphismProperty.RespectsIso.precomp @GeometricallyConnected _ _ hc
  change GeometricallyConnected (HopfSpectrum R₀ A).X.hom
  rw [← Over.w e.hom.hom.hom]
  exact hh

private def liftedMarking : IntegralMarking (liftDatum.{u} D) where
  group := HighGroup.{u} A
  affine := by
    change IsAffine (Spec (CommRingCat.of (liftRing R₀ R.{u} A)))
    infer_instance
  locallyOfFinitePresentation := by
    let : Smooth (HighGroup.{u} A).X.hom := highGroup_smooth M e
    infer_instance
  quasiCompact := by
    change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R.{u} (liftRing R₀ R.{u} A))))
    infer_instance
  smooth := highGroup_smooth M e
  connected := highGroup_connected M e
  line := liftedLine
  torus := liftedTorus M e
  torusClosed := liftTorus_closed M e
  root a := liftedRoot M e a.down
  rootClosed a := liftRoot_closed M e a.down
  conjugation C t a z := liftConjugation M e C t a.down z
  openCell := liftedMarking_openCell M e
  rankOne a := liftedRankOne M e a.down
  rankOneUpper a := liftRankOneUpper M e a.down
  rankOneLower a := liftRankOneLower M e a.down
  rankOneDiagonal a := liftRankOneDiagonal M e a.down

end Marking

/-- Every field fibre of the specified scalar extension is split with full datum of type F₄. -/
theorem splitFibre : F4LiftedChevalleySpecification.Statement.{u} := by
  intro S A _ _ e k _
  exact fieldPair_of_lifted_marking S (liftedMarking S.chevalley.toIntegralMarking e)
    (Iso.refl _) k

end

end LinearAlgebraicGroups.Arithmetic.F4LiftedChevalley
