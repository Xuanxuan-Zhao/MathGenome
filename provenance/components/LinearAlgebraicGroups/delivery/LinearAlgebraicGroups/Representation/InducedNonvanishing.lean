import Specs.LinearAlgebraicGroups.Representation.InducedNonvanishing
import Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import LinearAlgebraicGroups.Classification.CentralIsogenies
import LinearAlgebraicGroups.Reductive.CentralDerived
import LinearAlgebraicGroups.Representation.InducedSocle
import LinearAlgebraicGroups.Representation.ParabolicLineWeights
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Unramified.LocalStructure
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.EtaleNormality
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Opposite TopologicalSpace Coalgebra WithConv
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Representation.InducedNonvanishing

open _root_.LinearAlgebraicGroups.Specs
open AbstractPairing (Datum IsAttachedCoroot)
open CentralIsogenies (IsCentralIsogeny)
open CharacterDescent (Character)
open FlagLineBundle (OppositeBorelPair covariantFunctions)
open Specs.InducedNonvanishing (Dominant)
open RootWeightAction (IsDominant)


noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private theorem identity_isogeny (G : AffineAlgebraicGroup k) :
    IsCentralIsogeny (𝟙 G.val) := by
  let j : Grp.trivial (SchemeOver k) ⟶ G.val := default
  have hj : j.hom.hom = η[G.val.X] := rfl
  have hclosed : IsClosedImmersion j.hom.hom.left := by
    rw [hj]
    exact isClosedImmersion_of_comp_eq_id G.val.X.hom _ (Over.w η[G.val.X])
  let N : ClosedSubgroup G.val := ⟨Grp.trivial (SchemeOver k), j, hclosed⟩
  refine ⟨inferInstanceAs (IsFinite (𝟙 G.val.X.left)),
    inferInstanceAs (Flat (𝟙 G.val.X.left)),
    inferInstanceAs (Surjective (𝟙 G.val.X.left)), N, ?_, ?_⟩
  · change IsPullback j.hom.hom (toUnit (𝟙_ (SchemeOver k))) (𝟙 G.val.X) η[G.val.X]
    rw [hj, show toUnit (𝟙_ (SchemeOver k)) = 𝟙 (𝟙_ (SchemeOver k)) from
      (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _]
    exact (IsPullback.of_id_fst (f := η[G.val.X])).flip
  · change Centralizes (𝟙 G.val) j.hom.hom
    rw [hj]
    have hs : snd G.val.X (𝟙_ (SchemeOver k)) = toUnit (G.val.X ⊗ (𝟙_ (SchemeOver k))) :=
      (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
    change (snd G.val.X (𝟙_ (SchemeOver k)) ≫ η[G.val.X]) *
      (fst G.val.X (𝟙_ (SchemeOver k)) ≫ 𝟙 _) *
      (snd G.val.X (𝟙_ (SchemeOver k)) ≫ η[G.val.X])⁻¹ =
        fst G.val.X (𝟙_ (SchemeOver k)) ≫ 𝟙 _
    rw [hs]
    change 1 * _ * (1 : G.val.X ⊗ (𝟙_ (SchemeOver k)) ⟶ G.val.X)⁻¹ = _
    simp

/-- The intrinsic dominance condition agrees with testing the coroots
of the attached root datum. -/
theorem dominant_iff_datum (comparison : Specs.CentralIsogenies.CentralIsogenyComparison.{u}) (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) (χ : Character P.torus.group) :
    Dominant P χ ↔ IsDominant D P.positive χ := by
  constructor
  · intro h α
    have he := D.pairing_eq χ (Additive.toMul (D.rootDatum.coroot α.val))
    change D.rootDatum.toLinearMap (Additive.ofMul χ) (D.rootDatum.coroot α.val) = _ at he
    change 0 ≤ D.rootDatum.toLinearMap (Additive.ofMul χ) (D.rootDatum.coroot α.val)
    rw [he]
    exact h α _ (D.attached α.val)
  · intro h α c hc
    have hcomp := comparison G G P.reductive P.reductive P.torus P.torus P.split P.maximal P.split P.maximal
      (𝟙 G.val) (𝟙 P.torus.group) (identity_isogeny G)
      (by simp) (by change Surjective (𝟙 P.torus.group.X.left); infer_instance)
    have he := (hcomp.2.2.2 α.val.val α.val.property
      (by simp [Specs.CentralIsogenies.characterPullback])).2
      (Additive.toMul (D.rootDatum.coroot α.val)) c (D.attached α.val) hc
    change Additive.toMul (D.rootDatum.coroot α.val) ≫ 𝟙 P.torus.group = c at he
    rw [Category.comp_id] at he
    rw [← he, ← D.pairing_eq]
    exact h α

/-- In the E04 covariance model, a nonzero induced module forces dominance
of the inducing character. -/
theorem dominant_of_nontrivial (comparison : Specs.CentralIsogenies.CentralIsogenyComparison.{u}) (P : OppositeBorelPair G) (χ : Character P.torus.group)
    (A : HopfAlgebraCategory k) (e : specGroup A ≅ G.val)
    {D : HopfAlgebraCategory k} (q : A ⟶ D) (c : GroupLike k D)
    (ρ : RightComodule k A (covariantFunctions q c))
    (hsocle : Specs.InducedSocle.SocleProperties P χ A e q c ρ)
    (hne : Nontrivial (covariantFunctions q c)) : Dominant P χ := by
  obtain ⟨I, hI, hDec, b, U, hU, comm, R, ey, base, hb, σ, ha, hev, hn⟩ := hsocle
  letI := comm
  obtain ⟨v, hv, hline, hweight, hdom, _⟩ := hn hne
  exact (dominant_iff_datum comparison P R χ).mpr hdom


open FlagLineBundle
open AdjointRepresentation (GroupPoints)

private theorem zero_coordinate_at_point {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val)
    (R : TestAlgebra k) (g : GroupPoints G.val R) :
    g ≫ (e.inv.hom.hom ≫ linePoint (CommAlgCat.of k A) (0 : A)) = linePoint R 0 := by
  let z : (testSpec k).obj (op R) ⟶ (testSpec k).obj (op (CommAlgCat.of k A)) :=
    g ≫ e.inv.hom.hom
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let map : op R ⟶ op (CommAlgCat.of k A) := ff.preimage z
  have hm : (testSpec k).map map = z := ff.map_preimage z
  change z ≫ linePoint (CommAlgCat.of k A) (0 : A) = linePoint R 0
  rw [← hm]
  unfold linePoint
  rw [← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext
  simp [map]

/-- A covariant regular function that is nonzero at the identity gives a
nonzero section in any of the coordinate presentations used by E04. -/
theorem nontrivial_of_covariant_function
    (hComparison : SchemeCovarianceComparison.{u})
    (P : OppositeBorelPair G) (p : BorelProjection P)
    (χ : Character P.torus.group) {A D : HopfAlgebraCategory k}
    (e : specGroup A ≅ G.val) (d : specGroup D ≅ P.negative.group)
    (q : A ⟶ D) (φ : DiagonalizableGroups.groupAlgebra k
      DiagonalizableGroups.IntegerCharacters ⟶ D)
    (hq : specGroupMap q ≫ e.hom = d.hom ≫ P.negative.inclusion)
    (hφ : specGroupMap φ = d.hom ≫ p.projection ≫ χ)
    (c : GroupLike k D) (hc : (c : D) = characterCoordinate φ)
    (f : G.val.X ⟶ affineLine k) (hf : SchemeCovariant p χ f)
    (z : k) (hz : z ≠ 0) (he : (1 : GroupPoints G.val (CommAlgCat.of k k)) ≫ f =
      linePoint (CommAlgCat.of k k) z) : Nontrivial (covariantFunctions q c) := by
  obtain ⟨F, hF, hcov⟩ := hComparison p χ e d q φ hq hφ c hc
  obtain ⟨a, rfl⟩ := F.surjective f
  have ha : a ∈ covariantFunctions q c := (hcov a).mpr hf
  have hne : a ≠ 0 := by
    rintro rfl
    rw [hF, zero_coordinate_at_point] at he
    have h := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective he
    have h' := congrArg (fun f => f.unop.hom (Polynomial.X (R := k))) h
    exact hz (by simpa [linePoint] using h'.symm)
  exact ⟨⟨⟨a, ha⟩, 0, fun h ↦ hne (congrArg Subtype.val h)⟩⟩

section RingGeometry
variable {X : Scheme.{u}}

private theorem germ_restrict (U : X.Opens) [IsIntegral X] [Nonempty U] [Nonempty (⊤ : X.Opens)] (b : Γ(X, ⊤)) :
    algebraMap Γ(X, U) X.functionField
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op b) =
    algebraMap Γ(X, ⊤) X.functionField b := by
  change (X.germToFunctionField U) (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op b) =
    (X.germToFunctionField ⊤) b
  exact ConcreteCategory.congr_hom
    (X.presheaf.germ_res (homOfLE (show U ≤ ⊤ from le_top)) _ _) b

/-- A regular function on a nonempty affine open of a normal integral affine
scheme extends if a positive power already extends. -/
private theorem extends_of_pow_extends [IsIntegral X] [IsAffine X]
    [IsIntegrallyClosed Γ(X, ⊤)] (U : X.Opens) [Nonempty U]
    (f : Γ(X, U)) (n : ℕ) (hn : 0 < n) (b : Γ(X, ⊤))
    (hb : X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op b = f ^ n) :
    ∃ a : Γ(X, ⊤), X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a = f := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩
  letI := functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  let fK := algebraMap Γ(X, U) X.functionField f
  have hpow : fK ^ n = algebraMap Γ(X, ⊤) X.functionField b := by
    rw [← germ_restrict U b, hb, map_pow]
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hn
    (hpow.symm ▸ isIntegral_algebraMap (R := Γ(X, ⊤)) (A := X.functionField) (x := b))
  refine ⟨a, X.germToFunctionField_injective U ?_⟩
  change algebraMap Γ(X, U) X.functionField
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a) = fK
  rwa [germ_restrict]

private theorem appTop_factor {Y : Scheme.{u}} (m : Y ⟶ X) [IsOpenImmersion m] :
    m.appTop = X.presheaf.map (homOfLE (show m ''ᵁ (⊤ : Y.Opens) ≤ ⊤ from le_top)).op ≫
      (m.appIso ⊤).hom := by
  rw [m.appIso_hom', m.map_appLE]
  exact m.app_eq_appLE (U := ⊤)

/-- Restriction along a nonempty open immersion into a normal integral affine
scheme detects whether a function has a global positive power. -/
private theorem restrict_of_pow_restrict [IsIntegral X] [IsAffine X]
    [IsIntegrallyClosed Γ(X, ⊤)] {Y : Scheme.{u}} [Nonempty Y]
    (m : Y ⟶ X) [IsOpenImmersion m]
    (f : Γ(Y, ⊤)) (n : ℕ) (hn : 0 < n) (b : Γ(X, ⊤))
    (hb : m.appTop b = f ^ n) :
    ∃ a : Γ(X, ⊤), m.appTop a = f := by
  let U := m ''ᵁ (⊤ : Y.Opens)
  letI : Nonempty U := ⟨⟨m (Nonempty.some inferInstance), by simp [U]⟩⟩
  let e := m.appIso (⊤ : Y.Opens)
  have he (x : Γ(X, ⊤)) :
      e.inv (m.appTop x) = X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op x := by
    rw [appTop_factor]
    exact e.hom_inv_id_apply _
  obtain ⟨a, ha⟩ := extends_of_pow_extends U (e.inv f) n hn b (by
    rw [← he b, hb, map_pow])
  refine ⟨a, ?_⟩
  apply e.commRingCatIsoToRingEquiv.symm.injective
  exact (he a).trans ha

/-- Pullback along a nonempty open immersion of affine schemes is injective
on functions when the target is integral. -/
private theorem appTop_injective_of_nonempty_open [IsIntegral X] {Y : Scheme.{u}} [Nonempty Y]
    (m : Y ⟶ X) [IsOpenImmersion m] : Function.Injective m.appTop := by
  rw [appTop_factor]
  letI : Nonempty (m ''ᵁ (⊤ : Y.Opens)) := ⟨⟨m (Nonempty.some inferInstance), by simp⟩⟩
  exact (m.appIso ⊤).commRingCatIsoToRingEquiv.injective.comp
    (map_injective_of_isIntegral X (homOfLE le_top))

/-- The ring map underlying a nonempty open immersion of affine spectra
has image closed under taking a positive power root when the source ring
is an integrally closed domain. -/
private theorem preimage_of_pow_mem_range {R S : CommRingCat.{u}} [IsDomain R]
    [IsIntegrallyClosed R] [Nontrivial S] (i : R ⟶ S)
    [IsOpenImmersion (Spec.map i)] (s : S) (n : ℕ) (hn : 0 < n) (r : R)
    (hr : i r = s ^ n) : ∃ r' : R, i r' = s := by
  let eR := Scheme.ΓSpecIso R
  let eS := Scheme.ΓSpecIso S
  letI : IsIntegrallyClosed Γ(Spec R, ⊤) :=
    IsIntegrallyClosed.of_equiv eR.commRingCatIsoToRingEquiv.symm
  letI : Nonempty (Spec S) := inferInstanceAs (Nonempty (PrimeSpectrum S))
  have hmap (a : R) : (Spec.map i).appTop (eR.inv a) = eS.inv (i a) :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality i).symm a
  obtain ⟨a, ha⟩ := restrict_of_pow_restrict (Spec.map i) (eS.inv s) n hn (eR.inv r) (by
    rw [hmap, hr, map_pow])
  refine ⟨eR.hom a, ?_⟩
  have ha' := hmap (eR.hom a)
  rw [eR.hom_inv_id_apply, ha] at ha'
  exact eS.commRingCatIsoToRingEquiv.symm.injective ha'.symm

private theorem specMap_injective_of_nonempty_open {R S : CommRingCat.{u}} [IsDomain R]
    [Nontrivial S] (i : R ⟶ S) [IsOpenImmersion (Spec.map i)] : Function.Injective i := by
  letI : Nonempty (Spec S) := inferInstanceAs (Nonempty (PrimeSpectrum S))
  intro a b hab
  apply (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.injective
  apply appTop_injective_of_nonempty_open (Spec.map i)
  have h (x : R) : (Spec.map i).appTop ((Scheme.ΓSpecIso R).inv x) =
      (Scheme.ΓSpecIso S).inv (i x) :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality i).symm x
  change (Spec.map i).appTop ((Scheme.ΓSpecIso R).inv a) =
    (Spec.map i).appTop ((Scheme.ΓSpecIso R).inv b)
  rw [h, h, hab]

end RingGeometry

/-- If a covariant function on a right-stable affine open has a positive
power defined globally, it extends globally with the original covariance.
The compatibility of the two coactions encodes right stability of the open. -/
theorem extend_covariant_from_power {k : Type u} [Field k]
    {A D : HopfAlgebraCategory k} (q : A ⟶ D) (c : GroupLike k D)
    [IsDomain A] [IsIntegrallyClosed A] {S : Type u} [CommRing S] [Algebra k S] [Nontrivial S]
    (j : A →ₐ[k] S)
    (hj : IsOpenImmersion (Spec.map (CommRingCat.ofHom j.toRingHom)))
    (rightAction : S →ₐ[k] S ⊗[k] D)
    (hAction : ∀ a : A, rightAction (j a) = j.toLinearMap.rTensor D
      (q.hom.toAlgHom.toLinearMap.lTensor A (comul (R := k) a)))
    (f : S) (hf : f ≠ 0) (hCov : rightAction f = f ⊗ₜ[k] (↑(c⁻¹) : D))
    (n : ℕ) (hn : 0 < n) (a : A) (ha : j a = f ^ n) :
    ∃ g : covariantFunctions q c, g ≠ 0 ∧ j (g : A) = f := by
  let i := CommRingCat.ofHom j.toRingHom
  letI : IsOpenImmersion (Spec.map i) := hj
  have hji : Function.Injective j := specMap_injective_of_nonempty_open i
  obtain ⟨b, hb⟩ := preimage_of_pow_mem_range i f n hn a ha
  change j b = f at hb
  have hmem : b ∈ covariantFunctions q c := by
    change q.hom.toAlgHom.toLinearMap.lTensor A (comul (R := k) b) =
      b ⊗ₜ[k] (↑(c⁻¹) : D)
    apply Module.Flat.rTensor_preserves_injective_linearMap j.toLinearMap hji
    rw [← hAction, hb, hCov, LinearMap.rTensor_tmul]
    rw [AlgHom.toLinearMap_apply, hb]
  refine ⟨⟨b, hmem⟩, ?_, hb⟩
  intro hz
  have hz' : b = 0 := congrArg Subtype.val hz
  exact hf (hb.symm.trans (hz' ▸ map_zero j))


section ProductChart

open Algebra.TensorProduct Bialgebra

variable {k : Type u} [Field k] {A D : HopfAlgebraCategory k}
variable {S : Type u} [CommRing S] [Algebra k S]

/-- Pullback by the multiplication map from the left factor and the
subgroup used for covariance. -/
noncomputable def multiplicationCoordinates (r : A →ₐ[k] S) (q : A ⟶ D) :
    A →ₐ[k] S ⊗[k] D :=
  (Algebra.TensorProduct.map r q.hom.toAlgHom).comp (comulAlgHom k A)

private noncomputable def rightActionCoordinates (S : Type u) [CommRing S] [Algebra k S]
    (D : HopfAlgebraCategory k) : (S ⊗[k] D) →ₐ[k] (S ⊗[k] D) ⊗[k] D :=
  (Algebra.TensorProduct.assoc k k k S D D).symm.toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id k S) (comulAlgHom k D))

private theorem multiplicationCoordinates_intertwines (r : A →ₐ[k] S) (q : A ⟶ D) (a : A) :
    rightActionCoordinates S D (multiplicationCoordinates r q a) =
      (multiplicationCoordinates r q).toLinearMap.rTensor D
        (q.hom.toAlgHom.toLinearMap.lTensor A (comul (R := k) a)) := by
  let l := r.toLinearMap
  let d := q.hom.toAlgHom.toLinearMap
  have hd : (comul (R := k)).comp d =
      (TensorProduct.map d d).comp (comul (R := k)) := (CoalgHomClass.map_comp_comul q.hom).symm
  change (TensorProduct.assoc k S D D).symm
      (TensorProduct.map LinearMap.id (comul (R := k))
        (TensorProduct.map l d (comul (R := k) a))) =
    ((TensorProduct.map l d).comp (comul (R := k))).rTensor D
      (d.lTensor A (comul (R := k) a))
  rw [TensorProduct.map_map, LinearMap.id_comp, hd,
    ← LinearMap.map_lTensor A l (TensorProduct.map d d) (comul (R := k)),
    ← TensorProduct.map_map_assoc_symm, Coalgebra.coassoc_symm_apply,
    LinearMap.map_rTensor]
  exact (LinearMap.congr_fun (LinearMap.rTensor_comp_lTensor A
    ((TensorProduct.map l d).comp (comul (R := k))) d) (comul (R := k) a)).symm

/-- A global covariant function for the positive power of a character,
normalized to one on the left factor, yields a nonzero global covariant
function for the character itself. -/
theorem extend_covariant_from_product_chart
    [IsDomain A] [IsIntegrallyClosed A] [Nontrivial S]
    (r : A →ₐ[k] S) (q : A ⟶ D) (c : GroupLike k D)
    (hj : IsOpenImmersion (Spec.map (CommRingCat.ofHom (multiplicationCoordinates r q).toRingHom)))
    (n : ℕ) (hn : 0 < n)
    (f : covariantFunctions q (c ^ n)) (hf : r (f : A) = 1) :
    ∃ g : covariantFunctions q c, g ≠ 0 ∧ r (g : A) = 1 := by
  let ε := (Algebra.ofId k S).comp (counitAlgHom k D)
  let s := Algebra.TensorProduct.lift (AlgHom.id k S) ε (fun _ _ ↦ Commute.all _ _)
  letI : Nontrivial (S ⊗[k] D) := s.toRingHom.domain_nontrivial
  let b : D := (c⁻¹ : GroupLike k D)
  let f₀ : S ⊗[k] D := (1 : S) ⊗ₜ[k] b
  have hf₀ : f₀ ≠ 0 :=
    (((c⁻¹ : GroupLike k D).2.isUnit).map
      (Algebra.TensorProduct.includeRight : D →ₐ[k] S ⊗[k] D)).ne_zero
  have hff := f.property
  change q.hom.toAlgHom.toLinearMap.lTensor A (comul (R := k) (f : A)) =
    (f : A) ⊗ₜ[k] (↑((c ^ n)⁻¹ : GroupLike k D) : D) at hff
  have hpow : multiplicationCoordinates r q (f : A) = f₀ ^ n := by
    change TensorProduct.map r.toLinearMap q.hom.toAlgHom.toLinearMap (comul (R := k) (f : A)) = _
    rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hff, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply, hf, ← inv_pow, GroupLike.val_pow]
    simpa only [one_pow, f₀] using (Algebra.TensorProduct.tmul_pow (R := k) (1 : S) b n).symm
  have hCov : rightActionCoordinates S D f₀ = f₀ ⊗ₜ[k] b := by
    simp only [rightActionCoordinates, AlgHom.comp_apply, f₀, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, comulAlgHom_apply, b, (c⁻¹ : GroupLike k D).2.comul_eq_tmul_self,
      AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.assoc_symm_tmul]
  obtain ⟨g, hg, hrestrict⟩ := extend_covariant_from_power q c
    (multiplicationCoordinates r q) hj (rightActionCoordinates S D)
    (multiplicationCoordinates_intertwines r q) f₀ hf₀ hCov n hn (f : A) hpow
  refine ⟨g, hg, ?_⟩
  have he (a : A) : s (multiplicationCoordinates r q a) = r a := by
    have hmap (x : A ⊗[k] A) :
        s (TensorProduct.map r.toLinearMap q.hom.toAlgHom.toLinearMap x) =
          r (TensorProduct.rid k A
            ((counit (R := k) (A := A)).lTensor A x)) := by
      refine TensorProduct.inductionOn x ?_ ?_
      · intro x y
        simp [s, ε, Algebra.smul_def, mul_comm, CoalgHomClass.counit_comp_apply]
      · intro x y hx hy
        simp only [map_add, hx, hy]
    change s (TensorProduct.map r.toLinearMap q.hom.toAlgHom.toLinearMap
      (comul (R := k) a)) = r a
    rw [hmap, Coalgebra.lTensor_counit_comul]
    simp
  rw [← he, hrestrict]
  change s ((1 : S) ⊗ₜ[k] b) = 1
  simp [s, ε, b]

end ProductChart

section PowerCovariance

open RootWeightAction (Representation act extendVector IsPrimitive fixedSpace mem_fixedSpace)
open CharacterPairing (characterValue)
open DiagonalizableGroups (groupAlgebra IntegerCharacters integerGenerator)
open CharacterDescent (groupLikeCharacterEquiv)
open private act_mul act_one act_smul act_extend_natural characterValue_mul characterValue_one
  characterValue_comp characterValue_natural primitiveLine
  from LinearAlgebraicGroups.Representation.RootWeightAction
open private characterValue_unit multiplicativeGroup_isOfMultiplicativeType
  from LinearAlgebraicGroups.Representation.ParabolicLineWeights
open private unitEquiv from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private schemeKernel_eq_iff from LinearAlgebraicGroups.Classification.CentralIsogenies
open private postMul from LinearAlgebraicGroups.Reductive.CentralDerived
open private integerHopfHomEquiv integerHopfHomEquiv_generator
  from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private coordinateFunction eval_coordinateFunction transport_point_surjective
  linePointEquiv inverseCharacterValue schemeCovariant_iff
  from LinearAlgebraicGroups.Representation.FlagLineBundle

private theorem character_power {D : HopfAlgebraCategory k} {P : OppositeBorelPair G}
    (p : BorelProjection P) (χ : Character P.torus.group)
    (d : specGroup D ≅ P.negative.group) (φ : groupAlgebra k IntegerCharacters ⟶ D)
    (hφ : specGroupMap φ = d.hom ≫ p.projection ≫ χ)
    (c : GroupLike k D) (hc : (c : D) = characterCoordinate φ) (n : ℕ) :
    ∃ φ' : groupAlgebra k IntegerCharacters ⟶ D,
      specGroupMap φ' = d.hom ≫ p.projection ≫ χ ^ n ∧
      (↑(c ^ n) : D) = characterCoordinate φ' := by
  let φ' := integerHopfHomEquiv D (c ^ n)
  have h : integerHopfHomEquiv D c = φ := by
    apply (integerHopfHomEquiv D).symm.injective
    rw [Equiv.symm_apply_apply]
    exact GroupLike.val_injective hc
  refine ⟨φ', ?_, (integerHopfHomEquiv_generator D (c ^ n)).symm⟩
  change groupLikeCharacterEquiv D (c ^ n) = d.hom ≫ p.projection ≫ χ ^ n
  rw [map_pow, show groupLikeCharacterEquiv D c = specGroupMap φ from
    congrArg specGroupMap h, hφ]
  exact (map_pow (Specs.CentralIsogenies.characterPullback (d.hom ≫ p.projection)) χ n).symm

private theorem characterValue_inverse {T : GroupScheme k} (χ : Character T)
    (R : TestAlgebra k) (t : GroupPoints T R) :
    characterValue χ⁻¹ R t = characterValue χ R t⁻¹ := by
  have he : t ≫ (χ⁻¹ : Character T).hom.hom = t⁻¹ ≫ χ.hom.hom :=
    (congrArg (fun a ↦ t ≫ a) (Grp.Hom.hom_hom_inv χ)).trans
      ((GrpObj.comp_inv t χ.hom.hom).trans (GrpObj.inv_comp t χ.hom.hom).symm)
  unfold characterValue
  simp only [he]
  rfl

private theorem characterValue_point_mul {H : GroupScheme k} (ξ : Character H)
    (R : TestAlgebra k) (g h : GroupPoints H R) :
    characterValue ξ R (g * h) = characterValue ξ R g * characterValue ξ R h := by
  simp only [characterValue_unit]
  have hmul := postMul ξ g h
  calc
    (unitEquiv R ((g * h) ≫ ξ.hom.hom) : R) =
      (unitEquiv R ((g ≫ ξ.hom.hom) * (h ≫ ξ.hom.hom)) : R) :=
        congrArg (fun z ↦ (unitEquiv R z : R)) hmul
    _ = _ := congrArg Units.val (map_mul (unitEquiv R) _ _)

private theorem characterValue_identity {H : GroupScheme k} (ξ : Character H)
    (R : TestAlgebra k) : characterValue ξ R 1 = 1 := by
  rw [characterValue_unit]
  exact (congrArg (fun z ↦ (unitEquiv R z : R)) (MonObj.one_comp ξ.hom.hom)).trans
    (congrArg Units.val (map_one (unitEquiv R)))

private theorem character_from_borel_projection {P : OppositeBorelPair G}
    (p : BorelProjection P) (ξ : Character G.val) :
    P.negative.inclusion ≫ ξ = p.projection ≫ P.torus.inclusion ≫ ξ := by
  let h := P.negative.inclusion ≫ ξ
  let U := Unipotent.closedSubgroupAlgebraicGroup
    (G := Unipotent.closedSubgroupAlgebraicGroup P.negative) p.radical
  let M := DiagonalizableGroups.diagonalGroup (k := k) IntegerCharacters
  have hk : p.radical.inclusion ≫ h = 0 :=
    LinearAlgebraicGroups.Unipotent.homFromUnipotentToMultiplicativeType U M _
      p.isRadical.2.1 multiplicativeGroup_isOfMultiplicativeType
  let a := p.projection.hom.hom ≫ p.inclusion.hom.hom
  have ha : a ≫ p.projection.hom.hom = (𝟙 _) ≫ p.projection.hom.hom := by
    dsimp only [a]
    have he := congrArg (fun j : P.torus.group ⟶ P.torus.group ↦ j.hom.hom) p.section_projection
    rw [Grp.comp_hom_hom] at he
    change p.inclusion.hom.hom ≫ p.projection.hom.hom = 𝟙 _ at he
    simp only [Category.assoc, he, Category.comp_id, Category.id_comp]
  obtain ⟨u, hu⟩ := (schemeKernel_eq_iff p.isKernel a (𝟙 _)).mp ha
  have he : a * (u ≫ p.radical.inclusion.hom.hom) = 𝟙 _ := by
    rw [hu, mul_inv_cancel_left]
  apply Grp.hom_ext
  change h.hom.hom = (p.projection ≫ P.torus.inclusion ≫ ξ).hom.hom
  calc
    h.hom.hom = (a * (u ≫ p.radical.inclusion.hom.hom)) ≫ h.hom.hom := by rw [he, Category.id_comp]
    _ = _ := by
      rw [postMul h, Category.assoc u, ← Grp.comp_hom_hom, hk]
      change (a ≫ h.hom.hom) * (u ≫ (1 : _ ⟶ _)) = _
      rw [MonObj.comp_one, mul_one]
      have hi : p.inclusion ≫ h = P.torus.inclusion ≫ ξ := by
        rw [← Category.assoc, p.inclusion_comp]
      change (p.projection.hom.hom ≫ p.inclusion.hom.hom) ≫ h.hom.hom = _
      rw [Category.assoc, ← Grp.comp_hom_hom, hi, Grp.comp_hom_hom]
      rfl

/-- A primitive vector for the opposite Borel, twisted by a character of
the group, gives a covariant matrix coefficient for the inverse weight. -/
private theorem covariant_of_opposite_primitive {P : OppositeBorelPair G}
    (p : BorelProjection P) (χ : Character P.torus.group) {A D : HopfAlgebraCategory k}
    (e : specGroup A ≅ G.val) (d : specGroup D ≅ P.negative.group)
    (q : A ⟶ D) (φ : groupAlgebra k IntegerCharacters ⟶ D)
    (hq : specGroupMap q ≫ e.hom = d.hom ≫ P.negative.inclusion)
    (hφ : specGroupMap φ = d.hom ≫ p.projection ≫ χ)
    (c : GroupLike k D) (hc : (c : D) = characterCoordinate φ)
    (ξ : Character G.val) (ψ : Character P.torus.group)
    (hχ : χ⁻¹ = ψ * (P.torus.inclusion ≫ ξ))
    {I : Type u} [Fintype I] [DecidableEq I] {σ : Representation G.val I} {v : I → k}
    (hv : IsPrimitive σ P.torus P.negative p.radical ψ v) :
    Nontrivial (covariantFunctions q c) := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv.1 (funext h)
  let K := CommAlgCat.of k k
  let generic : GroupPoints G.val (CommAlgCat.of k A) := e.hom.hom.hom
  let x : A := characterValue ξ (CommAlgCat.of k A) generic *
    act σ (CommAlgCat.of k A) generic (extendVector (CommAlgCat.of k A) v) i
  let f := coordinateFunction e x
  have heval (R : TestAlgebra k) (g : GroupPoints G.val R) :
      g ≫ f = linePoint R (characterValue ξ R g * act σ R g (extendVector R v) i) := by
    obtain ⟨a, rfl⟩ := transport_point_surjective e R g
    rw [eval_coordinateFunction]
    apply congrArg (linePoint R)
    rw [show x = _ from rfl, map_mul]
    exact congrArg₂ (· * ·)
      (characterValue_natural ξ (CommAlgCat.ofHom a) generic).symm
      (congrFun (act_extend_natural σ (CommAlgCat.ofHom a) generic v) i).symm
  have hf : SchemeCovariant p χ f := by
    intro R g b z hz
    let g' : GroupPoints G.val R := g
    let b' : GroupPoints P.negative.group R := b
    let bG : GroupPoints G.val R := b' ≫ P.negative.inclusion.hom.hom
    change (g' * bG) ≫ f = linePoint R (characterValue (p.projection ≫ χ) R b'⁻¹ * z)
    have hz' := (linePointEquiv R).injective ((heval R g').symm.trans hz)
    rw [← hz', heval R (g' * bG), act_mul σ R g' bG]
    have hprim := primitiveLine σ P.torus P.negative p.radical p.inclusion p.projection
      p.inclusion_comp p.section_projection p.isKernel ψ v hv R b'
    change act σ R bG (extendVector R v) = _ at hprim
    rw [hprim, act_smul, Pi.smul_apply, smul_eq_mul]
    let t : GroupPoints P.torus.group R := b' ≫ p.projection.hom.hom
    have hcoef : characterValue χ⁻¹ R t = characterValue (p.projection ≫ χ) R b'⁻¹ :=
      (characterValue_inverse χ R t).trans
        ((congrArg (characterValue χ R) (GrpObj.inv_comp b' p.projection.hom.hom).symm).trans
          (characterValue_comp p.projection χ R b'⁻¹).symm)
    have hb : characterValue ξ R bG = characterValue (P.torus.inclusion ≫ ξ) R t := by
      rw [← characterValue_comp P.negative.inclusion ξ R b',
        character_from_borel_projection p ξ]
      exact characterValue_comp p.projection (P.torus.inclusion ≫ ξ) R b'
    apply congrArg (linePoint R)
    change characterValue ξ R (g' * bG) *
      (characterValue ψ R t * act σ R g' (extendVector R v) i) =
        characterValue (p.projection ≫ χ) R b'⁻¹ *
          (characterValue ξ R g' * act σ R g' (extendVector R v) i)
    rw [characterValue_point_mul, hb, ← hcoef, hχ, characterValue_mul]
    ac_rfl
  have he : (1 : GroupPoints G.val K) ≫ f = linePoint K (v i) := by
    rw [heval, act_one, characterValue_identity, one_mul]
    simp [extendVector, K]
  exact nontrivial_of_covariant_function
    LinearAlgebraicGroups.FlagLineBundle.schemeCovarianceComparison
    P p χ e d q φ hq hφ c hc f (by exact hf) (v i) hi he

end PowerCovariance

section NormalizedCovariance

open RootWeightAction (act extendVector mem_fixedSpace)
open Specs.InducedSocle (SocleProperties)
open RationalRepresentations (tensorCoordinate evaluate)
open Specs.GeometricRadicals (IsUnipotentRadical)
open private evaluationLinear evaluationLinear_extend evaluationLinear_tensor pointIso moduleSocle IsLeftTranslation
  from LinearAlgebraicGroups.Representation.InducedSocle
open private subgroupAffine from LinearAlgebraicGroups.Representation.CyclicHighestWeight
open private splitWithSpecifiedRadical from LinearAlgebraicGroups.Flag.OpenCell
open private affinePoint affinePoint_mul affinePoint_specGroupMap
  from LinearAlgebraicGroups.Representation.FlagLineBundle

private theorem normalized_on_radical {P : OppositeBorelPair G} {A D : HopfAlgebraCategory k}
    (χ : Character P.torus.group) (e : specGroup A ≅ G.val) (q : A ⟶ D)
    (c : GroupLike k D) (ρ : RightComodule k A (covariantFunctions q c))
    (htrans : IsLeftTranslation ρ)
    (hsocle : SocleProperties P χ A e q c ρ) (hne : Nontrivial (covariantFunctions q c)) :
    ∃ (U : ClosedSubgroup P.positive.group),
      IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup P.positive) U ∧
      ∃ f : covariantFunctions q c,
        ∀ (S : HopfAlgebraCategory k) (s : specGroup S ≅ U.group) (r : A ⟶ S),
          specGroupMap r ≫ e.hom = s.hom ≫ U.inclusion ≫ P.positive.inclusion →
            r.hom (f : A) = 1 := by
  obtain ⟨I, hI, hDec, b, U, hU, comm, R, ey, base, hb, σ, ha, hev, hn⟩ := hsocle
  obtain ⟨v, hv, hline, _⟩ := hn hne
  let x := b.equivFun.symm v
  let z : k := counit (R := k) (x : A)
  have hfixed : v ∈ RootWeightAction.fixedSpace σ (U.inclusion ≫ P.positive.inclusion) := by
    rw [hline]
    exact Submodule.subset_span (Set.mem_singleton v)
  have hz : z ≠ 0 := by
    intro h
    apply hv
    have eq := hev (a₁ := ⟨v, hfixed⟩) (a₂ := 0) (by
      change z = counit (R := k) (b.equivFun.symm (0 : I → k) : A)
      simpa only [map_zero, Submodule.coe_zero] using h)
    exact congrArg Subtype.val eq
  refine ⟨U, hU, z⁻¹ • x, ?_⟩
  intro S s r hr
  let K := CommAlgCat.of k S
  letI := convolutionGroup A K
  let y : WithConv (A →ₐ[k] K) := toConv r.hom.toAlgHom
  let g : GroupPoints U.group K := s.hom.hom.hom
  have hy : (pointIso e).hom.app K y = g ≫ (U.inclusion ≫ P.positive.inclusion).hom.hom := by
    change (specGroupMap r).hom.hom ≫ e.hom.hom.hom = _
    exact congrArg (fun a : specGroup S ⟶ G.val ↦ a.hom.hom) hr
  have hyinv : (pointIso e).hom.app K (y⁻¹) =
      g⁻¹ ≫ (U.inclusion ≫ P.positive.inclusion).hom.hom := by
    rw [map_inv, hy]
    exact (GrpObj.inv_comp g (U.inclusion ≫ P.positive.inclusion).hom.hom).symm
  have hact :
      act σ K ((pointIso e).hom.app K y⁻¹) (extendVector K v) = extendVector K v := by
    rw [hyinv]
    exact mem_fixedSpace.mp hfixed K g⁻¹
  have hact' : act σ K ((pointIso e).hom.app K y⁻¹) (extendVector K v) =
      fun i ↦ tensorCoordinate b i (evaluate A ρ (y⁻¹).ofConv x) := by
    funext i
    exact ha K _ v i
  have hval := congrArg (evaluationLinear b K) (hact'.symm.trans hact)
  rw [evaluationLinear_extend] at hval
  change evaluationLinear b K (fun i ↦ tensorCoordinate b i
    ((y⁻¹).ofConv.toLinearMap.lTensor _ (ρ.coaction x))) = algebraMap k K z at hval
  rw [evaluationLinear_tensor, htrans K (y⁻¹) 1 x, inv_inv, mul_one] at hval
  change r.hom (x : A) = algebraMap k S z at hval
  change r.hom.toAlgHom (z⁻¹ • (x : A)) = 1
  rw [map_smul, show r.hom.toAlgHom (x : A) = algebraMap k S z from hval,
    Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hz, map_one]

private def radicalBorelMap {P : OppositeBorelPair G} (U : ClosedSubgroup P.positive.group) :
    U.group.X ⊗ P.negative.group.X ⟶ G.val.X :=
  CocharacterDynamics.multiplyFactors (U.inclusion ≫ P.positive.inclusion) P.negative.inclusion

private theorem radicalBorelMap_open {P : OppositeBorelPair G} (p : BorelProjection P)
    (U : ClosedSubgroup P.positive.group)
    (hU : IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup P.positive) U) :
    IsOpenImmersion (radicalBorelMap U).left := by
  have hop : OpenCell.AreOpposite P.torus P.negative P.positive := by
    unfold OpenCell.AreOpposite
    rw [P.opposite, compl_compl]
  have hm := (LinearAlgebraicGroups.Flag.OpenCell.openCell G P.reductive P.torus P.split
    P.maximal P.negative P.positive P.negativeBorel P.positiveBorel P.inNegative P.inPositive
    hop U p.radical hU p.isRadical).1
  obtain ⟨_, _, _, _, _, _, hd⟩ :=
    LinearAlgebraicGroups.RootData.BorelPositivity.borelPositivity G P.reductive P.torus P.split P.maximal
  obtain ⟨j, hj, hiso⟩ := splitWithSpecifiedRadical
    (hd P.negative P.negativeBorel P.inNegative) p.isRadical
  letI := P.negative.isClosedImmersion
  letI : Mono P.negative.inclusion.hom.hom := Over.mono_of_mono_left _
  have hji : j = p.inclusion := by
    apply Grp.hom_ext
    apply (cancel_mono P.negative.inclusion.hom.hom).mp
    exact congrArg (fun f : P.torus.group ⟶ G.val ↦ f.hom.hom) (hj.trans p.inclusion_comp.symm)
  subst j
  let m := CocharacterDynamics.multiplyFactors p.inclusion p.radical.inclusion
  have he : (U.group.X ◁ m) ≫ radicalBorelMap U = OpenCell.cellMap P.torus U p.radical := by
    have hp := congrArg (fun f : P.torus.group ⟶ G.val ↦ f.hom.hom) p.inclusion_comp
    rw [Grp.comp_hom_hom] at hp
    simp only [radicalBorelMap, OpenCell.cellMap, CocharacterDynamics.multiplyFactors, m,
      MonObj.comp_mul, MonObj.mul_comp, Category.assoc, whiskerLeft_fst_assoc,
      whiskerLeft_snd_assoc, hp, Grp.comp_hom_hom]
  letI : IsIso m := hiso
  haveI : IsIso (U.group.X ◁ m).left :=
    (Over.forget (Spec (CommRingCat.of k))).map_isIso (U.group.X ◁ m)
  have he' : (U.group.X ◁ m).left ≫ (radicalBorelMap U).left =
      (OpenCell.cellMap P.torus U p.radical).left := congrArg (fun f ↦ f.left) he
  exact ((MorphismProperty.cancel_left_of_respectsIso (P := @IsOpenImmersion) _ _).mp
    (he'.symm ▸ hm))

open Bialgebra Algebra.TensorProduct

private def spectrumTensorIso (S D : TestAlgebra k) :
    ((testSpec k).obj (op S) ⊗ (testSpec k).obj (op D)) ≅
      (testSpec k).obj (op (CommAlgCat.of k (S ⊗[k] D))) :=
  Over.isoMk (pullbackSpecIso (CommRingCat.of k) S D) (by
    let a := (testSpec k).map (CommAlgCat.ofHom (includeLeft : S →ₐ[k] S ⊗[k] D)).op
    let p := fst ((testSpec k).obj (op S)) ((testSpec k).obj (op D))
    let e := pullbackSpecIso (CommRingCat.of k) S D
    have h : e.hom ≫ a.left = p.left := pullbackSpecIso_hom_fst (CommRingCat.of k) S D
    exact (congrArg (fun x ↦ e.hom ≫ x) (Over.w a).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun x ↦ x ≫ ((testSpec k).obj (op S)).hom) h).trans (Over.w p))))

private theorem spectrumTensorIso_left (S D : TestAlgebra k) :
    (spectrumTensorIso S D).hom.left = (pullbackSpecIso (CommRingCat.of k) S D).hom :=
  rfl

private theorem spectrum_tensor_fst (S D : TestAlgebra k) :
    (spectrumTensorIso S D).hom ≫
      (testSpec k).map (CommAlgCat.ofHom (includeLeft : S →ₐ[k] S ⊗[k] D)).op =
      fst ((testSpec k).obj (op S)) ((testSpec k).obj (op D)) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, spectrumTensorIso_left]
  exact pullbackSpecIso_hom_fst (CommRingCat.of k) S D

private theorem spectrum_tensor_snd (S D : TestAlgebra k) :
    (spectrumTensorIso S D).hom ≫
      (testSpec k).map (CommAlgCat.ofHom (includeRight : D →ₐ[k] S ⊗[k] D)).op =
      snd ((testSpec k).obj (op S)) ((testSpec k).obj (op D)) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, spectrumTensorIso_left]
  exact pullbackSpecIso_hom_snd (CommRingCat.of k) S D

private theorem multiplicationCoordinates_spec {P : OppositeBorelPair G}
    {A D S : HopfAlgebraCategory k} {U : ClosedSubgroup P.positive.group}
    (e : specGroup A ≅ G.val) (d : specGroup D ≅ P.negative.group)
    (s : specGroup S ≅ U.group) (r : A ⟶ S) (q : A ⟶ D)
    (hr : specGroupMap r ≫ e.hom = s.hom ≫ U.inclusion ≫ P.positive.inclusion)
    (hq : specGroupMap q ≫ e.hom = d.hom ≫ P.negative.inclusion) :
    (spectrumTensorIso (CommAlgCat.of k S) (CommAlgCat.of k D)).hom ≫
      (testSpec k).map (CommAlgCat.ofHom (multiplicationCoordinates r.hom.toAlgHom q)).op ≫
        e.hom.hom.hom =
      (s.hom.hom.hom ⊗ₘ d.hom.hom.hom) ≫ radicalBorelMap U := by
  let K := CommAlgCat.of k (S ⊗[k] D)
  let l : S →ₐ[k] S ⊗[k] D := includeLeft
  let b : D →ₐ[k] S ⊗[k] D := includeRight
  letI := convolutionGroup A K
  let g : WithConv (A →ₐ[k] K) := toConv (l.comp r.hom.toAlgHom)
  let h : WithConv (A →ₐ[k] K) := toConv (b.comp q.hom.toAlgHom)
  have hm : (g * h).ofConv = multiplicationCoordinates r.hom.toAlgHom q := by
    have ht : (Algebra.TensorProduct.lift g.ofConv h.ofConv (fun _ _ ↦ Commute.all _ _)) =
        Algebra.TensorProduct.map r.hom.toAlgHom q.hom.toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro x y
      rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul]
      change (r.hom.toAlgHom x ⊗ₜ[k] (1 : D)) * ((1 : S) ⊗ₜ[k] q.hom.toAlgHom y) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    ext x
    rw [show (g * h).ofConv x = (g * h) x from rfl, AlgHom.convMul_apply, ht]
    rfl
  have hg : affinePoint K g.ofConv ≫ e.hom.hom.hom =
      affinePoint K l ≫ s.hom.hom.hom ≫ (U.inclusion ≫ P.positive.inclusion).hom.hom := by
    change affinePoint K (l.comp r.hom.toAlgHom) ≫ e.hom.hom.hom = _
    rw [← affinePoint_specGroupMap K r l]
    have he := congrArg (fun a : specGroup S ⟶ G.val ↦ a.hom.hom) hr
    simp only [Grp.comp_hom_hom] at he
    rw [Category.assoc, he, Grp.comp_hom_hom]
  have hh : affinePoint K h.ofConv ≫ e.hom.hom.hom =
      affinePoint K b ≫ d.hom.hom.hom ≫ P.negative.inclusion.hom.hom := by
    change affinePoint K (b.comp q.hom.toAlgHom) ≫ e.hom.hom.hom = _
    rw [← affinePoint_specGroupMap K q b]
    have he := congrArg (fun a : specGroup D ⟶ G.val ↦ a.hom.hom) hq
    rw [Grp.comp_hom_hom, Grp.comp_hom_hom] at he
    rw [Category.assoc, he]
  let τ := (spectrumTensorIso (CommAlgCat.of k S) (CommAlgCat.of k D)).hom
  change τ ≫ affinePoint K (multiplicationCoordinates r.hom.toAlgHom q) ≫ e.hom.hom.hom = _
  rw [← hm, affinePoint_mul, MonObj.mul_comp, hg, hh, MonObj.comp_mul]
  simp only [radicalBorelMap, CocharacterDynamics.multiplyFactors, MonObj.comp_mul, ← Category.assoc]
  rw [show τ ≫
    affinePoint K l = _ from spectrum_tensor_fst (CommAlgCat.of k S) (CommAlgCat.of k D),
    show τ ≫
    affinePoint K b = _ from spectrum_tensor_snd (CommAlgCat.of k S) (CommAlgCat.of k D)]
  simp only [Category.assoc, tensorHom_fst_assoc, tensorHom_snd_assoc]
  rfl

/-- A nonzero covariant module for a positive power of the character
gives a nonzero module for the character on a normal integral group. -/
private theorem nontrivial_of_positive_power {P : OppositeBorelPair G}
    (p : BorelProjection P) (χ : Character P.torus.group) {A D : HopfAlgebraCategory k}
    [IsDomain A] [IsIntegrallyClosed A]
    (e : specGroup A ≅ G.val) (d : specGroup D ≅ P.negative.group)
    (q : A ⟶ D) (φ : DiagonalizableGroups.groupAlgebra k
      DiagonalizableGroups.IntegerCharacters ⟶ D)
    (hq : specGroupMap q ≫ e.hom = d.hom ≫ P.negative.inclusion)
    (hφ : specGroupMap φ = d.hom ≫ p.projection ≫ χ)
    (c : GroupLike k D) (hc : (c : D) = characterCoordinate φ)
    (Q : QuotientEmbedding.Presentation P.negative) (a : ModObj G.val.X Q.scheme)
    (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul)
    (n : ℕ) (hn : 0 < n) (hne : Nontrivial (covariantFunctions q (c ^ n))) :
    Nontrivial (covariantFunctions q c) := by
  obtain ⟨φ', hφ', hc'⟩ := character_power p χ d φ hφ c hc n
  obtain ⟨c', hcoord, L, E, ρ, hfin, hE, hρ, ht⟩ :=
    LinearAlgebraicGroups.FlagLineBundle.flagLineBundleAndSections k G P p
      (χ ^ n) Q a ha A D e d q φ' hq hφ'
  have he : c' = c ^ n := GroupLike.val_injective (hcoord.trans hc'.symm)
  subst c'
  letI := hfin
  have hsoc := moduleSocle p (χ ^ n) e d hq φ' hφ' hc' ρ ht
  obtain ⟨U, hU, f, hf⟩ := normalized_on_radical (χ ^ n) e q (c ^ n) ρ ht hsoc hne
  letI : IsAffine P.positive.group.X.left := subgroupAffine (G := G) P.positive
  letI : IsAffine U.group.X.left := subgroupAffine (G := Unipotent.closedSubgroupAlgebraicGroup P.positive) U
  obtain ⟨Sop, ⟨s⟩⟩ := essImage_hopfSpec.mpr (show IsAffine U.group.X.left from inferInstance)
  let S := Sop.unop
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let r : A ⟶ S := (ff.preimage (s.hom ≫ U.inclusion ≫ P.positive.inclusion ≫ e.inv)).unop
  have hr : specGroupMap r ≫ e.hom = s.hom ≫ U.inclusion ≫ P.positive.inclusion := by
    change (hopfSpec (CommRingCat.of k)).map (ff.preimage _) ≫ e.hom = _
    rw [ff.map_preimage]
    simp
  let j := multiplicationCoordinates r.hom.toAlgHom q
  have hcomp := multiplicationCoordinates_spec e d s r q hr hq
  have ho := radicalBorelMap_open p U hU
  letI : IsOpenImmersion (radicalBorelMap U).left := ho
  have hop : IsOpenImmersion (Spec.map (CommRingCat.ofHom j.toRingHom)) := by
    have h := congrArg (fun f ↦ f.left) hcomp
    simp only [Over.comp_left, spectrumTensorIso_left] at h
    let i := (pullbackSpecIso (CommRingCat.of k) (CommAlgCat.of k S) (CommAlgCat.of k D)).hom
    let g := Spec.map (CommRingCat.ofHom j.toRingHom)
    let f := e.hom.hom.hom.left
    letI : IsIso f := (Over.forget (Spec (CommRingCat.of k))).map_isIso e.hom.hom.hom
    haveI : IsIso (s.hom.hom.hom ⊗ₘ d.hom.hom.hom).left :=
      (Over.forget (Spec (CommRingCat.of k))).map_isIso (s.hom.hom.hom ⊗ₘ d.hom.hom.hom)
    change i ≫ g ≫ f = (s.hom.hom.hom ⊗ₘ d.hom.hom.hom).left ≫
      (radicalBorelMap U).left at h
    haveI : IsIso i := inferInstanceAs (IsIso (pullbackSpecIso (CommRingCat.of k)
      (CommAlgCat.of k S) (CommAlgCat.of k D)).hom)
    have h' : IsOpenImmersion (i ≫ g ≫ f) := h.symm ▸
      inferInstanceAs (IsOpenImmersion ((s.hom.hom.hom ⊗ₘ d.hom.hom.hom).left ≫
        (radicalBorelMap U).left))
    have h'' := (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion i (g ≫ f)).mp h'
    have hf : IsIso f := (Over.forget (Spec (CommRingCat.of k))).map_isIso e.hom.hom.hom
    exact (@MorphismProperty.cancel_right_of_respectsIso _ _ @IsOpenImmersion _ _ _ _ g f hf).mp h''
  letI : Nontrivial S := (counitAlgHom k S).toRingHom.domain_nontrivial
  obtain ⟨g, hg, _⟩ := extend_covariant_from_product_chart r.hom.toAlgHom q c hop n hn f (hf S s r hr)
  exact nontrivial_of_ne g 0 hg

end NormalizedCovariance

section CentralCharacters

open Specs.DiagonalizableGroups (diagonalClosedInclusion groupAlgebra groupAlgebraMap)
open LinearAlgebraicGroups.CharacterDescent (groupLikeCharacterEquiv mapGroupLike monomialCharacterEquiv)
open Specs.SchemeCentre (rootLattice)
open RationalRepresentations (coefficients coefficients_isCoactionMatrix)
open private diagonal_coefficients offBlock_zero block_isCoactionMatrix determinant_isGroupLike
  hopfPreimage specGroupMap_hopfPreimage commute_from_centre
  from LinearAlgebraicGroups.Reductive.CentralTorus
open private basis_vector_eq_sum_coefficients from LinearAlgebraicGroups.Affine.FaithfulLinearization
open private restrictCoaction from LinearAlgebraicGroups.Unipotent.ExactOperations
open private monomialEquiv monomial_natural from LinearAlgebraicGroups.Classification.CentralIsogenies
open private integerHopfHomEquiv integerHopfHomEquiv_generator mapGroupLike_comp
  from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private specGroupMap_comp from LinearAlgebraicGroups.Affine.ClosedSubgroups

/-- Some positive power of every character of a split diagonalizable
central subgroup is the restriction of a group-like element. -/
private theorem central_monomial_power {M : Type u} [CommGroup M]
    {A : HopfAlgebraCategory k} (q : A ⟶ groupAlgebra k M)
    (hq : Function.Surjective q.hom)
    (hcentral : ∀ (R : TestAlgebra k) (a : A →ₐ[k] R) (c : MonoidAlgebra k M →ₐ[k] R),
      letI := convolutionGroup A R
      Commute (toConv a) (toConv (c.comp q.hom.toAlgHom))) (m : M) :
    ∃ (n : ℕ) (x : GroupLike k A), 0 < n ∧ q.hom x.val = MonoidAlgebra.of k M (m ^ n) := by
  classical
  obtain ⟨x, hx⟩ := hq (MonoidAlgebra.of k M m)
  let ρ : RightComodule k A A := RightComodule.regular
  obtain ⟨W₀, hxW⟩ := ρ.exists_finiteSubcomodule x
  let W := W₀.val
  letI : FiniteDimensional k W := W₀.property.2
  obtain ⟨σ, hσ⟩ := (ρ.isSubcomodule_iff_exists_coaction W).mp W₀.property.1
  let V := LinearAlgebraicGroups.WeightDecomposition.weightSpace (restrictCoaction q σ)
  let bs (m : M) := Module.Basis.ofVectorSpace k (V m)
  have hV := LinearAlgebraicGroups.WeightDecomposition.weightDecomposition (restrictCoaction q σ)
  let b := hV.collectedBasis bs
  let J := Σ m : M, Module.Basis.ofVectorSpaceIndex k (V m)
  letI : Finite J := Module.Finite.finite_basis b
  letI : Fintype J := Fintype.ofFinite J
  let X := coefficients A b σ
  have hX := coefficients_isCoactionMatrix A b σ
  have hdiag (i j : J) : q.hom (X i j) =
      if i = j then MonoidAlgebra.of k M j.1 else 0 :=
    diagonal_coefficients q σ b Sigma.fst (fun j ↦ hV.collectedBasis_mem bs j) i j
  have hweight : ∃ j : J, j.1 = m := by
    by_contra! hm
    let l := (MonoidAlgebra.basis M k).coord m
    let f : W →ₗ[k] k := l.comp (q.hom.toAlgHom.toLinearMap.comp W.subtype)
    have hf : f = 0 := by
      apply b.ext
      intro j
      change l (q.hom (b j : A)) = 0
      rw [basis_vector_eq_sum_coefficients A W b σ hσ j, map_sum, map_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [map_smul, map_smul, hdiag]
      split_ifs with h
      · have hcoeff : l (MonoidAlgebra.of k M j.1) = 0 := by
          change (MonoidAlgebra.basis M k).coord m ((MonoidAlgebra.basis M k) j.1) = 0
          rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne (hm j).symm]
        rw [hcoeff, smul_zero]
      · rw [map_zero, smul_zero]
    have hh := DFunLike.congr_fun hf (⟨x, hxW⟩ : W)
    change l (q.hom x) = 0 at hh
    rw [hx] at hh
    change (MonoidAlgebra.basis M k).coord m ((MonoidAlgebra.basis M k) m) = 0 at hh
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same] at hh
    exact one_ne_zero hh
  let Jm := {i : J // i.1 = m}
  let Xm : Matrix Jm Jm A := X.submatrix Subtype.val Subtype.val
  have hXm := block_isCoactionMatrix X hX Sigma.fst
    (offBlock_zero q X hX Sigma.fst hdiag hcentral) m
  have hn : 0 < Fintype.card Jm := by
    obtain ⟨j, hj⟩ := hweight
    exact Fintype.card_pos_iff.mpr ⟨⟨j, hj⟩⟩
  refine ⟨Fintype.card Jm, ⟨Xm.det, determinant_isGroupLike Xm hXm⟩, hn, ?_⟩
  have hmat : q.hom.toAlgHom.mapMatrix Xm = Matrix.diagonal (fun _ ↦ MonoidAlgebra.of k M m) := by
    apply Matrix.ext
    intro i j
    change q.hom (X i j) = _
    rw [hdiag, show j.val.1 = m from j.property, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst j
      simp
    · have h' : i.val ≠ j.val := fun he ↦ h (Subtype.ext he)
      simp [h, h']
  change q.hom.toAlgHom Xm.det = _
  rw [AlgHom.map_det, hmat, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, map_pow]

private theorem groupLike_of_monomial {M : Type u} [CommGroup M] (m : M) :
    groupLikeCharacterEquiv (groupAlgebra k M) (monomialCharacterEquiv k m) =
      monomialEquiv (k := k) M m := by
  let φ := groupAlgebraMap k ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom)
  change specGroupMap (integerHopfHomEquiv _ (monomialCharacterEquiv k m)) = specGroupMap φ
  congr 1
  apply (integerHopfHomEquiv (groupAlgebra k M)).symm.injective
  rw [Equiv.symm_apply_apply]
  apply GroupLike.val_injective
  change MonoidAlgebra.of k M m =
    (MonoidAlgebra.mapDomainBialgHom k ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom))
      (MonoidAlgebra.of k _ Specs.DiagonalizableGroups.integerGenerator)
  change MonoidAlgebra.single m (1 : k) =
    (MonoidAlgebra.mapDomainBialgHom k ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom))
      (MonoidAlgebra.single Specs.DiagonalizableGroups.integerGenerator (1 : k))
  rw [MonoidAlgebra.mapDomainBialgHom_single]
  congr 1
  change m = m ^ (1 : ℤ)
  rw [zpow_one]

private theorem groupLikeCharacter_restriction {A B : HopfAlgebraCategory k} (q : A ⟶ B)
    (x : GroupLike k A) :
    groupLikeCharacterEquiv B (mapGroupLike q x) = specGroupMap q ≫ groupLikeCharacterEquiv A x := by
  change specGroupMap (integerHopfHomEquiv B (mapGroupLike q x)) =
    specGroupMap q ≫ specGroupMap (integerHopfHomEquiv A x)
  rw [← specGroupMap_comp]
  congr 1
  apply (integerHopfHomEquiv B).symm.injective
  rw [Equiv.symm_apply_apply]
  change _ = mapGroupLike (integerHopfHomEquiv A x ≫ q)
    (monomialCharacterEquiv k Specs.DiagonalizableGroups.integerGenerator)
  rw [mapGroupLike_comp]
  exact congrArg (mapGroupLike q) ((integerHopfHomEquiv A).symm_apply_apply x).symm

private theorem central_character_power {P : OppositeBorelPair G} {A : HopfAlgebraCategory k}
    (e : specGroup A ≅ G.val) (χ : Character P.torus.group) :
    ∃ (n : ℕ) (ξ : Character G.val), 0 < n ∧
      χ ^ n / (P.torus.inclusion ≫ ξ) ∈ rootLattice P.torus := by
  let T := P.torus
  let X := Character T.group
  let L := rootLattice T
  let M := X ⧸ L
  let B := groupAlgebra k M
  obtain ⟨_, t, ht, hz, hZ, _⟩ :=
    LinearAlgebraicGroups.RootData.SchemeCentre.schemeCentre G P.reductive T P.split P.maximal
  let j : specGroup B ⟶ T.group := diagonalClosedInclusion k L ≫ t.hom
  let i : specGroup B ⟶ G.val := j ≫ T.inclusion
  let q : A ⟶ B := hopfPreimage (i ≫ e.inv)
  have hq : specGroupMap q ≫ e.hom = i := by rw [specGroupMap_hopfPreimage]; simp
  have hs : Function.Surjective q.hom := by
    apply (LinearAlgebraicGroups.hopfMapClosedImmersion k q).mp
    rw [specGroupMap_hopfPreimage]
    letI : IsClosedImmersion i.hom.hom.left := hz
    letI : IsIso e.inv.hom.hom.left :=
      (Over.forget (Spec (CommRingCat.of k))).map_isIso e.inv.hom.hom
    exact inferInstanceAs (IsClosedImmersion (i.hom.hom.left ≫ e.inv.hom.hom.left))
  have hcent : Centralizes (𝟙 G.val) i.hom.hom := by
    exact (hZ (specGroup B).X i.hom.hom).mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨conv, _, hconv⟩ := LinearAlgebraicGroups.hopfSpecPoints k
  have hcentral (R : TestAlgebra k) (a : A →ₐ[k] R) (c : MonoidAlgebra k M →ₐ[k] R) :
      letI := convolutionGroup A R
      Commute (toConv a) (toConv (c.comp q.hom.toAlgHom)) := by
    letI := convolutionGroup A R
    let α := (conv A).hom.app R
    let β := (conv B).hom.app R
    let f := (yonedaGrp.map e.hom).app (op ((testSpec k).obj (op R)))
    apply Commute.of_map (f := (f.hom.comp α.hom))
      ((ConcreteCategory.bijective_of_isIso f).1.comp (ConcreteCategory.bijective_of_isIso α).1)
    have hc := hconv q R (toConv c)
    change ((conv A).hom.app R (toConv (c.comp q.hom.toAlgHom)) : Points _ R) =
      (β (toConv c) : Points _ R) ≫ (specGroupMap q).hom.hom at hc
    change Commute ((α (toConv a) : Points _ R) ≫ e.hom.hom.hom)
      ((α (toConv (c.comp q.hom.toAlgHom)) : Points _ R) ≫ e.hom.hom.hom)
    have h : (specGroupMap q).hom.hom ≫ e.hom.hom.hom = i.hom.hom :=
      congrArg (Grp.forget (SchemeOver k)).map hq
    have he : (α (toConv (c.comp q.hom.toAlgHom)) : Points _ R) ≫ e.hom.hom.hom =
        (β (toConv c) : Points _ R) ≫ i.hom.hom :=
      (congrArg (fun y : Points (specGroup A).X R ↦ y ≫ e.hom.hom.hom) hc).trans
        ((Category.assoc _ _ _).trans (congrArg (fun y ↦ (β (toConv c) : Points _ R) ≫ y) h))
    rw [he]
    exact (commute_from_centre hcent (β (toConv c)) ((α (toConv a) : Points _ R) ≫ e.hom.hom.hom)).symm
  let m : M := QuotientGroup.mk' L χ
  obtain ⟨n, x, hn, hx⟩ := central_monomial_power q hs hcentral m
  let ξ := e.inv ≫ groupLikeCharacterEquiv A x
  refine ⟨n, ξ, hn, ?_⟩
  let π := QuotientGroup.mk' L
  have hres (ψ : X) : j ≫ ψ = monomialEquiv (k := k) M (π ψ) := by
    change specGroupMap (groupAlgebraMap k π) ≫ t.hom ≫ ψ = _
    rw [ht ψ]
    exact monomial_natural π ψ
  have hξ : i ≫ ξ = monomialEquiv (k := k) M (m ^ n) := by
    have hval : mapGroupLike q x = monomialCharacterEquiv k (m ^ n) :=
      GroupLike.val_injective hx
    change i ≫ e.inv ≫ groupLikeCharacterEquiv A x = _
    rw [← hq, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← groupLikeCharacter_restriction]
    rw [hval]
    exact groupLike_of_monomial (m ^ n)
  have hr : π (T.inclusion ≫ ξ) = m ^ n := by
    apply (monomialEquiv (k := k) M).injective
    rw [← hres, ← Category.assoc]
    exact hξ
  apply (QuotientGroup.eq_one_iff _).mp
  change π (χ ^ n / (T.inclusion ≫ ξ)) = 1
  rw [map_div, map_pow, hr, div_self']

end CentralCharacters

section Weights

open Specs.AbstractPairing (Root)
open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open Specs.CharacterPairing (absoluteRoots pairing)
open Specs.DatumAndWeyl (Identification)
open Specs.ParabolicLineWeights (ParabolicLine omittedSimpleRoot)
open Specs.RootWeightAction (SimpleRoot DominanceLE weightSpace)
open Specs.SimpleRoots (evaluate IsBaseFor)
open Specs.StandardParabolicLevi (parabolicWeylGroup)
open Specs.StandardParabolics (SimpleSubset HasWeylIndices)
open Specs.SchemeCentre (rootLattice)
open private baseSimpleRoot exists_cyclic_parabolic_line simple_coroot_of_line
  omitted_reflection_not_mem HasPrimitive hasPrimitive_prod hasPrimitive_pow reflection_fixes_iff
  from LinearAlgebraicGroups.Representation.ParabolicLineWeights
open private normalizerOnTorus radicalIso from LinearAlgebraicGroups.Flag.OpenCell
open private normKillsRoot postMul postInv from LinearAlgebraicGroups.Reductive.CentralDerived

private theorem opposite_dominant (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) (χ : Character P.torus.group) (hχ : Dominant P χ) :
    IsDominant D P.negative χ⁻¹ := by
  obtain ⟨c, _, hc, _, hp⟩ :=
    (LinearAlgebraicGroups.RootData.BorelsAndChambers.borelsThroughT G P.reductive P.torus
      P.split P.maximal).1 P.positive P.positiveBorel P.inPositive
  let neg (i : Root P.torus) := D.rootDatum.reflectionPerm i i
  have hinv (i : Root P.torus) : (neg i).val = i.val⁻¹ := by
    apply Additive.ofMul.injective
    rw [← D.root_eq, show neg i = D.rootDatum.reflectionPerm i i from rfl,
      D.rootDatum.root_reflectionPerm, D.rootDatum.reflection_apply_self, D.root_eq]
    rfl
  have hneg (i : Root P.torus) : neg i ∈ subgroupRoots P.torus P.negative ↔
      i ∈ subgroupRoots P.torus P.positive := by
    rw [P.opposite, hp, Set.mem_compl_iff]
    change (¬ 0 < pairing P.torus.group (neg i).val c) ↔ 0 < pairing P.torus.group i.val c
    have he : pairing P.torus.group (neg i).val c = -pairing P.torus.group i.val c := by
      rw [hinv, ← D.pairing_eq, ← D.pairing_eq]
      exact LinearMap.congr_fun (map_neg D.rootDatum.toLinearMap (Additive.ofMul i.val))
        (Additive.ofMul c)
    rw [he]
    have := hc i
    omega
  have hinvol (i : Root P.torus) : neg (neg i) = i :=
    Subtype.ext (by rw [hinv, hinv, inv_inv])
  intro i
  let j : SimpleRoot P.torus P.positive := ⟨neg i.val,
    (hneg _).mp (by rw [hinvol]; exact i.property.1), by
      intro a ha b hb h
      apply i.property.2 (neg a) ((hneg _).mpr ha) (neg b) ((hneg _).mpr hb)
      simpa only [hinv, inv_inv, mul_inv_rev, mul_comm b.val⁻¹ a.val⁻¹] using
        congrArg (Inv.inv : Character P.torus.group → Character P.torus.group) h⟩
  have hj : D.rootDatum.coroot j.val = -D.rootDatum.coroot i.val := by
    apply (D.opposite _ _).mp
    rw [D.root_eq, D.root_eq, hinv]
    rfl
  have h := hχ j _ (D.attached j.val)
  rw [← D.pairing_eq] at h
  change 0 ≤ D.rootDatum.toLinearMap (Additive.ofMul χ) (D.rootDatum.coroot j.val) at h
  rw [hj, map_neg] at h
  change 0 ≤ D.rootDatum.toLinearMap (-(Additive.ofMul χ)) (D.rootDatum.coroot i.val)
  simpa only [map_neg, LinearMap.neg_apply] using h

private theorem restriction_fixed_by_weyl {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] {D : Datum T} (W : Identification D)
    (w : D.rootDatum.weylGroup) (n : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X)
    (hn : Specs.BruhatOrbitParametrization.IsRepresentative W w n)
    (ξ : Character G.val) :
    (W.labelEquiv w).val (T.inclusion ≫ ξ) = T.inclusion ≫ ξ := by
  let a := W.image.conjugation (W.labelEquiv w)
  have h : a.hom ≫ T.inclusion ≫ ξ = T.inclusion ≫ ξ := by
    apply Grp.hom_ext
    have he := normalizerOnTorus W w n hn
    change (a.hom ≫ T.inclusion).hom.hom = _ at he
    rw [← Category.assoc, Grp.comp_hom_hom, he, postMul, postMul, postInv, Grp.comp_hom_hom]
    rw [mul_comm _ (T.inclusion.hom.hom ≫ ξ.hom.hom), mul_assoc, mul_inv_cancel, mul_one]
  rw [W.image.characterAction]
  change a.inv ≫ T.inclusion ≫ ξ = _
  exact (congrArg (a.inv ≫ ·) h.symm).trans (Iso.inv_hom_id_assoc _ _)

private theorem root_lattice_coroot_kernel {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] {D : Datum T} (W : Identification D) {b : D.rootDatum.Base}
    {c : Specs.CharacterDescent.Cocharacter T.group}
    (hb : IsBaseFor D.rootDatum (evaluate D c) b)
    (δ : Character T.group) (hδ : δ ∈ rootLattice T)
    (hzero : ∀ i : b.support, D.rootDatum.coroot' i.val (Additive.ofMul δ) = 0) :
    δ = 1 := by
  classical
  letI := D.freeCharacters
  letI : IsMulTorsionFree (Character T.group) := ⟨by
    intro n hn a b _ he
    have hh : (a / b) ^ n = 1 := by rw [div_pow, he, div_self']
    have h : (n : ℤ) • Additive.ofMul (a / b) = 0 := by
      rw [natCast_zsmul]
      exact hh
    exact div_eq_one.mp ((smul_eq_zero.mp h).resolve_left (by exact_mod_cast hn))⟩
  let fixδ : Subgroup D.rootDatum.weylGroup :=
    { carrier := {w | (W.labelEquiv w).val δ = δ}
      one_mem' := by simp
      mul_mem' := by
        intro v w hv hw
        change (W.labelEquiv (v * w)).val δ = δ
        rw [map_mul]
        change (W.labelEquiv v).val ((W.labelEquiv w).val δ) = δ
        rw [show (W.labelEquiv w).val δ = δ from hw]
        exact hv
      inv_mem' := by
        intro v hv
        change (W.labelEquiv v⁻¹).val δ = δ
        rw [map_inv]
        exact ((W.labelEquiv v).val.symm_apply_eq.mpr hv.symm) }
  have hfix : (⊤ : Subgroup D.rootDatum.weylGroup) ≤ fixδ := by
    rw [← hb.generates]
    apply (Subgroup.closure_le fixδ).mpr
    rintro _ ⟨i, rfl⟩
    change (W.labelEquiv (RootPairing.weylGroup.ofIdx D.rootDatum i.val)).val δ = δ
    apply Additive.ofMul.injective
    rw [← W.characterAction]
    exact (reflection_fixes_iff i.val _).mpr (hzero i)
  letI := W.image.finite
  letI : Fintype W.image.labels := Fintype.ofFinite _
  let N : Character T.group →* Character T.group :=
    { toFun := fun x ↦ ∏ w : W.image.labels, w.val x
      map_one' := by simp
      map_mul' := by intro a b; simp only [map_mul, Finset.prod_mul_distrib] }
  have hkill : rootLattice T ≤ N.ker := by
    apply (Subgroup.closure_le N.ker).mpr
    intro α hα
    let i : Root T := ⟨α, hα⟩
    let s := RootPairing.weylGroup.ofIdx D.rootDatum i
    have hs : (W.labelEquiv s).val α = α⁻¹ := by
      apply Additive.ofMul.injective
      rw [← W.characterAction]
      change (RootPairing.Equiv.reflection D.rootDatum i).weightEquiv (Additive.ofMul i.val) =
        -(Additive.ofMul i.val)
      rw [← D.root_eq i, RootPairing.Equiv.reflection_weightEquiv,
        D.rootDatum.reflection_apply_self]
    exact normKillsRoot W.image.labels α (W.labelEquiv s) hs
  have h := hkill hδ
  change (∏ w : W.image.labels, w.val δ) = 1 at h
  have hall (w : W.image.labels) : w.val δ = δ := by
    obtain ⟨v, rfl⟩ := W.labelEquiv.surjective w
    exact hfix (Subgroup.mem_top v)
  rw [Finset.prod_congr rfl (fun w _ ↦ hall w), Finset.prod_const, Finset.card_univ] at h
  exact (pow_eq_one_iff_left (n := Fintype.card W.image.labels) Fintype.card_pos.ne').mp h

open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.RootWeightAction (Representation IsPrimitive mem_fixedSpace)

/-- Omitted-root parabolic lines provide integral primitive weights with
independently prescribed simple-coroot pairings up to a common factor. -/
private theorem reductive_parabolic_weights {P : OppositeBorelPair G} (p : BorelProjection P)
    (χ : Character P.torus.group) (hχ : Dominant P χ) :
    ∃ comm : IsCommMonObj P.torus.group.X, letI := comm
    ∃ (D : Datum P.torus) (W : Identification D) (cochar : Specs.CharacterDescent.Cocharacter P.torus.group)
      (b : D.rootDatum.Base), IsBaseFor D.rootDatum (evaluate D cochar) b ∧
      (∀ w : D.rootDatum.weylGroup, ∃ n, Specs.BruhatOrbitParametrization.IsRepresentative W w n) ∧
      ∃ (d : ℕ) (ψ : Character P.torus.group), 0 < d ∧
        HasPrimitive (U := p.radical) ψ ∧
        ∀ j : b.support, D.rootDatum.coroot' j.val (Additive.ofMul ((χ⁻¹) ^ d / ψ)) = 0 := by
  classical
  let T := P.torus
  let B := P.negative
  obtain ⟨comm, D, W, F, c, b, hreg, hpos, hb, hrep, Q, hQ, _⟩ :=
    LinearAlgebraicGroups.Flag.StandardParabolics.standardParabolicClassification
      G P.reductive T B P.split P.maximal P.negativeBorel P.inNegative
  letI := comm
  obtain ⟨_, _, U, hU, hhigh, _, _⟩ :=
    LinearAlgebraicGroups.Representation.PrimitiveLine.primitiveLine G P.reductive T B
      P.split P.maximal P.negativeBorel P.inNegative
  let omitted (i : b.support) : SimpleSubset b := ⟨omittedSimpleRoot b i, Set.sdiff_subset⟩
  let Par (i : b.support) := Q (omitted i)
  have hPW (i : b.support) : HasWeylIndices W (Par i).limitGroups.parabolic
      (parabolicWeylGroup D (omittedSimpleRoot b i)) := hQ _
  have hex (i : b.support) : Nonempty (ParabolicLine (T := T) U (Par i).limitGroups.parabolic) :=
    exists_cyclic_parabolic_line (Par i).limitGroups.parabolic hU P.inNegative (Par i).containsBorel
      (fun ρ χ v hv hgen ↦ (hhigh ρ χ v hv hgen).1)
  let L (i : b.support) := (hex i).some
  have hpositive (a : SimpleRoot T B) : 0 < evaluate D c (Additive.ofMul a.val.val) := by
    change 0 < D.rootDatum.toLinearMap (Additive.ofMul a.val.val) (Additive.ofMul c)
    rw [D.pairing_eq]
    exact (show a.val ∈ positiveRoots T c by rw [hpos]; exact a.property.1)
  have hsimple (j : b.support) : ∃ a : SimpleRoot T B, a.val = j.val :=
    (baseSimpleRoot hpos hb j.val).mp j.property
  have hroot (j : b.support) : 0 < evaluate D c (D.rootDatum.root j.val) := by
    obtain ⟨a, ha⟩ := hsimple j
    rw [← ha, D.root_eq]
    exact hpositive a
  let degree (i j : b.support) := D.rootDatum.coroot' j.val (Additive.ofMul (L i).weight)
  have hdegree (i j : b.support) : 0 ≤ degree i j ∧ (degree i j = 0 ↔ i ≠ j) := by
    letI := (L i).finite
    letI := (L i).decidable
    let s := RootPairing.weylGroup.ofIdx D.rootDatum j.val
    obtain ⟨n, hn⟩ := hrep s
    have hmax nu hne hnonzero := ((hhigh (L i).representation (L i).weight (L i).vector
      (L i).primitive (L i).cyclic).2.1 nu hnonzero hne).1
    obtain ⟨hle, hzero⟩ := simple_coroot_of_line W P.split hpositive (Par i).limitGroups.parabolic
      (L i).representation (L i).weight (L i).vector (L i).primitive (L i).highestLine hmax
      j (hroot j) n hn (L i).stabilizer
    refine ⟨hle, hzero.trans ((hPW i s n hn).trans ?_)⟩
    constructor
    · rintro hs rfl
      exact omitted_reflection_not_mem i (Par i).face hs
    · intro hne
      apply Subgroup.subset_closure
      exact ⟨j.val, ⟨j.property, fun h ↦ hne (Subtype.ext (Set.mem_singleton_iff.mp h).symm)⟩, rfl⟩
  have hdiag (i : b.support) : 0 < degree i i :=
    lt_of_le_of_ne (hdegree i i).1 fun h ↦ (hdegree i i).2.mp h.symm rfl
  let di (i : b.support) := (degree i i).toNat
  let d := ∏ i : b.support, di i
  have hdi (i : b.support) : 0 < di i := by
    have hi := hdiag i
    dsimp only [di]
    omega
  have hd : 0 < d := Finset.prod_pos (fun i _ ↦ hdi i)
  have hdiv (i : b.support) : di i ∣ d := Finset.dvd_prod_of_mem di (Finset.mem_univ i)
  let ev (j : b.support) := D.rootDatum.coroot' j.val
  have hpair (i j : b.support) : ev j (Additive.ofMul (L i).weight) =
      if i = j then (di i : ℤ) else 0 := by
    by_cases h : i = j
    · subst j
      exact (Int.toNat_of_nonneg (hdiag i).le).symm.trans (ite_eq_left rfl).symm
    · exact ((hdegree i j).2.mpr h).trans (ite_eq_right h).symm
  let coeff (i : b.support) := (ev i (Additive.ofMul χ⁻¹)).toNat
  have hcoeff (i : b.support) : (coeff i : ℤ) = ev i (Additive.ofMul χ⁻¹) := by
    apply Int.toNat_of_nonneg
    obtain ⟨a, ha⟩ := hsimple i
    change 0 ≤ D.rootDatum.coroot' i.val (Additive.ofMul χ⁻¹)
    rw [← ha]
    exact opposite_dominant P D χ hχ a
  let exp (i : b.support) := (d / di i) * coeff i
  let ψ := ∏ i : b.support, (L i).weight ^ exp i
  obtain ⟨r, hr⟩ := radicalIso p.isRadical hU
  have hprim (i : b.support) : HasPrimitive (U := p.radical) (L i).weight := by
    letI := (L i).finite
    letI := (L i).decidable
    refine ⟨(L i).index, (L i).finite, (L i).decidable, (L i).representation, (L i).vector,
      (L i).primitive.1, mem_fixedSpace.mpr ?_, (L i).primitive.2.2⟩
    intro R x
    have he := mem_fixedSpace.mp (L i).primitive.2.1 R (x ≫ r.hom.hom.hom)
    have ht : r.hom ≫ U.inclusion ≫ B.inclusion = p.radical.inclusion ≫ B.inclusion :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun a ↦ a ≫ B.inclusion) hr)
    have hx : (x ≫ r.hom.hom.hom) ≫ (U.inclusion ≫ B.inclusion).hom.hom =
        x ≫ (p.radical.inclusion ≫ P.negative.inclusion).hom.hom :=
      (Category.assoc _ _ _).trans
        (congrArg (fun a : p.radical.group ⟶ G.val ↦ x ≫ a.hom.hom) ht)
    rw [hx] at he
    exact he
  refine ⟨comm, D, W, c, b, hb, hrep, d, ψ, hd,
    hasPrimitive_prod Finset.univ _ (fun i _ ↦ hasPrimitive_pow (hprim i) (exp i)), ?_⟩
  intro j
  change ev j (Additive.ofMul ((χ⁻¹) ^ d / ψ)) = 0
  rw [show Additive.ofMul ((χ⁻¹) ^ d / ψ) = d • Additive.ofMul χ⁻¹ - Additive.ofMul ψ from rfl,
    map_sub, sub_eq_zero, map_nsmul, ← hcoeff]
  unfold ψ
  rw [ofMul_prod, map_sum]
  simp only [show ∀ i : b.support, Additive.ofMul ((L i).weight ^ exp i) =
    exp i • Additive.ofMul (L i).weight from fun _ ↦ rfl, map_nsmul, hpair]
  rw [Finset.sum_eq_single j]
  · rw [ite_eq_left rfl, ← natCast_zsmul, ← natCast_zsmul, smul_eq_mul, smul_eq_mul]
    exact_mod_cast (show d * coeff j = exp j * di j by
      dsimp only [exp]
      rw [mul_right_comm, Nat.div_mul_cancel (hdiv j)])
  · intro i _ hi
    rw [ite_eq_right hi, smul_zero]
  · simp

end Weights

section Normality

open private irreducible_of_geometricallyConnected
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private isReduced_of_smooth_over_field
  from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private smooth_coordinate_hopf from LinearAlgebraicGroups.RootData.RootGroups

/-- The coordinate algebra of a connected smooth reductive group is a domain. -/
private theorem coordinate_domain {A : HopfAlgebraCategory k}
    (e : specGroup A ≅ G.val) (hG : Specs.GeometricRadicals.IsReductive G) : IsDomain A := by
  letI := G.property.2.1
  letI := G.property.2.2
  letI : GeometricallyConnected G.val.X.hom := hG.2.1
  letI : IrreducibleSpace G.val.X.left := irreducible_of_geometricallyConnected G.val
  letI : Smooth G.val.X.hom := hG.1
  letI : IsReduced G.val.X.left := isReduced_of_smooth_over_field G.val.X.hom
  letI : IsIntegral G.val.X.left := isIntegral_of_irreducibleSpace_of_isReduced _
  let j : (specGroup A).X.left ≅ G.val.X.left :=
    (Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))).mapIso e
  have h : IsIntegral (specGroup A).X.left :=
    @IsIntegral.of_isIso G.val.X.left (specGroup A).X.left inferInstance j.inv (Iso.isIso_inv j)
  exact (affine_isIntegral_iff (CommRingCat.of A)).mp h

/-- Smooth domain algebras over a field are integrally closed. Each prime
has an étale neighborhood of a polynomial algebra. -/
private theorem smooth_domain_integrallyClosed (A : Type u) [CommRing A] [Algebra k A]
    [IsDomain A] [Algebra.Smooth k A] : IsIntegrallyClosed A := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  letI : p.IsPrime := hp.isPrime
  obtain ⟨f, hf, n, hAlg, _, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p)
  let B := MvPolynomial (Fin n) k
  let S := Localization.Away f
  letI : Algebra B S := hAlg
  letI : Algebra.IsStandardEtale B S := hEtale
  have hB : AdvCommAlg.Normality.Specs.IsNormalValue B := by
    intro q
    refine ⟨inferInstance, ?_⟩
    exact isIntegrallyClosed_of_isLocalization (Localization.AtPrime q.asIdeal)
      q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors
  obtain ⟨hn, hS⟩ := AdvCommAlg.Normality.etale_normal_ascent B S hB
  let q := Ideal.map (algebraMap A S) p
  have hdis : Disjoint ((Submonoid.powers f : Submonoid A) : Set A) (p : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  letI : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) S p
    inferInstance hdis
  have hq : q.comap (algebraMap A S) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) S inferInstance hdis
  letI : IsIntegrallyClosed (Localization.AtPrime q) := (hS ⟨q, inferInstance⟩).2
  have hcompl : (q.comap (algebraMap A S)).primeCompl = p.primeCompl := by
    ext x
    change x ∉ q.comap (algebraMap A S) ↔ x ∉ p
    rw [hq]
  letI : IsLocalization p.primeCompl (Localization.AtPrime q) := hcompl ▸
    (IsLocalization.isLocalization_atPrime_localization_atPrime (Submonoid.powers f) q)
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime q) (Localization.AtPrime p)).toRingEquiv

end Normality

open Specs.SimplyConnectedLattice (AdjointForm LatticeCriterion SplitCover)
open Specs.SchemeCentre (rootLattice)
open private hasPrimitive_pow reflection_fixes_iff
  from LinearAlgebraicGroups.Representation.ParabolicLineWeights
open private smooth_coordinate_hopf from LinearAlgebraicGroups.RootData.RootGroups

private theorem dominant_covariant_power {P : OppositeBorelPair G} (p : BorelProjection P)
    (χ : Character P.torus.group) {A D : HopfAlgebraCategory k}
    (e : specGroup A ≅ G.val) (d : specGroup D ≅ P.negative.group)
    (q : A ⟶ D) (φ : DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters ⟶ D)
    (hq : specGroupMap q ≫ e.hom = d.hom ≫ P.negative.inclusion)
    (hφ : specGroupMap φ = d.hom ≫ p.projection ≫ χ)
    (c : GroupLike k D) (hc : (c : D) = characterCoordinate φ) (hχ : Dominant P χ) :
    ∃ n : ℕ, 0 < n ∧ Nontrivial (covariantFunctions q (c ^ n)) := by
  obtain ⟨comm, Δ, W, cochar, b, hb, hrep, degree, ψ, hdegree, hprim, hpair⟩ :=
    reductive_parabolic_weights p χ hχ
  letI := comm
  let δ := χ⁻¹ ^ degree / ψ
  obtain ⟨n, ξ, hn, hroot⟩ := central_character_power e δ
  have hξ (j : b.support) :
      Δ.rootDatum.coroot' j.val (Additive.ofMul (P.torus.inclusion ≫ ξ)) = 0 := by
    let w := RootPairing.weylGroup.ofIdx Δ.rootDatum j.val
    obtain ⟨t, ht⟩ := hrep w
    apply (reflection_fixes_iff j.val _).mp
    change w.val.weightEquiv (Additive.ofMul (P.torus.inclusion ≫ ξ)) =
      Additive.ofMul (P.torus.inclusion ≫ ξ)
    rw [W.characterAction, restriction_fixed_by_weyl W w t ht ξ]
  have hres : δ ^ n = P.torus.inclusion ≫ ξ := by
    apply div_eq_one.mp
    apply root_lattice_coroot_kernel W hb _ hroot
    intro j
    change Δ.rootDatum.coroot' j.val
      (n • Additive.ofMul δ - Additive.ofMul (P.torus.inclusion ≫ ξ)) = 0
    rw [map_sub, map_nsmul, show Δ.rootDatum.coroot' j.val (Additive.ofMul δ) = 0
      from hpair j, hξ j, nsmul_zero, sub_zero]
  have htwist : (χ ^ (degree * n))⁻¹ = ψ ^ n * (P.torus.inclusion ≫ ξ) := by
    rw [← inv_pow, ← hres, ← mul_pow, pow_mul]
    exact congrArg (· ^ n) (mul_div_cancel ψ (χ⁻¹ ^ degree)).symm
  obtain ⟨φ', hφ', hc'⟩ := character_power p χ d φ hφ c hc (degree * n)
  obtain ⟨I, hI, hDec, ρ, v, hv⟩ := hasPrimitive_pow hprim n
  exact ⟨degree * n, Nat.mul_pos hdegree hn,
    covariant_of_opposite_primitive p (χ ^ (degree * n)) e d q φ' hq hφ' (c ^ (degree * n)) hc'
      ξ (ψ ^ n) htwist hv⟩

/-- Nonvanishing for split reductive groups on the actual character lattice.
The three ordered classification premises are available in the conditional
contract. The determinant argument works directly with the full scheme centre. -/
theorem nonvanishing_conditional
    (_adjoint : AdjointForm.{u}) (_lattice : LatticeCriterion.{u}) (_cover : SplitCover.{u}) :
    Specs.InducedNonvanishing.Statement.{u} := by
  intro k _ G P χ
  obtain ⟨p, Q, a, A, D, e, d, q, φ, c, ρ₁, L, E, ρ, hs, hp, ht, hj,
    ha, hq, hφ, hc, hρ₁, hfinite, hE, hcoact, htrans, hsocle⟩ :=
    LinearAlgebraicGroups.Representation.InducedSocle.inducedSocle k G P χ
  refine ⟨p, Q, a, A, D, e, d, q, φ, c, L, E, ρ, ha, hq, hφ, hc, hfinite, hE, hcoact, hsocle,
    dominant_of_nontrivial LinearAlgebraicGroups.Classification.CentralIsogenies.centralIsogenyComparison
      P χ A e q c ρ hsocle, ?_⟩
  intro hdom
  obtain ⟨m, hm, hnonzero⟩ := dominant_covariant_power p χ e d q φ hq hφ c hc hdom
  letI : IsDomain A := coordinate_domain e P.reductive
  letI : Algebra.Smooth k A := smooth_coordinate_hopf e P.reductive.1
  letI : IsIntegrallyClosed A := smooth_domain_integrallyClosed (k := k) A
  exact nontrivial_of_positive_power p χ e d q φ hq hφ c hc Q a ha m hm hnonzero

end

end LinearAlgebraicGroups.Representation.InducedNonvanishing

universe v8_closure_1f246c59dcd6aacc_u0
theorem _root_.«LinearAlgebraicGroups».«Representation».«InducedNonvanishing».«nonvanishing» : _root_.«LinearAlgebraicGroups».«Specs».«InducedNonvanishing».«Statement».{v8_closure_1f246c59dcd6aacc_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«InducedNonvanishing».«nonvanishing_conditional».{v8_closure_1f246c59dcd6aacc_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{v8_closure_1f246c59dcd6aacc_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{v8_closure_1f246c59dcd6aacc_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{v8_closure_1f246c59dcd6aacc_u0})
