import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RamifiedOuterExceptionalForms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBuilding
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalTwistedTraceComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBuilding
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalMarkedAdjoint
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalParahoricCongruenceDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalParahoricResidueDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.NonabelianCohomology
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import Batteries.Tactic.OpenPrivate
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

open CategoryTheory
open scoped TensorProduct CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Arithmetic.RamifiedOuterExceptionalForms

section UnramifiedDescent

open MaximalUnramifiedBrauer (IsUnramified maximalUnramified mem_maximalUnramified_iff)
open LinearAlgebraicGroups.Descent.NonabelianCohomology
open Polynomial ValuativeRel
open scoped Topology WithZero

open private cyclotomicStage cyclotomicStage_data le_cyclotomicStage_of_unramified from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer
open private descend_of_trivial_on_kernel eventually_trivial restriction_ker from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.NonabelianCohomology

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Surjectivity on values for a finite unramified extension identifies the two
normalized valuations used in the marked affine comparison. -/
theorem unramifiedLocalExtensionOfSurjectiveValues
    {K : Type u} [Field K] [Algebra F K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
    (hs : Function.Surjective (fun z : F => valuation K (algebraMap F K z))) :
    Specs.ExceptionalAffineBruhat.IsUnramifiedLocalExtension F K := by
  let eF := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  let eK := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  let m := ValuativeExtension.mapValueGroupWithZero F K
  let f : ℤᵐ⁰ →*₀ ℤᵐ⁰ := eK.toMonoidWithZeroHom.comp (m.comp eF.symm.toMonoidWithZeroHom)
  have hm : StrictMono f :=
    eK.strictMono.comp ((ValuativeExtension.mapValueGroupWithZero_strictMono
      (A := F) (B := K)).comp eF.symm.strictMono)
  have hv (z : F) : f (eF (valuation F z)) = eK (valuation K (algebraMap F K z)) := by
    change eK (m (eF.symm (eF (valuation F z)))) = _
    rw [eF.symm_apply_apply, ValuativeExtension.mapValueGroupWithZero_valuation]
  obtain ⟨z, hz⟩ := hs (eK.symm (WithZero.exp 1))
  change valuation K (algebraMap F K z) = _ at hz
  have hpre : f (eF (valuation F z)) = WithZero.exp 1 := by
    rw [hv, hz, eK.apply_symm_apply]
  have hexp : (1 : ℤᵐ⁰) < WithZero.exp 1 := WithZero.one_lt_exp_iff.mpr Int.zero_lt_one
  have hz₁ : 1 < eF (valuation F z) := by
    apply hm.lt_iff_lt.mp
    rwa [map_one, hpre]
  have hmin {x : ℤᵐ⁰} (hx : 1 < x) : WithZero.exp 1 ≤ x := by
    have h := WithZero.lt_mul_exp_iff_le (x := x) (y := 1) one_ne_zero
    exact le_of_not_gt (fun hx' => hx.not_ge (h.mp (by simpa only [one_mul] using hx')))
  have hf₁ : f (WithZero.exp 1) = WithZero.exp 1 := by
    apply le_antisymm
    · exact (hm.monotone (hmin hz₁)).trans_eq hpre
    · apply hmin
      simpa only [map_one] using hm hexp
  have hid (x : ℤᵐ⁰) : f x = x := by
    obtain rfl | hx := eq_or_ne x 0
    · exact map_zero f
    lift x to ℤ using hx
    have he (a : ℤ) : WithZero.exp a = (WithZero.exp (1 : ℤ)) ^ a := by
      rw [← WithZero.exp_zsmul]
      exact congrArg WithZero.exp (by simp)
    rw [he, map_zpow₀, hf₁]
  intro z
  change eK (valuation K (algebraMap F K z)) = eF (valuation F z)
  rw [← hv, hid]

/-- A finite intermediate field of the maximal unramified extension is
contained in a finite Galois unramified stage. -/
theorem finiteUnramifiedStage {B : IntermediateField F (SeparableClosure F)}
    [FiniteDimensional F B] (hB : B ≤ maximalUnramified F) :
    ∃ E : FiniteGaloisIntermediateField F (SeparableClosure F),
      IsUnramified F E ∧ B ≤ E.toIntermediateField := by
  obtain ⟨a, ha⟩ := Field.exists_primitive_element F B
  obtain ⟨U, hU, haU⟩ := mem_maximalUnramified_iff.mp (hB a.property)
  have hBU : B ≤ U := by
    have he : IntermediateField.adjoin F ({(a : SeparableClosure F)} : Set (SeparableClosure F)) = B := by
      change IntermediateField.adjoin F ({B.val a} : Set (SeparableClosure F)) = B
      rw [← Set.image_singleton (f := B.val) (a := a), ← IntermediateField.adjoin_map, ha,
        ← AlgHom.fieldRange_eq_map, B.fieldRange_val]
    rw [← he]
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr haU)
  obtain ⟨n, hn, hUn⟩ := le_cyclotomicStage_of_unramified hU
  let p : F[X] := X ^ n - Polynomial.C 1
  have hnF : (n : F) ≠ 0 := by
    intro hz
    apply hn
    have hzO : (n : (valuation F).valuationSubring) = 0 := by
      apply Subtype.ext
      simpa using hz
    simpa only [map_natCast, map_zero] using
      congrArg (IsLocalRing.residue (valuation F).valuationSubring) hzO
  have hsep : p.Separable := separable_X_pow_sub_C 1 hnF one_ne_zero
  have hsplit : (p.map (algebraMap F (SeparableClosure F))).Splits :=
    IsSepClosed.splits_codomain p hsep
  let K := cyclotomicStage F n
  let : p.IsSplittingField F K := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  let : IsGalois F K := IsGalois.of_separable_splitting_field hsep
  have hK : IsUnramified F K := (cyclotomicStage_data hn).1
  exact ⟨{ K with finiteDimensional := hK.1, isGalois := inferInstance },
    hK, hBU.trans hUn⟩

/-- A continuous cocycle trivial on the fixing group of the maximal unramified
extension descends to a finite unramified Galois group with the corresponding
kernel-fixed coefficients. -/
theorem cocycleDescendsAtUnramifiedLevel
    {M : Type v} [Group M] [TopologicalSpace M] [DiscreteTopology M]
    {ρ : Gal(SeparableClosure F/F) →* MulAut M} (a : Cocycle ρ)
    (ha : ∀ σ ∈ (maximalUnramified F).fixingSubgroup, a σ = 1) :
    ∃ (E : FiniteGaloisIntermediateField F (SeparableClosure F))
      (c : Cocycle (levelAction ρ E)), IsUnramified F E ∧ DescendsAt ρ a E c := by
  let U : Subgroup Gal(SeparableClosure F/F) :=
    { carrier := {σ | a σ = 1}
      one_mem' := a.map_one
      mul_mem' := fun {σ τ} hσ hτ => by
        change a σ = 1 at hσ
        change a τ = 1 at hτ
        change a (σ * τ) = 1
        simp [a.property.2, hσ, hτ]
      inv_mem' := fun {σ} hσ => by
        change a σ = 1 at hσ
        change a σ⁻¹ = 1
        have h := a.property.2 σ⁻¹ σ
        simpa [hσ] using h.symm }
  have hclosed : IsClosed (U : Set Gal(SeparableClosure F/F)) :=
    (isClosed_discrete ({1} : Set M)).preimage a.property.1
  let B := IntermediateField.fixedField U
  have hBK : B ≤ maximalUnramified F := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (maximalUnramified F)]
    exact IntermediateField.fixedField_le ha
  obtain ⟨L, hL⟩ := (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois _).mp
    (eventually_trivial a)
  have hBL : B ≤ L.toIntermediateField := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup L.toIntermediateField]
    exact IntermediateField.fixedField_le hL
  let f := IntermediateField.inclusion hBL
  let : FiniteDimensional F B := FiniteDimensional.of_injective f.toLinearMap f.injective
  obtain ⟨E, hE, hBE⟩ := finiteUnramifiedStage hBK
  have hfix : B.fixingSubgroup = U :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U, hclosed⟩
  have hker : ∀ σ ∈ (restriction E).ker, a σ = 1 := by
    rw [restriction_ker]
    intro σ hσ
    have hm := IntermediateField.fixingSubgroup_le hBE hσ
    rwa [hfix] at hm
  obtain ⟨c, hc⟩ := descend_of_trivial_on_kernel
    (AlgEquiv.restrictNormalHom_surjective (SeparableClosure F)) a hker
  exact ⟨E, c, hE, hc⟩

set_option maxHeartbeats 600000 in
/-- Inflation from an unramified finite stage can be expressed using actual
rational points and their coefficient action. -/
theorem pointCocycleDescendsAtUnramifiedLevel
    (G : Specs.GroupScheme F)
    (a : @Cocycle (Gal(SeparableClosure F/F))
      (LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F (SeparableClosure F) G.X)
      _ (krullTopology F (SeparableClosure F)) _ ⊥ (pointAction F (SeparableClosure F) G.X))
    (ha : ∀ σ ∈ (maximalUnramified F).fixingSubgroup, a σ = 1) :
    ∃ (E : FiniteGaloisIntermediateField F (SeparableClosure F))
      (r : ValuativeRel E) (T : TopologicalSpace E),
      letI := r
      letI := T
      ∃ (hlocal : IsNonarchimedeanLocalField E) (_ : ValuativeExtension F E),
        letI := hlocal
        Specs.ExceptionalAffineBruhat.IsUnramifiedLocalExtension F E ∧
        ∃ c : Gal(E/F) → LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F E G.X,
          (∀ σ τ, c (σ * τ) = c σ * pointAction F E G.X σ (c τ)) ∧
          ∀ σ, pointMap F E G.X E.toIntermediateField.val (c (restriction E σ)) = a σ := by
  let : TopologicalSpace (LinearAlgebraicGroups.Descent.NonabelianCohomology.Points
    F (SeparableClosure F) G.X) := ⊥
  let : DiscreteTopology (LinearAlgebraicGroups.Descent.NonabelianCohomology.Points
    F (SeparableClosure F) G.X) := ⟨rfl⟩
  obtain ⟨E, c, ⟨_, _, r, T, hlocal, hext, hs⟩, hc⟩ :=
    cocycleDescendsAtUnramifiedLevel a ha
  let := r
  let := T
  obtain ⟨e, hmap, hact⟩ := finitePointsIdentification (H := G.X) E
  refine ⟨E, r, T, hlocal, hext, unramifiedLocalExtensionOfSurjectiveValues hs,
    fun σ => e.symm (c σ), ?_, ?_⟩
  · intro σ τ
    apply e.injective
    simpa only [MulEquiv.apply_symm_apply, map_mul, hact] using c.property.2 σ τ
  · intro σ
    rw [← hmap, MulEquiv.apply_symm_apply, hc]

end UnramifiedDescent

section PinnedReference

open _root_.LinearAlgebraicGroups.Specs
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence relativePoints)
open _root_.LinearAlgebraicGroups.Descent.Forms (SchemeModels)
open Specs.Pinning (AttachedDatum PinnedGroup)
open Specs.QuasiSplitInnerForms (AreInnerForms PinnedRepresentative basedAutTopology
  fieldGalTopology basedAutDiscrete outerHom trivialOuterAction)
open Specs.RelativeFormComparison (fieldTest transportedAut)
open Specs.RootGroups (AdditiveLine)
open LinearAlgebraicGroups.Descent.NonabelianCohomology (Cocycle restriction)
open LinearAlgebraicGroups.Descent.QuasiSplitInnerForms (splitCoefficientMaps)
open LinearAlgebraicGroups.Descent.AutomorphismSequence (twists_of_exactSequence)
attribute [local instance] basedAutTopology fieldGalTopology basedAutDiscrete

open private pinnedRepresentatives innerComparison from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms

universe u

set_option maxHeartbeats 2000000 in
/-- The given outer homomorphism determines a pinned quasi-split reference,
and equality of the actual projected cocycles makes the given form inner to
that reference. -/
theorem existsPinnedInnerReference
    {F S : Type u} [Field F] [Field S] [Algebra F S] [IsSepClosure F S]
    {A : AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (E : SplitSequence P D l Q) (L : FiniteGaloisIntermediateField F S)
    (ω : Gal(L/F) →* Aut D.toBased)
    (H : SchemeModels S P.pair.G)
    (i : relativePoints P.pair.G.val (fieldTest F S) ≅
      relativePoints H.val.val (fieldTest F S))
    (hi : ∀ σ, outerHom (S := S) E (transportedAut F S i σ) = ω (restriction L σ)) :
    ∃ (outerCocycle : Cocycle (trivialOuterAction (k := F) (S := S) D.toBased))
      (V : PinnedRepresentative (S := S) E outerCocycle),
      (∀ σ, outerCocycle σ = ω (restriction L σ)) ∧
        AreInnerForms (S := S) V.model.val H.val := by
  let outerCocycle : Cocycle (trivialOuterAction (k := F) (S := S) D.toBased) :=
    ⟨fun σ => ω (restriction L σ),
      continuous_of_discreteTopology.comp
        (InfiniteGalois.restrictNormalHom_continuous L.toIntermediateField),
      fun σ τ => by
        change ω (restriction L (σ * τ)) = ω (restriction L σ) * ω (restriction L τ)
        rw [map_mul, map_mul]⟩
  obtain ⟨V⟩ := pinnedRepresentatives E outerCocycle
  obtain ⟨Qv, _, Ev, _, _⟩ := twists_of_exactSequence E.toExactSequence V.model.val
    ⟨S, ‹Field S›, ‹Algebra F S›, ‹IsSepClosure F S›, V.model.property⟩
  refine ⟨outerCocycle, V, fun _ => rfl, Qv, Ev.inner, Ev.onLift, Ev.innerInjective,
    V.trivialization.symm ≪≫ i, ?_⟩
  apply (innerComparison E Qv Ev.inner Ev.onLift Ev.innerInjective V.trivialization i).mpr
  intro σ
  rw [hi, V.transport_eq, (splitCoefficientMaps (S := S) E).2.2]

end PinnedReference

section InnerCocycle

open AlgebraicGeometry Opposite
open _root_.LinearAlgebraicGroups.Specs
open Specs.AutomorphismSequence (AdjointQuotient relativePoints)
open Specs.ExceptionalTwistedTraceComparison (PointCocycle)
open Specs.QuasiSplitInnerForms (AreInnerForms relativeAutTopology relativeAutDiscrete)
open Specs.RelativeFormComparison (fieldTest fieldMap transportedAut automorphismAction)
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology
open private modelOfRelativeIso isoOfInvariant from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
open private transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private reductive_of_geometric_iso borel_of_square from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.PinnedPairDescent

attribute [local instance] relativeAutTopology relativeAutDiscrete

universe u

set_option maxHeartbeats 1400000 in
/-- Neutrality of the adjoint cocycle for a particular inner form descends
the corresponding isomorphism to the base field. -/
theorem existsInnerFormCocycle {F S : Type u} [Field F] [Field S] [Algebra F S]
    [IsSepClosure F S] (G H : AffineAlgebraicGroup F) (h : AreInnerForms (S := S) G H) :
    ∃ (Q : AdjointQuotient G) (a : PointCocycle (S := S) Q.quotient.val),
      (∃ b : Descent.NonabelianCohomology.Points F S Q.quotient.val.X,
        ∀ σ, a.val σ = b * (pointAction F S Q.quotient.val.X σ b)⁻¹) →
          Nonempty (G.val ≅ H.val) := by
  obtain ⟨Q, inn, _, hinj, i, hi⟩ := h
  let : TopologicalSpace (Descent.NonabelianCohomology.Points F S Q.quotient.val.X) := ⊥
  obtain ⟨C⟩ := LinearAlgebraicGroups.Descent.RelativeFormComparison.relativeFormClassification
    (S := S) G
  obtain ⟨a, ha, _⟩ := C.computes (modelOfRelativeIso G H i) i
  obtain ⟨d, hd, _⟩ := LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.liftInnerCocycle
    G.val Q.quotient.val inn (hinj _) a (fun σ => ha σ ▸ hi σ)
  refine ⟨Q, d, ?_⟩
  rintro ⟨b, hb⟩
  let p : Descent.NonabelianCohomology.Points F S Q.quotient.val.X →*
      AutomorphismSequence.RelativeAut G.val (fieldTest F S) :=
    (inn.app (op (fieldTest F S))).hom.comp
      { toFun := ULift.up, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hequiv (σ : Gal(S/F)) (x : Descent.NonabelianCohomology.Points F S Q.quotient.val.X) :
      p (pointAction F S Q.quotient.val.X σ x) = automorphismAction F S G.val σ (p x) :=
    ConcreteCategory.congr_hom (inn.naturality (fieldMap F S σ).op) (ULift.up x)
  let j := (p b).asIso ≪≫ i
  have hj (σ : Gal(S/F)) : transportedAut F S j σ = 1 := by
    have hp : p (d σ) = transportedAut F S i σ := (hd σ).trans (ha σ)
    rw [LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.changeOfTrivialization,
      ← hp, hb, map_mul, map_inv, hequiv, inv_mul_cancel_left, inv_mul_cancel]
  apply isoOfInvariant C j
  intro σ
  have he := congrArg Aut.asIso (hj σ)
  change AutomorphismSequence.restrictIso (fieldMap F S σ) j ≪≫ j.symm = Iso.refl _ at he
  simpa only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl, Iso.refl_trans] using
    congrArg (fun e => e ≪≫ j) he

set_option maxHeartbeats 1200000 in
/-- An isomorphism over the ground field transports the Borel over that field. -/
theorem isQuasiSplitOfIso {F : Type u} [Field F] {G H : AffineAlgebraicGroup F}
    (e : G.val ≅ H.val) (h : GeometricBorelConjugacy.IsQuasiSplit G) :
    GeometricBorelConjugacy.IsQuasiSplit H := by
  obtain ⟨hG, B, hB, hgeom⟩ := h
  let e' := (groupBaseChange F (AlgebraicClosure F)).mapIso e
  let C := transportSubgroup e B
  refine ⟨reductive_of_geometric_iso e' hG, C, ?_⟩
  have hC : AlgebraicGeometry.IsClosedImmersion
      ((groupBaseChange F (AlgebraicClosure F)).map C.inclusion).hom.hom.left := by
    let := hB
    have : IsIso e'.hom.hom.hom.left :=
      (Grp.forget _ ⋙ CategoryTheory.Over.forget _).map_isIso e'.hom
    change AlgebraicGeometry.IsClosedImmersion
      (((groupBaseChange F (AlgebraicClosure F)).map (B.inclusion ≫ e.hom)).hom.hom.left)
    rw [Functor.map_comp]
    exact inferInstanceAs (AlgebraicGeometry.IsClosedImmersion
      (((groupBaseChange F (AlgebraicClosure F)).map B.inclusion).hom.hom.left ≫
        e'.hom.hom.hom.left))
  refine ⟨hC, borel_of_square (X := GeometricRadicals.GeometricGroup G)
    (Y := GeometricRadicals.GeometricGroup H) e' _ _ (Iso.refl _) ?_ hgeom⟩
  change 𝟙 _ ≫ (groupBaseChange F (AlgebraicClosure F)).map (B.inclusion ≫ e.hom) =
    (groupBaseChange F (AlgebraicClosure F)).map B.inclusion ≫ e'.hom
  rw [Category.id_comp, Functor.map_comp]
  rfl

end InnerCocycle

section RamifiedCoordinates

open IsLocalRing ValuativeRel
open Specs.ExceptionalAffineBruhat (residue)
attribute [local instance] Specs.ExceptionalLocalRootCoordinates.canonicalExtension

open private restrictToIntegers from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer

variable {k K E : Type*} [Field k] [Field K] [Field E] [Algebra k K] [Algebra K E]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension k K] [ValuativeExtension K E]

local notation "𝒪" L => Valuation.integer (valuation L)

/-- In an extension with unchanged finite residue field, the reduction of
an integral parameter is fixed by every automorphism over the base. -/
theorem ramifiedAutomorphismFixesResidue [FiniteDimensional k K]
    (hκ : Nat.card (residue k) = Nat.card (residue K)) (τ : Gal(K/k)) :
    ∃ t : (𝒪 K) ≃ₐ[(𝒪 k)] (𝒪 K), (∀ b : 𝒪 K, (t b : K) = τ (b : K)) ∧
      ∀ b, IsLocalRing.residue (𝒪 K) (t b) = IsLocalRing.residue (𝒪 K) b := by
  let t := restrictToIntegers τ
  refine ⟨t, fun _ => rfl, ?_⟩
  let f := IsLocalRing.ResidueField.map (algebraMap (𝒪 k) (𝒪 K))
  have hsurj : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨f.injective, hκ⟩).2
  intro b
  obtain ⟨v, hv⟩ := hsurj (IsLocalRing.residue (𝒪 K) b)
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective v
  change IsLocalRing.residue (𝒪 K) (algebraMap (𝒪 k) (𝒪 K) c) = _ at hv
  let : IsLocalHom t.toRingHom := IsLocalHom.of_surjective _ t.surjective
  have hfix := congrArg (IsLocalRing.ResidueField.map t.toRingHom) hv
  change IsLocalRing.residue (𝒪 K) (t (algebraMap (𝒪 k) (𝒪 K) c)) =
    IsLocalRing.residue (𝒪 K) (t b) at hfix
  rw [AlgEquiv.commutes, hv] at hfix
  exact hfix.symm

/-- The conjugate of a uniformizer differs from it by an integral unit. -/
theorem conjugateUniformizerRatio [FiniteDimensional k K]
    (τ : Gal(K/k)) (π : 𝒪 K) (hπ : (valuation K).IsUniformizer (π : K)) :
    ∃ ε : (𝒪 K)ˣ, τ (π : K) = ((ε : 𝒪 K) : K) * (π : K) := by
  let t := restrictToIntegers τ
  have hgen : maximalIdeal (𝒪 K) = Ideal.span ({π} : Set (𝒪 K)) := hπ.is_generator
  have hid : Ideal.span {t π} = Ideal.span {π} := by
    calc
      Ideal.span {t π} = (Ideal.span {π}).map t.toRingHom := by
        rw [Ideal.map_span, Set.image_singleton]
        rfl
      _ = Ideal.span {π} := by
        rw [← hgen]
        exact IsLocalRing.map_ringEquiv_maximalIdeal t.toRingEquiv
  obtain ⟨ε, he⟩ := Ideal.span_singleton_eq_span_singleton.mp hid.symm
  refine ⟨ε, ?_⟩
  have h := congrArg (fun x : 𝒪 K => (x : K)) he
  change (π : K) * ((ε : 𝒪 K) : K) = τ (π : K) at h
  simpa only [mul_comm] using h.symm

/-- Scaling the two members of a paired root orbit gives the same depth
shift. After extracting the common power of the auxiliary uniformizer,
the two residues are a free leading coefficient multiplied by the two
marking units and by the residue of the conjugate-uniformizer ratio. -/
theorem scaledPairedRootCoefficients [FiniteDimensional k K]
    (hκ : Nat.card (residue k) = Nat.card (residue K)) (τ : Gal(K/k))
    (π : Kˣ) (ξ : Eˣ) (d : ℕ) (hξ : (ξ : E) ^ d = algebraMap K E (π : K))
    (ε : (𝒪 K)ˣ) (hε : τ (π : K) = ((ε : 𝒪 K) : K) * (π : K))
    (c₁ c₂ : (𝒪 E)ˣ) (s m : ℤ) (b : 𝒪 K) :
    ∃ z₁ z₂ : 𝒪 E,
      (ξ : E) ^ s * (c₁ : 𝒪 E) * algebraMap K E ((π : K) ^ m * (b : K)) =
        (ξ : E) ^ (s + (d : ℤ) * m) * (z₁ : E) ∧
      (ξ : E) ^ s * (c₂ : 𝒪 E) * algebraMap K E (τ ((π : K) ^ m * (b : K))) =
        (ξ : E) ^ (s + (d : ℤ) * m) * (z₂ : E) ∧
      let red := IsLocalRing.residue (𝒪 E)
      let f := algebraMap (𝒪 K) (𝒪 E)
      red z₁ = red c₁ * red (f b) ∧
      red z₂ = (red c₂ * red (f ((ε ^ m : (𝒪 K)ˣ) : 𝒪 K))) * red (f b) := by
  obtain ⟨τ₀, hτ₀, hτ⟩ := ramifiedAutomorphismFixesResidue hκ τ
  let f := algebraMap (𝒪 K) (𝒪 E)
  let z₁ : 𝒪 E := (c₁ : 𝒪 E) * f b
  let z₂ : 𝒪 E := (c₂ : 𝒪 E) * f ((ε ^ m : (𝒪 K)ˣ) : 𝒪 K) * f (τ₀ b)
  have fcoe (z : 𝒪 K) : (f z : E) = algebraMap K E (z : K) := rfl
  have mulcoe (z w : 𝒪 E) : ((z * w : 𝒪 E) : E) = (z : E) * (w : E) := rfl
  have unitcoe : (((ε ^ m : (𝒪 K)ˣ) : 𝒪 K) : K) = (((ε : 𝒪 K) : K) ^ m) := by
    let i := (valuation K).valuationSubring.subtype.toMonoidHom
    change ((Units.map i (ε ^ m) : Kˣ) : K) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  have hpow : (ξ : E) ^ (s + (d : ℤ) * m) = (ξ : E) ^ s * (algebraMap K E (π : K)) ^ m := by
    rw [zpow_add₀ (Units.ne_zero ξ), zpow_mul, zpow_natCast, hξ]
  refine ⟨z₁, z₂, ?_, ?_, ?_⟩
  · rw [hpow, map_mul, map_zpow₀]
    simp only [z₁, mulcoe, fcoe]
    ac_rfl
  · rw [hpow, map_mul τ, map_zpow₀, hε, mul_zpow, map_mul, map_mul, map_zpow₀, map_zpow₀]
    simp only [z₂, mulcoe, fcoe, unitcoe, hτ₀, map_zpow₀]
    ring
  · let red := IsLocalRing.residue (𝒪 E)
    have hb : red (f (τ₀ b)) = red (f b) := by
      simpa only [IsLocalRing.ResidueField.map_residue] using
        congrArg (IsLocalRing.ResidueField.map f) (hτ b)
    change red z₁ = red c₁ * red (f b) ∧
      red z₂ = (red c₂ * red (f ((ε ^ m : (𝒪 K)ˣ) : 𝒪 K))) * red (f b)
    exact ⟨map_mul red _ _, by simp only [z₂, map_mul, hb]⟩

end RamifiedCoordinates

/-- A rational point of the cocharacter apartment has a positive integral
multiple in the cocharacter lattice. -/
theorem clearCocharacterDenominators {Y : Type*} [AddCommGroup Y] (x : ℚ ⊗[ℤ] Y) :
    ∃ (d : ℕ) (y : Y), 0 < d ∧ (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y := by
  induction x using TensorProduct.inductionOn with
  | tmul q y =>
    refine ⟨q.den, q.num • y, q.den_pos, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_comm, Rat.mul_den_eq_num,
      ← TensorProduct.smul_tmul (R := ℤ) q.num (1 : ℚ) y]
    simp
  | add x y hx hy =>
    obtain ⟨d, a, hd, ha⟩ := hx
    obtain ⟨e, b, he, hb⟩ := hy
    refine ⟨d * e, e • a + d • b, Nat.mul_pos hd he, ?_⟩
    rw [Nat.cast_mul, smul_add, mul_comm (d : ℚ) (e : ℚ), ← smul_smul, ha,
      mul_comm (e : ℚ) (d : ℚ), ← smul_smul, hb, TensorProduct.tmul_add]
    have h (n : ℕ) (v : Y) : (n : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] v) = (1 : ℚ) ⊗ₜ[ℤ] (n • v) := by
      rw [Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℤ (b := v), TensorProduct.tmul_smul]
      exact (Nat.cast_smul_eq_nsmul ℚ _ _).symm
    rw [h e a, h d b]

/-- A subgroup with a nonempty relatively open subset in its closure is
closed. Separate continuity of translations suffices for the Zariski
topology on geometric points. -/
theorem subgroupClosedOfRelativelyOpenSubset
    {G : Type*} [Group G] [TopologicalSpace G]
    (hleft : ∀ g : G, Continuous (g * ·))
    (hright : ∀ g : G, Continuous (· * g))
    (hinv : Continuous (Inv.inv : G → G))
    (H : Subgroup G) (U : Set G) (hU : IsOpen U)
    (hne : (U ∩ (H : Set G)).Nonempty)
    (hsub : U ∩ closure (H : Set G) ⊆ H) :
    IsClosed (H : Set G) := by
  obtain ⟨u, hu, huH⟩ := hne
  apply closure_subset_iff_isClosed.mp
  intro x hx
  have hmap : Set.MapsTo (fun y => y⁻¹ * u) (H : Set G) (H : Set G) :=
    fun y hy => H.mul_mem (H.inv_mem hy) huH
  have hx' := hmap.closure ((hright u).comp hinv) hx
  have hmem : x⁻¹ * u ∈ (x * ·) ⁻¹' U := by
    change x * (x⁻¹ * u) ∈ U
    simpa using hu
  obtain ⟨h, hhU, hh⟩ := mem_closure_iff.mp hx' _ (hU.preimage (hleft x)) hmem
  have hmap' : Set.MapsTo (· * h) (H : Set G) (H : Set G) := fun y hy => H.mul_mem hy hh
  have hxH : x * h ∈ H := hsub ⟨hhU, hmap'.closure (hright h) hx⟩
  simpa using H.mul_mem hxH (H.inv_mem hh)

/-- A trace-one element contracts the additive cocycle equation for a semilinear
action. This works also when the characteristic divides the extension degree. -/
theorem semilinearCocycleIsCoboundary
    {k K V : Type*} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] [AddCommGroup V] [Module K V]
    (ρ : Gal(K/k) → AddAut V)
    (hsmul : ∀ (σ : Gal(K/k)) (t : K) (v : V), ρ σ (t • v) = σ t • ρ σ v)
    (a : Gal(K/k) → V) (ha : ∀ σ τ, a (σ * τ) = a σ + ρ σ (a τ)) :
    ∃ b : V, ∀ σ, a σ = b - ρ σ b := by
  classical
  obtain ⟨t, ht⟩ := Algebra.trace_surjective k K (1 : k)
  have htrace : ∑ σ : Gal(K/k), σ t = 1 :=
    (trace_eq_sum_automorphisms (K := k) t).symm.trans (by rw [ht, map_one])
  let b : V := ∑ τ : Gal(K/k), τ t • a τ
  refine ⟨b, fun σ => eq_sub_of_add_eq ?_⟩
  have htranslate :
      (∑ τ : Gal(K/k), (σ * τ) t • a (σ * τ)) = b := by
    exact Fintype.sum_equiv (Equiv.mulLeft σ) _ _ (fun τ => rfl)
  have hweights : ∑ τ : Gal(K/k), (σ * τ) t = 1 := by
    rw [← htrace]
    exact Fintype.sum_equiv (Equiv.mulLeft σ) _ _ (fun τ => rfl)
  calc
    a σ + ρ σ b = (∑ τ : Gal(K/k), (σ * τ) t) • a σ + ρ σ b := by rw [hweights, one_smul]
    _ = ∑ τ : Gal(K/k), (σ * τ) t • a (σ * τ) := by
      change _ + ρ σ (∑ τ : Gal(K/k), τ t • a τ) = _
      rw [map_sum, Finset.sum_smul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro τ _
      rw [ha, smul_add, hsmul]
      rfl
    _ = b := htranslate

section Filtration

variable {Γ P : Type*} [Group Γ] [Group P]
variable (ρ : Γ →* MulAut P)

private theorem changedCocycleLaw (a : Γ → P)
    (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) (b : P) (σ τ : Γ) :
    b⁻¹ * a (σ * τ) * ρ (σ * τ) b =
      (b⁻¹ * a σ * ρ σ b) * ρ σ (b⁻¹ * a τ * ρ τ b) := by
  simp only [ha, map_mul, map_inv, MulAut.mul_apply]
  group

/-- Corrections along a separated congruence filtration give a coboundary
when the set of corrections is compact. This uses nested closed sets of
corrections, so no choice of a convergent subsequence of products is needed. -/
theorem compactFiltrationCoboundary [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] (hρ : ∀ σ, Continuous (ρ σ : P → P))
    (N : ℕ → Subgroup P) (hN : Antitone N)
    (hclosed : ∀ n, IsClosed (N n : Set P))
    (hsep : ∀ x : P, (∀ n, x ∈ N n) → x = 1)
    (hstep : ∀ n (c : Γ → P), (∀ σ τ, c (σ * τ) = c σ * ρ σ (c τ)) →
      (∀ σ, c σ ∈ N n) →
      ∃ d : N n, ∀ σ, (d : P)⁻¹ * c σ * ρ σ d ∈ N (n + 1))
    (a : Γ → P) (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ))
    (hfirst : ∃ b : P, ∀ σ, b⁻¹ * a σ * ρ σ b ∈ N 0) :
    ∃ b : P, ∀ σ, a σ = b * (ρ σ b)⁻¹ := by
  let S (n : ℕ) : Set P := {b | ∀ σ, b⁻¹ * a σ * ρ σ b ∈ N n}
  have hnest : Antitone S := fun _ _ h _ hb σ => hN h (hb σ)
  have hcl : ∀ n, IsClosed (S n) := by
    intro n
    have hset : S n = ⋂ σ : Γ, (fun b : P => b⁻¹ * a σ * ρ σ b) ⁻¹' (N n : Set P) := by
      ext b
      simp [S]
    rw [hset]
    exact isClosed_iInter fun σ => (hclosed n).preimage
      ((continuous_inv.mul continuous_const).mul (hρ σ))
  have hnonempty : ∀ n, (S n).Nonempty := by
    intro n
    induction n with
    | zero => exact hfirst
    | succ n ih =>
      obtain ⟨b, hb⟩ := ih
      obtain ⟨d, hd⟩ := hstep n _ (changedCocycleLaw ρ a ha b) hb
      refine ⟨b * (d : P), fun σ => ?_⟩
      simpa only [mul_inv_rev, map_mul, mul_assoc] using hd σ
  obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S (fun n => hnest (Nat.le_succ n)) hnonempty (hcl 0).isCompact hcl
  refine ⟨b, fun σ => ?_⟩
  have he := hsep (b⁻¹ * a σ * ρ σ b) (fun n => (Set.mem_iInter.mp hb n) σ)
  calc
    a σ = b * (b⁻¹ * a σ * ρ σ b) * (ρ σ b)⁻¹ := by group
    _ = b * (ρ σ b)⁻¹ := by rw [he, mul_one]

variable {k K V : Type*} [Field k] [Field K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [AddCommGroup V] [Module K V]

/-- A surjective leading-coordinate map with semilinear coefficient action
gives the correcting element for one congruence layer. -/
theorem semilinearLayerCorrection
    (ρ : Gal(K/k) →* MulAut P) (N N' : Subgroup P)
    (hstable : ∀ σ (n : N), ρ σ n ∈ N)
    (red : N →* Multiplicative V) (hsurj : Function.Surjective red)
    (hker : ∀ n : N, red n = 1 ↔ (n : P) ∈ N')
    (ψ : Gal(K/k) → AddAut V)
    (hsmul : ∀ (σ : Gal(K/k)) (t : K) (v : V), ψ σ (t • v) = σ t • ψ σ v)
    (hequiv : ∀ σ (n : N), (red ⟨ρ σ n, hstable σ n⟩).toAdd = ψ σ (red n).toAdd)
    (a : Gal(K/k) → P) (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ))
    (hmem : ∀ σ, a σ ∈ N) :
    ∃ d : N, ∀ σ, (d : P)⁻¹ * a σ * ρ σ d ∈ N' := by
  let c (σ : Gal(K/k)) : N := ⟨a σ, hmem σ⟩
  have hc (σ τ : Gal(K/k)) : c (σ * τ) = c σ * ⟨ρ σ (c τ), hstable σ (c τ)⟩ :=
    Subtype.ext (ha σ τ)
  obtain ⟨b, hb⟩ := semilinearCocycleIsCoboundary ψ hsmul (fun σ => (red (c σ)).toAdd)
    (fun σ τ => by rw [hc, map_mul]; exact congrArg ((red (c σ)).toAdd + ·) (hequiv σ (c τ)))
  obtain ⟨d, hd⟩ := hsurj (Multiplicative.ofAdd b)
  refine ⟨d, fun σ => (hker (d⁻¹ * c σ * ⟨ρ σ d, hstable σ d⟩)).mp ?_⟩
  rw [map_mul, map_mul, map_inv, hd]
  change -b + (red (c σ)).toAdd + (red ⟨ρ σ d, hstable σ d⟩).toAdd = 0
  rw [hequiv, hd, hb]
  change -b + (b - ψ σ b) + ψ σ b = 0
  abel

end Filtration

section Building

open _root_.LinearAlgebraicGroups.Specs
open ExceptionalAffineBruhat ExceptionalAffineBuilding
open ExceptionalAffineRootSystems (ApartmentRoots alcoveStabilizer threshold)
open IntegralSemisimpleModel (Model)
open Pinning (BasedRootDatum)
open scoped WithZero

universe u v

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G Wf V Γ : Type u} {J : Type v} [Group G] [Group Wf] [Group Γ]
  [AddCommGroup V] [Module ℚ V] {j : G →* FieldPoints M K}
  {A : ApartmentRoots ℚ V J} {p : V} {C : LocalComparison (j := j) (Wf := Wf) A p}

private theorem realAffine_one (r : RealCoordinates V) (x : EuclideanApartment V) :
    realAffine r r 1 x = x := by
  change r ((LinearMap.id : V →ₗ[ℚ] V).baseChange ℝ (r.symm x) + 1 ⊗ₜ[ℚ] (0 : V)) = x
  simp [LinearMap.baseChange_id]

private theorem standardPointInChart (X : Building C) (t : Weights (A.SimpleWall p)) :
    X.realization.chart 1 (simplexPoint X.realization.coordinates X.realization.vertex t) =
      X.realization.place 1 t := by
  let n : C.G₀ := ⟨(C.lift 1 : G), X.realization.lift_mem 1⟩
  have hn : (n : G) ∈ C.T₀ := by
    have hk : C.affine.ker.map C.N.subtype = C.T₀ := C.kernel
    rw [← hk]
    exact Subgroup.mem_map.mpr ⟨C.lift 1, by rw [MonoidHom.mem_ker, C.lift_label]; rfl, rfl⟩
  have hi : (n : G) ∈ C.I := by
    rw [← X.iwahori_inter_normalizer] at hn
    exact hn.1
  have hp : X.realization.place n t = X.realization.place 1 t :=
    (X.realization.place_eq n 1 t t).mpr ⟨rfl, by
      change (n : G)⁻¹ * 1 ∈ parahoric C (cotype t)
      rw [mul_one]
      exact Subgroup.subset_closure (Or.inl (C.I.inv_mem hi))⟩
  have h := X.realization.chart_place 1 1 t
  change X.realization.chart 1 (realAffine _ _ 1 (simplexPoint _ _ t)) =
    X.realization.place (1 * n) t at h
  simpa only [realAffine_one, one_mul, hp] using h

private theorem cotypeNeUniv {B : Type*} (t : Weights B) : cotype t ≠ Set.univ := by
  intro h
  have hzero : t.val = 0 := funext fun b => by
    have hb : b ∈ cotype t := h.symm ▸ Set.mem_univ b
    exact hb
  simpa [hzero] using t.property.2

private theorem parahoricPreserved (X : Building C) (T : Set (A.SimpleWall p))
    {s : MulAut G} (hs : AutomorphismComparison C s 1) :
    ∀ g ∈ parahoric C T, s g ∈ parahoric C T := by
  obtain ⟨hI, _, _, _, _, _, _, hlift⟩ := hs
  have hT₀ : C.T₀ ≤ parahoric C T := by
    rw [← X.iwahori_inter_normalizer]
    exact fun g hg => Subgroup.subset_closure (Or.inl hg.1)
  change parahoric C T ≤ (parahoric C T).comap s.toMonoidHom
  apply (Subgroup.closure_le _).mpr
  rintro g (hg | ⟨a, ha, rfl⟩)
  · change s g ∈ parahoric C T
    have hi : s g ∈ C.I := by
      rw [← hI]
      exact Subgroup.mem_map.mpr ⟨_, hg, rfl⟩
    exact Subgroup.subset_closure (Or.inl hi)
  · let w := C.coxeter.coxeter.simple a
    change s (C.lift w : G) ∈ parahoric C T
    obtain ⟨v, hv, hmem⟩ := hlift w
    have hvw : v = w := Subtype.ext (by simpa using hv)
    subst v
    have hsimple : (C.lift w : G) ∈ parahoric C T :=
      Subgroup.subset_closure (Or.inr ⟨a, ha, rfl⟩)
    have hh := (parahoric C T).mul_mem (hT₀ hmem) hsimple
    simpa only [inv_mul_cancel_right] using hh

private theorem rationalWallValue (r : RealCoordinates V) (a : J × ℤ) (x : V) :
    realWallValue A r a (rationalPoint r x) = (A.root a.1 x : ℝ) + (a.2 : ℝ) := by
  simp only [realWallValue, rationalPoint, ExceptionalRealAlcove.realWallValue,
    ExceptionalRealAlcove.rationalPoint, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul,
    TensorProduct.AlgebraTensorModule.rid_tmul, Rat.smul_def, mul_one]

set_option maxHeartbeats 600000 in
/-- Each nonzero root parameter in the marked Iwahori chart has nonnegative
scaled depth at a rational point of the closed standard alcove. The root
functional and valuation exponent are both in the units of that parameter's
field. -/
theorem iwahoriRootDepthsAtFace (X : Building C) (q : ℕ) (hB : C.Bruhat q)
    (t : Weights (A.SimpleWall p)) (x : V)
    (hx : rationalPoint X.realization.coordinates x =
      simplexPoint X.realization.coordinates X.realization.vertex t)
    (g : C.I) :
    ∃ (z : C.chart.chart.torus × (∀ a, C.chart.parameter a)),
      ExceptionalIwahoriCongruence.cellValue M.toIntegralMarking
        (ExceptionalIwahoriCongruence.integralRing K) C.chart.negative C.chart.positive
        (C.chart.chart.coordinates z.1 z.2) = j g ∧
      (∀ χ, ExceptionalValuedTorusNormalizer.normalizedValuation K (z.1.val χ : K) = 1) ∧
      ∀ a, C.chart.value a (z.2 a) = 0 ∨
        ∃ n : ℤ, C.chart.value a (z.2 a) = WithZero.exp (-n) ∧ 0 ≤ A.root a x + (n : ℚ) := by
  obtain ⟨z, ⟨hz, ht, hd⟩, _⟩ := (hB.base_chart g).mp g.property
  refine ⟨z, hz, ht, fun a => ?_⟩
  let v := C.chart.value a (z.2 a)
  by_cases hv : v = 0
  · exact Or.inl hv
  right
  let n := -WithZero.log v
  have hn : v = WithZero.exp (-n) := by simpa [n] using (WithZero.exp_log hv).symm
  refine ⟨n, hn, ?_⟩
  have hdepth : (threshold (A.root a p) : ℚ) ≤ (n : ℚ) := by
    apply Int.cast_le.mpr
    have hd' : v ≤ WithZero.exp (-threshold (A.root a p)) := hd a
    simpa only [hn, WithZero.exp_le_exp, neg_le_neg_iff] using hd'
  have hpos : A.positive p (a, threshold (A.root a p)) := by
    change 0 < A.root a p + (threshold (A.root a p) : ℚ)
    have hh := Int.lt_floor_add_one (-(A.root a p))
    rw [threshold, Int.cast_add, Int.cast_one]
    linarith
  have hcl := congrArg (fun s : Set (EuclideanApartment V) =>
    rationalPoint X.realization.coordinates x ∈ s) X.realization.closed_alcove
  have hwall := (Iff.of_eq hcl).mp ⟨t, hx.symm⟩ _
    hpos
  rw [rationalWallValue] at hwall
  have hwall' : 0 ≤ A.root a x + (threshold (A.root a p) : ℚ) := by exact_mod_cast hwall
  exact hwall'.trans (add_le_add_right hdepth _)

/-- A coefficient action that fixes the apartment and a trivial alcove-type
quotient allow a cocycle to be conjugated into the actual face subgroup. -/
theorem cocycleIntoParahoric [Finite Γ] {X : Building C} {Q : C.TypeQuotient}
    (ad : AdjointAction X Q) [Subsingleton (alcoveStabilizer A (A.alcove p))]
    (hcoef : AdjointCoefficientActions ad)
    (ρ : Γ →* MulAut G) (hρ : ∀ σ, AutomorphismComparison C (ρ σ) 1)
    (a : Γ → G) (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) :
    ∃ (g : C.G₀) (T : Set (A.SimpleWall p)) (t : Weights (A.SimpleWall p)) (x : V),
      cotype t = T ∧ IsBarycenter T t ∧
      rationalPoint X.realization.coordinates x = simplexPoint X.realization.coordinates X.realization.vertex t ∧
      ∀ σ, (g : G)⁻¹ * a σ * ρ σ g ∈ parahoric C T := by
  obtain ⟨coef, hequiv, htwist⟩ := hcoef Γ ρ (fun _ => 1) hρ
  obtain ⟨twist, _, htw, _, _, ⟨y, hy⟩, hface⟩ := htwist a ha
  obtain ⟨g, T, t, _, ht, hb, hplace, hfixed⟩ := hface y hy
  obtain ⟨x, hx⟩ := X.realization.barycenter_rational T t hb
  refine ⟨g, T, t, x, ht, hb, hx, fun σ => ?_⟩
  let z := X.realization.place 1 t
  have hcoefz : coef.action σ z = z := by
    change coef.action σ (X.realization.place 1 t) = X.realization.place 1 t
    rw [← standardPointInChart X t, coef.chart σ 1 1 (by simp)]
    rw [realAffine_one]
  have hstab : ad.action ((g : G)⁻¹ * a σ * ρ σ g) z = z := by
    have h := (hfixed σ).2
    rw [htw, ← hplace, ← ad.restrict, hequiv, hcoefz] at h
    simpa only [map_mul, map_inv, IsometryEquiv.trans_apply, IsometryEquiv.mul_apply,
      IsometryEquiv.inv_apply_self, z] using congrArg (ad.action ((g : G)⁻¹)) h
  have hG : C.G₀ = ⊤ := by
    rw [← ad.type_preserving]
    ext b
    have h : typeChange Q b = 1 := Subsingleton.elim _ _
    simp [h]
  have hAll (b : G) : b ∈ C.G₀ := hG.symm ▸ Subgroup.mem_top b
  let d : C.G₀ := ⟨(g : G)⁻¹ * a σ * ρ σ g, hAll _⟩
  apply (X.stabilizer T t ht d).mp
  rw [← ad.restrict d]
  exact hstab

/-- The face subgroup is compact as a finite union of double cosets of
the compact marked Iwahori. -/
theorem isCompactParahoric [TopologicalSpace G] [ContinuousMul G]
    (X : Building C) (T : Set (A.SimpleWall p)) (hT : T ≠ Set.univ)
    (hI : IsCompact (C.I : Set G)) : IsCompact (parahoric C T : Set G) := by
  let := X.realization.finite_wall_group T hT
  rw [show (parahoric C T : Set G) = _ from X.realization.face_union T]
  exact isCompact_iUnion fun w => by
    rw [DoubleCoset.doubleCoset_eq_image2, ← Set.image_uncurry_prod]
    exact (hI.prod hI).image ((continuous_fst.mul continuous_const).mul continuous_snd)

end Building

section FoldedCocycle

open _root_.LinearAlgebraicGroups.Specs
open ExceptionalAffineBruhat ExceptionalAffineBuilding
open ExceptionalValuedTorusNormalizer (invariantApartment)
open IntegralSemisimpleModel (Model)
open Pinning (BasedRootDatum)
open AdjointRepresentation (GroupPoints)

universe u

set_option maxHeartbeats 1400000 in
/-- At a finite unramified level the cocycle is conjugate into a marked
face subgroup. This uses the coefficient action on the descended group. -/
theorem foldedCocycleIntoParahoric
    {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
    [FiniteDimensional F k]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
    {σ : Gal(L/F)} (T : DiagramCompositum F L k σ) {A : FoldedApartment (R.diagram σ)}
    (Y : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A)
    {X : Building Y.comparison} (ad : AdjointAction X Y.typeQuotient)
    (hcoef : AdjointCoefficientActions ad) (hY : Y.Coefficients T)
    (a : Gal(k/F) → GroupPoints R.descent.group.val (CommAlgCat.of F k))
    (ha : ∀ s t, a (s * t) = a s * coefficientPoints R.descent.group.val s.toAlgHom (a t)) :
    ∃ (g : GroupPoints R.descent.group.val (CommAlgCat.of F k))
      (J : Set (A.roots.SimpleWall A.basepoint))
      (w : Weights (A.roots.SimpleWall A.basepoint)) (x : invariantApartment D (R.diagram σ)),
      cotype w = J ∧ J ≠ Set.univ ∧ IsBarycenter J w ∧
      rationalPoint X.realization.coordinates x = simplexPoint X.realization.coordinates X.realization.vertex w ∧
      ∀ s, g⁻¹ * a s * coefficientPoints R.descent.group.val s.toAlgHom g ∈
        parahoric Y.comparison J := by
  obtain ⟨ρ, hρ, _, hcomp⟩ := hY
  let := A.omega_trivial
  obtain ⟨g, J, w, x, hJ, hw, hx, hc⟩ :=
    cocycleIntoParahoric ad hcoef ρ (fun s => (hcomp s).1) a
      (fun s t => by rw [hρ]; exact ha s t)
  refine ⟨g, J, w, x, hJ, hJ ▸ cotypeNeUniv w, hw, hx, ?_⟩
  intro s
  exact hρ s g ▸ hc s

end FoldedCocycle

section Descent

open _root_.LinearAlgebraicGroups.Specs
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology (pointAction restriction)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalAffineBruhat (coefficientPoints FoldedApartment RamifiedReference
  ExceptionalNumbering)
open Specs.ExceptionalAffineBuilding (AdjointAction AdjointCoefficientActions
  cotype IsBarycenter rationalPoint simplexPoint)
open Specs.ExceptionalAffineRootSystems (e6Partner exceptionalCartan)
open Specs.ExceptionalFormsOverUnramifiedFields (HasTypeE)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation ramificationIndex)
open Specs.IntegralSemisimpleModel (Model)
open Specs.Pinning (AttachedDatum BasedRootDatum PinnedGroup SimpleRoot)
open Specs.RamifiedExceptionalAuxiliaryTower (UnramifiedLevel)
open Specs.RamifiedExceptionalFaceReduction (faceInclusion)
open Specs.RamifiedExceptionalLocalFaceCoordinates (MarkedLevel)
open Specs.RamifiedExceptionalMarkedAdjoint (HasE6Diagram NaturalPointComparison)
open Specs.RamifiedExceptionalParahoricResidueDescent (faceCoefficient restrictCoefficient)

open private faceAction faceAction_extend restrict_commutes from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalParahoricResidueDescent

open scoped WithZero

universe u

noncomputable section

private theorem hasE6Diagram_of_hasTypeE {F : Type u} [Field F] {A : RootGroups.AdditiveLine F}
    {P : PinnedGroup A} {D : AttachedDatum P.pair} (h : HasTypeE D 6) :
    HasE6Diagram D.toBased := by
  obtain ⟨numbering, hnumbering⟩ := h
  let e : SimpleRoot P.pair ≃ D.toBased.base.support :=
    Equiv.subtypeEquivRight fun i => (D.simple_iff i).symm
  have hCartan : ∀ i j, CartanMatrix.E 6 i j = exceptionalCartan 6 i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  refine ⟨numbering.trans e, fun i j => ?_⟩
  let := D.comm
  change D.datum.rootDatum.pairing (numbering i).val (numbering j).val = exceptionalCartan 6 i j
  exact (hnumbering i j).trans (hCartan i j)

private def pointsIso {F K : Type u} [Field F] [Field K] [Algebra F K]
    {G H : GroupScheme F} (e : G ≅ H) :
    GroupPoints G (CommAlgCat.of F K) ≃* GroupPoints H (CommAlgCat.of F K) :=
  (((groupPointsFunctor F).mapIso e).app (CommAlgCat.of F K)).groupIsoToMulEquiv

private theorem pointsIso_coefficient {F K E : Type u} [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] {G H : GroupScheme F} (e : G ≅ H)
    (he : NaturalPointComparison e) (f : K →ₐ[F] E) (p : GroupPoints G (CommAlgCat.of F K)) :
    coefficientPoints H f (pointsIso e p) = pointsIso e (coefficientPoints G f p) :=
  he (CommAlgCat.ofHom f) p

private theorem coefficientPoints_comp {F K E T : Type u} [Field F] [Field K] [Field E]
    [Field T] [Algebra F K] [Algebra F E] [Algebra F T]
    (G : GroupScheme F) (f : K →ₐ[F] E) (g : E →ₐ[F] T) (p : GroupPoints G (CommAlgCat.of F K)) :
    coefficientPoints G g (coefficientPoints G f p) = coefficientPoints G (g.comp f) p :=
  (ConcreteCategory.congr_hom
    (((groupPointsFunctor F).obj G).map_comp (CommAlgCat.ofHom f) (CommAlgCat.ofHom g)) p).symm

private theorem coboundary_of_change {M : Type u} [Group M] (ρ : MulAut M) (a b c : M)
    (h : b⁻¹ * a * ρ b = c * (ρ c)⁻¹) : a = (b * c) * (ρ (b * c))⁻¹ := by
  calc
    a = b * (b⁻¹ * a * ρ b) * (ρ b)⁻¹ := by group
    _ = (b * c) * (ρ (b * c))⁻¹ := by rw [h, map_mul]; group

variable {F S : Type u} [Field F] [Field S] [Algebra F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private abbrev levelPointMap (G : GroupScheme F) (k : UnramifiedLevel F S) :=
  coefficientPoints G k.field.val

private theorem levelPointMap_inclusion (G : GroupScheme F) {k k' : UnramifiedLevel F S}
    (h : k ≤ k') (p : GroupPoints G (CommAlgCat.of F k.field)) :
    levelPointMap G k' (coefficientPoints G (UnramifiedLevel.inclusion h) p) =
      levelPointMap G k p := by
  change coefficientPoints G k'.field.val (coefficientPoints G (UnramifiedLevel.inclusion h) p) = _
  rw [coefficientPoints_comp]
  rfl

private theorem levelPointMap_equivariant (G : GroupScheme F) (k : UnramifiedLevel F S)
    (s : Gal(S/F)) (p : GroupPoints G (CommAlgCat.of F k.field)) :
    levelPointMap G k (coefficientPoints G (AlgEquiv.restrictNormalHom k.field s).toAlgHom p) =
      coefficientPoints G s.toAlgHom (levelPointMap G k p) := by
  change coefficientPoints G k.field.val
    (coefficientPoints G (AlgEquiv.restrictNormalHom k.field s).toAlgHom p) =
    coefficientPoints G s.toAlgHom (coefficientPoints G k.field.val p)
  have he : k.field.val.comp (AlgEquiv.restrictNormalHom k.field s).toAlgHom =
      s.toAlgHom.comp k.field.val :=
    AlgHom.ext (AlgEquiv.restrictNormalHom_apply k.field s)
  rw [coefficientPoints_comp, coefficientPoints_comp, he]

private theorem restrictCoefficient_fromClosure {k k' : UnramifiedLevel F S} (h : k ≤ k')
    (s : Gal(S/F)) :
    restrictCoefficient h (AlgEquiv.restrictNormalHom k'.field s) =
      AlgEquiv.restrictNormalHom k.field s := by
  apply AlgEquiv.ext
  intro z
  apply k.field.val.injective
  have he := congrArg k'.field.val
    ((restrict_commutes h (AlgEquiv.restrictNormalHom k'.field s) z).symm)
  exact he.trans ((AlgEquiv.restrictNormalHom_apply k'.field s
    (UnramifiedLevel.inclusion h z)).trans (AlgEquiv.restrictNormalHom_apply k.field s z).symm)

set_option maxHeartbeats 1800000 in
/-- A cocycle over a finite unramified coefficient stage is neutral after the
marked face reduction and the higher congruence corrections. -/
private theorem markedCocycle_neutral
    [IsSepClosed S] [Algebra.IsSeparable F S]
    {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension F L]
    (σ : Gal(L/F)) (hdegree : Module.finrank F L = 2) (hσ : σ ≠ 1)
    (hram : 1 < ramificationIndex F L)
    {D : BasedRootDatum.{u}} {M : Model D} (R : RamifiedReference F L M)
    (numbering : Fin 6 ≃ D.base.support) (hnumbering : ExceptionalNumbering D 6 numbering)
    (hspan : D.datum.rootSpan ℤ = ⊤)
    (hdiagram : ∀ i, (R.diagram σ).val.indexEquiv (numbering i) = numbering (e6Partner i))
    (A : FoldedApartment (R.diagram σ))
    (X : ∀ k : UnramifiedLevel F S, MarkedLevel R σ A k.field)
    (k : UnramifiedLevel F S)
    (ad : AdjointAction (X k).building (X k).folded.typeQuotient)
    (hcoef : AdjointCoefficientActions ad)
    (a : Gal(k.field/F) → GroupPoints R.descent.group.val (CommAlgCat.of F k.field))
    (ha : ∀ s t, a (s * t) = a s * coefficientPoints R.descent.group.val s.toAlgHom (a t)) :
    ∃ b : GroupPoints R.descent.group.val (CommAlgCat.of F S), ∀ s : Gal(S/F),
      levelPointMap R.descent.group.val k (a (AlgEquiv.restrictNormalHom k.field s)) =
        b * (coefficientPoints R.descent.group.val s.toAlgHom b)⁻¹ := by
  classical
  obtain ⟨g, J, t, x, hJ, hproper, ht, hx, hg⟩ :=
    foldedCocycleIntoParahoric (X k).compositum (X k).folded ad hcoef (X k).coefficients a ha
  subst J
  obtain ⟨π₀, hπ₀⟩ := RamifiedExceptionalAuxiliaryTower.normalizedValuation_surjective L (WithZero.exp (-1))
  have hπne : π₀ ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hπ₀
    exact WithZero.exp_ne_zero hπ₀.symm
  let π := Units.mk0 π₀ hπne
  have hπ : normalizedValuation L (π : L) = WithZero.exp (-1) := hπ₀
  obtain ⟨_, _, ϖ, d, y, _, hd, hy, P, ⟨hgeometry⟩⟩ :=
    RamifiedExceptionalFaceReduction.ramifiedParahoricScaling σ hdegree hσ hram
      R numbering hnumbering hspan hdiagram A X k t x ht hx π hπ
  let aChanged (s : Gal(k.field/F)) :=
    g⁻¹ * a s * coefficientPoints R.descent.group.val s.toAlgHom g
  let aFace (s : Gal(k.field/F)) : (X k).parahoric (cotype t) :=
    ⟨aChanged s, hg s⟩
  obtain ⟨ρ, hρ, _, _⟩ := (X k).coefficients
  have haFace (s t' : Gal(k.field/F)) :
      aFace (s * t') = aFace s * faceCoefficient P k s (aFace t') := by
    apply Subtype.ext
    change aChanged (s * t') =
      aChanged s * coefficientPoints R.descent.group.val s.toAlgHom (aChanged t')
    simpa only [hρ, aChanged] using
      changedCocycleLaw ρ a (fun s t => (ha s t).trans (by rw [hρ])) g s t'
  obtain ⟨k', h, b, hb⟩ :=
    RamifiedExceptionalParahoricResidueDescent.parahoricResidueDescent P hgeometry k aFace haFace
  let extend := faceInclusion X h (cotype t) (P.face_comap h)
  let restrict := restrictCoefficient h
  let action := faceAction P k'
  let aExtended (s : Gal(k'.field/F)) := extend (aFace (restrict s))
  have haExtended (s t' : Gal(k'.field/F)) :
      aExtended (s * t') = aExtended s * action s (aExtended t') := by
    change extend (aFace (restrict (s * t'))) = _
    rw [map_mul restrict, haFace, map_mul extend]
    exact congrArg (aExtended s * ·) (faceAction_extend P h s (aFace (restrict t')))
  let aCorrected (s : Gal(k'.field/F)) := b⁻¹ * aExtended s * action s b
  obtain ⟨z, hz⟩ := RamifiedExceptionalParahoricCongruenceDescent.parahoricCongruenceDescent
    σ hdegree hσ hram R numbering hnumbering hspan hdiagram A X (cotype t) hproper
    k t x ht rfl hx π hπ d hd y hy.symm P k' aCorrected
    (changedCocycleLaw action aExtended haExtended b) hb
  have haNeutral (s : Gal(k'.field/F)) :
      aExtended s = (b * z.val) * (action s (b * z.val))⁻¹ :=
    coboundary_of_change (action s) (aExtended s) b z.val (hz s)
  let correction := levelPointMap R.descent.group.val k' (b * z.val).val
  have hFaceNeutral (s : Gal(S/F)) :
      levelPointMap R.descent.group.val k (aFace (AlgEquiv.restrictNormalHom k.field s)).val =
        correction * (coefficientPoints R.descent.group.val s.toAlgHom correction)⁻¹ := by
    let s' := AlgEquiv.restrictNormalHom k'.field s
    have hpoint := congrArg (fun p : (X k').parahoric (cotype t) =>
        levelPointMap R.descent.group.val k' p.val) (haNeutral s')
    change levelPointMap R.descent.group.val k'
        (coefficientPoints R.descent.group.val (UnramifiedLevel.inclusion h)
          (aFace (restrict s')).val) =
      levelPointMap R.descent.group.val k'
        ((b * z.val).val *
          (coefficientPoints R.descent.group.val s'.toAlgHom (b * z.val).val)⁻¹) at hpoint
    rw [levelPointMap_inclusion _ h, restrictCoefficient_fromClosure h s,
      map_mul (levelPointMap R.descent.group.val k'),
      map_inv (levelPointMap R.descent.group.val k'), levelPointMap_equivariant] at hpoint
    exact hpoint
  let gS := levelPointMap R.descent.group.val k g
  refine ⟨gS * correction, fun s => coboundary_of_change
    (pointAction F S R.descent.group.val.X s) _ gS correction ?_⟩
  have hpoint := hFaceNeutral s
  change levelPointMap R.descent.group.val k
    (g⁻¹ * a (AlgEquiv.restrictNormalHom k.field s) *
      coefficientPoints R.descent.group.val (AlgEquiv.restrictNormalHom k.field s).toAlgHom g) =
        _ at hpoint
  rw [map_mul, map_mul, map_inv, levelPointMap_equivariant] at hpoint
  exact hpoint

set_option maxHeartbeats 1800000 in
/-- Every simply connected outer form of type E₆ with a ramified quadratic
diagram field over a nonarchimedean local field is quasi-split. -/
theorem ramifiedOuterQuasiSplit : Specs.RamifiedOuterExceptionalForms.RamifiedOuterQuasiSplit.{u} := by
  classical
  intro F S _ _ _ _ _ _ _ Add P D l Q E hss hsc htype L _ _ _ _ hdegree hram ω hω H i hi
  let : IsSepClosed S := IsSepClosure.sep_closed F
  obtain ⟨outer, V, houter, hinner⟩ := existsPinnedInnerReference E L ω H i hi
  obtain ⟨Q₀, a, hdescend⟩ := existsInnerFormCocycle V.model.val H.val hinner
  obtain ⟨Dsc, Dad, M, M', cover, numbering, numbering', R, R', j, hnumbering, hnumbering',
    hsc', had, hdiagrams, _, hadjoint⟩ :=
    RamifiedExceptionalMarkedAdjoint.markedReference F S E hss hsc
      (hasE6Diagram_of_hasTypeE htype) L hdegree hram ω hω outer houter V
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(L/F), σ ≠ 1 := by
    by_contra! hall
    apply hω
    apply MonoidHom.ext
    intro s
    rw [hall s]
    exact map_one ω
  obtain ⟨hdiagram, hdiagram', hcompat⟩ := hdiagrams σ hσ
  obtain ⟨A, A', e, φ, B, B', BX, _, _, hφ, _, hlevels⟩ :=
    ExceptionalAffineBuilding.ramifiedAffineBuildings F L σ hdegree hσ hram cover
      numbering numbering' hnumbering hnumbering' hsc' had R R' hdiagram hdiagram' hcompat
  obtain ⟨jAdjoint, _, hjAdjoint⟩ := hadjoint φ hφ Q₀
  have hMarked : ∀ k : UnramifiedLevel F S,
      ∃ (X : MarkedLevel R' σ A' k.field)
        (ad : AdjointAction X.building X.folded.typeQuotient), AdjointCoefficientActions ad := by
    intro k
    obtain ⟨T, Y, Y', BY, _, _, _, _, _, _, hcf⟩ := hlevels k.field k.unramified
    exact ⟨⟨T, Y', BY.ad, hcf⟩, BY.adjoint, BY.coefficients⟩
  choose X adjoint hcoefficients using hMarked
  obtain ⟨K, valK, topK, localK, extK, hK, p, c, hc, hinfl⟩ :=
    RamifiedExceptionalUnramifiedCocycle.finiteUnramifiedInflation F S V hss hsc htype Q₀ a
  let k : UnramifiedLevel F S :=
    { field := K.toIntermediateField
      finite := K.finiteDimensional
      galois := K.isGalois
      valuative := valK
      topology := topK
      localField := localK
      extendsBase := extK
      unramified := hK }
  let pointsK := pointsIso (K := k.field) jAdjoint
  let aMarked (s : Gal(k.field/F)) := pointsK.symm (c s)
  have hMarkedPoint (s : Gal(k.field/F)) : pointsK (aMarked s) = c s :=
    pointsK.apply_symm_apply (c s)
  have haMarked (s t : Gal(k.field/F)) :
      aMarked (s * t) = aMarked s * coefficientPoints R'.descent.group.val s.toAlgHom (aMarked t) := by
    apply pointsK.injective
    have he := pointsIso_coefficient jAdjoint hjAdjoint s.toAlgHom (aMarked t)
    change coefficientPoints Q₀.quotient.val s.toAlgHom (pointsK (aMarked t)) =
      pointsK (coefficientPoints R'.descent.group.val s.toAlgHom (aMarked t)) at he
    rw [map_mul, ← he, hMarkedPoint, hMarkedPoint, hMarkedPoint]
    exact hc s t
  obtain ⟨b, hb⟩ := markedCocycle_neutral σ hdegree hσ hram R' numbering' hnumbering' had
    hdiagram' A' X k (adjoint k) (hcoefficients k) aMarked haMarked
  let bAdjoint : Descent.NonabelianCohomology.Points F S Q₀.quotient.val.X :=
    pointsIso (K := S) jAdjoint b
  have hcNeutral (s : Gal(S/F)) :
      coefficientPoints Q₀.quotient.val K.toIntermediateField.val (c (restriction K s)) =
        bAdjoint * (pointAction F S Q₀.quotient.val.X s bAdjoint)⁻¹ := by
    have hpoint := congrArg (pointsIso (K := S) jAdjoint) (hb s)
    change pointsIso jAdjoint
        (coefficientPoints R'.descent.group.val k.field.val (aMarked (restriction K s))) =
      pointsIso jAdjoint (b * (coefficientPoints R'.descent.group.val s.toAlgHom b)⁻¹) at hpoint
    rw [← pointsIso_coefficient jAdjoint hjAdjoint, map_mul, map_inv,
      ← pointsIso_coefficient jAdjoint hjAdjoint] at hpoint
    change coefficientPoints Q₀.quotient.val K.toIntermediateField.val
      (pointsK (aMarked (restriction K s))) = _ at hpoint
    rw [hMarkedPoint] at hpoint
    exact hpoint
  have haNeutral (s : Gal(S/F)) :
      a.val s = (p * bAdjoint) * (pointAction F S Q₀.quotient.val.X s (p * bAdjoint))⁻¹ :=
    coboundary_of_change (pointAction F S Q₀.quotient.val.X s) (a.val s) p bAdjoint
      ((hinfl s).symm.trans (hcNeutral s))
  obtain ⟨iso⟩ := hdescend ⟨p * bAdjoint, haNeutral⟩
  exact isQuasiSplitOfIso iso ⟨V.reductive, V.B, V.borel⟩

end

end Descent

end LinearAlgebraicGroups.Arithmetic.RamifiedOuterExceptionalForms
