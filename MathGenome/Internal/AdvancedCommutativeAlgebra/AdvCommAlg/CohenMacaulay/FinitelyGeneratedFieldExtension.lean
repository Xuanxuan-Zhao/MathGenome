import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.PolynomialExtension
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.QuotientsAndScalars
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.FinitelyGeneratedFieldExtension
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

universe u
open scoped TensorProduct IntermediateField
noncomputable section
set_option linter.style.haveILetI false
namespace AdvCommAlg.CohenMacaulay

theorem finitelyGeneratedFieldExtension_noetherian :
    Specs.finitelyGeneratedFieldExtension_noetherianType.{u} := by
  intro k R K _ _ _ _ _ _ _
  exact Specs.fieldTensorNoetherian k R K

namespace FinitelyGeneratedFieldExtension

/-- The localization of the ring as a module is its usual localization. -/
def localizedSelfEquiv (R : Type u) [CommRing R] (T : Submonoid R) :
    LocalizedModule T R ≃ₗ[Localization T] Localization T :=
  LocalizedModule.equivTensorProduct T R ≪≫ₗ
    TensorProduct.AlgebraTensorModule.rid R (Localization T) (Localization T)

/-- The ring and module versions of global Cohen–Macaulayness agree. -/
lemma cohenMacaulayRing_iff_self (R : Type u) [CommRing R] [IsNoetherianRing R] :
    CohenMacaulayRing R ↔ IsCohenMacaulay R R := by
  rw [isCohenMacaulay_iff_all_primes]
  exact forall_congr' fun p =>
    (localCohenMacaulay_iff_of_linearEquiv
      (localizedSelfEquiv R p.asIdeal.primeCompl)).symm

/-- Faithfully flat descent uses a prime over each base prime and CM-10. -/
lemma cohenMacaulayRing_of_faithfullyFlat (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.FaithfullyFlat R S]
    (hS : CohenMacaulayRing S) : CohenMacaulayRing R := by
  intro p
  obtain ⟨q, hq⟩ := (PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := R) (B := S)) p
  let A := Localization.AtPrime p.asIdeal
  let B := Localization.AtPrime q.asIdeal
  letI : q.asIdeal.LiesOver p.asIdeal := ⟨(congrArg PrimeSpectrum.asIdeal hq).symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  letI : IsLocalHom (algebraMap A B) := stalk_algebraMap_isLocalHom R S _ _
  letI : Module.Flat A B := stalk_flat R S p.asIdeal q.asIdeal
  exact ((flatLocal_ring_cohenMacaulay A B).mp (hS q)).1

/-- This direction holds for every field extension whenever the tensor ring
is Noetherian. It has no finite-generation or separability requirement. -/
lemma fieldExtension_cohenMacaulay_descent (k R K : Type u)
    [Field k] [CommRing R] [Field K] [Algebra k R] [Algebra k K]
    [IsNoetherianRing R] [IsNoetherianRing (R ⊗[k] K)]
    (h : CohenMacaulayRing (R ⊗[k] K)) : CohenMacaulayRing R := by
  exact cohenMacaulayRing_of_faithfullyFlat R (R ⊗[k] K) h

/-- Ring CM transports along a ring isomorphism. -/
lemma cohenMacaulayRing_iff_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] (e : R ≃+* S) :
    CohenMacaulayRing R ↔ CohenMacaulayRing S := by
  rw [cohenMacaulayRing_iff_self, cohenMacaulayRing_iff_self]
  exact isCohenMacaulay_iff_of_semilinearEquiv e e.toSemilinearEquiv

/-- Ring CM survives arbitrary multiplicative-set localization. -/
lemma cohenMacaulayRing_localization (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [IsNoetherianRing R] [IsNoetherianRing A]
    (T : Submonoid R) [IsLocalization T A] (h : CohenMacaulayRing R) :
    CohenMacaulayRing A := by
  have h' := isCohenMacaulay_localizedModule R
    ((cohenMacaulayRing_iff_self R).mp h) T
  have h'' : CohenMacaulayRing (Localization T) := by
    apply (cohenMacaulayRing_iff_self _).mpr
    exact (isCohenMacaulay_iff_of_linearEquiv (localizedSelfEquiv R T)).mp h'
  exact (cohenMacaulayRing_iff_of_ringEquiv
    (IsLocalization.algEquiv T (Localization T) A).toRingEquiv).mp h''

/-- The polynomial module theorem specializes to the usual polynomial ring. -/
lemma cohenMacaulayRing_polynomial (R : Type u) [CommRing R] [IsNoetherianRing R]
    (h : CohenMacaulayRing R) : CohenMacaulayRing (Polynomial R) := by
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := Polynomial R) R (Polynomial R)
  letI := Specs.rightTensorFinite R (Polynomial R) R (Polynomial R)
  have h' := (polynomial_cohenMacaulay_iff R R).mpr ((cohenMacaulayRing_iff_self R).mp h)
  let e := RegularSequence.rightTensorComm (S := Polynomial R) R (Polynomial R) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.rid R (Polynomial R) (Polynomial R)
  exact (cohenMacaulayRing_iff_self _).mpr
    ((isCohenMacaulay_iff_of_linearEquiv e).mp h')

/-- The depth bound proves that every Artinian local ring is CM. -/
lemma localCohenMacaulay_of_artinian (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsArtinianRing A] :
    LocalCohenMacaulay A A := by
  rw [localCohenMacaulay_self_iff,
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mp (inferInstance : Ring.KrullDimLE 0 A)]
  have h := Depth.depth_le_supportDim (R := A) A
  rw [Module.supportDim_self_eq_ringKrullDim,
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mp (inferInstance : Ring.KrullDimLE 0 A)] at h
  rw [Depth.depth_eq_libraryDepth (ModuleCat.of A A)] at h
  exact le_antisymm h (WithBot.coe_le_coe.mpr zero_le)

set_option backward.isDefEq.respectTransparency false in
/-- The localized closed fiber is a localization of the residue-field fiber. -/
lemma localFiber_artinian (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (h : PrimeSpectrum.comap (algebraMap R S) q = p)
    [IsArtinianRing (p.asIdeal.Fiber S)] :
    IsArtinianRing (Localization.AtPrime q.asIdeal ⧸
      p.asIdeal.map (algebraMap R (Localization.AtPrime q.asIdeal))) := by
  let E := PrimeSpectrum.preimageEquivFiber R S p
  let q' := E ⟨q, h⟩
  let F := p.asIdeal.Fiber S
  let L := Localization.AtPrime q'.asIdeal
  letI : IsArtinianRing L := IsArtinianRing.localization_artinian q'.asIdeal.primeCompl L
  let P : PrimeSpectrum S → Prop := fun r =>
    IsArtinianRing (Localization.AtPrime r.asIdeal ⧸
      p.asIdeal.map (algebraMap R (Localization.AtPrime r.asIdeal)))
  have hr : PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom q' = q :=
    congrArg Subtype.val (E.symm_apply_apply ⟨q, h⟩)
  have hh : P (PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom q') := by
    let e' := (Ideal.Fiber.algEquivAux₂ p.asIdeal q'.asIdeal).toRingEquiv
    let r := PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom q'
    have hJ : (p.asIdeal.map (algebraMap R S)).map
        (algebraMap S (Localization.AtPrime r.asIdeal)) =
        p.asIdeal.map (algebraMap R (Localization.AtPrime r.asIdeal)) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact (e'.trans (Ideal.quotEquivOfEq hJ)).isArtinianRing
  exact Eq.mp (congrArg P hr) hh

/-- Flat ascent when the actual residue-field fibers are Artinian. -/
lemma cohenMacaulayRing_of_flat_artinianFibers (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (hf : ∀ p : PrimeSpectrum R, IsArtinianRing (p.asIdeal.Fiber S))
    (hR : CohenMacaulayRing R) : CohenMacaulayRing S := by
  intro q
  let p := PrimeSpectrum.comap (algebraMap R S) q
  let A := Localization.AtPrime p.asIdeal
  let B := Localization.AtPrime q.asIdeal
  letI : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  letI : IsLocalHom (algebraMap A B) := stalk_algebraMap_isLocalHom R S _ _
  letI : Module.Flat A B := stalk_flat R S p.asIdeal q.asIdeal
  let J := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
  letI := Specs.closedFiberLocalRing A B
  letI := hf p
  letI := localFiber_artinian R S p q rfl
  have hJ : p.asIdeal.map (algebraMap R B) = J := by
    dsimp only [J]
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  letI : IsArtinianRing (B ⧸ J) := (Ideal.quotEquivOfEq hJ).isArtinianRing
  exact (flatLocal_ring_cohenMacaulay A B).mpr
    ⟨hR p, localCohenMacaulay_of_artinian (B ⧸ J)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Finite field extensions have finite-dimensional, hence Artinian, fibers
for every coefficient algebra, including inseparable extensions. -/
lemma finiteFieldExtension_fiber_artinian (k R K : Type u)
    [Field k] [CommRing R] [Field K] [Algebra k R] [Algebra k K]
    [Module.Finite k K] (p : PrimeSpectrum R) :
    IsArtinianRing (p.asIdeal.Fiber (R ⊗[k] K)) := by
  let F := p.asIdeal.ResidueField
  let e := Algebra.TensorProduct.cancelBaseChange k R F F K
  letI : IsArtinianRing (F ⊗[k] K) := IsArtinianRing.of_finite F (F ⊗[k] K)
  exact e.symm.toRingEquiv.isArtinianRing

/-- Algebraic ascent for a finite field extension, with no separability
hypothesis. -/
lemma finiteFieldExtension_cohenMacaulay_ascent (k R K : Type u)
    [Field k] [CommRing R] [Field K] [Algebra k R] [Algebra k K]
    [IsNoetherianRing R] [Module.Finite k K]
    (h : CohenMacaulayRing R) :
    letI := Specs.fieldTensorNoetherian k R K
    CohenMacaulayRing (R ⊗[k] K) := by
  letI := Specs.fieldTensorNoetherian k R K
  exact cohenMacaulayRing_of_flat_artinianFibers R (R ⊗[k] K)
    (finiteFieldExtension_fiber_artinian k R K) h

set_option backward.isDefEq.respectTransparency false in
/-- Rational-function scalar extension is a localization of a polynomial
extension of the coefficient ring. -/
lemma rationalFunction_cohenMacaulay_ascent (k R : Type u)
    [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R]
    [IsNoetherianRing (R ⊗[k] RatFunc k)]
    (h : CohenMacaulayRing R) : CohenMacaulayRing (R ⊗[k] RatFunc k) := by
  let P := R ⊗[k] Polynomial k
  letI : IsNoetherianRing P := Algebra.EssFiniteType.isNoetherianRing R P
  have hP : CohenMacaulayRing P :=
    (cohenMacaulayRing_iff_of_ringEquiv (polyEquivTensor k R).toRingEquiv).mp
      (cohenMacaulayRing_polynomial R h)
  let T := (nonZeroDivisors (Polynomial k)).map
    (Algebra.TensorProduct.includeRight (R := k) (A := R)).toMonoidHom
  let C := Localization T
  have hC : CohenMacaulayRing C := cohenMacaulayRing_localization P C T hP
  letI : IsLocalization T C := inferInstance
  letI : IsLocalization ((nonZeroDivisors (Polynomial k)).map
      (Algebra.TensorProduct.includeRight (R := k) (A := R))) C := by
    change IsLocalization T C
    infer_instance
  let e := IsLocalization.tensorProductEquivOfMapIncludeRight k R
    (nonZeroDivisors (Polynomial k)) (RatFunc k) C
  exact (cohenMacaulayRing_iff_of_ringEquiv e.toRingEquiv).mpr hC

/-- A single field generator is either finite algebraic or rational. -/
lemma simpleFieldExtension_cohenMacaulay_ascent (k R K : Type u)
    [Field k] [CommRing R] [Field K] [Algebra k R] [Algebra k K]
    [IsNoetherianRing R] (x : K) [IsNoetherianRing (R ⊗[k] k⟮x⟯)]
    (h : CohenMacaulayRing R) : CohenMacaulayRing (R ⊗[k] k⟮x⟯) := by
  by_cases hx : IsAlgebraic k x
  · letI := IntermediateField.adjoin.finiteDimensional hx.isIntegral
    exact finiteFieldExtension_cohenMacaulay_ascent k R k⟮x⟯ h
  · let e := Algebra.TensorProduct.congr ((AlgEquiv.refl : R ≃ₐ[k] R))
      (RatFunc.algEquivOfTranscendental x hx)
    letI : IsNoetherianRing (R ⊗[k] RatFunc k) :=
      isNoetherianRing_of_surjective _ _ e.symm.toRingHom e.symm.surjective
    exact (cohenMacaulayRing_iff_of_ringEquiv e.toRingEquiv).mp
      (rationalFunction_cohenMacaulay_ascent k R h)

set_option backward.isDefEq.respectTransparency false in
/-- Associativity of field scalar extension, with the right factor action
on the intermediate tensor ring. -/
def fieldTensorTowerEquiv (k R A B : Type u)
    [CommRing k] [CommRing R] [CommRing A] [CommRing B]
    [Algebra k R] [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B] :
    letI := Algebra.TensorProduct.rightAlgebra (R := k) (A := R) (B := A)
    ((R ⊗[k] A) ⊗[A] B) ≃+* (R ⊗[k] B) := by
  letI := Algebra.TensorProduct.rightAlgebra (R := k) (A := R) (B := A)
  exact (Algebra.TensorProduct.comm A (R ⊗[k] A) B).toRingEquiv.trans
    ((Algebra.TensorProduct.congr ((AlgEquiv.refl : B ≃ₐ[A] B))
      (Algebra.TensorProduct.commRight k A R).symm).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange k A A B R).toRingEquiv.trans
        (Algebra.TensorProduct.comm k B R).toRingEquiv))

set_option backward.isDefEq.respectTransparency false in
/-- One generator may be adjoined after an already constructed field
extension of the original base. -/
lemma simpleFieldExtension_ascent_tower (k R A K : Type u)
    [Field k] [CommRing R] [Field A] [Field K]
    [Algebra k R] [Algebra k A] [Algebra k K] [Algebra A K]
    [IsScalarTower k A K] [IsNoetherianRing R] [Algebra.EssFiniteType k A]
    (x : K) [IsNoetherianRing (R ⊗[k] A⟮x⟯)]
    (hA : letI := Specs.fieldTensorNoetherian k R A; CohenMacaulayRing (R ⊗[k] A)) :
    CohenMacaulayRing (R ⊗[k] A⟮x⟯) := by
  let P := R ⊗[k] A
  letI : IsNoetherianRing P := Specs.fieldTensorNoetherian k R A
  letI := Algebra.TensorProduct.rightAlgebra (R := k) (A := R) (B := A)
  letI : Algebra.EssFiniteType A A⟮x⟯ :=
    IntermediateField.essFiniteType_iff.mpr
      (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x))
  letI : IsNoetherianRing (P ⊗[A] A⟮x⟯) := Specs.fieldTensorNoetherian A P A⟮x⟯
  have hB := simpleFieldExtension_cohenMacaulay_ascent A P K x hA
  exact (cohenMacaulayRing_iff_of_ringEquiv (fieldTensorTowerEquiv k R A A⟮x⟯)).mp hB

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Induct over a finite set of field generators, allowing an arbitrary
mix of algebraic and transcendental steps. -/
lemma finitelyGeneratedFieldExtension_cohenMacaulay_ascent (k R K : Type u)
    [Field k] [CommRing R] [Field K] [Algebra k R] [Algebra k K]
    [IsNoetherianRing R] [Algebra.EssFiniteType k K]
    (h : CohenMacaulayRing R) :
    letI := Specs.fieldTensorNoetherian k R K
    CohenMacaulayRing (R ⊗[k] K) := by
  letI := Specs.fieldTensorNoetherian k R K
  let motive : IntermediateField k K → Prop := fun L => L.FG ∧
    ∀ [IsNoetherianRing (R ⊗[k] L)],
      CohenMacaulayRing R → CohenMacaulayRing (R ⊗[k] L)
  have htop : motive ⊤ := by
    apply IntermediateField.induction_on_adjoin_fg
    · refine ⟨IntermediateField.fg_bot, ?_⟩
      intro _ hR
      let e := (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[k] R)
        (IntermediateField.botEquiv k K)).toRingEquiv.trans
        (Algebra.TensorProduct.rid k k R).toRingEquiv
      exact (cohenMacaulayRing_iff_of_ringEquiv e).mpr hR
    · intro L x ih
      refine ⟨?_, ?_⟩
      · rw [IntermediateField.restrictScalars_adjoin_eq_sup]
        exact IntermediateField.fg_sup ih.1
          (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x))
      · intro _ hR
        letI : Algebra.EssFiniteType k L := IntermediateField.essFiniteType_iff.mpr ih.1
        letI := Specs.fieldTensorNoetherian k R L
        letI : Algebra.EssFiniteType L L⟮x⟯ :=
          IntermediateField.essFiniteType_iff.mpr
            (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x))
        letI : Algebra.EssFiniteType k L⟮x⟯ := Algebra.EssFiniteType.comp k L L⟮x⟯
        letI := Specs.fieldTensorNoetherian k R L⟮x⟯
        exact simpleFieldExtension_ascent_tower k R L K x (ih.2 hR)
    · exact IntermediateField.fg_top k K
  letI : Algebra.EssFiniteType k (⊤ : IntermediateField k K) :=
    IntermediateField.essFiniteType_iff.mpr htop.1
  letI := Specs.fieldTensorNoetherian k R (⊤ : IntermediateField k K)
  let e := Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[k] R)
    (IntermediateField.topEquiv : (⊤ : IntermediateField k K) ≃ₐ[k] K)
  exact (cohenMacaulayRing_iff_of_ringEquiv e.toRingEquiv).mp (htop.2 h)

end FinitelyGeneratedFieldExtension

/-- The finitely-generated-field alternative of CM-15, with the canonical
tensor ring and with no separability assumption. -/
theorem finitelyGeneratedFieldExtension_cohenMacaulay_iff :
    Specs.finitelyGeneratedFieldExtension_cohenMacaulay_iffType.{u} := by
  intro k R K _ _ _ _ _ _ _
  letI := Specs.fieldTensorNoetherian k R K
  exact ⟨FinitelyGeneratedFieldExtension.fieldExtension_cohenMacaulay_descent k R K,
    FinitelyGeneratedFieldExtension.finitelyGeneratedFieldExtension_cohenMacaulay_ascent k R K⟩

end AdvCommAlg.CohenMacaulay
