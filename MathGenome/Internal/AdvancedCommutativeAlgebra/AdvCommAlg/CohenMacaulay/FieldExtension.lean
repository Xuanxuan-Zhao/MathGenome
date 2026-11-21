import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.PolynomialExtension
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.FieldExtension
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.FinitelyGeneratedFieldExtension
/-! CM-15, field extension. The two unproved finitely generated field
extension results enter only as explicit parameters of the conditional helpers.
No separability hypothesis is used. -/
universe u
open scoped TensorProduct Pointwise
noncomputable section
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
namespace AdvCommAlg.CohenMacaulay
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Local ring Cohen–Macaulayness is invariant under a ring isomorphism. -/
lemma localCohenMacaulay_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) : LocalCohenMacaulay A A ↔ LocalCohenMacaulay B B :=
  localCohenMacaulay_iff_of_semilinearEquiv A e e.toSemilinearEquiv

/-- Global ring Cohen–Macaulayness is invariant under a ring isomorphism. -/
lemma cohenMacaulayRing_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (e : A ≃+* B)
    (h : CohenMacaulayRing A) : CohenMacaulayRing B := by
  intro q
  let p := PrimeSpectrum.comap e.toRingHom q
  let e' := Localization.localRingEquiv p.asIdeal q.asIdeal e rfl
  exact (localCohenMacaulay_ringEquiv e').mp (h p)

/-- Fields are Cohen–Macaulay at every prime. -/
lemma cohenMacaulayRing_field (k : Type u) [Field k] : CohenMacaulayRing k := by
  intro p
  exact localCohenMacaulay_of_localPID (Localization.AtPrime p.asIdeal)

set_option backward.isDefEq.respectTransparency false in
/-- A CM fiber gives the CM closed fiber of the map on local rings. -/
lemma closedFiber_cohenMacaulay_of_fiber (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (h : PrimeSpectrum.comap (algebraMap R S) q = p)
    [IsNoetherianRing (p.asIdeal.Fiber S)]
    (hF : CohenMacaulayRing (p.asIdeal.Fiber S))
    [Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)]
    [IsScalarTower R (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)]
    [IsLocalHom (algebraMap (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal))] :
    let A := Localization.AtPrime p.asIdeal
    let B := Localization.AtPrime q.asIdeal
    let J := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
    letI := Specs.closedFiberLocalRing A B
    LocalCohenMacaulay (B ⧸ J) (B ⧸ J) := by
  let A := Localization.AtPrime p.asIdeal
  let B := Localization.AtPrime q.asIdeal
  let J := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
  letI := Specs.closedFiberLocalRing A B
  have hJ : p.asIdeal.map (algebraMap R B) = J := by
    dsimp only [J]
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  let E := PrimeSpectrum.preimageEquivFiber R S p
  let q' := E ⟨q, h⟩
  have hr : PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom q' = q :=
    congrArg Subtype.val (E.symm_apply_apply ⟨q, h⟩)
  let P : PrimeSpectrum S → Prop := fun r =>
    let Q := Localization.AtPrime r.asIdeal ⧸ p.asIdeal.map
      (algebraMap R (Localization.AtPrime r.asIdeal))
    ∃ hQ : IsLocalRing Q, letI := hQ; LocalCohenMacaulay Q Q
  have hh : P (PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom q') := by
    let e := (Ideal.Fiber.algEquivAux₂ p.asIdeal q'.asIdeal).toRingEquiv
    let r := PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom q'
    have he : (p.asIdeal.map (algebraMap R S)).map
        (algebraMap S (Localization.AtPrime r.asIdeal)) =
        p.asIdeal.map (algebraMap R (Localization.AtPrime r.asIdeal)) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    let e' := e.trans (Ideal.quotEquivOfEq he)
    letI := e'.toEquiv.nontrivial_congr.mp inferInstance
    letI := IsLocalRing.of_surjective' e'.toRingHom e'.surjective
    exact ⟨inferInstance, (localCohenMacaulay_ringEquiv e').mp (hF q')⟩
  obtain ⟨hQ, hCM⟩ := Eq.mp (congrArg P hr) hh
  letI := hQ
  exact (localCohenMacaulay_ringEquiv (Ideal.quotEquivOfEq hJ)).mp hCM

/-- The actual residue-field fiber of scalar extension, with the base change
cancelled and the factors commuted. -/
def fieldExtensionFiberEquiv (k R K : Type u) [Field k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] (p : PrimeSpectrum R) :
    p.asIdeal.Fiber (R ⊗[k] K) ≃+* K ⊗[k] p.asIdeal.ResidueField :=
  (Algebra.TensorProduct.cancelBaseChange k R R p.asIdeal.ResidueField K).toRingEquiv.trans
    (Algebra.TensorProduct.comm k p.asIdeal.ResidueField K).toRingEquiv

/-- For finite-type R, its residue fields supply the finite generation needed
by the conditional theorem, even when K/k is arbitrary. -/
lemma fieldExtension_fiber_cohenMacaulay
    (hCM : Specs.finitelyGeneratedFieldExtension_cohenMacaulay_iffType.{u})
    (hN : Specs.finitelyGeneratedFieldExtension_noetherianType.{u})
    (k R K : Type u) [Field k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] [IsNoetherianRing R] [Algebra.FiniteType k R]
    (p : PrimeSpectrum R) :
    ∃ hF : IsNoetherianRing (p.asIdeal.Fiber (R ⊗[k] K)),
      @CohenMacaulayRing _ _ hF := by
  let L := p.asIdeal.ResidueField
  letI : Algebra.EssFiniteType k L := Algebra.EssFiniteType.comp k R L
  letI : IsNoetherianRing (K ⊗[k] L) := hN k K L
  let e := fieldExtensionFiberEquiv k R K p
  letI : IsNoetherianRing (p.asIdeal.Fiber (R ⊗[k] K)) :=
    isNoetherianRing_of_ringEquiv _ e.symm
  refine ⟨inferInstance, ?_⟩
  apply cohenMacaulayRing_of_ringEquiv e.symm
  exact (hCM k K L).mpr (cohenMacaulayRing_field K)

/-- Flat descent on stalks; no hypothesis on the fibers is needed. -/
lemma cohenMacaulayAt_comap_of_flat (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (q : PrimeSpectrum S) (hq : CohenMacaulayAt S q) :
    CohenMacaulayAt R (PrimeSpectrum.comap (algebraMap R S) q) := by
  let p := PrimeSpectrum.comap (algebraMap R S) q
  let A := Localization.AtPrime p.asIdeal
  let B := Localization.AtPrime q.asIdeal
  letI : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  letI : IsLocalHom (algebraMap A B) := stalk_algebraMap_isLocalHom R S _ _
  letI : Module.Flat A B := stalk_flat R S p.asIdeal q.asIdeal
  exact ((flatLocal_ring_cohenMacaulay A B).mp hq).1

/-- Faithful flatness reaches every base prime, including for a zero base ring. -/
lemma cohenMacaulayRing_of_faithfullyFlat (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.FaithfullyFlat R S] (hS : CohenMacaulayRing S) : CohenMacaulayRing R := by
  intro p
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S) p
  have h := cohenMacaulayAt_comap_of_flat R S q (hS q)
  exact Eq.mp (congrArg (CohenMacaulayAt R) hq) h

/-- Ascent at a prime for a flat map with a Cohen–Macaulay fiber. -/
lemma cohenMacaulayAt_of_flat_of_fiber (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (q : PrimeSpectrum S)
    (hR : CohenMacaulayAt R (PrimeSpectrum.comap (algebraMap R S) q))
    [IsNoetherianRing ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.Fiber S)]
    (hF : CohenMacaulayRing ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.Fiber S)) :
    CohenMacaulayAt S q := by
  let p := PrimeSpectrum.comap (algebraMap R S) q
  let A := Localization.AtPrime p.asIdeal
  let B := Localization.AtPrime q.asIdeal
  letI : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  letI : IsLocalHom (algebraMap A B) := stalk_algebraMap_isLocalHom R S _ _
  letI : Module.Flat A B := stalk_flat R S p.asIdeal q.asIdeal
  exact (flatLocal_ring_cohenMacaulay A B).mpr
    ⟨hR, closedFiber_cohenMacaulay_of_fiber R S p q rfl hF⟩

/-- Conditional Noetherianness with the exact two ordered upstream premises. -/
theorem fieldExtension_noetherian_conditional
    (_hCM : Specs.finitelyGeneratedFieldExtension_cohenMacaulay_iffType.{u})
    (hN : Specs.finitelyGeneratedFieldExtension_noetherianType.{u}) :
    Specs.fieldExtension_noetherianType.{u} := by
  intro k R K _ _ _ _ _ _ h
  rcases h with h | h
  · exact Specs.fieldExtensionTensorNoetherian k R K (Or.inl h)
  · letI := h
    exact hN k R K

/-- The full field-extension theorem, conditional only on the finitely
 generated field-extension theorems, with no restriction on inseparability. -/
theorem fieldExtension_cohenMacaulay_iff_conditional
    (hCM : Specs.finitelyGeneratedFieldExtension_cohenMacaulay_iffType.{u})
    (hN : Specs.finitelyGeneratedFieldExtension_noetherianType.{u}) :
    Specs.fieldExtension_cohenMacaulay_iffType.{u} := by
  intro k R K _ _ _ _ _ _ h
  letI := Specs.fieldExtensionTensorNoetherian k R K h
  change CohenMacaulayRing (R ⊗[k] K) ↔ CohenMacaulayRing R
  rcases h with h | h
  · letI := h
    constructor
    · intro hS
      exact cohenMacaulayRing_of_faithfullyFlat R (R ⊗[k] K) hS
    · intro hR q
      let p := PrimeSpectrum.comap (algebraMap R (R ⊗[k] K)) q
      obtain ⟨hF, hFCM⟩ := fieldExtension_fiber_cohenMacaulay hCM hN k R K p
      letI := hF
      exact cohenMacaulayAt_of_flat_of_fiber R (R ⊗[k] K) q (hR p) hFCM
  · letI := h
    exact hCM k R K

end AdvCommAlg.CohenMacaulay

universe v8_closure_4581ff9c2ed21c9f_u0
theorem _root_.«AdvCommAlg».«CohenMacaulay».«fieldExtension_cohenMacaulay_iff» : _root_.«AdvCommAlg».«CohenMacaulay».«Specs».«fieldExtension_cohenMacaulay_iffType».{v8_closure_4581ff9c2ed21c9f_u0} :=
  @_root_.«AdvCommAlg».«CohenMacaulay».«fieldExtension_cohenMacaulay_iff_conditional».{v8_closure_4581ff9c2ed21c9f_u0} (@_root_.«AdvCommAlg».«CohenMacaulay».«finitelyGeneratedFieldExtension_cohenMacaulay_iff».{v8_closure_4581ff9c2ed21c9f_u0}) (@_root_.«AdvCommAlg».«CohenMacaulay».«finitelyGeneratedFieldExtension_noetherian».{v8_closure_4581ff9c2ed21c9f_u0})
theorem _root_.«AdvCommAlg».«CohenMacaulay».«fieldExtension_noetherian» : _root_.«AdvCommAlg».«CohenMacaulay».«Specs».«fieldExtension_noetherianType».{v8_closure_4581ff9c2ed21c9f_u0} :=
  @_root_.«AdvCommAlg».«CohenMacaulay».«fieldExtension_noetherian_conditional».{v8_closure_4581ff9c2ed21c9f_u0} (@_root_.«AdvCommAlg».«CohenMacaulay».«finitelyGeneratedFieldExtension_cohenMacaulay_iff».{v8_closure_4581ff9c2ed21c9f_u0}) (@_root_.«AdvCommAlg».«CohenMacaulay».«finitelyGeneratedFieldExtension_noetherian».{v8_closure_4581ff9c2ed21c9f_u0})
