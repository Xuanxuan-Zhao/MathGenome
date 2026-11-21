import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.OpenLocus
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.LocalResidueFields
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.FieldAlgebraClassification
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.Flatness
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.PointwiseFlatSeparableCriterion
import Mathlib.RingTheory.Smooth.Fiber

namespace AdvCommAlg.Etale

universe u v
noncomputable section
open scoped TensorProduct
open Specs.AdvCommAlg.Etale.PointwiseFlatSeparableCriterion

/-- Flatness on the principal neighborhood passes to the stalk. -/
lemma flat_stalk_of_neighborhood (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (q : PrimeSpectrum B)
    (h : IsEtaleAt A B q) : Module.Flat A (Localization.AtPrime q.asIdeal) := by
  obtain ⟨b, hb, he⟩ := h
  let : Algebra.Etale A (Localization.Away b) := he
  have hle : Submonoid.powers b ≤ q.asIdeal.primeCompl := by
    simpa [Submonoid.powers_le, Ideal.primeCompl] using hb
  letI : Algebra (Localization.Away b) (Localization.AtPrime q.asIdeal) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ hle
  have : IsScalarTower B (Localization.Away b) (Localization.AtPrime q.asIdeal) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  have : IsScalarTower A (Localization.Away b) (Localization.AtPrime q.asIdeal) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply A B (Localization.Away b),
        ← IsScalarTower.algebraMap_apply B (Localization.Away b),
        ← IsScalarTower.algebraMap_apply A B]
  have : IsLocalization (q.asIdeal.primeCompl.map (algebraMap B (Localization.Away b)))
      (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ _ _ hle
  have : Module.Flat (Localization.Away b) (Localization.AtPrime q.asIdeal) :=
    IsLocalization.flat _ (q.asIdeal.primeCompl.map (algebraMap B (Localization.Away b)))
  exact Module.Flat.trans A (Localization.Away b) _

/-- The local version of flat plus unramified. Only the stalk is assumed flat.
The finite presentation is used after localizing the base, before the final
passage from formal étaleness to a principal neighborhood. -/
lemma formallyEtale_stalk_of_flat_unramified (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
    (q : PrimeSpectrum B)
    [Algebra.IsUnramifiedAt A q.asIdeal]
    (hflat : letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under A) q.asIdeal
      Module.Flat (Localization.AtPrime (q.asIdeal.under A)) (Localization.AtPrime q.asIdeal)) :
    Algebra.IsEtaleAt A q.asIdeal := by
  let p := q.asIdeal.under A
  let Rp := Localization.AtPrime p
  let Sp := Localization (Algebra.algebraMapSubmonoid B p.primeCompl)
  let Sq := Localization.AtPrime q.asIdeal
  letI := Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  let : Module.Flat Rp Sq := hflat
  let f : Sp →ₐ[B] Sq := IsLocalization.liftAlgHom
    (M := Algebra.algebraMapSubmonoid B p.primeCompl)
    (f := Algebra.ofId _ _) (by
      rintro ⟨_, x, hx, rfl⟩
      simpa using! IsLocalization.map_units (M := q.asIdeal.primeCompl) Sq
        ⟨algebraMap A B x, by simpa [p, Ideal.under_def] using hx⟩)
  algebraize [f.toRingHom]
  have : IsScalarTower A Sp Sq := .to₁₃₄ _ B _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (Algebra.algebraMapSubmonoid Sp q.asIdeal.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (Algebra.algebraMapSubmonoid B p.primeCompl) _
      (by rintro _ ⟨x, hx, rfl⟩; simpa [p, Ideal.under_def] using hx)
  have : Algebra.FinitePresentation Rp Sp := by
    have : Algebra.IsPushout A Rp B Sp :=
      .symm <| Algebra.isPushout_of_isLocalization p.primeCompl _ _ _
    exact .equiv (Algebra.IsPushout.equiv A Rp B Sp)
  have : Algebra.EssFiniteType Rp Sq := .of_comp A _ _
  have : Algebra.FormallyUnramified Rp Sq := .of_restrictScalars A _ _
  have : Algebra.FormallyUnramified (IsLocalRing.ResidueField Rp)
      (IsLocalRing.ResidueField Rp ⊗[Rp] Sq) := inferInstance
  have : Algebra.FormallyEtale (IsLocalRing.ResidueField Rp)
      (IsLocalRing.ResidueField Rp ⊗[Rp] Sq) :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field _ _
  have : Algebra.FormallySmooth Rp Sq :=
    Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
      (R := Rp) (S := Sq) (P := Sp) (Algebra.algebraMapSubmonoid Sp q.asIdeal.primeCompl)
  have : Algebra.FormallyEtale Rp Sq := ⟨inferInstance, inferInstance⟩
  exact Algebra.FormallyEtale.comp A Rp Sq

theorem pointwise_flat_separable_criterion : pointwiseCriterion.{u,v} := by
  intro A B _ _ _ _ q
  letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under A) q.asIdeal
  constructor
  · intro h
    have hf := flat_stalk_of_neighborhood A B q h
    have hflat := (Module.flat_iff_of_isLocalization
      (Localization.AtPrime (q.asIdeal.under A)) (q.asIdeal.under A).primeCompl
      (Localization.AtPrime q.asIdeal)).mpr hf
    exact ⟨hflat, (prime_extension_eq A B q h).symm,
      finite_separable_residueFields A B q h⟩
  · rintro ⟨hflat, heq, hfin, hsep⟩
    have : Algebra.IsUnramifiedAt A q.asIdeal :=
      (Algebra.isUnramifiedAt_iff_map_eq A (q.asIdeal.under A) q.asIdeal).mpr
        ⟨hsep, heq.trans Localization.AtPrime.map_eq_maximalIdeal⟩
    have : Algebra.IsEtaleAt A q.asIdeal :=
      formallyEtale_stalk_of_flat_unramified A B q hflat
    exact (neighborhood_iff_isEtaleAt A B q).mpr inferInstance

theorem fibers_finite_separable_product : fibersFiniteSeparableProduct.{u,v} := by
  intro A B _ _ _ h p
  let : Algebra.Etale A B := h
  have he : Algebra.Etale p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] B) :=
    inferInstance
  exact (etale_iff_finite_separable_product p.asIdeal.ResidueField
    (p.asIdeal.ResidueField ⊗[A] B)).mp he

theorem zero_fiber_empty_product : zeroFiberEmptyProduct.{u,v} := by
  intro A B _ _ _ h p _
  exact ⟨default⟩

end
end AdvCommAlg.Etale

/- Mathlib proof attribution
Adapted portion near line 42:
The localization and finite-presentation construction, adapted to prove the
pointwise etale criterion.

Upstream: Mathlib/RingTheory/Smooth/Fiber.lean (around line 193)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
