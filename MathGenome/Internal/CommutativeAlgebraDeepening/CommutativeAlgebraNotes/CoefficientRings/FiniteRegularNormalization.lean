import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.FiniteRegularNormalization
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.FinitePowerSeriesNormalization
import Mathlib.RingTheory.AdicCompletion.Topology

namespace CommutativeAlgebraNotes.CoefficientRings

open IsLocalRing
open Specs.CommutativeAlgebraNotes.CoefficientRings.FinitePowerSeriesNormalization
  (IsFiniteNormalization)
open Specs.CommutativeAlgebraNotes.CoefficientRings.FiniteRegularNormalization (Normalization)

private theorem finiteNormalization_range {A B : Type*}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [IsDomain B]
    {d : ℕ} {F : A →+* B} (hF : IsFiniteNormalization d F) :
    ∃ (S : Subring B) (hS : IsLocalRing S),
      letI : IsLocalRing S := hS
      IsFiniteNormalization d S.subtype := by
  obtain ⟨hlocal, _, hregular, hcomplete, hdim, hinj, hres, hfinite, hrad⟩ := hF
  let : IsLocalHom F := hlocal
  let : IsRegularLocalRing A := hregular
  let e : A ≃+* F.range := RingEquiv.ofBijective F.rangeRestrict
    ⟨fun _ _ h => hinj (congrArg Subtype.val h), F.rangeRestrict_surjective⟩
  let : IsLocalRing F.range := e.isLocalRing
  let ι : F.range →+* B := F.range.subtype
  have hfactor : ι.comp e.toRingHom = F := rfl
  have hι : IsLocalHom ι := by
    constructor
    intro a ha
    obtain ⟨x, rfl⟩ := e.surjective a
    exact e.toRingHom.isUnit_map (isUnit_of_map_unit F x ha)
  let : IsLocalHom ι := hι
  let : IsLocalHom e.toRingHom := isLocalHom_toRingHom e
  have hm : (maximalIdeal A).map e.toRingHom = maximalIdeal F.range :=
    map_ringEquiv_maximalIdeal e
  have hcompleteRange : IsAdicComplete (maximalIdeal F.range) F.range := by
    rw [← hm]
    exact (IsAdicComplete.congr_ringEquiv _ e).2 hcomplete
  have hresRange : Function.Bijective (ResidueField.map ι) := by
    refine ⟨(ResidueField.map ι).injective, ?_⟩
    intro b
    obtain ⟨a, ha⟩ := hres.surjective b
    exact ⟨ResidueField.map e.toRingHom a, (ResidueField.map_map e.toRingHom ι a).trans ha⟩
  let : Algebra A B := F.toAlgebra
  let : Algebra F.range B := ι.toAlgebra
  have hfiniteRange : Module.Finite F.range B :=
    Module.Finite.of_equiv_equiv e (RingEquiv.refl B) rfl
  refine ⟨F.range, inferInstance, hι, inferInstance, IsRegularLocalRing.of_ringEquiv e,
    hcompleteRange, e.ringKrullDim.symm.trans hdim, Subtype.val_injective, hresRange,
    hfiniteRange, ?_⟩
  change ((maximalIdeal F.range).map ι).radical = maximalIdeal B
  rwa [← hm, Ideal.map_map, hfactor]

/-- Finite regular normalization inside a complete Noetherian local domain. -/
theorem finiteRegularNormalization : Normalization := by
  intro B _ _ _ _ _
  obtain ⟨d, hd, hcases⟩ := finitePowerSeriesNormalization B
  refine ⟨d, hd, ?_⟩
  rcases hcases with hequal | hmixed
  · obtain ⟨_, _, F, _, _, _, _, _, _, hF⟩ := hequal.2
    exact finiteNormalization_range hF
  · obtain ⟨p, _, _, _, hQ, _, _, _, Λ, _, _, _, _, _, _, _, _, _, F,
      _, _, _, _, _, _, _, hF⟩ := hmixed
    exact finiteNormalization_range hF

end CommutativeAlgebraNotes.CoefficientRings
