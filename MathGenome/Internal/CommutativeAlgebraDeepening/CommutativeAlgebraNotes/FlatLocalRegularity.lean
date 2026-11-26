import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.FlatLocalRegularity
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.SerreFlatTransfer
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.ResidueFieldRegularity
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.Flat.EquationalCriterion

universe u

open IsLocalRing
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace CommutativeAlgebraNotes

/-- The numbers of generators of an ideal and a quotient of it bound the
number of generators of its inverse image. -/
private theorem spanFinrank_le_of_quotient {B : Type u} [CommRing B] [IsNoetherianRing B]
    {I J : Ideal B} (hIJ : J ≤ I) :
    I.spanFinrank ≤ J.spanFinrank + (I.map (Ideal.Quotient.mk J)).spanFinrank := by
  classical
  let q := Ideal.Quotient.mk J
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  obtain ⟨s, hs, hspan⟩ :=
    (IsNoetherian.noetherian (I.map q)).exists_span_finset_card_eq_spanFinrank
  let t := s.image (Function.surjInv hq)
  let K := Ideal.span (↑t : Set B)
  have hcard : t.card ≤ (I.map q).spanFinrank :=
    (Finset.card_image_le (s := s)).trans_eq hs
  have hmap : K.map q = I.map q := by
    rw [Ideal.map_span, ← hspan]
    congr 1
    rw [Finset.coe_image, Set.image_image]
    simp only [Function.surjInv_eq, Set.image_id']
  have hsup : K ⊔ J = I := by
    have h := congrArg (Ideal.comap q) hmap
    rw [Ideal.comap_map_of_surjective q hq, Ideal.comap_map_of_surjective q hq,
      ← RingHom.ker_eq_comap_bot, show RingHom.ker q = J from Ideal.mk_ker,
      sup_eq_left.mpr hIJ] at h
    exact h
  have hK : K.spanFinrank ≤ (I.map q).spanFinrank := by
    apply le_trans _ hcard
    simpa [K, Ideal.span] using
      (Submodule.spanFinrank_span_le_ncard_of_finite (R := B) (Finset.finite_toSet t))
  have h := Submodule.spanRank_sup_le_sum_spanRank (p := K) (q := J)
  have hfg (L : Ideal B) : L.FG := IsNoetherian.noetherian L
  change (K ⊔ J : Ideal B).spanRank ≤ K.spanRank + J.spanRank at h
  rw [hsup, Submodule.FG.spanRank_eq_spanFinrank (hfg I),
    Submodule.FG.spanRank_eq_spanFinrank (hfg K),
    Submodule.FG.spanRank_eq_spanFinrank (hfg J), ← Nat.cast_add] at h
  exact (Nat.cast_le.mp h).trans (by simpa [Nat.add_comm] using Nat.add_le_add_right hK J.spanFinrank)

theorem isRegularLocalRing_of_flatLocal_of_regularClosedFiber :
    Specs.flatLocalRegularityAscent.{u} := by
  intro A B _ _ _ _ _ _ _ _ _ hA hF
  let J := (maximalIdeal A).map (algebraMap A B)
  have hJ : J ≤ maximalIdeal B := map_maximalIdeal_le (algebraMap A B)
  let : IsRegularLocalRing (B ⧸ J) := hF
  have hq : (maximalIdeal B).map (Ideal.Quotient.mk J) = maximalIdeal (B ⧸ J) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hgen := spanFinrank_le_of_quotient hJ
  rw [hq] at hgen
  have hJgen : J.spanFinrank ≤ (maximalIdeal A).spanFinrank :=
    Ideal.spanFinrank_map_le_of_fg (algebraMap A B) (IsNoetherian.noetherian _)
  have hdim : ringKrullDim B = ringKrullDim A + ringKrullDim (B ⧸ J) :=
    (AdvCommAlg.CohenMacaulay.SerreFlatTransfer.flatLocal_ring_formulas A B).1
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hbound := hgen.trans (Nat.add_le_add_right hJgen (maximalIdeal (B ⧸ J)).spanFinrank)
  have hcast : ((maximalIdeal B).spanFinrank : WithBot ℕ∞) ≤
      (((maximalIdeal A).spanFinrank + (maximalIdeal (B ⧸ J)).spanFinrank : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast hbound
  rwa [Nat.cast_add, hA.spanFinrank_maximalIdeal, hF.spanFinrank_maximalIdeal, ← hdim] at hcast

private noncomputable def extendScalarsTensorEquivOfRingHom {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (M : ModuleCat.{u} A) :
    let : Algebra A B := f.toAlgebra
    (ModuleCat.extendScalars f).obj M ≃ₗ[B] (B ⊗[A] M) :=
  LinearEquiv.refl _ _

private noncomputable def extendScalarsTensorEquiv {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (algebraMap A B)).obj M ≃ₗ[B] (B ⊗[A] M) := by
  have e := extendScalarsTensorEquivOfRingHom (algebraMap A B) M
  dsimp only at e
  rwa [toAlgebra_algebraMap] at e

/-- A projective-dimension bound on a finite module descends by descending
projectivity at the end of a finite free resolution segment. -/
private theorem hasProjectiveDimensionLE_of_faithfullyFlat
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsLocalRing A] [Module.FaithfullyFlat A B]
    (n : ℕ) (M : ModuleCat.{u} A) [Module.Finite A M]
    (h : HasProjectiveDimensionLE ((ModuleCat.extendScalars (algebraMap A B)).obj M) n) :
    HasProjectiveDimensionLE M n := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap A B)
  let : PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let : F.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))
  induction n generalizing M with
  | zero =>
    have : Projective (F.obj M) := (projective_iff_hasProjectiveDimensionLE_zero _).mpr h
    have : Module.Projective B (B ⊗[A] M) :=
      Module.Projective.of_equiv (extendScalarsTensorEquiv M)
    have : Module.Flat B (B ⊗[A] M) := Module.Flat.of_projective
    have : Module.Flat A M := Module.Flat.of_flat_tensorProduct A M B
    have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
    have : Module.Projective A M := Module.Flat.projective_of_finitePresentation
    exact (projective_iff_hasProjectiveDimensionLE_zero _).mp inferInstance
  | succ n ih =>
    obtain ⟨P, hP⟩ := AdvCommAlg.exists_minimalFreeResolution M
    let S := AdvCommAlg.syzygyShortComplex P 0
    let e : S.X₃ ≅ M := AdvCommAlg.resolutionSyzygyZeroIso P
    have hS : S.ShortExact := AdvCommAlg.syzygyShortComplex_shortExact P 0
    have : Projective S.X₂ := P.projective 0
    have : Module.Finite A S.X₁ := AdvCommAlg.minimalFreeResolution_syzygy_finite M P hP 1
    have : HasProjectiveDimensionLE (F.obj M) (n + 1) := h
    have h₃ : HasProjectiveDimensionLE (S.map F).X₃ (n + 1) :=
      hasProjectiveDimensionLT_of_iso (F.mapIso e).symm (n + 2)
    have h₂ : Projective (S.map F).X₂ := F.projective_obj S.X₂
    have h₁ : HasProjectiveDimensionLE (S.map F).X₁ n :=
      ((hS.map_of_exact F).hasProjectiveDimensionLT_X₃_iff n h₂).mp h₃
    have h₁' : HasProjectiveDimensionLE S.X₁ n := ih S.X₁ h₁
    have : HasProjectiveDimensionLE S.X₃ (n + 1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mpr h₁'
    exact hasProjectiveDimensionLT_of_iso e (n + 2)

theorem isRegularLocalRing_of_flatLocal_target :
    Specs.flatLocalRegularityDescent.{u} := by
  intro A B _ _ _ _ _ _ _ _ _ hB
  let : IsRegularLocalRing B := hB
  let : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let M : ModuleCat.{u} A := ModuleCat.of A (ResidueField A)
  let N := (ModuleCat.extendScalars (algebraMap A B)).obj M
  let e := (extendScalarsTensorEquiv (B := B) M).symm
  have : Module.Finite B (B ⊗[A] M) := inferInstance
  have : Module.Finite B N := Module.Finite.of_surjective e.toLinearMap e.surjective
  obtain ⟨xs, _, hd, _⟩ := AdvCommAlg.CohenMacaulay.exists_regular_generators B
  have hb := AdvCommAlg.CohenMacaulay.regularLocal_projectiveDimension_le B N xs.length hd
  have ha := hasProjectiveDimensionLE_of_faithfullyFlat (B := B) xs.length M
    ((projectiveDimension_le_iff N xs.length).mp hb)
  have hpd := (projectiveDimension_le_iff M xs.length).mpr ha
  have hne : projectiveDimension M ≠ ⊥ := by
    intro h
    exact not_subsingleton M (ModuleCat.subsingleton_of_isZero ((projectiveDimension_eq_bot_iff _).mp h))
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hd] at hpd
  obtain ⟨n, hn, _⟩ := ENat.le_natCast_iff.mp (WithBot.coe_le_coe.mp hpd)
  apply AdvCommAlg.CohenMacaulay.regularLocal_of_residueField_projectiveDimension_eq_nat n A
  simpa [hn] using hd.symm

end CommutativeAlgebraNotes
