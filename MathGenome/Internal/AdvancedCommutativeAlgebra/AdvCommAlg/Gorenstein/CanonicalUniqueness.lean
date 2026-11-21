import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.CanonicalUniqueness
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.MaximalCohenMacaulayDuality
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.CanonicalQuotient
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.GorensteinExtProfile

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Abelian

namespace AdvCommAlg.Gorenstein
open CohenMacaulay HomDualSpec

/-- Reduction by a common parameter and Ext¹ vanishing lift uniqueness. -/
private theorem canonical_unique_of_dimension (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R],
    ringKrullDim R = d →
    ∀ (W V : Type u) [AddCommGroup W] [Module R W] [Module.Finite R W]
      [AddCommGroup V] [Module R V] [Module.Finite R V],
      IsCanonicalModule R W → IsCanonicalModule R V → Nonempty (W ≃ₗ[R] V) := by
  induction d with
  | zero =>
    intro R _ _ _ _ hd W V _ _ _ _ _ _ hW hV
    haveI : Ring.KrullDimLE 0 R := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hd
    haveI : IsArtinianRing R := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
    obtain ⟨ι, hι⟩ := canonical_envelope_of_dimension_zero W hW hd
    obtain ⟨κ, hκ⟩ := canonical_envelope_of_dimension_zero V hV hd
    obtain ⟨e, _⟩ := injectiveEnvelope_equiv ι κ hι hκ
    exact ⟨e⟩
  | succ d ih =>
    intro R _ _ _ _ hd W V _ _ _ _ _ _ hW hV
    haveI : Nontrivial W := hW.2.1
    haveI : Nontrivial V := hV.2.1
    obtain ⟨xs, hs⟩ := exists_systemOfParameters R R
    cases xs with
    | nil =>
      have hz := (systemOfParameters_nil_iff R R).mp hs
      rw [dimension, Module.supportDim_self_eq_ringKrullDim, hd] at hz
      norm_cast at hz
    | cons x xs =>
      have hx := hs.1 x (by simp)
      have hRM : MaximalCohenMacaulay R R := by
        apply (maximalCohenMacaulay_iff_sourceDepth R R).mpr
        exact ((localCohenMacaulay_iff_sourceDepth R R).mp hW.1).trans
          (Module.supportDim_self_eq_ringKrullDim R)
      have hR := firstParameter_regular_maximalCM R hRM x xs hs
      have hVreg := firstParameter_regular_maximalCM V hV.2.2.1 x xs hs
      letI := principalQuotientLocalRing x hx
      let Q := R ⧸ Ideal.span {x}
      have hqdim : ringKrullDim Q = d := by
        have he := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hR hx
        rw [hd] at he
        apply ENat.WithBot.add_one_cancel.mp
        simpa only [Nat.cast_add, Nat.cast_one] using he
      have hBW : IsCanonicalModule Q (Reduction x W) := canonical_reduction R W hW x xs hs
      have hBV : IsCanonicalModule Q (Reduction x V) := canonical_reduction R V hV x xs hs
      obtain ⟨e⟩ := ih Q hqdim (Reduction x W) (Reduction x V) hBW hBV
      haveI := maximalCohenMacaulay_ext_vanishing R V hV W hW.2.2.1 1 (by omega)
      obtain ⟨f, hf⟩ := homDual_reduce_surjective W V x hVreg e.toLinearMap
      have hb : Function.Bijective (reductionMap x f) := by
        change reductionMap x f = e.toLinearMap at hf
        rw [hf]
        exact e.bijective
      exact ⟨LinearEquiv.ofBijective f (bijective_of_reduction_bijective f x hx hVreg hb)⟩

/-- GC-13: any two existing canonical modules are linearly isomorphic. -/
theorem canonical_unique : CanonicalUniquenessSpec.uniquenessType.{u} := by
  intro R _ _ _ _ W V _ _ _ _ _ _ hW hV
  obtain ⟨d, hd⟩ := exists_nat_dimension (R := R) R
  have hdR : ringKrullDim R = d := (Module.supportDim_self_eq_ringKrullDim R).symm.trans hd
  exact canonical_unique_of_dimension d R hdR W V hW hV

/-- GC-13: a chosen canonical module detects the Gorenstein condition. -/
theorem canonical_gorenstein_iff : CanonicalUniquenessSpec.gorensteinTestType.{u} := by
  intro R _ _ _ _ W _ _ _ hW
  constructor
  · intro hG
    have hCM := localGorenstein_cohenMacaulay R hG
    have hMCM : MaximalCohenMacaulay R R := by
      apply (maximalCohenMacaulay_iff_sourceDepth R R).mpr
      exact ((localCohenMacaulay_iff_sourceDepth R R).mp hCM).trans
        (Module.supportDim_self_eq_ringKrullDim R)
    have hcan : IsCanonicalModule R R :=
      ⟨hCM, inferInstance, hMCM, localGorenstein_type_one R hG, hG⟩
    exact canonical_unique R W R hW hcan
  · rintro ⟨e⟩
    have he := injectiveDimension_eq_of_iso e.toModuleIso
    change injectiveDimension (ModuleCat.of R R) ≠ ⊤
    rw [← he]
    exact hW.2.2.2.2

/-- GC-13: independence of the Gorenstein local presentation in GC-10. -/
theorem canonical_presentation_independent :
    CanonicalUniquenessSpec.presentationIndependenceType.{u} := by
  intro S T R _ _ _ _ _ _ _ _ _ _ _ hf hg hS hT hR s t d hs ht hd
  obtain ⟨hfinS, hcanS, _⟩ := canonicalQuotient_properties S R hf hS hR s d hs hd
  obtain ⟨hfinT, hcanT, _⟩ := canonicalQuotient_properties T R hg hT hR t d ht hd
  haveI := hfinS
  haveI := hfinT
  exact canonical_unique R _ _ hcanS hcanT

end AdvCommAlg.Gorenstein
