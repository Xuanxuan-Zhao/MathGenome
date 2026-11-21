import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.VectorLpDual
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.VectorLpRepresentation

/-!
Full Bochner Lp duality for reflexive real or complex Banach spaces.

The upstream representation theorem proves the norm bound using a countable
norming family on the separable range of a strongly measurable representative
(`exists_countable_norming_family`, `exists_stronglyMeasurable_norming_test`,
and `memLp_bound_of_unit_scalar_tests`). Its `pairing_norm` and `full_duality`
therefore apply to nonseparable E and to p = 1, q = infinity. Here we package
that fixed bilinear integral pairing as a linear isometric equivalence and
make quotient uniqueness and ordinary a.e. uniqueness explicit.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v

namespace ExpandedFA.PartIV.VectorLpDual
open VectorLpRepresentationSpec

theorem isometric_duality : VectorLpDualSpec.IsometricDuality.{u,v} := by
  intro 𝕜 _ X E _ _ _ _ hE μ _ p q _ _ _ hp
  obtain ⟨hi, hs⟩ := VectorLpRepresentation.full_duality 𝕜 hE μ p q hp
  exact ⟨hi, hi.injective, hs⟩

theorem isometric_equivalence : VectorLpDualSpec.IsometricEquivalence.{u,v} := by
  intro 𝕜 _ X E _ _ _ _ hE μ _ p q _ _ _ hp
  obtain ⟨hi, hs⟩ := VectorLpRepresentation.full_duality 𝕜 hE μ p q hp
  let T := LinearIsometryEquiv.ofSurjective
    ((PairingValue (E := E) 𝕜 μ p q).toLinearMap.toLinearIsometry hi) hs
  refine ⟨T, ?_⟩
  intro g f
  exact VectorLpRepresentation.pairing_formula 𝕜 μ p q g f

theorem exact_norm : VectorLpDualSpec.ExactNorm.{u,v} := by
  intro 𝕜 _ X E _ _ _ μ _ p q _ _ _ hp g
  exact VectorLpRepresentation.pairing_norm μ p q hp g

theorem representation : VectorLpDualSpec.Representation.{u,v} := by
  intro 𝕜 _ X E _ _ _ _ hE μ _ p q _ _ _ hp L
  obtain ⟨hi, hs⟩ := VectorLpRepresentation.full_duality 𝕜 hE μ p q hp
  obtain ⟨g, hg⟩ := hs L
  refine ⟨g, ⟨?_, ?_⟩, ?_⟩
  · intro f
    obtain ⟨hint, hform⟩ := VectorLpRepresentation.pairing_formula 𝕜 μ p q g f
    exact ⟨hint, by rw [← hform, hg]⟩
  · rw [← VectorLpRepresentation.pairing_norm μ p q hp g, hg]
  · intro h hh
    apply hi.injective
    ext f
    exact (VectorLpRepresentation.pairing_formula 𝕜 μ p q h f).2.trans
      ((hh.1 f).2.symm.trans (congrArg (fun M => M f) hg.symm))

theorem ordinary_ae_uniqueness : VectorLpDualSpec.OrdinaryAeUniqueness.{u,v} := by
  intro 𝕜 _ X E _ _ _ μ _ p q _ _ _ hp g h
  constructor
  · intro heq
    have hgh : g = h := (VectorLpRepresentation.pairing_isometry μ p q hp).injective (by
      ext f
      exact (VectorLpRepresentation.pairing_formula 𝕜 μ p q g f).2.trans
        ((heq f).trans (VectorLpRepresentation.pairing_formula 𝕜 μ p q h f).2.symm))
    subst h
    exact Filter.EventuallyEq.rfl
  · intro hgh f
    exact integral_congr_ae (hgh.mono (fun t ht => congrArg (fun ℓ => ℓ (f t)) ht))

theorem stronglyMeasurable_representation :
    VectorLpDualSpec.StronglyMeasurableRepresentation.{u,v} := by
  intro 𝕜 _ X E _ _ _ _ hE μ _ p q _ _ _ hp L
  obtain ⟨g, hg, _⟩ := representation 𝕜 hE μ p q hp L
  refine ⟨g, Lp.stronglyMeasurable g, Lp.memLp g, hg.1, ?_, ?_⟩
  · exact (Lp.norm_def g).symm.trans hg.2
  · intro h hh hL
    have heq : (hh.toLp h : X → (E →L[𝕜] 𝕜)) =ᵐ[μ] g := by
      apply (ordinary_ae_uniqueness 𝕜 μ p q hp (hh.toLp h) g).mp
      intro f
      calc
        (∫ t, (hh.toLp h) t (f t) ∂μ) = ∫ t, h t (f t) ∂μ := by
          apply integral_congr_ae
          exact hh.coeFn_toLp.mono (fun t ht => congrArg (fun ℓ => ℓ (f t)) ht)
        _ = L f := (hL f).symm
        _ = ∫ t, g t (f t) ∂μ := (hg.1 f).2
    exact hh.coeFn_toLp.symm.trans heq

end ExpandedFA.PartIV.VectorLpDual
