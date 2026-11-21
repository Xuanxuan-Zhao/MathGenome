import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.FiniteLengthDuality
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.FiniteLengthDual

noncomputable section
universe u
namespace AdvCommAlg.Gorenstein
variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {E : Type u} [AddCommGroup E] [Module R E]

/-- Every simple module over a local ring embeds into the residue-field envelope. -/
lemma simple_embeds_envelope
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : IsInjectiveEnvelope ι)
    (S : Type u) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    ∃ j : S →ₗ[R] E, Function.Injective j := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule R S)
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact ⟨ι.comp e.toLinearMap, hι.injective.comp e.injective⟩

/-- Maps to the injective envelope separate every nonzero Artinian submodule. -/
lemma envelopeEvaluation_injective
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : IsInjectiveEnvelope ι)
    (M : Type u) [AddCommGroup M] [Module R M] [IsArtinian R M] :
    Function.Injective (envelopeEvaluation R E M) := by
  have : Module.Injective R E := hι.injectiveModule
  have : IsAtomic (Submodule R M) := inferInstance
  apply LinearMap.ker_eq_bot.mp
  by_contra hn
  obtain ⟨S, hS, hSk⟩ :=
    (eq_bot_or_exists_atom_le (LinearMap.ker (envelopeEvaluation R E M))).resolve_left hn
  have : IsSimpleModule R S := isSimpleModule_iff_isAtom.mpr hS
  obtain ⟨j, hj⟩ := simple_embeds_envelope ι hι S
  obtain ⟨f, hf⟩ := Module.Injective.out S.subtype S.subtype_injective j
  have hj0 : j = 0 := by
    ext s
    have hs := hSk s.property
    have hs0 : envelopeEvaluation R E M (s : M) = 0 := hs
    have he : f (s : M) = 0 := DFunLike.congr_fun hs0 f
    exact (hf s).symm.trans he
  have : Subsingleton S := ⟨fun x y => hj (by simp [hj0])⟩
  exact hS.ne_bot (Submodule.subsingleton_iff_eq_bot.mp this)

/-- Length preservation turns the separating evaluation map into a bijection. -/
lemma envelopeEvaluation_bijective [IsArtinianRing R]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : IsInjectiveEnvelope ι)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Bijective (envelopeEvaluation R E M) := by
  have : Module.Finite R (M →ₗ[R] E) := finiteLength_dual_finite R E ι hι M
  have : Module.Finite R ((M →ₗ[R] E) →ₗ[R] E) :=
    finiteLength_dual_finite R E ι hι (M →ₗ[R] E)
  have hi := envelopeEvaluation_injective ι hι M
  refine ⟨hi, LinearMap.range_eq_top.mp ?_⟩
  by_contra hn
  have hl := Submodule.length_lt hn
  have heq : Module.length R (LinearMap.range (envelopeEvaluation R E M)) =
      Module.length R ((M →ₗ[R] E) →ₗ[R] E) := by
    rw [← (LinearEquiv.ofInjective (envelopeEvaluation R E M) hi).length_eq,
      finiteLength_dual_length R E ι hι (M →ₗ[R] E),
      finiteLength_dual_length R E ι hι M]
  exact (ne_of_lt hl) heq

/-- The isomorphism has the required evaluation map as its underlying map. -/
theorem finiteLength_biduality : FiniteLengthDualitySpec.biduality.{u} := by
  intro R _ _ _ _ E _ _ ι hι M _ _ _
  exact ⟨LinearEquiv.ofBijective (envelopeEvaluation R E M)
    (envelopeEvaluation_bijective ι hι M), rfl⟩

/-- Naturality holds without finiteness, local, or Artinian assumptions. -/
theorem envelopeEvaluation_naturality : FiniteLengthDualitySpec.naturality.{u} := by
  intro R _ E M N _ _ _ _ _ _ f
  ext m ψ
  rfl

/-- Dualizing evaluation and then evaluating is the identity on the dual. -/
theorem envelopeEvaluation_triangle : FiniteLengthDualitySpec.triangle.{u} := by
  intro R _ E M _ _ _ _
  ext ψ m
  rfl

/-- Every map of duals is uniquely precomposition by a map of the original modules. -/
theorem finiteLength_dual_fullyFaithful : FiniteLengthDualitySpec.fullyFaithful.{u} := by
  intro R _ _ _ _ E _ _ ι hι M N _ _ _ _ _ _
  constructor
  · intro f g h
    ext m
    apply envelopeEvaluation_injective ι hι N
    ext ψ
    exact congrArg (fun k => k ψ m) h
  · intro g
    let e := LinearEquiv.ofBijective (envelopeEvaluation R E N)
      (envelopeEvaluation_bijective ι hι N)
    let f : M →ₗ[R] N := e.symm.toLinearMap.comp
      ((LinearMap.lcomp R E g).comp (envelopeEvaluation R E M))
    refine ⟨f, ?_⟩
    ext ψ m
    have h := congrArg (fun k : (N →ₗ[R] E) →ₗ[R] E => k ψ)
      (e.apply_symm_apply ((LinearMap.lcomp R E g) (envelopeEvaluation R E M m)))
    exact h

/-- The exact, length-preserving self-inverse Hom duality on all finite modules. -/
theorem finiteLength_exactDuality : FiniteLengthDualitySpec.exactDuality.{u} :=
  ⟨finiteLength_dual_finite, finiteLength_dual_exact, finiteLength_dual_length,
    finiteLength_biduality, envelopeEvaluation_naturality,
    finiteLength_dual_fullyFaithful, envelopeEvaluation_triangle⟩

end AdvCommAlg.Gorenstein
