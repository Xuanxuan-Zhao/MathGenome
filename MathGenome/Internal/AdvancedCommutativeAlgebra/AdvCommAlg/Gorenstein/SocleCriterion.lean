import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.FiniteLengthDual
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.InjectiveEnvelope
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.SocleCriterion
import Mathlib.RingTheory.HopkinsLevitzki

noncomputable section
universe u
namespace AdvCommAlg.Gorenstein
variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Every simple module over a local ring is isomorphic to its residue field. -/
lemma simpleModule_residue_equiv (S : Type u) [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] : Nonempty (S ≃ₗ[R] IsLocalRing.ResidueField R) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule R S)
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact ⟨e⟩

/-- An Artinian nonzero module contains a copy of the residue field. -/
lemma exists_residue_embedding (M : Type u) [AddCommGroup M] [Module R M]
    [IsArtinian R M] [Nontrivial M] :
    ∃ j : IsLocalRing.ResidueField R →ₗ[R] M, Function.Injective j := by
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R M)
  have : IsSimpleModule R S := isSimpleModule_iff_isAtom.mpr hS
  obtain ⟨e⟩ := simpleModule_residue_equiv (R := R) S
  exact ⟨S.subtype.comp e.symm.toLinearMap, S.subtype_injective.comp e.symm.injective⟩

/-- Every simple submodule is killed by the maximal ideal. -/
lemma simple_submodule_le_socle (M : Type u) [AddCommGroup M] [Module R M]
    (S : Submodule R M) [IsSimpleModule R S] : S ≤ socle R M := by
  obtain ⟨e⟩ := simpleModule_residue_equiv (R := R) S
  intro x hx
  apply (mem_socle_iff R M x).mpr
  intro a ha
  have hz : a • (⟨x, hx⟩ : S) = 0 := e.injective (by
    rw [map_smul, map_zero]
    change IsLocalRing.residue R a * e ⟨x, hx⟩ = 0
    rw [(IsLocalRing.residue_eq_zero_iff _).mpr ha, zero_mul])
  exact congrArg Subtype.val hz

/-- In an Artinian module the socle is an essential submodule. -/
lemma socle_isEssential (M : Type u) [AddCommGroup M] [Module R M]
    [IsArtinian R M] : IsEssential (socle R M).subtype := by
  intro N hN
  obtain ⟨S, hS, hSN⟩ := (eq_bot_or_exists_atom_le N).resolve_left hN
  have : IsSimpleModule R S := isSimpleModule_iff_isAtom.mpr hS
  have hSs := simple_submodule_le_socle M S
  rw [Submodule.range_subtype]
  exact fun h => hS.ne_bot (le_bot_iff.mp (h ▸ le_inf hSN hSs))

omit [IsLocalRing R] in
/-- An injection between modules of equal finite length is an isomorphism. -/
lemma surjective_of_injective_of_length_eq {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [IsArtinian R N] [IsNoetherian R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f)
    (hlen : Module.length R M = Module.length R N) : Function.Surjective f := by
  apply LinearMap.range_eq_top.mp
  by_contra hn
  have he := (LinearEquiv.ofInjective f hf).length_eq
  have hlt := Submodule.length_lt hn
  rw [← he, hlen] at hlt
  exact lt_irrefl _ hlt

/-- Self-injectivity identifies the ring with an injective envelope of k.
The envelope's residue-field Hom is one-dimensional. -/
lemma socle_finrank_one_of_selfInjective [IsArtinianRing R]
    (hinj : Module.Injective R R) :
    Module.finrank (IsLocalRing.ResidueField R) (socle R R) = 1 := by
  have : Module.Injective R R := hinj
  obtain ⟨D⟩ := residueField_injectiveEnvelope_exists R
  let E := D.carrier
  let ι : IsLocalRing.ResidueField R →ₗ[R] E := D.inclusion
  have hι : IsInjectiveEnvelope ι := D.isEnvelope
  obtain ⟨j, hj⟩ := exists_residue_embedding (R := R) R
  obtain ⟨f, hf⟩ := Module.Injective.out ι hι.injective j
  have hcomp : f.comp ι = j := LinearMap.ext hf
  have hfi : Function.Injective f :=
    injective_of_essential ι hι.essential f (hcomp ▸ hj)
  have hlen := (finiteLength_envelope_length R E ι hι).2
  have hfs := surjective_of_injective_of_length_eq f hfi hlen
  let e : E ≃ₗ[R] R := LinearEquiv.ofBijective f ⟨hfi, hfs⟩
  let p : Depth.ResidueHom R E ≃ₗ[R] Depth.ResidueHom R R :=
    LinearEquiv.congrRight e
  let q := Depth.residueLinearEquiv R p
  obtain ⟨d, _⟩ := finiteLength_residueDual R E ι hι
  obtain ⟨s, _⟩ := hom_socle_equiv R R
  simpa using (s.symm.trans (q.symm.trans d)).finrank_eq

/-- A one-dimensional socle makes R an essential extension of k.
Embedding it in the injective envelope and comparing lengths proves injectivity. -/
lemma selfInjective_of_socle_finrank_one [IsArtinianRing R]
    (hdim : Module.finrank (IsLocalRing.ResidueField R) (socle R R) = 1) :
    Module.Injective R R := by
  obtain ⟨s⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hdim
  let sR := s.restrictScalars R
  let j : IsLocalRing.ResidueField R →ₗ[R] R := (socle R R).subtype.comp sR.toLinearMap
  have hj : Function.Injective j := (socle R R).subtype_injective.comp sR.injective
  have hjrange : LinearMap.range j = socle R R := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact (sR a).property
    · intro hx
      obtain ⟨a, ha⟩ := sR.surjective ⟨x, hx⟩
      exact ⟨a, congrArg Subtype.val ha⟩
  have hjess : IsEssential j := by
    intro N hN
    have hs := socle_isEssential (R := R) R N hN
    rwa [Submodule.range_subtype, ← hjrange] at hs
  obtain ⟨D⟩ := residueField_injectiveEnvelope_exists R
  let E := D.carrier
  let ι : IsLocalRing.ResidueField R →ₗ[R] E := D.inclusion
  have hι : IsInjectiveEnvelope ι := D.isEnvelope
  have : Module.Injective R E := hι.injectiveModule
  obtain ⟨f, hf⟩ := Module.Injective.out j hj ι
  have hcomp : f.comp j = ι := LinearMap.ext hf
  have hfi : Function.Injective f :=
    injective_of_essential j hjess f (hcomp ▸ hι.injective)
  obtain ⟨hE, hlen⟩ := finiteLength_envelope_length R E ι hι
  have : Module.Finite R E := hE
  have hfs := surjective_of_injective_of_length_eq f hfi hlen.symm
  let e : R ≃ₗ[R] E := LinearEquiv.ofBijective f ⟨hfi, hfs⟩
  exact (Module.Baer.of_equiv e.symm (Module.Baer.of_injective hι.injectiveModule)).injective

/-- GC-05 (second assertion): an Artinian local ring is self-injective
if and only if its canonical residue-field socle has dimension one. -/
theorem selfInjective_iff_socle_finrank_one :
    SocleCriterionSpec.selfInjective_iff_socle_finrank_one.{u} := by
  intro R _ _ _ _
  exact ⟨socle_finrank_one_of_selfInjective, selfInjective_of_socle_finrank_one⟩

end AdvCommAlg.Gorenstein
