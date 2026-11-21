import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.FiniteLengthDual
import Mathlib.RingTheory.HopkinsLevitzki

noncomputable section
universe u
namespace AdvCommAlg.Gorenstein
variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {E : Type u} [AddCommGroup E] [Module R E]

/-- Essentiality forces every map from a simple module to land in the envelope's socle. -/
lemma range_le_envelope {S : Type u} [AddCommGroup S] [Module R S] [IsSimpleModule R S]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : IsInjectiveEnvelope ι)
    (f : S →ₗ[R] E) : LinearMap.range f ≤ LinearMap.range ι := by
  by_cases hf : f = 0
  · simp [hf]
  have hfi := f.injective_of_ne_zero hf
  have hs : IsSimpleModule R (LinearMap.range f) :=
    IsSimpleModule.congr (LinearEquiv.ofInjective f hfi).symm
  have ha : IsAtom (LinearMap.range f) := isSimpleModule_iff_isAtom.mp hs
  have hn : LinearMap.range f ≠ ⊥ := fun h => hf (LinearMap.range_eq_bot.mp h)
  have hi := hι.essential (LinearMap.range f) hn
  exact ha.not_disjoint_iff_le.mp (fun hd => hi (disjoint_iff.mp hd))

/-- Postcomposing with the displayed inclusion identifies endomorphisms of k with its dual. -/
def residueEndDualEquiv
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : IsInjectiveEnvelope ι) :
    (IsLocalRing.ResidueField R →ₗ[R] IsLocalRing.ResidueField R) ≃ₗ[R]
      (IsLocalRing.ResidueField R →ₗ[R] E) := by
  have : IsSimpleModule R (IsLocalRing.ResidueField R) :=
    (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
      (R := R) (S := IsLocalRing.ResidueField R) (M := IsLocalRing.ResidueField R)
      (IsLocalRing.residue_surjective (R := R))).mpr inferInstance
  let p := LinearMap.compRight R (M := IsLocalRing.ResidueField R) ι
  apply LinearEquiv.ofBijective p
  constructor
  · intro f g h
    ext x
    exact hι.injective (DFunLike.congr_fun h x)
  · intro f
    let f' := f.codRestrict (LinearMap.range ι) (fun x => range_le_envelope ι hι f ⟨x, rfl⟩)
    let e := LinearEquiv.ofInjective ι hι.injective
    refine ⟨e.symm.toLinearMap.comp f', ?_⟩
    ext x
    exact congrArg Subtype.val (e.apply_symm_apply (f' x))

/-- R-linear endomorphisms of the residue field are multiplications by scalars. -/
def residueEndEquiv :
    (IsLocalRing.ResidueField R →ₗ[R] IsLocalRing.ResidueField R) ≃ₗ[R]
      IsLocalRing.ResidueField R :=
  (LinearMap.extendScalarsOfSurjectiveEquiv
    (IsLocalRing.residue_surjective (R := R))).trans
      (LinearMap.ringLmapEquivSelf (IsLocalRing.ResidueField R) R _)

lemma residue_dual_equiv
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : IsInjectiveEnvelope ι) :
    ∃ e : Depth.ResidueHom R E ≃ₗ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R,
      ∀ f, ι (e f) = f 1 := by
  let e := (residueEndDualEquiv ι hι).symm.trans (residueEndEquiv (R := R))
  refine ⟨e.extendScalarsOfSurjective (IsLocalRing.residue_surjective (R := R)), ?_⟩
  intro f
  change ι (((residueEndDualEquiv ι hι).symm f) 1) = f 1
  exact DFunLike.congr_fun ((residueEndDualEquiv ι hι).apply_symm_apply f) 1

omit [IsLocalRing R] in
/-- Hom into an injective module sends any short exact sequence to a reversed one. -/
lemma injective_dual_shortExact [Module.Injective R E]
    {A B C : Type u} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g) :
    Function.Injective (LinearMap.lcomp R E g) ∧
    Function.Surjective (LinearMap.lcomp R E f) ∧
    Function.Exact (LinearMap.lcomp R E g) (LinearMap.lcomp R E f) := by
  refine ⟨LinearMap.lcomp_injective_of_surjective g hg, ?_,
    LinearMap.exact_lcomp_of_exact_of_surjective E hex hg⟩
  intro h
  obtain ⟨l, hl⟩ := Module.Injective.out f hf h
  exact ⟨l, LinearMap.ext hl⟩

lemma length_dual_simple
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : IsInjectiveEnvelope ι)
    (S : Type u) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    Module.length R (S →ₗ[R] E) = Module.length R S := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp (inferInstance : IsSimpleModule R S)
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  obtain ⟨d, _⟩ := residue_dual_equiv ι hι
  exact (LinearEquiv.congrLeft E R e).length_eq.trans
    ((d.restrictScalars R).length_eq.trans e.length_eq.symm)

/-- Composition-series induction; neither the ring nor E needs to be finite here. -/
lemma length_dual_of_finiteLength
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : IsInjectiveEnvelope ι)
    (M : Type u) [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Module.length R (M →ₗ[R] E) = Module.length R M := by
  have : Module.Injective R E := hι.injectiveModule
  induction hM with
  | of_subsingleton => simp
  | @of_simple_quotient M _ _ N _ hN ih =>
    have hd := injective_dual_shortExact (E := E) N.subtype N.mkQ
      N.subtype_injective N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
    calc
      Module.length R (M →ₗ[R] E) =
          Module.length R ((M ⧸ N) →ₗ[R] E) + Module.length R (N →ₗ[R] E) :=
        Module.length_eq_add_of_exact _ _ hd.1 hd.2.1 hd.2.2
      _ = Module.length R (M ⧸ N) + Module.length R N := by
        rw [length_dual_simple ι hι, ih]
      _ = Module.length R M := by
        rw [Module.length_eq_add_of_exact N.subtype N.mkQ
          N.subtype_injective N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)]
        exact add_comm _ _

/-- The dual of the residue field is canonically the residue field. -/
theorem finiteLength_residueDual : FiniteLengthDualSpec.residueDual.{u} := by
  intro R _ _ _ _ E _ _ ι hι
  exact residue_dual_equiv ι hι

/-- Contravariant exactness on finite modules. -/
theorem finiteLength_dual_exact : FiniteLengthDualSpec.exactness.{u} := by
  intro R _ _ _ _ E _ _ ι hι A B C _ _ _ _ _ _ _ _ _ f g hf hg hex
  have := hι.injectiveModule
  exact injective_dual_shortExact f g hf hg hex

/-- Length is preserved for every finite module over the Artinian local ring. -/
theorem finiteLength_dual_length : FiniteLengthDualSpec.lengthDual.{u} := by
  intro R _ _ _ _ E _ _ ι hι M _ _ _
  exact length_dual_of_finiteLength ι hι M
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

/-- Finiteness follows from the length equality, without presupposing E finite. -/
theorem finiteLength_dual_finite : FiniteLengthDualSpec.finiteDual.{u} := by
  intro R _ _ _ _ E _ _ ι hι M _ _ _
  have hn : Module.length R (M →ₗ[R] E) ≠ ⊤ := by
    rw [finiteLength_dual_length R E ι hι M]
    exact Module.length_ne_top
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hn)).1
  infer_instance

/-- Taking the dual of R proves both finiteness and the required length of E. -/
theorem finiteLength_envelope_length : FiniteLengthDualSpec.envelopeLength.{u} := by
  intro R _ _ _ _ E _ _ ι hι
  have := finiteLength_dual_finite R E ι hι R
  let e := LinearMap.ringLmapEquivSelf R R E
  exact ⟨Module.Finite.equiv e, e.length_eq.symm.trans (finiteLength_dual_length R E ι hι R)⟩

end AdvCommAlg.Gorenstein
