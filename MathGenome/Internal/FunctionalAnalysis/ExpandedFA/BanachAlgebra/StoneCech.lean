import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.StoneCech
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.ContinuousFunctionCharacters

noncomputable section
open scoped BoundedContinuousFunction
open Topology
namespace ExpandedFA.BanachAlgebra.StoneCech
open Spec
universe u v

/-- Restriction from the native compactification to the original space. -/
def restriction (S : Type u) [TopologicalSpace S] :
    C(_root_.StoneCech S, ℂ) →ₐ[ℂ] (S →ᵇ ℂ) where
  toFun f := (BoundedContinuousFunction.mkOfCompact f).compContinuous
    ⟨stoneCechUnit, continuous_stoneCechUnit⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem restriction_apply (S : Type u) [TopologicalSpace S]
    (f : C(_root_.StoneCech S, ℂ)) (x : S) :
    restriction S f x = f (stoneCechUnit x) := rfl

theorem restriction_injective (S : Type u) [TopologicalSpace S] :
    Function.Injective (restriction S) := by
  intro f g h
  apply ContinuousMap.coe_injective
  exact stoneCech_hom_ext f.continuous g.continuous
    (funext fun x => DFunLike.congr_fun h x)

/-- Extend a bounded scalar function into its compact closed norm ball, then
forget the codomain restriction. This works also when S is empty. -/
theorem restriction_surjective (S : Type u) [TopologicalSpace S] :
    Function.Surjective (restriction S) := by
  intro f
  let g : S → ↥(Metric.closedBall (0 : ℂ) ‖f‖) :=
    fun x => ⟨f x, by simpa using f.norm_coe_le_norm x⟩
  have hg : Continuous g := f.continuous.subtype_mk _
  let F : C(_root_.StoneCech S, ℂ) :=
    ⟨fun z => (stoneCechExtend hg z).val,
      continuous_subtype_val.comp (continuous_stoneCechExtend hg)⟩
  refine ⟨F, ?_⟩
  ext x
  exact congrArg Subtype.val (stoneCechExtend_stoneCechUnit hg x)

def restrictionEquiv (S : Type u) [TopologicalSpace S] :
    C(_root_.StoneCech S, ℂ) ≃ₐ[ℂ] (S →ᵇ ℂ) :=
  AlgEquiv.ofBijective (restriction S)
    ⟨restriction_injective S, restriction_surjective S⟩

/-- A unital complex algebra homomorphism to ℂ is a shared algebraic character. -/
def characterOfAlgHom {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A]
    (f : A →ₐ[ℂ] ℂ) : Specs.ExpandedFA.BanachAlgebra.Conventions.CharacterValue ℂ A :=
  ⟨f.toLinearMap, by
    refine ⟨?_, fun a b => map_mul f a b⟩
    intro h
    have hh := LinearMap.congr_fun h (1 : A)
    simp at hh⟩

/-- Evaluate the unique scalar extensions at a point of the native compactification. -/
def compactificationCharacter (S : Type u) [TopologicalSpace S]
    (z : _root_.StoneCech S) : Space S :=
  characterOfAlgHom ((ContinuousMap.evalAlgHom ℂ ℂ z).comp
    (restrictionEquiv S).symm.toAlgHom)

@[simp] theorem compactificationCharacter_apply (S : Type u) [TopologicalSpace S]
    (z : _root_.StoneCech S) (f : S →ᵇ ℂ) :
    (compactificationCharacter S z).val f = (restrictionEquiv S).symm f z := rfl

theorem compactificationCharacter_unit (S : Type u) [TopologicalSpace S] (x : S) :
    compactificationCharacter S (stoneCechUnit x) = evaluation x := by
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  exact DFunLike.congr_fun ((restrictionEquiv S).apply_symm_apply f) x

theorem compactificationCharacter_bijective (S : Type u) [TopologicalSpace S] :
    Function.Bijective (compactificationCharacter S) := by
  let : TopologicalSpace (Character ℂ C(_root_.StoneCech S, ℂ)) :=
    Characters.characterTopology C(_root_.StoneCech S, ℂ)
  constructor
  · intro z w h
    apply (ContinuousFunctionCharacters.compactEvaluationHomeomorph
      (_root_.StoneCech S)).injective
    apply Subtype.ext
    apply LinearMap.ext
    intro f
    have hh := congrArg (fun χ : Space S => χ.val (restrictionEquiv S f)) h
    simpa only [compactificationCharacter_apply, AlgEquiv.symm_apply_apply,
      ContinuousFunctionCharacters.compactEvaluationHomeomorph_apply] using hh
  · intro χ
    let ψ := characterOfAlgHom ((Characters.characterAlgHom χ).comp (restriction S))
    obtain ⟨z, hz, _⟩ := ContinuousFunctionCharacters.compact_characters_are_evaluations
      (_root_.StoneCech S) ψ
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply LinearMap.ext
    intro f
    have h := hz ((restrictionEquiv S).symm f)
    change χ.val (restrictionEquiv S ((restrictionEquiv S).symm f)) = _ at h
    change (restrictionEquiv S).symm f z = χ.val f
    simpa only [AlgEquiv.apply_symm_apply] using h.symm

theorem continuous_compactificationCharacter (S : Type u) [TopologicalSpace S] :
    Continuous (compactificationCharacter S) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro f
  exact ((restrictionEquiv S).symm f).continuous

local instance spaceT2 (S : Type u) [TopologicalSpace S] : T2Space (Space S) :=
  (Characters.characterHomeomorph (S →ᵇ ℂ)).isEmbedding.t2Space

/-- The homeomorphism identifies the actual character space with Stone–Čech;
its value on the original points is precisely point evaluation. -/
def characterHomeomorph (S : Type u) [TopologicalSpace S] :
    _root_.StoneCech S ≃ₜ Space S :=
  (Equiv.ofBijective (compactificationCharacter S)
    (compactificationCharacter_bijective S)).toHomeomorphOfContinuousClosed
      (continuous_compactificationCharacter S)
      (continuous_compactificationCharacter S).isClosedMap

@[simp] theorem characterHomeomorph_unit (S : Type u) [TopologicalSpace S] (x : S) :
    characterHomeomorph S (stoneCechUnit x) = evaluation x :=
  compactificationCharacter_unit S x

theorem compact_hausdorff : CompactHausdorff.{u} := by
  intro S _
  exact ⟨(characterHomeomorph S).compactSpace, inferInstance⟩

theorem native_identification : NativeIdentification.{u} := by
  intro S _
  exact ⟨characterHomeomorph S, characterHomeomorph_unit S⟩

theorem evaluation_dense_embedding : EvaluationDenseEmbedding.{u} := by
  intro S _ _ _
  let : T35Space S := { }
  have he : (evaluation : S → Space S) = characterHomeomorph S ∘ stoneCechUnit :=
    funext fun x => (characterHomeomorph_unit S x).symm
  rw [he]
  exact ⟨(characterHomeomorph S).isEmbedding.comp isEmbedding_stoneCechUnit,
    (characterHomeomorph S).surjective.denseRange.comp denseRange_stoneCechUnit
      (characterHomeomorph S).continuous⟩

theorem scalar_extension : ScalarExtension.{u} := by
  intro S _ _ _ f
  refine ⟨fun _ => rfl, ?_⟩
  intro F hF
  apply ContinuousMap.coe_injective
  exact (evaluation_dense_embedding S).2.equalizer F.continuous
    (gelfandExtension f).continuous (funext hF)

theorem universal_property : UniversalProperty.{u,v} := by
  intro S _ _ _ K _ _ _ f
  let F : C(Space S, K) :=
    ⟨stoneCechExtend f.continuous ∘ (characterHomeomorph S).symm,
      (continuous_stoneCechExtend f.continuous).comp (characterHomeomorph S).symm.continuous⟩
  have hF : ∀ x : S, F (evaluation x) = f x := by
    intro x
    change stoneCechExtend f.continuous ((characterHomeomorph S).symm (evaluation x)) = f x
    rw [← characterHomeomorph_unit S x, Homeomorph.symm_apply_apply,
      stoneCechExtend_stoneCechUnit]
  refine ⟨F, hF, ?_⟩
  intro G hG
  apply ContinuousMap.coe_injective
  exact (evaluation_dense_embedding S).2.equalizer G.continuous F.continuous
    (funext fun x => (hG x).trans (hF x).symm)

theorem empty_case : EmptyCase.{u} := by
  intro S _ _
  have hs : Subsingleton (S →ᵇ ℂ) := ⟨fun f g => by ext x; exact isEmptyElim x⟩
  let := hs
  refine ⟨hs, ⟨fun χ => ?_⟩⟩
  have h := Characters.character_map_one χ
  rw [Subsingleton.elim (1 : S →ᵇ ℂ) 0, map_zero] at h
  exact zero_ne_one h

theorem compact_characters_are_evaluations : CompactCharactersAreEvaluations.{u} :=
  ContinuousFunctionCharacters.compact_characters_are_evaluations

theorem empty_compact_case : EmptyCompactCase.{u} :=
  ContinuousFunctionCharacters.empty_compact_case

theorem disk_characters : DiskCharacters := ContinuousFunctionCharacters.disk_characters

theorem polydisk_characters : PolydiskCharacters :=
  ContinuousFunctionCharacters.holomorphic_polydisk_characters

end ExpandedFA.BanachAlgebra.StoneCech
