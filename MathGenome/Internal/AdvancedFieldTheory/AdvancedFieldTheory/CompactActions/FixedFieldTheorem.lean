import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.CompactActions.FiniteOrbitFields
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteGaloisStages.UnionConverse
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.InverseLimit.Profiniteness
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.CompactActions.FixedFieldTheorem
import Mathlib.Topology.Algebra.MulAction

/-! C11: fixed fields of faithful compact actions.
Finite orbit fields prove the Galois property and finite-set approximation.
The action has dense image by approximation, and closed image by compactness.
The final continuous bijection has continuous inverse by compact-to-Hausdorff.
-/

universe u v
noncomputable section
open scoped Classical Pointwise
namespace AdvancedFieldTheory.CompactActions

variable (G : Type u) (E : Type v) [Group G] [Field E] [MulSemiringAction G E]
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable (hOpen : ∀ a : E, IsOpen (MulAction.stabilizer G a : Set G))
include hOpen

/-- The orbit fields form a directed cover by finite Galois extensions. -/
theorem isGalois_compact_fixedBase : IsGalois (fixedBase G E) E := by
  obtain ⟨hdir, hcover, _, _⟩ := directed_cover_cofinal G E
  apply isGalois_of_directed_union (orbitField G E)
  · intro S T
    exact ⟨S ∪ T, (hdir S T).1, (hdir S T).2⟩
  · intro S
    obtain ⟨_, _, ρ, _, _, _, hfd, _, _⟩ := finiteOrbitStage G E hOpen S
    exact hfd
  · intro S
    obtain ⟨_, _, ρ, _, _, _, _, hgal, _⟩ := finiteOrbitStage G E hOpen S
    exact hgal
  · exact hcover

/-- Every finite part of an automorphism is realized by the given action. -/
lemma exists_action_matching (σ : E ≃ₐ[fixedBase G E] E) (S : Finset E) :
    ∃ g : G, ∀ x ∈ S, g • x = σ x := by
  obtain ⟨_, _, ρ, hρ, _, _, hfd, hgal, hsurj⟩ := finiteOrbitStage G E hOpen S
  let := hgal
  obtain ⟨g, hg⟩ := hsurj (restriction (orbitField G E S) σ)
  refine ⟨g, fun x hx => ?_⟩
  let y : orbitField G E S := ⟨x, self_mem_orbitField G E S hx⟩
  calc
    g • x = (ρ g y : E) := (hρ g y).symm
    _ = (restriction (orbitField G E S) σ y : E) := by rw [hg]
    _ = σ x := restriction_apply _ σ y

/-- Continuity uses only the openness of the original element stabilizers. -/
lemma continuous_actionHom :
    Continuous (MulSemiringAction.toAlgAut G (fixedBase G E) E) := by
  let := isGalois_compact_fixedBase G E hOpen
  apply (KrullTopology.continuous_iff_evaluations (fixedBase G E) E _).mpr
  let : TopologicalSpace E := ⊥
  let : DiscreteTopology E := ⟨rfl⟩
  let : ContinuousSMul G E := continuousSMul_iff_stabilizer_isOpen.mpr hOpen
  intro x
  exact continuous_id.smul continuous_const

/-- Finite-set matching meets every basic Krull coset. -/
lemma denseRange_actionHom :
    DenseRange (MulSemiringAction.toAlgAut G (fixedBase G E) E) := by
  let := isGalois_compact_fixedBase G E hOpen
  let φ := MulSemiringAction.toAlgAut G (fixedBase G E) E
  apply (KrullTopology.finiteCosetBasis_isTopologicalBasis (fixedBase G E) E).dense_iff.mpr
  rintro U ⟨σ, S, hS, rfl⟩ _
  obtain ⟨g, hg⟩ := exists_action_matching G E hOpen σ hS.toFinset
  refine ⟨φ g, ?_, ⟨g, rfl⟩⟩
  refine ⟨σ⁻¹ * φ g, ?_, by simp⟩
  intro x hx
  change σ.symm (g • x) = x
  rw [hg x (hS.mem_toFinset.mpr hx), σ.symm_apply_apply]

/-- The image is both dense and compact, hence is the whole Hausdorff target. -/
lemma surjective_actionHom :
    Function.Surjective (MulSemiringAction.toAlgAut G (fixedBase G E) E) := by
  let := isGalois_compact_fixedBase G E hOpen
  let := galoisGroup_t2Space (fixedBase G E) E
  have hc := continuous_actionHom G E hOpen
  have hd := denseRange_actionHom G E hOpen
  intro σ
  have hmem := hd σ
  rw [(isCompact_range hc).isClosed.closure_eq] at hmem
  exact hmem

/-- The isomorphism is the given action, with its original topology on G
and the Krull topology on the automorphism group. -/
theorem compactAction_topologicalIsomorphism [FaithfulSMul G E] :
    ∃! e : G ≃ₜ* (E ≃ₐ[fixedBase G E] E),
      e.toMulEquiv.toMonoidHom = MulSemiringAction.toAlgAut G (fixedBase G E) E := by
  let := isGalois_compact_fixedBase G E hOpen
  let := galoisGroup_t2Space (fixedBase G E) E
  let φ := MulSemiringAction.toAlgAut G (fixedBase G E) E
  have hinj : Function.Injective φ := by
    intro g h heq
    exact eq_of_smul_eq_smul (fun x : E => DFunLike.congr_fun heq x)
  let e := MulEquiv.ofBijective φ ⟨hinj, surjective_actionHom G E hOpen⟩
  have hc : Continuous e := continuous_actionHom G E hOpen
  let c : G ≃ₜ* (E ≃ₐ[fixedBase G E] E) :=
    { e with
      continuous_toFun := hc
      continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 }
  refine ⟨c, rfl, ?_⟩
  intro c' hc'
  apply ContinuousMulEquiv.ext
  intro g
  exact DFunLike.congr_fun hc' g

end AdvancedFieldTheory.CompactActions
