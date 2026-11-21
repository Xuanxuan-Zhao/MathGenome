import MathGenome.Internal.D07.Ch03.CosetsPartition
import MathGenome.Internal.D07.Ch05.OrbitStabilizerEquivalence
import MathGenome.Internal.D07.Ch05.PermutationRepresentation
import MathGenome.Internal.Specs.D07.Ch05.CosetActionKernel

/-!
Coset actions, the normal core, and classification of transitive sets.
`K07.05.coset_action_kernel`, paper.tex:862–877. The canonical quotient
action is left multiplication, even when the subgroup is not normal.
-/

namespace D07.Ch05.CosetActionKernel

universe u v

open Specs.D07.Ch03.CosetsPartition

/-- The quotient representation agrees with the source's set-valued cosets. -/
theorem coset_equality (G : Type u) [Group G] (H : Subgroup G) (x y : G) :
    (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk y ↔
      leftCoset H x = leftCoset H y := by
  rw [QuotientGroup.eq]
  change x⁻¹ * y ∈ H ↔
    (fun h : G => x * h) '' (H : Set G) = (fun h : G => y * h) '' (H : Set G)
  exact (leftCoset_eq_iff H).symm

theorem coset_action_apply (G : Type u) [Group G] (H : Subgroup G) (g x : G) :
    g • (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk (g * x) := rfl

theorem coset_action_transitive (G : Type u) [Group G] (H : Subgroup G) :
    ActionDefinition.IsTransitive G (G ⧸ H) := by
  exact ⟨⟨QuotientGroup.mk (1 : G)⟩, fun x y => MulAction.exists_smul_eq G x y⟩

theorem coset_stabilizer (G : Type u) [Group G] (H : Subgroup G) :
    MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) = H :=
  MulAction.stabilizer_quotient H

theorem coset_kernel (G : Type u) [Group G] (H : Subgroup G) :
    (PermutationRepresentation.actionToHom G (G ⧸ H) inferInstance).ker =
      H.normalCore :=
  H.normalCore_eq_ker.symm

/-- Inverting the index converts the library's universal conjugation
condition into membership in the intersection of the conjugate subgroups. -/
theorem core_intersection (G : Type u) [Group G] (H : Subgroup G) :
    (H.normalCore : Set G) =
      ⋂ x : G, (fun h : G => x * h * x⁻¹) '' (H : Set G) := by
  ext g
  change (∀ b : G, b * g * b⁻¹ ∈ H) ↔ _
  simp only [Set.mem_iInter, Set.mem_image, SetLike.mem_coe]
  constructor
  · intro hg x
    refine ⟨x⁻¹ * g * x, ?_, ?_⟩
    · simpa only [inv_inv] using hg x⁻¹
    · simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  · intro hg b
    obtain ⟨h, hh, heq⟩ := hg b⁻¹
    rw [← heq]
    simpa only [inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hh

theorem core_largest_normal (G : Type u) [Group G] (H : Subgroup G) :
    H.normalCore.Normal ∧ H.normalCore ≤ H ∧
      ∀ N : Subgroup G, N.Normal → N ≤ H → N ≤ H.normalCore := by
  refine ⟨inferInstance, H.normalCore_le, ?_⟩
  intro N hN hNH
  haveI := hN
  exact Subgroup.normal_le_normalCore.mpr hNH

/-- Orbit–stabilizer becomes a bijection onto the whole set by transitivity;
its value on representatives proves equivariance by quotient induction. -/
theorem transitive_coset_equivalence (G : Type u) (X : Type v)
    [Group G] [MulAction G X] (ht : ActionDefinition.IsTransitive G X) :
    ∃ a : X, ∃ e : (G ⧸ OrbitStabilizerDefinitions.stabilizer G X a) ≃ X,
      (∀ g : G, e (QuotientGroup.mk g) = g • a) ∧
      (∀ (g : G) (q : G ⧸ OrbitStabilizerDefinitions.stabilizer G X a),
        e (g • q) = g • e q) := by
  obtain ⟨a⟩ := ht.1
  obtain ⟨e₀, he₀⟩ :=
    OrbitStabilizerEquivalence.orbit_stabilizer_equivalence G X a
  have hs : Function.Surjective
      (Subtype.val : ↥(OrbitStabilizerDefinitions.orbit G X a) → X) := by
    intro y
    obtain ⟨g, hg⟩ := ht.2 a y
    exact ⟨⟨y, ⟨g, hg⟩⟩, rfl⟩
  let e : (G ⧸ OrbitStabilizerDefinitions.stabilizer G X a) ≃ X :=
    e₀.trans (Equiv.ofBijective Subtype.val ⟨Subtype.val_injective, hs⟩)
  have he (g : G) : e (QuotientGroup.mk g) = g • a := he₀ g
  refine ⟨a, e, he, ?_⟩
  intro g q
  refine Quotient.inductionOn' q (fun x => ?_)
  change e (QuotientGroup.mk (g * x)) = g • e (QuotientGroup.mk x)
  rw [he, he, mul_smul]

end D07.Ch05.CosetActionKernel
