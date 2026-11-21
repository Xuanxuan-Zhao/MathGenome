import MathGenome.Internal.D07.Ch01.IsomorphismDefinition
import MathGenome.Internal.D07.Ch03.SubgroupProductCounting
import MathGenome.Internal.Specs.D07.Ch04.InternalDirectProduct

/-!
Recognition of internal direct products (K07.04.internal_direct_product).
Normality puts each mixed commutator in the intersection, so the factors commute.
Multiplication is then a homomorphism; trivial intersection gives injectivity,
and the set-product hypothesis gives surjectivity. No counting is involved.
-/
namespace D07.Ch04.InternalDirectProduct

open scoped Pointwise
universe u v

/-- Elements of the two normal factors commute when their intersection is trivial. -/
theorem normal_factors_commute (G : Type u) [Group G] (H K : Subgroup G)
    [H.Normal] [K.Normal] (hdis : H ⊓ K = ⊥) (h : H) (k : K) :
    Commute (h : G) (k : G) :=
  Subgroup.commute_of_normal_of_disjoint H K inferInstance inferInstance
    (disjoint_iff.mpr hdis) h k h.property k.property

/-- The source's specified multiplication map is a group isomorphism. -/
theorem internal_direct_product (G : Type u) [Group G] (H K : Subgroup G)
    [H.Normal] [K.Normal] (hdis : H ⊓ K = ⊥)
    (hprod : (H : Set G) * (K : Set G) = Set.univ) :
    ∃ e : H × K ≃* G, ∀ p : H × K, e p = (p.1 : G) * (p.2 : G) := by
  let f : H × K →* G :=
    { toFun := fun p => (p.1 : G) * (p.2 : G)
      map_one' := one_mul 1
      map_mul' := by
        intro p q
        change ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
          ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
        calc
          _ = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by
            simp only [mul_assoc]
          _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by
            rw [(normal_factors_commute G H K hdis q.1 p.2).eq]
          _ = _ := by simp only [mul_assoc] }
  have hf : Function.Bijective f := by
    constructor
    · exact Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hdis)
    · intro g
      have hg : g ∈ (H : Set G) * (K : Set G) := by rw [hprod]; trivial
      obtain ⟨h, hh, k, hk, he⟩ := hg
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), he⟩
  exact ⟨MulEquiv.ofBijective f hf, fun _ => rfl⟩

/-- The converse: the actual coordinate subgroups have all the required properties. -/
theorem coordinate_subgroups (A : Type u) (B : Type v) [Group A] [Group B] :
    let H : Subgroup (A × B) := (⊤ : Subgroup A).prod (⊥ : Subgroup B)
    let K : Subgroup (A × B) := (⊥ : Subgroup A).prod (⊤ : Subgroup B)
    H.Normal ∧ K.Normal ∧ H ⊓ K = ⊥ ∧
      (H : Set (A × B)) * (K : Set (A × B)) = Set.univ ∧
      ∀ (h : H) (k : K), Commute (h : A × B) (k : A × B) := by
  let H : Subgroup (A × B) := (⊤ : Subgroup A).prod (⊥ : Subgroup B)
  let K : Subgroup (A × B) := (⊥ : Subgroup A).prod (⊤ : Subgroup B)
  have hdis : H ⊓ K = ⊥ := by
    ext p
    simp [H, K, Subgroup.mem_prod, Prod.ext_iff, and_comm]
  refine ⟨inferInstance, inferInstance, hdis, ?_, normal_factors_commute _ H K hdis⟩
  apply Set.eq_univ_of_forall
  intro p
  refine ⟨(p.1, 1), ?_, (1, p.2), ?_, ?_⟩
  · simp [Subgroup.mem_prod]
  · simp [Subgroup.mem_prod]
  · exact Prod.ext (mul_one _) (one_mul _)

end D07.Ch04.InternalDirectProduct
