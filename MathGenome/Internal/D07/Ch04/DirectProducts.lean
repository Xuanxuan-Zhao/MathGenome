import MathGenome.Internal.Specs.D07.Ch04.DirectProducts
import MathGenome.Internal.D07.Ch01.GroupDefinition

/-!
# External direct products

`K07.04.direct_products` (paper.tex:746–754). The product uses the
canonical pointwise group structure on the dependent Cartesian product.
Finite support is not imposed on this product. The final results identify
the additive direct sum with the finite-support subgroup and exhibit the
distinction for infinite families of nontrivial factors.
-/

namespace D07.Ch04.DirectProducts

universe u v w

abbrev Product (I : Type u) (G : I → Type v) : Type (max u v) := ∀ i, G i

abbrev productGroup (I : Type u) (G : I → Type v) [∀ i, Group (G i)] :
    Group (Product I G) := inferInstance

theorem pointwise_operations :
    Specs.D07.Ch04.DirectProducts.PointwiseOperations.{u, v} := by
  intro I G _
  exact ⟨fun _ _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem product_group_laws :
    Specs.D07.Ch04.DirectProducts.ProductGroupLaws.{u, v} := by
  intro I G _
  exact D07.Ch01.GroupDefinition.group_laws (Product I G)

theorem empty_product_trivial :
    Specs.D07.Ch04.DirectProducts.EmptyProductTrivial.{u, v} := by
  intro I G _ _ x
  exact funext fun i => isEmptyElim i

def projection (I : Type u) (G : I → Type v) [∀ i, Group (G i)] (i : I) :
    Product I G →* G i := Pi.evalMonoidHom G i

noncomputable def inclusion (I : Type u) (G : I → Type v) [∀ i, Group (G i)]
    (i : I) : G i →* Product I G := by
  classical
  exact MonoidHom.mulSingle G i

theorem projection_laws :
    Specs.D07.Ch04.DirectProducts.ProjectionLaws.{u, v} := by
  intro I G _ i
  exact ⟨fun _ => rfl, (projection I G i).map_one, (projection I G i).map_mul⟩

theorem inclusion_laws :
    Specs.D07.Ch04.DirectProducts.InclusionLaws.{u, v} := by
  classical
  intro I G _ i
  refine ⟨?_, ?_, (inclusion I G i).map_one, (inclusion I G i).map_mul⟩
  · intro g
    exact Pi.mulSingle_eq_same i g
  · intro g j hji
    exact Pi.mulSingle_eq_of_ne hji g

theorem coordinate_maps_split :
    Specs.D07.Ch04.DirectProducts.CoordinateMapsSplit.{u, v} := by
  intro I G _ i
  have h : ∀ g : G i, projection I G i (inclusion I G i g) = g :=
    (inclusion_laws I G i).1
  exact ⟨h, Function.LeftInverse.injective h, Function.LeftInverse.surjective h⟩

theorem finite_product_cardinality :
    Specs.D07.Ch04.DirectProducts.FiniteProductCardinality.{u, v} := by
  classical
  intro I G _ _ _
  exact Fintype.card_pi

theorem pair_cardinality :
    Specs.D07.Ch04.DirectProducts.PairCardinality.{v, w} := by
  intro A B _ _ _ _
  exact Fintype.card_prod A B

/-- The subgroup of tuples with only finitely many nonidentity coordinates.
No commutativity or finiteness assumption on the factors is needed. -/
def finiteSupportSubgroup (I : Type u) (G : I → Type v) [∀ i, Group (G i)] :
    Subgroup (Product I G) where
  carrier := {x | Set.Finite {i : I | x i ≠ 1}}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    apply (hx.union hy).subset
    intro i hi
    by_cases hx' : x i = 1
    · exact Or.inr (fun hy' => hi (by simp [hx', hy']))
    · exact Or.inl hx'
  inv_mem' := by
    intro x hx
    change Set.Finite {i : I | x i ≠ 1} at hx
    change Set.Finite {i : I | (x i)⁻¹ ≠ 1}
    simpa only [ne_eq, inv_eq_one] using hx

theorem finite_support_subgroup_exists :
    Specs.D07.Ch04.DirectProducts.FiniteSupportSubgroupExists.{u, v} := by
  intro I G _
  exact ⟨finiteSupportSubgroup I G, fun _ => Iff.rfl⟩

theorem finite_index_support :
    Specs.D07.Ch04.DirectProducts.FiniteIndexSupport.{u, v} := by
  intro I G _ _ x
  exact Set.toFinite _

theorem infinite_product_has_infinite_support :
    Specs.D07.Ch04.DirectProducts.InfiniteProductHasInfiniteSupport.{u, v} := by
  classical
  intro I G _ _ _
  have h : ∀ i : I, ∃ g : G i, g ≠ 1 := fun _ => exists_ne 1
  choose x hx using h
  refine ⟨x, ?_⟩
  have hs : {i : I | x i ≠ 1} = Set.univ := Set.ext (fun _ => by simp [hx])
  rw [hs]
  exact Set.infinite_univ

/-- The natural inclusion of the additive direct sum into the full product. -/
def directSumInclusion (I : Type u) (A : I → Type v) [∀ i, AddCommGroup (A i)] :
    DirectSum I A →+ (∀ i, A i) := DirectSum.coeFnAddMonoidHom A

theorem direct_sum_identification :
    Specs.D07.Ch04.DirectProducts.DirectSumIdentification.{u, v} := by
  classical
  intro I A _
  refine ⟨?_, ?_⟩
  · intro s t h
    exact DirectSum.ext (fun i => congrFun h i)
  · intro x
    constructor
    · rintro ⟨s, rfl⟩
      exact DFinsupp.finite_support s
    · intro hx
      let s : DFinsupp A := ⟨x, Trunc.mk ⟨hx.toFinset.val, by
        intro i
        by_cases hi : x i = 0
        · exact Or.inr hi
        · exact Or.inl (by simpa using hi)⟩⟩
      exact ⟨s, rfl⟩

theorem finite_direct_sum_is_product :
    Specs.D07.Ch04.DirectProducts.FiniteDirectSumIsProduct.{u, v} := by
  intro I A _ _
  refine ⟨(direct_sum_identification I A).1, ?_⟩
  intro x
  exact (direct_sum_identification I A).2 x |>.mpr (Set.toFinite _)

theorem infinite_direct_sum_is_proper :
    Specs.D07.Ch04.DirectProducts.InfiniteDirectSumIsProper.{u, v} := by
  classical
  intro I A _ _ _ hsurj
  have h : ∀ i : I, ∃ a : A i, a ≠ 0 := fun _ => exists_ne 0
  choose x hx using h
  have hfinite := (direct_sum_identification I A).2 x |>.mp (hsurj x)
  have hs : {i : I | x i ≠ 0} = Set.univ := Set.ext (fun _ => by simp [hx])
  rw [hs] at hfinite
  exact Set.infinite_univ hfinite

end D07.Ch04.DirectProducts
