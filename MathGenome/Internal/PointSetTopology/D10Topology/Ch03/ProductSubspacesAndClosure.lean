import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.ProductSubspacesAndClosure
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Products
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Subspaces

/-! Products and subspaces, canonical permutations/regroupings, and closure
of rectangles (paper.tex, lines 405–425). All conclusions concern the product
initial topology. Empty index sets, empty blocks and empty rectangles are allowed.
Classical choice is permitted for the closure theorem, as in the source. -/

open Set Topology
universe u v w z

namespace D10Topology.Ch03

theorem product_subspace_topology {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (A : ∀ i, Set (X i)) :
    productTopology (fun i => (tX i).induced (Subtype.val : A i → X i)) =
      (productTopology tX).induced (fun a i => (a i).val) := by
  simp +instances only [productTopology_eq_pi]
  let := tX
  let : ∀ i, TopologicalSpace (A i) := fun i => (tX i).induced Subtype.val
  exact (@IsEmbedding.piMap I (fun i => A i) X
    (fun i => (tX i).induced Subtype.val) tX
    (fun i => (Subtype.val : A i → X i)) (fun i => IsEmbedding.subtypeVal)).isInducing.eq_induced

theorem product_subspace_range {I : Type u} {X : I → Type v}
    (A : ∀ i, Set (X i)) :
    range (fun (a : ∀ i, A i) i => (a i).val) = univ.pi A := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩ i _
    exact (a i).property
  · intro hx
    exact ⟨fun i => ⟨x i, hx i (mem_univ i)⟩, rfl⟩

theorem product_embeddings {I : Type u} {A : I → Type v} {X : I → Type w}
    (tA : ∀ i, TopologicalSpace (A i)) (tX : ∀ i, TopologicalSpace (X i))
    (e : ∀ i, A i → X i) (he : ∀ i, @IsEmbedding _ _ (tA i) (tX i) (e i)) :
    @IsEmbedding _ _ (productTopology tA) (productTopology tX)
      (fun a i => e i (a i)) := by
  simp +instances only [productTopology_eq_pi]
  let := tA
  let := tX
  exact IsEmbedding.piMap he

theorem product_reindex {I : Type u} {J : Type v} {X : J → Type w}
    (tX : ∀ j, TopologicalSpace (X j)) (e : I ≃ J) :
    ∃ h : @Homeomorph (∀ i, X (e i)) (∀ j, X j)
      (productTopology (fun i => tX (e i))) (productTopology tX),
      (@Homeomorph.toEquiv _ _ (productTopology (fun i => tX (e i))) (productTopology tX) h) = Equiv.piCongrLeft X e := by
  let := tX
  refine ⟨@Homeomorph.mk _ _ (productTopology (fun i => tX (e i)))
    (productTopology tX) (Equiv.piCongrLeft X e) ?_ ?_, rfl⟩
  · simp +instances only [productTopology_eq_pi]
    exact (Homeomorph.piCongrLeft e).continuous_toFun
  · simp +instances only [productTopology_eq_pi]
    exact (Homeomorph.piCongrLeft e).continuous_invFun

theorem product_regroup {I : Type u} {J : I → Type v} {X : ∀ i, J i → Type w}
    (tX : ∀ i j, TopologicalSpace (X i j)) :
    ∃ h : @Homeomorph (∀ p : Sigma J, X p.1 p.2) (∀ i j, X i j)
      (productTopology (fun p : Sigma J => tX p.1 p.2))
      (productTopology (fun i => productTopology (tX i))),
      (@Homeomorph.toEquiv _ _ (productTopology (fun p : Sigma J => tX p.1 p.2))
        (productTopology (fun i => productTopology (tX i))) h) = Equiv.piCurry X := by
  let := tX
  refine ⟨@Homeomorph.mk _ _ (productTopology (fun p : Sigma J => tX p.1 p.2))
    (productTopology (fun i => productTopology (tX i))) (Equiv.piCurry X) ?_ ?_, rfl⟩
  · simp +instances only [productTopology_eq_pi]
    exact continuous_pi fun i => continuous_pi fun j => continuous_apply (A := fun p : Sigma J => X p.1 p.2) ⟨i, j⟩
  · simp +instances only [productTopology_eq_pi]
    exact continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)

theorem product_group_fibers {I : Type u} {J : Type v} {X : I → Type w}
    (tX : ∀ i, TopologicalSpace (X i)) (q : I → J) :
    ∃ h : @Homeomorph (∀ i, X i) (∀ j, ∀ i : {i // q i = j}, X i.val)
      (productTopology tX)
      (productTopology (fun j => productTopology
        (fun i : {i // q i = j} => tX i.val))),
      (@Homeomorph.toEquiv _ _ (productTopology tX)
        (productTopology (fun j => productTopology (fun i : {i // q i = j} => tX i.val))) h) = @Equiv.piCongrFiberwise I J X
        (fun j => ∀ i : {i // q i = j}, X i.val) q (fun _ => Equiv.refl _) := by
  let := tX
  refine ⟨@Homeomorph.mk _ _ (productTopology tX)
    (productTopology (fun j => productTopology (fun i : {i // q i = j} => tX i.val)))
    (@Equiv.piCongrFiberwise I J X
      (fun j => ∀ i : {i // q i = j}, X i.val) q (fun _ => Equiv.refl _)) ?_ ?_, rfl⟩
  · simp +instances only [productTopology_eq_pi]
    exact continuous_pi fun _ => continuous_pi fun i => continuous_apply i.val
  · simp +instances only [productTopology_eq_pi]
    exact continuous_pi fun i => (continuous_apply (A := fun a : {a // q a = q i} => X a.val) ⟨i, rfl⟩).comp
      (continuous_apply (A := fun j => ∀ a : {a // q a = j}, X a.val) (q i))

theorem closure_product_rectangle {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (A : ∀ i, Set (X i)) :
    @closure _ (productTopology tX) (univ.pi A) =
      univ.pi (fun i => @closure _ (tX i) (A i)) := by
  rw [productTopology_eq_pi]
  let := tX
  exact closure_pi_set univ A

theorem dense_product_rectangle {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (A : ∀ i, Set (X i))
    (hA : ∀ i, @Dense _ (tX i) (A i)) :
    @Dense _ (productTopology tX) (univ.pi A) := by
  rw [productTopology_eq_pi]
  let := tX
  exact dense_pi univ (fun i _ => hA i)

theorem closed_product_rectangle {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (A : ∀ i, Set (X i))
    (hA : ∀ i, IsClosed[tX i] (A i)) :
    IsClosed[productTopology tX] (univ.pi A) := by
  let := tX
  let : TopologicalSpace (Product X) := productTopology tX
  change IsClosed (univ.pi A)
  rw [Set.pi_def]
  exact isClosed_biInter fun i _ => (hA i).preimage (projection_continuous tX i)

end D10Topology.Ch03
