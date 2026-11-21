import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.ClosabilityAndDoubleAdjoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.HilbertAdjoint

/-! The closability criterion, double adjoint, and range/kernel identities of
paper.tex:13499–13526. Orthogonality is taken in the Hilbert `WithLp 2` product;
the graph itself retains the canonical ordinary-product representation. -/

noncomputable section

namespace ExpandedFA.Unbounded

variable {𝕜 H K : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

omit [CompleteSpace K] in
private theorem mem_graph_orthogonal_iff (A : Operator 𝕜 H K) (hA : DenselyDefined A)
    (y : K) (z : H) :
    WithLp.toLp 2 (-z, y) ∈
      (A.graph.map (WithLp.linearEquiv 2 𝕜 (H × K)).symm.toLinearMap).orthogonal ↔
    (y, z) ∈ (hilbertAdjoint A).graph := by
  rw [mem_hilbertAdjoint_graph_iff A hA]
  constructor
  · intro h x
    have hx := h _ (Submodule.mem_map.mpr
      ⟨((x : H), A x), A.mem_graph_iff.mpr ⟨x, rfl, rfl⟩, rfl⟩)
    change inner 𝕜 (x : H) (-z) + inner 𝕜 (A x) y = 0 at hx
    exact (neg_add_eq_zero.mp (by simpa only [inner_neg_right] using hx)).symm
  · intro h u hu
    obtain ⟨⟨x, b⟩, hx, rfl⟩ := hu
    obtain ⟨v, hv, hb⟩ := A.mem_graph_iff.mp hx
    dsimp only at hv hb
    change inner 𝕜 x (-z) + inner 𝕜 b y = 0
    rw [inner_neg_right, ← hv, ← hb, h v, neg_add_cancel]

/-- All adjoint graph vectors test membership in the closure of the original
graph. Completeness enters through the double-orthogonal-complement theorem. -/
theorem mem_graphClosure_iff_adjoint (A : Operator 𝕜 H K) (hA : DenselyDefined A)
    (x : H) (b : K) :
    (x, b) ∈ A.graph.topologicalClosure ↔
      ∀ y : (hilbertAdjoint A).domain,
        inner 𝕜 b (y : K) = inner 𝕜 x (hilbertAdjoint A y) := by
  let e := WithLp.prodContinuousLinearEquiv 2 𝕜 H K
  let L := A.graph.map e.symm.toLinearMap
  have hmap : L.topologicalClosure = A.graph.topologicalClosure.map e.symm.toLinearMap := by
    apply SetLike.coe_injective
    exact (e.symm.toHomeomorph.image_closure (A.graph : Set (H × K))).symm
  have hmem : (x, b) ∈ A.graph.topologicalClosure ↔
      WithLp.toLp 2 (x, b) ∈ L.orthogonal.orthogonal := by
    rw [Submodule.orthogonal_orthogonal_eq_closure, hmap, Submodule.mem_map_equiv]
    rfl
  rw [hmem, Submodule.mem_orthogonal']
  constructor
  · intro h y
    have hy : WithLp.toLp 2 (-hilbertAdjoint A y, (y : K)) ∈ L.orthogonal :=
      (mem_graph_orthogonal_iff A hA _ _).mpr
        ((hilbertAdjoint A).mem_graph_iff.mpr ⟨y, rfl, rfl⟩)
    have hh := h _ hy
    change inner 𝕜 x (-hilbertAdjoint A y) + inner 𝕜 b (y : K) = 0 at hh
    exact (neg_add_eq_zero.mp (by simpa only [inner_neg_right] using hh)).symm
  · intro h u hu
    obtain ⟨⟨a, y⟩, rfl⟩ := (WithLp.linearEquiv 2 𝕜 (H × K)).symm.surjective u
    change WithLp.toLp 2 (a, y) ∈
      (A.graph.map (WithLp.linearEquiv 2 𝕜 (H × K)).symm.toLinearMap).orthogonal at hu
    have hg : (y, -a) ∈ (hilbertAdjoint A).graph :=
      (mem_graph_orthogonal_iff A hA y (-a)).mp (by simpa only [neg_neg] using hu)
    obtain ⟨hy, hz⟩ := (mem_graph_iff (hilbertAdjoint A) (y, -a)).mp hg
    have hh := h ⟨y, hy⟩
    rw [hz, inner_neg_right] at hh
    change inner 𝕜 x a + inner 𝕜 b y = 0
    rw [hh, add_neg_cancel]

private theorem doubleAdjoint_graph_of_dense (A : Operator 𝕜 H K)
    (hA : DenselyDefined A) (hAdj : DenselyDefined (hilbertAdjoint A)) :
    (hilbertAdjoint (hilbertAdjoint A)).graph = A.graph.topologicalClosure := by
  ext ⟨x, b⟩
  rw [mem_hilbertAdjoint_graph_iff _ hAdj, mem_graphClosure_iff_adjoint A hA]
  constructor <;> intro h y
  · rw [← inner_conj_symm, ← inner_conj_symm x, h y]
  · rw [← inner_conj_symm, ← inner_conj_symm (y : K), h y]

/-- A densely defined operator is closable precisely when its adjoint has
dense domain. The forward implication rules out vertical graph vectors. -/
theorem isClosable_iff_dense_hilbertAdjoint (A : Operator 𝕜 H K)
    (hA : DenselyDefined A) : IsClosable A ↔ DenselyDefined (hilbertAdjoint A) := by
  constructor
  · intro hC
    change Dense ((hilbertAdjoint A).domain : Set K)
    rw [Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff]
    apply (Submodule.eq_bot_iff _).mpr
    intro b hb
    have hg : (0, b) ∈ A.graph.topologicalClosure :=
      (mem_graphClosure_iff_adjoint A hA 0 b).mpr (fun y => by
        rw [inner_zero_left]
        exact (Submodule.mem_orthogonal' _ _).mp hb y y.prop)
    rw [hC.graph_closure_eq_closure_graph] at hg
    exact A.closure.graph_fst_eq_zero_snd hg rfl
  · intro hAdj
    exact ⟨hilbertAdjoint (hilbertAdjoint A), (doubleAdjoint_graph_of_dense A hA hAdj).symm⟩

theorem hilbertAdjoint_hilbertAdjoint_graph (A : Operator 𝕜 H K)
    (hA : DenselyDefined A) (hC : IsClosable A) :
    (hilbertAdjoint (hilbertAdjoint A)).graph = A.graph.topologicalClosure :=
  doubleAdjoint_graph_of_dense A hA ((isClosable_iff_dense_hilbertAdjoint A hA).mp hC)

/-- Equality here includes equality of the operator domains. -/
theorem closure_eq_hilbertAdjoint_hilbertAdjoint (A : Operator 𝕜 H K)
    (hA : DenselyDefined A) (hC : IsClosable A) :
    closure A hC = hilbertAdjoint (hilbertAdjoint A) := by
  apply LinearPMap.eq_of_eq_graph
  exact hC.graph_closure_eq_closure_graph.symm.trans
    (hilbertAdjoint_hilbertAdjoint_graph A hA hC).symm

theorem hilbertAdjoint_hilbertAdjoint_of_closed (A : Operator 𝕜 H K)
    (hA : DenselyDefined A) (hC : IsClosed A) :
    hilbertAdjoint (hilbertAdjoint A) = A := by
  apply LinearPMap.eq_of_eq_graph
  exact (hilbertAdjoint_hilbertAdjoint_graph A hA hC.isClosable).trans
    hC.submodule_topologicalClosure_eq

theorem orthogonal_range_eq_kernel_hilbertAdjoint (A : Operator 𝕜 H K)
    (hA : DenselyDefined A) : (range A).orthogonal = kernel (hilbertAdjoint A) := by
  ext y
  change y ∈ A.toFun.range.orthogonal ↔ y ∈ OperatorDomainsSpec.kernelValue (hilbertAdjoint A)
  rw [Submodule.mem_orthogonal, mem_kernel_iff]
  constructor
  · intro h
    have hid : ∀ x : A.domain, inner 𝕜 (A x) y = inner 𝕜 (x : H) (0 : H) := by
      intro x
      rw [inner_zero_right]
      exact h (A x) ⟨x, rfl⟩
    have hy := (mem_hilbertAdjoint_domain_iff A hA y).mpr ⟨0, hid⟩
    exact ⟨hy, hilbertAdjoint_apply_eq A hA ⟨y, hy⟩ 0 hid⟩
  · rintro ⟨hy, hz⟩ b ⟨x, rfl⟩
    calc
      inner 𝕜 (A.toFun x) y = inner 𝕜 (x : H) (hilbertAdjoint A ⟨y, hy⟩) :=
        hilbertAdjoint_inner A hA ⟨y, hy⟩ x
      _ = 0 := by rw [hz, inner_zero_right]

theorem orthogonal_range_hilbertAdjoint_eq_kernel (A : Operator 𝕜 H K)
    (hA : DenselyDefined A) (hC : IsClosed A) :
    (range (hilbertAdjoint A)).orthogonal = kernel A := by
  rw [orthogonal_range_eq_kernel_hilbertAdjoint (hilbertAdjoint A)
    ((isClosable_iff_dense_hilbertAdjoint A hA).mp hC.isClosable),
    hilbertAdjoint_hilbertAdjoint_of_closed A hA hC]

end ExpandedFA.Unbounded
