import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.HilbertAdjoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.OperatorDomains

/-! The densely defined Hilbert adjoint, with its exact domain and graph semantics.
This uses the canonical partial linear maps; no closedness of A is assumed. -/

noncomputable section

namespace ExpandedFA.Unbounded

variable {𝕜 H K : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

/-- The Hilbert adjoint. Semantic assertions require the original operator to
be densely defined; outside that case this retains Mathlib's totalization. -/
def hilbertAdjoint (A : Operator 𝕜 H K) : Operator 𝕜 K H :=
  HilbertAdjointSpec.adjointValue A

theorem hilbertAdjoint_inner (A : Operator 𝕜 H K) (hA : DenselyDefined A)
    (y : (hilbertAdjoint A).domain) (x : A.domain) :
    inner 𝕜 (A x) (y : K) = inner 𝕜 (x : H) (hilbertAdjoint A y) :=
  (LinearPMap.adjoint_isFormalAdjoint hA).symm x y

theorem mem_hilbertAdjoint_domain_iff (A : Operator 𝕜 H K) (hA : DenselyDefined A)
    (y : K) : y ∈ (hilbertAdjoint A).domain ↔
      ∃ z : H, ∀ x : A.domain, inner 𝕜 (A x) y = inner 𝕜 (x : H) z := by
  constructor
  · intro hy
    exact ⟨hilbertAdjoint A ⟨y, hy⟩, hilbertAdjoint_inner A hA ⟨y, hy⟩⟩
  · rintro ⟨z, hz⟩
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨z, fun x => ?_⟩
    rw [← inner_conj_symm, ← inner_conj_symm y, hz x]

theorem hilbertAdjoint_witness_unique (A : Operator 𝕜 H K) (hA : DenselyDefined A)
    (y : K) (z w : H)
    (hz : ∀ x : A.domain, inner 𝕜 (A x) y = inner 𝕜 (x : H) z)
    (hw : ∀ x : A.domain, inner 𝕜 (A x) y = inner 𝕜 (x : H) w) : z = w := by
  apply Dense.eq_of_inner_right (𝕜 := 𝕜) hA
  intro x hx
  exact (hz ⟨x, hx⟩).symm.trans (hw ⟨x, hx⟩)

theorem hilbertAdjoint_apply_eq (A : Operator 𝕜 H K) (hA : DenselyDefined A)
    (y : (hilbertAdjoint A).domain) (z : H)
    (hz : ∀ x : A.domain, inner 𝕜 (A x) (y : K) = inner 𝕜 (x : H) z) :
    hilbertAdjoint A y = z :=
  hilbertAdjoint_witness_unique A hA y _ z (hilbertAdjoint_inner A hA y) hz

theorem hilbertAdjoint_isClosed (A : Operator 𝕜 H K) (hA : DenselyDefined A) :
    IsClosed (hilbertAdjoint A) :=
  LinearPMap.adjoint_isClosed hA

theorem mem_hilbertAdjoint_graph_iff (A : Operator 𝕜 H K) (hA : DenselyDefined A)
    (y : K) (z : H) : (y, z) ∈ (hilbertAdjoint A).graph ↔
      ∀ x : A.domain, inner 𝕜 (A x) y = inner 𝕜 (x : H) z := by
  constructor
  · intro h
    obtain ⟨hy, hz⟩ := (mem_graph_iff (hilbertAdjoint A) (y, z)).mp h
    change hilbertAdjoint A ⟨y, hy⟩ = z at hz
    intro x
    rw [← hz]
    exact hilbertAdjoint_inner A hA ⟨y, hy⟩ x
  · intro hz
    have hy := (mem_hilbertAdjoint_domain_iff A hA y).mpr ⟨z, hz⟩
    exact (mem_graph_iff (hilbertAdjoint A) (y, z)).mpr
      ⟨hy, hilbertAdjoint_apply_eq A hA ⟨y, hy⟩ z hz⟩

theorem hilbertAdjoint_graph_orthogonal (A : Operator 𝕜 H K) (hA : DenselyDefined A) :
    (hilbertAdjoint A).graph.map (WithLp.linearEquiv 2 𝕜 (K × H)).symm.toLinearMap =
      (A.graph.map ((LinearEquiv.skewSwap 𝕜 H K).trans
        (WithLp.linearEquiv 2 𝕜 (K × H)).symm).toLinearMap).orthogonal := by
  ext u
  obtain ⟨⟨y, z⟩, rfl⟩ := (WithLp.linearEquiv 2 𝕜 (K × H)).symm.surjective u
  rw [Submodule.mem_map_equiv]
  simp only [LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
  rw [mem_hilbertAdjoint_graph_iff A hA]
  simp only [Submodule.mem_map, Submodule.mem_orthogonal,
    LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.skewSwap_apply,
    WithLp.coe_symm_linearEquiv, WithLp.prod_inner_apply,
    Prod.exists, forall_exists_index, and_imp]
  constructor
  · intro h u x b hab hu
    subst u
    obtain ⟨v, hv, hb⟩ := A.mem_graph_iff.mp hab
    dsimp only at hv hb
    change inner 𝕜 (-b) y + inner 𝕜 x z = 0
    rw [inner_neg_left, ← hv, ← hb, h v, neg_add_cancel]
  · intro h x
    have hx := h (WithLp.toLp 2 (-A x, (x : H))) x (A x)
      (A.mem_graph_iff.mpr ⟨x, rfl, rfl⟩) rfl
    change inner 𝕜 (-A x) y + inner 𝕜 (x : H) z = 0 at hx
    simpa only [inner_neg_left, neg_add_eq_zero] using hx

end ExpandedFA.Unbounded
