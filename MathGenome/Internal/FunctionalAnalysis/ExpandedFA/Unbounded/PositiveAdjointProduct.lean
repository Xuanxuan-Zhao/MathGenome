import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.PositiveAdjointProduct
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.ClosabilityAndDoubleAdjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Sequences

/-! The elementary adjoint-product stage of paper.tex:13879–13892.
Orthogonal projection onto the closed graph solves I+A*A. Positivity yields
its contractive inverse and symmetry; surjectivity gives self-adjointness.
Orthogonality proves the graph core. Finally a common-core Cauchy argument
establishes the domain and norm conclusions for normal operators, without
an unbounded spectral theorem. -/

noncomputable section
open scoped InnerProductSpace Topology
namespace ExpandedFA.Unbounded.PositiveAdjointProduct
open PositiveAdjointProductSpec
variable {𝕜 H K : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

abbrev base (A : Operator 𝕜 H K) (x : (adjointProduct A).domain) : A.domain :=
  ⟨x, x.property.choose⟩
abbrev image (A : Operator 𝕜 H K) (x : (adjointProduct A).domain) :
    (hilbertAdjoint A).domain := ⟨A (base A x), x.property.choose_spec⟩

theorem product_inner (A : Operator 𝕜 H K) (hd : DenselyDefined A)
    (x : (adjointProduct A).domain) (y : A.domain) :
    inner 𝕜 (y : H) (adjointProduct A x) = inner 𝕜 (A y) (A (base A x)) :=
  (hilbertAdjoint_inner A hd (image A x) y).symm

theorem shifted_surjective (A : Operator 𝕜 H K) (hd : DenselyDefined A)
    (hc : A.IsClosed) (f : H) :
    ∃ x : (adjointProduct A).domain, (x : H) + adjointProduct A x = f := by
  let e := WithLp.prodContinuousLinearEquiv 2 𝕜 H K
  let G := A.graph.map e.symm.toLinearMap
  have hG : _root_.IsClosed (G : Set (WithLp 2 (H × K))) := by
    exact e.symm.toHomeomorph.isClosedMap _ hc
  let : CompleteSpace G := hG.isComplete.completeSpace_coe
  obtain ⟨u, hu, v, hv, huv⟩ := G.exists_add_mem_mem_orthogonal (WithLp.toLp 2 (f, 0))
  obtain ⟨⟨x, a⟩, hx, hxu⟩ := hu
  obtain ⟨z, hz, ha⟩ := A.mem_graph_iff.mp hx
  have hvpair : e v = (f - (z : H), -A z) := by
    have hh := congrArg e huv
    change (f, (0 : K)) = e u + e v at hh
    have he : e u = ((z : H), A z) := by rw [← hxu]; exact Prod.ext hz.symm ha.symm
    rw [he] at hh
    have hv : e v = (f, (0 : K)) - ((z : H), A z) := eq_sub_of_add_eq' hh.symm
    exact hv.trans (by ext <;> simp)
  have htest : ∀ y : A.domain,
      inner 𝕜 (A y) (A z) = inner 𝕜 (y : H) (f - (z : H)) := by
    intro y
    have hh := hv _ (Submodule.mem_map.mpr ⟨((y : H), A y), A.mem_graph y, rfl⟩)
    have he : v = e.symm (f - (z : H), -A z) := by rw [← hvpair, e.symm_apply_apply]
    rw [he] at hh
    change inner 𝕜 (y : H) (f - (z : H)) + inner 𝕜 (A y) (-A z) = 0 at hh
    rw [inner_neg_right] at hh
    exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hh)).symm
  have hm := (mem_hilbertAdjoint_domain_iff A hd (A z)).mpr ⟨f - (z : H), htest⟩
  refine ⟨⟨z, ⟨z.property, hm⟩⟩, ?_⟩
  have he := hilbertAdjoint_apply_eq A hd ⟨A z, hm⟩ (f - (z : H)) htest
  change (z : H) + hilbertAdjoint A ⟨A z, hm⟩ = f
  rw [he, add_sub_cancel]

theorem product_nonnegative (A : Operator 𝕜 H K) (hd : DenselyDefined A)
    (x : (adjointProduct A).domain) :
    0 ≤ RCLike.re (inner 𝕜 (x : H) (adjointProduct A x)) := by
  rw [product_inner A hd x (base A x)]
  exact inner_self_nonneg

theorem product_formalAdjoint (A : Operator 𝕜 H K) (hd : DenselyDefined A) :
    (adjointProduct A).IsFormalAdjoint (adjointProduct A) := by
  intro x y
  rw [← inner_conj_symm, product_inner A hd x (base A y), inner_conj_symm,
    product_inner A hd y (base A x)]

/-- I+A*A, as a linear map on the exact product domain. -/
def shiftedMap (A : Operator 𝕜 H K) : (adjointProduct A).domain →ₗ[𝕜] H :=
  (adjointProduct A).domain.subtype + (adjointProduct A).toFun

theorem shiftedMap_bound (A : Operator 𝕜 H K) (hd : DenselyDefined A)
    (x : (adjointProduct A).domain) : ‖(x : H)‖ ≤ ‖shiftedMap A x‖ := by
  have hp := product_nonnegative A hd x
  have he : ‖(x : H)‖ ^ 2 ≤ RCLike.re (inner 𝕜 (x : H) (shiftedMap A x)) := by
    change _ ≤ RCLike.re (inner 𝕜 (x : H) ((x : H) + adjointProduct A x))
    rw [inner_add_right, map_add, ← norm_sq_eq_re_inner]
    exact le_add_of_nonneg_right hp
  have hb := re_inner_le_norm (𝕜 := 𝕜) (x : H) (shiftedMap A x)
  by_cases hz : ‖(x : H)‖ = 0
  · rw [hz]; exact norm_nonneg _
  · have hpos : 0 < ‖(x : H)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

theorem shiftedMap_injective (A : Operator 𝕜 H K) (hd : DenselyDefined A) :
    Function.Injective (shiftedMap A) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have h := shiftedMap_bound A hd x
  rw [hx, norm_zero] at h
  exact Subtype.ext (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

theorem product_dense (A : Operator 𝕜 H K) (hd : DenselyDefined A) (hc : A.IsClosed) :
    Dense ((adjointProduct A).domain : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm _ bot_le
  intro f hf
  obtain ⟨u, hu⟩ := shifted_surjective A hd hc f
  have ho : inner 𝕜 (u : H) f = 0 := hf u u.property
  rw [← hu, inner_add_right] at ho
  have hr := congrArg RCLike.re ho
  rw [map_add, map_zero, ← norm_sq_eq_re_inner] at hr
  have hp := product_nonnegative A hd u
  have hn : ‖(u : H)‖ = 0 := by nlinarith [sq_nonneg ‖(u : H)‖]
  have hz : u = 0 := Subtype.ext (norm_eq_zero.mp hn)
  simpa [hz] using hu.symm

theorem product_selfAdjoint (A : Operator 𝕜 H K) (hd : DenselyDefined A)
    (hc : A.IsClosed) : adjointProduct A = hilbertAdjoint (adjointProduct A) := by
  let P := adjointProduct A
  have hdp : DenselyDefined P := product_dense A hd hc
  have hs : P.IsFormalAdjoint P := product_formalAdjoint A hd
  have hle : P ≤ P.adjoint := LinearPMap.IsFormalAdjoint.le_adjoint hdp hs
  apply le_antisymm hle
  apply LinearPMap.le_of_le_graph
  intro p hp
  obtain ⟨y, hy, hyp⟩ := P.adjoint.mem_graph_iff.mp hp
  obtain ⟨u, hu⟩ := shifted_surjective A hd hc ((y : H) + P.adjoint y)
  have heq : (y : H) = (u : H) := by
    apply ext_inner_left 𝕜
    intro f
    obtain ⟨v, hv⟩ := shifted_surjective A hd hc f
    rw [← hv, inner_add_left, inner_add_left]
    rw [(LinearPMap.adjoint_isFormalAdjoint hdp).symm v y, hs v u]
    rw [← inner_add_right, ← inner_add_right, ← hu]
  have hvalue : P.adjoint y = P u := by
    have he := hu
    change (u : H) + P u = (y : H) + P.adjoint y at he
    rw [heq] at he
    exact (add_left_cancel he).symm
  exact P.mem_graph_iff.mpr ⟨u, heq.symm.trans hy, hvalue.symm.trans hyp⟩

/-- Linear bijection underlying the inverse; no completeness of the ambient-norm
product domain is asserted. -/
def shiftedEquiv (A : Operator 𝕜 H K) (hd : DenselyDefined A) (hc : A.IsClosed) :
    (adjointProduct A).domain ≃ₗ[𝕜] H :=
  LinearEquiv.ofBijective (shiftedMap A)
    ⟨shiftedMap_injective A hd, shifted_surjective A hd hc⟩

def inverse (A : Operator 𝕜 H K) (hd : DenselyDefined A) (hc : A.IsClosed) : H →L[𝕜] H :=
  (((adjointProduct A).domain.subtype).comp (shiftedEquiv A hd hc).symm.toLinearMap).mkContinuous
    1 (by
      intro f
      change ‖((shiftedEquiv A hd hc).symm f : H)‖ ≤ 1 * ‖f‖
      have he : shiftedMap A ((shiftedEquiv A hd hc).symm f) = f :=
        (shiftedEquiv A hd hc).apply_symm_apply f
      simpa only [one_mul, he] using
        shiftedMap_bound A hd ((shiftedEquiv A hd hc).symm f))

theorem inverse_right (A : Operator 𝕜 H K) (hd : DenselyDefined A) (hc : A.IsClosed)
    (f : H) : ∃ hx : inverse A hd hc f ∈ (adjointProduct A).domain,
    inverse A hd hc f + adjointProduct A ⟨inverse A hd hc f, hx⟩ = f := by
  exact ⟨((shiftedEquiv A hd hc).symm f).property,
    (shiftedEquiv A hd hc).apply_symm_apply f⟩

theorem inverse_left (A : Operator 𝕜 H K) (hd : DenselyDefined A) (hc : A.IsClosed)
    (x : (adjointProduct A).domain) :
    inverse A hd hc ((x : H) + adjointProduct A x) = (x : H) :=
  congrArg Subtype.val ((shiftedEquiv A hd hc).symm_apply_apply x)

theorem inverse_injective (A : Operator 𝕜 H K) (hd : DenselyDefined A) (hc : A.IsClosed) :
    Function.Injective (inverse A hd hc) := by
  intro f g h
  change ((shiftedEquiv A hd hc).symm f : H) = ((shiftedEquiv A hd hc).symm g : H) at h
  exact (shiftedEquiv A hd hc).symm.injective (Subtype.ext h)

theorem inverse_symmetric (A : Operator 𝕜 H K) (hd : DenselyDefined A) (hc : A.IsClosed)
    (f g : H) : inner 𝕜 (inverse A hd hc f) g = inner 𝕜 f (inverse A hd hc g) := by
  let u := (shiftedEquiv A hd hc).symm f
  let v := (shiftedEquiv A hd hc).symm g
  have hf : (u : H) + adjointProduct A u = f := (shiftedEquiv A hd hc).apply_symm_apply f
  have hg : (v : H) + adjointProduct A v = g := (shiftedEquiv A hd hc).apply_symm_apply g
  change inner 𝕜 (u : H) g = inner 𝕜 f (v : H)
  rw [← hf, ← hg, inner_add_right, inner_add_left, product_formalAdjoint A hd u v]

theorem inverse_selfAdjoint (A : Operator 𝕜 H K) (hd : DenselyDefined A) (hc : A.IsClosed) :
    (inverse A hd hc).adjoint = inverse A hd hc := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left 𝕜
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right, inverse_symmetric A hd hc]

theorem inverse_contract (A : Operator 𝕜 H K) (hd : DenselyDefined A) (hc : A.IsClosed) :
    ‖inverse A hd hc‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖((shiftedEquiv A hd hc).symm f : H)‖ ≤ 1 * ‖f‖
  have he : shiftedMap A ((shiftedEquiv A hd hc).symm f) = f :=
    (shiftedEquiv A hd hc).apply_symm_apply f
  simpa only [one_mul, he] using
    shiftedMap_bound A hd ((shiftedEquiv A hd hc).symm f)

theorem inverse_nonnegative (A : Operator 𝕜 H K) (hd : DenselyDefined A)
    (hc : A.IsClosed) (f : H) : 0 ≤ RCLike.re (inner 𝕜 f (inverse A hd hc f)) := by
  let u := (shiftedEquiv A hd hc).symm f
  have hf : (u : H) + adjointProduct A u = f := (shiftedEquiv A hd hc).apply_symm_apply f
  change 0 ≤ RCLike.re (inner 𝕜 f (u : H))
  rw [← hf, inner_add_left, map_add, ← norm_sq_eq_re_inner,
    product_formalAdjoint A hd u u]
  exact add_nonneg (sq_nonneg _) (product_nonnegative A hd u)

/-- Hilbert realization of a graph, with the product inner product. -/
def hilbertGraph (A : Operator 𝕜 H K) : Submodule 𝕜 (WithLp 2 (H × K)) :=
  A.graph.map (WithLp.linearEquiv 2 𝕜 (H × K)).symm.toLinearMap

theorem hilbertGraph_closed (A : Operator 𝕜 H K) (hc : A.IsClosed) :
    _root_.IsClosed (hilbertGraph A : Set (WithLp 2 (H × K))) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 H K).symm.toHomeomorph.isClosedMap _ hc

theorem graph_core_orthogonal (A : Operator 𝕜 H K) (hd : DenselyDefined A)
    (hc : A.IsClosed) (x : A.domain)
    (hx : WithLp.toLp 2 ((x : H), A x) ∈
      (hilbertGraph (A.domRestrict (adjointProduct A).domain)).orthogonal) : x = 0 := by
  obtain ⟨y, hy⟩ := shifted_surjective A hd hc (x : H)
  have hm : ((y : H), A (base A y)) ∈ (A.domRestrict (adjointProduct A).domain).graph := by
    exact (A.domRestrict _).mem_graph ⟨y, y.property, (base A y).property⟩
  have hh := (Submodule.mem_orthogonal' _ _).mp hx _
    (Submodule.mem_map.mpr ⟨((y : H), A (base A y)), hm, rfl⟩)
  change inner 𝕜 (x : H) (y : H) + inner 𝕜 (A x) (A (base A y)) = 0 at hh
  rw [← product_inner A hd y x, ← inner_add_right, hy] at hh
  exact Subtype.ext (inner_self_eq_zero.mp hh)

theorem graph_core (A : Operator 𝕜 H K) (hd : DenselyDefined A) (hc : A.IsClosed) :
    OperatorDomainsSpec.coreValue A (adjointProduct A).domain := by
  have hle : (adjointProduct A).domain ≤ A.domain := fun x hx => hx.choose
  refine ⟨hle, ?_⟩
  let e := WithLp.prodContinuousLinearEquiv 2 𝕜 H K
  let G := hilbertGraph A
  let L := hilbertGraph (A.domRestrict (adjointProduct A).domain)
  have hLG : L ≤ G := Submodule.map_mono (LinearPMap.le_graph_of_le (A.domRestrict_le))
  have hG := hilbertGraph_closed A hc
  let : CompleteSpace G := hG.isComplete.completeSpace_coe
  have horth : L.orthogonal = G.orthogonal := by
    apply le_antisymm _ (Submodule.orthogonal_le hLG)
    intro v hv
    obtain ⟨u, hu, w, hw, hvuw⟩ := G.exists_add_mem_mem_orthogonal v
    have huL : u ∈ L.orthogonal := by
      have hwL := (Submodule.orthogonal_le hLG) hw
      have huvw : u = v - w := eq_sub_of_add_eq hvuw.symm
      rw [huvw]
      exact L.orthogonal.sub_mem hv hwL
    obtain ⟨⟨a, b⟩, hab, huab⟩ := hu
    obtain ⟨x, hxa, hxb⟩ := A.mem_graph_iff.mp hab
    have huform : u = WithLp.toLp 2 ((x : H), A x) := by
      rw [← huab]; exact congrArg (WithLp.toLp 2) (Prod.ext hxa.symm hxb.symm)
    have hxzero : x = 0 := graph_core_orthogonal A hd hc x (huform ▸ huL)
    have huzero : u = 0 := by rw [huform, hxzero]; simp
    simpa only [hvuw, huzero, zero_add] using hw
  have hclosure : L.topologicalClosure = G := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, horth, G.orthogonal_orthogonal]
  have mapclosure (T : Operator 𝕜 H K) :
      (hilbertGraph T).topologicalClosure = T.graph.topologicalClosure.map e.symm.toLinearMap := by
    apply SetLike.coe_injective
    exact (e.symm.toHomeomorph.image_closure (T.graph : Set (H × K))).symm
  have hgraphs : (A.domRestrict (adjointProduct A).domain).graph.topologicalClosure = A.graph := by
    apply Submodule.map_injective_of_injective e.symm.injective
    exact (mapclosure _).symm.trans hclosure
  exact hgraphs.trans hc.submodule_topologicalClosure_eq.symm

/-- Equality of image norms on a graph core extends to the whole graph.
The target operator is only required to be closed. -/
theorem norm_extension_from_core (S T : Operator 𝕜 H K)
    (D : Submodule 𝕜 H) (hcore : OperatorDomainsSpec.coreValue S D)
    (hDT : D ≤ T.domain) (hT : T.IsClosed)
    (hNorm : ∀ d : D, ‖S ⟨d, hcore.1 d.property⟩‖ = ‖T ⟨d, hDT d.property⟩‖)
    (x : S.domain) : ∃ y : T.domain, (y : H) = (x : H) ∧ ‖T y‖ = ‖S x‖ := by
  have hm : ((x : H), S x) ∈ (S.domRestrict D).graph.topologicalClosure := by
    rw [hcore.2]
    exact S.graph.le_topologicalClosure (S.mem_graph x)
  obtain ⟨p, hp, hlim⟩ := mem_closure_iff_seq_limit.mp hm
  choose z hz1 hz2 using fun n => (S.domRestrict D).mem_graph_iff.mp (hp n)
  let d (n : ℕ) : D := ⟨z n, (z n).property.1⟩
  let s (n : ℕ) : S.domain := ⟨d n, hcore.1 (d n).property⟩
  let t (n : ℕ) : T.domain := ⟨d n, hDT (d n).property⟩
  have hpair : (fun n => ((d n : H), S (s n))) = p := by
    funext n
    exact Prod.ext (hz1 n) (hz2 n)
  rw [← hpair] at hlim
  have hxc : Filter.Tendsto (fun n => (d n : H)) Filter.atTop (𝓝 (x : H)) := hlim.fst_nhds
  have hSc : Filter.Tendsto (fun n => S (s n)) Filter.atTop (𝓝 (S x)) := hlim.snd_nhds
  have hdist : ∀ n m, dist (T (t n)) (T (t m)) = dist (S (s n)) (S (s m)) := by
    intro n m
    rw [dist_eq_norm, dist_eq_norm, ← T.map_sub, ← S.map_sub]
    exact (hNorm (d n - d m)).symm
  have hTc : CauchySeq (fun n => T (t n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.mp hSc.cauchySeq ε hε
    exact ⟨M, fun n hn m hm => (hdist n m) ▸ hM n hn m hm⟩
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hTc
  have hgraph : ((x : H), b) ∈ T.graph := by
    exact hT.mem_of_tendsto (hxc.prodMk_nhds hb)
      (Filter.Eventually.of_forall (fun n => T.mem_graph (t n)))
  obtain ⟨y, hy, hTy⟩ := T.mem_graph_iff.mp hgraph
  refine ⟨y, hy, ?_⟩
  have hnormlim : Filter.Tendsto (fun n => ‖S (s n)‖) Filter.atTop (𝓝 ‖b‖) := by
    have he : (fun n => ‖S (s n)‖) = (fun n => ‖T (t n)‖) := funext (fun n => hNorm (d n))
    rw [he]
    exact hb.norm
  rw [hTy]
  exact tendsto_nhds_unique hnormlim hSc.norm

section Normal
variable (N : Operator 𝕜 H H) (hd : DenselyDefined N) (hc : N.IsClosed)
include hd hc

theorem normal_product_norm
    (he : adjointProduct N = adjointProduct (hilbertAdjoint N))
    (x : (adjointProduct N).domain) (y : (adjointProduct (hilbertAdjoint N)).domain)
    (hxy : (x : H) = (y : H)) :
    ‖N (base N x)‖ = ‖hilbertAdjoint N (base (hilbertAdjoint N) y)‖ := by
  have hda : DenselyDefined (hilbertAdjoint N) :=
    (isClosable_iff_dense_hilbertAdjoint N hd).mp hc.isClosable
  have hp : adjointProduct N x = adjointProduct (hilbertAdjoint N) y :=
    (le_of_eq he).2 hxy
  have hinner : inner 𝕜 (N (base N x)) (N (base N x)) =
      inner 𝕜 (hilbertAdjoint N (base (hilbertAdjoint N) y))
        (hilbertAdjoint N (base (hilbertAdjoint N) y)) := by
    rw [← product_inner N hd x (base N x),
      ← product_inner (hilbertAdjoint N) hda y (base (hilbertAdjoint N) y), hp]
    exact congrArg (fun u => inner 𝕜 u (adjointProduct (hilbertAdjoint N) y)) hxy
  have hs := congrArg RCLike.re hinner
  rw [← norm_sq_eq_re_inner, ← norm_sq_eq_re_inner] at hs
  nlinarith [norm_nonneg (N (base N x)),
    norm_nonneg (hilbertAdjoint N (base (hilbertAdjoint N) y))]

theorem normal_domain_norm
    (hn : OperatorDomainsSpec.productValue (HilbertAdjointSpec.adjointValue N) N =
      OperatorDomainsSpec.productValue N (HilbertAdjointSpec.adjointValue N)) :
    N.domain = (hilbertAdjoint N).domain ∧
      ∀ (x : N.domain) (y : (hilbertAdjoint N).domain),
        (x : H) = (y : H) → ‖N x‖ = ‖hilbertAdjoint N y‖ := by
  have hda : DenselyDefined (hilbertAdjoint N) :=
    (isClosable_iff_dense_hilbertAdjoint N hd).mp hc.isClosable
  have hca := hilbertAdjoint_isClosed N hd
  have haa := hilbertAdjoint_hilbertAdjoint_of_closed N hd hc
  have he : adjointProduct N = adjointProduct (hilbertAdjoint N) := by
    change OperatorDomainsSpec.productValue (hilbertAdjoint N) N =
      OperatorDomainsSpec.productValue (hilbertAdjoint (hilbertAdjoint N)) (hilbertAdjoint N)
    rw [haa]
    exact hn
  have hle : N.domain ≤ (hilbertAdjoint N).domain := by
    let D := (adjointProduct N).domain
    have hDT : D ≤ (hilbertAdjoint N).domain :=
      fun x hx => (base (hilbertAdjoint N) ⟨x, (le_of_eq he).1 hx⟩).property
    intro x hx
    obtain ⟨y, hy, _⟩ := norm_extension_from_core N (hilbertAdjoint N) D
      (graph_core N hd hc) hDT hca
      (fun d => normal_product_norm N hd hc he d ⟨d, (le_of_eq he).1 d.property⟩ rfl) ⟨x, hx⟩
    change (y : H) = x at hy
    exact hy ▸ y.property
  have hge : (hilbertAdjoint N).domain ≤ N.domain := by
    let D := (adjointProduct (hilbertAdjoint N)).domain
    have hDT : D ≤ N.domain :=
      fun x hx => (base N ⟨x, (le_of_eq he.symm).1 hx⟩).property
    intro x hx
    obtain ⟨y, hy, _⟩ := norm_extension_from_core (hilbertAdjoint N) N D
      (graph_core (hilbertAdjoint N) hda hca) hDT hc
      (fun d => (normal_product_norm N hd hc he ⟨d, (le_of_eq he.symm).1 d.property⟩ d rfl).symm)
      ⟨x, hx⟩
    change (y : H) = x at hy
    exact hy ▸ y.property
  refine ⟨le_antisymm hle hge, ?_⟩
  intro x y hxy
  let D := (adjointProduct N).domain
  have hDT : D ≤ (hilbertAdjoint N).domain :=
    fun x hx => (base (hilbertAdjoint N) ⟨x, (le_of_eq he).1 hx⟩).property
  obtain ⟨z, hz, hnorm⟩ := norm_extension_from_core N (hilbertAdjoint N) D
    (graph_core N hd hc) hDT hca
    (fun d => normal_product_norm N hd hc he d ⟨d, (le_of_eq he).1 d.property⟩ rfl) x
  have hzy : z = y := Subtype.ext (hz.trans hxy)
  simpa only [hzy] using hnorm.symm
end Normal

/-- Full independently specified source conclusions. -/
theorem shift_surjectivity : PositiveAdjointProductSpec.ShiftSurjective := by
  intro 𝕜 H K _ _ _ _ _ _ _ A hd hc
  exact shifted_surjective A hd hc

theorem product_properties : PositiveAdjointProductSpec.ProductProperties := by
  intro 𝕜 H K _ _ _ _ _ _ _ A hd hc
  exact ⟨product_dense A hd hc, product_selfAdjoint A hd hc, product_nonnegative A hd⟩

theorem inverse_properties : PositiveAdjointProductSpec.InverseProperties := by
  intro 𝕜 H K _ _ _ _ _ _ _ A hd hc
  exact ⟨inverse A hd hc, inverse_right A hd hc, inverse_left A hd hc,
    inverse_injective A hd hc, inverse_selfAdjoint A hd hc, inverse_contract A hd hc,
    inverse_nonnegative A hd hc⟩

theorem graph_core_property : PositiveAdjointProductSpec.GraphCore := by
  intro 𝕜 H K _ _ _ _ _ _ _ A hd hc
  exact graph_core A hd hc

theorem normal_domain_norm_property : PositiveAdjointProductSpec.NormalDomainNorm := by
  intro 𝕜 H _ _ _ _ N hd hc hn
  exact normal_domain_norm N hd hc hn

end ExpandedFA.Unbounded.PositiveAdjointProduct
