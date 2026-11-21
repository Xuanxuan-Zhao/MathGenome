import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.NormalBoundedSpectralPieces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.PositiveAdjointProduct
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.NormalSpectral
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.InnerProductSpace.StarOrder

noncomputable section
open scoped InnerProductSpace
namespace ExpandedFA.Unbounded.NormalBoundedSpectralPieces
open PositiveAdjointProductSpec PositiveAdjointProduct
open OperatorDomainsSpec HilbertAdjointSpec
variable {𝕜 H K : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- The inverse takes its values in the exact product domain. -/
def inverseToProduct (A : Operator 𝕜 H K) (hd : DenselyDefined A) (hc : A.IsClosed) :
    H →ₗ[𝕜] (adjointProduct A).domain := (shiftedEquiv A hd hc).symm.toLinearMap

def inverseToDomain (A : Operator 𝕜 H K) (hd : DenselyDefined A) (hc : A.IsClosed) :
    H →ₗ[𝕜] A.domain :=
  (inverse A hd hc).toLinearMap.codRestrict A.domain
    (fun f => (base A (inverseToProduct A hd hc f)).property)

theorem transform_bound (A : Operator 𝕜 H K) (hd : DenselyDefined A)
    (hc : A.IsClosed) (f : H) : ‖A (inverseToDomain A hd hc f)‖ ≤ ‖f‖ := by
  let u := inverseToProduct A hd hc f
  have hu : (u : H) + adjointProduct A u = f :=
    (shiftedEquiv A hd hc).apply_symm_apply f
  have hid : ‖A (base A u)‖ ^ 2 + ‖(u : H)‖ ^ 2 =
      RCLike.re (inner 𝕜 (u : H) f) := by
    rw [← hu, inner_add_right, map_add, ← norm_sq_eq_re_inner,
      product_inner A hd u (base A u), ← norm_sq_eq_re_inner]
    exact add_comm _ _
  have hub : ‖(u : H)‖ ≤ ‖f‖ := by
    have hh := shiftedMap_bound A hd u
    change ‖(u : H)‖ ≤ ‖(u : H) + adjointProduct A u‖ at hh
    rwa [hu] at hh
  have hib := re_inner_le_norm (𝕜 := 𝕜) (u : H) f
  have hb := mul_le_mul_of_nonneg_right hub (norm_nonneg f)
  change ‖A (base A u)‖ ≤ ‖f‖
  nlinarith [sq_nonneg ‖(u : H)‖, norm_nonneg (A (base A u)), norm_nonneg f]

/-- NB is bounded before any spectral theorem for N has been used. -/
def boundedTransform (A : Operator 𝕜 H K) (hd : DenselyDefined A) (hc : A.IsClosed) :
    H →L[𝕜] K :=
  (A.toFun.comp (inverseToDomain A hd hc)).mkContinuous 1 (by
    intro f
    simpa using transform_bound A hd hc f)

theorem boundedTransform_apply (A : Operator 𝕜 H K) (hd : DenselyDefined A)
    (hc : A.IsClosed) (f : H) :
    boundedTransform A hd hc f = A (inverseToDomain A hd hc f) := rfl

section Normal
variable (N : Operator 𝕜 H H) (hd : DenselyDefined N) (hc : N.IsClosed)
  (hn : productValue (adjointValue N) N = productValue N (adjointValue N))
include hn

/-- This calculation keeps the intermediate vector in D(NN*) before
transferring it through the exact product equality. -/
theorem inverse_commutes_on_domain (x : N.domain) :
    N (inverseToDomain N hd hc x) = inverse N hd hc (N x) := by
  let u := inverseToProduct N hd hc (x : H)
  let v : (hilbertAdjoint N).domain := image N u
  have hu : (u : H) + adjointProduct N u = (x : H) :=
    (shiftedEquiv N hd hc).apply_symm_apply x
  have hv : hilbertAdjoint N v = (x : H) - (u : H) :=
    eq_sub_of_add_eq' hu
  have hvm : hilbertAdjoint N v ∈ N.domain := by
    rw [hv]
    exact N.domain.sub_mem x.property (base N u).property
  let q : (productValue N (hilbertAdjoint N)).domain := ⟨v, v.property, hvm⟩
  let p : (adjointProduct N).domain := ⟨v, (le_of_eq hn.symm).1 q.property⟩
  have hpq : adjointProduct N p = N ⟨hilbertAdjoint N v, hvm⟩ :=
    (le_of_eq hn).2 (show (p : H) = (q : H) from rfl)
  have heval : N ⟨hilbertAdjoint N v, hvm⟩ = N x - N (base N u) := by
    rw [← N.map_sub]
    exact congrArg N (Subtype.ext hv)
  have hshift : (p : H) + adjointProduct N p = N x := by
    rw [hpq, heval]
    change N (base N u) + (N x - N (base N u)) = N x
    rw [add_comm, sub_add_cancel]
  have hi := inverse_left N hd hc p
  rw [hshift] at hi
  exact hi.symm

theorem inverse_commutes_transform :
    Commute (inverse N hd hc) (boundedTransform N hd hc) := by
  change (inverse N hd hc) * (boundedTransform N hd hc) =
    (boundedTransform N hd hc) * (inverse N hd hc)
  apply ContinuousLinearMap.ext
  intro f
  exact (inverse_commutes_on_domain N hd hc hn (inverseToDomain N hd hc f)).symm

/-- Equality with N*B follows by testing on the dense original domain;
there is no unproved interchange of unbounded products. -/
theorem adjoint_transform (f : H) :
    ∃ hf : inverse N hd hc f ∈ (hilbertAdjoint N).domain,
      (boundedTransform N hd hc).adjoint f =
        hilbertAdjoint N ⟨inverse N hd hc f, hf⟩ := by
  have htest : ∀ x : N.domain,
      inner 𝕜 (N x) (inverse N hd hc f) =
        inner 𝕜 (x : H) ((boundedTransform N hd hc).adjoint f) := by
    intro x
    rw [← inverse_symmetric N hd hc,
      ← inverse_commutes_on_domain N hd hc hn x]
    exact (ContinuousLinearMap.adjoint_inner_right (boundedTransform N hd hc) _ _).symm
  have hf := (mem_hilbertAdjoint_domain_iff N hd _).mpr ⟨_, htest⟩
  exact ⟨hf, (hilbertAdjoint_apply_eq N hd ⟨_, hf⟩ _ htest).symm⟩

theorem inverse_commutes_on_adjoint_domain (x : (hilbertAdjoint N).domain) :
    ∃ hx : inverse N hd hc x ∈ (hilbertAdjoint N).domain,
      hilbertAdjoint N ⟨inverse N hd hc x, hx⟩ =
        inverse N hd hc (hilbertAdjoint N x) := by
  obtain ⟨hx, hval⟩ := adjoint_transform N hd hc hn (x : H)
  refine ⟨hx, hval.symm.trans ?_⟩
  apply ext_inner_left 𝕜
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right, ← inverse_symmetric N hd hc]
  exact hilbertAdjoint_inner N hd x (inverseToDomain N hd hc f)

theorem boundedTransform_normal : IsStarNormal (boundedTransform N hd hc) := by
  apply ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mpr
  intro f
  obtain ⟨hf, hval⟩ := adjoint_transform N hd hc hn f
  rw [hval]
  exact (normal_domain_norm N hd hc hn).2 (inverseToDomain N hd hc f) ⟨_, hf⟩ rfl

end Normal

theorem bounded_transforms : NormalBoundedSpectralPiecesSpec.BoundedTransforms := by
  intro G _ _ _ N hd hc hn
  refine ⟨inverse N hd hc, boundedTransform N hd hc, ?_⟩
  exact {
    inverse_right := inverse_right N hd hc
    inverse_left := inverse_left N hd hc
    injective := inverse_injective N hd hc
    selfAdjoint := inverse_selfAdjoint N hd hc
    contractive := inverse_contract N hd hc
    nonnegative := inverse_nonnegative N hd hc
    transform := fun f => ⟨(inverseToDomain N hd hc f).property, rfl⟩
    adjoint_transform := adjoint_transform N hd hc hn
    commute_domain := fun x => ⟨(inverseToDomain N hd hc x).property,
      inverse_commutes_on_domain N hd hc hn x⟩
    commute_adjoint_domain := inverse_commutes_on_adjoint_domain N hd hc hn
    commute := inverse_commutes_transform N hd hc hn
    normal := boundedTransform_normal N hd hc hn }

/-- Closedness identifies the graph from convergent sums of component
graphs. This lemma does not assume a spectral representation of N. -/
theorem graph_of_component_sums
    (N : Operator 𝕜 H K) (hc : N.IsClosed)
    (q : ℕ → H) (r : ℕ → K) (x : H) (y : K)
    (hq : ∀ n, q n ∈ N.domain)
    (hr : ∀ n, N ⟨q n, hq n⟩ = r n)
    (hsx : HasSum q x) (hsy : HasSum r y) : (x, y) ∈ N.graph := by
  let d (s : Finset ℕ) : N.domain := ∑ n ∈ s, ⟨q n, hq n⟩
  have hd (s : Finset ℕ) : ((d s : H), N (d s)) ∈ N.graph := N.mem_graph (d s)
  have hdx (s : Finset ℕ) : (d s : H) = ∑ n ∈ s, q n := by
    simp [d]
  have hdy (s : Finset ℕ) : N (d s) = ∑ n ∈ s, r n := by
    change N.toFun (∑ n ∈ s, ⟨q n, hq n⟩) = _
    simp only [map_sum]
    exact Finset.sum_congr rfl (fun n _ => hr n)
  apply hc.mem_of_tendsto (hsx.prodMk_nhds hsy)
  exact Filter.Eventually.of_forall (fun s =>
    N.mem_graph_iff.mpr ⟨d s, hdx s, hdy s⟩)

/-- Orthogonal reducing components determine both the square-summability
domain and the graph of the original operator. The hypotheses are the local
restriction identities that the spectral cutoffs will supply. -/
theorem orthogonal_sum_domain_graph
    (N : Operator 𝕜 H H) (hc : N.IsClosed)
    (D : ℕ → Submodule 𝕜 H)
    (horth : OrthogonalFamily 𝕜 (fun n => D n) (fun n => (D n).subtypeₗᵢ))
    (hD : ∀ n, D n ≤ N.domain)
    (Q : ∀ n, H →L[𝕜] D n) (T : ∀ n, D n →L[𝕜] D n)
    (hsum : ∀ x : H, HasSum (fun n => (Q n x : H)) x)
    (heval : ∀ n x, (T n (Q n x) : H) = N ⟨Q n x, hD n (Q n x).property⟩)
    (hreduce : ∀ n (x : N.domain), (T n (Q n x) : H) = (Q n (N x) : H)) :
    (∀ x : H, x ∈ N.domain ↔ Summable (fun n => ‖T n (Q n x)‖ ^ 2)) ∧
    (∀ x y : H, (x, y) ∈ N.graph ↔
      Summable (fun n => ‖T n (Q n x)‖ ^ 2) ∧
        HasSum (fun n => (T n (Q n x) : H)) y) := by
  have hcrit (x : H) : Summable (fun n => (T n (Q n x) : H)) ↔
      Summable (fun n => ‖T n (Q n x)‖ ^ 2) :=
    horth.summable_iff_norm_sq_summable (fun n => T n (Q n x))
  have hNsum (x : N.domain) : HasSum (fun n => (T n (Q n x) : H)) (N x) := by
    simpa only [hreduce] using hsum (N x)
  have hgraph (x y : H) (hy : HasSum (fun n => (T n (Q n x) : H)) y) :
      (x, y) ∈ N.graph :=
    graph_of_component_sums N hc _ _ x y
      (fun n => hD n (Q n x).property) (fun n => (heval n x).symm) (hsum x) hy
  constructor
  · intro x
    constructor
    · intro hx
      exact (hcrit x).mp (hNsum ⟨x, hx⟩).summable
    · intro hx
      obtain ⟨y, hy⟩ := (hcrit x).mpr hx
      obtain ⟨z, hz, _⟩ := N.mem_graph_iff.mp (hgraph x y hy)
      change (z : H) = x at hz
      exact hz ▸ z.property
  · intro x y
    constructor
    · intro hxy
      obtain ⟨z, hz, hNz⟩ := N.mem_graph_iff.mp hxy
      have hs := hNsum z
      rw [hz, hNz] at hs
      exact ⟨(hcrit x).mp hs.summable, hs⟩
    · rintro ⟨_, hy⟩
      exact hgraph x y hy

section Complex
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
open SpectralMeasure
open NormalBoundedSpectralPiecesSpec

/-- Commutation on a graph core extends through the closed graph. -/
theorem commutes_from_core (N : Operator ℂ G G) (hc : N.IsClosed)
    (D : Submodule ℂ G) (hcore : coreValue N D) (Q : G →L[ℂ] G)
    (hQ : ∀ d : D,
      (Q d, Q (N ⟨d, hcore.1 d.property⟩)) ∈ N.graph) :
    ∀ x : N.domain, ∃ hx : Q x ∈ N.domain, N ⟨Q x, hx⟩ = Q (N x) := by
  intro x
  have hm : ((x : G), N x) ∈ (N.domRestrict D).graph.topologicalClosure := by
    rw [hcore.2]
    exact N.graph.le_topologicalClosure (N.mem_graph x)
  obtain ⟨p, hp, hlim⟩ := mem_closure_iff_seq_limit.mp hm
  have hgraphs (n : ℕ) : (Q (p n).1, Q (p n).2) ∈ N.graph := by
    obtain ⟨z, hz, hNz⟩ := (N.domRestrict D).mem_graph_iff.mp (hp n)
    have he : N ⟨z, hcore.1 z.property.1⟩ = (p n).2 := hNz
    rw [← hz, ← he]
    exact hQ ⟨z, z.property.1⟩
  have hg : (Q x, Q (N x)) ∈ N.graph :=
    hc.mem_of_tendsto ((Q.continuous.tendsto _ |>.comp hlim.fst_nhds).prodMk_nhds
      (Q.continuous.tendsto _ |>.comp hlim.snd_nhds))
      (Filter.Eventually.of_forall hgraphs)
  obtain ⟨y, hy, hNy⟩ := N.mem_graph_iff.mp hg
  change (y : G) = Q x at hy
  have hm : Q x ∈ N.domain := hy ▸ y.property
  refine ⟨hm, ?_⟩
  have he : (⟨Q x, hm⟩ : N.domain) = y := Subtype.ext hy.symm
  rw [he]
  exact hNy

/-- A bounded operator commuting with both bounded transforms preserves the
entire domain of N. The inverse range is the graph core used in this step. -/
theorem commutes_of_transforms (N : Operator ℂ G G)
    (hd : DenselyDefined N) (hc : N.IsClosed) (B C Q : G →L[ℂ] G)
    (h : TransformLaws N B C) (hQB : Commute Q B) (hQC : Commute Q C) :
    ∀ x : N.domain, ∃ hx : Q x ∈ N.domain, N ⟨Q x, hx⟩ = Q (N x) := by
  apply commutes_from_core N hc (adjointProduct N).domain (graph_core N hd hc) Q
  intro d
  let f := (d : G) + adjointProduct N d
  have hBf : B f = (d : G) := h.inverse_left d
  obtain ⟨hdf, hCd⟩ := h.transform f
  obtain ⟨hQf, hCQ⟩ := h.transform (Q f)
  have hQBf : B (Q f) = Q d := by
    have he := congrArg (fun T : G →L[ℂ] G => T f) hQB.eq
    change Q (B f) = B (Q f) at he
    exact (by rwa [hBf] at he : Q d = B (Q f)).symm
  have hQCf : C (Q f) = Q (C f) := by
    exact (congrArg (fun T : G →L[ℂ] G => T f) hQC.eq).symm
  have hdval : C f = N ⟨d, (graph_core N hd hc).1 d.property⟩ := by
    exact hCd.trans (congrArg N (Subtype.ext hBf))
  exact N.mem_graph_iff.mpr ⟨⟨B (Q f), hQf⟩, hQBf,
    hCQ.symm.trans (hQCf.trans (congrArg Q hdval))⟩

/-- For a bounded self-adjoint map, domain-sensitive commutation with N
implies the corresponding commutation with its Hilbert adjoint. -/
theorem commutes_adjoint_of_selfAdjoint (N : Operator ℂ G G)
    (hd : DenselyDefined N) (Q : G →L[ℂ] G) (hQ : Q.adjoint = Q)
    (hcomm : ∀ x : N.domain, ∃ hx : Q x ∈ N.domain,
      N ⟨Q x, hx⟩ = Q (N x)) :
    ∀ x : (hilbertAdjoint N).domain,
      ∃ hx : Q x ∈ (hilbertAdjoint N).domain,
        hilbertAdjoint N ⟨Q x, hx⟩ = Q (hilbertAdjoint N x) := by
  have hs (a b : G) : inner ℂ (Q a) b = inner ℂ a (Q b) := by
    simpa only [hQ] using ContinuousLinearMap.adjoint_inner_left Q b a
  intro x
  have htest (y : N.domain) : inner ℂ (N y) (Q x) =
      inner ℂ (y : G) (Q (hilbertAdjoint N x)) := by
    obtain ⟨hy, hNy⟩ := hcomm y
    rw [← hs, ← hNy, hilbertAdjoint_inner N hd x ⟨Q y, hy⟩]
    exact hs y (hilbertAdjoint N x)
  have hx := (mem_hilbertAdjoint_domain_iff N hd _).mpr ⟨_, htest⟩
  exact ⟨hx, hilbertAdjoint_apply_eq N hd ⟨Q x, hx⟩ _ htest⟩

/-- The bounded spectral theorem is applied only to the positive inverse.
Its commutant clause gives commutation with C on every Borel set. -/
theorem inverse_spectral_resolution (N : Operator ℂ G G) (B C : G →L[ℂ] G)
    (h : TransformLaws N B C) :
    ∃ P : ProjectionValuedMeasure (spectrum ℂ B) G,
      NormalPVM.Spec.Resolves B P ∧
      ∀ S, MeasurableSet S → Commute C (P S) := by
  have hBself : IsSelfAdjoint B := by
    change B.adjoint = B
    exact h.selfAdjoint
  have hBn : IsStarNormal B := hBself.isStarNormal
  obtain ⟨P, Φ, hP, _, _, _, _, _, hcomm⟩ :=
    SpectralMeasure.NormalSpectral.normal_spectral_theorem G B hBn
  refine ⟨P, hP, ?_⟩
  apply hcomm C h.commute.symm
  simpa only [show star B = B from hBself] using h.commute.symm

/-- Every spectral projection of B reduces the original partial operator,
including its entire domain and the entire adjoint domain. -/
theorem spectral_projection_reduces (N : Operator ℂ G G)
    (hd : DenselyDefined N) (hc : N.IsClosed) (B C : G →L[ℂ] G)
    (h : TransformLaws N B C) (P : ProjectionValuedMeasure (spectrum ℂ B) G)
    (hP : NormalPVM.Spec.Resolves B P) (S : Set (spectrum ℂ B))
    (hS : MeasurableSet S) :
    (∀ x : N.domain, ∃ hx : P S x ∈ N.domain,
      N ⟨P S x, hx⟩ = P S (N x)) ∧
    (∀ x : (adjointValue N).domain, ∃ hx : P S x ∈ (adjointValue N).domain,
      adjointValue N ⟨P S x, hx⟩ = P S (adjointValue N x)) := by
  have hBself : IsSelfAdjoint B := h.selfAdjoint
  have hBstar : Commute B (star B) := by
    rw [show star B = B from hBself]
  have hCBstar : Commute C (star B) := by
    simpa only [show star B = B from hBself] using h.commute.symm
  have hQB : Commute (P S) B :=
    (SpectralMeasure.NormalSpectral.spectral_commutation hBself.isStarNormal P hP
      B (Commute.refl B) hBstar S hS).symm
  have hQC : Commute (P S) C :=
    (SpectralMeasure.NormalSpectral.spectral_commutation hBself.isStarNormal P hP
      C h.commute.symm hCBstar S hS).symm
  have hred := commutes_of_transforms N hd hc B C (P S) h hQB hQC
  refine ⟨hred, commutes_adjoint_of_selfAdjoint N hd (P S) ?_ hred⟩
  exact P.selfAdjoint S hS

/-- A bounded estimate on a reducing projection range produces the actual
normal restriction, with its adjoint evaluated on that same range. -/
theorem reducingPiece_of_bound (N : Operator ℂ G G)
    (hd : DenselyDefined N) (hc : N.IsClosed)
    (hn : productValue (adjointValue N) N = productValue N (adjointValue N))
    (Q : G →L[ℂ] G) (hQ : Q * Q = Q)
    (hD : Q.range ≤ N.domain)
    (hred : ∀ x : N.domain, ∃ hx : Q x ∈ N.domain,
      N ⟨Q x, hx⟩ = Q (N x))
    (hredA : ∀ x : (adjointValue N).domain, ∃ hx : Q x ∈ (adjointValue N).domain,
      adjointValue N ⟨Q x, hx⟩ = Q (adjointValue N x))
    (r : ℝ) (hr : 0 ≤ r)
    (hb : ∀ x : Q.range, ‖N ⟨x, hD x.property⟩‖ ≤ r * ‖x‖) :
    Nonempty (ReducingPiece N Q r) := by
  have hclosed : _root_.IsClosed (Q.range : Set G) :=
    ContinuousLinearMap.IsIdempotentElem.isClosed_range hQ
  letI : CompleteSpace Q.range := hclosed.isComplete.completeSpace_coe
  have hfix (x : Q.range) : Q x = (x : G) := by
    obtain ⟨y, hy⟩ := x.property
    rw [← hy]
    exact congrArg (fun A : G →L[ℂ] G => A y) hQ
  have hnorm := normal_domain_norm N hd hc hn
  have hDA : Q.range ≤ (adjointValue N).domain := fun x hx => hnorm.1 ▸ hD hx
  have hmaps (x : Q.range) : N ⟨x, hD x.property⟩ ∈ Q.range := by
    obtain ⟨hx, he⟩ := hred ⟨x, hD x.property⟩
    exact ⟨N ⟨x, hD x.property⟩, he.symm.trans
      (congrArg N (Subtype.ext (hfix x)))⟩
  let L : Q.range →ₗ[ℂ] Q.range :=
    (N.toFun.comp (Q.range.inclusion hD)).codRestrict Q.range hmaps
  let T : Q.range →L[ℂ] Q.range := L.mkContinuous r hb
  have hTeval (x : Q.range) : (T x : G) = N ⟨x, hD x.property⟩ := rfl
  have hmapsA (x : Q.range) : adjointValue N ⟨x, hDA x.property⟩ ∈ Q.range := by
    obtain ⟨hx, he⟩ := hredA ⟨x, hDA x.property⟩
    exact ⟨adjointValue N ⟨x, hDA x.property⟩, he.symm.trans
      (congrArg (adjointValue N) (Subtype.ext (hfix x)))⟩
  have hAeval (x : Q.range) :
      (T.adjoint x : G) = adjointValue N ⟨x, hDA x.property⟩ := by
    have he : T.adjoint x =
        (⟨adjointValue N ⟨x, hDA x.property⟩, hmapsA x⟩ : Q.range) := by
      apply ext_inner_left ℂ
      intro y
      rw [ContinuousLinearMap.adjoint_inner_right]
      change inner ℂ (T y : G) (x : G) =
        inner ℂ (y : G) (adjointValue N ⟨x, hDA x.property⟩)
      rw [hTeval]
      exact hilbertAdjoint_inner N hd ⟨x, hDA x.property⟩ ⟨y, hD y.property⟩
    exact congrArg Subtype.val he
  refine ⟨⟨hclosed, T, hD, hDA, hTeval, hAeval, ?_,
    T.opNorm_le_bound hr hb, hred, hredA⟩⟩
  apply ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mpr
  intro x
  change ‖(T x : G)‖ = ‖(T.adjoint x : G)‖
  rw [hTeval, hAeval]
  exact hnorm.2 ⟨x, hD x.property⟩ ⟨x, hDA x.property⟩ rfl

/-- Positivity here is derived from the quadratic form law, rather than
silently assuming a spectral positivity certificate. -/
theorem inverse_spectrum_bounds (N : Operator ℂ G G) (B C : G →L[ℂ] G)
    (h : TransformLaws N B C) (z : spectrum ℂ B) :
    (z : ℂ) = ((z : ℂ).re : ℂ) ∧ 0 ≤ (z : ℂ).re ∧ (z : ℂ).re ≤ 1 := by
  have hs : IsSelfAdjoint B := h.selfAdjoint
  have hp : B.IsPositive := by
    apply (ContinuousLinearMap.isPositive_iff_complex B).mpr
    intro x
    have he := (LinearMap.isSymmetric_iff_inner_map_self_real B.toLinearMap).mp
      hs.isSymmetric x
    refine ⟨RCLike.conj_eq_iff_re.mp he, ?_⟩
    change 0 ≤ (inner ℂ (B x) x).re
    have hh : inner ℂ (B x) x = inner ℂ x (B x) := hs.isSymmetric x x
    rw [hh]
    exact h.nonnegative x
  have hzreal := hs.mem_spectrum_eq_re z.property
  have hzpos : 0 ≤ (z : ℂ).re :=
    (SpectrumRestricts.nnreal_iff.mp hp.spectrumRestricts) _
      (hs.spectrumRestricts.apply_mem z.property)
  have hznorm : ‖(z : ℂ)‖ ≤ 1 := by
    calc
      ‖(z : ℂ)‖ ≤ ‖B‖ * ‖(1 : G →L[ℂ] G)‖ :=
        spectrum.norm_le_norm_mul_of_mem z.property
      _ ≤ 1 * 1 := mul_le_mul h.contractive (ContinuousLinearMap.norm_id_le)
        (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  exact ⟨hzreal, hzpos, (Complex.re_le_norm _).trans hznorm⟩

/-- The energy identity for the inverse of the positive adjoint product. -/
theorem transform_energy (N : Operator ℂ G G) (hd : DenselyDefined N)
    (B C : G →L[ℂ] G) (h : TransformLaws N B C) (f : G) :
    ‖C f‖ ^ 2 + ‖B f‖ ^ 2 = (inner ℂ (B f) f).re := by
  obtain ⟨hx, hshift⟩ := h.inverse_right f
  obtain ⟨hf, hCf⟩ := h.transform f
  rw [hCf]
  calc
    ‖N ⟨B f, hf⟩‖ ^ 2 + ‖B f‖ ^ 2 =
        (inner ℂ (B f) (B f + adjointProduct N ⟨B f, hx⟩)).re := by
      change _ = RCLike.re (inner ℂ (B f) (B f + adjointProduct N ⟨B f, hx⟩))
      rw [inner_add_right, map_add, ← norm_sq_eq_re_inner,
        product_inner N hd ⟨B f, hx⟩ ⟨B f, hf⟩, ← norm_sq_eq_re_inner]
      exact add_comm _ _
    _ = (inner ℂ (B f) f).re := congrArg (fun y => (inner ℂ (B f) y).re) hshift

/-- Inverting the coordinate on a Borel set away from zero. -/
theorem spectral_local_inverse (N : Operator ℂ G G) (B C : G →L[ℂ] G)
    (_h : TransformLaws N B C) (P : ProjectionValuedMeasure (spectrum ℂ B) G)
    (hP : NormalPVM.Spec.Resolves B P) (S : Set (spectrum ℂ B))
    (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ)
    (hbound : ∀ z ∈ S, δ ≤ (z : ℂ).re) :
    ∃ D : G →L[ℂ] G, B * D = P S ∧ ‖D‖ ≤ δ⁻¹ := by
  classical
  let f : spectrum ℂ B → ℂ := fun z => (z : ℂ)
  have hf : SpectralMeasure.Spec.IsBoundedMeasurable f :=
    NormalPVM.continuous_bounded ((ContinuousMap.id ℂ).restrict (spectrum ℂ B))
  let g := S.indicator (fun z => (f z)⁻¹)
  have hgBound (z) : ‖g z‖ ≤ δ⁻¹ := by
    by_cases hz : z ∈ S
    · simp only [g, Set.indicator_of_mem hz, norm_inv]
      exact inv_anti₀ hδ ((hbound z hz).trans (Complex.re_le_norm _))
    · simp [g, hz, le_of_lt (inv_pos.mpr hδ)]
  have hg : SpectralMeasure.Spec.IsBoundedMeasurable g :=
    ⟨hf.1.inv.indicator hS, δ⁻¹, hgBound⟩
  have hfg : f * g = S.indicator (fun _ => 1) := by
    funext z
    by_cases hz : z ∈ S
    · have hnz : f z ≠ 0 := by
        intro he
        have hh := hbound z hz
        change δ ≤ (f z).re at hh
        rw [he] at hh
        exact (not_le_of_gt hδ) hh
      simp [g, hz, hnz]
    · simp [g, hz]
  refine ⟨P.spectralIntegral g, ?_, P.spectralIntegral_norm_le g hg δ⁻¹
    (le_of_lt (inv_pos.mpr hδ)) hgBound⟩
  have hcoord : P.spectralIntegral f = B := NormalPVM.continuousIntegral_coordinate P hP
  calc
    B * P.spectralIntegral g = P.spectralIntegral f * P.spectralIntegral g :=
      congrArg (fun A : G →L[ℂ] G => A * P.spectralIntegral g) hcoord.symm
    _ = P S := by rw [← P.spectralIntegral_mul f g hf hg, hfg,
      BorelNormSpectrum.integral_indicator_one P S hS]

/-- Every spectral range bounded away from zero is an everywhere defined
reducing normal restriction, with the sharp inverse-energy estimate. -/
theorem spectral_reducing_piece (N : Operator ℂ G G)
    (hd : DenselyDefined N) (hc : N.IsClosed)
    (hn : productValue (adjointValue N) N = productValue N (adjointValue N))
    (B C : G →L[ℂ] G) (h : TransformLaws N B C)
    (P : ProjectionValuedMeasure (spectrum ℂ B) G) (hP : NormalPVM.Spec.Resolves B P)
    (S : Set (spectrum ℂ B)) (hS : MeasurableSet S)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hbound : ∀ z ∈ S, δ ≤ (z : ℂ).re) :
    Nonempty (ReducingPiece N (P S) (Real.sqrt ((1 - δ) / δ))) := by
  obtain ⟨D, hBD, hDb⟩ := spectral_local_inverse N B C h P hP S hS δ hδ hbound
  have hfix (x : (P S).range) : P S x = (x : G) := by
    obtain ⟨y, hy⟩ := x.property
    rw [← hy]
    exact congrArg (fun A : G →L[ℂ] G => A y) (P.idempotent S hS)
  have hBDx (x : (P S).range) : B (D x) = (x : G) := by
    exact (congrArg (fun A : G →L[ℂ] G => A x) hBD).trans (hfix x)
  have hD : (P S).range ≤ N.domain := by
    intro x hx
    obtain ⟨hf, _⟩ := h.transform (D x)
    have hh : B (D x) = x := hBDx ⟨x, hx⟩
    rwa [hh] at hf
  obtain ⟨hred, hredA⟩ := spectral_projection_reduces N hd hc B C h P hP S hS
  apply reducingPiece_of_bound N hd hc hn (P S) (P.idempotent S hS) hD hred hredA
    _ (Real.sqrt_nonneg _)
  intro x
  have hCeval : C (D x) = N ⟨x, hD x.property⟩ := by
    obtain ⟨hf, he⟩ := h.transform (D x)
    exact he.trans (congrArg N (Subtype.ext (hBDx x)))
  have he := transform_energy N hd B C h (D x)
  rw [hCeval, hBDx] at he
  have hi := re_inner_le_norm (𝕜 := ℂ) (x : G) (D x)
  change (inner ℂ (x : G) (D x)).re ≤ ‖(x : G)‖ * ‖D x‖ at hi
  have hDx : ‖D x‖ ≤ δ⁻¹ * ‖(x : G)‖ :=
    (D.le_opNorm _).trans (mul_le_mul_of_nonneg_right hDb (norm_nonneg _))
  have hcst : δ⁻¹ - 1 = (1 - δ) / δ := by field_simp
  have hsqrt : Real.sqrt ((1 - δ) / δ) ^ 2 = δ⁻¹ - 1 := by
    rw [hcst, Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hδ1) hδ.le)]
  have hsq : ‖N ⟨x, hD x.property⟩‖ ^ 2 ≤
      (Real.sqrt ((1 - δ) / δ) * ‖(x : G)‖) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hDx (norm_nonneg (x : G))
    rw [mul_pow, hsqrt]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hsq

theorem measurable_cutoff (B : G →L[ℂ] G) (δ : ℝ) :
    MeasurableSet (cutoff B δ) :=
  (measurableSet_le measurable_const
    (Complex.measurable_re.comp measurable_subtype_coe)).inter
    (measurableSet_le (Complex.measurable_re.comp measurable_subtype_coe) measurable_const)

theorem measurable_band (B : G →L[ℂ] G) (n : ℕ) :
    MeasurableSet (band B n) :=
  (measurableSet_lt measurable_const
    (Complex.measurable_re.comp measurable_subtype_coe)).inter
    (measurableSet_le (Complex.measurable_re.comp measurable_subtype_coe) measurable_const)

/-- The reciprocal intervals partition (0,1], with no condition on the
cardinality or separability of the underlying Hilbert space. -/
theorem exists_reciprocal_band {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ n : ℕ, 1 / ((n : ℝ) + 2) < t ∧ t ≤ 1 / ((n : ℝ) + 1) := by
  classical
  have hex : ∃ n : ℕ, 1 / ((n : ℝ) + 2) < t := by
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht
    refine ⟨n, lt_of_le_of_lt ?_ hn⟩
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  let n := Nat.find hex
  refine ⟨n, Nat.find_spec hex, ?_⟩
  cases hn : n with
  | zero => simpa [hn] using ht1
  | succ k =>
    have hh : ¬ 1 / ((k : ℝ) + 2) < t := Nat.find_min hex (by omega)
    simpa only [hn, Nat.cast_succ, add_assoc, one_add_one_eq_two] using le_of_not_gt hh

theorem bands_disjoint (B : G →L[ℂ] G) :
    Pairwise (fun n m => Disjoint (band B n) (band B m)) := by
  have hord (i j : ℕ) (hij : i < j) : Disjoint (band B i) (band B j) := by
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    have hcast : (i : ℝ) + 2 ≤ (j : ℝ) + 1 := by exact_mod_cast (by omega : i + 2 ≤ j + 1)
    have hb : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) hcast
    exact (not_lt_of_ge (hzj.2.trans hb)) hzi.1
  intro i j hij
  rcases lt_or_gt_of_ne hij with hh | hh
  · exact hord i j hh
  · exact (hord j i hh).symm

/-- Injectivity removes the spectral atom at zero. -/
theorem spectral_zero_null (N : Operator ℂ G G) (B C : G →L[ℂ] G)
    (h : TransformLaws N B C) (P : ProjectionValuedMeasure (spectrum ℂ B) G)
    (hP : NormalPVM.Spec.Resolves B P) : P {z | (z : ℂ) = 0} = 0 := by
  classical
  let Z : Set (spectrum ℂ B) := {z | (z : ℂ) = 0}
  have hZ : MeasurableSet Z := measurableSet_eq_fun measurable_subtype_coe measurable_const
  let f : spectrum ℂ B → ℂ := fun z => (z : ℂ)
  have hf : SpectralMeasure.Spec.IsBoundedMeasurable f :=
    NormalPVM.continuous_bounded ((ContinuousMap.id ℂ).restrict (spectrum ℂ B))
  have hcoord : P.spectralIntegral f = B := NormalPVM.continuousIntegral_coordinate P hP
  have hfun : Z.indicator f = (fun _ => 0) := by
    funext z
    by_cases hz : z ∈ Z
    · simp [Set.indicator_of_mem hz, f, (show (z : ℂ) = 0 from hz)]
    · simp [hz]
  have hzprod : B * P Z = 0 := by
    calc
      B * P Z = P.spectralIntegral f * P Z :=
        congrArg (fun A : G →L[ℂ] G => A * P Z) hcoord.symm
      _ = P.spectralIntegral (Z.indicator f) :=
        (BorelNormSpectrum.integral_indicator P Z hZ hf).symm
      _ = 0 := by rw [hfun, BorelNormSpectrum.integral_const]; simp
  ext x
  apply h.injective
  change B (P Z x) = B 0
  simpa using congrArg (fun A : G →L[ℂ] G => A x) hzprod

/-- The band projections add strongly to the identity. Only the atom at
zero is discarded; it is null by injectivity of the bounded inverse. -/
theorem spectral_bands_complete (N : Operator ℂ G G) (B C : G →L[ℂ] G)
    (h : TransformLaws N B C) (P : ProjectionValuedMeasure (spectrum ℂ B) G)
    (hP : NormalPVM.Spec.Resolves B P) (x : G) :
    HasSum (fun n => P (band B n) x) x := by
  classical
  let Z : Set (spectrum ℂ B) := {z | (z : ℂ) = 0}
  have hZ : MeasurableSet Z := measurableSet_eq_fun measurable_subtype_coe measurable_const
  have hcov : (⋃ n, band B n) = Zᶜ := by
    ext z
    obtain ⟨hreal, h0, h1⟩ := inverse_spectrum_bounds N B C h z
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
      intro hz0
      have hzre : (z : ℂ).re = 0 := by rw [show (z : ℂ) = 0 from hz0]; rfl
      exact (not_lt_of_ge (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) + 2)))
        (by simpa [hzre] using hn.1)
    · intro hz
      have hpos : 0 < (z : ℂ).re := by
        apply lt_of_le_of_ne h0
        intro he
        apply hz
        change (z : ℂ) = 0
        rw [hreal, ← he]
        rfl
      obtain ⟨n, hn⟩ := exists_reciprocal_band hpos h1
      exact Set.mem_iUnion.mpr ⟨n, hn⟩
  have hnull : P Z = 0 := spectral_zero_null N B C h P hP
  have hcompl : P Zᶜ = 1 := by
    have hfun : Z.indicator (fun _ => (1 : ℂ)) +
        Zᶜ.indicator (fun _ => (1 : ℂ)) = (fun _ => 1) := by
      funext z
      by_cases hz : z ∈ Z <;> simp [hz]
    have hadd := P.spectralIntegral_add _ _
      (BorelNormSpectrum.bounded_indicator Z hZ (BorelNormSpectrum.bounded_const 1))
      (BorelNormSpectrum.bounded_indicator Zᶜ hZ.compl (BorelNormSpectrum.bounded_const 1))
    rw [hfun, P.spectralIntegral_one,
      BorelNormSpectrum.integral_indicator_one P Z hZ,
      BorelNormSpectrum.integral_indicator_one P Zᶜ hZ.compl, hnull, zero_add] at hadd
    exact hadd.symm
  have hh := P.iUnion (band B) (measurable_band B) (bands_disjoint B) x
  rwa [hcov, hcompl, one_apply_eq_self] at hh

end Complex

open NormalBoundedSpectralPiecesSpec

/-- The bounded normal spectral pieces, including their sharp bounds and
the exact domain and graph of their orthogonal sum. -/
theorem bounded_spectral_pieces :
    NormalBoundedSpectralPiecesSpec.BoundedSpectralPieces := by
  intro G _ _ _ N hd hc hn
  obtain ⟨B, C, h⟩ := bounded_transforms G N hd hc hn
  obtain ⟨P, hP, hCP⟩ := inverse_spectral_resolution N B C h
  refine ⟨B, C, P, h, hP, ?_, hCP, ?_⟩
  · intro δ hδ hδ1
    apply spectral_reducing_piece N hd hc hn B C h P hP (cutoff B δ)
      (measurable_cutoff B δ) δ hδ hδ1
    exact fun _ hz => hz.1
  · classical
    have hp (n : ℕ) : Nonempty (ReducingPiece N (P (NormalBoundedSpectralPiecesSpec.band B n))
        (Real.sqrt ((n : ℝ) + 1))) := by
      have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      have hδ1 : 1 / ((n : ℝ) + 2) ≤ 1 :=
        (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      have he : (1 - 1 / ((n : ℝ) + 2)) / (1 / ((n : ℝ) + 2)) = (n : ℝ) + 1 := by
        field_simp; ring
      have hh := spectral_reducing_piece N hd hc hn B C h P hP
        (NormalBoundedSpectralPiecesSpec.band B n) (measurable_band B n)
        (1 / ((n : ℝ) + 2)) hδ hδ1 (fun _ hz => hz.1.le)
      simpa only [he] using hh
    let p (n : ℕ) := Classical.choice (hp n)
    let D (n : ℕ) := (P (NormalBoundedSpectralPiecesSpec.band B n)).range
    let Q (n : ℕ) : G →L[ℂ] D n :=
      (P (NormalBoundedSpectralPiecesSpec.band B n)).codRestrict (D n) (fun x => ⟨x, rfl⟩)
    let R (n : ℕ) : G →L[ℂ] G := (D n).subtypeL.comp ((p n).T.comp (Q n))
    have horth : ∀ n m, n ≠ m → ∀ x y : G,
        inner ℂ (P (NormalBoundedSpectralPiecesSpec.band B n) x)
          (P (NormalBoundedSpectralPiecesSpec.band B m) y) = 0 := by
      intro n m hnm
      exact P.orthogonality _ _ (measurable_band B n) (measurable_band B m)
        (bands_disjoint B hnm)
    have hfam : OrthogonalFamily ℂ (fun n => D n) (fun n => (D n).subtypeₗᵢ) := by
      intro n m hnm x y
      obtain ⟨a, ha⟩ := x.property
      obtain ⟨b, hb⟩ := y.property
      change inner ℂ (x : G) (y : G) = 0
      rw [← ha, ← hb]
      exact horth n m hnm a b
    have hsum : ∀ x : G, HasSum (fun n => P (NormalBoundedSpectralPiecesSpec.band B n) x) x :=
      spectral_bands_complete N B C h P hP
    have hgraph := orthogonal_sum_domain_graph N hc D hfam (fun n => (p n).domain)
      Q (fun n => (p n).T) hsum (fun n x => (p n).evaluation (Q n x)) (by
        intro n x
        obtain ⟨hx, he⟩ := (p n).reduces x
        exact ((p n).evaluation (Q n x)).trans he)
    refine ⟨R, ?_, horth, hsum, ?_, ?_⟩
    · intro n
      exact ⟨p n, fun _ => rfl⟩
    · intro x
      exact hgraph.1 x
    · intro x y
      exact hgraph.2 x y

end ExpandedFA.Unbounded.NormalBoundedSpectralPieces
