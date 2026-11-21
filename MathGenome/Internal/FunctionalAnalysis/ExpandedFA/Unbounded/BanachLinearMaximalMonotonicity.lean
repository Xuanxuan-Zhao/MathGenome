import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.BanachLinearMaximalMonotonicity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.BanachAdjoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Monotone.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.StrictDualSmoothness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14Minimization
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.LinearIsometry
import Mathlib.Topology.Order.WithTop
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option maxHeartbeats 800000

noncomputable section
namespace ExpandedFA.Unbounded
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The real Banach adjoint under canonical evaluation into the bidual. -/
abbrev realAdjoint (A : Operator ℝ X (X →L[ℝ] ℝ)) :=
  BanachLinearMaximalSpec.adjointValue A

/-- Exact-domain characterization, independent of reflexivity. -/
theorem mem_realAdjoint_domain_iff (A : Operator ℝ X (X →L[ℝ] ℝ)) (v : X) :
    v ∈ (realAdjoint A).domain ↔
      ∃ f : X →L[ℝ] ℝ, ∀ x : A.domain, f (x : X) = A x v := by
  exact mem_banachAdjoint_domain_iff A
    (P1.C04CanonicalMap.Spec.CanonicalEvaluationValue ℝ X v)

/-- The scalar-linear adjoint pairing, with no conjugation. -/
theorem realAdjoint_apply (A : Operator ℝ X (X →L[ℝ] ℝ))
    (hA : Dense (A.domain : Set X)) (v : (realAdjoint A).domain) (x : A.domain) :
    realAdjoint A v (x : X) = A x (v : X) :=
  banachAdjoint_apply A hA
    ⟨P1.C04CanonicalMap.Spec.CanonicalEvaluationValue ℝ X v, v.2⟩ x

/-- A prescribed continuous extension gives the actual adjoint value. -/
theorem realAdjoint_unique (A : Operator ℝ X (X →L[ℝ] ℝ))
    (hA : Dense (A.domain : Set X)) (v : (realAdjoint A).domain)
    (f : X →L[ℝ] ℝ) (hf : ∀ x : A.domain, f (x : X) = A x (v : X)) :
    realAdjoint A v = f :=
  (banachAdjoint_unique_extension A hA
    ⟨P1.C04CanonicalMap.Spec.CanonicalEvaluationValue ℝ X v, v.2⟩ f hf).symm

/-- The pulled-back graph has the full defining pairing relation. -/
theorem mem_realAdjoint_graph_iff (A : Operator ℝ X (X →L[ℝ] ℝ))
    (hA : Dense (A.domain : Set X)) (v : X) (f : X →L[ℝ] ℝ) :
    (v, f) ∈ (realAdjoint A).graph ↔ ∀ x : A.domain, f (x : X) = A x v := by
  constructor
  · intro h
    obtain ⟨w, hw, hf⟩ := (realAdjoint A).mem_graph_iff.mp h
    change (w : X) = v at hw
    change realAdjoint A w = f at hf
    subst v
    rw [← hf]
    exact realAdjoint_apply A hA w
  · intro hf
    have hv := (mem_realAdjoint_domain_iff A v).mpr ⟨f, hf⟩
    exact (realAdjoint A).mem_graph_iff.mpr
      ⟨⟨v, hv⟩, rfl, realAdjoint_unique A hA ⟨v, hv⟩ f hf⟩

/-- Maximality forces positivity of the adjoint. This implication needs neither
closedness, completeness, reflexivity, nor either strict convexity assumption. -/
theorem realAdjoint_monotone_of_maximal (A : Operator ℝ X (X →L[ℝ] ℝ))
    (hA : Dense (A.domain : Set X))
    (hmax : Monotone.Spec.LinearMaximalMonotoneValue X A) :
    Monotone.Spec.LinearMonotoneValue X (realAdjoint A) := by
  obtain ⟨hmono, hrelated⟩ := (Monotone.maximalMonotone_iff_related X _).mp hmax
  have hpos := (Monotone.linearMonotone_iff_positive X A).mp hmono
  apply (Monotone.linearMonotone_iff_positive X (realAdjoint A)).mpr
  intro v
  by_contra hv
  have hvneg : realAdjoint A v (v : X) < 0 := lt_of_not_ge hv
  have hmem : ((v : X), -realAdjoint A v) ∈ A.graph := by
    apply hrelated
    intro y g hg
    obtain ⟨w, hw, hgw⟩ := A.mem_graph_iff.mp hg
    change (w : X) = y at hw
    change A w = g at hgw
    subst y
    subst g
    have hadj := realAdjoint_apply A hA v w
    have hp := hpos w
    simp only [sub_apply, neg_apply, map_sub]
    linarith
  obtain ⟨w, hw, hgw⟩ := A.mem_graph_iff.mp hmem
  change (w : X) = (v : X) at hw
  change A w = -realAdjoint A v at hgw
  have hp := hpos w
  rw [hgw] at hp
  simp only [neg_apply, hw] at hp
  have hadj := realAdjoint_apply A hA v w
  rw [hgw] at hadj
  simp only [neg_apply, hw] at hadj
  linarith


/-- A closed graph is recovered from its adjoint pairings. Only reflexivity of
X is required; no density statement about the adjoint is assumed here. -/
theorem mem_graph_of_adjoint_pairings (A : Operator ℝ X (X →L[ℝ] ℝ))
    (hA : Dense (A.domain : Set X)) (hc : A.IsClosed)
    (href : P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X)
    (x : X) (f : X →L[ℝ] ℝ)
    (hp : ∀ v : (realAdjoint A).domain, f (v : X) = realAdjoint A v x) :
    (x, f) ∈ A.graph := by
  by_contra hnot
  have hn : (x, f) ∉ _root_.closure (A.graph : Set (X × (X →L[ℝ] ℝ))) := by
    have hclosed : _root_.IsClosed (A.graph : Set (X × (X →L[ℝ] ℝ))) := hc
    rw [hclosed.closure_eq]
    exact hnot
  obtain ⟨L, hL, hLne⟩ := exists_dual_vanishing_of_not_mem_closure A.graph (x, f) hn
  let g : X →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ X (X →L[ℝ] ℝ))
  let F : (X →L[ℝ] ℝ) →L[ℝ] ℝ :=
    L.comp (ContinuousLinearMap.inr ℝ X (X →L[ℝ] ℝ))
  obtain ⟨v, hv⟩ := href F
  have hsplit (u : X) (q : X →L[ℝ] ℝ) : L (u, q) = g u + q v := by
    have hadd := L.map_add (u, (0 : X →L[ℝ] ℝ)) ((0 : X), q)
    change L (u + 0, 0 + q) = g u + F q at hadd
    simpa only [add_zero, zero_add] using (hadd.trans (by rw [← hv]; rfl))
  have hpair (u : A.domain) : (-g) (u : X) = A u v := by
    have hz := hL ((u : X), A u) (A.mem_graph u)
    rw [hsplit] at hz
    change -g (u : X) = A u v
    linarith
  have hdom := (mem_realAdjoint_domain_iff A v).mpr ⟨-g, hpair⟩
  have hval := realAdjoint_unique A hA ⟨v, hdom⟩ (-g) hpair
  have hh := hp ⟨v, hdom⟩
  rw [hval] at hh
  apply hLne
  rw [hsplit]
  change f v = -g x at hh
  linarith

/-- In the reflexive closed-operator case the adjoint has norm-dense domain. -/
theorem realAdjoint_dense (A : Operator ℝ X (X →L[ℝ] ℝ))
    (hA : Dense (A.domain : Set X)) (hc : A.IsClosed)
    (href : P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X) :
    Dense ((realAdjoint A).domain : Set X) := by
  intro x
  by_contra hx
  obtain ⟨f, hf, hfx⟩ :=
    exists_dual_vanishing_of_not_mem_closure (realAdjoint A).domain x hx
  have hg : ((0 : X), f) ∈ A.graph :=
    mem_graph_of_adjoint_pairings A hA hc href 0 f (fun v => by
      rw [hf v v.2, map_zero])
  obtain ⟨u, hu, huf⟩ := A.mem_graph_iff.mp hg
  change (u : X) = 0 at hu
  change A u = f at huf
  have hu0 : u = 0 := Subtype.ext hu
  have hf0 : f = 0 := by rw [← huf, hu0, A.map_zero]
  exact hfx (by rw [hf0]; rfl)

/-- Closedness is preserved by the canonical pullback. -/
theorem realAdjoint_closed (A : Operator ℝ X (X →L[ℝ] ℝ))
    (hA : Dense (A.domain : Set X)) : (realAdjoint A).IsClosed := by
  change _root_.IsClosed ((realAdjoint A).graph : Set (X × (X →L[ℝ] ℝ)))
  have he : ((realAdjoint A).graph : Set (X × (X →L[ℝ] ℝ))) =
      {p | ∀ u : A.domain, p.2 (u : X) = A u p.1} := by
    ext p
    exact mem_realAdjoint_graph_iff A hA p.1 p.2
  rw [he]
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun u => isClosed_eq
    ((ContinuousLinearMap.apply ℝ ℝ (u : X)).continuous.comp continuous_snd)
    ((A u).continuous.comp continuous_fst)

/-- The double adjoint equals A as an exact-domain partial linear map. -/
theorem realAdjoint_realAdjoint (A : Operator ℝ X (X →L[ℝ] ℝ))
    (hA : Dense (A.domain : Set X)) (hc : A.IsClosed)
    (href : P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X) :
    realAdjoint (realAdjoint A) = A := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  rw [mem_realAdjoint_graph_iff _ (realAdjoint_dense A hA hc href)]
  constructor
  · exact mem_graph_of_adjoint_pairings A hA hc href p.1 p.2
  · intro hp v
    obtain ⟨u, hu, huf⟩ := A.mem_graph_iff.mp hp
    change (u : X) = p.1 at hu
    change A u = p.2 at huf
    rw [← hu, ← huf]
    exact (realAdjoint_apply A hA v u).symm

/-- For a positive linear operator its kernel annihilates the entire range. -/
theorem kernel_annihilates_range (A : Operator ℝ X (X →L[ℝ] ℝ))
    (hm : Monotone.Spec.LinearMonotoneValue X A)
    (u : A.domain) (hu : A u = 0) (w : A.domain) : A w (u : X) = 0 := by
  have hp := (Monotone.linearMonotone_iff_positive X A).mp hm
  have h (t : ℝ) : 0 ≤ A w (w : X) + t * A w (u : X) := by
    have ht := hp (w + t • u)
    simpa only [A.map_add, A.map_smul, hu, smul_zero, add_zero,
      Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, smul_eq_mul] using ht
  by_contra hne
  have ht := h (-(A w (w : X) + 1) / A w (u : X))
  have he : -(A w (w : X) + 1) / A w (u : X) * A w (u : X) =
      -(A w (w : X) + 1) := div_mul_cancel₀ _ hne
  rw [he] at ht
  linarith

/-- Kernel inclusion uses monotonicity alone, in addition to domain density. -/
theorem ker_le_realAdjoint_ker (A : Operator ℝ X (X →L[ℝ] ℝ))
    (hA : Dense (A.domain : Set X))
    (hm : Monotone.Spec.LinearMonotoneValue X A) : A.ker ≤ (realAdjoint A).ker := by
  intro x hx
  obtain ⟨u, hu, hAu⟩ := A.mem_ker_iff.mp hx
  change x = (u : X) at hu
  subst x
  have hpair (w : A.domain) : (0 : X →L[ℝ] ℝ) (w : X) = A w (u : X) :=
    (kernel_annihilates_range A hm u hAu w).symm
  have hv := (mem_realAdjoint_domain_iff A (u : X)).mpr ⟨0, hpair⟩
  exact (realAdjoint A).mem_ker_iff.mpr
    ⟨⟨(u : X), hv⟩, rfl, realAdjoint_unique A hA ⟨(u : X), hv⟩ 0 hpair⟩

/-- Both kernels agree as soon as both operators are monotone. -/
theorem ker_eq_realAdjoint_ker (A : Operator ℝ X (X →L[ℝ] ℝ))
    (hA : Dense (A.domain : Set X)) (hc : A.IsClosed)
    (href : P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X)
    (hm : Monotone.Spec.LinearMonotoneValue X A)
    (hm' : Monotone.Spec.LinearMonotoneValue X (realAdjoint A)) :
    A.ker = (realAdjoint A).ker := by
  apply le_antisymm (ker_le_realAdjoint_ker A hA hm)
  have hh := ker_le_realAdjoint_ker (realAdjoint A) (realAdjoint_dense A hA hc href) hm'
  rwa [realAdjoint_realAdjoint A hA hc href] at hh


/-- The identified adjoint kernel is the preannihilator of the range. -/
theorem mem_realAdjoint_ker_iff (A : Operator ℝ X (X →L[ℝ] ℝ))
    (hA : Dense (A.domain : Set X)) (v : X) :
    v ∈ (realAdjoint A).ker ↔ ∀ u : A.domain, A u v = 0 := by
  constructor
  · intro hv
    obtain ⟨w, hw, hw0⟩ := (realAdjoint A).mem_ker_iff.mp hv
    change v = (w : X) at hw
    intro u
    rw [hw, ← realAdjoint_apply A hA w u, hw0]
    rfl
  · intro hv
    have hpair (u : A.domain) : (0 : X →L[ℝ] ℝ) (u : X) = A u v := (hv u).symm
    have hm := (mem_realAdjoint_domain_iff A v).mpr ⟨0, hpair⟩
    exact (realAdjoint A).mem_ker_iff.mpr
      ⟨⟨v, hm⟩, rfl, realAdjoint_unique A hA ⟨v, hm⟩ 0 hpair⟩

/-- Norm closure, rather than equality of the original ranges, is the
annihilator statement supplied by Hahn–Banach. -/
theorem realAdjoint_range_closure (A : Operator ℝ X (X →L[ℝ] ℝ))
    (hA : Dense (A.domain : Set X))
    (href : P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X) :
    _root_.closure (A.toFun.range : Set (X →L[ℝ] ℝ)) =
      {f | ∀ v ∈ (realAdjoint A).ker, f v = 0} := by
  ext f
  constructor
  · intro hf v hv
    have hvan := (mem_realAdjoint_ker_iff A hA v).mp hv
    exact (isClosed_eq
      (ContinuousLinearMap.apply ℝ ℝ v).continuous continuous_const).closure_subset_iff.mpr
      (by rintro q ⟨u, rfl⟩; exact hvan u) hf
  · intro hf
    by_contra hn
    obtain ⟨F, hF, hFne⟩ :=
      exists_dual_vanishing_of_not_mem_closure A.toFun.range f hn
    obtain ⟨v, hv⟩ := href F
    have hvker : v ∈ (realAdjoint A).ker :=
      (mem_realAdjoint_ker_iff A hA v).mpr (fun u => by
        have hh := hF (A u) (LinearMap.mem_range_self A.toFun u)
        rw [← hv] at hh
        exact hh)
    exact hFne (by rw [← hv]; exact hf v hvker)

/-- The two monotone adjoints have the same norm-closed range. -/
theorem range_closure_eq_realAdjoint (A : Operator ℝ X (X →L[ℝ] ℝ))
    (hA : Dense (A.domain : Set X)) (hc : A.IsClosed)
    (href : P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X)
    (hm : Monotone.Spec.LinearMonotoneValue X A)
    (hm' : Monotone.Spec.LinearMonotoneValue X (realAdjoint A)) :
    _root_.closure (A.toFun.range : Set (X →L[ℝ] ℝ)) =
      _root_.closure ((realAdjoint A).toFun.range : Set (X →L[ℝ] ℝ)) := by
  rw [realAdjoint_range_closure A hA href,
    realAdjoint_range_closure (realAdjoint A) (realAdjoint_dense A hA hc href) href,
    realAdjoint_realAdjoint A hA hc href, ker_eq_realAdjoint_ker A hA hc href hm hm']

/-- The kernel conclusion of the source theorem. -/
theorem linear_maximal_kernel_equality : BanachLinearMaximalSpec.KernelEquality.{u} := by
  intro X _ _ _ _ _ href A hc hd hm
  exact ker_eq_realAdjoint_ker A hd hc href hm.1
    (realAdjoint_monotone_of_maximal A hd hm)

/-- The range-closure conclusion of the source theorem. -/
theorem linear_maximal_range_closure_equality :
    BanachLinearMaximalSpec.RangeClosureEquality.{u} := by
  intro X _ _ _ _ _ href A hc hd hm
  exact range_closure_eq_realAdjoint A hd hc href hm.1
    (realAdjoint_monotone_of_maximal A hd hm)


/-- Canonical reflexivity passes to the continuous dual. -/
theorem reflexive_dual
    (href : P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X) :
    P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ (X →L[ℝ] ℝ) := by
  intro H
  refine ⟨H.comp (P1.C04CanonicalMap.Spec.CanonicalEvaluationValue ℝ X), ?_⟩
  ext F
  obtain ⟨x, rfl⟩ := href F
  rfl

/-- Canonical reflexivity passes to finite products, with their native norm. -/
theorem reflexive_prod {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (hX : P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X)
    (hY : P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ Y) :
    P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ (X × Y) := by
  intro H
  let L₁ : (X →L[ℝ] ℝ) →L[ℝ] ((X × Y) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (X × Y) X ℝ).flip (ContinuousLinearMap.fst ℝ X Y)
  let L₂ : (Y →L[ℝ] ℝ) →L[ℝ] ((X × Y) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (X × Y) Y ℝ).flip (ContinuousLinearMap.snd ℝ X Y)
  obtain ⟨x, hx⟩ := hX (H.comp L₁)
  obtain ⟨y, hy⟩ := hY (H.comp L₂)
  refine ⟨(x, y), ?_⟩
  ext f
  let g := f.comp (ContinuousLinearMap.inl ℝ X Y)
  let q := f.comp (ContinuousLinearMap.inr ℝ X Y)
  have he : f = L₁ g + L₂ q := by
    apply ContinuousLinearMap.ext
    intro z
    change f z = f (z.1, 0) + f (0, z.2)
    simpa using f.map_add (z.1, 0) (0, z.2)
  have hx' : g x = H (L₁ g) := congrArg (fun F : (X →L[ℝ] ℝ) →L[ℝ] ℝ => F g) hx
  have hy' : q y = H (L₂ q) := congrArg (fun F : (Y →L[ℝ] ℝ) →L[ℝ] ℝ => F q) hy
  change f (x, y) = H f
  conv_rhs => rw [he, H.map_add]
  rw [← hx', ← hy']
  simpa only [Prod.mk_add_mk, add_zero, zero_add, g, q,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply] using f.map_add (x, 0) (0, y)

/-- A norm-closed subspace of a reflexive space is reflexive. -/
theorem reflexive_closed_submodule (S : Submodule ℝ X)
    (hS : _root_.IsClosed (S : Set X))
    (href : P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X) :
    P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ S := by
  intro H
  let R := P1.C04DualMaps.dualRestriction ℝ X S
  obtain ⟨x, hx⟩ := href (H.comp R)
  have hxS : x ∈ S := by
    by_contra hn
    have hnc : x ∉ _root_.closure (S : Set X) := by rwa [hS.closure_eq]
    obtain ⟨g, hg, hgx⟩ := exists_dual_vanishing_of_not_mem_closure S x hnc
    have hRg : R g = 0 := by ext u; exact hg u u.2
    have hxg := congrArg (fun F : (X →L[ℝ] ℝ) →L[ℝ] ℝ => F g) hx
    change g x = H (R g) at hxg
    rw [hRg, map_zero] at hxg
    exact hgx hxg
  refine ⟨⟨x, hxS⟩, ?_⟩
  ext f
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq S f
  have hRg : R g = f := by ext u; exact hg u
  have hxg := congrArg (fun F : (X →L[ℝ] ℝ) →L[ℝ] ℝ => F g) hx
  change g x = H (R g) at hxg
  change f ⟨x, hxS⟩ = H f
  rw [← hg ⟨x, hxS⟩, ← hRg]
  exact hxg


/-- The shifted quadratic on the actual graph, with its inherited product norm. -/
def graphEnergy (A : Operator ℝ X (X →L[ℝ] ℝ)) (x : X) (f : X →L[ℝ] ℝ)
    (z : A.graph) : ℝ :=
  ‖z.val.1 - x‖ ^ 2 / 2 + ‖z.val.2 - f‖ ^ 2 / 2 + (z.val.2 - f) (z.val.1 - x)

/-- The cross term is convex on the graph precisely because A is monotone. -/
theorem graphEnergy_convex (A : Operator ℝ X (X →L[ℝ] ℝ))
    (hm : Monotone.Spec.LinearMonotoneValue X A) (x : X) (f : X →L[ℝ] ℝ) :
    ConvexOn ℝ (Set.univ : Set A.graph) (graphEnergy A x f) := by
  have hcross : ConvexOn ℝ (Set.univ : Set A.graph)
      (fun z : A.graph => (z.val.2 - f) (z.val.1 - x)) := by
    refine ⟨convex_univ, ?_⟩
    intro z _ w _ a b ha hb hab
    have hp : 0 ≤ (z.val.2 - w.val.2) (z.val.1 - w.val.1) := hm z.2 w.2
    have he : a * ((z.val.2 - f) (z.val.1 - x)) +
        b * ((w.val.2 - f) (w.val.1 - x)) -
        (((a • z + b • w : A.graph).val.2 - f)
          ((a • z + b • w : A.graph).val.1 - x)) =
        a * b * ((z.val.2 - w.val.2) (z.val.1 - w.val.1)) := by
      change a * ((z.val.2 - f) (z.val.1 - x)) +
        b * ((w.val.2 - f) (w.val.1 - x)) -
        ((a • z.val.2 + b • w.val.2 - f) (a • z.val.1 + b • w.val.1 - x)) = _
      simp only [_root_.sub_apply, _root_.add_apply,
        _root_.smul_apply, map_sub, map_add, map_smul, smul_eq_mul]
      rw [show b = 1 - a by linarith]
      ring
    change _ ≤ a * _ + b * _
    have hh := mul_nonneg (mul_nonneg ha hb) hp
    linarith
  refine ⟨convex_univ, ?_⟩
  intro z hz w hw a b ha hb hab
  have hn₁ := BanachConvex.halfNormSquare_convex (X := X)
    (z.val.1 - x) (w.val.1 - x) (‖z.val.1 - x‖ ^ 2 / 2)
    (‖w.val.1 - x‖ ^ 2 / 2) a b rfl rfl ha hb hab
  have hn₂ := BanachConvex.halfNormSquare_convex (X := X →L[ℝ] ℝ)
    (z.val.2 - f) (w.val.2 - f) (‖z.val.2 - f‖ ^ 2 / 2)
    (‖w.val.2 - f‖ ^ 2 / 2) a b rfl rfl ha hb hab
  have he₁ : a • (z.val.1 - x) + b • (w.val.1 - x) =
      (a • z + b • w : A.graph).val.1 - x := by
    change _ = a • z.val.1 + b • w.val.1 - x
    rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]
  have he₂ : a • (z.val.2 - f) + b • (w.val.2 - f) =
      (a • z + b • w : A.graph).val.2 - f := by
    change _ = a • z.val.2 + b • w.val.2 - f
    rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]
  change ((‖a • (z.val.1 - x) + b • (w.val.1 - x)‖ ^ 2 / 2 : ℝ) : WithTop ℝ) ≤ _ at hn₁
  change ((‖a • (z.val.2 - f) + b • (w.val.2 - f)‖ ^ 2 / 2 : ℝ) : WithTop ℝ) ≤ _ at hn₂
  rw [he₁, WithTop.coe_le_coe] at hn₁
  rw [he₂, WithTop.coe_le_coe] at hn₂
  have hc := hcross.2 hz hw ha hb hab
  change _ ≤ a * _ + b * _ at hc
  change graphEnergy A x f (a • z + b • w) ≤ a * graphEnergy A x f z + b * graphEnergy A x f w
  dsimp only [graphEnergy]
  linarith


/-- The graph functional is continuous in the graph topology. -/
theorem graphEnergy_continuous (A : Operator ℝ X (X →L[ℝ] ℝ))
    (x : X) (f : X →L[ℝ] ℝ) : Continuous (graphEnergy A x f) := by
  unfold graphEnergy
  fun_prop

/-- A monotonically related pair makes the cross term nonnegative everywhere
on the graph; hence a real energy sublevel is bounded in the graph norm. -/
theorem graphEnergy_bounded_sublevels (A : Operator ℝ X (X →L[ℝ] ℝ))
    (x : X) (f : X →L[ℝ] ℝ)
    (hrel : ∀ z : A.graph, 0 ≤ (z.val.2 - f) (z.val.1 - x)) :
    P1.C14Minimization.Spec.BoundedSublevels (Set.univ : Set A.graph)
      (fun z => (graphEnergy A x f z : WithTop ℝ)) := by
  intro a
  apply (isBounded_iff_forall_norm_le (s := P1.C14Minimization.Spec.sublevel
    (Set.univ : Set A.graph) (fun z => (graphEnergy A x f z : WithTop ℝ)) a)).mpr
  refine ⟨a + 1 + max ‖x‖ ‖f‖, ?_⟩
  rintro z ⟨w, hw, rfl⟩
  have hle : graphEnergy A x f w ≤ a := WithTop.coe_le_coe.mp hw
  have hcross := hrel w
  have hn₁ := sq_nonneg (‖w.val.val.1 - x‖ - 1)
  have hn₂ := sq_nonneg (‖w.val.val.2 - f‖ - 1)
  have hs₁ := sq_nonneg ‖w.val.val.1 - x‖
  have hs₂ := sq_nonneg ‖w.val.val.2 - f‖
  have h₁ : ‖w.val.val.1 - x‖ ≤ a + 1 := by
    dsimp [graphEnergy] at hle
    nlinarith
  have h₂ : ‖w.val.val.2 - f‖ ≤ a + 1 := by
    dsimp [graphEnergy] at hle
    nlinarith
  change max ‖w.val.val.1‖ ‖w.val.val.2‖ ≤ _
  apply max_le
  · have ht := norm_sub_le w.val.val.1 x
    have ht' := norm_add_le (w.val.val.1 - x) x
    rw [sub_add_cancel] at ht'
    linarith [le_max_left ‖x‖ ‖f‖]
  · have ht' := norm_add_le (w.val.val.2 - f) f
    rw [sub_add_cancel] at ht'
    linarith [le_max_right ‖x‖ ‖f‖]

/-- The direct method produces a genuine minimizer on the exact graph. -/
theorem graphEnergy_attains_minimum [CompleteSpace X]
    (A : Operator ℝ X (X →L[ℝ] ℝ)) (hc : A.IsClosed)
    (href : P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X)
    (hm : Monotone.Spec.LinearMonotoneValue X A) (x : X) (f : X →L[ℝ] ℝ)
    (hrel : ∀ z : A.graph, 0 ≤ (z.val.2 - f) (z.val.1 - x)) :
    ∃ z : A.graph, ∀ w : A.graph, graphEnergy A x f z ≤ graphEnergy A x f w := by
  have hc' : _root_.IsClosed (A.graph : Set (X × (X →L[ℝ] ℝ))) := hc
  letI : CompleteSpace A.graph := hc'.completeSpace_coe
  have hrG := reflexive_closed_submodule A.graph hc' (reflexive_prod href (reflexive_dual href))
  have hconv := graphEnergy_convex A hm x f
  have hepi : Convex ℝ {p : A.graph × ℝ |
      (graphEnergy A x f p.1 : WithTop ℝ) ≤ (p.2 : WithTop ℝ)} := by
    simpa only [WithTop.coe_le_coe, Set.mem_univ, true_and] using hconv.convex_epigraph
  have hcont : Continuous (fun z : A.graph => (graphEnergy A x f z : WithTop ℝ)) :=
    WithTop.continuous_coe.comp (graphEnergy_continuous A x f)
  obtain ⟨z, m, _hz, hmin⟩ := P1.C14Minimization.convex_direct_method ℝ A.graph hrG
    Set.univ ⟨0, Set.mem_univ _⟩ convex_univ isClosed_univ
    (fun z => (graphEnergy A x f z : WithTop ℝ)) hepi hcont.lowerSemicontinuous
    ⟨⟨0, Set.mem_univ _⟩, WithTop.coe_ne_top⟩
    (Or.inl (graphEnergy_bounded_sublevels A x f hrel))
  exact ⟨z, fun w => WithTop.coe_le_coe.mp (hmin ⟨w, Set.mem_univ _⟩)⟩


/-- The bidual inherits strict convexity through the canonical onto isometry. -/
theorem strictConvex_bidual [StrictConvexSpace ℝ X]
    (href : P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X) :
    StrictConvexSpace ℝ ((X →L[ℝ] ℝ) →L[ℝ] ℝ) := by
  let e : X →ₗᵢ[ℝ] ((X →L[ℝ] ℝ) →L[ℝ] ℝ) :=
    { (P1.C04CanonicalMap.Spec.CanonicalEvaluationValue ℝ X).toLinearMap with
      norm_map' := P1.C05BidualIsometry.canonicalEvaluation_norm ℝ X }
  exact (LinearIsometryEquiv.ofSurjective e href).strictConvexSpace_iff.mp inferInstance

/-- Differentiating the real graph functional uses only directional derivatives
of the two squared norms and the continuous bilinear evaluation pairing. -/
theorem graphEnergy_stationary [CompleteSpace X]
    [StrictConvexSpace ℝ X] [StrictConvexSpace ℝ (X →L[ℝ] ℝ)]
    (href : P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X)
    (A : Operator ℝ X (X →L[ℝ] ℝ)) (x : X) (f : X →L[ℝ] ℝ)
    (J : X → (X →L[ℝ] ℝ)) (hJ : ∀ v, BanachConvex.Spec.DualityMapValue X v = {J v})
    (D : (X →L[ℝ] ℝ) → ((X →L[ℝ] ℝ) →L[ℝ] ℝ))
    (hD : ∀ r, BanachConvex.Spec.DualityMapValue (X →L[ℝ] ℝ) r = {D r})
    (z : A.graph) (hmin : ∀ w : A.graph, graphEnergy A x f z ≤ graphEnergy A x f w)
    (w : A.domain) :
    J (z.val.1 - x) (w : X) + D (z.val.2 - f) (A w) +
      A w (z.val.1 - x) + (z.val.2 - f) (w : X) = 0 := by
  letI := strictConvex_bidual href
  let v := z.val.1 - x
  let r := z.val.2 - f
  let wg : A.graph := ⟨((w : X), A w), A.mem_graph w⟩
  have hd₁ := BanachConvex.halfNormSquare_gateaux X J hJ v (w : X)
  have hd₂ := BanachConvex.halfNormSquare_gateaux (X →L[ℝ] ℝ) D hD r (A w)
  have hdr : HasDerivAt (fun t : ℝ => r + t • A w) (A w) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (A w)).const_add r
  have hdv : HasDerivAt (fun t : ℝ => v + t • (w : X)) (w : X) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (w : X)).const_add v
  have hdc : HasDerivAt (fun t : ℝ => (r + t • A w) (v + t • (w : X)))
      (A w v + r (w : X)) 0 := by
    simpa using hdr.clm_apply hdv
  have hd : HasDerivAt (fun t : ℝ => graphEnergy A x f (z + t • wg))
      (J v (w : X) + D r (A w) + (A w v + r (w : X))) 0 := by
    convert (hd₁.add hd₂).add hdc using 1
    funext t
    dsimp [graphEnergy, wg, v, r]
    congr 2 <;> abel
  have hl : IsLocalMin (fun t : ℝ => graphEnergy A x f (z + t • wg)) 0 := by
    apply IsMinOn.isLocalMin (s := Set.univ)
    · intro t _
      change graphEnergy A x f (z + (0 : ℝ) • wg) ≤ graphEnergy A x f (z + t • wg)
      simpa only [zero_smul, add_zero] using hmin (z + t • wg)
    · exact Filter.univ_mem
  have hh := hl.hasDerivAt_eq_zero hd
  dsimp [v, r] at hh
  linarith

/-- Monotonicity of A and its adjoint forces every related pair into G(A). -/
theorem maximal_of_realAdjoint_monotone [CompleteSpace X]
    [StrictConvexSpace ℝ X] [StrictConvexSpace ℝ (X →L[ℝ] ℝ)]
    (A : Operator ℝ X (X →L[ℝ] ℝ)) (hc : A.IsClosed)
    (hA : Dense (A.domain : Set X))
    (href : P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X)
    (hm : Monotone.Spec.LinearMonotoneValue X A)
    (hm' : Monotone.Spec.LinearMonotoneValue X (realAdjoint A)) :
    Monotone.Spec.LinearMaximalMonotoneValue X A := by
  apply (Monotone.maximalMonotone_iff_related X _).mpr
  refine ⟨hm, ?_⟩
  intro x f hrelated
  have hrel (z : A.graph) : 0 ≤ (z.val.2 - f) (z.val.1 - x) := by
    have hh := hrelated z.val.1 z.val.2 z.2
    simpa only [← neg_sub f z.val.2, ← neg_sub x z.val.1,
      _root_.neg_apply, map_neg, neg_neg] using hh
  obtain ⟨z, hmin⟩ := graphEnergy_attains_minimum A hc href hm x f hrel
  letI := strictConvex_bidual href
  obtain ⟨J, hJ⟩ := BanachConvex.dualityMap_singleton X
  obtain ⟨D, hD⟩ := BanachConvex.dualityMap_singleton (X →L[ℝ] ℝ)
  let v := z.val.1 - x
  let r := z.val.2 - f
  obtain ⟨y, hy⟩ := href (D r)
  have hvJ := BanachConvex.selection_mem J hJ v
  have hrD := BanachConvex.selection_mem D hD r
  have hny : ‖y‖ = ‖r‖ := by
    have hnorm := hrD.1
    rw [← hy, P1.C05BidualIsometry.canonicalEvaluation_norm ℝ X y] at hnorm
    exact hnorm
  have hry : r y = ‖r‖ ^ 2 := by
    have hval := hrD.2
    rw [← hy] at hval
    exact hval
  have hpair (w : A.domain) : (-(J v + r)) (w : X) = A w (y + v) := by
    have hs := graphEnergy_stationary href A x f J hJ D hD z hmin w
    change J v (w : X) + D r (A w) + A w v + r (w : X) = 0 at hs
    rw [← hy] at hs
    change J v (w : X) + A w y + A w v + r (w : X) = 0 at hs
    simp only [_root_.neg_apply, _root_.add_apply, map_add]
    linarith
  have hdom := (mem_realAdjoint_domain_iff A (y + v)).mpr ⟨-(J v + r), hpair⟩
  have hval := realAdjoint_unique A hA ⟨y + v, hdom⟩ (-(J v + r)) hpair
  have hp := (Monotone.linearMonotone_iff_positive X (realAdjoint A)).mp hm' ⟨y + v, hdom⟩
  rw [hval] at hp
  change 0 ≤ -(J v + r) (y + v) at hp
  have hcross : 0 ≤ r v := hrel z
  have hjbound := (J v).le_opNorm y
  rw [Real.norm_eq_abs, hvJ.1, hny] at hjbound
  have hjlower := (abs_le.mp hjbound).1
  simp only [_root_.add_apply, map_add] at hp
  rw [hvJ.2, hry] at hp
  have hv0 : ‖v‖ = 0 := by nlinarith [sq_nonneg (‖v‖ - ‖r‖)]
  have hr0 : ‖r‖ = 0 := by nlinarith [sq_nonneg (‖v‖ - ‖r‖)]
  have hv : z.val.1 = x := sub_eq_zero.mp (norm_eq_zero.mp hv0)
  have hr : z.val.2 = f := sub_eq_zero.mp (norm_eq_zero.mp hr0)
  change (x, f) ∈ A.graph
  have he : z.val = (x, f) := Prod.ext hv hr
  rw [← he]
  exact z.2

/-- The complete maximal-monotonicity equivalence, with the source hypotheses. -/
theorem linear_maximal_monotonicity_criterion : BanachLinearMaximalSpec.Criterion.{u} := by
  intro X _ _ _ _ _ href A hc hd hm
  exact ⟨realAdjoint_monotone_of_maximal A hd,
    maximal_of_realAdjoint_monotone A hc hd href hm⟩

/-- In that case the Banach adjoint is also maximal among all monotone graphs. -/
theorem linear_maximal_adjoint_maximality : BanachLinearMaximalSpec.AdjointMaximality.{u} := by
  intro X _ _ _ _ _ href A hc hd hmax
  have hm' := realAdjoint_monotone_of_maximal A hd hmax
  apply maximal_of_realAdjoint_monotone (realAdjoint A) (realAdjoint_closed A hd)
    (realAdjoint_dense A hd hc href) href hm'
  rw [realAdjoint_realAdjoint A hd hc href]
  exact hmax.1

end ExpandedFA.Unbounded
