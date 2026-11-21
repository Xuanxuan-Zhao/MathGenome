import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Differential.ImplicitFunction
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Differential.InverseFunction
import Mathlib.Analysis.Calculus.ImplicitContDiff

open Filter Set
open scoped Topology ContDiff

namespace ExpandedFA.Differential.ImplicitFunction

variable {𝕜 E Y Z : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]

omit [CompleteSpace E] [CompleteSpace Y] [CompleteSpace Z] in
/-- The derivative of `(x,y) ↦ (x,H(x,y))` is a bounded isomorphism
whenever the partial derivative in `y` is a bounded isomorphism. -/
lemma block_equiv (L : E × Y →L[𝕜] Z) (B : Y ≃L[𝕜] Z)
    (hB : L.comp (ContinuousLinearMap.inr 𝕜 E Y) = (B : Y →L[𝕜] Z)) :
    (((ContinuousLinearEquiv.refl 𝕜 E).skewProd B
      (L.comp (ContinuousLinearMap.inl 𝕜 E Y))) : E × Y →L[𝕜] E × Z) =
        (ContinuousLinearMap.fst 𝕜 E Y).prod L := by
  apply ContinuousLinearMap.ext
  intro p
  apply Prod.ext
  · rfl
  · change (B : Y →L[𝕜] Z) p.2 + L.comp (ContinuousLinearMap.inl 𝕜 E Y) p.1 = L p
    rw [← hB, add_comm]
    exact L.comp_inl_add_comp_inr p

omit [CompleteSpace E] [CompleteSpace Y] [CompleteSpace Z] in
/-- The derivative compositions used in the statement are the native partial
Fréchet derivatives of the two one-variable slices. -/
lemma partial_derivatives {H : E × Y → Z} {p : E × Y}
    (hH : DifferentiableAt 𝕜 H p) :
    fderiv 𝕜 (fun x => H (x, p.2)) p.1 =
        (fderiv 𝕜 H p).comp (ContinuousLinearMap.inl 𝕜 E Y) ∧
    fderiv 𝕜 (fun y => H (p.1, y)) p.2 =
        (fderiv 𝕜 H p).comp (ContinuousLinearMap.inr 𝕜 E Y) := by
  exact ⟨(hH.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left p.1 p.2)).fderiv,
    (hH.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)).fderiv⟩

/-- Apply the accepted inverse theorem to the block map and take its inverse
on the slice `(x,0)`. Restrict to a product neighborhood on which both the
slice and the graph stay in the inverse chart. -/
theorem implicit_function : Spec.LocalImplicitTheorem := by
  intro 𝕜 E Y Z _ _ _ _ _ _ _ _ _ _ Ω hΩ H hH x₀ y₀ hp₀ hzero B hB
  let L := fderiv 𝕜 H (x₀, y₀)
  have hH₀ : ContDiffAt 𝕜 1 H (x₀, y₀) := hH.contDiffAt (hΩ.mem_nhds hp₀)
  have hInv₀ : (L.comp (ContinuousLinearMap.inr 𝕜 E Y)).IsInvertible := by
    rw [hB]
    exact ContinuousLinearMap.isInvertible_equiv
  have hcont : ContinuousAt
      (fun p => (fderiv 𝕜 H p).comp (ContinuousLinearMap.inr 𝕜 E Y)) (x₀, y₀) :=
    ((ContinuousLinearMap.compL 𝕜 Y (E × Y) Z).flip
      (ContinuousLinearMap.inr 𝕜 E Y)).continuous.continuousAt.comp
        (hH₀.continuousAt_fderiv one_ne_zero)
  have hInvnhds : {p | ((fderiv 𝕜 H p).comp
      (ContinuousLinearMap.inr 𝕜 E Y)).IsInvertible} ∈ 𝓝 (x₀, y₀) :=
    hcont.preimage_mem_nhds hInv₀.eventually_nhds
  obtain ⟨W, hWsub, hWopen, hpW⟩ := mem_nhds_iff.mp
    (inter_mem (hΩ.mem_nhds hp₀) hInvnhds)
  let T : E × Y → E × Z := fun p => (p.1, H p)
  have hT (k : WithTop ℕ∞) (hk : ContDiffOn 𝕜 k H Ω) : ContDiffOn 𝕜 k T W :=
    contDiffOn_fst.prodMk (hk.mono (fun p hp => (hWsub hp).1))
  let A := (ContinuousLinearEquiv.refl 𝕜 E).skewProd B
    (L.comp (ContinuousLinearMap.inl 𝕜 E Y))
  have hA : HasFDerivAt T (A : E × Y →L[𝕜] E × Z) (x₀, y₀) := by
    rw [block_equiv L B hB]
    exact hasFDerivAt_fst.prodMk ((hH₀.differentiableAt one_ne_zero).hasFDerivAt)
  obtain ⟨e, _he, hpS, hSW, hpT₀, _heC1, hleft, hright, _hderiv, _hexact,
      _hunique, hregular⟩ :=
    InverseFunction.inverse_function 𝕜 (E × Y) (E × Z) W hWopen T (hT 1 hH)
      (x₀, y₀) hpW A hA
  have hpT : (x₀, (0 : Z)) ∈ e.target := by
    simpa only [T, hzero] using hpT₀
  let φ : E → Y := fun x => (e.symm (x, 0)).2
  have hφ₀ : φ x₀ = y₀ := by
    have := hleft (x₀, y₀) hpS
    simpa only [T, hzero, φ] using congrArg Prod.snd this
  obtain ⟨U₀, V, hU₀, hxU₀, hV, hyV, hUV⟩ := mem_nhds_prod_iff'.mp
    (e.open_source.mem_nhds hpS)
  have htarget : {x : E | (x, (0 : Z)) ∈ e.target} ∈ 𝓝 x₀ :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds hpT)
  have hscont : ContinuousAt (fun x : E => (x, (0 : Z))) x₀ :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hφcont : ContinuousAt φ x₀ :=
    (ContinuousAt.comp (g := e.symm) (f := fun x : E => (x, (0 : Z)))
      (x := x₀) (e.symm.continuousAt hpT) hscont).snd
  have hφV : {x | φ x ∈ V} ∈ 𝓝 x₀ := by
    apply hφcont.preimage_mem_nhds
    rw [hφ₀]
    exact hV.mem_nhds hyV
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp
    (inter_mem (hU₀.mem_nhds hxU₀) (inter_mem htarget hφV))
  have hslice (x : E) (hx : x ∈ U) : (x, (0 : Z)) ∈ e.target :=
    (hUsub hx).2.1
  have hφrange : MapsTo φ U V := fun x hx => (hUsub hx).2.2
  have hprod : U ×ˢ V ⊆ e.source := fun p hp => hUV ⟨(hUsub hp.1).1, hp.2⟩
  have hsourceΩ : e.source ⊆ Ω := fun p hp => (hWsub (hSW hp)).1
  have hgraph (x : E) (hx : x ∈ U) : e.symm (x, (0 : Z)) = (x, φ x) := by
    have h := congrArg Prod.fst (hright (x, 0) (hslice x hx))
    exact Prod.ext h rfl
  have hgraphS (x : E) (hx : x ∈ U) : (x, φ x) ∈ e.source :=
    hprod ⟨hx, hφrange hx⟩
  have hφregular (k : WithTop ℕ∞) (hk : ContDiffOn 𝕜 k H Ω) :
      ContDiffOn 𝕜 k φ U := by
    have hi := hregular k (hT k hk)
    exact (hi.comp (contDiffOn_id.prodMk contDiffOn_const) hslice).snd
  have hzeros (x : E) (hx : x ∈ U) (y : Y) (hy : y ∈ V) :
      H (x, y) = 0 ↔ y = φ x := by
    constructor
    · intro hz
      have h := hleft (x, y) (hprod ⟨hx, hy⟩)
      have heq : T (x, y) = (x, (0 : Z)) := Prod.ext rfl hz
      rw [heq] at h
      exact (congrArg Prod.snd h).symm
    · intro hyφ
      subst y
      have h := hright (x, 0) (hslice x hx)
      rw [hgraph x hx] at h
      exact congrArg Prod.snd h
  refine ⟨U, V, φ, hU, hV, hxU, hyV, fun p hp => hsourceΩ (hprod hp),
    hφ₀, hφrange, hφregular 1 hH, hzeros, ?_, ?_, ?_, hφregular⟩
  · intro x hx
    have hInv := (hWsub (hSW (hgraphS x hx))).2
    have hc : ContDiffAt 𝕜 1 H (x, φ x) :=
      hH.contDiffAt (hΩ.mem_nhds (hsourceΩ (hgraphS x hx)))
    -- The native local implicit function gives the derivative formula at this
    -- graph point; exactness of the graph identifies its germ with our map.
    let ψ := hc.implicitFunction one_ne_zero hInv
    have hψbase : ψ x = φ x := hc.implicitFunction_apply_self one_ne_zero hInv
    have hψcont : ContinuousAt ψ x :=
      (hc.contDiffAt_implicitFunction one_ne_zero hInv).continuousAt
    have hψV : ∀ᶠ z in 𝓝 x, ψ z ∈ V := by
      apply hψcont.preimage_mem_nhds
      rw [hψbase]
      exact hV.mem_nhds (hφrange hx)
    have hψzero : ∀ᶠ z in 𝓝 x, H (z, ψ z) = 0 := by
      have hz := hc.eventually_apply_implicitFunction one_ne_zero hInv
      have hzx := (hzeros x hx (φ x) (hφrange hx)).mpr rfl
      simpa only [ψ, hzx] using hz
    have heq : ψ =ᶠ[𝓝 x] φ := by
      filter_upwards [hU.mem_nhds hx, hψV, hψzero] with z hzU hzV hz0
      exact (hzeros z hzU (ψ z) hzV).mp hz0
    have hd := (hc.hasStrictFDerivAt_implicitFunction one_ne_zero hInv).hasFDerivAt
    have hdφ := hd.congr_of_eventuallyEq heq.symm
    exact ⟨hInv, hdφ, hdφ.fderiv⟩
  · intro ψ hψ x hx
    exact (hzeros x hx (ψ x) (hψ x hx).1).mp (hψ x hx).2
  · intro ψ hc hb hz
    have hψV : ∀ᶠ x in 𝓝 x₀, ψ x ∈ V := by
      apply hc.preimage_mem_nhds
      rw [hb]
      exact hV.mem_nhds hyV
    filter_upwards [hU.mem_nhds hxU, hψV, hz] with x hx hxV hx0
    exact (hzeros x hx (ψ x) hxV).mp hx0

end ExpandedFA.Differential.ImplicitFunction
