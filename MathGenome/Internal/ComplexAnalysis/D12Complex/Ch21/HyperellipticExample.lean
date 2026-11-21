import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.HyperellipticEvenEnds
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.HyperellipticOddEnd
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.AnalyticEndPasting
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.CompactCompletion
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.HyperellipticExample
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.SimpleRootBranches
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.MonodromyTransitive
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalHolomorphicInverse
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.MapsMultiplicity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.LocalLogarithmsRoots
import Mathlib.FieldTheory.Perfect
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
Construction for paper.tex:3720–3755. These results establish the finite
local graph parameters and their order, a compatible complex atlas with immersed
inverse charts, elementary infinity formulas and sheet coverage, irreducibility,
compact affine cores, and the connected full affine Riemann surface.

The final-topology infinity disk attachments below give compact connected
completions, with the stated coordinate formulas and projection multiplicities.
-/
noncomputable section
open Set Polynomial Filter
open scoped Topology

namespace D12Complex.HyperellipticExample

lemma squarefree_derivative_ne_zero (P : Polynomial ℂ) (hP : Squarefree P)
    (a : ℂ) (ha : P.eval a = 0) : P.derivative.eval a ≠ 0 := by
  have hs : P.Separable := PerfectField.separable_iff_squarefree.mpr hP
  simpa only [Polynomial.eval₂_id] using hs.eval₂_derivative_ne_zero (RingHom.id ℂ) ha

lemma polynomial_holomorphic (P : Polynomial ℂ) : HolomorphicOn Set.univ P.eval :=
  ⟨isOpen_univ, fun z _ => (P.hasDerivAt z).differentiableAt⟩

lemma affine_graph_at_nonzero (P : Polynomial ℂ) (a b : ℂ)
    (h : b ^ 2 = P.eval a) (hb : b ≠ 0) :
    ∃ (U V : Set ℂ) (f : ℂ → ℂ),
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ b ∈ V ∧
      HolomorphicOn U f ∧ f a = b ∧ MapsTo f U V ∧
      ∀ z ∈ U, ∀ w ∈ V, w ^ 2 = P.eval z ↔ w = f z := by
  have hpoly : ContDiffAt ℂ 1 (fun q : ℂ × ℂ => q.2 ^ 2 - P.eval q.1) (a,b) :=
    (contDiffAt_snd.pow 2).sub (by
      have hc : ContDiff ℂ 1 P.eval := by simpa using P.contDiff_aeval (𝕜 := ℂ) 1
      exact hc.contDiffAt.comp (a,b) contDiffAt_fst)
  have hzero : (b ^ 2 - P.eval a) = 0 := sub_eq_zero.mpr h
  have hd : HasDerivAt (fun w : ℂ => w ^ 2 - P.eval a) (2 * b) b := by
    simpa using ((hasDerivAt_id b).pow 2).sub_const (P.eval a)
  obtain ⟨U, V, f, hU, hV, haU, hbV, hf, hfa, hmap, hgraph⟩ :=
    SimpleRootBranches.local_simple_root_hasDerivAt hpoly hzero hd (mul_ne_zero (by norm_num) hb)
  exact ⟨U, V, f, hU, hV, haU, hbV, ⟨hU, hf⟩, hfa, hmap,
    fun z hz w hw => by simpa only [sub_eq_zero] using hgraph z hz w hw⟩

lemma polynomial_inverse_at_root (P : Polynomial ℂ) (hP : Squarefree P)
    (a : ℂ) (ha : P.eval a = 0) :
    ∃ (U V : Set ℂ) (h : ℂ → ℂ),
      a ∈ U ∧ 0 ∈ V ∧ BiholomorphicPair U V P.eval h ∧ h 0 = a ∧
      HasDerivAt h (1 / P.derivative.eval a) 0 := by
  have hderiv : deriv P.eval a ≠ 0 := by
    simpa only [(P.hasDerivAt a).deriv] using squarefree_derivative_ne_zero P hP a ha
  obtain ⟨U, V, h, haU, haV, _, hbihol, _, hder⟩ :=
    LocalHolomorphicInverse.local_holomorphic_inverse Set.univ P.eval a
      (polynomial_holomorphic P) (mem_univ a) hderiv
  have h0 : 0 ∈ V := ha ▸ haV
  have hha : h 0 = a := by
    simpa only [ha] using hbihol.2.2.2.2.1 haU
  refine ⟨U, V, h, haU, h0, hbihol, hha, ?_⟩
  simpa only [hha, (P.hasDerivAt a).deriv] using (hder 0 h0).1


lemma affine_graph_at_root (P : Polynomial ℂ) (hP : Squarefree P)
    (a : ℂ) (ha : P.eval a = 0) :
    ∃ (U W : Set ℂ) (f : ℂ → ℂ),
      IsOpen U ∧ IsOpen W ∧ a ∈ U ∧ 0 ∈ W ∧
      HolomorphicOn W f ∧ f 0 = a ∧ MapsTo f W U ∧
      (∀ w ∈ W, ∀ z ∈ U, w ^ 2 = P.eval z ↔ z = f w) ∧
      analyticOrderAt (fun w => f w - a) 0 = (2 : ℕ∞) := by
  obtain ⟨U, V, h, haU, h0V, hbihol, hha, hder⟩ :=
    polynomial_inverse_at_root P hP a ha
  let W : Set ℂ := (fun w : ℂ => w ^ 2) ⁻¹' V
  let f : ℂ → ℂ := fun w => h (w ^ 2)
  have hW : IsOpen W := hbihol.2.1.1.preimage (continuous_id.pow 2)
  have h0W : 0 ∈ W := by simpa only [W, mem_preimage, zero_pow (by decide : 2 ≠ 0)] using h0V
  have hf : HolomorphicOn W f := by
    refine ⟨hW, ?_⟩
    intro w hw
    exact (hbihol.2.1.2 (w ^ 2) hw).comp w ((differentiableAt_id).pow 2)
  have hgerm : HolomorphicGermAt h 0 := ⟨V, h0V, hbihol.2.1⟩
  have hpower : HolomorphicGermAt (fun w : ℂ => w ^ 2) 0 :=
    ⟨univ, mem_univ _, ⟨isOpen_univ, fun _ _ => differentiableAt_id.pow 2⟩⟩
  have hderne : deriv h 0 ≠ 0 := by
    rw [hder.deriv]
    exact one_div_ne_zero (squarefree_derivative_ne_zero P hP a ha)
  have horder := Surfaces.centered_order_comp (G := h) hpower
    (by simpa only [zero_pow (by decide : 2 ≠ 0)] using hgerm)
    (by simpa only [zero_pow (by decide : 2 ≠ 0)] using hderne)
  have hsqorder : analyticOrderAt (fun w : ℂ => w ^ 2) 0 = (2 : ℕ∞) := by
    have ho := (analyticOrderAt_centeredMonomial (𝕜 := ℂ) (n := 2) (z₀ := (0 : ℂ)))
    convert ho using 1
    congr 1
    funext w
    simp
  refine ⟨U, W, f, hbihol.1.1, hW, haU, h0W, hf, ?_, ?_, ?_, ?_⟩
  · simpa only [f, zero_pow (by decide : 2 ≠ 0)] using hha
  · intro w hw
    exact hbihol.2.2.2.1 hw
  · intro w hw z hz
    constructor
    · intro heq
      dsimp only [f]
      rw [heq]
      exact (hbihol.2.2.2.2.1 hz).symm
    · intro heq
      rw [heq]
      exact (hbihol.2.2.2.2.2 hw).symm
  · simpa only [f, zero_pow (by decide : 2 ≠ 0), hha, sub_zero, hsqorder] using horder

end D12Complex.HyperellipticExample

namespace D12Complex.HyperellipticExample.FiniteGeometry

/-- The affine model, reusing the canonical zero set from the independent contract. -/
abbrev affineCurveModel (P : Polynomial ℂ) := AffineCurve P

/-- The coordinate-chart predicate on the canonical affine model. -/
abbrev goodCoordinateChart {P : Polynomial ℂ}
    (e : OpenPartialHomeomorph (AffineCurve P) ℂ) : Prop := GoodCoordinateChart e

def zChart (P : Polynomial ℂ) (U V : Set ℂ) (f : ℂ → ℂ) (x₀ : AffineCurve P)
    (hU : IsOpen U) (hV : IsOpen V)
    (hf : HolomorphicOn U f) (hmaps : MapsTo f U V)
    (hgraph : ∀ z ∈ U, ∀ w ∈ V, w ^ 2 = P.eval z ↔ w = f z) :
    OpenPartialHomeomorph (AffineCurve P) ℂ := by
  classical
  have hroot : ∀ z ∈ U, (f z) ^ 2 = P.eval z :=
    fun z hz => (hgraph z hz _ (hmaps hz)).mpr rfl
  exact {
    toFun x := x.val.1
    invFun z := if hz : z ∈ U then ⟨(z, f z), hroot z hz⟩ else x₀
    source := {x | x.val.1 ∈ U ∧ x.val.2 ∈ V}
    target := U
    map_source' x hx := hx.1
    map_target' z hz := by
      simp only [dite_eq_left hz]
      exact ⟨hz, hmaps hz⟩
    left_inv' x hx := by
      simp only [dite_eq_left hx.1]
      apply Subtype.ext
      exact Prod.ext rfl ((hgraph _ hx.1 _ hx.2).mp x.property).symm
    right_inv' z hz := by simp only [dite_eq_left hz]
    continuousOn_toFun := continuous_subtype_val.fst.continuousOn
    continuousOn_invFun := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hc0 : ContinuousOn f U := fun z hz => (hf.2 z hz).continuousAt.continuousWithinAt
      have hc : Continuous (fun z : U => f (z : ℂ)) := hc0.domRestrict
      have hpair : Continuous (fun z : U => (⟨((z : ℂ), f z), hroot z z.property⟩ : AffineCurve P)) :=
        (continuous_subtype_val.prodMk hc).subtype_mk _
      convert hpair using 1
      funext z
      simp [Set.domRestrict, z.property]
    open_source := (hU.preimage continuous_subtype_val.fst).inter
      (hV.preimage continuous_subtype_val.snd)
    open_target := hU }

def wChart (P : Polynomial ℂ) (U V : Set ℂ) (f : ℂ → ℂ) (x₀ : AffineCurve P)
    (hU : IsOpen U) (hV : IsOpen V)
    (hf : HolomorphicOn V f) (hmaps : MapsTo f V U)
    (hgraph : ∀ w ∈ V, ∀ z ∈ U, w ^ 2 = P.eval z ↔ z = f w) :
    OpenPartialHomeomorph (AffineCurve P) ℂ := by
  classical
  have hroot : ∀ w ∈ V, w ^ 2 = P.eval (f w) :=
    fun w hw => (hgraph w hw _ (hmaps hw)).mpr rfl
  exact {
    toFun x := x.val.2
    invFun w := if hw : w ∈ V then ⟨(f w, w), hroot w hw⟩ else x₀
    source := {x | x.val.1 ∈ U ∧ x.val.2 ∈ V}
    target := V
    map_source' x hx := hx.2
    map_target' w hw := by
      simp only [dite_eq_left hw]
      exact ⟨hmaps hw, hw⟩
    left_inv' x hx := by
      simp only [dite_eq_left hx.2]
      apply Subtype.ext
      exact Prod.ext ((hgraph _ hx.2 _ hx.1).mp x.property).symm rfl
    right_inv' w hw := by simp only [dite_eq_left hw]
    continuousOn_toFun := continuous_subtype_val.snd.continuousOn
    continuousOn_invFun := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hc0 : ContinuousOn f V := fun w hw => (hf.2 w hw).continuousAt.continuousWithinAt
      have hc : Continuous (fun w : V => f (w : ℂ)) := hc0.domRestrict
      have hpair : Continuous (fun w : V => (⟨(f w, (w : ℂ)), hroot w w.property⟩ : AffineCurve P)) :=
        (hc.prodMk continuous_subtype_val).subtype_mk _
      convert hpair using 1
      funext w
      simp [Set.domRestrict, w.property]
    open_source := (hU.preimage continuous_subtype_val.fst).inter
      (hV.preimage continuous_subtype_val.snd)
    open_target := hV }

lemma zChart_inverse (P : Polynomial ℂ) (U V : Set ℂ) (f : ℂ → ℂ) (x₀ : AffineCurve P)
    (hU : IsOpen U) (hV : IsOpen V)
    (hf : HolomorphicOn U f) (hmaps : MapsTo f U V)
    (hgraph : ∀ z ∈ U, ∀ w ∈ V, w ^ 2 = P.eval z ↔ w = f z)
    (z : ℂ) (hz : z ∈ U) :
    ((zChart P U V f x₀ hU hV hf hmaps hgraph).symm z).val = (z, f z) := by
  classical
  change (if h : z ∈ U then
    (⟨(z, f z), (hgraph z h _ (hmaps h)).mpr rfl⟩ : AffineCurve P) else x₀).val = (z, f z)
  rw [dite_eq_left hz]

lemma wChart_inverse (P : Polynomial ℂ) (U V : Set ℂ) (f : ℂ → ℂ) (x₀ : AffineCurve P)
    (hU : IsOpen U) (hV : IsOpen V)
    (hf : HolomorphicOn V f) (hmaps : MapsTo f V U)
    (hgraph : ∀ w ∈ V, ∀ z ∈ U, w ^ 2 = P.eval z ↔ z = f w)
    (w : ℂ) (hw : w ∈ V) :
    ((wChart P U V f x₀ hU hV hf hmaps hgraph).symm w).val = (f w, w) := by
  classical
  change (if h : w ∈ V then
    (⟨(f w, w), (hgraph w h _ (hmaps h)).mpr rfl⟩ : AffineCurve P) else x₀).val = (f w, w)
  rw [dite_eq_left hw]

end D12Complex.HyperellipticExample.FiniteGeometry

namespace D12Complex.HyperellipticExample.FiniteGeometry

lemma local_parameter_z (P : Polynomial ℂ) (x : AffineCurve P) (hx : x.val.2 ≠ 0) :
    ∃ e : OpenPartialHomeomorph (AffineCurve P) ℂ,
      x ∈ e.source ∧ (∀ y, e y = y.val.1) ∧
      HolomorphicOn e.target (fun z => (e.symm z).val.2) := by
  obtain ⟨U, V, f, hU, hV, hxU, hxV, hf, hfx, hmaps, hgraph⟩ :=
    affine_graph_at_nonzero P x.val.1 x.val.2 x.property hx
  let e := zChart P U V f x hU hV hf hmaps hgraph
  refine ⟨e, ⟨hxU, hxV⟩, fun _ => rfl, hU, ?_⟩
  intro z hz
  apply (hf.2 z hz).congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hz] with y hy
  exact congrArg Prod.snd (zChart_inverse P U V f x hU hV hf hmaps hgraph y hy)

lemma local_parameter_w (P : Polynomial ℂ) (hP : Squarefree P)
    (a : ℂ) (ha : P.eval a = 0) :
    ∃ e : OpenPartialHomeomorph (AffineCurve P) ℂ,
      (⟨(a, 0), by simpa using ha.symm⟩ : AffineCurve P) ∈ e.source ∧
      (∀ y, e y = y.val.2) ∧
      HolomorphicOn e.target (fun w => (e.symm w).val.1) ∧
      analyticOrderAt (fun w => (e.symm w).val.1 - a) 0 = (2 : ℕ∞) := by
  let x : AffineCurve P := ⟨(a, 0), by simpa using ha.symm⟩
  obtain ⟨U, W, f, hU, hW, haU, h0W, hf, hf0, hmaps, hgraph, horder⟩ :=
    affine_graph_at_root P hP a ha
  let e := wChart P U W f x hU hW hf hmaps hgraph
  refine ⟨e, ⟨haU, h0W⟩, fun _ => rfl, ⟨hW, ?_⟩, ?_⟩
  · intro w hw
    apply (hf.2 w hw).congr_of_eventuallyEq
    filter_upwards [hW.mem_nhds hw] with y hy
    exact congrArg Prod.fst (wChart_inverse P U W f x hU hW hf hmaps hgraph y hy)
  · have heq : (fun w => (e.symm w).val.1 - a) =ᶠ[𝓝 0] fun w => f w - a := by
      filter_upwards [hW.mem_nhds h0W] with w hw
      exact congrArg (fun q : ℂ × ℂ => q.1 - a)
        (wChart_inverse P U W f x hU hW hf hmaps hgraph w hw)
    exact (analyticOrderAt_congr heq).trans horder

end D12Complex.HyperellipticExample.FiniteGeometry

namespace D12Complex.HyperellipticExample.FiniteGeometry

lemma zChart_inverse_immersion (P : Polynomial ℂ) (U V : Set ℂ) (f : ℂ → ℂ)
    (x₀ : AffineCurve P) (hU : IsOpen U) (hV : IsOpen V)
    (hf : HolomorphicOn U f) (hmaps : MapsTo f U V)
    (hgraph : ∀ z ∈ U, ∀ w ∈ V, w ^ 2 = P.eval z ↔ w = f z)
    (z : ℂ) (hz : z ∈ U) :
    HasDerivAt (fun z => ((zChart P U V f x₀ hU hV hf hmaps hgraph).symm z).val)
      (1, deriv f z) z ∧ (1, deriv f z) ≠ (0 : ℂ × ℂ) := by
  constructor
  · have hd : HasDerivAt (fun z : ℂ => (z, f z)) (1, deriv f z) z :=
      (hasDerivAt_id z).prodMk (hf.2 z hz).hasDerivAt
    apply HasDerivAt.congr_of_eventuallyEq hd
    filter_upwards [hU.mem_nhds hz] with y hy
    exact zChart_inverse P U V f x₀ hU hV hf hmaps hgraph y hy
  · intro h
    have heq := congrArg Prod.fst h
    simp at heq

lemma wChart_inverse_immersion (P : Polynomial ℂ) (U V : Set ℂ) (f : ℂ → ℂ)
    (x₀ : AffineCurve P) (hU : IsOpen U) (hV : IsOpen V)
    (hf : HolomorphicOn V f) (hmaps : MapsTo f V U)
    (hgraph : ∀ w ∈ V, ∀ z ∈ U, w ^ 2 = P.eval z ↔ z = f w)
    (w : ℂ) (hw : w ∈ V) :
    HasDerivAt (fun w => ((wChart P U V f x₀ hU hV hf hmaps hgraph).symm w).val)
      (deriv f w, 1) w ∧ (deriv f w, 1) ≠ (0 : ℂ × ℂ) := by
  constructor
  · have hd : HasDerivAt (fun w : ℂ => (f w, w)) (deriv f w, 1) w :=
      (hf.2 w hw).hasDerivAt.prodMk (hasDerivAt_id w)
    apply HasDerivAt.congr_of_eventuallyEq hd
    filter_upwards [hV.mem_nhds hw] with y hy
    exact wChart_inverse P U V f x₀ hU hV hf hmaps hgraph y hy
  · intro h
    have heq := congrArg Prod.snd h
    simp at heq

end D12Complex.HyperellipticExample.FiniteGeometry

namespace D12Complex.HyperellipticExample.FiniteGeometry

/-- Coordinate charts whose inverse coordinates are both holomorphic. -/

lemma good_zChart (P : Polynomial ℂ) (U V : Set ℂ) (f : ℂ → ℂ) (x₀ : AffineCurve P)
    (hU : IsOpen U) (hV : IsOpen V)
    (hf : HolomorphicOn U f) (hmaps : MapsTo f U V)
    (hgraph : ∀ z ∈ U, ∀ w ∈ V, w ^ 2 = P.eval z ↔ w = f z) :
    GoodCoordinateChart (zChart P U V f x₀ hU hV hf hmaps hgraph) := by
  refine ⟨Or.inl (fun _ => rfl), ⟨hU, ?_⟩, ⟨hU, ?_⟩⟩
  · intro z hz
    apply differentiableAt_id.congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hz] with y hy
    exact congrArg Prod.fst (zChart_inverse P U V f x₀ hU hV hf hmaps hgraph y hy)
  · intro z hz
    apply (hf.2 z hz).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hz] with y hy
    exact congrArg Prod.snd (zChart_inverse P U V f x₀ hU hV hf hmaps hgraph y hy)

lemma good_wChart (P : Polynomial ℂ) (U V : Set ℂ) (f : ℂ → ℂ) (x₀ : AffineCurve P)
    (hU : IsOpen U) (hV : IsOpen V)
    (hf : HolomorphicOn V f) (hmaps : MapsTo f V U)
    (hgraph : ∀ w ∈ V, ∀ z ∈ U, w ^ 2 = P.eval z ↔ z = f w) :
    GoodCoordinateChart (wChart P U V f x₀ hU hV hf hmaps hgraph) := by
  refine ⟨Or.inr (fun _ => rfl), ⟨hV, ?_⟩, ⟨hV, ?_⟩⟩
  · intro w hw
    apply (hf.2 w hw).congr_of_eventuallyEq
    filter_upwards [hV.mem_nhds hw] with y hy
    exact congrArg Prod.fst (wChart_inverse P U V f x₀ hU hV hf hmaps hgraph y hy)
  · intro w hw
    apply differentiableAt_id.congr_of_eventuallyEq
    filter_upwards [hV.mem_nhds hw] with y hy
    exact congrArg Prod.snd (wChart_inverse P U V f x₀ hU hV hf hmaps hgraph y hy)

lemma coordinate_charts_compatible {P : Polynomial ℂ}
    (e f : Surfaces.ComplexChart (AffineCurve P))
    (he : GoodCoordinateChart e.val) (hf : GoodCoordinateChart f.val) :
    Surfaces.CompatibleCharts e f := by
  have hd (e f : OpenPartialHomeomorph (AffineCurve P) ℂ)
      (he : GoodCoordinateChart e) (hf : GoodCoordinateChart f) :
      ∀ z ∈ (e.symm.trans f).source, DifferentiableAt ℂ (e.symm.trans f) z := by
    intro z hz
    change DifferentiableAt ℂ (fun y => f (e.symm y)) z
    rcases hf.1 with hf | hf
    · have heq : (fun y => f (e.symm y)) = fun y => (e.symm y).val.1 :=
        funext fun y => hf _
      rw [heq]
      exact he.2.1.2 z hz.1
    · have heq : (fun y => f (e.symm y)) = fun y => (e.symm y).val.2 :=
        funext fun y => hf _
      rw [heq]
      exact he.2.2.2 z hz.1
  let t := e.val.symm.trans f.val
  exact ⟨⟨t.open_source, hd e.val f.val he hf⟩,
    ⟨t.open_target, hd f.val e.val hf he⟩,
    t.mapsTo, t.symm.mapsTo, t.leftInvOn, t.rightInvOn⟩

lemma exists_good_chart (P : Polynomial ℂ) (hP : Squarefree P) (x : AffineCurve P) :
    ∃ e : OpenPartialHomeomorph (AffineCurve P) ℂ,
      x ∈ e.source ∧ IsDomain e.target ∧ GoodCoordinateChart e := by
  by_cases hx : x.val.2 = 0
  · have ha : P.eval x.val.1 = 0 := by simpa only [hx, zero_pow (by decide : 2 ≠ 0)] using x.property.symm
    obtain ⟨U, W, f, hU, hW, haU, h0W, hf, hf0, hmaps, hgraph, horder⟩ :=
      affine_graph_at_root P hP x.val.1 ha
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds h0W)
    let B : Set ℂ := Metric.ball 0 r
    have hB : IsOpen B := Metric.isOpen_ball
    have h0B : 0 ∈ B := Metric.mem_ball_self hr
    have hfB : HolomorphicOn B f := ⟨hB, fun w hw => hf.2 w (hball hw)⟩
    have hmapB : MapsTo f B U := fun w hw => hmaps (hball hw)
    have hgraphB : ∀ w ∈ B, ∀ z ∈ U, w ^ 2 = P.eval z ↔ z = f w :=
      fun w hw => hgraph w (hball hw)
    let e := wChart P U B f x hU hB hfB hmapB hgraphB
    refine ⟨e, ⟨haU, ?_⟩, ⟨⟨0, h0B⟩, hB, Metric.isPreconnected_ball⟩,
      good_wChart P U B f x hU hB hfB hmapB hgraphB⟩
    simpa only [hx] using h0B
  · obtain ⟨U, V, f, hU, hV, hxU, hxV, hf, hfx, hmaps, hgraph⟩ :=
      affine_graph_at_nonzero P x.val.1 x.val.2 x.property hx
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
    let B : Set ℂ := Metric.ball x.val.1 r
    have hB : IsOpen B := Metric.isOpen_ball
    have hxB : x.val.1 ∈ B := Metric.mem_ball_self hr
    have hfB : HolomorphicOn B f := ⟨hB, fun z hz => hf.2 z (hball hz)⟩
    have hmapB : MapsTo f B V := fun z hz => hmaps (hball hz)
    have hgraphB : ∀ z ∈ B, ∀ w ∈ V, w ^ 2 = P.eval z ↔ w = f z :=
      fun z hz => hgraph z (hball hz)
    let e := zChart P B V f x hB hV hfB hmapB hgraphB
    exact ⟨e, ⟨hxB, hxV⟩, ⟨⟨x.val.1, hxB⟩, hB, Metric.isPreconnected_ball⟩,
      good_zChart P B V f x hB hV hfB hmapB hgraphB⟩

lemma affine_complex_atlas (P : Polynomial ℂ) (hP : Squarefree P) :
    T2Space (AffineCurve P) ∧ SecondCountableTopology (AffineCurve P) ∧
      ∃ A : Set (Surfaces.ComplexChart (AffineCurve P)), Surfaces.IsAtlas A ∧
        ∀ e ∈ A, GoodCoordinateChart e.val := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  let A : Set (Surfaces.ComplexChart (AffineCurve P)) := {e | GoodCoordinateChart e.val}
  refine ⟨A, ⟨?_, ?_⟩, fun _ he => he⟩
  · intro x
    obtain ⟨e, hx, hdom, he⟩ := exists_good_chart P hP x
    exact ⟨⟨e, hdom⟩, he, hx⟩
  · intro e he f hf
    exact coordinate_charts_compatible e f he hf

end D12Complex.HyperellipticExample.FiniteGeometry

namespace D12Complex.HyperellipticExample.FiniteGeometry

/-- Every good coordinate chart is an actual embedded holomorphic immersion. -/
lemma good_chart_immersion {P : Polynomial ℂ}
    (e : OpenPartialHomeomorph (AffineCurve P) ℂ) (he : GoodCoordinateChart e) :
    ∀ t ∈ e.target, ∃ v : ℂ × ℂ, v ≠ 0 ∧
      HasDerivAt (fun t => (e.symm t).val) v t := by
  intro t ht
  let F : ℂ → ℂ := fun y => (e.symm y).val.1
  let G : ℂ → ℂ := fun y => (e.symm y).val.2
  have hF : HasDerivAt F (deriv F t) t := (he.2.1.2 t ht).hasDerivAt
  have hG : HasDerivAt G (deriv G t) t := (he.2.2.2 t ht).hasDerivAt
  refine ⟨(deriv F t, deriv G t), ?_, ?_⟩
  · intro hv
    rcases he.1 with hc | hc
    · have hid : HasDerivAt F 1 t := by
        apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_id t)
        filter_upwards [e.open_target.mem_nhds ht] with y hy
        exact (hc (e.symm y)).symm.trans (e.right_inv hy)
      have hfst : deriv F t = 0 := congrArg Prod.fst hv
      rw [hF.unique hid] at hfst
      exact one_ne_zero hfst
    · have hid : HasDerivAt G 1 t := by
        apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_id t)
        filter_upwards [e.open_target.mem_nhds ht] with y hy
        exact (hc (e.symm y)).symm.trans (e.right_inv hy)
      have hsnd : deriv G t = 0 := congrArg Prod.snd hv
      rw [hG.unique hid] at hsnd
      exact one_ne_zero hsnd
  · simpa only [F, G, Prod.eta] using (HasDerivAt.prodMk hF hG)

lemma smooth_affine_curve (P : Polynomial ℂ) (hP : Squarefree P) :
    T2Space (AffineCurve P) ∧ SecondCountableTopology (AffineCurve P) ∧
      ∃ A : Set (Surfaces.ComplexChart (AffineCurve P)), Surfaces.IsAtlas A ∧
        ∀ e ∈ A, GoodCoordinateChart e.val ∧
          ∀ t ∈ e.val.target, ∃ v : ℂ × ℂ, v ≠ 0 ∧
            HasDerivAt (fun t => (e.val.symm t).val) v t := by
  obtain ⟨hT2, hSC, A, hA, hgood⟩ := affine_complex_atlas P hP
  exact ⟨hT2, hSC, A, hA, fun e he => ⟨hgood e he, good_chart_immersion e.val (hgood e he)⟩⟩

end D12Complex.HyperellipticExample.FiniteGeometry

namespace D12Complex.HyperellipticExample.FiniteGeometry

/-- The finite root parameter is compatible with every good affine atlas and
therefore lies in the associated maximal atlas. Its projection order is two. -/
lemma finite_root_chart_order (P : Polynomial ℂ) (hP : Squarefree P)
    (a : ℂ) (ha : P.eval a = 0)
    (S : Surfaces.RiemannSurface (AffineCurve P))
    (hS : ∀ e ∈ S.atlas, GoodCoordinateChart e.val) :
    let x : AffineCurve P := ⟨(a, 0), by simpa using ha.symm⟩
    ∃ e : Surfaces.ComplexChart (AffineCurve P),
      e ∈ Surfaces.maximalAtlas S.atlas ∧ x ∈ e.val.source ∧ e.val x = 0 ∧
      (∀ y, e.val y = y.val.2) ∧
      analyticOrderAt (fun w => (e.val.symm w).val.1 - a) 0 = (2 : ℕ∞) := by
  dsimp only
  let x : AffineCurve P := ⟨(a, 0), by simpa using ha.symm⟩
  obtain ⟨U, W, f, hU, hW, haU, h0W, hf, hf0, hmaps, hgraph, horder⟩ :=
    affine_graph_at_root P hP a ha
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds h0W)
  let B : Set ℂ := Metric.ball 0 r
  have hB : IsOpen B := Metric.isOpen_ball
  have h0B : 0 ∈ B := Metric.mem_ball_self hr
  have hfB : HolomorphicOn B f := ⟨hB, fun w hw => hf.2 w (hball hw)⟩
  have hmapB : MapsTo f B U := fun w hw => hmaps (hball hw)
  have hgraphB : ∀ w ∈ B, ∀ z ∈ U, w ^ 2 = P.eval z ↔ z = f w :=
    fun w hw => hgraph w (hball hw)
  let e₀ := wChart P U B f x hU hB hfB hmapB hgraphB
  have hdomain : IsDomain e₀.target :=
    ⟨⟨0, h0B⟩, hB, Metric.isPreconnected_ball⟩
  let e : Surfaces.ComplexChart (AffineCurve P) := ⟨e₀, hdomain⟩
  have hgood : GoodCoordinateChart e.val :=
    good_wChart P U B f x hU hB hfB hmapB hgraphB
  refine ⟨e, ?_, ⟨haU, h0B⟩, rfl, fun _ => rfl, ?_⟩
  · intro c hc
    exact coordinate_charts_compatible e c hgood (hS c hc)
  · have heq : (fun w => (e.val.symm w).val.1 - a) =ᶠ[𝓝 0] fun w => f w - a := by
      filter_upwards [hB.mem_nhds h0B] with w hw
      exact congrArg (fun q : ℂ × ℂ => q.1 - a)
        (wChart_inverse P U B f x hU hB hfB hmapB hgraphB w hw)
    exact (analyticOrderAt_congr heq).trans horder

end D12Complex.HyperellipticExample.FiniteGeometry

namespace D12Complex.HyperellipticExample.InfinityCharts

lemma reverse_eval_eq (p : Polynomial ℂ) (t : ℂ) (ht : t ≠ 0) :
    p.reverse.eval t = t ^ p.natDegree * p.eval t⁻¹ := by
  letI : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht)
  have hh := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) t⁻¹ p
  simp only [Polynomial.eval₂_id, invOf_eq_inv, inv_inv] at hh
  calc
    p.reverse.eval t = (p.reverse.eval t * (t⁻¹) ^ p.natDegree) * t ^ p.natDegree := by
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ ht, one_pow, mul_one]
    _ = p.eval t⁻¹ * t ^ p.natDegree := by rw [hh]
    _ = _ := mul_comm _ _

lemma reverse_eval_zero (p : Polynomial ℂ) : p.reverse.eval 0 = p.leadingCoeff := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]

lemma exists_local_nonzero_sqrt (p : Polynomial ℂ) (hp : p ≠ 0)
    (c : ℂ) (hc : c ^ 2 = p.leadingCoeff) :
    ∃ r : ℝ, ∃ h : ℂ → ℂ, 0 < r ∧ HolomorphicOn (Metric.ball 0 r) h ∧
      h 0 = c ∧ ∀ t ∈ Metric.ball 0 r, h t ≠ 0 ∧ (h t)^2 = p.reverse.eval t := by
  have hq : HolomorphicOn Set.univ p.reverse.eval :=
    ⟨isOpen_univ, fun t _ => p.reverse.differentiableAt⟩
  have hq0 : p.reverse.eval 0 ≠ 0 := by
    rw [reverse_eval_zero]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hc0 : c ≠ 0 := by
    intro h
    apply hq0
    rw [reverse_eval_zero, ← hc, h]
    norm_num
  obtain ⟨U,h,h0,hU,hhol,hh0,hroot⟩ := LocalLogarithmsRoots.local_root
    Set.univ p.reverse.eval 0 2 c hq (by trivial) hq0 (by norm_num)
    (by simpa [reverse_eval_zero] using hc)
  have hnonzero : ∀ᶠ t in 𝓝 (0 : ℂ), h t ≠ 0 :=
    ((hhol.2 0 h0).continuousAt.eventually_ne (by simpa [hh0] using hc0))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hhol.1.mem_nhds h0) hnonzero)
  exact ⟨r,h,hr,⟨Metric.isOpen_ball,fun t ht => hhol.2 t (hball ht).1⟩,
    hh0,fun t ht => ⟨(hball ht).2,hroot t (hball ht).1⟩⟩

lemma exists_even_local_sqrt (p : Polynomial ℂ) (hp : p ≠ 0) :
    ∃ r : ℝ, ∃ u : ℂ → ℂ, 0 < r ∧ HolomorphicOn (Metric.ball 0 r) u ∧
      (∀ t : ℂ, u (-t) = u t) ∧
      (u 0)^2 = p.leadingCoeff ∧
      ∀ t ∈ Metric.ball 0 r, u t ≠ 0 ∧ (u t)^2 = p.reverse.eval (t^2) := by
  obtain ⟨c,hc⟩ := IsAlgClosed.exists_pow_nat_eq p.leadingCoeff (n := 2) (by norm_num)
  obtain ⟨R,h,hR,hhol,hh0,hroot⟩ := exists_local_nonzero_sqrt p hp c hc
  have hnear : (fun t : ℂ => t^2) ⁻¹' Metric.ball 0 R ∈ 𝓝 (0 : ℂ) := by
    exact (continuousAt_id.pow 2).preimage_mem_nhds (by simpa using Metric.ball_mem_nhds 0 hR)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r,fun t => h (t^2),hr,⟨Metric.isOpen_ball,?_⟩,?_,?_,?_⟩
  · intro t ht
    exact (hhol.2 (t^2) (hball ht)).comp t (differentiableAt_id.pow 2)
  · intro t
    simp
  · simpa [hh0] using hc
  · intro t ht
    exact hroot (t^2) (hball ht)

lemma even_substitution (p : Polynomial ℂ) (g : ℕ) (hd : p.natDegree = 2*g+2)
    (t v : ℂ) (ht : t ≠ 0) :
    v^2 = p.reverse.eval t ↔ (v / t^(g+1))^2 = p.eval t⁻¹ := by
  rw [reverse_eval_eq p t ht, hd]
  have hpow : t^(2*g+2) = (t^(g+1))^2 := by ring
  rw [hpow]
  constructor
  · intro h
    rw [div_pow, h]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ (pow_ne_zero _ ht))
  · intro h
    rw [div_pow] at h
    exact (div_eq_iff (pow_ne_zero _ (pow_ne_zero _ ht))).mp h |>.trans (mul_comm _ _)

lemma odd_substitution (p : Polynomial ℂ) (g : ℕ) (hd : p.natDegree = 2*g+1)
    (t u : ℂ) (ht : t ≠ 0) :
    u^2 = p.reverse.eval (t^2) ↔ (u / t^(2*g+1))^2 = p.eval (t^2)⁻¹ := by
  rw [reverse_eval_eq p (t^2) (pow_ne_zero _ ht), hd]
  have hpow : (t^2)^(2*g+1) = (t^(2*g+1))^2 := by ring
  rw [hpow]
  constructor
  · intro h
    rw [div_pow,h]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ (pow_ne_zero _ ht))
  · intro h
    rw [div_pow] at h
    exact (div_eq_iff (pow_ne_zero _ (pow_ne_zero _ ht))).mp h |>.trans (mul_comm _ _)

lemma even_sheet_values (p : Polynomial ℂ) (g : ℕ) (hd : p.natDegree = 2*g+2)
    (t h : ℂ) (ht : t ≠ 0) (hh : h^2 = p.reverse.eval t) (w : ℂ) :
    w^2 = p.eval t⁻¹ ↔ w = h / t^(g+1) ∨ w = -(h / t^(g+1)) := by
  rw [← (even_substitution p g hd t h ht).mp hh, sq_eq_sq_iff_eq_or_eq_neg]

lemma odd_opposite_parameter (g : ℕ) (u : ℂ → ℂ) (hu : ∀ t, u (-t) = u t) (t : ℂ) :
    u (-t) / (-t)^(2*g+1) = -(u t / t^(2*g+1)) := by
  rw [hu]
  simp [pow_add, pow_mul, div_neg]

lemma odd_parameter_injective (g : ℕ) (u : ℂ → ℂ) (U : Set ℂ)
    (hu : ∀ t, u (-t) = u t) (hne : ∀ t ∈ U, u t ≠ 0) :
    Set.InjOn (fun t : ℂ => ((t^2)⁻¹, u t / t^(2*g+1))) (U \ {0}) := by
  intro s hs t ht hst
  have hs0 : s ≠ 0 := by simpa using hs.2
  have ht0 : t ≠ 0 := by simpa using ht.2
  have heq : s^2 = t^2 := inv_injective (congrArg Prod.fst hst)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with h | h
  · exact h
  · have hsecond := congrArg Prod.snd hst
    change u s / s^(2*g+1) = u t / t^(2*g+1) at hsecond
    rw [h,odd_opposite_parameter g u hu] at hsecond
    have hz : u t / t^(2*g+1) = 0 := by linear_combination -(1/2:ℂ) * hsecond
    have hz' : u t = 0 := (div_eq_zero_iff).mp hz |>.resolve_right (pow_ne_zero _ ht0)
    exact False.elim (hne t ht.1 hz')

lemma odd_recover_parameter (g : ℕ) (t a : ℂ) (ht : t ≠ 0) (ha : a ≠ 0) :
    a * ((t^2)⁻¹)^g / (a / t^(2*g+1)) = t := by
  have hpow : t^(2*g+1) = (t^2)^g*t := by rw [pow_add,pow_mul]; simp
  rw [hpow]
  field_simp
  rw [← mul_pow]
  simp [ht]

lemma odd_sheet_values (p : Polynomial ℂ) (g : ℕ) (hd : p.natDegree = 2*g+1)
    (u : ℂ → ℂ) (hu : ∀ t, u (-t) = u t) (t : ℂ) (ht : t ≠ 0)
    (hroot : (u t)^2 = p.reverse.eval (t^2)) (w : ℂ) :
    w^2 = p.eval (t^2)⁻¹ ↔
      w = u t / t^(2*g+1) ∨ w = u (-t) / (-t)^(2*g+1) := by
  rw [← (odd_substitution p g hd t (u t) ht).mp hroot,
    sq_eq_sq_iff_eq_or_eq_neg, odd_opposite_parameter g u hu]

lemma odd_parameter_covers (p : Polynomial ℂ) (g : ℕ) (hd : p.natDegree = 2*g+1)
    (r : ℝ) (hr : 0 < r) (u : ℂ → ℂ) (hu : ∀ t, u (-t) = u t)
    (hroot : ∀ t ∈ Metric.ball 0 r, (u t)^2 = p.reverse.eval (t^2))
    (z w : ℂ) (hz : z ≠ 0) (hnorm : ‖z⁻¹‖ < r^2) (hw : w^2 = p.eval z) :
    ∃ t ∈ Metric.ball 0 r, t ≠ 0 ∧
      ((t^2)⁻¹,u t / t^(2*g+1)) = (z,w) := by
  obtain ⟨t,ht⟩ := IsAlgClosed.exists_pow_nat_eq z⁻¹ (n := 2) (by norm_num)
  have ht0 : t ≠ 0 := by
    intro hh
    have := inv_ne_zero hz
    apply this
    simpa [hh] using ht.symm
  have hnormt : ‖t‖^2 = ‖z⁻¹‖ := by rw [← norm_pow,ht]
  have htr : t ∈ Metric.ball 0 r := by
    rw [Metric.mem_ball,dist_zero_right]
    nlinarith [norm_nonneg t]
  have hnt : -t ∈ Metric.ball 0 r := by simpa [Metric.mem_ball,dist_zero_right] using htr
  have hz' : (t^2)⁻¹ = z := by rw [ht,inv_inv]
  have hvalues := (odd_sheet_values p g hd u hu t ht0 (hroot t htr) w).mp
    (by simpa [hz'] using hw)
  rcases hvalues with heq | heq
  · exact ⟨t,htr,ht0,Prod.ext hz' heq.symm⟩
  · exact ⟨-t,hnt,neg_ne_zero.mpr ht0,Prod.ext (by simpa using hz') heq.symm⟩

lemma even_parameter_injective (g : ℕ) (h : ℂ → ℂ) :
    Function.Injective (fun t : ℂ => (t⁻¹,h t / t^(g+1))) := by
  intro s t heq
  exact inv_injective (congrArg Prod.fst heq)

lemma opposite_sheet_values_ne (g : ℕ) (t a : ℂ) (ht : t ≠ 0) (ha : a ≠ 0) :
    a / t^(g+1) ≠ -(a / t^(g+1)) := by
  intro hh
  have hh' : a / t^(g+1) = 0 := by linear_combination (1/2:ℂ) * hh
  exact (div_ne_zero ha (pow_ne_zero _ ht)) hh'

lemma parameter_coordinate_holomorphic (r : ℝ) (u : ℂ → ℂ)
    (hu : HolomorphicOn (Metric.ball 0 r) u) (n : ℕ) :
    HolomorphicOn (Metric.ball 0 r \ {0}) (fun t => u t / t^n) := by
  refine ⟨Metric.isOpen_ball.sdiff isClosed_singleton,?_⟩
  intro t ht
  have ht0 : t ≠ 0 := by simpa using ht.2
  exact (hu.2 t ht.1).div (differentiableAt_id.pow n) (pow_ne_zero _ ht0)

lemma inverse_power_holomorphic (r : ℝ) (n : ℕ) :
    HolomorphicOn (Metric.ball 0 r \ {0}) (fun t : ℂ => (t^n)⁻¹) := by
  refine ⟨Metric.isOpen_ball.sdiff isClosed_singleton,?_⟩
  intro t ht
  have ht0 : t ≠ 0 := by simpa using ht.2
  exact (differentiableAt_id.pow n).inv (pow_ne_zero _ ht0)
end D12Complex.HyperellipticExample.InfinityCharts




namespace D12Complex.HyperellipticExample

theorem quadraticPolynomial_irreducible (P : Polynomial ℂ) (hP : Squarefree P)
    (hd : 1 ≤ P.natDegree) :
    Irreducible ((X : Polynomial (Polynomial ℂ)) ^ 2 - C P) := by
  let F : Polynomial (Polynomial ℂ) := X ^ 2 - C P
  have hm : F.Monic := monic_X_pow_sub_C P (by decide : 2 ≠ 0)
  have hdeg : F.natDegree = 2 := by
    exact natDegree_X_pow_sub_C
  apply (hm.irreducible_iff_roots_eq_zero_of_degree_le_three
    (by omega) (by omega)).mpr
  apply Multiset.eq_zero_iff_forall_notMem.mpr
  intro q hq
  have hroot := (mem_roots hm.ne_zero).mp hq
  have heq : q ^ 2 = P := by
    have he : q ^ 2 - P = 0 := by simpa [F] using hroot
    exact sub_eq_zero.mp he
  have hunit : IsUnit q := hP q (by rw [← heq, pow_two])
  have hPunit : IsUnit P := heq ▸ hunit.pow 2
  have hzero : P.natDegree = 0 := natDegree_eq_zero_of_isUnit hPunit
  omega

end D12Complex.HyperellipticExample

namespace D12Complex.HyperellipticExample
lemma isCompact_affine_core (P : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) :
    IsCompact {q : ℂ × ℂ | q.1 ∈ K ∧ q.2 ^ 2 = P.eval q.1} := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn P.continuous.continuousOn
  let R : ℝ := max C 0 + 1
  have hbound : ∀ z ∈ K, ∀ w : ℂ, w ^ 2 = P.eval z → ‖w‖ ≤ R := by
    intro z hz w hw
    have hh : ‖w‖ ^ 2 ≤ C := by
      calc
        ‖w‖ ^ 2 = ‖w ^ 2‖ := (norm_pow w 2).symm
        _ = ‖P.eval z‖ := by rw [hw]
        _ ≤ C := hC z hz
    have hmax : C ≤ max C 0 := le_max_left _ _
    have hmax0 : 0 ≤ max C 0 := le_max_right _ _
    dsimp [R]
    nlinarith [norm_nonneg w]
  have hclosed : IsClosed {q : ℂ × ℂ | q.1 ∈ K ∧ q.2 ^ 2 = P.eval q.1} :=
    (hK.isClosed.preimage continuous_fst).inter
      (isClosed_eq (continuous_snd.pow 2) (P.continuous.comp continuous_fst))
  apply (hK.prod (isCompact_closedBall (0 : ℂ) R)).of_isClosed_subset hclosed
  intro q hq
  exact ⟨hq.1, by simpa [Metric.mem_closedBall, dist_zero_right] using hbound q.1 hq.1 q.2 hq.2⟩
end D12Complex.HyperellipticExample

namespace D12Complex.HyperellipticExample.FiniteGeometry

abbrev quadraticEquation (P : Polynomial ℂ) : Polynomial (Polynomial ℂ) := X^2 - C P

lemma quadraticEquation_fiber (P : Polynomial ℂ) (z w : ℂ) :
    (AlgebraicCovering.fiber (quadraticEquation P) z).eval w = w^2 - P.eval z := by
  simp [AlgebraicCovering.fiber, Specs.D12Complex.Ch21.FiniteExceptionalSet.fiber_value,
    quadraticEquation]

def ordinaryInclusion (P : Polynomial ℂ) (x : AlgebraicCovering.Curve (quadraticEquation P)) :
    AffineCurve P :=
  ⟨x.val, sub_eq_zero.mp ((quadraticEquation_fiber P x.val.1 x.val.2).symm.trans x.property.2)⟩

lemma continuous_ordinaryInclusion (P : Polynomial ℂ) : Continuous (ordinaryInclusion P) :=
  continuous_subtype_val.subtype_mk _

lemma range_ordinaryInclusion (P : Polynomial ℂ) :
    Set.range (ordinaryInclusion P) =
      {x : AffineCurve P | x.val.1 ∉ AlgebraicCovering.exceptionalSet (quadraticEquation P)} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property.1
  · intro hx
    refine ⟨⟨x.val, hx, ?_⟩, ?_⟩
    · rw [quadraticEquation_fiber]
      exact sub_eq_zero.mpr x.property
    · rfl

lemma affine_fiber_finite (P : Polynomial ℂ) (a : ℂ) :
    Set.Finite {x : AffineCurve P | x.val.1 = a} := by
  have hp : ((X : Polynomial ℂ)^2 - C (P.eval a)) ≠ 0 :=
    (monic_X_pow_sub_C (P.eval a) (by decide : 2 ≠ 0)).ne_zero
  have hroots : Set.Finite {w : ℂ | w^2 = P.eval a} := by
    simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using
      Polynomial.finite_setOfPred_isRoot hp
  apply hroots.of_injOn (f := fun x : AffineCurve P => x.val.2)
  · intro x hx
    change x.val.2 ^ 2 = P.eval a
    exact x.property.trans (congrArg P.eval hx)
  · intro x hx y hy hxy
    apply Subtype.ext
    exact Prod.ext (hx.trans hy.symm) hxy

lemma affine_bad_finite (P : Polynomial ℂ) {E : Set ℂ} (hE : E.Finite) :
    Set.Finite {x : AffineCurve P | x.val.1 ∈ E} := by
  apply Set.Finite.of_finite_fibers (fun x : AffineCurve P => x.val.1)
  · exact hE.subset (by rintro a ⟨x, hx, rfl⟩; exact hx)
  · intro a ha
    exact (affine_fiber_finite P a).subset (by
      intro x hx
      exact hx.2)

lemma affine_finite_compl_dense (P : Polynomial ℂ) (hP : Squarefree P)
    {S : Set (AffineCurve P)} (hS : S.Finite) : Dense Sᶜ := by
  apply dense_iff_inter_open.mpr
  intro U hU hUn
  obtain ⟨x, hxU⟩ := hUn
  obtain ⟨e, hxe, _, _⟩ := exists_good_chart P hP x
  let V : Set ℂ := e.target ∩ e.symm ⁻¹' U
  have hV : IsOpen V := e.isOpen_inter_preimage_symm hU
  have hxV : e x ∈ V := ⟨e.map_source hxe, by
    change e.symm (e x) ∈ U
    rwa [e.left_inv hxe]⟩
  have hVinf : V.Infinite := infinite_of_mem_nhds (e x) (hV.mem_nhds hxV)
  obtain ⟨z, hzV, hzS⟩ := hVinf.exists_notMem_finite (hS.image e)
  refine ⟨e.symm z, hzV.2, ?_⟩
  intro hz
  apply hzS
  exact ⟨e.symm z, hz, e.right_inv hzV.1⟩

lemma denseRange_ordinaryInclusion (P : Polynomial ℂ) (hP : Squarefree P)
    (hE : (AlgebraicCovering.exceptionalSet (quadraticEquation P)).Finite) :
    DenseRange (ordinaryInclusion P) := by
  change Dense (Set.range (ordinaryInclusion P))
  rw [range_ordinaryInclusion]
  exact affine_finite_compl_dense P hP (affine_bad_finite P hE)

lemma affine_connected_of_ordinary (P : Polynomial ℂ) (hP : Squarefree P)
    (hE : (AlgebraicCovering.exceptionalSet (quadraticEquation P)).Finite)
    [ConnectedSpace (AlgebraicCovering.Curve (quadraticEquation P))] :
    ConnectedSpace (AffineCurve P) := by
  letI := (denseRange_ordinaryInclusion P hP hE).preconnectedSpace (continuous_ordinaryInclusion P)
  obtain ⟨x⟩ := (inferInstance : Nonempty (AlgebraicCovering.Curve (quadraticEquation P)))
  letI : Nonempty (AffineCurve P) := ⟨ordinaryInclusion P x⟩
  exact ⟨inferInstance⟩

end D12Complex.HyperellipticExample.FiniteGeometry

namespace D12Complex.HyperellipticExample.FiniteGeometry

lemma affine_connected (P : Polynomial ℂ) (hP : Squarefree P) (hd : 1 ≤ P.natDegree) :
    ConnectedSpace (AffineCurve P) := by
  have hF : Irreducible (quadraticEquation P) := quadraticPolynomial_irreducible P hP hd
  have hdeg : (quadraticEquation P).natDegree = 2 := natDegree_X_pow_sub_C
  have hE := (D12Complex.Ch21.FiniteExceptionalSet.finite_exceptional_set
    (quadraticEquation P) 2 hF hdeg (by decide)).2.1
  letI := (D12Complex.MonodromyTransitive.connected
    (quadraticEquation P) 2 hF hdeg (by decide)).2
  exact affine_connected_of_ordinary P hP hE

lemma exists_affine_surface (P : Polynomial ℂ) (hP : Squarefree P) (hd : 1 ≤ P.natDegree) :
    ∃ S : Surfaces.RiemannSurface (AffineCurve P),
      (∀ e ∈ S.atlas, GoodCoordinateChart e.val) ∧
      Surfaces.ScalarHolomorphic S (fun x => x.val.1) ∧
      Surfaces.ScalarHolomorphic S (fun x => x.val.2) := by
  obtain ⟨hT, hC, A, hA, hgood⟩ := affine_complex_atlas P hP
  let S : Surfaces.RiemannSurface (AffineCurve P) := {
    connected := affine_connected P hP hd
    hausdorff := hT
    secondCountable := hC
    atlas := A
    isAtlas := hA }
  exact ⟨S, hgood, ⟨continuous_subtype_val.fst, fun e he => (hgood e he).2.1⟩,
    ⟨continuous_subtype_val.snd, fun e he => (hgood e he).2.2⟩⟩

end D12Complex.HyperellipticExample.FiniteGeometry

end

noncomputable section
open Set Topology
namespace D12Complex.HyperellipticExample.CompletionGeometry
open FiniteGeometry FiniteEndGluing AnalyticEndPasting Surfaces

/-- Identity change between the two established punctured-disk conventions. -/
def puncturedParameterHomeomorph (r : ℝ) :
    Parameter r ≃ₜ {t : ℂ // t ≠ 0 ∧ ‖t‖ < r} where
  toFun t := ⟨t, norm_pos_iff.mp t.property.1, t.property.2⟩
  invFun t := ⟨t, norm_pos_iff.mpr t.property.1, t.property.2⟩
  left_inv t := Subtype.ext rfl
  right_inv t := Subtype.ext rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def evenTheta {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticEvenEnds.EvenEnds P g) (b : Bool) :
    Parameter e.radius → AffineCurve P :=
  if b then e.minus.parameter ∘ puncturedParameterHomeomorph e.radius
    else e.plus.parameter ∘ puncturedParameterHomeomorph e.radius

def evenChart {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticEvenEnds.EvenEnds P g) (b : Bool) : ComplexChart (AffineCurve P) :=
  if b then e.minus.chart else e.plus.chart

lemma range_evenTheta_false {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticEvenEnds.EvenEnds P g) :
    range (evenTheta e false) = range e.plus.parameter := by
  exact (puncturedParameterHomeomorph e.radius).surjective.range_comp _

lemma range_evenTheta_true {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticEvenEnds.EvenEnds P g) :
    range (evenTheta e true) = range e.minus.parameter := by
  exact (puncturedParameterHomeomorph e.radius).surjective.range_comp _

def evenGluingData {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticEvenEnds.EvenEnds P g) :
    FiniteEndGluing.Data (AffineCurve P) Bool RiemannSphere where
  radius := fun _ => e.radius
  radius_pos := fun _ => e.radius_pos
  theta := evenTheta e
  theta_openEmbedding := by
    intro b
    cases b
    · exact e.plus.openEmbedding.comp (puncturedParameterHomeomorph e.radius).isOpenEmbedding
    · exact e.minus.openEmbedding.comp (puncturedParameterHomeomorph e.radius).isOpenEmbedding
  projection := fun x => sphereFinite x.val.1
  projection_continuous := continuous_sphereFinite.comp continuous_subtype_val.fst
  diskProjection := fun _ t => infinityParametrization t
  diskProjection_continuous := fun _ =>
    continuous_infinityParametrization.comp continuous_subtype_val
  agrees := by
    intro b t
    have ht : (t : ℂ) ≠ 0 := norm_pos_iff.mp t.property.1
    change infinityParametrization (t : ℂ) = sphereFinite (evenTheta e b t).val.1
    rw [infinityParametrization_ne_zero _ ht]
    cases b
    · exact congrArg sphereFinite (e.plus.parameter_z (puncturedParameterHomeomorph e.radius t)).symm
    · exact congrArg sphereFinite (e.minus.parameter_z (puncturedParameterHomeomorph e.radius t)).symm
  avoids := by
    intro x b
    change sphereFinite x.val.1 ≠ infinityParametrization 0
    rw [infinityParametrization_zero]
    exact OnePoint.coe_ne_infty _
  disjoint := by
    intro b c hbc _
    cases b <;> cases c
    · exact False.elim (hbc rfl)
    · rw [range_evenTheta_false, range_evenTheta_true]
      exact e.disjoint
    · rw [range_evenTheta_true, range_evenTheta_false]
      exact e.disjoint.symm
    · exact False.elim (hbc rfl)

lemma goodChart_even {P : Polynomial ℂ} {c : ComplexChart (AffineCurve P)}
    (hc : GoodCoordinateChart c.val) : HyperellipticEvenEnds.CoordinateChart P c := by
  refine ⟨?_, hc.2⟩
  rcases hc.1 with hz | hw
  · exact Or.inl (fun x _ => hz x)
  · exact Or.inr (fun x _ => hw x)

lemma goodChart_odd {P : Polynomial ℂ} {c : ComplexChart (AffineCurve P)}
    (hc : GoodCoordinateChart c.val) : HyperellipticOddEnd.GoodCoordinateChart c := by
  refine ⟨?_, hc.2⟩
  rcases hc.1 with hz | hw
  · exact Or.inl (fun x _ => hz x)
  · exact Or.inr (fun x _ => hw x)

def evenAnalyticParameters {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticEvenEnds.EvenEnds P g) (S : RiemannSurface (AffineCurve P))
    (hS : ∀ c ∈ S.atlas, GoodCoordinateChart c.val) :
    AnalyticParameters (evenGluingData e) S where
  chart := evenChart e
  source := by
    intro b
    cases b
    · exact e.plus.chart_source.trans (range_evenTheta_false e).symm
    · exact e.minus.chart_source.trans (range_evenTheta_true e).symm
  target := by
    intro b
    cases b
    · rw [show evenChart e false = e.plus.chart from rfl, e.plus.chart_target]
      ext t
      simp [HyperellipticEvenEnds.parameterDomain, norm_pos_iff, evenGluingData]
    · rw [show evenChart e true = e.minus.chart from rfl, e.minus.chart_target]
      ext t
      simp [HyperellipticEvenEnds.parameterDomain, norm_pos_iff, evenGluingData]
  apply_theta := by
    intro b t
    change Parameter e.radius at t
    have ht : (t : ℂ) ∈ HyperellipticEvenEnds.parameterDomain e.radius :=
      (puncturedParameterHomeomorph e.radius t).property
    cases b
    · change e.plus.chart.val (e.plus.parameter (puncturedParameterHomeomorph e.radius t)) = _
      have hr := e.plus.right_inverse (t : ℂ) ht
      rw [e.plus.chart_inverse] at hr
      exact hr
    · change e.minus.chart.val (e.minus.parameter (puncturedParameterHomeomorph e.radius t)) = _
      have hr := e.minus.right_inverse (t : ℂ) ht
      rw [e.minus.chart_inverse] at hr
      exact hr
  symm_parameter := by
    intro b t
    cases b
    · exact e.plus.chart_inverse _ _
    · exact e.minus.chart_inverse _ _
  compatible := by
    intro b c hc
    cases b
    · exact e.plus.compatible c (goodChart_even (hS c hc))
    · exact e.minus.compatible c (goodChart_even (hS c hc))

def oddTheta {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticOddEnd.Data P g) : Parameter e.r → AffineCurve P :=
  e.theta ∘ puncturedParameterHomeomorph e.r

lemma range_oddTheta {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticOddEnd.Data P g) : range (oddTheta e) = range e.theta :=
  (puncturedParameterHomeomorph e.r).surjective.range_comp _

def oddGluingData {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticOddEnd.Data P g) :
    FiniteEndGluing.Data (AffineCurve P) Unit RiemannSphere where
  radius := fun _ => e.r
  radius_pos := fun _ => e.r_pos
  theta := fun _ => oddTheta e
  theta_openEmbedding := fun _ =>
    e.theta_openEmbedding.comp (puncturedParameterHomeomorph e.r).isOpenEmbedding
  projection := fun x => sphereFinite x.val.1
  projection_continuous := continuous_sphereFinite.comp continuous_subtype_val.fst
  diskProjection := fun _ t => infinityParametrization ((t : ℂ) ^ 2)
  diskProjection_continuous := fun _ =>
    continuous_infinityParametrization.comp (continuous_subtype_val.pow 2)
  agrees := by
    intro j t
    have ht : (t : ℂ) ≠ 0 := norm_pos_iff.mp t.property.1
    change infinityParametrization ((t : ℂ) ^ 2) = sphereFinite (oddTheta e t).val.1
    rw [infinityParametrization_ne_zero _ (pow_ne_zero 2 ht)]
    let q : HyperellipticOddEnd.puncturedDisk e.r := ⟨t, ht, t.property.2⟩
    change sphereFinite ((q : ℂ) ^ 2)⁻¹ = sphereFinite (e.theta q).val.1
    rw [e.theta_eq q]
    rw [e.chart_symm_z _ q.property]
    simp only [inv_pow]
  avoids := by
    intro x j
    change sphereFinite x.val.1 ≠ infinityParametrization ((0 : ℂ) ^ 2)
    rw [zero_pow (by decide), infinityParametrization_zero]
    exact OnePoint.coe_ne_infty _
  disjoint := by
    intro j k hjk _
    exact False.elim (hjk (Subsingleton.elim _ _))

def oddAnalyticParameters {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticOddEnd.Data P g) (S : RiemannSurface (AffineCurve P))
    (hS : ∀ c ∈ S.atlas, GoodCoordinateChart c.val) :
    AnalyticParameters (oddGluingData e) S where
  chart := fun _ => e.chart
  source := fun _ => e.chart_source.trans (e.theta_range.symm.trans (range_oddTheta e).symm)
  target := by
    intro j
    rw [e.chart_target]
    ext t
    simp [HyperellipticOddEnd.puncturedDisk, norm_pos_iff, oddGluingData]
  apply_theta := by
    intro j t
    change Parameter e.r at t
    let q : HyperellipticOddEnd.puncturedDisk e.r :=
      ⟨t, norm_pos_iff.mp t.property.1, t.property.2⟩
    change e.chart.val (e.theta q) = (q : ℂ)
    rw [e.theta_eq q]
    exact e.chart.val.right_inv (by rw [e.chart_target]; exact q.property)
  symm_parameter := fun _ t => (e.theta_eq (puncturedParameterHomeomorph e.r t)).symm
  compatible := fun _ c hc => e.compatible c (goodChart_odd (hS c hc))

lemma exists_even_completion {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticEvenEnds.EvenEnds P g) (S : RiemannSurface (AffineCurve P))
    (hS : ∀ c ∈ S.atlas, GoodCoordinateChart c.val) :
    letI := (evenGluingData e).topology
    Nonempty (Completion (evenGluingData e) S) :=
  AnalyticEndPasting.analytic_end_pasting _ _ (evenAnalyticParameters e S hS)

lemma exists_odd_completion {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticOddEnd.Data P g) (S : RiemannSurface (AffineCurve P))
    (hS : ∀ c ∈ S.atlas, GoodCoordinateChart c.val) :
    letI := (oddGluingData e).topology
    Nonempty (Completion (oddGluingData e) S) :=
  AnalyticEndPasting.analytic_end_pasting _ _ (oddAnalyticParameters e S hS)

end D12Complex.HyperellipticExample.CompletionGeometry
end

noncomputable section
open Set Topology

namespace D12Complex.HyperellipticExample.CompletionCompactness

universe u v w

/-- A compact old core and finitely many small closed end disks cover the exact
finite-end attachment. The hypotheses concern only the old parameter maps. -/
theorem compactSpace_of_core_and_ends
    {E : Type u} {J : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace B] [Finite J]
    (d : FiniteEndGluing.Data E J B)
    (K : Set E) (hK : IsCompact K)
    (s : J → ℝ) (hs0 : ∀ j, 0 ≤ s j) (hs : ∀ j, s j < d.radius j)
    (hcover : ∀ x : E, x ∉ K → ∃ (j : J) (t : FiniteEndGluing.Parameter (d.radius j)),
      d.theta j t = x ∧ ‖(t : ℂ)‖ ≤ s j) :
    letI := d.topology; CompactSpace (E ⊕ J) := by
  letI := d.topology
  have hc : IsCompact (Sum.inl '' K : Set (E ⊕ J)) :=
    hK.image d.old_openEmbedding.continuous
  have hd (j : J) : IsCompact (range (d.closedDiskMap j (s j) (hs j))) := by
    rw [d.range_closedDiskMap]
    exact d.compact_parameter_disk j (hs j)
  have hfull : (univ : Set (E ⊕ J)) =
      Sum.inl '' K ∪ ⋃ j, range (d.closedDiskMap j (s j) (hs j)) := by
    apply Subset.antisymm
    · rintro (x | j) _
      · by_cases hx : x ∈ K
        · exact Or.inl ⟨x, hx, rfl⟩
        · obtain ⟨j, t, rfl, ht⟩ := hcover x hx
          refine Or.inr (mem_iUnion.mpr ⟨j, ?_⟩)
          refine ⟨⟨t, ?_⟩, ?_⟩
          · simpa only [Metric.mem_closedBall, dist_zero_right] using ht
          · exact d.psi_puncture j t
      · refine Or.inr (mem_iUnion.mpr ⟨j, ?_⟩)
        refine ⟨⟨0, ?_⟩, ?_⟩
        · simpa only [Metric.mem_closedBall, dist_self] using hs0 j
        · exact d.psi_center j
    · exact subset_univ _
  exact isCompact_univ_iff.mp (hfull ▸ hc.union (isCompact_iUnion hd))

/-- The bounded-root compact core is also compact in the actual affine subtype. -/
lemma isCompact_affine_core_subtype (P : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) :
    IsCompact {q : FiniteGeometry.AffineCurve P | q.val.1 ∈ K} := by
  apply IsEmbedding.subtypeVal.isInducing.isCompact_iff.mpr
  convert isCompact_affine_core P hK using 1
  ext q
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨hq, q.property⟩
  · rintro ⟨hq, heq⟩
    exact ⟨⟨q, heq⟩, hq, rfl⟩

/-- It is enough to cover a sufficiently small reciprocal-base exterior by
parameters lying in strictly smaller closed parameter disks. -/
theorem compactSpace_of_affine_exterior
    (P : Polynomial ℂ) {J : Type v} {B : Type w}
    [TopologicalSpace B] [Finite J]
    (d : FiniteEndGluing.Data (FiniteGeometry.AffineCurve P) J B)
    (ρ : ℝ) (hρ : 0 < ρ)
    (s : J → ℝ) (hs0 : ∀ j, 0 ≤ s j) (hs : ∀ j, s j < d.radius j)
    (hcover : ∀ q : FiniteGeometry.AffineCurve P,
      q.val.1 ≠ 0 → ‖q.val.1⁻¹‖ < ρ →
      ∃ (j : J) (t : FiniteEndGluing.Parameter (d.radius j)),
        d.theta j t = q ∧ ‖(t : ℂ)‖ ≤ s j) :
    letI := d.topology; CompactSpace (FiniteGeometry.AffineCurve P ⊕ J) := by
  apply compactSpace_of_core_and_ends d
    {q | q.val.1 ∈ Metric.closedBall (0 : ℂ) ρ⁻¹}
    (isCompact_affine_core_subtype P (isCompact_closedBall _ _)) s hs0 hs
  intro q hq
  have hlarge : ρ⁻¹ < ‖q.val.1‖ := by
    simpa only [mem_setOf_eq, Metric.mem_closedBall, dist_zero_right, not_le] using hq
  have hq0 : q.val.1 ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hlarge
    exact (not_lt_of_ge (inv_nonneg.mpr hρ.le)) hlarge
  apply hcover q hq0
  rw [norm_inv]
  exact (inv_lt_comm₀ (norm_pos_iff.mpr hq0) hρ).mpr hlarge

end D12Complex.HyperellipticExample.CompletionCompactness
end

noncomputable section
open Set Topology

namespace D12Complex.HyperellipticExample.CompletionGeometry
open FiniteGeometry FiniteEndGluing AnalyticEndPasting Surfaces CompletionCompactness

lemma even_compact {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticEvenEnds.EvenEnds P g) :
    letI := (evenGluingData e).topology
    CompactSpace (AffineCurve P ⊕ Bool) := by
  have hhalf : 0 < e.radius / 2 := half_pos e.radius_pos
  have hhalflt : e.radius / 2 < e.radius := half_lt_self e.radius_pos
  apply compactSpace_of_affine_exterior P (evenGluingData e) (e.radius / 2) hhalf
    (fun _ => e.radius / 2) (fun _ => hhalf.le) (fun _ => hhalflt)
  intro q hz hq
  have hq' : q ∈ range e.plus.parameter ∪ range e.minus.parameter := by
    rw [e.exterior]
    exact ⟨hz, hq.trans hhalflt⟩
  rcases hq' with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · refine ⟨false, (puncturedParameterHomeomorph e.radius).symm t, ?_, ?_⟩
    · change e.plus.parameter (puncturedParameterHomeomorph e.radius
        ((puncturedParameterHomeomorph e.radius).symm t)) = _
      rfl
    · change ‖(t : ℂ)‖ ≤ e.radius / 2
      rw [e.plus.parameter_z, inv_inv] at hq
      exact hq.le
  · refine ⟨true, (puncturedParameterHomeomorph e.radius).symm t, ?_, ?_⟩
    · change e.minus.parameter (puncturedParameterHomeomorph e.radius
        ((puncturedParameterHomeomorph e.radius).symm t)) = _
      rfl
    · change ‖(t : ℂ)‖ ≤ e.radius / 2
      rw [e.minus.parameter_z, inv_inv] at hq
      exact hq.le

lemma odd_compact {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticOddEnd.Data P g) :
    letI := (oddGluingData e).topology
    CompactSpace (AffineCurve P ⊕ Unit) := by
  have hhalf : 0 < e.r / 2 := half_pos e.r_pos
  have hhalflt : e.r / 2 < e.r := half_lt_self e.r_pos
  have hρ : 0 < (e.r / 2) ^ 2 := sq_pos_of_pos hhalf
  apply compactSpace_of_affine_exterior P (oddGluingData e) ((e.r / 2) ^ 2) hρ
    (fun _ => e.r / 2) (fun _ => hhalf.le) (fun _ => hhalflt)
  intro q hz hq
  have hq' : q ∈ HyperellipticOddEnd.exterior P e.r := by
    refine ⟨hz, ?_⟩
    have hsq : (e.r / 2) ^ 2 < e.r ^ 2 := by nlinarith [e.r_pos]
    exact hq.trans hsq
  rw [← e.theta_range] at hq'
  obtain ⟨t, rfl⟩ := hq'
  refine ⟨(), (puncturedParameterHomeomorph e.r).symm t, ?_, ?_⟩
  · change e.theta (puncturedParameterHomeomorph e.r
      ((puncturedParameterHomeomorph e.r).symm t)) = _
    rfl
  · change ‖(t : ℂ)‖ ≤ e.r / 2
    have hb : (e.theta t).val.1⁻¹ = (t : ℂ) ^ 2 := by
      rw [e.theta_eq]
      exact e.inverse_base _ t.property
    rw [hb, norm_pow] at hq
    nlinarith [norm_nonneg (t : ℂ)]

end D12Complex.HyperellipticExample.CompletionGeometry
end

noncomputable section
open Set Filter
open scoped Topology
namespace D12Complex.HyperellipticExample.CompletionGeometry

/-- The actual polar expression, with its prescribed sphere value at zero. -/
lemma scalarMeromorphicOn_pole_expression (r : ℝ) (u : ℂ → ℂ) (n : ℕ)
    (hn : 0 < n) (hu : HolomorphicOn (Metric.ball 0 r) u)
    (hne : ∀ t ∈ Metric.ball 0 r, u t ≠ 0) :
    ScalarMeromorphicOn (Metric.ball 0 r)
      (fun t : ℂ => if t = 0 then sphereInfty else sphereFinite (u t / t^n)) := by
  let F : ℂ → RiemannSphere := fun t => if t = 0 then sphereInfty else sphereFinite (u t / t^n)
  have hfinite : ∀ t : ℂ, t ≠ 0 → F t ≠ sphereInfty := by
    intro t ht
    simp only [F, if_neg ht]
    exact OnePoint.coe_ne_infty _
  have hp : PlaneSphereHolomorphicOn (Metric.ball 0 r) F := by
    refine ⟨Metric.isOpen_ball, ?_⟩
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      have hg : HolomorphicGermAt (fun z : ℂ => z ^ n / u z) 0 := by
        refine ⟨Metric.ball 0 r, ht, Metric.isOpen_ball, ?_⟩
        intro z hz
        exact (differentiableAt_id.pow n).div (hu.2 z hz) (hne z hz)
      apply planeSphereHolomorphicAt_of_reciprocal_lift hg
      · simp [hn.ne']
      · filter_upwards [Metric.isOpen_ball.mem_nhds ht] with z hz
        by_cases hz0 : z = 0
        · simp [F, hz0, hn.ne', infinityParametrization_zero]
        · change (if z = 0 then sphereInfty else sphereFinite (u z / z ^ n)) = infinityParametrization (z ^ n / u z)
          rw [if_neg hz0, infinityParametrization_ne_zero _
            (div_ne_zero (pow_ne_zero n hz0) (hne z hz)), inv_div]
    · apply planeSphereHolomorphicAt_of_finite_germ
      · have hg : HolomorphicGermAt (fun z : ℂ => u z / z ^ n) t := by
          refine ⟨Metric.ball 0 r ∩ {0}ᶜ, ⟨ht, ht0⟩,
            Metric.isOpen_ball.inter isOpen_compl_singleton, ?_⟩
          intro z hz
          exact (hu.2 z hz.1).div (differentiableAt_id.pow n) (pow_ne_zero n hz.2)
        apply hg.congr
        filter_upwards [isOpen_compl_singleton.mem_nhds ht0] with z hz
        change u z / z ^ n = finiteCoordinate (if z = 0 then sphereInfty else sphereFinite (u z / z ^ n))
        rw [if_neg (show z ≠ 0 from hz), finiteCoordinate_sphereFinite]
      · filter_upwards [isOpen_compl_singleton.mem_nhds ht0] with z hz
        exact hfinite z hz
  apply plane_scalarMeromorphic_of_no_infty_germ hp
  intro t ht hinf
  have hf : ∀ᶠ z in 𝓝[≠] t, F z ≠ sphereInfty := by
    by_cases ht0 : t = 0
    · subst t
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hfinite z hz
    · filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds ht0)] with z hz
      exact hfinite z hz
  exact ((hinf.filter_mono nhdsWithin_le_nhds).and hf).exists.elim fun z hz => hz.2 hz.1

end D12Complex.HyperellipticExample.CompletionGeometry
end

noncomputable section
open Set Filter Topology
open scoped Topology
namespace D12Complex.HyperellipticExample.CompletionMultiplicity
open Surfaces FiniteEndGluing AnalyticEndPasting

universe u v w

/-- A change of the source parameter preserves the order of any scalar germ. -/
lemma scalar_order_chart_independent
    {X : Type u} [TopologicalSpace X] {e e' : ComplexChart X}
    {f : X → ℂ} {a : X} (he : CompatibleCharts e' e)
    (ha : a ∈ e.val.source) (ha' : a ∈ e'.val.source) :
    analyticOrderAt (fun t => f (e'.val.symm t) - f a) (e'.val a) =
      analyticOrderAt (fun t => f (e.val.symm t) - f a) (e.val a) := by
  let G : ℂ → ℂ := fun t => e.val (e'.val.symm t)
  have hG := compatibleCharts_germ he ha' ha
  have hG' := compatibleCharts_deriv_ne_zero he ha' ha
  have hGa : G (e'.val a) = e.val a := by
    simp only [G, e'.val.left_inv ha']
  have hEq : (fun t => f (e.val.symm (G t)) - f a) =ᶠ[𝓝 (e'.val a)]
      (fun t => f (e'.val.symm t) - f a) := by
    filter_upwards [(e'.val.tendsto_symm ha') (e.val.open_source.mem_nhds ha)] with t ht
    change e'.val.symm t ∈ e.val.source at ht
    simp only [G, e.val.left_inv ht]
  rw [← analyticOrderAt_congr hEq]
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := fun t => f (e.val.symm t) - f a) hG.analyticAt hG'
  change analyticOrderAt (fun t => f (e.val.symm (G t)) - f a) (e'.val a) =
    analyticOrderAt (fun t => f (e.val.symm t) - f a) (G (e'.val a)) at hcomp
  simpa only [hGa] using hcomp

section Completion
variable {E : Type u} {J : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace B]
  (d : Data E J B) (S : RiemannSurface E)
  [TopologicalSpace (E ⊕ J)] (C : Completion d S)

lemma parameterChart_mem_atlas (j : J) : C.parameterChart j ∈ C.surface.atlas := by
  rw [C.atlas_eq]
  exact Or.inr ⟨j, rfl⟩

lemma parameterChart_mem_source (j : J) : Sum.inr j ∈ (C.parameterChart j).val.source := by
  rw [C.parameter_source]
  exact ⟨d.center j, d.psi_center j⟩

lemma transported_finite_order (f : E → ℂ) (F : E ⊕ J → RiemannSphere)
    (hF : ∀ x, F (Sum.inl x) = sphereFinite (f x))
    (e : ComplexChart E) (he : e ∈ maximalAtlas S.atlas)
    (x : E) (hx : x ∈ e.val.source) (m : ℕ)
    (horder : analyticOrderAt (fun t => f (e.val.symm t) - f x) (e.val x) = m) :
    ∃ e' : ComplexChart (E ⊕ J), e' ∈ maximalAtlas C.surface.atlas ∧
      Sum.inl x ∈ e'.val.source ∧ e'.val (Sum.inl x) = e.val x ∧
      (∀ y, e'.val (Sum.inl y) = e.val y) ∧
      (∀ t, finiteCoordinate (F (e'.val.symm t)) = f (e.val.symm t)) ∧
      analyticOrderAt (fun t => finiteCoordinate (F (e'.val.symm t)) - f x)
        (e'.val (Sum.inl x)) = m := by
  let e' := transportChart C.oldEmbedding e
  have he' : e' ∈ maximalAtlas C.surface.atlas := (C.old_structure e).mp he
  have hx' : Sum.inl x ∈ e'.val.source :=
    (transportChart_mem_source_iff C.oldEmbedding e x).mpr hx
  have hv : e'.val (Sum.inl x) = e.val x := transportChart_apply C.oldEmbedding e x
  have hcoord : ∀ t, finiteCoordinate (F (e'.val.symm t)) = f (e.val.symm t) := by
    intro t
    change finiteCoordinate (F (Sum.inl (e.val.symm t))) = _
    rw [hF, finiteCoordinate_sphereFinite]
  refine ⟨e', he', hx', hv, fun y => transportChart_apply C.oldEmbedding e y, hcoord, ?_⟩
  simpa only [hv, hcoord] using horder


/-- The same finite centered order is visible in every compatible completed chart. -/
lemma transported_finite_order_all_charts (f : E → ℂ) (F : E ⊕ J → RiemannSphere)
    (hF : ∀ x, F (Sum.inl x) = sphereFinite (f x))
    (e : ComplexChart E) (he : e ∈ maximalAtlas S.atlas)
    (x : E) (hx : x ∈ e.val.source) (m : ℕ)
    (horder : analyticOrderAt (fun t => f (e.val.symm t) - f x) (e.val x) = m)
    (e' : ComplexChart (E ⊕ J)) (he' : e' ∈ maximalAtlas C.surface.atlas)
    (hx' : Sum.inl x ∈ e'.val.source) :
    analyticOrderAt (fun t => finiteCoordinate (F (e'.val.symm t)) - f x)
      (e'.val (Sum.inl x)) = m := by
  obtain ⟨e₀, he₀, hx₀, hv₀, happly₀, hcoord₀, horder₀⟩ :=
    transported_finite_order d S C f F hF e he x hx m horder
  have hcompat := (maximalAtlas_isAtlas C.surface.isAtlas).2 e' he' e₀ he₀
  have hchange := scalar_order_chart_independent
    (f := fun x => finiteCoordinate (F x)) hcompat hx₀ hx'
  have hvalue : finiteCoordinate (F (Sum.inl x)) = f x := by
    rw [hF, finiteCoordinate_sphereFinite]
  rw [hvalue] at hchange
  exact hchange.trans horder₀

end Completion

section Infinity
variable {E : Type u} {J : Type v} [TopologicalSpace E]
  (d : Data E J RiemannSphere) (S : RiemannSurface E)
  [TopologicalSpace (E ⊕ J)] (C : Completion d S)

/-- The actual reciprocal projection in the completed disk is exactly the
prescribed local power, including its value at the attached center. -/
lemma infinity_coordinate_formula (j : J) (m : ℕ)
    (hproj : ∀ t : FullDisk (d.radius j),
      d.diskProjection j t = infinityParametrization ((t : ℂ) ^ m)) :
    ∀ t ∈ (C.parameterChart j).val.target,
      infinityCoordinate (d.extendedProjection ((C.parameterChart j).val.symm t)) = t ^ m := by
  intro t ht
  have ht' : t ∈ FullDisk (d.radius j) := by rwa [C.parameter_target] at ht
  rw [C.parameter_symm j ⟨t, ht'⟩]
  have h := congrFun (d.extendedProjection_psi j) ⟨t, ht'⟩
  change d.extendedProjection (d.psi j ⟨t, ht'⟩) = _ at h
  rw [h, hproj]
  exact infinityChart.right_inv (mem_univ _)

lemma infinity_projection_value (j : J) (m : ℕ) (hm : 0 < m)
    (hproj : ∀ t : FullDisk (d.radius j),
      d.diskProjection j t = infinityParametrization ((t : ℂ) ^ m)) :
    d.extendedProjection (Sum.inr j) = sphereInfty := by
  change d.diskProjection j (d.center j) = sphereInfty
  rw [hproj]
  simp only [Data.center, zero_pow (Nat.ne_of_gt hm),
    infinityParametrization_zero]

lemma infinity_parameter_order (j : J) (m : ℕ)
    (hproj : ∀ t : FullDisk (d.radius j),
      d.diskProjection j t = infinityParametrization ((t : ℂ) ^ m)) :
    analyticOrderAt
      (fun t => infinityCoordinate (d.extendedProjection ((C.parameterChart j).val.symm t)))
      0 = m := by
  have hEq : (fun t => infinityCoordinate
      (d.extendedProjection ((C.parameterChart j).val.symm t))) =ᶠ[𝓝 0]
      (fun t : ℂ => t ^ m) := by
    have h0 : (0 : ℂ) ∈ (C.parameterChart j).val.target := by
      rw [C.parameter_target]
      exact Metric.mem_ball_self (d.radius_pos j)
    filter_upwards [(C.parameterChart j).val.open_target.mem_nhds h0] with t ht
    exact infinity_coordinate_formula d S C j m hproj t ht
  rw [analyticOrderAt_congr hEq]
  have hp : ((fun z : ℂ => z - 0) ^ m) = (fun t : ℂ => t ^ m) := by
    funext t
    simp
  rw [← hp]
  exact analyticOrderAt_centeredMonomial

/-- The computed order holds in every compatible source chart. The target
coordinate is the canonical reciprocal chart, valid at the actual infinity image. -/
lemma infinity_order_all_charts (j : J) (m : ℕ) (hm : 0 < m)
    (hproj : ∀ t : FullDisk (d.radius j),
      d.diskProjection j t = infinityParametrization ((t : ℂ) ^ m))
    (e : ComplexChart (E ⊕ J)) (he : e ∈ maximalAtlas C.surface.atlas)
    (ha : Sum.inr j ∈ e.val.source) :
    analyticOrderAt
      (fun t => infinityCoordinate (d.extendedProjection (e.val.symm t)))
      (e.val (Sum.inr j)) = m := by
  let e₀ := C.parameterChart j
  have he₀ : e₀ ∈ C.surface.atlas := parameterChart_mem_atlas d S C j
  have ha₀ : Sum.inr j ∈ e₀.val.source := parameterChart_mem_source d S C j
  have hzero : infinityCoordinate (d.extendedProjection (Sum.inr j)) = 0 := by
    rw [infinity_projection_value d j m hm hproj]
    rfl
  have hchange := scalar_order_chart_independent (f := fun x => infinityCoordinate
      (d.extendedProjection x)) (he e₀ he₀) ha₀ ha
  rw [hzero] at hchange
  dsimp only [e₀] at hchange
  simp only [sub_zero, C.parameter_center] at hchange
  exact hchange.trans (infinity_parameter_order d S C j m hproj)

end Infinity
end D12Complex.HyperellipticExample.CompletionMultiplicity
end

noncomputable section
open Set Filter Topology
namespace D12Complex.HyperellipticExample.CompletionMultiplicity
open Surfaces FiniteEndGluing AnalyticEndPasting FiniteGeometry

universe v

/-- The completed affine root has the original w coordinate and z-order two. -/
lemma completed_finite_root_chart_order
    (P : Polynomial ℂ) (hP : Squarefree P) (a : ℂ) (ha : P.eval a = 0)
    (S : RiemannSurface (AffineCurve P))
    (hS : ∀ e ∈ S.atlas, GoodCoordinateChart e.val)
    {J : Type v} (d : Data (AffineCurve P) J RiemannSphere)
    (F : AffineCurve P ⊕ J → RiemannSphere)
    (hF : ∀ x, F (Sum.inl x) = sphereFinite x.val.1)
    [TopologicalSpace (AffineCurve P ⊕ J)] (C : Completion d S) :
    let x : AffineCurve P := ⟨(a, 0), by simpa using ha.symm⟩
    ∃ e : ComplexChart (AffineCurve P ⊕ J),
      e ∈ maximalAtlas C.surface.atlas ∧ Sum.inl x ∈ e.val.source ∧
      e.val (Sum.inl x) = 0 ∧
      (∀ y : AffineCurve P, e.val (Sum.inl y) = y.val.2) ∧
      analyticOrderAt (fun t => finiteCoordinate
        (F (e.val.symm t)) - a) 0 = (2 : ℕ∞) := by
  dsimp only
  let x : AffineCurve P := ⟨(a, 0), by simpa using ha.symm⟩
  obtain ⟨e₀, he₀, hx₀, hv₀, happly₀, horder₀⟩ :=
    finite_root_chart_order P hP a ha S hS
  have hxvalue : x.val.1 = a := rfl
  have hxparam : e₀.val x = 0 := hv₀
  have horderOld : analyticOrderAt (fun t => (e₀.val.symm t).val.1 - x.val.1)
      (e₀.val x) = (2 : ℕ∞) := by
    rw [hxparam, hxvalue]
    exact horder₀
  have hfinite : ∀ y, F (Sum.inl y) = sphereFinite y.val.1 := hF
  obtain ⟨e, he, hx, hv, happly, hcoord, horder⟩ :=
    transported_finite_order d S C (fun y => y.val.1) F
      hfinite e₀ he₀ x hx₀ 2 horderOld
  refine ⟨e, he, hx, hv.trans hv₀, fun y => (happly y).trans (happly₀ y), ?_⟩
  simpa [hv, hxparam, hxvalue] using horder

lemma completed_finite_root_order_all_charts
    (P : Polynomial ℂ) (hP : Squarefree P) (a : ℂ) (ha : P.eval a = 0)
    (S : RiemannSurface (AffineCurve P))
    (hS : ∀ e ∈ S.atlas, GoodCoordinateChart e.val)
    {J : Type v} (d : Data (AffineCurve P) J RiemannSphere)
    (F : AffineCurve P ⊕ J → RiemannSphere)
    (hF : ∀ x, F (Sum.inl x) = sphereFinite x.val.1)
    [TopologicalSpace (AffineCurve P ⊕ J)] (C : Completion d S) :
    let x : AffineCurve P := ⟨(a, 0), by simpa using ha.symm⟩
    ∀ e : ComplexChart (AffineCurve P ⊕ J), e ∈ maximalAtlas C.surface.atlas →
      Sum.inl x ∈ e.val.source →
      analyticOrderAt (fun t => finiteCoordinate
        (F (e.val.symm t)) - a) (e.val (Sum.inl x)) = (2 : ℕ∞) := by
  dsimp only
  let x : AffineCurve P := ⟨(a, 0), by simpa using ha.symm⟩
  intro e he hx
  obtain ⟨e₀, he₀, hx₀, hv₀, happly₀, horder₀⟩ :=
    finite_root_chart_order P hP a ha S hS
  have hxvalue : x.val.1 = a := rfl
  have hxparam : e₀.val x = 0 := hv₀
  have horderOld : analyticOrderAt (fun t => (e₀.val.symm t).val.1 - x.val.1)
      (e₀.val x) = (2 : ℕ∞) := by
    rw [hxparam, hxvalue]
    exact horder₀
  exact transported_finite_order_all_charts d S C (fun y => y.val.1)
    F hF e₀ he₀ x hx₀ 2
      horderOld e he hx

end D12Complex.HyperellipticExample.CompletionMultiplicity
end

noncomputable section
open Set Topology
namespace D12Complex.HyperellipticExample.CompletionGeometry
open Surfaces FiniteGeometry FiniteEndGluing AnalyticEndPasting CompletionMultiplicity

/-- Package the constructed final topology and analytic attachment together
with its scalar functions. Compactness is discharged by the exterior cover. -/
def compactificationOfPasting
    (P : Polynomial ℂ) (hP : Squarefree P) {J : Type}
    (d : Data (AffineCurve P) J RiemannSphere)
    (S : RiemannSurface (AffineCurve P))
    (hS : ∀ e ∈ S.atlas, GoodCoordinateChart e.val)
    (hproj : ∀ x, d.projection x = sphereFinite x.val.1)
    (hinf : ∀ j, d.diskProjection j (d.center j) = sphereInfty)
    (W : AffineCurve P ⊕ J → RiemannSphere)
    (hw : ∀ x, W (Sum.inl x) = sphereFinite x.val.2)
    (hwInf : ∀ j, W (Sum.inr j) = sphereInfty) :
    letI := d.topology
    (C : Completion d S) → CompactSpace (AffineCurve P ⊕ J) →
    ScalarMeromorphic C.surface d.extendedProjection →
    ScalarMeromorphic C.surface W → Compactification P J := by
  letI := d.topology
  intro C hcompact hzmer hwmer
  refine {
    affineSurface := S
    good_affine := hS
    surface := C.surface
    compact := hcompact
    old_open := C.oldEmbedding
    old_dense := d.dense_old
    old_holomorphic := C.old_holomorphic
    old_locallyBiholomorphic := C.old_locallyBiholomorphic
    Z := d.extendedProjection
    W := W
    z_old := hproj
    w_old := hw
    z_infinity := hinf
    w_infinity := hwInf
    z_meromorphic := hzmer
    w_meromorphic := hwmer
    z_holomorphic := scalarMeromorphic_sphereValuedHolomorphic C.surface _ hzmer
    infinity_fiber := ?_
    finite_root_order := ?_ }
  · ext x
    cases x with
    | inl x =>
      change d.projection x = sphereInfty ↔ _
      rw [hproj]
      simp only [sphereFinite, sphereInfty, OnePoint.coe_ne_infty, mem_range, reduceCtorEq, exists_false]
    | inr j =>
      change d.diskProjection j (d.center j) = sphereInfty ↔ _
      rw [hinf]
      exact iff_of_true rfl (mem_range_self j)
  · intro a ha
    obtain ⟨e, he, hx, hv, _, ho⟩ := completed_finite_root_chart_order
      P hP a ha S hS d d.extendedProjection hproj C
    exact ⟨e, he, hx, hv, ho⟩

end D12Complex.HyperellipticExample.CompletionGeometry
end

noncomputable section
open Set
namespace D12Complex.HyperellipticExample.CompletionGeometry
open FiniteGeometry FiniteEndGluing AnalyticEndPasting Surfaces

/-- The sphere-valued polar expression, including the actual value at its center. -/
def poleExpression (u : ℂ → ℂ) (n : ℕ) (t : ℂ) : RiemannSphere :=
  if t = 0 then sphereInfty else sphereFinite (u t / t ^ n)

def evenWExpression {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticEvenEnds.EvenEnds P g) (b : Bool) : ℂ → RiemannSphere :=
  if b then poleExpression (fun t => -e.root t) (g + 1)
    else poleExpression e.root (g + 1)

def oddWExpression {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticOddEnd.Data P g) (_j : Unit) : ℂ → RiemannSphere :=
  poleExpression (fun t => e.h (t ^ 2)) (2 * g + 1)

def evenCompletedW {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticEvenEnds.EvenEnds P g) : AffineCurve P ⊕ Bool → RiemannSphere :=
  paste (fun x : AffineCurve P => sphereFinite x.val.2) (evenWExpression e)

def oddCompletedW {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticOddEnd.Data P g) : AffineCurve P ⊕ Unit → RiemannSphere :=
  paste (fun x : AffineCurve P => sphereFinite x.val.2) (oddWExpression e)

lemma evenW_match {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticEvenEnds.EvenEnds P g) (b : Bool)
    (t : Parameter ((evenGluingData e).radius b)) :
    evenWExpression e b t = sphereFinite (((evenGluingData e).theta b t).val.2) := by
  change Parameter e.radius at t
  have ht : (t : ℂ) ≠ 0 := norm_pos_iff.mp t.property.1
  cases b
  · change (if (t : ℂ) = 0 then sphereInfty else sphereFinite (e.root t / (t : ℂ) ^ (g + 1))) = _
    rw [if_neg ht]
    exact congrArg sphereFinite (e.plus.parameter_w (puncturedParameterHomeomorph e.radius t)).symm
  · change (if (t : ℂ) = 0 then sphereInfty else sphereFinite (-e.root t / (t : ℂ) ^ (g + 1))) = _
    rw [if_neg ht]
    exact congrArg sphereFinite (e.minus.parameter_w (puncturedParameterHomeomorph e.radius t)).symm

lemma oddW_match {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticOddEnd.Data P g) (j : Unit)
    (t : Parameter ((oddGluingData e).radius j)) :
    oddWExpression e j t = sphereFinite (((oddGluingData e).theta j t).val.2) := by
  change Parameter e.r at t
  have ht : (t : ℂ) ≠ 0 := norm_pos_iff.mp t.property.1
  let q : HyperellipticOddEnd.puncturedDisk e.r := ⟨t, ht, t.property.2⟩
  change (if (q : ℂ) = 0 then sphereInfty else
    sphereFinite (e.h ((q : ℂ) ^ 2) / (q : ℂ) ^ (2 * g + 1))) = sphereFinite (e.theta q).val.2
  rw [if_neg ht, e.theta_eq q, e.chart_symm_w _ q.property]
  simp only [div_eq_mul_inv, inv_pow]
  exact congrArg sphereFinite (mul_comm _ _)

lemma evenWExpression_meromorphic {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticEvenEnds.EvenEnds P g) (b : Bool) :
    ScalarMeromorphicOn (Metric.ball 0 e.radius) (evenWExpression e b) := by
  cases b
  · exact scalarMeromorphicOn_pole_expression e.radius e.root (g + 1)
      (Nat.succ_pos _) e.root_holomorphic e.root_nonzero
  · exact scalarMeromorphicOn_pole_expression e.radius (fun t => -e.root t) (g + 1)
      (Nat.succ_pos _) ⟨e.root_holomorphic.1, fun t ht => (e.root_holomorphic.2 t ht).neg⟩
      (fun t ht => neg_ne_zero.mpr (e.root_nonzero t ht))

lemma oddWExpression_meromorphic {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticOddEnd.Data P g) (j : Unit) :
    ScalarMeromorphicOn (Metric.ball 0 e.r) (oddWExpression e j) :=
  scalarMeromorphicOn_pole_expression e.r (fun t => e.h (t ^ 2)) (2 * g + 1)
    (Nat.succ_pos _) e.u_holomorphic e.u_nonzero

lemma evenCompletedW_old {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticEvenEnds.EvenEnds P g) (x : AffineCurve P) :
    evenCompletedW e (Sum.inl x) = sphereFinite x.val.2 := rfl

lemma oddCompletedW_old {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticOddEnd.Data P g) (x : AffineCurve P) :
    oddCompletedW e (Sum.inl x) = sphereFinite x.val.2 := rfl

lemma evenCompletedW_infty {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticEvenEnds.EvenEnds P g) (b : Bool) :
    evenCompletedW e (Sum.inr b) = sphereInfty := by
  cases b <;> simp [evenCompletedW, paste, evenWExpression, poleExpression]

lemma oddCompletedW_infty {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticOddEnd.Data P g) (j : Unit) :
    oddCompletedW e (Sum.inr j) = sphereInfty := by
  simp [oddCompletedW, paste, oddWExpression, poleExpression]

lemma even_projection_meromorphic {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticEvenEnds.EvenEnds P g) (S : RiemannSurface (AffineCurve P))
    [TopologicalSpace (AffineCurve P ⊕ Bool)]
    (C : Completion (evenGluingData e) S)
    (hz : ScalarHolomorphic S (fun x => x.val.1)) :
    ScalarMeromorphic C.surface (evenGluingData e).extendedProjection := by
  have hG : ∀ b : Bool, ScalarMeromorphicOn (Metric.ball 0 e.radius)
      (fun t : ℂ => infinityParametrization t) := by
    intro b
    simpa only [pow_one] using CompactCompletion.scalarMeromorphicOn_infinity_power e.radius 1 (by decide)
  have hm := C.meromorphic_paste
    (fun x : AffineCurve P => sphereFinite x.val.1)
    (fun _ t => infinityParametrization t)
    (CompactCompletion.scalarMeromorphic_of_scalarHolomorphic S _ hz)
    hG (fun b t => (evenGluingData e).agrees b t)
  have heq : paste (fun x : AffineCurve P => sphereFinite x.val.1)
      (fun (_ : Bool) t => infinityParametrization t) = (evenGluingData e).extendedProjection := by
    funext x
    cases x <;> rfl
  rw [heq] at hm
  exact hm

lemma odd_projection_meromorphic {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticOddEnd.Data P g) (S : RiemannSurface (AffineCurve P))
    [TopologicalSpace (AffineCurve P ⊕ Unit)]
    (C : Completion (oddGluingData e) S)
    (hz : ScalarHolomorphic S (fun x => x.val.1)) :
    ScalarMeromorphic C.surface (oddGluingData e).extendedProjection := by
  have hG : ∀ j : Unit, ScalarMeromorphicOn (Metric.ball 0 e.r)
      (fun t : ℂ => infinityParametrization (t ^ 2)) := fun _ =>
    CompactCompletion.scalarMeromorphicOn_infinity_power e.r 2 (by decide)
  have hm := C.meromorphic_paste
    (fun x : AffineCurve P => sphereFinite x.val.1)
    (fun _ t => infinityParametrization (t ^ 2))
    (CompactCompletion.scalarMeromorphic_of_scalarHolomorphic S _ hz)
    hG (fun j t => (oddGluingData e).agrees j t)
  have heq : paste (fun x : AffineCurve P => sphereFinite x.val.1)
      (fun (_ : Unit) t => infinityParametrization (t ^ 2)) = (oddGluingData e).extendedProjection := by
    funext x
    cases x <;> rfl
  rw [heq] at hm
  exact hm

lemma even_w_meromorphic {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticEvenEnds.EvenEnds P g) (S : RiemannSurface (AffineCurve P))
    [TopologicalSpace (AffineCurve P ⊕ Bool)]
    (C : Completion (evenGluingData e) S)
    (hw : ScalarHolomorphic S (fun x => x.val.2)) :
    ScalarMeromorphic C.surface (evenCompletedW e) :=
  C.meromorphic_paste _ _ (CompactCompletion.scalarMeromorphic_of_scalarHolomorphic S _ hw)
    (evenWExpression_meromorphic e) (evenW_match e)

lemma odd_w_meromorphic {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticOddEnd.Data P g) (S : RiemannSurface (AffineCurve P))
    [TopologicalSpace (AffineCurve P ⊕ Unit)]
    (C : Completion (oddGluingData e) S)
    (hw : ScalarHolomorphic S (fun x => x.val.2)) :
    ScalarMeromorphic C.surface (oddCompletedW e) :=
  C.meromorphic_paste _ _ (CompactCompletion.scalarMeromorphic_of_scalarHolomorphic S _ hw)
    (oddWExpression_meromorphic e) (oddW_match e)

lemma even_w_chart_formula {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticEvenEnds.EvenEnds P g) (S : RiemannSurface (AffineCurve P))
    [TopologicalSpace (AffineCurve P ⊕ Bool)]
    (C : Completion (evenGluingData e) S) (b : Bool)
    (t : ℂ) (ht : t ∈ (C.parameterChart b).val.target) :
    evenCompletedW e ((C.parameterChart b).val.symm t) = evenWExpression e b t := by
  have htd : t ∈ FullDisk ((evenGluingData e).radius b) := by
    rwa [C.parameter_target] at ht
  rw [C.parameter_symm b ⟨t, htd⟩]
  exact paste_psi (evenGluingData e) _ _ (evenW_match e) b ⟨t, htd⟩

lemma odd_w_chart_formula {P : Polynomial ℂ} {g : ℕ}
    (e : HyperellipticOddEnd.Data P g) (S : RiemannSurface (AffineCurve P))
    [TopologicalSpace (AffineCurve P ⊕ Unit)]
    (C : Completion (oddGluingData e) S) (j : Unit)
    (t : ℂ) (ht : t ∈ (C.parameterChart j).val.target) :
    oddCompletedW e ((C.parameterChart j).val.symm t) = oddWExpression e j t := by
  have htd : t ∈ FullDisk ((oddGluingData e).radius j) := by
    rwa [C.parameter_target] at ht
  rw [C.parameter_symm j ⟨t, htd⟩]
  exact paste_psi (oddGluingData e) _ _ (oddW_match e) j ⟨t, htd⟩

end D12Complex.HyperellipticExample.CompletionGeometry
end

noncomputable section
open Set Topology
namespace D12Complex.HyperellipticExample
open Surfaces FiniteGeometry FiniteEndGluing AnalyticEndPasting
open CompletionGeometry CompletionMultiplicity

/-- The smooth double cover with its two genuine, unramified infinity centers. -/
theorem even_compact_completion :
    Specs.D12Complex.Ch21.HyperellipticExample.even_compact_completion_type := by
  intro P g hP hd
  obtain ⟨S, hS, hz, hw⟩ := exists_affine_surface P hP (by omega)
  obtain ⟨e⟩ := HyperellipticEvenEnds.even_ends P g hP hd
  let d := evenGluingData e
  letI := d.topology
  obtain ⟨C⟩ := exists_even_completion e S hS
  have hinf : ∀ b, d.diskProjection b (d.center b) = sphereInfty := by
    intro b
    exact infinityParametrization_zero
  let c : Compactification P Bool := compactificationOfPasting P hP d S hS
    (fun _ => rfl) hinf (evenCompletedW e) (evenCompletedW_old e)
    (evenCompletedW_infty e) C (even_compact e)
    (even_projection_meromorphic e S C hz) (even_w_meromorphic e S C hw)
  refine ⟨d.topology, c, e.radius, e.root, C.parameterChart, e.radius_pos,
    e.root_holomorphic, ?_, e.root_zero_square, ?_, ?_⟩
  · intro t ht
    exact ⟨e.root_nonzero t ht, e.root_square t ht⟩
  · rw [C.parameter_source false, C.parameter_source true]
    exact d.disjoint_range_psi false true (by decide) rfl
  · intro b
    refine ⟨parameterChart_mem_atlas d S C b, parameterChart_mem_source d S C b,
      C.parameter_target b, C.parameter_center b, ?_, ?_⟩
    · intro t ht
      have ht' : t ∈ (C.parameterChart b).val.target := by
        rw [C.parameter_target]
        exact ht
      constructor
      · change d.extendedProjection ((C.parameterChart b).val.symm t) = _
        calc
          _ = d.extendedProjection (d.psi b ⟨t, ht⟩) :=
            congrArg d.extendedProjection (C.parameter_symm b ⟨t, ht⟩)
          _ = infinityParametrization t := congrFun (d.extendedProjection_psi b) ⟨t, ht⟩
      · change evenCompletedW e ((C.parameterChart b).val.symm t) = _
        exact (even_w_chart_formula e S C b t ht').trans (by cases b <;> rfl)
    · intro f hf ha
      change analyticOrderAt
        (fun t => infinityCoordinate (d.extendedProjection (f.val.symm t)))
        (f.val (Sum.inr b)) = 1
      apply infinity_order_all_charts d S C b 1 (by decide) _ f hf ha
      intro t
      change infinityParametrization (t : ℂ) = infinityParametrization ((t : ℂ) ^ 1)
      rw [pow_one]

/-- The smooth double cover with its single ramified infinity center. -/
theorem odd_compact_completion :
    Specs.D12Complex.Ch21.HyperellipticExample.odd_compact_completion_type := by
  intro P g hP hd
  obtain ⟨S, hS, hz, hw⟩ := exists_affine_surface P hP (by omega)
  obtain ⟨e⟩ := HyperellipticOddEnd.exists_odd_end P g hP hd
  let d := oddGluingData e
  letI := d.topology
  obtain ⟨C⟩ := exists_odd_completion e S hS
  have hinf : ∀ j, d.diskProjection j (d.center j) = sphereInfty := by
    intro j
    change infinityParametrization ((0 : ℂ) ^ 2) = sphereInfty
    rw [zero_pow (by decide), infinityParametrization_zero]
  let c : Compactification P Unit := compactificationOfPasting P hP d S hS
    (fun _ => rfl) hinf (oddCompletedW e) (oddCompletedW_old e)
    (oddCompletedW_infty e) C (odd_compact e)
    (odd_projection_meromorphic e S C hz) (odd_w_meromorphic e S C hw)
  refine ⟨d.topology, c, e.r, (fun t => e.h (t ^ 2)), C.parameterChart (),
    e.r_pos, e.u_holomorphic, e.u_even, ?_, ?_,
    parameterChart_mem_atlas d S C (), parameterChart_mem_source d S C (),
    C.parameter_target (), C.parameter_center (), ?_, ?_⟩
  · intro t ht
    exact ⟨e.u_nonzero t ht, e.u_square t ht⟩
  · simpa only [zero_pow (by decide : 2 ≠ 0)] using e.h_zero_square
  · intro t ht
    have ht' : t ∈ (C.parameterChart ()).val.target := by
      rw [C.parameter_target]
      exact ht
    constructor
    · change d.extendedProjection ((C.parameterChart ()).val.symm t) = _
      calc
        _ = d.extendedProjection (d.psi () ⟨t, ht⟩) :=
          congrArg d.extendedProjection (C.parameter_symm () ⟨t, ht⟩)
        _ = infinityParametrization (t ^ 2) := congrFun (d.extendedProjection_psi ()) ⟨t, ht⟩
    · change oddCompletedW e ((C.parameterChart ()).val.symm t) = _
      exact odd_w_chart_formula e S C () t ht'
  · intro f hf ha
    change analyticOrderAt
      (fun t => infinityCoordinate (d.extendedProjection (f.val.symm t)))
      (f.val (Sum.inr ())) = 2
    exact infinity_order_all_charts d S C () 2 (by decide) (fun _ => rfl) f hf ha

/-- Every positive-degree square-free hyperelliptic curve has a compact completion. -/
theorem compact_completion :
    Specs.D12Complex.Ch21.HyperellipticExample.compact_completion_type := by
  intro P hP hd
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' P.natDegree
  · have heven : P.natDegree = 2 * (k - 1) + 2 := by omega
    obtain ⟨top, hc⟩ := even_compact_completion P (k - 1) hP heven
    letI := top
    obtain ⟨c, _⟩ := hc
    exact ⟨Bool, inferInstance, top, ⟨c⟩⟩
  · obtain ⟨top, hc⟩ := odd_compact_completion P k hP hk
    letI := top
    obtain ⟨c, _⟩ := hc
    exact ⟨Unit, inferInstance, top, ⟨c⟩⟩

end D12Complex.HyperellipticExample
end
