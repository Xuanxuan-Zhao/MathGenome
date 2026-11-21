import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.RegularLevelsAndGraphs
import MathGenome.Internal.MultivariableAnalysis.D04.C14.GraphTransitionsAndIntrinsicBoundary
import MathGenome.Internal.MultivariableAnalysis.D04.C04.ImplicitFunction
import Mathlib.LinearAlgebra.Dimension.Free
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace D04
namespace RegularLevels
open Specs.D04.C14.RegularLevelsAndGraphs.Model
open private implicit_neighborhood from MathGenome.Internal.MultivariableAnalysis.D04.C04.ImplicitFunction

/-- A surjective linear map supplies transverse coordinates. Rank-nullity
identifies its kernel with the requested k-dimensional parameter space. -/
theorem surjective_splitting {k q n : ℕ} (A : E n →L[ℝ] E q)
    (hA : Function.Surjective A) (hdim : k + q = n) :
    ∃ e : E n ≃L[ℝ] E k × E q, ∀ x, (e x).2 = A x := by
  obtain ⟨R, hR⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hA)
  have hdimK : Module.finrank ℝ A.ker = k := by
    have hh := A.toLinearMap.finrank_range_add_finrank_ker
    have htop : LinearMap.range A.toLinearMap = ⊤ := LinearMap.range_eq_top.mpr hA
    rw [htop, finrank_top] at hh
    simp only [finrank_euclideanSpace_fin] at hh
    have hh' : q + Module.finrank ℝ A.ker = n := hh
    omega
  let K : A.ker ≃L[ℝ] E k :=
    (LinearEquiv.ofFinrankEq (R := ℝ) A.ker (E k)
      (hdimK.trans (finrank_euclideanSpace_fin.symm))).toContinuousLinearEquiv
  let e := (ContinuousLinearEquiv.equivOfRightInverse A R
    (fun y => congrArg (fun f : E q →L[ℝ] E q => f y) hR)).trans
    ((ContinuousLinearEquiv.refl ℝ (E q)).prodCongr K) |>.trans
      (ContinuousLinearEquiv.prodComm ℝ (E q) (E k))
  exact ⟨e, fun _ => rfl⟩


/-- The standard graph parametrization is C^r and has injective derivative. -/
theorem graph_regular {r : ℕ∞ω} {k q n : ℕ}
    (e : E n ≃L[ℝ] E k × E q) (A : Set (E k)) (h : E k → E q)
    (hr : ManifoldRegularity r) (hA : IsOpen A) (hh : ContDiffOn ℝ r h A) :
    FullRankLocalExtension r A (fun v => e.symm (v, h v)) := by
  apply (open_fullRankLocalExtension_iff _ _ hA).mpr
  refine ⟨e.symm.contDiff.comp_contDiffOn (contDiffOn_id.prodMk hh), ?_⟩
  intro v hv
  have hd := ((hh.contDiffAt (hA.mem_nhds hv)).differentiableAt
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hr.1))).hasFDerivAt
  have hdθ := e.symm.hasFDerivAt.comp v ((hasFDerivAt_id v).prodMk hd)
  change Function.Injective (fderiv ℝ (⇑e.symm ∘ (fun v => (id v, h v))) v)
  rw [hdθ.fderiv]
  intro z w hzw
  have hz := e.symm.injective hzw
  exact congrArg Prod.fst hz

/-- Graph chart with an arbitrary prescribed ambient open neighborhood. -/
def graph_chart {r : ℕ∞ω} {k q n : ℕ}
    (e : E n ≃L[ℝ] E k × E q) (A : Set (E k)) (h : E k → E q)
    (M O : Set (E n)) (hr : ManifoldRegularity r)
    (hA : IsOpen A) (hh : ContDiffOn ℝ r h A) (hO : IsOpen O)
    (heq : M ∩ O = graphSet e A h) : EmbeddedChart r k n M where
  half := false
  half_pos := by simp
  source := A
  source_open := ⟨A, hA, by simp [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace]⟩
  ambient := O
  ambient_open := hO
  toFun v := e.symm (v, h v)
  invFun x := (e x).1
  map_source := by
    intro v hv
    rw [heq]
    simp [graphSet, hv]
  map_target := by
    intro x hx
    rw [heq] at hx
    exact hx.1
  left_inv := by intro v _; simp
  right_inv := by
    intro x hx
    rw [heq] at hx
    apply e.injective
    rw [e.apply_symm_apply]
    exact Prod.ext rfl hx.2.symm
  continuous_toFun := e.symm.continuous.comp_continuousOn (continuousOn_id.prodMk hh.continuousOn)
  continuous_invFun := (continuous_fst.comp e.continuous).continuousOn
  regular := graph_regular e A h hr hA hh

/-- Full-rank zero sets have an open Euclidean chart at each point. -/
theorem regular_zero_set : Specs.D04.C14.RegularLevelsAndGraphs.regular_zero_setType := by
  intro r k n O g hr hkn hO hg hRank
  refine ⟨hr, hkn, ?_⟩
  rintro a ⟨ha, hga⟩
  change g a = 0 at hga
  have hsurj : Function.Surjective (fderiv ℝ g a) := by
    apply LinearMap.range_eq_top.mp
    exact Submodule.eq_top_of_finrank_eq ((hRank a ha hga).trans finrank_euclideanSpace_fin.symm)
  obtain ⟨e, he⟩ := surjective_splitting (k := k) (fderiv ℝ g a) hsurj
    (Nat.add_sub_of_le hkn)
  let W := e.symm ⁻¹' O
  let G := g ∘ e.symm
  have hW : IsOpen W := hO.preimage e.symm.continuous
  have hG : ContDiffOn ℝ r G W := hg.comp e.symm.contDiff.contDiffOn (fun _ hx => hx)
  have hdg := ((hg.contDiffAt (hO.mem_nhds ha)).differentiableAt
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hr.1))).hasFDerivAt
  have hdg' : HasFDerivAt g (fderiv ℝ g a) (e.symm (e a)) := by simpa using hdg
  have hdG := hdg'.comp (e a) e.symm.hasFDerivAt
  have hDy : Specs.D04.C04.ImplicitFunction.Model.solvedDerivative G (e a) =
      ContinuousLinearMap.id ℝ (E (n-k)) := by
    apply ContinuousLinearMap.ext
    intro w
    change fderiv ℝ G (e a) (0,w) = w
    have hdG' : HasFDerivAt G ((fderiv ℝ g a).comp e.symm.toContinuousLinearMap) (e a) := by
      simpa using hdG
    rw [hdG'.fderiv]
    exact (he (e.symm (0,w))).symm.trans (congrArg Prod.snd (e.apply_symm_apply (0,w)))
  have hGa : G (e a) = 0 := by simpa [G] using hga
  obtain ⟨A, B, φ, hI, hφ⟩ := implicit_neighborhood W G (e a).1 (e a).2 0 hr.1 hW hG
    (by simpa [W] using ha) hGa (by rw [hDy]; exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩)
  obtain ⟨hA, hB, haA, haB, hABW, hmap, hφa, hiff, _⟩ := hI
  let T := e ⁻¹' (A ×ˢ B)
  have hT : IsOpen T := (hA.prod hB).preimage e.continuous
  have heq : (O ∩ g ⁻¹' {0}) ∩ T = graphSet e A φ := by
    ext x
    constructor
    · rintro ⟨⟨hxO, hxg⟩, hxT⟩
      refine ⟨hxT.1, (hiff (e x).1 hxT.1 (e x).2 hxT.2).mp ?_⟩
      simpa [G] using hxg
    · rintro ⟨hxA, hxφ⟩
      have hxB : (e x).2 ∈ B := hxφ ▸ hmap hxA
      refine ⟨⟨?_, ?_⟩, hxA, hxB⟩
      · have := hABW ⟨hxA, hxB⟩
        simpa [W] using this
      · have := (hiff (e x).1 hxA (e x).2 hxB).mpr hxφ
        simpa [G] using this
  refine ⟨graph_chart e A φ _ T hr hA hφ hT heq, (e a).1, rfl, haA, ?_⟩
  change e.symm ((e a).1, φ (e a).1) = a
  rw [hφa]
  exact e.symm_apply_apply a


/-- The graph equation has the full block derivative, with an identity
solved-variable block even when that block has dimension zero. -/
theorem graph_defining : Specs.D04.C14.RegularLevelsAndGraphs.graph_definingType := by
  intro r k q n e A h hr hA hh
  let P := (ContinuousLinearMap.fst ℝ (E k) (E q)).comp e.toContinuousLinearMap
  let Q := (ContinuousLinearMap.snd ℝ (E k) (E q)).comp e.toContinuousLinearMap
  have hreg : ContDiffOn ℝ r (graphDefining e h) {x | (e x).1 ∈ A} :=
    Q.contDiff.contDiffOn.sub (hh.comp P.contDiff.contDiffOn (fun _ hx => hx))
  refine ⟨hreg, ?_, ?_⟩
  · ext x
    simp only [graphSet, graphDefining, mem_ofPred_eq, mem_inter_iff, mem_preimage,
      mem_singleton_iff, sub_eq_zero]
  · intro x hx
    have hd := ((hh.contDiffAt (hA.mem_nhds hx)).differentiableAt
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hr.1))).hasFDerivAt
    have hdg : HasFDerivAt (graphDefining e h) (Q - (fderiv ℝ h (P x)).comp P) x :=
      Q.hasFDerivAt.sub (hd.comp x P.hasFDerivAt)
    refine ⟨hdg, ?_, ?_⟩
    · intro v w
      rw [hdg.fderiv]
      simp [P, Q]
    · intro w
      refine ⟨e.symm (0,w), ?_⟩
      rw [hdg.fderiv]
      simp [P, Q]

/-- Graphs are boundaryless embedded manifolds, in any linear product coordinates. -/
theorem graph_manifold : Specs.D04.C14.RegularLevelsAndGraphs.graph_manifoldType := by
  intro r k q e A h hr hA hh
  let O := {x | (e x).1 ∈ A}
  have hO : IsOpen O := hA.preimage (continuous_fst.comp e.continuous)
  have heq : graphSet e A h ∩ O = graphSet e A h := by
    apply inter_eq_left.mpr
    exact fun _ hx => hx.1
  refine ⟨hr, Nat.le_add_right k q, ?_⟩
  intro x hx
  refine ⟨graph_chart e A h _ O hr hA hh hO heq, (e x).1, rfl, hx.1, ?_⟩
  change e.symm ((e x).1, h (e x).1) = x
  apply e.injective
  rw [e.apply_symm_apply]
  exact Prod.ext rfl hx.2.symm

/-- The full-rank/range-dimension bridge for a finite Euclidean target. -/
theorem range_finrank_of_surjective {n q : ℕ} (A : E n →L[ℝ] E q)
    (hA : Function.Surjective A) : Module.finrank ℝ (LinearMap.range A.toLinearMap) = q := by
  rw [LinearMap.range_eq_top.mpr hA, finrank_top, finrank_euclideanSpace_fin]

theorem regular_zero_dim_discrete :
    Specs.D04.C14.RegularLevelsAndGraphs.regular_zero_dim_discreteType := by
  intro r n O g hr hO hg hRank
  have hM := regular_zero_set (k := 0) O g hr (Nat.zero_le n) hO hg
    (fun x hx hz => range_finrank_of_surjective _ (hRank x hx hz))
  have hEmb : IsEmbeddedManifold r 0 (O ∩ g ⁻¹' {0}) := (boundaryless_iff.mp hM).1
  exact ((zero_manifold_iff_discrete r _).mp hEmb).2

theorem zero_codimension : Specs.D04.C14.RegularLevelsAndGraphs.zero_codimensionType := by
  intro r n O g hr hO
  have heq : O ∩ g ⁻¹' {0} = O := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff,
      Subsingleton.elim (g x) 0, and_true]
  refine ⟨heq, ?_⟩
  let e : E n ≃L[ℝ] E n × E 0 :=
    (ContinuousLinearEquiv.prodUnique ℝ (E n) (E 0)).symm
  have hgraph : graphSet e O (fun _ => (0 : E 0)) = O := by
    ext x
    simp only [graphSet, mem_ofPred_eq, e, ContinuousLinearEquiv.prodUnique_symm_apply]
    exact and_iff_left (Subsingleton.elim _ _)
  have hgr := graph_manifold (q := 0) e O (fun _ => (0 : E 0)) hr hO contDiffOn_const
  rwa [hgraph] at hgr


/-- A coordinate projection onto distinct coordinates is onto, including k=0. -/
theorem coordinateProjection_surjective {k n : ℕ} (s : Fin k ↪ Fin n) :
    Function.Surjective (coordinateProjection s) := by
  classical
  intro y
  refine ⟨WithLp.toLp 2 (Function.extend s (fun i => y i) (fun _ => 0)), ?_⟩
  ext i
  change Function.extend s (fun i => y i) (fun _ => 0) (s i) = y i
  exact s.injective.extend_apply _ _ i

/-- Converse regular-level description at any interior parameter point.
The graph is first restricted to an open parameter neighborhood; this is
necessary when the original chart also contains boundary parameters. -/
theorem chart_local_regular_level :
    Specs.D04.C14.RegularLevelsAndGraphs.chart_local_regular_levelType := by
  intro r k n M c u hr hkn hu hi
  obtain ⟨s, W, f, X, Y, q, h⟩ := local_graph_and_ambient_inverse
    c.source c.toFun u c.half hr hkn c.half_pos c.source_open c.regular hu
  obtain ⟨hX, hY, huX, hfuY, hXW, hbij, hqmap, hleft, hright, _⟩ := h.inverse
  let P := coordinateProjection s
  have hPuY : P (c.toFun u) ∈ Y := by
    rw [← h.extension_agrees ⟨hu, hXW huX⟩]
    exact hfuY
  have hqu : q (P (c.toFun u)) = u := h.inverse_left ⟨hu, huX⟩
  obtain ⟨U, hUsub, hU, huU⟩ := mem_nhds_iff.mp (EmbeddedChart.source_mem_nhds c hu hi)
  have hqcont : ContinuousAt q (P (c.toFun u)) :=
    h.inverse_regular.continuousOn.continuousAt (hY.mem_nhds hPuY)
  have hqU : q ⁻¹' U ∈ 𝓝 (P (c.toFun u)) :=
    hqcont.preimage_mem_nhds (by rw [hqu]; exact hU.mem_nhds huU)
  obtain ⟨Z, hZsub, hZ, hPuZ⟩ := mem_nhds_iff.mp (inter_mem (hY.mem_nhds hPuY) hqU)
  have hZY : Z ⊆ Y := fun _ hz => (hZsub hz).1
  have hqV : MapsTo q Z c.source := fun _ hz => hUsub (hZsub hz).2
  obtain ⟨T, hT, hTeq⟩ := continuousOn_iff'.mp c.continuous_invFun X hX
  have hxu : c.toFun u ∈ M ∩ c.ambient := c.map_source hu
  have hxuT : c.toFun u ∈ T := by
    have hx : c.toFun u ∈ c.invFun ⁻¹' X ∩ (M ∩ c.ambient) :=
      ⟨by simpa only [mem_preimage, c.left_inv u hu] using huX, hxu⟩
    rw [hTeq] at hx
    exact hx.1
  obtain ⟨e₀, he₀⟩ := surjective_splitting (k := n-k) P (coordinateProjection_surjective s)
    (Nat.sub_add_cancel hkn)
  let e := e₀.trans (ContinuousLinearEquiv.prodComm ℝ (E (n-k)) (E k))
  have he : ∀ x, (e x).1 = P x := he₀
  let Q := (ContinuousLinearMap.snd ℝ (E k) (E (n-k))).comp e.toContinuousLinearMap
  let H := f ∘ q
  let b := Q ∘ H
  have hb : ContDiffOn ℝ r b Z :=
    Q.contDiff.comp_contDiffOn (h.graph_regular.mono hZY)
  let O := (c.ambient ∩ T) ∩ P ⁻¹' Z
  have hO : IsOpen O := (c.ambient_open.inter hT).inter (hZ.preimage P.continuous)
  have hxO : c.toFun u ∈ O := ⟨⟨hxu.2, hxuT⟩, hPuZ⟩
  have hbdef := graph_defining e Z b hr hZ hb
  refine ⟨O, graphDefining e b, hO, hxO, (fun _ hx => hx.1.1), ?_, ?_, ?_⟩
  · exact hbdef.1.mono (fun x hx => by change (e x).1 ∈ Z; rw [he]; exact hx.2)
  · ext x
    constructor
    · rintro ⟨hxM, hxO⟩
      refine ⟨hxO, ?_⟩
      have hxma : x ∈ M ∩ c.ambient := ⟨hxM, hxO.1.1⟩
      have hxX : c.invFun x ∈ X := by
        have hx : x ∈ T ∩ (M ∩ c.ambient) := ⟨hxO.1.2, hxma⟩
        rw [← hTeq] at hx
        exact hx.1
      have hv := h.inverse_left ⟨c.map_target hxma, hxX⟩
      rw [c.right_inv x hxma] at hv
      change q (P x) = c.invFun x at hv
      have hHx : H (P x) = x := by
        change f (q (P x)) = x
        rw [hv, h.extension_agrees ⟨c.map_target hxma, hXW hxX⟩, c.right_inv x hxma]
      change (e x).2 - b (e x).1 = 0
      rw [he]
      change Q x - Q (H (P x)) = 0
      rw [hHx, sub_self]
    · rintro ⟨hxO, hxg⟩
      have hxZ : P x ∈ Z := hxO.2
      have hv : q (P x) ∈ c.source ∩ X := ⟨hqV hxZ, hqmap (hZY hxZ)⟩
      have hPH : P (H (P x)) = P x := h.graph_coordinates (hZY hxZ)
      have hQH : Q x = Q (H (P x)) := by
        change (e x).2 - b (e x).1 = 0 at hxg
        rw [he] at hxg
        exact sub_eq_zero.mp hxg
      have hxH : x = H (P x) := by
        apply e.injective
        apply Prod.ext
        · simpa only [he] using hPH.symm
        · exact hQH
      have hHM : H (P x) ∈ M := by
        change f (q (P x)) ∈ M
        rw [h.extension_agrees ⟨hv.1, hXW hv.2⟩]
        exact (c.map_source hv.1).1
      exact ⟨hxH.symm ▸ hHM, hxO⟩
  · intro x hx
    exact (hbdef.2.2 x (by rw [he]; exact hx.2)).2.2

/-- Ordinary graphs, using the canonical first/last coordinate split. -/
theorem standard_graph_manifold :
    Specs.D04.C14.RegularLevelsAndGraphs.standard_graph_manifoldType := by
  intro r k q A h hr hA hh
  exact graph_manifold EuclideanSpace.finAddEquivProd A h hr hA hh

end RegularLevels
end D04
