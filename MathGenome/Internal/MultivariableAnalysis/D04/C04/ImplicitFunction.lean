import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C04.ImplicitFunction
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeInterfaces
import Mathlib.Analysis.Calculus.ImplicitContDiff

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace D04
open Specs.D04.C04.ImplicitFunction.Model

/-- Local uniqueness transports both the regularity and derivative of a newly
constructed implicit function to any solution graph on an open product. -/
private theorem implicit_graph_regular {p q : ℕ} {r : ℕ∞ω}
    (G : E p × E q → E q) (φ : E p → E q) (c : E q)
    (A : Set (E p)) (B : Set (E q)) (hA : IsOpen A) (hB : IsOpen B)
    (hmap : MapsTo φ A B)
    (hiff : ∀ x ∈ A, ∀ y ∈ B, G (x, y) = c ↔ y = φ x)
    (x : E p) (hx : x ∈ A) (hr : r ≠ 0)
    (hG : ContDiffAt ℝ r G (x, φ x))
    (hDy : (solvedDerivative G (x, φ x)).IsInvertible) :
    ContDiffAt ℝ r φ x ∧
    HasFDerivAt φ
      (-((solvedDerivative G (x, φ x)).inverse.comp (parameterDerivative G (x, φ x)))) x := by
  let ψ := hG.implicitFunction hr hDy
  have hψ : ContDiffAt ℝ r ψ x := hG.contDiffAt_implicitFunction hr hDy
  have hψx : ψ x = φ x := hG.implicitFunction_apply_self hr hDy
  have hψB : ∀ᶠ z in 𝓝 x, ψ z ∈ B := by
    have ht : Tendsto ψ (𝓝 x) (𝓝 (φ x)) := by
      simpa only [hψx] using hψ.continuousAt.tendsto
    exact ht (hB.mem_nhds (hmap hx))
  have hgraph : G (x, φ x) = c := (hiff x hx (φ x) (hmap hx)).mpr rfl
  have hsame : φ =ᶠ[𝓝 x] ψ := by
    filter_upwards [hA.mem_nhds hx, hψB,
      hG.eventually_apply_implicitFunction hr hDy] with z hz hzB hgz
    exact ((hiff z hz (ψ z) hzB).mp (hgz.trans hgraph)).symm
  refine ⟨hψ.congr_of_eventuallyEq hsame, ?_⟩
  have hd := (hG.hasStrictFDerivAt_implicitFunction hr hDy).hasFDerivAt
  exact hd.congr_of_eventuallyEq hsame

/-- Choose a whole open product where the equation has exactly the prescribed
solution, then apply the local regularity argument at every graph point.
Using the C¹ construction first makes one neighborhood work also for C∞. -/
private theorem implicit_neighborhood {p q : ℕ} {r : ℕ∞ω}
    (W : Set (E p × E q)) (G : E p × E q → E q)
    (a : E p) (b c : E q) (hr : 1 ≤ r) (hW : IsOpen W)
    (hG : ContDiffOn ℝ r G W) (hab : (a, b) ∈ W) (hc : G (a, b) = c)
    (hDy : (solvedDerivative G (a, b)).IsInvertible) :
    ∃ A B φ, ImplicitNeighborhood W G a b c A B φ ∧ ContDiffOn ℝ r φ A := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr)
  have hG1 : ContDiffOn ℝ 1 G W := hG.of_le hr
  have hGa : ContDiffAt ℝ 1 G (a, b) := hG1.contDiffAt (hW.mem_nhds hab)
  let φ := hGa.implicitFunction one_ne_zero hDy
  have hφa : φ a = b := hGa.implicitFunction_apply_self one_ne_zero hDy
  have hφcont : ContinuousAt φ a :=
    (hGa.contDiffAt_implicitFunction one_ne_zero hDy).continuousAt
  have hInv : ∀ᶠ z in 𝓝 (a, b), (solvedDerivative G z).IsInvertible := by
    have hdc : ContinuousAt (fderiv ℝ G) (a, b) :=
      (hG1.continuousOn_fderiv_of_isOpen hW le_rfl).continuousAt (hW.mem_nhds hab)
    have hbc : ContinuousAt (solvedDerivative G) (a, b) := hdc.clm_comp continuousAt_const
    exact hbc.tendsto hDy.eventually_nhds
  have hLocal : {z : E p × E q | z ∈ W ∧
      (solvedDerivative G z).IsInvertible ∧ (G z = c ↔ φ z.1 = z.2)} ∈ 𝓝 (a, b) := by
    filter_upwards [hW.mem_nhds hab, hInv,
      hGa.eventually_apply_eq_iff_implicitFunction one_ne_zero hDy] with z hz hi he
    exact ⟨hz, hi, by simpa only [hc] using he⟩
  obtain ⟨A₀, B, hA₀, ha₀, hB, hb, hprod⟩ := mem_nhds_prod_iff'.mp hLocal
  have hpre : φ ⁻¹' B ∈ 𝓝 a := by
    apply hφcont.preimage_mem_nhds
    simpa only [hφa] using hB.mem_nhds hb
  obtain ⟨A, hAsub, hA, ha⟩ := mem_nhds_iff.mp (inter_mem (hA₀.mem_nhds ha₀) hpre)
  have hmap : MapsTo φ A B := fun x hx => (hAsub hx).2
  have hABW : A ×ˢ B ⊆ W := fun z hz => (hprod ⟨(hAsub hz.1).1, hz.2⟩).1
  have hiff : ∀ x ∈ A, ∀ y ∈ B, G (x, y) = c ↔ y = φ x := by
    intro x hx y hy
    exact (hprod ⟨(hAsub hx).1, hy⟩).2.2.trans eq_comm
  have hgraphInv (x : E p) (hx : x ∈ A) :
      (solvedDerivative G (x, φ x)).IsInvertible :=
    (hprod (show (x, φ x) ∈ A₀ ×ˢ B from ⟨(hAsub hx).1, hmap hx⟩)).2.1
  have hreg (x : E p) (hx : x ∈ A) :=
    implicit_graph_regular G φ c A B hA hB hmap hiff x hx hr0
      (hG.contDiffAt (hW.mem_nhds (hABW ⟨hx, hmap hx⟩))) (hgraphInv x hx)
  refine ⟨A, B, φ, ?_, fun x hx => (hreg x hx).1.contDiffWithinAt⟩
  refine ⟨hA, hB, ha, hb, hABW, hmap, hφa, hiff, ?_, ?_⟩
  · intro ψ hψ hsolve x hx
    exact (hiff x hx (ψ x) (hψ hx)).mp (hsolve x hx)
  · intro x hx
    have hd := (hreg x hx).2
    exact ⟨hgraphInv x hx,
      (hasTotalDerivative_iff_hasFDerivAt A φ _ x hA hx).mpr hd, hd.fderiv⟩

/-- Implicit function theorem for every positive finite order. Neither the
parameter nor the solved-variable dimension is required to be positive. -/
theorem implicit_function_finite : Specs.D04.C04.ImplicitFunction.implicit_function_finiteType := by
  intro p q r W G a b c hr hW hG hab hc hDy
  obtain ⟨A, B, φ, hgeom, hreg⟩ := implicit_neighborhood W G a b c
    (by exact_mod_cast hr) hW ((crOn_iff_contDiffOn r W G hW).mp hG) hab hc hDy
  exact ⟨A, B, φ, hgeom, (crOn_iff_contDiffOn r A φ hgeom.1).mpr hreg⟩

/-- A single product neighborhood and a smooth implicit function for smooth data. -/
theorem implicit_function_smooth : Specs.D04.C04.ImplicitFunction.implicit_function_smoothType := by
  intro p q W G a b c hW hG hab hc hDy
  obtain ⟨A, B, φ, hgeom, hreg⟩ := implicit_neighborhood (r := ∞) W G a b c
    (by simp) hW ((smoothOn_iff_contDiffOn W G hW).mp hG) hab hc hDy
  exact ⟨A, B, φ, hgeom, (smoothOn_iff_contDiffOn A φ hgeom.1).mpr hreg⟩

end D04
