import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.CuspExample
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.Surfaces
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalZeroFactorization
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Data.ENat.Monoid

noncomputable section
open Filter Set
open scoped Topology

namespace D12Complex.CuspExample

/-- The affine cusp with its inherited subset topology. -/
def affineCusp : Set (ℂ × ℂ) := {p | p.2 ^ 2 = p.1 ^ 3}

def parametrization (t : ℂ) : ℂ × ℂ := (t ^ 2, t ^ 3)

def inverseParameter (p : ℂ × ℂ) : ℂ :=
  if p.1 = 0 then 0 else p.2 / p.1

/-- The standard regular-parametrization characterization of a one-dimensional
complex embedded submanifold at a point. The chart is for the inherited
subset topology, and regularity is imposed on its ambient-valued inverse. -/
def IsEmbeddedComplexCurveAt (s : Set (ℂ × ℂ)) (p : ℂ × ℂ) : Prop :=
  ∃ (q : s) (e : OpenPartialHomeomorph s ℂ),
    (q : ℂ × ℂ) = p ∧ q ∈ e.source ∧
    DifferentiableOn ℂ (fun t => (e.symm t : ℂ × ℂ)) e.target ∧
    deriv (fun t => (e.symm t : ℂ × ℂ)) (e q) ≠ 0

/-- The abstract parameter surface has the standard identity complex chart. -/
theorem parameter_surface :
    ∃ S : Surfaces.RiemannSurface ℂ,
      S.atlas = {e | e.val = OpenPartialHomeomorph.refl ℂ} := by
  have hC : IsDomain (Set.univ : Set ℂ) :=
    ⟨Set.univ_nonempty, isOpen_univ, isPreconnected_univ⟩
  let e : Surfaces.ComplexChart ℂ := ⟨OpenPartialHomeomorph.refl ℂ, hC⟩
  have hA : Surfaces.IsAtlas {e} := by
    refine ⟨fun z => ⟨e, rfl, ?_⟩, ?_⟩
    · trivial
    · rintro f (rfl : f = e) g (rfl : g = e)
      exact Surfaces.compatibleCharts_refl e
  refine ⟨⟨inferInstance, inferInstance, inferInstance, {e}, hA⟩, ?_⟩
  ext f
  change f = e ↔ f.val = (OpenPartialHomeomorph.refl ℂ)
  exact Subtype.ext_iff

theorem parametrization_polynomial :
    ∃ P Q : Polynomial ℂ, ∀ t : ℂ,
      parametrization t = (P.eval t, Q.eval t) := by
  exact ⟨Polynomial.X ^ 2, Polynomial.X ^ 3, by simp [parametrization]⟩

theorem parametrization_holomorphic : Differentiable ℂ parametrization := by
  exact (differentiable_id.pow 2).prodMk (differentiable_id.pow 3)

theorem parametrization_mem (t : ℂ) : parametrization t ∈ affineCusp := by
  dsimp [parametrization, affineCusp]
  ring

theorem inverse_left : Function.LeftInverse inverseParameter parametrization := by
  intro t
  by_cases ht : t = 0
  · simp [parametrization, inverseParameter, ht]
  · simp [parametrization, inverseParameter, pow_ne_zero 2 ht]
    field_simp

lemma coordinates_zero {p : ℂ × ℂ} (hp : p ∈ affineCusp) (hx : p.1 = 0) :
    p = (0, 0) := by
  have hy : p.2 = 0 := by
    have : p.2 ^ 2 = 0 := by simpa [affineCusp, hx] using hp
    exact eq_zero_of_pow_eq_zero this
  exact Prod.ext hx hy

theorem inverse_right (p : ℂ × ℂ) (hp : p ∈ affineCusp) :
    parametrization (inverseParameter p) = p := by
  by_cases hx : p.1 = 0
  · rw [coordinates_zero hp hx]
    simp [parametrization, inverseParameter]
  · have hrel : p.2 ^ 2 = p.1 ^ 3 := hp
    simp only [inverseParameter, ite_eq_right hx, parametrization]
    apply Prod.ext
    · change (p.2 / p.1) ^ 2 = p.1
      rw [div_pow, hrel]
      field_simp
    · change (p.2 / p.1) ^ 3 = p.2
      rw [div_pow]
      apply (div_eq_iff (pow_ne_zero 3 hx)).mpr
      calc
        p.2 ^ 3 = p.2 * p.2 ^ 2 := by ring
        _ = p.2 * p.1 ^ 3 := by rw [hrel]

theorem parametrization_bijOn : Set.BijOn parametrization Set.univ affineCusp := by
  refine ⟨fun t _ => parametrization_mem t, ?_, ?_⟩
  · exact inverse_left.injective.injOn
  · intro p hp
    exact ⟨inverseParameter p, trivial, inverse_right p hp⟩

theorem inverse_at_origin : inverseParameter (0, 0) = 0 := by
  simp [inverseParameter]

theorem inverse_off_origin (p : ℂ × ℂ) (hp : p ∈ affineCusp) (h0 : p ≠ (0, 0)) :
    inverseParameter p = p.2 / p.1 := by
  exact ite_eq_right (fun hx => h0 (coordinates_zero hp hx))

private lemma analytic_of_holomorphicOn {U : Set ℂ} {f : ℂ → ℂ} {a : ℂ}
    (hf : HolomorphicOn U f) (ha : a ∈ U) : AnalyticAt ℂ f a := by
  apply (LocalZeroFactorization.holomorphicNear_iff_analyticAt f a).mp
  exact ⟨U, ha, hf⟩

theorem cusp_orders (U : Set ℂ) (x y : ℂ → ℂ) (a : ℂ) (ha : a ∈ U)
    (hx : HolomorphicOn U x) (hy : HolomorphicOn U y)
    (hC : ∀ t ∈ U, (x t, y t) ∈ affineCusp) :
    2 • analyticOrderAt y a = 3 • analyticOrderAt x a := by
  have hEq : y ^ 2 =ᶠ[𝓝 a] x ^ 3 :=
    Filter.eventually_of_mem (hx.1.mem_nhds ha) hC
  have h := analyticOrderAt_congr hEq
  rw [analyticOrderAt_pow (analytic_of_holomorphicOn hy ha),
    analyticOrderAt_pow (analytic_of_holomorphicOn hx ha)] at h
  exact h

theorem cusp_curve_deriv_zero (U : Set ℂ) (x y : ℂ → ℂ) (a : ℂ) (ha : a ∈ U)
    (hx : HolomorphicOn U x) (hy : HolomorphicOn U y)
    (hx0 : x a = 0) (hy0 : y a = 0)
    (hC : ∀ t ∈ U, (x t, y t) ∈ affineCusp) :
    deriv x a = 0 ∧ deriv y a = 0 := by
  have ho := cusp_orders U x y a ha hx hy hC
  simp only [nsmul_eq_mul] at ho
  constructor
  · by_contra hd
    have hx1 := (analytic_of_holomorphicOn hx ha).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hx0 hd
    rw [hx1] at ho
    by_cases ht : analyticOrderAt y a = ⊤
    · simp [ht] at ho
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ht
      rw [← hn] at ho
      change (2 : ℕ∞) * (n : ℕ∞) = 3 at ho
      have hn' : 2 * n = 3 := by
        simpa only [ENat.toNat_mul, ENat.toNat_natCast, ENat.toNat_ofNat,
          ENat.toNat_one, Nat.mul_one] using congrArg ENat.toNat ho
      omega
  · by_contra hd
    have hy1 := (analytic_of_holomorphicOn hy ha).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hy0 hd
    rw [hy1] at ho
    by_cases ht : analyticOrderAt x a = ⊤
    · simp [ht] at ho
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ht
      rw [← hn] at ho
      change (2 : ℕ∞) = 3 * (n : ℕ∞) at ho
      have hn' : 2 = 3 * n := by
        simpa only [ENat.toNat_mul, ENat.toNat_natCast, ENat.toNat_ofNat,
          ENat.toNat_one, Nat.mul_one] using congrArg ENat.toNat ho
      omega

theorem not_embedded_at_origin : ¬ IsEmbeddedComplexCurveAt affineCusp (0, 0) := by
  rintro ⟨q, e, hq, hsource, hhol, hreg⟩
  let f : ℂ → ℂ × ℂ := fun t => (e.symm t : ℂ × ℂ)
  have ha : e q ∈ e.target := e.map_source hsource
  have hf0 : f (e q) = (0, 0) := by
    dsimp [f]
    rw [e.left_inv hsource]
    exact hq
  have hx : HolomorphicOn e.target (fun t => (f t).1) :=
    ⟨e.open_target, fun t ht => ((hhol t ht).differentiableAt
      (e.open_target.mem_nhds ht)).fst⟩
  have hy : HolomorphicOn e.target (fun t => (f t).2) :=
    ⟨e.open_target, fun t ht => ((hhol t ht).differentiableAt
      (e.open_target.mem_nhds ht)).snd⟩
  have hd := cusp_curve_deriv_zero e.target (fun t => (f t).1) (fun t => (f t).2)
    (e q) ha hx hy (congrArg Prod.fst hf0) (congrArg Prod.snd hf0)
    (fun t _ => (e.symm t).property)
  have hfd : HasDerivAt f (0, 0) (e q) := by
    have h := (hx.2 _ ha).hasDerivAt.prodMk (hy.2 _ ha).hasDerivAt
    simpa only [hd.1, hd.2] using h
  exact hreg hfd.deriv

end D12Complex.CuspExample
