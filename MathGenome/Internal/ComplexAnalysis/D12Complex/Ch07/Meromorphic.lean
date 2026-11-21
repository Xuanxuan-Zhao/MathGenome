import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Meromorphic
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalZeroFactorization
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.Sphere

noncomputable section
open Filter Set
open scoped Topology

namespace D12Complex.Meromorphic

abbrev scalarFinitePart : Specs.D12Complex.Ch07.Meromorphic.scalarFinitePart_type :=
  _root_.D12Complex.scalarFinitePart

abbrev scalarPoleSet : Specs.D12Complex.Ch07.Meromorphic.scalarPoleSet_type :=
  _root_.D12Complex.scalarPoleSet

abbrev ScalarMeromorphicOn : Specs.D12Complex.Ch07.Meromorphic.ScalarMeromorphicOn_type :=
  _root_.D12Complex.ScalarMeromorphicOn

abbrev scalarZeroGerm : Specs.D12Complex.Ch07.Meromorphic.scalarZeroGerm_type :=
  _root_.D12Complex.scalarZeroGerm

abbrev scalarSignedOrder : Specs.D12Complex.Ch07.Meromorphic.scalarSignedOrder_type :=
  _root_.D12Complex.scalarSignedOrder

abbrev ScalarMeromorphicOnSphere : Specs.D12Complex.Ch07.Meromorphic.ScalarMeromorphicOnSphere_type :=
  _root_.D12Complex.ScalarMeromorphicOnSphere

abbrev sphereScalarSignedOrder : Specs.D12Complex.Ch07.Meromorphic.sphereScalarSignedOrder_type :=
  _root_.D12Complex.sphereScalarSignedOrder

end D12Complex.Meromorphic

namespace D12Complex

/-- The definition requires weak holomorphy on the actual open finite locus. -/
theorem scalarMeromorphicOn_finite_analytic
    (Ω : Set ℂ) (F : ℂ → RiemannSphere) (hF : ScalarMeromorphicOn Ω F)
    (a : ℂ) (ha : a ∈ Ω) (hfin : F a ≠ sphereInfty) :
    AnalyticAt ℂ (scalarFinitePart F) a := by
  exact (LocalZeroFactorization.holomorphicNear_iff_analyticAt _ _).mp
    ⟨{z | z ∈ Ω ∧ F z ≠ sphereInfty}, ⟨ha, hfin⟩, hF.2.2.2.1⟩

theorem scalarMeromorphicOn_not_identicallyInfty
    (Ω : Set ℂ) (F : ℂ → RiemannSphere) (hF : ScalarMeromorphicOn Ω F)
    (a : ℂ) (ha : a ∈ Ω) :
    ¬ EqOn F (fun _ => sphereInfty) (connectedComponentIn Ω a) := by
  obtain ⟨b, hb, hfb⟩ := hF.2.2.2.2.2 a ha
  exact fun h => hfb (h hb)

theorem scalarSignedOrder_finite
    (Ω : Set ℂ) (F : ℂ → RiemannSphere) (hF : ScalarMeromorphicOn Ω F)
    (a : ℂ) (ha : a ∈ Ω) (hfin : F a ≠ sphereInfty) :
    scalarSignedOrder F a =
      (analyticOrderAt (scalarFinitePart F) a).map (fun n => (n : ℤ)) :=
  (scalarMeromorphicOn_finite_analytic Ω F hF a ha hfin).meromorphicOrderAt_eq

theorem scalarSignedOrder_of_zeroMultiplicity
    (Ω : Set ℂ) (F : ℂ → RiemannSphere) (hF : ScalarMeromorphicOn Ω F)
    (a : ℂ) (ha : a ∈ Ω) (hfin : F a ≠ sphereInfty) (m : ℕ)
    (hm : Specs.D12Complex.Ch05.LocalZeroFactorization.HasFiniteOrder_value
      (scalarFinitePart F) a m) : scalarSignedOrder F a = some (m : ℤ) := by
  have han := scalarMeromorphicOn_finite_analytic Ω F hF a ha hfin
  have hnear := (LocalZeroFactorization.holomorphicNear_iff_analyticAt _ _).mpr han
  have hord := (LocalZeroFactorization.order_eq_nat_iff _ _ hnear m).mpr hm
  rw [scalarSignedOrder_finite Ω F hF a ha hfin]
  change analyticOrderAt (scalarFinitePart F) a = (m : ℕ∞) at hord
  rw [hord]
  rfl

/-- Convert the source's exact pole factorization into the library's punctured
integer-power factorization. In particular the filler at the puncture is unused. -/
private theorem pole_integer_factorization {f : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hm : PoleOfOrderAt f a m) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ g a ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] a, f z = (z - a) ^ (-(m : ℤ)) • g z := by
  obtain ⟨R, hR, g, hg, hg0, heq⟩ := hm.2.2
  refine ⟨g, (LocalZeroFactorization.holomorphicNear_iff_analyticAt _ _).mp
    ⟨Metric.ball a R, Metric.mem_ball_self hR, hg⟩, hg0, ?_⟩
  have hb : ∀ᶠ z in 𝓝[≠] a, z ∈ Metric.ball a R :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds a hR)
  filter_upwards [hb, self_mem_nhdsWithin] with z hz hza
  have hnorm : ‖z - a‖ < R := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hp : z ∈ puncturedDisk a R := ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hza), hnorm⟩
  simpa only [zpow_neg, zpow_natCast, smul_eq_mul] using heq z hp

theorem scalarSignedOrder_pole (F : ℂ → RiemannSphere) (a : ℂ) (m : ℕ)
    (hm : PoleOfOrderAt (scalarFinitePart F) a m) :
    scalarSignedOrder F a = some (-(m : ℤ)) := by
  obtain ⟨g, hg, hg0, heq⟩ := pole_integer_factorization hm
  have hmero : MeromorphicAt (scalarFinitePart F) a :=
    MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr ⟨-(m : ℤ), g, hg, heq⟩
  exact (meromorphicOrderAt_eq_int_iff hmero).mpr ⟨g, hg, hg0, heq⟩

theorem scalarSignedOrder_regular
    (Ω : Set ℂ) (F : ℂ → RiemannSphere) (hF : ScalarMeromorphicOn Ω F)
    (a : ℂ) (ha : a ∈ Ω) (c : ℂ) (hc : F a = sphereFinite c) (hc0 : c ≠ 0) :
    scalarSignedOrder F a = some 0 := by
  have hfin : F a ≠ sphereInfty := by rw [hc]; exact OnePoint.coe_ne_infty c
  have han := scalarMeromorphicOn_finite_analytic Ω F hF a ha hfin
  have hne : scalarFinitePart F a ≠ 0 := by simpa [scalarFinitePart, hc] using hc0
  rw [scalarSignedOrder_finite Ω F hF a ha hfin, han.analyticOrderAt_eq_zero.mpr hne]
  rfl

private theorem sphere_eq_finiteCoordinate {p : RiemannSphere} (hp : p ≠ sphereInfty) :
    p = sphereFinite (finiteCoordinate p) := by
  rcases sphere_eq_infty_or_finite p with h | ⟨z, rfl⟩
  · exact (hp h).elim
  · rfl

theorem scalarSignedOrder_none_iff
    (Ω : Set ℂ) (F : ℂ → RiemannSphere) (hF : ScalarMeromorphicOn Ω F)
    (a : ℂ) (ha : a ∈ Ω) :
    scalarSignedOrder F a = none ↔ scalarZeroGerm F a := by
  by_cases hfin : F a ≠ sphereInfty
  · have han := scalarMeromorphicOn_finite_analytic Ω F hF a ha hfin
    rw [scalarSignedOrder_finite Ω F hF a ha hfin]
    change (analyticOrderAt (scalarFinitePart F) a).map (fun n => (n : ℤ)) = ⊤ ↔ _
    rw [ENat.map_eq_top_iff, analyticOrderAt_eq_top]
    constructor
    · intro heq
      have hloc := hF.2.2.2.1.1.mem_nhds (show a ∈ {z | z ∈ Ω ∧ F z ≠ sphereInfty}
        from ⟨ha, hfin⟩)
      filter_upwards [heq, hloc] with z hz hzf
      have hval := sphere_eq_finiteCoordinate hzf.2
      change scalarFinitePart F z = 0 at hz
      change finiteCoordinate (F z) = 0 at hz
      exact hval.trans (congrArg sphereFinite hz)
    · intro heq
      filter_upwards [heq] with z hz
      simp [scalarFinitePart, hz]
  · have hInf : F a = sphereInfty := not_ne_iff.mp hfin
    obtain ⟨m, hm⟩ := hF.2.2.2.2.1 a ha hInf
    rw [scalarSignedOrder_pole F a m hm]
    constructor
    · intro h; cases h
    · intro hzero
      have hval : F a = sphereFinite 0 := hzero.self_of_nhds
      exact ((OnePoint.coe_ne_infty (0 : ℂ)) (hval.symm.trans hInf)).elim

theorem scalarSignedOrder_exists_iff
    (Ω : Set ℂ) (F : ℂ → RiemannSphere) (hF : ScalarMeromorphicOn Ω F)
    (a : ℂ) (ha : a ∈ Ω) :
    (∃ k : ℤ, scalarSignedOrder F a = some k) ↔ ¬ scalarZeroGerm F a := by
  rw [← scalarSignedOrder_none_iff Ω F hF a ha]
  exact Option.ne_none_iff_exists'.symm

theorem sphereScalarSignedOrder_finite (F : RiemannSphere → RiemannSphere) (z : ℂ) :
    sphereScalarSignedOrder F (sphereFinite z) = scalarSignedOrder (F ∘ sphereFinite) z := by
  have hfin : sphereFinite z ≠ sphereInfty := OnePoint.coe_ne_infty z
  simp only [sphereScalarSignedOrder, ite_eq_right hfin, finiteCoordinate_sphereFinite]

theorem sphereScalarSignedOrder_infty (F : RiemannSphere → RiemannSphere) :
    sphereScalarSignedOrder F sphereInfty = scalarSignedOrder (F ∘ infinityParametrization) 0 := by
  simp only [sphereScalarSignedOrder, ↓reduceIte]

theorem scalarMeromorphicOnSphere_finite
    (U : Set RiemannSphere) (F : RiemannSphere → RiemannSphere)
    (hF : ScalarMeromorphicOnSphere U F) :
    ScalarMeromorphicOn (sphereFinite ⁻¹' U) (F ∘ sphereFinite) := hF.2.1

theorem scalarMeromorphicOnSphere_infty
    (U : Set RiemannSphere) (F : RiemannSphere → RiemannSphere)
    (hF : ScalarMeromorphicOnSphere U F) :
    ScalarMeromorphicOn (infinityParametrization ⁻¹' U) (F ∘ infinityParametrization) := hF.2.2

end D12Complex
