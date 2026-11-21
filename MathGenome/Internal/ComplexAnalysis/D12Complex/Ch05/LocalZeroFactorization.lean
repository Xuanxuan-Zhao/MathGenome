import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.LocalZeroFactorization
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section
open Filter
open scoped Topology

namespace D12Complex.LocalZeroFactorization

/-- Weak holomorphy on some open neighborhood, using the project's predicate. -/
def HolomorphicNear (f : ℂ → ℂ) (a : ℂ) : Prop :=
  ∃ U : Set ℂ, a ∈ U ∧ HolomorphicOn U f

/-- The identically-zero germ, independently of the values far from a. -/
def ZeroGerm (f : ℂ → ℂ) (a : ℂ) : Prop := ∀ᶠ z in 𝓝 a, f z = 0

/-- A finite order is witnessed by a holomorphic unit and a local power factor. -/
def HasFiniteOrder (f : ℂ → ℂ) (a : ℂ) (m : ℕ) : Prop :=
  ∃ g : ℂ → ℂ, HolomorphicNear g a ∧ g a ≠ 0 ∧
    ∀ᶠ z in 𝓝 a, f z = (z - a)^m * g z

/-- Extended local zero multiplicity; applied to holomorphic germs below.
The value ∞ denotes the identically-zero germ. -/
def order (f : ℂ → ℂ) (a : ℂ) : ℕ∞ := analyticOrderAt f a


theorem holomorphicNear_iff_analyticAt :
  ∀ (f : ℂ → ℂ) (a : ℂ), HolomorphicNear f a ↔ AnalyticAt ℂ f a := by
  intro f a
  change (∃ U : Set ℂ, a ∈ U ∧ HolomorphicOn U f) ↔ AnalyticAt ℂ f a
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  constructor
  · rintro ⟨U, ha, hU, hf⟩
    exact Filter.eventually_of_mem (hU.mem_nhds ha) hf
  · intro hf
    obtain ⟨U, hU, ho, ha⟩ := eventually_nhds_iff.mp hf
    exact ⟨U, ha, ho, hU⟩

theorem order_eq_top_iff :
  ∀ (f : ℂ → ℂ) (a : ℂ), order f a = ⊤ ↔ ZeroGerm f a := by
  intro f a
  exact analyticOrderAt_eq_top

theorem order_eq_nat_iff :
  ∀ (f : ℂ → ℂ) (a : ℂ), HolomorphicNear f a → ∀ m : ℕ,
    order f a = (m : ℕ∞) ↔ HasFiniteOrder f a m := by
  intro f a hf m
  rw [order, (holomorphicNear_iff_analyticAt f a).mp hf |>.analyticOrderAt_eq_natCast]
  simp only [smul_eq_mul]
  constructor
  · rintro ⟨g, hg, hg0, heq⟩
    exact ⟨g, (holomorphicNear_iff_analyticAt g a).mpr hg, hg0, heq⟩
  · rintro ⟨g, hg, hg0, heq⟩
    exact ⟨g, (holomorphicNear_iff_analyticAt g a).mp hg, hg0, heq⟩

private lemma finiteOrder_analytic {f : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hf : HasFiniteOrder f a m) : AnalyticAt ℂ f a := by
  obtain ⟨g, hg, _, heq⟩ := hf
  have h : AnalyticAt ℂ (fun z => (z - a)^m * g z) a :=
    ((analyticAt_id.sub analyticAt_const).pow m).mul
      ((holomorphicNear_iff_analyticAt g a).mp hg)
  exact (analyticAt_congr heq).mpr h

theorem local_zero_factorization :
  ∀ (f : ℂ → ℂ) (a : ℂ), HolomorphicNear f a →
    (ZeroGerm f a ∧ ¬ ∃ m : ℕ, HasFiniteOrder f a m) ∨
    (¬ ZeroGerm f a ∧ ∃! m : ℕ, HasFiniteOrder f a m) := by
  intro f a hf
  classical
  by_cases hzero : ZeroGerm f a
  · left
    refine ⟨hzero, ?_⟩
    rintro ⟨m, hm⟩
    have ht := (order_eq_top_iff f a).mpr hzero
    have hn := (order_eq_nat_iff f a hf m).mpr hm
    exact (ENat.top_ne_natCast m) (ht.symm.trans hn)
  · right
    refine ⟨hzero, ?_⟩
    have htop : order f a ≠ ⊤ := fun ht => hzero ((order_eq_top_iff f a).mp ht)
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp htop
    refine ⟨m, (order_eq_nat_iff f a hf m).mp hm.symm, ?_⟩
    intro n hn
    exact WithTop.coe_inj.mp (((order_eq_nat_iff f a hf n).mpr hn).symm.trans hm.symm)

theorem factor_unique :
  ∀ (f g h : ℂ → ℂ) (a : ℂ) (m : ℕ),
    HolomorphicNear g a → HolomorphicNear h a →
    (∀ᶠ z in 𝓝 a, f z = (z - a)^m * g z) →
    (∀ᶠ z in 𝓝 a, f z = (z - a)^m * h z) → g =ᶠ[𝓝 a] h := by
  intro f g h a m hg hh hfg hfh
  have hgc := ((holomorphicNear_iff_analyticAt g a).mp hg).continuousAt
  have hhc := ((holomorphicNear_iff_analyticAt h a).mp hh).continuousAt
  apply (hgc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hhc).mp
  filter_upwards [hfg.filter_mono nhdsWithin_le_nhds,
    hfh.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hz' hza
  exact mul_left_cancel₀ (pow_ne_zero m (sub_ne_zero.mpr hza)) (hz.symm.trans hz')

theorem finiteOrder_zero_iff :
  ∀ (f : ℂ → ℂ) (a : ℂ) (m : ℕ), HasFiniteOrder f a m →
    (f a = 0 ↔ 0 < m) := by
  intro f a m hf
  obtain ⟨g, _, hg, heq⟩ := hf
  rw [heq.self_of_nhds]
  cases m with
  | zero => simp [hg]
  | succ m => simp

theorem finiteOrder_isolated :
  ∀ (f : ℂ → ℂ) (a : ℂ) (m : ℕ), HasFiniteOrder f a m →
    ∀ᶠ z in 𝓝[≠] a, f z ≠ 0 := by
  intro f a m hf
  obtain ⟨g, hg, hg0, heq⟩ := hf
  have hg_ne := ((holomorphicNear_iff_analyticAt g a).mp hg).continuousAt.eventually_ne hg0
  filter_upwards [heq.filter_mono nhdsWithin_le_nhds,
    hg_ne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hgz hza
  rw [hz]
  exact mul_ne_zero (pow_ne_zero m (sub_ne_zero.mpr hza)) hgz

theorem order_eq_zero_iff :
  ∀ (f : ℂ → ℂ) (a : ℂ), HolomorphicNear f a →
    (order f a = 0 ↔ f a ≠ 0) := by
  intro f a hf
  exact ((holomorphicNear_iff_analyticAt f a).mp hf).analyticOrderAt_eq_zero

theorem order_mul :
  ∀ (f g : ℂ → ℂ) (a : ℂ), HolomorphicNear f a → HolomorphicNear g a →
    order (f * g) a = order f a + order g a := by
  intro f g a hf hg
  exact analyticOrderAt_mul ((holomorphicNear_iff_analyticAt f a).mp hf)
    ((holomorphicNear_iff_analyticAt g a).mp hg)

theorem finiteOrder_mul :
  ∀ (f g : ℂ → ℂ) (a : ℂ) (m n : ℕ),
    HasFiniteOrder f a m → HasFiniteOrder g a n →
    HasFiniteOrder (f * g) a (m + n) ∧ order (f * g) a = ((m + n : ℕ) : ℕ∞) := by
  intro f g a m n hf hg
  have hf' := (holomorphicNear_iff_analyticAt f a).mpr (finiteOrder_analytic hf)
  have hg' := (holomorphicNear_iff_analyticAt g a).mpr (finiteOrder_analytic hg)
  have hfg := (holomorphicNear_iff_analyticAt (f * g) a).mpr
    ((finiteOrder_analytic hf).mul (finiteOrder_analytic hg))
  have heq : order (f * g) a = ((m+n : ℕ) : ℕ∞) := by
    rw [order_mul f g a hf' hg', (order_eq_nat_iff f a hf' m).mpr hf,
      (order_eq_nat_iff g a hg' n).mpr hg, Nat.cast_add]
  exact ⟨(order_eq_nat_iff (f * g) a hfg (m+n)).mp heq, heq⟩

end D12Complex.LocalZeroFactorization
