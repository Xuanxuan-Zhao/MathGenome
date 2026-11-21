import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Canonical Gagliardo objects. The second component of the graph is an Lp class
for the measure |x-y|^(-d-sp) dx dy. Thus its norm is precisely the
Gagliardo seminorm, without taking a p-th root in the difference operator.
The first projection identifies this graph with the finite-energy Lp classes. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal NNReal Topology
namespace P102.Fractional

abbrev Domain (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Lebesgue measure on the open set, also meaningful for the empty set. -/
def domainMeasure {d : ℕ} (G : Set (Domain d)) : Measure (Domain d) := volume.restrict G

instance domainMeasure_sigmaFinite {d : ℕ} (G : Set (Domain d)) :
    SigmaFinite (domainMeasure G) := by
  unfold domainMeasure
  infer_instance

/-- The singular weight; its value on the diagonal is explicitly zero. -/
def kernel (d : ℕ) (s : ℝ) (p : ℝ≥0∞) (z : Domain d × Domain d) : ℝ≥0∞ :=
  if z.1 = z.2 then 0 else (ENNReal.ofReal ‖z.1 - z.2‖ ^ ((d : ℝ) + s * p.toReal))⁻¹

/-- Product Lebesgue measure with the Gagliardo weight. -/
def pairMeasure {d : ℕ} (G : Set (Domain d)) (s : ℝ) (p : ℝ≥0∞) :
    Measure (Domain d × Domain d) :=
  ((domainMeasure G).prod (domainMeasure G)).withDensity (kernel d s p)

/-- Unweighted increment, used with `pairMeasure`. -/
def increment {d : ℕ} {𝕜 : Type*} [RCLike 𝕜] (u : Domain d → 𝕜)
    (z : Domain d × Domain d) : 𝕜 := u z.1 - u z.2

@[simp] theorem increment_zero {d : ℕ} {𝕜 : Type*} [RCLike 𝕜] :
    increment (0 : Domain d → 𝕜) = 0 := by
  funext z
  simp [increment]

/-- The original iterated nonnegative extended integral, diagonal zero. -/
def energy {d : ℕ} {𝕜 : Type*} [RCLike 𝕜] (G : Set (Domain d)) (s : ℝ)
    (p : ℝ≥0∞) (u : Domain d → 𝕜) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y,
    if x = y then 0 else
      ‖u x - u y‖ₑ ^ p.toReal / ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + s * p.toReal) ∂domainMeasure G ∂domainMeasure G

/-- Extended Gagliardo seminorm, so divergent integrals remain infinite. -/
def seminorm {d : ℕ} {𝕜 : Type*} [RCLike 𝕜] (G : Set (Domain d)) (s : ℝ)
    (p : ℝ≥0∞) (u : Domain d → 𝕜) : ℝ≥0∞ := (energy G s p u) ^ (1 / p.toReal)

/-- Two a.e. equal functions have a.e. equal increments for the weighted measure. -/
theorem increment_congr {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞} {u v : Domain d → 𝕜}
    (h : u =ᵐ[domainMeasure G] v) :
    increment u =ᵐ[pairMeasure G s p] increment v := by
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [quasiMeasurePreserving_fst.ae h, quasiMeasurePreserving_snd.ae h] with z hx hy
  simp only [increment, hx, hy]

/-- Ambient product equipped with the sum norm. -/
abbrev Ambient (d : ℕ) (𝕜 : Type*) [RCLike 𝕜] (G : Set (Domain d)) (s : ℝ)
    (p : ℝ≥0∞) :=
  WithLp 1 (Lp 𝕜 p (domainMeasure G) × Lp 𝕜 p (pairMeasure G s p))

/-- The graph condition uses equality almost everywhere, never pointwise equality
of chosen Lp representatives. -/
def graph {d : ℕ} (𝕜 : Type*) [RCLike 𝕜] (G : Set (Domain d)) (s : ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule 𝕜 (Ambient d 𝕜 G s p) where
  carrier := {z | (z.snd : (Domain d × Domain d) → 𝕜) =ᵐ[pairMeasure G s p]
    increment (z.fst : Domain d → 𝕜)}
  zero_mem' := by
    change (⇑(0 : Lp 𝕜 p (pairMeasure G s p))) =ᵐ[pairMeasure G s p]
      increment (⇑(0 : Lp 𝕜 p (domainMeasure G)))
    apply (Lp.coeFn_zero 𝕜 p (pairMeasure G s p)).trans
    simpa only [increment_zero] using (increment_congr (s := s) (p := p)
      (Lp.coeFn_zero 𝕜 p (domainMeasure G))).symm
  add_mem' := by
    intro a b ha hb
    have hi := increment_congr (s := s) (p := p) (Lp.coeFn_add a.fst b.fst)
    filter_upwards [Lp.coeFn_add a.snd b.snd, ha, hb, hi] with z hz hza hzb hiz
    change (a.snd + b.snd) z = increment (a.fst + b.fst) z
    rw [hz, Pi.add_apply, hza, hzb, hiz]
    simp [increment, sub_add_sub_comm]
  smul_mem' := by
    intro c a ha
    have hi := increment_congr (s := s) (p := p) (Lp.coeFn_smul c a.fst)
    filter_upwards [Lp.coeFn_smul c a.snd, ha, hi] with z hz hza hiz
    change (c • a.snd) z = increment (c • a.fst) z
    rw [hz, Pi.smul_apply, hza, hiz]
    simp [increment, mul_sub]

/-- Gagliardo space in its graph realization, with its inherited sum norm.
`firstProjection` is injective and has exactly the finite-energy Lp classes as image. -/
abbrev Space {d : ℕ} (𝕜 : Type*) [RCLike 𝕜] (G : Set (Domain d)) (s : ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] := graph 𝕜 G s p

/-- Underlying Lp class. -/
def firstProjection {d : ℕ} {𝕜 : Type*} [RCLike 𝕜] {G : Set (Domain d)} {s : ℝ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] : Space 𝕜 G s p →ₗ[𝕜] Lp 𝕜 p (domainMeasure G) where
  toFun u := u.val.fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end P102.Fractional

/-! Independent expected values and proposition types for the assigned result. -/
namespace Specs.P102.Fractional
open _root_.P102.Fractional
universe u

/-- Full value specifications for the original definitions. -/
def energyType := {d : ℕ} → {𝕜 : Type u} → [RCLike 𝕜] →
  Set (Domain d) → ℝ → ℝ≥0∞ → (Domain d → 𝕜) → ℝ≥0∞
def energyValue : energyType := @energy

def seminormType := {d : ℕ} → {𝕜 : Type u} → [RCLike 𝕜] →
  Set (Domain d) → ℝ → ℝ≥0∞ → (Domain d → 𝕜) → ℝ≥0∞
def seminormValue : seminormType := @seminorm

def spaceType := {d : ℕ} → (𝕜 : Type u) → [RCLike 𝕜] →
  (G : Set (Domain d)) → (s : ℝ) → (p : ℝ≥0∞) → [Fact (1 ≤ p)] →
    Submodule 𝕜 (Ambient d 𝕜 G s p)
def spaceValue : spaceType := @Space

/-- Energy is a function of the almost-everywhere class. -/
def representativeIndependence : Prop :=
  ∀ {d : ℕ} {𝕜 : Type u} [RCLike 𝕜] {G : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞}
    {u v : Domain d → 𝕜}, u =ᵐ[domainMeasure G] v → energy G s p u = energy G s p v

/-- The graph's second component gives the actual Gagliardo seminorm. -/
def seminormIdentification : Prop :=
  ∀ {d : ℕ} {𝕜 : Type u} [RCLike 𝕜] {G : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞}
    {u : Domain d → 𝕜}, p ≠ 0 → p ≠ ∞ → AEStronglyMeasurable u (domainMeasure G) →
    eLpNorm (increment u) p (pairMeasure G s p) = seminorm G s p u

/-- No duplicate graph elements represent the same Lp class. -/
def projectionInjective : Prop :=
  ∀ {d : ℕ} {𝕜 : Type u} [RCLike 𝕜] {G : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)], Function.Injective (@firstProjection d 𝕜 _ G s p _)

/-- The graph realization has exactly the original underlying Lp classes. -/
def spaceIdentification : Prop :=
  ∀ {d : ℕ} {𝕜 : Type u} [RCLike 𝕜] {G : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)], p ≠ ∞ → ∀ u : Lp 𝕜 p (domainMeasure G),
    (∃ v : Space 𝕜 G s p, firstProjection v = u) ↔ seminorm G s p u < ∞

/-- The exact manuscript norm, rather than only an equivalent product norm. -/
def normFormula : Prop :=
  ∀ {d : ℕ} {𝕜 : Type u} [RCLike 𝕜] {G : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)], p ≠ ∞ → ∀ u : Space 𝕜 G s p,
    ‖u‖ = ‖firstProjection u‖ + (seminorm G s p (firstProjection u)).toReal

/-- Banach completeness. All open sets, positive dimensions and s in (0,1)
are covered; the construction in fact works for any set, dimension and s. -/
def banach : Prop :=
  ∀ {d : ℕ} {𝕜 : Type u} [RCLike 𝕜] {G : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)], CompleteSpace (Space 𝕜 G s p)

def emptySpace : Prop :=
  ∀ {d : ℕ} {𝕜 : Type u} [RCLike 𝕜] {s : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)], Subsingleton (Space 𝕜 (∅ : Set (Domain d)) s p)

end Specs.P102.Fractional
