import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.OrientedManifoldAndDensityIntegrals

/-! Independent full proposition types for paper.tex d04:15:independence.
The canonical fields, charts, supports, orientations, partitions, and proper
Riemann integrals are the upstream objects. No candidate module is imported.
Comparisons quantify over every allowed partition. The unsigned statements
require no orientation; the zero-dimensional statements retain finite support
on a possibly noncompact discrete manifold. -/
noncomputable section
open Set Function Topology
open scoped ContDiff BigOperators
namespace Specs.D04.C15.ManifoldIntegralIndependence
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model

def oriented_comparisonType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η : TangentTopField r k M)
    (hη : ContinuousTopField η) {K L : Set M}
    (P : SignedChartPartition o K) (Q : SignedChartPartition o L)
    (hK : topSupport η ⊆ K) (hL : topSupport η ⊆ L),
    (∑ i, (P.sign i).val * coefficientIntegral (localizedTopCoefficient η (P.chart i) (P.weight i))) =
      ∑ j, (Q.sign j).val * coefficientIntegral (localizedTopCoefficient η (Q.chart j) (Q.weight j))

def oriented_independentType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η : TangentTopField r k M)
    (hη : ContinuousTopField η)
    (P Q : SignedChartPartition o (topSupport η)),
    orientedIntegral η P = orientedIntegral η Q

def density_comparisonType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (ρ : DensityField M) (hρ : Continuous ρ) {K L : Set M}
    (P : ChartPartition r k M K) (Q : ChartPartition r k M L)
    (hK : tsupport ρ ⊆ K) (hL : tsupport ρ ⊆ L),
    (∑ i, coefficientIntegral (localizedDensityCoefficient ρ (P.chart i) (P.weight i))) =
      ∑ j, coefficientIntegral (localizedDensityCoefficient ρ (Q.chart j) (Q.weight j))

def density_independentType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (ρ : DensityField M) (hρ : Continuous ρ)
    (P Q : ChartPartition r k M (tsupport ρ)),
    densityIntegral ρ P = densityIntegral ρ Q

def oriented_addType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η ξ : TangentTopField r k M)
    (hη : ContinuousTopField η) (hξ : ContinuousTopField ξ)
    (hkη : IsCompact (topSupport η)) (hkξ : IsCompact (topSupport ξ))
    (P : SignedChartPartition o (topSupport η)) (Q : SignedChartPartition o (topSupport ξ))
    (R : SignedChartPartition o (topSupport (η + ξ))),
    orientedIntegral (η + ξ) R = orientedIntegral η P + orientedIntegral ξ Q

def oriented_smulType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (a : ℝ) (η : TangentTopField r k M)
    (hη : ContinuousTopField η) (P : SignedChartPartition o (topSupport η))
    (Q : SignedChartPartition o (topSupport (a • η))),
    orientedIntegral (a • η) Q = a * orientedIntegral η P

def oriented_finite_localizationType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η : TangentTopField r k M)
    (hη : ContinuousTopField η) {m : ℕ} (w : Fin m → E n → ℝ)
    (hw : ∀ j, Continuous (w j)) (hsum : ∀ x : M, η x ≠ 0 → ∑ j, w j x = 1)
    (P : SignedChartPartition o (topSupport η))
    (Q : (j : Fin m) → SignedChartPartition o (topSupport (fun x => w j x • η x))),
    orientedIntegral η P = ∑ j, orientedIntegral (fun x => w j x • η x) (Q j)

def oriented_reverseType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η : TangentTopField r k M)
    (hη : ContinuousTopField η) (P : SignedChartPartition o (topSupport η)),
    ∃ p : PositiveManifoldOrientation r k M,
      p.atPoint = (fun x hx => -o.atPoint x hx) ∧
      ∀ Q : SignedChartPartition p (topSupport η), orientedIntegral η Q = -orientedIntegral η P

def oriented_single_chartType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η : TangentTopField r k M)
    (hη : ContinuousTopField η) (hkη : IsCompact (topSupport η))
    (P : SignedChartPartition o (topSupport η)) (c : EmbeddedChart r k n M)
    (hs : topSupport η ⊆ Subtype.val ⁻¹' c.ambient) (s : PointSign)
    (hsgn : ∀ u : c.source, chartSign o.atPoint c u u.property = s.val),
    ProperIntegrable (topCoefficient η c) ∧
      orientedIntegral η P = s.val * coefficientIntegral (topCoefficient η c)

def density_single_chartType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (ρ : DensityField M) (hρ : Continuous ρ)
    (hkρ : HasCompactSupport ρ) (P : ChartPartition r k M (tsupport ρ))
    (c : EmbeddedChart r k n M) (hs : tsupport ρ ⊆ Subtype.val ⁻¹' c.ambient),
    ProperIntegrable (densityCoefficient ρ c) ∧
      densityIntegral ρ P = coefficientIntegral (densityCoefficient ρ c)

def density_addType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (ρ τ : DensityField M) (hρ : Continuous ρ) (hτ : Continuous τ)
    (hkρ : HasCompactSupport ρ) (hkτ : HasCompactSupport τ)
    (P : ChartPartition r k M (tsupport ρ)) (Q : ChartPartition r k M (tsupport τ))
    (R : ChartPartition r k M (tsupport (ρ + τ))),
    densityIntegral (ρ + τ) R = densityIntegral ρ P + densityIntegral τ Q

def density_smulType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (a : ℝ) (ρ : DensityField M) (hρ : Continuous ρ)
    (P : ChartPartition r k M (tsupport ρ)) (Q : ChartPartition r k M (tsupport (a • ρ))),
    densityIntegral (a • ρ) Q = a * densityIntegral ρ P

def density_finite_localizationType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (ρ : DensityField M) (hρ : Continuous ρ)
    {m : ℕ} (w : Fin m → E n → ℝ) (hw : ∀ j, Continuous (w j))
    (hsum : ∀ x : M, ρ x ≠ 0 → ∑ j, w j x = 1)
    (P : ChartPartition r k M (tsupport ρ))
    (Q : (j : Fin m) → ChartPartition r k M (tsupport (fun x : M => w j x * ρ x))),
    densityIntegral ρ P = ∑ j, densityIntegral (fun x : M => w j x * ρ x) (Q j)

def zero_integral_finsetType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)} (o : ZeroManifoldOrientation M)
    (f : M → ℝ) (s : Finset M) (hs : support f ⊆ (s : Set M)),
    zeroIntegral o f = ∑ x ∈ s, (o x).val * f x

def zero_addType : Prop :=
  ∀ {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r 0 M) (o : ZeroManifoldOrientation M)
    (f g : M → ℝ) (hf : HasCompactSupport f) (hg : HasCompactSupport g),
    zeroIntegral o (f + g) = zeroIntegral o f + zeroIntegral o g

def zero_smulType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)} (o : ZeroManifoldOrientation M)
    (a : ℝ) (f : M → ℝ),
    zeroIntegral o (a • f) = a * zeroIntegral o f

def zero_reverseType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)} (o : ZeroManifoldOrientation M) (f : M → ℝ),
    ∃ p : ZeroManifoldOrientation M, (∀ x, (p x).val = -(o x).val) ∧
      zeroIntegral p f = -zeroIntegral o f

def zero_single_pointType : Prop :=
  ∀ {n : ℕ} {M : Set (E n)} (o : ZeroManifoldOrientation M)
    (f : M → ℝ) (x : M) (hs : support f ⊆ {x}),
    zeroIntegral o f = (o x).val * f x

def zero_finite_localizationType : Prop :=
  ∀ {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r 0 M) (o : ZeroManifoldOrientation M)
    (f : M → ℝ) (hf : HasCompactSupport f) {m : ℕ} (w : Fin m → M → ℝ)
    (hsum : ∀ x, f x ≠ 0 → ∑ j, w j x = 1),
    zeroIntegral o f = ∑ j, zeroIntegral o (fun x => w j x * f x)

def density_zero_sumType : Prop :=
  ∀ {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r 0 M) (ρ : DensityField M) (hkρ : HasCompactSupport ρ)
    (P : ChartPartition r 0 M (tsupport ρ)),
    densityIntegral ρ P = ∑ᶠ x : M, ρ x

def zero_compact_agreesType : Prop :=
  ∀ {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r 0 M) (hc : IsCompact M)
    (o : ZeroManifoldOrientation M) (f : M → ℝ),
    ∃ h : M.Finite, zeroIntegral o f = compactZeroIntegral h o f

def oriented_single_chart_variable_signType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η : TangentTopField r k M)
    (hη : ContinuousTopField η) (hkη : IsCompact (topSupport η))
    (P : SignedChartPartition o (topSupport η)) (c : EmbeddedChart r k n M)
    (hs : topSupport η ⊆ Subtype.val ⁻¹' c.ambient),
    ProperIntegrable (fun u : c.source => chartSign o.atPoint c u u.property * topCoefficient η c u) ∧
      orientedIntegral η P = coefficientIntegral
        (fun u : c.source => chartSign o.atPoint c u u.property * topCoefficient η c u)

def oriented_reverse_comparisonType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o p : PositiveManifoldOrientation r k M)
    (hp : p.atPoint = fun x hx => -o.atPoint x hx)
    (η : TangentTopField r k M) (hη : ContinuousTopField η)
    (P : SignedChartPartition o (topSupport η)) (Q : SignedChartPartition p (topSupport η)),
    orientedIntegral η Q = -orientedIntegral η P

end Specs.D04.C15.ManifoldIntegralIndependence
