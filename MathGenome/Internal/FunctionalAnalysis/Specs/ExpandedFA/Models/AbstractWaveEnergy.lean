import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.RealNonnegativeSpectralCalculus
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.MeasurableSpectralCalculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
Independent statements for the wave portion of `fa2:p3:kooper-wave`,
paper.tex 15906–15918 and 15933–15947, with the conventions at lines 67–73.
The Koopman and homogeneous-completion assertions have separate allocations.

The domain carries the *graph* norm, including when the energy is degenerate.
The dual below is always scalar-linear. The family is canonically specified
using the upstream real calculus, respectively the complex PVM calculus.
No spectral family or solution certificate is assumed of the original operator.
-/
noncomputable section
open Set Filter
open scoped Topology NNReal

namespace ExpandedFA.Models.AbstractWaveEnergy
open Unbounded
namespace RealSymbols
abbrev coordinate := RealNonnegativeSpectralCalculus.coordinate
abbrev root := RealNonnegativeSpectralCalculus.root
abbrev cosine := RealNonnegativeSpectralCalculus.cosine
abbrev sine := RealNonnegativeSpectralCalculus.sine
abbrev quotientSine := RealNonnegativeSpectralCalculus.quotientSine
end RealSymbols

universe u
section General
variable {𝕜 : Type*} [RCLike 𝕜] {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

variable [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]

/-- Evaluation of the displacement coordinate, continuous in the sum graph norm. -/
def position (S : Operator 𝕜 H H) : GraphDomain S →L[𝕜] H :=
  LinearMap.mkContinuous
    { toFun := fun x => (GraphDomain.toDomain S x : H)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (by
      intro x
      change ‖(GraphDomain.toDomain S x : H)‖ ≤
        1 * (‖(GraphDomain.toDomain S x : H)‖ + ‖S (GraphDomain.toDomain S x)‖)
      simpa only [one_mul] using
        le_add_of_nonneg_right (norm_nonneg (S (GraphDomain.toDomain S x))))

/-- Evaluation of S on its domain; bounded for the graph norm. -/
def gradient (S : Operator 𝕜 H H) : GraphDomain S →L[𝕜] H :=
  LinearMap.mkContinuous
    { toFun := fun x => S (GraphDomain.toDomain S x)
      map_add' := fun _ _ => S.map_add _ _
      map_smul' := fun _ _ => S.map_smul _ _ }
    1 (by
      intro x
      change ‖S (GraphDomain.toDomain S x)‖ ≤
        1 * (‖(GraphDomain.toDomain S x : H)‖ + ‖S (GraphDomain.toDomain S x)‖)
      simpa only [one_mul] using
        le_add_of_nonneg_left (norm_nonneg (GraphDomain.toDomain S x : H)))

/-- Continuous scalar-linear dual, rather than the antidual. -/
abbrev EnergyDual (S : Operator 𝕜 H H) := GraphDomain S →L[𝕜] 𝕜

/-- Canonical Hilbert injection into the scalar-linear dual of D(S).
It is conjugate-linear in h when the scalars are complex. -/
def dualInjection (S : Operator 𝕜 H H) (h : H) : EnergyDual S :=
  (innerSL 𝕜 h).comp (position S)

/-- The form map u ↦ (w ↦ ⟨Su,Sw⟩), with the same dual convention. -/
def formFunctional (S : Operator 𝕜 H H) (u : GraphDomain S) : EnergyDual S :=
  (innerSL 𝕜 (gradient S u)).comp (gradient S)

/-- Weak equation in the manuscript's continuous scalar-linear dual.
The last field is exactly the scalar second-derivative identity, since the
preceding derivative field and real-time differentiation of inner products
give the first derivative ⟨v(t),w⟩. -/
structure IsEnergySolution (S : Operator 𝕜 H H)
    (u : ℝ → GraphDomain S) (v : ℝ → H) : Prop where
  continuous_graph : Continuous u
  continuous_velocity : Continuous v
  derivative : ∀ t, HasDerivAt (fun s => position S (u s)) (v t) t
  weak_derivative : ∀ (w : GraphDomain S) t,
    HasDerivAt (fun s => dualInjection S (v s) w) (-formFunctional S (u t) w) t

/-- The three bounded multipliers and the domain-carrying square root.
This record contains data only; the main theorems construct and identify them. -/
structure WaveFamily where
  S : Operator 𝕜 H H
  cosine : ℝ → H →L[𝕜] H
  sine : ℝ → H →L[𝕜] H
  quotient : ℝ → H →L[𝕜] H

namespace WaveFamily
variable (F : WaveFamily (𝕜 := 𝕜) (H := H))
def displacement (u₀ : GraphDomain F.S) (v₀ : H) (t : ℝ) : H :=
  F.cosine t (position F.S u₀) + F.quotient t v₀
def velocity (u₀ : GraphDomain F.S) (v₀ : H) (t : ℝ) : H :=
  -F.sine t (gradient F.S u₀) + F.cosine t v₀
end WaveFamily

def energy (S : Operator 𝕜 H H) (u : GraphDomain S) (v : H) : ℝ :=
  ‖gradient S u‖ ^ 2 + ‖v‖ ^ 2

def energyInner (S : Operator 𝕜 H H)
    (x y : GraphDomain S × H) : 𝕜 :=
  inner 𝕜 (gradient S x.1) (gradient S y.1) + inner 𝕜 x.2 y.2

/-- A faithful realization of the original energy space as a complete Hilbert
space. The coordinate bijection is scalar-linear and a homeomorphism for the
original graph-product topology, and the inner product is exactly the energy
form. Transport along this bijection gives the asserted Hilbert structure on
D(S) ⊕ H itself. It is required only under a positive gap. -/
structure EnergyHilbertModel (S : Operator 𝕜 H H) where
  Space : Type u
  [normed : NormedAddCommGroup Space]
  [innerProduct : InnerProductSpace 𝕜 Space]
  [complete : CompleteSpace Space]
  coordinates : (GraphDomain S × H) ≃L[𝕜] Space
  inner_eq : ∀ x y, inner 𝕜 (coordinates x) (coordinates y) = energyInner S x y

attribute [instance] EnergyHilbertModel.normed EnergyHilbertModel.innerProduct
  EnergyHilbertModel.complete

/-- Actual orthogonal projection onto the actual operator kernel. -/
def IsKernelProjection (L : Operator 𝕜 H H) (P : H →L[𝕜] H) : Prop :=
  (∀ x, P x ∈ L.ker) ∧ (∀ x : L.ker, P x = (x : H)) ∧
    ∀ x y, inner 𝕜 (P x) y = inner 𝕜 x (P y)

variable [CompleteSpace H]

def NonnegativeSelfAdjoint (L : Operator 𝕜 H H) : Prop :=
  Dense (L.domain : Set H) ∧ L.adjoint = L ∧
    ∀ x : L.domain, 0 ≤ RCLike.re (inner 𝕜 (x : H) (L x))

def IsNonnegativeSquareRoot (L S : Operator 𝕜 H H) : Prop :=
  NonnegativeSelfAdjoint S ∧
  OperatorDomainsSpec.productValue S S = L ∧ S.ker = L.ker

/-- Existence, uniqueness among all energy solutions, and exact conservation.
The velocity is the explicit spectral formula, not an assumed derivative. -/
def SolutionClaims (F : WaveFamily (𝕜 := 𝕜) (H := H)) : Prop :=
  ∀ (u₀ : GraphDomain F.S) (v₀ : H),
    ∃ u : ℝ → GraphDomain F.S,
      (∀ t, position F.S (u t) = F.displacement u₀ v₀ t) ∧
      IsEnergySolution F.S u (F.velocity u₀ v₀) ∧
      u 0 = u₀ ∧ F.velocity u₀ v₀ 0 = v₀ ∧
      (∀ (z : ℝ → GraphDomain F.S) (w : ℝ → H),
        IsEnergySolution F.S z w → z 0 = u₀ → w 0 = v₀ →
        z = u ∧ w = F.velocity u₀ v₀) ∧
      ∀ t, energy F.S (u t) (F.velocity u₀ v₀ t) = energy F.S u₀ v₀

def ClassicalClaims (L : Operator 𝕜 H H)
    (F : WaveFamily (𝕜 := 𝕜) (H := H)) : Prop :=
  ∀ (u₀ : GraphDomain F.S) (v₀ : H),
    position F.S u₀ ∈ L.domain → v₀ ∈ F.S.domain →
    ContDiff ℝ 2 (F.displacement u₀ v₀) ∧
      ∀ t, ∃ h : F.displacement u₀ v₀ t ∈ L.domain,
        HasDerivAt (F.velocity u₀ v₀) (-L ⟨F.displacement u₀ v₀ t, h⟩) t

/-- The gap is the form inequality on the original D(L), without a spectral
representation hypothesis. Linear isometry *equivalences* include surjectivity.
The coordinate identity identifies the group with the actual wave state maps. -/
def GapGroup (L : Operator 𝕜 H H)
    (F : WaveFamily (𝕜 := 𝕜) (H := H)) : Prop :=
  ∀ c : ℝ, 0 < c →
    (∀ x : L.domain, c * ‖(x : H)‖ ^ 2 ≤ RCLike.re (inner 𝕜 (x : H) (L x))) →
    ∃ M : EnergyHilbertModel F.S, ∃ U : ℝ → M.Space ≃ₗᵢ[𝕜] M.Space,
      (∀ x, U 0 x = x) ∧
      (∀ s t x, U (s + t) x = U s (U t x)) ∧
      (∀ x, Continuous (fun t => U t x)) ∧
      ∀ (x : GraphDomain F.S × H) t,
        position F.S (M.coordinates.symm (U t (M.coordinates x))).1 =
          F.displacement x.1 x.2 t ∧
        (M.coordinates.symm (U t (M.coordinates x))).2 = F.velocity x.1 x.2 t

def WaveTheorem (L : Operator 𝕜 H H)
    (F : WaveFamily (𝕜 := 𝕜) (H := H)) : Prop :=
  IsNonnegativeSquareRoot L F.S ∧ SolutionClaims F ∧ ClassicalClaims L F ∧
    (∃ P : H →L[𝕜] H, IsKernelProjection L P ∧
      ∀ (u₀ : GraphDomain F.S) (v₀ : H) t,
        P (F.displacement u₀ v₀ t) = P (position F.S u₀) + t • P v₀) ∧
    GapGroup L F
end General

/-- Exactly the real calculus supplied by the upstream restriction bridge. -/
def realFamily {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (C : RealNonnegativeSpectralCalculus.Calculus (H := H)) :
    WaveFamily (𝕜 := ℝ) (H := H) where
  S := RealNonnegativeSpectralCalculus.squareRoot C
  cosine := RealNonnegativeSpectralCalculus.cosOperator C
  sine := RealNonnegativeSpectralCalculus.sinOperator C
  quotient := RealNonnegativeSpectralCalculus.quotientOperator C

def complexSymbol (f : ℝ≥0 → ℝ) : ℝ≥0 → ℂ := fun s => (f s : ℂ)

/-- The square root and bounded wave multipliers of the same complex PVM. -/
def complexFamily {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 H}
    (C : MeasurableSpectralCalculus.BoundedRealization E) :
    WaveFamily (𝕜 := ℂ) (H := H) where
  S := MeasurableSpectralCalculus.measurableIntegral C (complexSymbol RealSymbols.root)
  cosine := fun t => C.integral (complexSymbol (RealSymbols.cosine t))
  sine := fun t => C.integral (complexSymbol (RealSymbols.sine t))
  quotient := fun t => C.integral (complexSymbol (RealSymbols.quotientSine t))

namespace Spec

def RealTheorem : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (L : Operator ℝ H H), NonnegativeSelfAdjoint L →
    ∃ C : RealNonnegativeSpectralCalculus.Calculus (H := H),
      C.integral RealSymbols.coordinate = L ∧ WaveTheorem L (realFamily C)

def ComplexTheorem : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : Operator ℂ H H), NonnegativeSelfAdjoint L →
    letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
    ∃ (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 H)
      (C : MeasurableSpectralCalculus.BoundedRealization E),
      MeasurableSpectralCalculus.measurableIntegral C
        (complexSymbol RealSymbols.coordinate) = L ∧ WaveTheorem L (complexFamily C)

def FullTheorem : Prop := RealTheorem.{u} ∧ ComplexTheorem.{u}

def ComplexSpectralExistence : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : Operator ℂ H H), NonnegativeSelfAdjoint L →
    ∃ (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 H)
      (C : MeasurableSpectralCalculus.BoundedRealization E),
      MeasurableSpectralCalculus.measurableIntegral C
        (complexSymbol RealSymbols.coordinate) = L

/-- Graph-domain and S-evaluation of the real spectral formula. -/
def RealDisplacementGraph : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : RealNonnegativeSpectralCalculus.Calculus (H := H))
    (u₀ : GraphDomain (realFamily C).S) (v₀ : H) t,
    ((realFamily C).displacement u₀ v₀ t,
      (realFamily C).cosine t (gradient (realFamily C).S u₀) +
        (realFamily C).sine t v₀) ∈ (realFamily C).S.graph

/-- Energy conservation, stated without assuming time differentiability. -/
def RealFormulaEnergy : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : RealNonnegativeSpectralCalculus.Calculus (H := H))
    (u₀ : GraphDomain (realFamily C).S) (v₀ : H) t,
    ‖(realFamily C).cosine t (gradient (realFamily C).S u₀) +
      (realFamily C).sine t v₀‖ ^ 2 + ‖(realFamily C).velocity u₀ v₀ t‖ ^ 2 =
      energy (realFamily C).S u₀ v₀

def RealGraphContinuity : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : RealNonnegativeSpectralCalculus.Calculus (H := H))
    (u₀ : GraphDomain (realFamily C).S) (v₀ : H),
    (∃ u : ℝ → GraphDomain (realFamily C).S,
      Continuous u ∧ ∀ t,
        position (realFamily C).S (u t) = (realFamily C).displacement u₀ v₀ t ∧
        gradient (realFamily C).S (u t) =
          (realFamily C).cosine t (gradient (realFamily C).S u₀) +
            (realFamily C).sine t v₀) ∧
    Continuous ((realFamily C).velocity u₀ v₀)

def RealInitialConditions : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : RealNonnegativeSpectralCalculus.Calculus (H := H))
    (u₀ : GraphDomain (realFamily C).S) (v₀ : H),
    (realFamily C).displacement u₀ v₀ 0 = position (realFamily C).S u₀ ∧
      (realFamily C).velocity u₀ v₀ 0 = v₀

def RealSquareRoot : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : RealNonnegativeSpectralCalculus.Calculus (H := H)),
    IsNonnegativeSquareRoot (C.integral RealSymbols.coordinate) (realFamily C).S

end Spec
end ExpandedFA.Models.AbstractWaveEnergy
