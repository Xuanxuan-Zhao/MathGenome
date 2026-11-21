import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.LinearAlgebra.Basis.Submodule

/-!
Independent specifications for paper.tex 1121–1125 (the general separable
stage in the proof of Theorem 6.8). D is an arbitrary Noetherian integrally
closed domain, E any field of fractions, and F any finite separable extension.
No characteristic assumption or nonvanishing assumption on Tr(1) is made.
The lattice is a span over D inside F, whereas both bases are over E.
-/

universe u v w t

namespace P103.Specs.Ch06.SeparableIntegralClosureFinite

/-- An integral E-basis exists by clearing denominators. -/
def integral_basisType : Prop :=
  ∀ (D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D]
    [IsIntegrallyClosed D] (E : Type v) [Field E] [Algebra D E]
    [IsFractionRing D E] (F : Type w) [Field F] [Algebra E F]
    [Algebra D F] [IsScalarTower D E F] [FiniteDimensional E F]
    [Algebra.IsSeparable E F],
    ∃ (s : Finset F) (b : Module.Basis s E F), ∀ i, IsIntegral D (b i)

/-- The trace-dual basis pairs with the integral basis by the Kronecker delta. -/
def trace_dualityType : Prop :=
  ∀ (D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D]
    [IsIntegrallyClosed D] (E : Type v) [Field E] [Algebra D E]
    [IsFractionRing D E] (F : Type w) [Field F] [Algebra E F]
    [Algebra D F] [IsScalarTower D E F] [FiniteDimensional E F]
    [Algebra.IsSeparable E F],
    ∀ (ι : Type t) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι E F),
    ∀ i j, Algebra.trace E F (b i * b.traceDual j) = if i = j then 1 else 0

/-- Expansion in the trace-dual basis, for every element of F. -/
def trace_expansionType : Prop :=
  ∀ (D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D]
    [IsIntegrallyClosed D] (E : Type v) [Field E] [Algebra D E]
    [IsFractionRing D E] (F : Type w) [Field F] [Algebra E F]
    [Algebra D F] [IsScalarTower D E F] [FiniteDimensional E F]
    [Algebra.IsSeparable E F],
    ∀ (ι : Type t) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι E F),
    ∀ z : F, z = ∑ i, Algebra.trace E F (z * b i) • b.traceDual i

/-- For integral z and b i the trace coefficients belong to D inside E. -/
def trace_coefficientsType : Prop :=
  ∀ (D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D]
    [IsIntegrallyClosed D] (E : Type v) [Field E] [Algebra D E]
    [IsFractionRing D E] (F : Type w) [Field F] [Algebra E F]
    [Algebra D F] [IsScalarTower D E F] [FiniteDimensional E F]
    [Algebra.IsSeparable E F],
    ∀ (ι : Type t) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι E F),
    (∀ i, IsIntegral D (b i)) → ∀ z : F, IsIntegral D z →
    ∀ i, ∃ d : D, algebraMap D E d = Algebra.trace E F (z * b i)

/-- The integral closure lies in the finite free D-lattice on the trace-dual basis. -/
def trace_latticeType : Prop :=
  ∀ (D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D]
    [IsIntegrallyClosed D] (E : Type v) [Field E] [Algebra D E]
    [IsFractionRing D E] (F : Type w) [Field F] [Algebra E F]
    [Algebra D F] [IsScalarTower D E F] [FiniteDimensional E F]
    [Algebra.IsSeparable E F],
    ∀ (ι : Type t) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι E F),
    (∀ i, IsIntegral D (b i)) →
    (integralClosure D F).toSubmodule ≤ Submodule.span D (Set.range b.traceDual) ∧
    Module.Free D (Submodule.span D (Set.range b.traceDual)) ∧
    Module.Finite D (Submodule.span D (Set.range b.traceDual))

/-- The general separable stage of Theorem 6.8, independent of affine normalization. -/
def finite_integralClosureType : Prop :=
  ∀ (D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D]
    [IsIntegrallyClosed D] (E : Type v) [Field E] [Algebra D E]
    [IsFractionRing D E] (F : Type w) [Field F] [Algebra E F]
    [Algebra D F] [IsScalarTower D E F] [FiniteDimensional E F]
    [Algebra.IsSeparable E F],
    Module.Finite D (integralClosure D F)

end P103.Specs.Ch06.SeparableIntegralClosureFinite
