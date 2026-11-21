import MathGenome.Internal.Specs.D05.M15.Charcoefficients

/-!
Independent specification for K05.15.charcoefficients, paper.tex:3187.
The two factors are arbitrary endomorphisms of the same finite-dimensional
space over any field. The exterior powers and characteristic polynomial are
the shared canonical objects. No invertibility, splitting, characteristic,
positive dimension, or positive degree hypothesis is imposed.
-/

noncomputable section
namespace Specs.D05.M15.Charcoefficients.AbBa

/-- Every exterior trace agrees, including degree zero and degrees above dimension. -/
def exterior_trace_comp_comm : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A B : V →ₗ[K] V) (p : ℕ),
    LinearMap.trace K (⋀[K]^p V) (WedgeSign.powerMap_value p (A.comp B)) =
      LinearMap.trace K (⋀[K]^p V) (WedgeSign.powerMap_value p (B.comp A))

/-- Equality of formal characteristic polynomials, also for singular factors. -/
def charpoly_comp_comm : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A B : V →ₗ[K] V),
    Specs.D05.M08.Charpoly.charpoly_value (A.comp B) =
      Specs.D05.M08.Charpoly.charpoly_value (B.comp A)

/-- Consequently every formal coefficient agrees, with no restriction on its index. -/
def charpoly_coeff_comp_comm : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A B : V →ₗ[K] V) (k : ℕ),
    (Specs.D05.M08.Charpoly.charpoly_value (A.comp B)).coeff k =
      (Specs.D05.M08.Charpoly.charpoly_value (B.comp A)).coeff k

end Specs.D05.M15.Charcoefficients.AbBa
