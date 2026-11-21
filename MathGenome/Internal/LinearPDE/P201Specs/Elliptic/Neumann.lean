import MathGenome.Internal.LinearPDE.P201Specs.Common.NormalTrace
import MathGenome.Internal.FourierSobolev.P102.Sobolev.MeanZeroPoincare
import Mathlib.Analysis.Normed.Group.Quotient

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped InnerProductSpace ENNReal
namespace P201Specs.Neumann

/-- Finite volume follows from the actual bounded Lipschitz geometry. -/
theorem finiteVolume {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) : IsFiniteMeasure (domainMeasure Ω) :=
  isFiniteMeasure_restrict.mpr
    (P102.Sobolev.Rellich.bounded_domain (graphFrame m) Ω hΩ).measure_lt_top.ne

/-- The H¹ class of a constant, with all positive derivatives zero. -/
def constant {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (c : ℝ) : H ℝ Ω 1 := by
  letI := finiteVolume Ω hΩ
  exact (hToW ℝ Ω 1).symm
    (P102.Sobolev.MeanZeroPoincare.exists_constant Ω 2 c).choose

/-- The mean uses the actual Lebesgue measure on Ω. -/
def mean {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) : ℝ :=
  ((domainMeasure Ω).real Set.univ)⁻¹ * ∫ x in Ω, hUnderlying Ω 1 u x

/-- The physical weak Neumann equation with the full H¹ test class. -/
def IsSolution {m : ℕ} {Ω : Domain (m + 1)} {hΩ : IsBoundedLipschitzOpen Ω}
    (D : NormalTrace.TraceData Ω hΩ) (f : Lp ℝ Ω 2) (g : HminusHalf Ω hΩ)
    (u : H ℝ Ω 1) : Prop :=
  ∀ v : H ℝ Ω 1,
    (∫ x in Ω, inner ℝ (hGradient u x) (hGradient v x)) =
      (∫ x in Ω, f x * hUnderlying Ω 1 v x) + g (D.trace v)

/-- The boundary constant is the physical trace of the bulk constant one. -/
def Compatible {m : ℕ} {Ω : Domain (m + 1)} {hΩ : IsBoundedLipschitzOpen Ω}
    (D : NormalTrace.TraceData Ω hΩ) (f : Lp ℝ Ω 2) (g : HminusHalf Ω hΩ) : Prop :=
  (∫ x in Ω, f x) + g (D.trace (constant Ω hΩ 1)) = 0

/-- The constants in the actual H¹ space. -/
def constants {n : ℕ} (Ω : Domain n) : Submodule ℝ (H ℝ Ω 1) where
  carrier := {u | ∃ c : ℝ, (hUnderlying Ω 1 u : Space n → ℝ) =ᵐ[domainMeasure Ω] fun _ => c}
  zero_mem' := by
    refine ⟨0, ?_⟩
    change (hUnderlying Ω 1 (0 : H ℝ Ω 1) : Space n → ℝ) =ᵐ[_] _
    rw [map_zero]
    filter_upwards [Lp.coeFn_zero ℝ 2 (domainMeasure Ω)] with x hx
    exact hx
  add_mem' := by
    rintro u v ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c + d, ?_⟩
    change (hUnderlying Ω 1 (u + v) : Space n → ℝ) =ᵐ[_] _
    rw [map_add]
    exact (Lp.coeFn_add _ _).trans (hc.add hd)
  smul_mem' := by
    rintro c u ⟨d, hd⟩
    refine ⟨c * d, ?_⟩
    rw [map_smul]
    exact (Lp.coeFn_smul _ _).trans (hd.const_smul c)

/-- This is the standard quotient seminorm; the theorem proves the required
estimate, and constants form a closed finite dimensional subspace. -/
abbrev Quotient {n : ℕ} (Ω : Domain n) := (H ℝ Ω 1) ⧸ constants Ω

/-- Connected zero distributional gradient implies a single a.e. constant. -/
def ZeroGradientStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n) (hconn : IsConnected (Ω : Set (Space n)))
    (u : Space n → ℝ), LocallyIntegrableOn u Ω volume →
    (∀ i : Fin n, distributionDerivative {i} (regularDistribution Ω u) = 0) →
    ∃! c : ℝ, u =ᵐ[domainMeasure Ω] fun _ => c

/-- A full-H¹ mean-zero Poincaré inequality on the concrete shared space. -/
def PoincareStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω),
    IsConnected (Ω : Set (Space (m + 1))) →
    ∃ C : ℝ, 0 < C ∧ ∀ u : H ℝ Ω 1, mean Ω u = 0 →
      ‖u‖ ≤ C * ‖hGradient u‖

/-- Existence iff compatibility, all solutions differ by exactly one constant,
a unique mean-zero representative, and the full and quotient norm estimates. -/
def SolvabilityStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω),
    IsConnected (Ω : Set (Space (m + 1))) →
    ∀ D : NormalTrace.TraceData Ω hΩ, ∃ C : ℝ, 0 < C ∧
      ∀ (f : Lp ℝ Ω 2) (g : HminusHalf Ω hΩ),
        ((∃ u, IsSolution D f g u) ↔ Compatible D f g) ∧
        (∀ u v, IsSolution D f g u → IsSolution D f g v →
          ∃! c : ℝ, u = v + constant Ω hΩ c) ∧
        (Compatible D f g → ∃! u, IsSolution D f g u ∧ mean Ω u = 0) ∧
        (∀ u, IsSolution D f g u → mean Ω u = 0 →
          ‖u‖ ≤ C * (‖f‖ + ‖g‖)) ∧
        (∀ u, IsSolution D f g u →
          ‖(Submodule.Quotient.mk u : Quotient Ω)‖ ≤ C * (‖f‖ + ‖g‖))

/-- The variational solution solves -Δu=f and has weak normal trace g. -/
def IdentificationStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (D : NormalTrace.TraceData Ω hΩ) (f : Lp ℝ Ω 2) (g : HminusHalf Ω hΩ)
    (u : H ℝ Ω 1), IsSolution D f g u →
      NormalTrace.HasLaplacian Ω u (-f) ∧
      NormalTrace.HasDivergence Ω (hGradient u) (-f) ∧
      NormalTrace.Pairing D (hGradient u) (-f) g

/-- A finite disjoint union with separate component Sobolev spaces and traces.
The product represents functions on the union by their restrictions. The empty
finite family is allowed; every actual component is nonempty and connected. -/
def ComponentsStatement : Prop :=
  ∀ {m k : ℕ} (Ω : Fin k → Domain (m + 1))
    (hΩ : ∀ i, IsBoundedLipschitzOpen (Ω i))
    (_ : ∀ i, IsConnected (Ω i : Set (Space (m + 1))))
    (_ : Pairwise fun i j => Disjoint (Ω i : Set (Space (m + 1))) (Ω j : Set (Space (m + 1))))
    (D : ∀ i, NormalTrace.TraceData (Ω i) (hΩ i))
    (f : ∀ i, Lp ℝ (Ω i) 2) (g : ∀ i, HminusHalf (Ω i) (hΩ i)),
      ((∃ u : ∀ i, H ℝ (Ω i) 1, ∀ i, IsSolution (D i) (f i) (g i) (u i)) ↔
        ∀ i, Compatible (D i) (f i) (g i)) ∧
      (∀ u v : ∀ i, H ℝ (Ω i) 1,
        (∀ i, IsSolution (D i) (f i) (g i) (u i)) →
        (∀ i, IsSolution (D i) (f i) (g i) (v i)) →
        ∃! c : Fin k → ℝ, ∀ i, u i = v i + constant (Ω i) (hΩ i) (c i))

/-- Restriction of the actual bulk class and every weak gradient coordinate. -/
def RestrictsTo {n : ℕ} (U V : Domain n) (u : H ℝ U 1) (v : H ℝ V 1) : Prop :=
  (hUnderlying U 1 u : Space n → ℝ) =ᵐ[domainMeasure V] hUnderlying V 1 v ∧
    ∀ j, (hFirstDerivative u j : Space n → ℝ) =ᵐ[domainMeasure V] hFirstDerivative v j

/-- A solution on the actual finite union, with separate component traces.
The left side is the integral on the union; the forcing and boundary terms
are summed over components. The final theorem also establishes that every
global H¹ test has its component restrictions. -/
def IsUnionSolution {m k : ℕ} (Ω : Fin k → Domain (m + 1))
    (hΩ : ∀ i, IsBoundedLipschitzOpen (Ω i))
    (D : ∀ i, NormalTrace.TraceData (Ω i) (hΩ i))
    (f : ∀ i, Lp ℝ (Ω i) 2) (g : ∀ i, HminusHalf (Ω i) (hΩ i))
    (u : H ℝ (⨆ i, Ω i) 1) : Prop :=
  (∃ us : ∀ i, H ℝ (Ω i) 1, ∀ i, RestrictsTo (⨆ i, Ω i) (Ω i) u (us i)) ∧
    ∀ (v : H ℝ (⨆ i, Ω i) 1) (vs : ∀ i, H ℝ (Ω i) 1),
      (∀ i, RestrictsTo (⨆ i, Ω i) (Ω i) v (vs i)) →
      (∫ x in (⨆ i, Ω i : Domain (m + 1)), inner ℝ (hGradient u x) (hGradient v x)) =
        ∑ i, ((∫ x in Ω i, f i x * hUnderlying (Ω i) 1 (vs i) x) + g i ((D i).trace (vs i)))

/-- Full finite-union conclusion on canonical H¹, with a separately chosen
constant on each component; there is no assumption about a global Lipschitz
boundary of the union, nor any separation of component closures. -/
def FiniteUnionStatement : Prop :=
  ∀ {m k : ℕ} (Ω : Fin k → Domain (m + 1))
    (hΩ : ∀ i, IsBoundedLipschitzOpen (Ω i))
    (_ : ∀ i, IsConnected (Ω i : Set (Space (m + 1))))
    (_ : Pairwise fun i j => Disjoint (Ω i : Set (Space (m + 1))) (Ω j : Set (Space (m + 1))))
    (D : ∀ i, NormalTrace.TraceData (Ω i) (hΩ i)),
      (∀ v : H ℝ (⨆ i, Ω i) 1,
        ∃ vs : ∀ i, H ℝ (Ω i) 1, ∀ i, RestrictsTo (⨆ i, Ω i) (Ω i) v (vs i)) ∧
      ∀ (f : ∀ i, Lp ℝ (Ω i) 2) (g : ∀ i, HminusHalf (Ω i) (hΩ i)),
        ((∃ u, IsUnionSolution Ω hΩ D f g u) ↔ ∀ i, Compatible (D i) (f i) (g i)) ∧
        (∀ u v, IsUnionSolution Ω hΩ D f g u → IsUnionSolution Ω hΩ D f g v →
          ∃! c : Fin k → ℝ, ∀ i,
            (fun x => hUnderlying (⨆ i, Ω i) 1 u x - hUnderlying (⨆ i, Ω i) 1 v x)
              =ᵐ[domainMeasure (Ω i)] fun _ => c i)

end P201Specs.Neumann
