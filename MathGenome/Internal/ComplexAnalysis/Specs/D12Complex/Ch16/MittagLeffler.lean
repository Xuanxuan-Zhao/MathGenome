import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.LocalQuotientsArithmetic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.PNat.Basic

/-! Independent statements for paper.tex:2828–2835 (d12:16-07).
Finite principal parts have arbitrary complex coefficients indexed by positive
integers; the finitely supported zero sequence includes zero and empty data.
All equalities at singularities use the existing scalar filling convention.
No connectedness or nonemptiness assumption is imposed on the open set. -/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D12Complex.Ch16.MittagLeffler.Objects
open _root_.D12Complex

/-- Finite principal parts, including the zero part. -/
abbrev PrincipalPart := ℕ+ →₀ ℂ

/-- The finite sum ∑ cₖ/(z-a)^k. Its value at a is irrelevant. -/
def principalPartValue (p : PrincipalPart) (a z : ℂ) : ℂ :=
  p.sum (fun k c => c / (z - a) ^ (k : ℕ))

/-- Local finiteness in Ω, in its equivalent compact-subset formulation. -/
def LocallyFiniteIn (Ω A : Set ℂ) : Prop :=
  A ⊆ Ω ∧ ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → (A ∩ K).Finite

/-- An analytic remainder at a, with equality of punctured germs. -/
def HasPrincipalPart (F : ℂ → RiemannSphere) (a : ℂ) (p : PrincipalPart) : Prop :=
  ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧
    scalarFinitePart F =ᶠ[𝓝[≠] a] fun z => principalPartValue p a z + h z

/-- Exactly the prescribed principal parts and no other poles. -/
def IsSolution (Ω A : Set ℂ) (p : A → PrincipalPart)
    (F : ℂ → RiemannSphere) : Prop :=
  ScalarMeromorphicOn Ω F ∧
    (∀ z ∈ Ω, z ∉ A → F z ≠ sphereInfty) ∧
    (∀ a : A, HasPrincipalPart F a (p a))

/-- Addition of a finite holomorphic function, with removable values filled. -/
def addHolomorphic (F : ℂ → RiemannSphere) (h : ℂ → ℂ) : ℂ → RiemannSphere :=
  Specs.D12Complex.Ch07.LocalQuotientsArithmetic.Objects.fill
    (fun z => scalarFinitePart F z + h z)

end Specs.D12Complex.Ch16.MittagLeffler.Objects

namespace Specs.D12Complex.Ch16.MittagLeffler
open _root_.D12Complex Objects

def PrincipalPart_type := Type
def PrincipalPart_value : PrincipalPart_type := ℕ+ →₀ ℂ

def principalPartValue_type := PrincipalPart → ℂ → ℂ → ℂ
def principalPartValue_value : principalPartValue_type :=
  fun p a z => p.sum (fun k c => c / (z - a) ^ (k : ℕ))

def LocallyFiniteIn_type := Set ℂ → Set ℂ → Prop
def LocallyFiniteIn_value : LocallyFiniteIn_type := fun Ω A =>
  A ⊆ Ω ∧ ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → (A ∩ K).Finite

def HasPrincipalPart_type := (ℂ → RiemannSphere) → ℂ → PrincipalPart → Prop
def HasPrincipalPart_value : HasPrincipalPart_type := fun F a p =>
  ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧
    scalarFinitePart F =ᶠ[𝓝[≠] a] fun z => principalPartValue p a z + h z

def IsSolution_type := Set ℂ → (A : Set ℂ) → (A → PrincipalPart) →
  (ℂ → RiemannSphere) → Prop
def IsSolution_value : IsSolution_type := fun Ω A p F =>
  ScalarMeromorphicOn Ω F ∧
    (∀ z ∈ Ω, z ∉ A → F z ≠ sphereInfty) ∧
    (∀ a : A, HasPrincipalPart F a (p a))

def addHolomorphic_type := (ℂ → RiemannSphere) → (ℂ → ℂ) → ℂ → RiemannSphere
def addHolomorphic_value : addHolomorphic_type := fun F h =>
  Specs.D12Complex.Ch07.LocalQuotientsArithmetic.Objects.fill
    (fun z => scalarFinitePart F z + h z)

/-- The existence conclusion, without excluding zero coefficients or empty Ω. -/
def mittag_leffler_exists_type : Prop :=
  ∀ (Ω A : Set ℂ), IsOpen Ω → LocallyFiniteIn Ω A →
    ∀ p : A → PrincipalPart, ∃ F : ℂ → RiemannSphere, IsSolution Ω A p F

/-- Finite data, including the empty set, already admit a finite-sum solution. -/
def mittag_leffler_finite_type : Prop :=
  ∀ (Ω A : Set ℂ), IsOpen Ω → A ⊆ Ω → A.Finite →
    ∀ p : A → PrincipalPart, ∃ F : ℂ → RiemannSphere, IsSolution Ω A p F

/-- Every designated point is an actual pole exactly when its part is nonzero. -/
def solution_pole_iff_type : Prop :=
  ∀ (Ω A : Set ℂ) (p : A → PrincipalPart) (F : ℂ → RiemannSphere),
    IsSolution Ω A p F → ∀ a : A, (a : ℂ) ∈ Ω →
      (F a = sphereInfty ↔ p a ≠ 0)

/-- The complete solution set is a solution plus all holomorphic functions.
Equality is on Ω, since total extensions outside Ω are immaterial. -/
def solution_affine_type : Prop :=
  ∀ (Ω A : Set ℂ) (p : A → PrincipalPart) (F G : ℂ → RiemannSphere),
    A ⊆ Ω → IsSolution Ω A p F →
    (IsSolution Ω A p G ↔ ∃ h : ℂ → ℂ, HolomorphicOn Ω h ∧
      EqOn G (addHolomorphic F h) Ω)

end Specs.D12Complex.Ch16.MittagLeffler
