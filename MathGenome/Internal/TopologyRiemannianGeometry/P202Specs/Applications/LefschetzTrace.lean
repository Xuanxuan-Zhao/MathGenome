import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The algebraic trace identity in paper.tex, 2916–2923.

Complexes and endomorphisms are the usual Mathlib chain complexes and chain maps.
The integer interval may begin in any degree, so shifted and augmented complexes
are included. Vanishing outside that interval means that the chain groups are
subsingleton; no hypothesis is imposed on the chain endomorphism beyond being a
chain map. Homology is also described concretely as cycles modulo boundaries.
-/

open CategoryTheory HomologicalComplex
open scoped BigOperators

universe u v
namespace P202Specs.LefschetzTrace

section LinearAlgebra
variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

/-- Trace additivity for an arbitrary invariant subspace. -/
def InvariantTraceType : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V) (p : Submodule K V) (hp : ∀ x ∈ p, f x ∈ p),
    LinearMap.trace K V f = LinearMap.trace K p (f.restrict hp) +
      LinearMap.trace K (V ⧸ p) (p.mapQ p f hp)
end LinearAlgebra

section Complex
variable {K : Type u} [Field K] (C : ChainComplex (ModuleCat.{v} K) ℤ)

/-- The cycles in degree `n`. -/
def cycles (n : ℤ) : Submodule K (C.X n) :=
  LinearMap.ker (C.d n (n - 1)).hom

/-- The boundaries in degree `n`, as a subspace of the chain group. -/
def boundaries (n : ℤ) : Submodule K (C.X n) :=
  LinearMap.range (C.d (n + 1) n).hom

/-- The differential with codomain restricted to cycles. -/
def toCycles (n : ℤ) : C.X (n + 1) →ₗ[K] cycles C n :=
  (C.d (n + 1) n).hom.codRestrict _ (fun x => by
    change (C.d n (n - 1)) ((C.d (n + 1) n) x) = 0
    exact congr($(C.d_comp_d (n + 1) n (n - 1)) x))

/-- Boundaries viewed as a subspace of cycles. -/
def boundaryCycles (n : ℤ) : Submodule K (cycles C n) :=
  LinearMap.range (toCycles C n)

/-- The usual kernel/image quotient definition of homology. -/
abbrev Homology (n : ℤ) := cycles C n ⧸ boundaryCycles C n

variable (F : C ⟶ C)

/-- The restricted chain endomorphism on cycles. -/
def onCycles (n : ℤ) : cycles C n →ₗ[K] cycles C n :=
  (F.f n).hom.restrict (by
    intro x hx
    change (C.d n (n - 1)) ((F.f n) x) = 0
    rw [← ModuleCat.comp_apply, F.comm, ModuleCat.comp_apply]
    rw [show (C.d n (n - 1)) x = 0 from hx, map_zero])

/-- The restricted chain endomorphism on boundaries. -/
def onBoundaries (n : ℤ) : boundaries C n →ₗ[K] boundaries C n :=
  (F.f n).hom.restrict (by
    rintro x ⟨y, rfl⟩
    refine ⟨(F.f (n + 1)) y, ?_⟩
    exact congr($(F.comm (n + 1) n) y))

/-- Invariance of boundaries inside cycles. -/
theorem preserves_boundaryCycles (n : ℤ) :
    ∀ x ∈ boundaryCycles C n, onCycles C F n x ∈ boundaryCycles C n := by
  rintro x ⟨y, rfl⟩
  refine ⟨(F.f (n + 1)) y, ?_⟩
  apply Subtype.ext
  exact congr($(F.comm (n + 1) n) y)

/-- The induced map `[z] ↦ [F z]` on homology. -/
def onHomology (n : ℤ) : Homology C n →ₗ[K] Homology C n :=
  (boundaryCycles C n).mapQ _ (onCycles C F n) (preserves_boundaryCycles C F n)

/-- The differential identifies `Cₙ/Zₙ` with `Bₙ₋₁`. -/
def BoundaryQuotientType : Prop :=
  ∀ n : ℤ, ∃ e : (C.X n ⧸ cycles C n) ≃ₗ[K] boundaries C (n - 1),
    (∀ x, (e ((cycles C n).mkQ x) : C.X (n - 1)) = (C.d n (n - 1)) x) ∧
    (∀ x, e ((cycles C n).mapQ _ (F.f n).hom (by
      intro x hx; exact (onCycles C F n ⟨x, hx⟩).property) x) =
      onBoundaries C F (n - 1) (e x))

/-- The cycle quotient is equivariantly the categorical homology used upstream. -/
def HomologyQuotientType : Prop :=
  ∀ n : ℤ, ∃ e : (C.homology n) ≃ₗ[K] Homology C n,
    ∀ x, e ((homologyMap F n) x) = onHomology C F n (e x)

/-- Degreewise trace decomposition, with both boundary terms explicit. -/
def DegreeTraceType : Prop :=
  ∀ n : ℤ, LinearMap.trace K (C.X n) (F.f n).hom =
    LinearMap.trace K (C.homology n) (homologyMap F n).hom +
    LinearMap.trace K (boundaries C n) (onBoundaries C F n) +
    LinearMap.trace K (boundaries C (n - 1)) (onBoundaries C F (n - 1))

/-- Finite complexes are supported in an arbitrary finite interval of degrees. -/
def SupportedIn (a : ℤ) (N : ℕ) : Prop :=
  ∀ n, n < a ∨ a + (N : ℤ) ≤ n → Subsingleton (C.X n)

/-- The full Hopf trace formula, including the zero complex and shifted complexes. -/
def TraceIdentityType : Prop :=
  ∀ (a : ℤ) (N : ℕ), SupportedIn C a N →
    (∑ j ∈ Finset.range N, (-1 : K) ^ (a + (j : ℤ)) *
      LinearMap.trace K (C.X (a + (j : ℤ))) (F.f (a + (j : ℤ))).hom) =
    ∑ j ∈ Finset.range N, (-1 : K) ^ (a + (j : ℤ)) *
      LinearMap.trace K (C.homology (a + (j : ℤ)))
        (homologyMap F (a + (j : ℤ))).hom
end Complex
/-- Universally quantified independent theorem contracts. -/
def InvariantTraceStatement : Prop :=
  ∀ {K : Type u} [Field K], InvariantTraceType.{u,v} (K := K)

def BoundaryQuotientStatement : Prop :=
  ∀ {K : Type u} [Field K] (C : ChainComplex (ModuleCat.{v} K) ℤ) (F : C ⟶ C),
    BoundaryQuotientType C F

def HomologyQuotientStatement : Prop :=
  ∀ {K : Type u} [Field K] (C : ChainComplex (ModuleCat.{v} K) ℤ) (F : C ⟶ C),
    HomologyQuotientType C F

def DegreeTraceStatement : Prop :=
  ∀ {K : Type u} [Field K] (C : ChainComplex (ModuleCat.{v} K) ℤ) (F : C ⟶ C)
    [∀ n, FiniteDimensional K (C.X n)], DegreeTraceType C F

def TraceIdentityStatement : Prop :=
  ∀ {K : Type u} [Field K] (C : ChainComplex (ModuleCat.{v} K) ℤ) (F : C ⟶ C)
    [∀ n, FiniteDimensional K (C.X n)], TraceIdentityType C F

end P202Specs.LefschetzTrace
