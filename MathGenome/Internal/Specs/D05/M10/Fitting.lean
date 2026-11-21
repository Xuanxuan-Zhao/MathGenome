import MathGenome.Internal.Specs.D05.M06.DirectSum
import MathGenome.Internal.Specs.D05.M10.Nilpotent

/-!
Independent statements for K05.10.fitting, paper.tex:1430–1438.
The summands are the actual kernel and image of the dimension-th power over
the original field. Invertibility concerns the actual restricted map, expressed
by a linear equivalence with that underlying linear map. Dimension zero is
included. The invariance and kernel-restriction statements hold for every
exponent, even without finite dimension.
-/

namespace Specs.D05.M10.Fitting

def kernel_invariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (n : ℕ),
    ∀ x ∈ LinearMap.ker (T ^ n), T x ∈ LinearMap.ker (T ^ n)

def image_invariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (n : ℕ),
    ∀ x ∈ LinearMap.range (T ^ n), T x ∈ LinearMap.range (T ^ n)

/-- Unique expression as the sum of a kernel vector and an image vector. -/
def decomposition : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (n : ℕ),
    Module.finrank K V = n →
      Specs.D05.M06.DirectSum.UniqueDecomposition
        (fun b : Bool => if b then LinearMap.range (T ^ n) else LinearMap.ker (T ^ n))

/-- Nilpotence includes the source's positive-exponent convention. -/
def kernel_restriction_nilpotent : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (n : ℕ)
    (h : ∀ x ∈ LinearMap.ker (T ^ n), T x ∈ LinearMap.ker (T ^ n)),
    (T.restrict h) ^ n = 0 ∧ IsNilpotent (T.restrict h) ∧
      ∃ r : ℕ, 0 < r ∧ (T.restrict h) ^ r = 0

def image_restriction_invertible : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (n : ℕ),
    Module.finrank K V = n →
      ∀ h : ∀ x ∈ LinearMap.range (T ^ n), T x ∈ LinearMap.range (T ^ n),
        ∃ e : LinearMap.range (T ^ n) ≃ₗ[K] LinearMap.range (T ^ n),
          e.toLinearMap = T.restrict h

/-- The full Fitting theorem, with invariance proved rather than assumed. -/
def fitting : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (n : ℕ),
    Module.finrank K V = n →
      Specs.D05.M06.DirectSum.UniqueDecomposition
        (fun b : Bool => if b then LinearMap.range (T ^ n) else LinearMap.ker (T ^ n)) ∧
      ∃ (hK : ∀ x ∈ LinearMap.ker (T ^ n), T x ∈ LinearMap.ker (T ^ n))
        (hI : ∀ x ∈ LinearMap.range (T ^ n), T x ∈ LinearMap.range (T ^ n)),
        IsNilpotent (T.restrict hK) ∧
          ∃ e : LinearMap.range (T ^ n) ≃ₗ[K] LinearMap.range (T ^ n),
            e.toLinearMap = T.restrict hI

end Specs.D05.M10.Fitting
