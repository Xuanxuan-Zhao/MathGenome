import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.ScalarObstruction

/-! Surjectivity and the relative Brauer isomorphism in RM03-C04.13. -/

open scoped TensorProduct MatrixGroups

namespace Specs.RM03.Brauer.RelativeIsomorphism

open _root_.RM03.Brauer.ProjectiveClassification
open _root_.RM03.Brauer.ScalarObstruction
open _root_.RM03.Brauer.SemilinearDescent
open Specs.RM03.Brauer.ScalarObstruction
open Matrix

universe u v w

/-- Every cohomology class has a representative whose values on pairs with
an identity argument are both `1`. -/
def NormalizedRepresentative : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (a : H2 k K), ∃ c : ScalarCocycle k K,
      cocycleClass k K c = a ∧ ∀ g, c.val (1, g) = 1 ∧ c.val (g, 1) = 1

/-- In the basis indexed by the Galois group, the operator at `g` sends
the basis vector at `h` to `c(g,h)` times the basis vector at `gh`.
Its conjugation action descends the matrix algebra, with scalar defect `c`. -/
def RegularDescent : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (c : ScalarCocycle k K),
    ∃ (n : ℕ) (index : Fin n ≃ Gal(K/k)), 0 < n ∧
      ∃ (G : Gal(K/k) → GL (Fin n) K) (p : Cocycle k K n)
        (ρ : AlgebraAction k K (Mat K n)),
        (∀ g i j, G g i j =
          if i = index.symm (g * index j) then (c.val (g, index j) : K) else 0) ∧
        IsLift p G ∧ RecordsDefect G c ∧ Implements ρ p ∧
        CSA.isCentralSimple k ρ.fixedSubalgebra ∧
        CSA.degree k ρ.fixedSubalgebra = n ∧
        ∃ s : (K ⊗[k] ρ.fixedSubalgebra) ≃ₐ[K] Mat K n,
          IsTransport ρ s ∧ ∀ (a : K) (x : ρ.fixedSubalgebra),
            s (a ⊗ₜ[k] x) = a • (x : Mat K n)

/-- The scalar obstruction is surjective and is the underlying homomorphism
of an isomorphism of the relative Brauer group with second cohomology. -/
def ScalarObstructionIsomorphism : Prop :=
  ∀ (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (gk : AddCommGroup (BrauerGroup.{u, max u v w} k))
    (gK : AddCommGroup (BrauerGroup.{v, max u v w} K)),
    GroupLaws.{u, max v w} k gk → GroupLaws.{v, max u w} K gK →
    letI := gk
    letI := gK
    ∀ (f : BrauerGroup.{u, max u v w} k →+ BrauerGroup.{v, max u v w} K),
      IsScalarExtension k K f →
      ∀ (φ : relativeSubgroup f →+ Additive (H2 k K)),
        IsObstructionHom.{u,v,w} f φ →
        Function.Surjective φ ∧
          ∃ e : relativeSubgroup f ≃+ Additive (H2 k K), e.toAddMonoidHom = φ

end Specs.RM03.Brauer.RelativeIsomorphism
