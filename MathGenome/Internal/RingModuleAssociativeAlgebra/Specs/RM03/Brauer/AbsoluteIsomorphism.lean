import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.ContinuousCohomology

/-! Finite-stage compatibility and the absolute Brauer isomorphism in RM03-C04.13. -/

namespace Specs.RM03.Brauer.AbsoluteIsomorphism

open _root_.RM03.Brauer.ContinuousCohomology
open _root_.RM03.Brauer.ProjectiveClassification
open _root_.RM03.Brauer.ScalarObstruction
open Specs.RM03.Brauer.ScalarObstruction
open Specs.RM03.Brauer.ContinuousCohomology (H2ContinuousValue)
open scoped TensorProduct MatrixGroups

universe u v w

/-- The relative kernel, characterized by splitting on representatives. -/
def IsStageKernel {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S]
    (E : Stage k S) [AddCommGroup (BrauerGroup.{u, max u v w} k)]
    (B : AddSubgroup (BrauerGroup.{u, max u v w} k)) : Prop :=
  ∀ A : _root_.CSA.{u, max u v w} k, classOf A ∈ B ↔ CSA.splits k E A

/-- The formula for the relative class map on each presented splitting. -/
def IsStageObstruction {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S]
    (E : Stage k S) [AddCommGroup (BrauerGroup.{u, max u v w} k)]
    {B : AddSubgroup (BrauerGroup.{u, max u v w} k)}
    (φ : B →+ StageCohomology E) : Prop :=
  ∀ (A : _root_.CSA.{u, max u v w} k) (hA : classOf A ∈ B)
    {n : ℕ}, 0 < n →
    ∀ (s : (E ⊗[k] A) ≃ₐ[E] Mat E n) (G : Gal(E/k) → GL (Fin n) E),
      Presents s G → ∀ c : ScalarCocycle k E, RecordsDefect G c →
      φ ⟨classOf A, hA⟩ = Additive.ofMul (cocycleClass k E c)

/-- On a tower, the relative class maps intertwine subgroup inclusion and inflation. -/
def RelativeInflation : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S]
    {E F : Stage k S} (h : E ≤ F) [AddCommGroup (BrauerGroup.{u, max u v w} k)]
    {B C : AddSubgroup (BrauerGroup.{u, max u v w} k)},
    IsStageKernel E B → IsStageKernel F C →
    ∀ (φ : B →+ StageCohomology E) (ψ : C →+ StageCohomology F),
      IsStageObstruction E φ → IsStageObstruction F ψ →
      ∃ le : B ≤ C, ψ.comp (AddSubgroup.inclusion le) = (stageTransition E F h).comp φ

/-- Every Brauer class has a representative split by a finite Galois subfield
of the given separable closure. -/
def FiniteStageCover : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (a : BrauerGroup.{u, max u v w} k),
    ∃ (E : Stage k S) (A : _root_.CSA.{u, max u v w} k), classOf A = a ∧ CSA.splits k E A

/-- The absolute isomorphism uses the given Brauer group law and sends every
finite-stage scalar defect to its class in continuous cohomology. -/
def AbsoluteBrauerIsomorphism : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S],
    ∃ g : AddCommGroup (BrauerGroup.{u, max u v w} k),
      GroupLaws.{u, max v w} k g ∧
      letI := g
      ∃ e : BrauerGroup.{u, max u v w} k ≃+ Additive (H2ContinuousValue k S),
        ∀ (E : Stage k S) (A : _root_.CSA.{u, max u v w} k) {n : ℕ}, 0 < n →
          ∀ (s : (E ⊗[k] A) ≃ₐ[E] Mat E n) (G : Gal(E/k) → GL (Fin n) E),
            Presents s G → ∀ c : ScalarCocycle k E, RecordsDefect G c →
            e (classOf A) = Additive.ofMul (toContinuous E (cocycleClass k E c))

end Specs.RM03.Brauer.AbsoluteIsomorphism
