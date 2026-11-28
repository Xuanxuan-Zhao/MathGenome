import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.Presentation
import Mathlib.RingTheory.Bialgebra.Basic

noncomputable section

namespace Specs.LieNotes.Quantum.Coproduct

open Presentation
open scoped TensorProduct

universe u v

section BialgebraData

variable {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]

/-- The Cartan unit inside the presented quantum enveloping algebra. -/
def K (C : Cartan A T) (i : Root) : (U C)ˣ :=
  Units.map (cartan C).toMonoidHom (C.K i)

/-- The coproduct and counit on the Serre quotient, together with their
bialgebra axioms and their values on the simple roots and Cartan units. -/
structure Data (C : Cartan A T) where
  comul : U C →ₐ[A] (U C ⊗[A] U C)
  counit : U C →ₐ[A] A
  comul_E (i : Root) :
    comul (E C i) = E C i ⊗ₜ[A] 1 + (K C i : U C) ⊗ₜ[A] E C i
  comul_F (i : Root) :
    comul (F C i) = F C i ⊗ₜ[A] (↑((K C i)⁻¹) : U C) + 1 ⊗ₜ[A] F C i
  counit_E (i : Root) : counit (E C i) = 0
  counit_F (i : Root) : counit (F C i) = 0
  comul_K (i : Root) :
    comul (K C i : U C) = (K C i : U C) ⊗ₜ[A] (K C i : U C)
  counit_K (i : Root) : counit (K C i : U C) = 1
  coassoc : (Algebra.TensorProduct.assoc A A A (U C) (U C) (U C)).toAlgHom.comp
      ((Algebra.TensorProduct.map comul (AlgHom.id A (U C))).comp comul) =
    (Algebra.TensorProduct.map (AlgHom.id A (U C)) comul).comp comul
  left_counit : (Algebra.TensorProduct.map counit (AlgHom.id A (U C))).comp comul =
    (Algebra.TensorProduct.lid A (U C)).symm
  right_counit : (Algebra.TensorProduct.map (AlgHom.id A (U C)) counit).comp comul =
    (Algebra.TensorProduct.rid A A (U C)).symm

/-- The Mathlib bialgebra structure with the given algebra maps. -/
abbrev Data.toBialgebra {C : Cartan A T} (d : Data C) : Bialgebra A (U C) :=
  Bialgebra.ofAlgHom d.comul d.counit d.coassoc d.left_counit d.right_counit

end BialgebraData

section Truncation

variable {k : Type u} [Field k] [CharZero k]

/-- The image of the polynomial Cartan generator in the truncated presentation. -/
def H (k : Type u) [Field k] [CharZero k] (N : ℕ) (i : Root) : Uₙ k N :=
  cartan (truncated k N) (MvPolynomial.X i)

/-- In the formal case the Cartan generators are primitive, in addition to
the exponential Cartan units being group-like. -/
structure TruncatedData (k : Type u) [Field k] [CharZero k] (N : ℕ)
    extends Data (truncated k N) where
  comul_H (i : Root) :
    comul (H k N i) = H k N i ⊗ₜ[Truncations.A k N] 1 + 1 ⊗ₜ[Truncations.A k N] H k N i
  counit_H (i : Root) : counit (H k N i) = 0

open Algebra.TensorProduct (lift includeLeft includeRight tmul_mul_tmul)

private abbrev TensorSquare (k : Type u) [Field k] [CharZero k] (N : ℕ) :=
  Uₙ k N ⊗[Truncations.A k N] Uₙ k N

private abbrev reductionAlgebra {M N : ℕ} (h : M ≤ N) :
    Algebra (Truncations.A k N) (TensorSquare k M) :=
  Algebra.compHom _ (Truncations.reduce h).toRingHom

private def reduceFactor {M N : ℕ} (h : M ≤ N)
    (f : Uₙ k M →ₐ[Truncations.A k M] TensorSquare k M) :
    letI := reductionAlgebra (k := k) h
    Uₙ k N →ₐ[Truncations.A k N] TensorSquare k M :=
  letI := reductionAlgebra (k := k) h
  { toRingHom := f.toRingHom.comp (reduce h)
    commutes' := fun a => (congrArg f (reduce_scalar h a)).trans (f.commutes _) }

private theorem reduceFactor_apply {M N : ℕ} (h : M ≤ N)
    (f : Uₙ k M →ₐ[Truncations.A k M] TensorSquare k M) (x : Uₙ k N) :
    letI := reductionAlgebra (k := k) h
    reduceFactor h f x = f (reduce h x) := rfl

private def tensorReduceAlgHom {M N : ℕ} (h : M ≤ N) :
    letI := reductionAlgebra (k := k) h
    TensorSquare k N →ₐ[Truncations.A k N] TensorSquare k M :=
  letI := reductionAlgebra (k := k) h
  lift (reduceFactor h includeLeft) (reduceFactor h includeRight)
    (fun x y => (Commute.one_right (reduce h x)).tmul (Commute.one_left (reduce h y)))

/-- Reduce both tensor factors over the accompanying change in coefficient ring. -/
def tensorReduce {M N : ℕ} (h : M ≤ N) :
    (Uₙ k N ⊗[Truncations.A k N] Uₙ k N) →+*
      (Uₙ k M ⊗[Truncations.A k M] Uₙ k M) :=
  letI := reductionAlgebra (k := k) h
  (tensorReduceAlgHom h).toRingHom

@[simp] theorem tensorReduce_tmul {M N : ℕ} (h : M ≤ N) (x y : Uₙ k N) :
    tensorReduce h (x ⊗ₜ[Truncations.A k N] y) =
      reduce h x ⊗ₜ[Truncations.A k M] reduce h y := by
  let f := reduceFactor (k := k) h includeLeft
  let g := reduceFactor (k := k) h includeRight
  have hc (a b : Uₙ k N) : Commute (f a) (g b) :=
    (Commute.one_right (reduce h a)).tmul (Commute.one_left (reduce h b))
  calc
    tensorReduce h (x ⊗ₜ[Truncations.A k N] y) = f x * g y :=
      letI := reductionAlgebra (k := k) h
      Algebra.TensorProduct.lift_tmul f g hc x y
    _ = (reduce h x ⊗ₜ[Truncations.A k M] 1) * (1 ⊗ₜ[Truncations.A k M] reduce h y) :=
      congrArg₂ (· * ·) (reduceFactor_apply (k := k) h includeLeft x)
        (reduceFactor_apply (k := k) h includeRight y)
    _ = (reduce h x * 1) ⊗ₜ[Truncations.A k M] (1 * reduce h y) :=
      tmul_mul_tmul (R := Truncations.A k M) (reduce h x) 1 1 (reduce h y)
    _ = _ := congrArg₂ (TensorProduct.tmul (Truncations.A k M))
      (mul_one (reduce h x)) (one_mul (reduce h y))

/-- The coproduct and counit commute with reduction to every lower positive level. -/
def ReductionProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {M N : ℕ} (_ : 1 ≤ M) (h : M ≤ N)
    (dN : TruncatedData k N) (dM : TruncatedData k M),
    (tensorReduce h).comp dN.comul.toRingHom = dM.comul.toRingHom.comp (reduce h) ∧
      (Truncations.reduce h).toRingHom.comp dN.counit.toRingHom =
        dM.counit.toRingHom.comp (reduce h)

end Truncation

def GenericProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (q : kˣ) (hq : (q : k)^2 ≠ 1),
    Nonempty (Data (generic q hq))

def IndeterminateProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k], Nonempty (Data (indeterminate k))

def TruncatedProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (N : ℕ), 1 ≤ N → Nonempty (TruncatedData k N)

end Specs.LieNotes.Quantum.Coproduct
