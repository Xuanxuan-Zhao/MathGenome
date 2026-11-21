import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.SemilinearDescent
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Degree
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-! The fixed-degree part of RM03-C04.13. -/

open scoped TensorProduct MatrixGroups

universe u v w

namespace RM03.Brauer.ProjectiveClassification

open SemilinearDescent
open Matrix

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] (n : ℕ)

abbrev Mat (K : Type v) (n : ℕ) := Matrix (Fin n) (Fin n) K

/-- The coefficientwise Galois action on the projective matrix group. -/
def projectiveAction (g : Gal(K/k)) : PGL(n, K) →* PGL(n, K) :=
  ProjGenLinGroup.map g.toRingHom

/-- Projective cocycles with the multiplication convention of RM03-C04.13. -/
structure Cocycle where
  val : Gal(K/k) → PGL(n, K)
  law : ∀ g h, val (g * h) = val g * projectiveAction k K n g (val h)

/-- Change of trivialization by a projective matrix. -/
def Cohomologous (c d : Cocycle k K n) : Prop :=
  ∃ h : PGL(n, K), ∀ g,
    d.val g = h⁻¹ * c.val g * projectiveAction k K n g h

/-- Pointed first nonabelian cohomology, with base point represented by `1`. -/
def H1 := Quot (Cohomologous k K n)

def trivial : Cocycle k K n :=
  ⟨fun _ => 1, fun _ _ => by rw [map_one, mul_one]⟩

/-- A representative of a degree-`n` central simple form of the matrix algebra. -/
def Form : Type (max u (v+1)) :=
  { A : _root_.CSA.{u,v} k //
    Nonempty (Specs.RM03.CSA.baseChange k K A ≃ₐ[K] Mat K n) }

/-- The equivalence relation uses isomorphism of algebras over the base field. -/
def Isomorphic (A B : Form k K n) : Prop :=
  Nonempty ((A.val : Type v) ≃ₐ[k] (B.val : Type v))

def SplitClasses := Quot (Isomorphic k K n)

variable {k K n}

/-- Every invertible lift of the projective cocycle gives the same operator. -/
def Implements (ρ : AlgebraAction k K (Mat K n)) (c : Cocycle k K n) : Prop :=
  ∀ (g : Gal(K/k)) (G : GL (Fin n) K), ProjGenLinGroup.mk G = c.val g →
    ∀ x : Mat K n, ρ.act g x = (G : Mat K n) * x.map g * (↑G⁻¹ : Mat K n)

/-- Coefficient action transported through a chosen splitting. -/
def IsTransport (ρ : AlgebraAction k K (Mat K n)) {A : Type w}
    [Ring A] [Algebra k A] (s : Specs.RM03.CSA.baseChange k K A ≃ₐ[K] Mat K n) : Prop :=
  ∀ (g : Gal(K/k)) (a : K) (x : A), ρ.act g (s (a ⊗ₜ[k] x)) = s (g a ⊗ₜ[k] x)

end RM03.Brauer.ProjectiveClassification

namespace Specs.RM03.Brauer.ProjectiveClassification

open _root_.RM03.Brauer.ProjectiveClassification
open _root_.RM03.Brauer.SemilinearDescent
open Matrix

def ProjectiveActionOne : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (p : PGL(n, K)), projectiveAction k K n 1 p = p

def ProjectiveActionMul : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (g h : Gal(K/k)) (p : PGL(n, K)),
    projectiveAction k K n (g * h) p =
      projectiveAction k K n g (projectiveAction k K n h p)

def ActionCorrespondence : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}, 0 < n →
    ∃ e : Cocycle k K n ≃ AlgebraAction k K (Mat K n),
      ∀ c ρ, Implements ρ c ↔ e c = ρ

def TransportedCocycle : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}
    {A : Type w} [Ring A] [Algebra k A], 0 < n →
    ∀ (s : Specs.RM03.CSA.baseChange k K A ≃ₐ[K] Mat K n),
      ∃ ρ : AlgebraAction k K (Mat K n), IsTransport ρ s ∧
        ∃ c : Cocycle k K n, Implements ρ c

def ChangeSplitting : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}
    {A : Type w} [Ring A] [Algebra k A]
    (s t : Specs.RM03.CSA.baseChange k K A ≃ₐ[K] Mat K n)
    (H : GL (Fin n) K),
    (∀ y, t y = (↑H⁻¹ : Mat K n) * s y * (H : Mat K n)) →
    ∀ (ρ τ : AlgebraAction k K (Mat K n)) (c d : Cocycle k K n),
      IsTransport ρ s → IsTransport τ t → Implements ρ c → Implements τ d →
      ∀ g, d.val g = (ProjGenLinGroup.mk H)⁻¹ * c.val g *
        projectiveAction k K n g (ProjGenLinGroup.mk H)

def RecoverForm : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {n : ℕ} [FiniteDimensional k K] [IsGalois k K] {A : Type w} [Ring A] [Algebra k A]
    (s : Specs.RM03.CSA.baseChange k K A ≃ₐ[K] Mat K n)
    (ρ : AlgebraAction k K (Mat K n)),
    IsTransport ρ s →
      ∃ e : A ≃ₐ[k] ρ.fixedSubalgebra, ∀ x : A, (e x : Mat K n) = s (1 ⊗ₜ[k] x)

def H1EqIff : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (c d : Cocycle k K n),
    (Quot.mk _ c : H1 k K n) = Quot.mk _ d ↔ Cohomologous k K n c d

def SplitClassesEqIff : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (A B : Form k K n),
    (Quot.mk _ A : SplitClasses k K n) = Quot.mk _ B ↔ Isomorphic k K n A B

def FormIffDegreeSplits : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {n : ℕ} {A : Type w} [Ring A] [Algebra k A], 0 < n →
    Specs.RM03.CSA.isCentralSimple k A →
      (Nonempty (Specs.RM03.CSA.baseChange k K A ≃ₐ[K] Mat K n) ↔
        Specs.RM03.CSA.degree k A = n ∧ Specs.RM03.CSA.splits k K A)

def DescendedForm : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {n : ℕ} [FiniteDimensional k K] [IsGalois k K], 0 < n →
    ∀ (c : Cocycle k K n) (ρ : AlgebraAction k K (Mat K n)), Implements ρ c →
      Specs.RM03.CSA.isCentralSimple k ρ.fixedSubalgebra ∧
      Specs.RM03.CSA.degree k ρ.fixedSubalgebra = n ∧
      ∃ s : Specs.RM03.CSA.baseChange k K ρ.fixedSubalgebra ≃ₐ[K] Mat K n,
        IsTransport ρ s ∧
        ∀ (a : K) (x : ρ.fixedSubalgebra), s (a ⊗ₜ[k] x) = a • (x : Mat K n)

def Classification : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {n : ℕ} [FiniteDimensional k K] [IsGalois k K], 0 < n →
    ∃ e : SplitClasses k K n ≃ H1 k K n,
      (∀ (A : Form k K n)
          (s : Specs.RM03.CSA.baseChange k K A.val ≃ₐ[K] Mat K n)
          (ρ : AlgebraAction k K (Mat K n)) (c : Cocycle k K n),
        IsTransport ρ s → Implements ρ c →
        e (Quot.mk (Isomorphic k K n) A) = Quot.mk (Cohomologous k K n) c) ∧
      (∀ {B : Type w} [Ring B] [Algebra k B]
          (s : Specs.RM03.CSA.baseChange k K B ≃ₐ[K] Mat K n)
          (ρ : AlgebraAction k K (Mat K n)) (c : Cocycle k K n),
        IsTransport ρ s → Implements ρ c →
        ∃ A : Form k K n, Nonempty (B ≃ₐ[k] (A.val : Type v)) ∧
          e (Quot.mk (Isomorphic k K n) A) = Quot.mk (Cohomologous k K n) c) ∧
      (∀ (c : Cocycle k K n) (ρ : AlgebraAction k K (Mat K n)), Implements ρ c →
        ∃ A : Form k K n, Nonempty ((A.val : Type v) ≃ₐ[k] ρ.fixedSubalgebra) ∧
          e.symm (Quot.mk (Cohomologous k K n) c) = Quot.mk (Isomorphic k K n) A) ∧
      (∃ A : Form k K n, Nonempty ((A.val : Type v) ≃ₐ[k] Mat k n)) ∧
      (∀ A : Form k K n, Nonempty ((A.val : Type v) ≃ₐ[k] Mat k n) →
        e (Quot.mk (Isomorphic k K n) A) = Quot.mk (Cohomologous k K n) (trivial k K n))

end Specs.RM03.Brauer.ProjectiveClassification
