import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.Reflection
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Archimedean.Basic

namespace LinearAlgebraicGroups.Arithmetic.AffineArrangement

abbrev Wall (ι : Type*) := ι × ℤ

structure Datum (K V ι : Type*) [Field K] [AddCommGroup V] [Module K V] where
  root : ι → V →ₗ[K] K
  coroot : ι → V
  diagonal (i : ι) : root i (coroot i) = 2
  integral (i j : ι) : ∃ k : ℤ, root i (coroot j) = (k : K)

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (D : Datum K V ι)

def Datum.linearReflection (i : ι) : V ≃ₗ[K] V :=
  Module.reflection (D.diagonal i)

def Datum.ReflectionClosed : Prop :=
  ∀ i j, ∃ k, D.root k = (D.root j).comp (D.linearReflection i).toLinearMap ∧
    D.coroot k = D.linearReflection i (D.coroot j)

def Datum.ReducedDirections : Prop :=
  Function.Injective D.root ∧
  ∀ i j (a : K), D.root j = a • D.root i → i = j ∨ D.root j = -D.root i

def Datum.value (a : Wall ι) (x : V) : K :=
  D.root a.1 x + (a.2 : K)

def Datum.reflection (a : Wall ι) : V ≃ᵃ[K] V :=
  AffineEquiv.constVAdd K V ((-a.2) • D.coroot a.1) *
    (D.linearReflection a.1).toAffineEquiv

noncomputable def Datum.opposite (a : Wall ι) : Wall ι := by
  classical
  exact (if h : ∃ i, D.root i = -D.root a.1 then h.choose else a.1, -a.2)

def Datum.regular (x : V) : Prop := ∀ a, D.value a x ≠ 0

def Datum.ordinary : Subgroup (V ≃ᵃ[K] V) :=
  Subgroup.closure (Set.range D.reflection)

def Datum.extended : Subgroup (V ≃ᵃ[K] V) :=
  Subgroup.closure
    (Set.range (fun i => (D.linearReflection i).toAffineEquiv) ∪
      AffineEquiv.constVAdd K V '' {v | ∀ i, ∃ n : ℤ, D.root i v = (n : K)})

/-- Transport of the signed equation and its matched coroot. -/
def Datum.Transports (g : V ≃ᵃ[K] V) (a b : Wall ι) : Prop :=
  (∀ x, D.value b (g x) = D.value a x) ∧ g.linear (D.coroot a.1) = D.coroot b.1

def Datum.symmetries : Subgroup (V ≃ᵃ[K] V) where
  carrier := {g | ∃ σ : Equiv.Perm (Wall ι), ∀ a, D.Transports g a (σ a)}
  one_mem' := ⟨1, fun _ => ⟨fun _ => rfl, rfl⟩⟩
  mul_mem' := by
    rintro g h ⟨σ, hσ⟩ ⟨τ, hτ⟩
    refine ⟨τ.trans σ, fun a => ⟨fun x => ?_, ?_⟩⟩
    · change D.value (σ (τ a)) (g (h x)) = _
      rw [(hσ (τ a)).1, (hτ a).1]
    · change g.linear (h.linear (D.coroot a.1)) = D.coroot (σ (τ a)).1
      rw [(hτ a).2, (hσ (τ a)).2]
  inv_mem' := by
    rintro g ⟨σ, hσ⟩
    refine ⟨σ.symm, fun a => ⟨fun x => ?_, ?_⟩⟩
    · have h := (hσ (σ.symm a)).1 (g.symm x)
      change D.value (σ.symm a) (g.symm x) = D.value a x
      simpa using h.symm
    · apply g.linear.injective
      change g.linear (g.linear.symm (D.coroot a.1)) = _
      rw [LinearEquiv.apply_symm_apply, (hσ (σ.symm a)).2, σ.apply_symm_apply]

section Ordered

variable [LinearOrder K] [IsStrictOrderedRing K]

def Datum.positive (p : V) (a : Wall ι) : Prop := 0 < D.value a p

/-- The alcove containing a regular point has the same strict signs as that point. -/
def Datum.alcove (p : V) : Set V :=
  {x | ∀ a, D.positive p a → D.positive x a}

/-- The set of alcoves in the complement of the arrangement. -/
def Datum.Chamber := {C : Set V // ∃ p, D.regular p ∧ C = D.alcove p}

/-- A positive bounding wall has a point in the relative interior of its panel. -/
def Datum.IsSimple (p : V) (a : Wall ι) : Prop :=
  D.positive p a ∧ ∃ x, D.value a x = 0 ∧
    ∀ b, D.positive p b → b ≠ a → D.positive x b

def Datum.simpleGroup (p : V) : Subgroup (V ≃ᵃ[K] V) :=
  Subgroup.closure (D.reflection '' {a | D.IsSimple p a})

def Datum.separators (p q : V) : Set (Wall ι) :=
  {a | D.positive p a ∧ D.value a q < 0}

end Ordered

namespace Expected

def ReflectionFormula (D : Datum K V ι) : Prop :=
  ∀ a x, D.reflection a x = x - D.value a x • D.coroot a.1

def ReflectionInvolution (D : Datum K V ι) : Prop :=
  ∀ a, D.reflection a * D.reflection a = 1

variable [LinearOrder K] [IsStrictOrderedRing K]

def OppositeRules (D : Datum K V ι) : Prop :=
  D.ReflectionClosed → D.ReducedDirections →
  ∀ a, (∀ x, D.value (D.opposite a) x = - D.value a x) ∧
    D.coroot (D.opposite a).1 = -D.coroot a.1 ∧
    D.opposite (D.opposite a) = a ∧ D.reflection (D.opposite a) = D.reflection a

def GroupPreservation (D : Datum K V ι) : Prop :=
  D.ReflectionClosed → D.ReducedDirections →
  D.ordinary ≤ D.symmetries ∧ D.extended ≤ D.symmetries

def SignedAction (D : Datum K V ι) : Prop :=
  D.ReflectionClosed → D.ReducedDirections →
  ∃ A : MulAction D.symmetries (Wall ι),
    ∀ (g : D.symmetries) a,
      D.Transports g a (@SMul.smul _ _ A.toSMul g a) ∧
      @SMul.smul _ _ A.toSMul g (D.opposite a) =
        D.opposite (@SMul.smul _ _ A.toSMul g a) ∧
      D.reflection (@SMul.smul _ _ A.toSMul g a) = (g : V ≃ᵃ[K] V) * D.reflection a * (g : V ≃ᵃ[K] V)⁻¹

def SignsAndAlcoveAction (D : Datum K V ι) : Prop :=
  D.ReflectionClosed → D.ReducedDirections →
  ∀ p, D.regular p →
    (∀ x, x ∈ D.alcove p ↔
      ∀ a, (0 < D.value a x ↔ 0 < D.value a p) ∧ (D.value a x < 0 ↔ D.value a p < 0)) ∧
    ∀ g : V ≃ᵃ[K] V, g ∈ D.symmetries → D.regular (g p) ∧
      g '' D.alcove p = D.alcove (g p)

omit [IsStrictOrderedRing K] in
def ChamberAction (D : Datum K V ι) : Prop :=
  ∃ A : MulAction D.symmetries D.Chamber, ∀ (g : D.symmetries) C,
    (@SMul.smul _ _ A.toSMul g C).val = (g.val : V → V) '' C.val

def SimpleWallSigns (D : Datum K V ι) : Prop :=
  D.ReflectionClosed → D.ReducedDirections →
  ∀ p a, D.regular p → D.IsSimple p a →
    D.Transports (D.reflection a) a (D.opposite a) ∧
    ∀ b c, D.Transports (D.reflection a) b c → D.positive p b → b ≠ a → D.positive p c

def GenerationAndTransitivity [Finite ι] [Archimedean K] (D : Datum K V ι) : Prop :=
  D.ReflectionClosed → D.ReducedDirections →
  ∀ p, D.regular p → D.simpleGroup p = D.ordinary ∧
    ∀ q, D.regular q → ∃ g ∈ D.ordinary, g '' D.alcove p = D.alcove q

def RealComponents {n : ℕ} (D : Datum ℝ (Fin n → ℝ) ι) : Prop :=
  D.ReflectionClosed → D.ReducedDirections →
  ∀ p, D.regular p → connectedComponentIn {x | D.regular x} p = D.alcove p

def WallGeometry [Finite ι] [Archimedean K] (D : Datum K V ι) : Prop :=
  D.ReflectionClosed → D.ReducedDirections →
  ∀ a,
    (∀ b, ({x | D.value a x = 0} : Set V) = {x | D.value b x = 0} ↔
      b = a ∨ b = D.opposite a) ∧
    (∃ p, D.regular p ∧ D.IsSimple p a)

def RealBoundingWalls [Finite ι] {n : ℕ} (D : Datum ℝ (Fin n → ℝ) ι) : Prop :=
  D.ReflectionClosed → D.ReducedDirections →
  ∀ p, D.regular p → ∀ a,
    D.IsSimple p a ↔
      D.positive p a ∧ ∃ U : Set (Fin n → ℝ), IsOpen U ∧
        (U ∩ {x | D.value a x = 0}).Nonempty ∧
        U ∩ {x | D.value a x = 0} ⊆ closure (D.alcove p)

end Expected

namespace Specification

def ReflectionFormula.{u,v,w} : Prop :=
  ∀ {K : Type u} {V : Type v} {ι : Type w} [Field K] [AddCommGroup V] [Module K V]
    (D : Datum K V ι), Expected.ReflectionFormula D

def ReflectionInvolution.{u,v,w} : Prop :=
  ∀ {K : Type u} {V : Type v} {ι : Type w} [Field K] [AddCommGroup V] [Module K V]
    (D : Datum K V ι), Expected.ReflectionInvolution D

def OppositeRules.{u,v,w} : Prop :=
  ∀ {K : Type u} {V : Type v} {ι : Type w} [Field K] [AddCommGroup V] [Module K V]
    (D : Datum K V ι) [LinearOrder K] [IsStrictOrderedRing K],
    Expected.OppositeRules D

def GroupPreservation.{u,v,w} : Prop :=
  ∀ {K : Type u} {V : Type v} {ι : Type w} [Field K] [AddCommGroup V] [Module K V]
    (D : Datum K V ι) [LinearOrder K] [IsStrictOrderedRing K],
    Expected.GroupPreservation D

def SignedAction.{u,v,w} : Prop :=
  ∀ {K : Type u} {V : Type v} {ι : Type w} [Field K] [AddCommGroup V] [Module K V]
    (D : Datum K V ι) [LinearOrder K] [IsStrictOrderedRing K],
    Expected.SignedAction D

def SignsAndAlcoveAction.{u,v,w} : Prop :=
  ∀ {K : Type u} {V : Type v} {ι : Type w} [Field K] [AddCommGroup V] [Module K V]
    (D : Datum K V ι) [LinearOrder K] [IsStrictOrderedRing K],
    Expected.SignsAndAlcoveAction D

def ChamberAction.{u,v,w} : Prop :=
  ∀ {K : Type u} {V : Type v} {ι : Type w} [Field K] [AddCommGroup V] [Module K V]
    (D : Datum K V ι) [LinearOrder K],
    Expected.ChamberAction D

def SimpleWallSigns.{u,v,w} : Prop :=
  ∀ {K : Type u} {V : Type v} {ι : Type w} [Field K] [AddCommGroup V] [Module K V]
    (D : Datum K V ι) [LinearOrder K] [IsStrictOrderedRing K],
    Expected.SimpleWallSigns D

def GenerationAndTransitivity.{u,v,w} : Prop :=
  ∀ {K : Type u} {V : Type v} {ι : Type w} [Field K] [AddCommGroup V] [Module K V]
    (D : Datum K V ι) [LinearOrder K] [IsStrictOrderedRing K]
    [Finite ι] [Archimedean K],
    Expected.GenerationAndTransitivity D

def WallGeometry.{u,v,w} : Prop :=
  ∀ {K : Type u} {V : Type v} {ι : Type w} [Field K] [AddCommGroup V] [Module K V]
    (D : Datum K V ι) [LinearOrder K] [IsStrictOrderedRing K]
    [Finite ι] [Archimedean K],
    Expected.WallGeometry D

def RealComponents.{u} : Prop :=
  ∀ {ι : Type u} {n : ℕ} (D : Datum ℝ (Fin n → ℝ) ι), Expected.RealComponents D

def RealBoundingWalls.{u} : Prop :=
  ∀ {ι : Type u} [Finite ι] {n : ℕ} (D : Datum ℝ (Fin n → ℝ) ι), Expected.RealBoundingWalls D

end Specification
end LinearAlgebraicGroups.Arithmetic.AffineArrangement
