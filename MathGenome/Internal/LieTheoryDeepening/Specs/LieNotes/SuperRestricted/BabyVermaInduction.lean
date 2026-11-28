import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.RestrictedSlTwo
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.ReducedEnveloping
import Mathlib.LinearAlgebra.Quotient.Basic

/-! The upper triangular Borel and induction from its one-dimensional reduced module. -/

namespace Specs.LieNotes.SuperRestricted.BabyVermaInduction

open _root_.Specs.LieAlgebrasAndRepresentations.Sl2Model (Model E F H)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)
open _root_.Specs.LieNotes.SuperRestricted.ReducedEnveloping (reducedEnvelopingValue quotientMapValue)
open _root_.Shared.Lie (inclusion)
open scoped BigOperators

universe u v w

variable (k : Type u) [Field k]

/-- The trace-zero matrices whose lower left entry vanishes. -/
def borelValue : LieSubalgebra k (Model k) where
  carrier := {x | x.val 1 0 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro x y hx hy
    change x.val 1 0 + y.val 1 0 = 0
    change x.val 1 0 = 0 at hx
    change y.val 1 0 = 0 at hy
    simp [hx, hy]
  smul_mem' := by
    intro a x hx
    change a * x.val 1 0 = 0
    change x.val 1 0 = 0 at hx
    simp [hx]
  lie_mem' := by
    intro x y hx hy
    change x.val 1 0 = 0 at hx
    change y.val 1 0 = 0 at hy
    change (x.val * y.val) 1 0 - (y.val * x.val) 1 0 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, hx, hy]

abbrev Borel := ↥(borelValue k)

def borelType := ∀ (k : Type u) [Field k], LieSubalgebra k (Model k)

def borelH : Borel k := ⟨H k, by
  change (H k).val 1 0 = 0
  rw [H, LieAlgebra.SpecialLinear.val_singleSubSingle]
  simp [Matrix.single]⟩

def borelE : Borel k := ⟨E k, by
  change (E k).val 1 0 = 0
  rw [E, LieAlgebra.SpecialLinear.val_single]
  simp [Matrix.single]⟩

/-- The ordered Borel basis consists of the diagonal element followed by the upper root element. -/
def borelBasisType : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ b : Module.Basis (Fin 2) k (Borel k), b 0 = borelH k ∧ b 1 = borelE k

variable {k}
variable {G : Type v} [LieRing G] [LieAlgebra k G] {p : ℕ} [CharP k p] [NeZero p]

/-- The class of an ordinary Lie generator in the reduced enveloping algebra. -/
def generator (P : restrictedPowerValue k p G) (χ : G →ₗ[k] k) (x : G) :
    reducedEnvelopingValue P χ :=
  quotientMapValue P χ (inclusion k G x)

abbrev Ambient (P : restrictedPowerValue k p (Model k)) (χ : Model k →ₗ[k] k) :=
  reducedEnvelopingValue P χ

def restrictCharacter (χ : Model k →ₗ[k] k) : Borel k →ₗ[k] k :=
  χ.comp (borelValue k).incl.toLinearMap

abbrev BorelAlgebra (Q : restrictedPowerValue k p (Borel k)) (χ : Model k →ₗ[k] k) :=
  reducedEnvelopingValue Q (restrictCharacter χ)

section Tensor

variable {A : Type v} {B : Type w} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (j : B →ₐ[k] A) (θ : B →ₐ[k] k)

/-- Relations for the balanced tensor of the right B-module A with the line
on which b acts by θ b. Under A ⊗[k] k ≃ A, a pure tensor a ⊗ t
corresponds to t • a, and the balancing relations are the left A-span
of j b - θ b • 1. -/
def balance : Submodule A A :=
  Submodule.span A (Set.range fun b => j b - algebraMap k A (θ b))

/-- The induced module, expressed as the quotient by the tensor balancing relations. -/
abbrev inducedValue := A ⧸ balance j θ

set_option linter.checkUnivs false in
def inducedType :=
  ∀ {k : Type u} [Field k] {A : Type v} {B : Type w}
    [Ring A] [Ring B] [Algebra k A] [Algebra k B],
    (B →ₐ[k] A) → (B →ₐ[k] k) → Type v

/-- The scalar line as a module over B via its character. -/
abbrev lineModule : Module B k := Module.compHom k θ.toRingHom

/-- The pure tensor a ⊗ t in the induced module. -/
def tensor (a : A) (t : k) : inducedValue j θ := (balance j θ).mkQ (t • a)

/-- The highest vector 1 ⊗ 1. -/
def highest : inducedValue j θ :=
  (balance j θ).mkQ 1

/-- The right B-basis of A, with right action given by multiplication by j b. -/
def RightBasis {ι : Type*} [Fintype ι] (x : ι → A) :=
  ∃ d : (ι → B) ≃ₗ[k] A,
    (∀ c, d c = ∑ i, x i * j (c i)) ∧
    ∀ c b, d (fun i => c i * b) = d c * j b

end Tensor

section Result

variable (P : restrictedPowerValue k p (Model k)) (Q : restrictedPowerValue k p (Borel k))
variable (χ : Model k →ₗ[k] k)

def MatrixPower : Prop := ∀ x : Model k, (P.val x).val = x.val ^ p

def InheritedPower : Prop := ∀ x : Borel k, (Q.val x : Model k) = P.val (x : Model k)

def CanonicalInclusion (j : BorelAlgebra Q χ →ₐ[k] Ambient P χ) : Prop :=
  ∀ x : Borel k, j (generator Q (restrictCharacter χ) x) = generator P χ (x : Model k)

def LineCharacter (weight : k) (θ : BorelAlgebra Q χ →ₐ[k] k) : Prop :=
  θ (generator Q (restrictCharacter χ) (borelH k)) = weight ∧
  θ (generator Q (restrictCharacter χ) (borelE k)) = 0

variable {P Q χ}
variable (j : BorelAlgebra Q χ →ₐ[k] Ambient P χ) (θ : BorelAlgebra Q χ →ₐ[k] k)
variable (weight : k)

abbrev BabyVerma := inducedValue j θ

def babyVermaType :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {P : restrictedPowerValue k p (Model k)} {Q : restrictedPowerValue k p (Borel k)}
    {χ : Model k →ₗ[k] k},
    (BorelAlgebra Q χ →ₐ[k] Ambient P χ) → (BorelAlgebra Q χ →ₐ[k] k) → Type u

/-- Basis and the actions of the three generators on the actual induced module. -/
def BasisAndActions : Prop :=
  ∃ v : Module.Basis (Fin p) k (BabyVerma j θ),
    (∀ i, v i = generator P χ (F k) ^ i.val • highest j θ) ∧
    (∀ i, generator P χ (H k) • v i = (weight - 2 * (i.val : k)) • v i) ∧
    (generator P χ (E k) • highest j θ = 0) ∧
    (∀ i j' : Fin p, i.val = j'.val + 1 →
      generator P χ (E k) • v i = ((i.val : k) * (weight - (i.val : k) + 1)) • v j') ∧
    (∀ i j' : Fin p, j'.val = i.val + 1 → generator P χ (F k) • v i = v j') ∧
    (∀ i : Fin p, i.val + 1 = p →
      generator P χ (F k) • v i = (χ (F k)) ^ p • highest j θ)

/-- Induction from a highest vector, including surjectivity for a cyclic vector. -/
def InductionProperty : Prop :=
  ∀ (V : Type w) [AddCommGroup V] [Module (Ambient P χ) V] (v : V),
    letI : Module k V := Module.compHom V (algebraMap k (Ambient P χ))
    generator P χ (H k) • v = weight • v →
    generator P χ (E k) • v = 0 →
    (∃! f : BabyVerma j θ →ₗ[Ambient P χ] V, f (highest j θ) = v) ∧
    (Submodule.span (Ambient P χ) {v} = ⊤ →
      ∃ f : BabyVerma j θ →ₗ[Ambient P χ] V, f (highest j θ) = v ∧ Function.Surjective f)

end Result

def babyVermaInductionType : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {p : ℕ} [CharP k p] (hp : 2 < p),
    letI : NeZero p := ⟨by omega⟩
    ∀ (P : restrictedPowerValue k p (Model k)), MatrixPower P →
    ∀ (χ : Model k →ₗ[k] k), χ (E k) = 0 →
      ∃ (Q : restrictedPowerValue k p (Borel k))
        (j : BorelAlgebra Q χ →ₐ[k] Ambient P χ),
        InheritedPower P Q ∧ CanonicalInclusion P Q χ j ∧ Function.Injective j ∧
        RightBasis j (fun i : Fin p => generator P χ (F k) ^ i.val) ∧
        ∀ weight : k, weight ^ p - weight = χ (H k) ^ p →
          ∃ θ : BorelAlgebra Q χ →ₐ[k] k,
            LineCharacter Q χ weight θ ∧ BasisAndActions j θ weight ∧ InductionProperty.{u, w} j θ weight

end Specs.LieNotes.SuperRestricted.BabyVermaInduction
