import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Heisenberg.ExtensionLocus
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.InfinitesimalDeformations
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Sl2Model
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.RingTheory.LaurentSeries

/-! LD03 on the designated Heisenberg model and its ordered basis. -/

noncomputable section

open scoped LaurentSeries PowerSeries TensorProduct

namespace Specs.LieNotes.Heisenberg.Examples

open _root_.LieAlgebrasAndRepresentations.AbelianExtensions
open _root_.LieAlgebrasAndRepresentations.DeformationObstructions
open _root_.LieAlgebrasAndRepresentations.InfinitesimalDeformations (Deformation model cocycle)
open LieModule.Cohomology (twoCocycle)
open _root_.Specs.LieAlgebrasAndRepresentations.Sl2Model (E F H)

universe u

variable (k : Type u) [Field k]

def firstParameters : Fin 5 → k := ![1, 0, 0, 0, 0]
def secondParameters : Fin 5 → k := ![0, 0, 0, 0, 1]

/-- The cohomology class of the linear coefficient in the canonical exterior complex. -/
def classOf [CharZero k] (D : Deformation k (ModelValue k)) :
    AdjointCohomology.H2 k (ModelValue k) :=
  Submodule.Quotient.mk (cocycleExteriorMap (AdjointCohomology.d k (ModelValue k))
    (Classical.choose_spec (canonicalCEExists_spec (k := k) (g := ModelValue k)
      (M := ModelValue k))).2 (cocycle D))

open private basis_bracket_table from MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Heisenberg.Basic

theorem heisenbergBasis : AdjointCohomology.HeisenbergBasis (basisValue k) :=
  basis_bracket_table k

abbrev FormalCarrier := k⟦X⟧ ⊗[k] ModelValue k

/-- The operation μ + Xφ₁ on the free formal module. -/
def formalBracket := ExtensionLocus.linearBracket (PowerSeries.X : k⟦X⟧) (firstParameters k)

/-- The two classes have formal extensions. Their sum is represented by the
sum cochain and every representative fails to extend modulo X³. -/
def ClassExamplesType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    let x := xValue k
    let y := yValue k
    let z := zValue k
    let φ₁ := NormalizedObstruction.normalized (1 : k) 0 0 0 0
    let φ₂ := NormalizedObstruction.normalized (0 : k) 0 0 0 1
    (φ₁ x y = 0 ∧ φ₁ x z = x ∧ φ₁ y z = -y) ∧
    (φ₂ x y = 0 ∧ φ₂ x z = 0 ∧ φ₂ y z = z) ∧
    ∃ c₁ c₂ c : twoCocycle k (ModelValue k) (ModelValue k),
      c₁.1 = φ₁ ∧ c₂.1 = φ₂ ∧ c.1 = φ₁ + φ₂ ∧
      c.1 = NormalizedObstruction.normalized (1 : k) 0 0 0 1 ∧
      classOf k (model c) = classOf k (model c₁) + classOf k (model c₂) ∧
      (∃ B : DeformationTransport.LieBracket k⟦X⟧,
        B.bracket = ExtensionLocus.coordinateBracket (formalBracket k) ∧
        ∀ p q, DeformationTransport.reduce (DeformationTransport.formalReduction k) (B.bracket p q) =
          (model c₁).bracket (DeformationTransport.reduce (DeformationTransport.formalReduction k) p)
            (DeformationTransport.reduce (DeformationTransport.formalReduction k) q)) ∧
      DeformationTransport.Extends (DeformationTransport.formalReduction k) (model c₂) ∧
      obstruction (NormalizedObstruction.coefficients (1 : k) 0 0 0 1) 2 x y z = -x ∧
      (Submodule.Quotient.mk (-x) : ModelValue k ⧸ centerLineValue k) ≠ 0 ∧
      ∀ D : Deformation k (ModelValue k), classOf k D = classOf k (model c) →
        ¬ ExtensionLocus.ExtendsInBasis (basisValue k) (heisenbergBasis k)
          (DeformationTransport.truncatedReduction k).toRingHom D

/-- Equip the free formal module with the specified operation once Jacobi and
alternation have been established. -/
@[instance_reducible] def formalLieRing (h : NormalizedObstruction.IsLieBracket (formalBracket k)) :
    LieRing (FormalCarrier k) where
  bracket p q := formalBracket k p q
  add_lie p q r := by simp [map_add]
  lie_add p q r := by simp [map_add]
  lie_self := h.1
  leibniz_lie p q r := by
    let B := formalBracket k
    have hskew (x y : FormalCarrier k) : B x y = -B y x := by
      have hh := h.1 (x + y)
      change B (x + y) (x + y) = 0 at hh
      have hx : B x x = 0 := h.1 x
      have hy : B y y = 0 := h.1 y
      simp only [map_add, LinearMap.add_apply, hx, hy, zero_add, add_zero] at hh
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hh
    have hj := h.2 p q r
    change B (B p q) r + B (B q r) p + B (B r p) q = 0 at hj
    rw [hskew (B q r) p, hskew (B r p) q, hskew r p, map_neg, neg_neg] at hj
    change B p (B q r) = B (B p q) r + B q (B p r)
    apply Eq.symm
    apply eq_of_sub_eq_zero
    convert hj using 1
    abel

@[instance_reducible] def formalLieAlgebra (h : NormalizedObstruction.IsLieBracket (formalBracket k)) :
    letI : LieRing (FormalCarrier k) := formalLieRing k h
    LieAlgebra k⟦X⟧ (FormalCarrier k) :=
  letI : LieRing (FormalCarrier k) := formalLieRing k h
  { (inferInstance : Module k⟦X⟧ (FormalCarrier k)) with
    lie_smul := fun a p q => (formalBracket k p).map_smul a q }

/-- The specialization X ↦ 0. -/
@[instance_reducible] def specializationAlgebra : Algebra k⟦X⟧ k := PowerSeries.constantCoeff.toAlgebra

abbrev Fiber (A : Type u) [CommRing A] [Algebra k⟦X⟧ A] :=
  A ⊗[k⟦X⟧] FormalCarrier k

def fiberVector (A : Type u) [CommRing A] [Algebra k⟦X⟧ A] (v : ModelValue k) :
    Fiber k A := 1 ⊗ₜ[k⟦X⟧] (1 ⊗ₜ[k] v)

def laurentParameter : k⸨X⸩ := algebraMap k⟦X⟧ k⸨X⸩ PowerSeries.X

/-- Special and generic fibers of the same formal Lie algebra. The actual
generic basis is ordered E, F, H. -/
def FibersType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    ∃ h : NormalizedObstruction.IsLieBracket (formalBracket k),
      letI : LieRing (FormalCarrier k) := formalLieRing k h
      letI : LieAlgebra k⟦X⟧ (FormalCarrier k) := formalLieAlgebra k h
      letI : Algebra k⟦X⟧ k := specializationAlgebra k
      let t := laurentParameter k
      let e := fiberVector k k⸨X⸩ (xValue k)
      let f := (-2 / t) • fiberVector k k⸨X⸩ (yValue k)
      let g := (-2 / t) • fiberVector k k⸨X⸩ (zValue k)
      (∃ S : Fiber k k ≃ₗ⁅k⁆ ModelValue k,
        ∀ v, S (fiberVector k k v) = v) ∧
      (∃ b : Module.Basis (Fin 3) k⸨X⸩ (Fiber k k⸨X⸩), b 0 = e ∧ b 1 = f ∧ b 2 = g) ∧
      (⁅g, e⁆ = (2 : k⸨X⸩) • e ∧ ⁅g, f⁆ = (-2 : k⸨X⸩) • f ∧ ⁅e, f⁆ = g) ∧
      ∃ T : Fiber k k⸨X⸩ ≃ₗ⁅k⸨X⸩⁆ LieAlgebra.SpecialLinear.sl (Fin 2) k⸨X⸩,
        T e = E k⸨X⸩ ∧ T f = F k⸨X⸩ ∧ T g = H k⸨X⸩

end Specs.LieNotes.Heisenberg.Examples
