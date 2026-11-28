import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Heisenberg.NormalizedObstruction
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Heisenberg.DeformationTransport

/-! The extension criterion for the normalized bracket and for every actual
first-order Heisenberg deformation (LD02). -/

noncomputable section

open scoped TensorProduct Polynomial PowerSeries

namespace Specs.LieNotes.Heisenberg.ExtensionLocus

open _root_.AdvancedHomologicalAlgebra.CE (wedge)
open _root_.LieAlgebrasAndRepresentations.InfinitesimalDeformations
  (Deformation Equivalent bracketFormula)
open LieModule.Cohomology (twoCocycle)

universe u v

/-- Coordinates on the scalar extension of an ordered Heisenberg basis, followed
by reduction to its two coefficients in the original Lie algebra. -/
def reduceInBasis {k A : Type u} [Field k] [CommRing A]
    {L : Type v} [LieRing L] [LieAlgebra k L] (b : Module.Basis (Fin 3) k L)
    (hb : AdjointCohomology.HeisenbergBasis b) (ρ : A →+* DualNumber k)
    (p : DeformationTransport.Carrier A) : L × L :=
  let E := basisLieEquivValue b hb.1 hb.2.1 hb.2.2
  let q := DeformationTransport.reduce ρ p
  (E q.1, E q.2)

/-- Existence of a Lie bracket on the free scalar extension in basis `b`
whose reduction is the given dual-number bracket. The scalar coordinate chart
is `(b.baseChange A).equivFun`. -/
def ExtendsInBasis {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {L : Type v} [LieRing L] [LieAlgebra k L] (b : Module.Basis (Fin 3) k L)
    (hb : AdjointCohomology.HeisenbergBasis b) (ρ : A →+* DualNumber k)
    (D : Deformation k L) : Prop :=
  ∃ B : DeformationTransport.LieBracket A, ∀ p q,
    reduceInBasis b hb ρ (B.bracket p q) =
      D.bracket (reduceInBasis b hb ρ p) (reduceInBasis b hb ρ q)

/-- The two equations in the ordered normal-form coordinates `(a,b,c,d,e)`. -/
def Locus {k : Type u} [Field k] (p : Fin 5 → k) : Prop :=
  NormalizedObstruction.Equations (p 0) (p 1) (p 2) (p 3) (p 4)

/-- The fixed normalized bracket with no terms of degree two or higher. -/
abbrev linearBracket {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (t : A) (p : Fin 5 → k) :=
  NormalizedObstruction.bracket t (p 0) (p 1) (p 2) (p 3) (p 4) 0

/-- The tensor bracket in the fixed coordinate chart. -/
def coordinateBracket {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (B : (A ⊗[k] ModelValue k) →ₗ[A] (A ⊗[k] ModelValue k) →ₗ[A]
      (A ⊗[k] ModelValue k)) :
    DeformationTransport.Carrier A →ₗ[A] DeformationTransport.Carrier A →ₗ[A]
      DeformationTransport.Carrier A :=
  let E := DeformationTransport.tensorCoordinates (k := k) (A := A)
  (B.compl₁₂ E.symm.toLinearMap E.symm.toLinearMap).compr₂ E.toLinearMap

/-- The criterion on the normalized representative, including the particular
polynomial and formal brackets and the first-order reduction of the latter. -/
def NormalizedExtensionType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (p : Fin 5 → k),
    let φ := NormalizedObstruction.normalized (p 0) (p 1) (p 2) (p 3) (p 4)
    ((∃ B : DeformationTransport.LieBracket (DeformationTransport.Truncated k),
      DeformationTransport.ReducesTo (DeformationTransport.truncatedReduction k).toRingHom B φ) ↔
      Locus p) ∧
    (Locus p →
      NormalizedObstruction.IsLieBracket (linearBracket (Polynomial.X : k[X]) p) ∧
      NormalizedObstruction.IsLieBracket (linearBracket (PowerSeries.X : k⟦X⟧) p) ∧
      ∃ B : DeformationTransport.LieBracket k⟦X⟧,
        B.bracket = coordinateBracket (linearBracket (PowerSeries.X : k⟦X⟧) p) ∧
        DeformationTransport.ReducesTo (DeformationTransport.formalReduction k) B φ)

/-- For any Heisenberg basis, the coordinates are read in actual adjoint H².
The criterion and the formal extension apply to the given first-order bracket. -/
def ExtensionLocusType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (L : Type v) [LieRing L] [LieAlgebra k L]
    (b : Module.Basis (Fin 3) k L) (hb : AdjointCohomology.HeisenbergBasis b),
    ∃ (e : (Fin 5 → k) ≃ₗ[k] AdjointCohomology.H2 k L)
      (classOf : Deformation k L → AdjointCohomology.H2 k L),
      (∀ p, ∃! f : AdjointCohomology.Cycles k L 2,
        AdjointCohomology.HasNormalValues b p f.1 ∧ Submodule.Quotient.mk f = e p) ∧
      Function.Surjective classOf ∧
      (∀ D D', classOf D = classOf D' ↔ Equivalent D D') ∧
      (∀ D (c : twoCocycle k L L), (∀ x y, D.bracket x y = bracketFormula c.1 x y) →
        ∃ h : AdjointCohomology.Cycles k L 2,
          (∀ x y, h.1 (wedge k L 2 ![x, y]) = c.1 x y) ∧
          classOf D = Submodule.Quotient.mk h) ∧
      ∀ D p, classOf D = e p →
        (ExtendsInBasis b hb (DeformationTransport.truncatedReduction k).toRingHom D ↔ Locus p) ∧
        (Locus p → ExtendsInBasis b hb (DeformationTransport.formalReduction k) D)

end Specs.LieNotes.Heisenberg.ExtensionLocus
