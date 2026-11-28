import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.SuperPbwBasis
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.SuperEnvelopingModules
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Maps

namespace LieNotes.SuperRestricted.SuperPbw.Definitions

open SuperEnveloping.Construction
open scoped TensorProduct

noncomputable section

universe u v

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
  (L : LieSuperalgebra k V)

abbrev Even := L.grading.piece 0
abbrev Odd := L.grading.piece 1
abbrev SymmetricExterior := SymmetricAlgebra k (Even L) ⊗[k] ExteriorAlgebra k (Odd L)

def evenLetter : Even L →ₗ[k] SymmetricExterior L :=
  Algebra.TensorProduct.includeLeft.toLinearMap.comp (SymmetricAlgebra.ι k (Even L))

def oddLetter : Odd L →ₗ[k] SymmetricExterior L :=
  Algebra.TensorProduct.includeRight.toLinearMap.comp (ExteriorAlgebra.ι k)

/-- Assemble linear maps on the two summands using the fixed parity decomposition. -/
def assemble {A : Type*} [AddCommGroup A] [Module k A] (G : Grading k V)
    (f : ∀ i, G.piece i →ₗ[k] A) : V →ₗ[k] A :=
  (DirectSum.toModule k _ A f).comp
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap G.piece) G.isInternal).symm.toLinearMap

theorem parity_cases (i : ZMod 2) : i = 0 ∨ i = 1 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

def tensorGenerator : V →ₗ[k] SymmetricExterior L :=
  assemble L.grading fun i =>
    if h : i = 0 then h.symm ▸ evenLetter L
    else ((parity_cases i).resolve_left h).symm ▸ oddLetter L

abbrev HomogeneousLetter := Σ i, L.grading.piece i

def homogeneousWordDegree (xs : List (HomogeneousLetter L)) : Degree :=
  (xs.length, (xs.map Sigma.fst).sum)

def homogeneousWord (xs : List (HomogeneousLetter L)) : List V :=
  xs.map fun x => (x.2 : V)

/-- Total length in the symmetric and exterior generators, with parity the exterior length
modulo two. The subspace is the span of the corresponding homogeneous products. -/
def tensorPiece (d : Degree) : Submodule k (SymmetricExterior L) :=
  Submodule.span k (Set.range fun xs : {xs : List (HomogeneousLetter L) //
      homogeneousWordDegree L xs = d} => word (tensorGenerator L) (homogeneousWord L xs.val))

/-- The canonical inclusion of the corresponding successive quotient into the associated graded. -/
def gradedComponent (d : Degree) : Submodule k (AssociatedGraded L) :=
  LinearMap.range (DirectSum.lof k Degree (GradedPiece L) d)

/-- The degree-one principal symbol of a homogeneous generator. -/
def generatorSymbol (i : ZMod 2) : L.grading.piece i →ₗ[k] AssociatedGraded L :=
  (ofSymbol L (1, i)).comp (((ι L).comp (L.grading.piece i).subtype).codRestrict
    (filtered L (1, i)) fun x => ⟨wordFiltration_generator (ι L) x,
      (mem_paritySpace ..).mpr (by
        change parity L (quotientMap L (TensorAlgebra.ι k (x : V))) = _
        rw [parity_quotientMap, tensorParity_ι L.grading x.property, map_smul]
        rfl)⟩)

end

end LieNotes.SuperRestricted.SuperPbw.Definitions

namespace Specs.LieNotes.SuperRestricted.SuperPbw

open _root_.LieNotes.SuperRestricted
open _root_.LieNotes.SuperRestricted.SuperPbwBasis
open _root_.LieNotes.SuperRestricted.SuperPbw.Definitions
open _root_.LieNotes.SuperRestricted.SuperEnveloping.Construction
open scoped TensorProduct

universe u v w z

/-- The PBW isomorphism on the actual quotient, preserving both degrees and generators. -/
def associatedGradedType : Prop :=
  ∀ {k : Type u} {V : Type v} {I : Type w} [Field k] [AddCommGroup V] [Module k V]
    [NeZero (2 : k)] [LinearOrder I] (L : LieSuperalgebra k V) (b : Module.Basis I k V)
    (degree : I → ZMod 2), Homogeneous L b degree →
    ∃! e : SymmetricExterior L ≃ₐ[k] AssociatedGraded L,
      (∀ x : Even L, e (evenLetter L x) = generatorSymbol L 0 x) ∧
      (∀ x : Odd L, e (oddLetter L x) = generatorSymbol L 1 x) ∧
      ∀ d : Degree, (SuperPbw.Definitions.tensorPiece L d).map e.toLinearMap = gradedComponent L d

/-- The ordered basis, the canonical bigraded algebra comparison, and graded-module agreement. -/
def superPbwType : Prop :=
  SuperPbwBasis.orderedBasisType.{u, v, w} ∧ associatedGradedType.{u, v, w} ∧
    SuperEnvelopingModules.gradedModulesAgreeType.{u, v, w, z}

end Specs.LieNotes.SuperRestricted.SuperPbw
