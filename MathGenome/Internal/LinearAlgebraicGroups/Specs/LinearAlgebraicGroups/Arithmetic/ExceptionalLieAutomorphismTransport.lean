import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdjointLieAutomorphisms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.PolarRealStructures
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Basic

open AlgebraicGeometry CategoryTheory Topology
open scoped Matrix TensorProduct

namespace LinearAlgebraicGroups.Specs.ExceptionalLieAutomorphismTransport

open AbsoluteDynkinTypes (HasDynkinType IsAbsolutelyAlmostSimple)
open AdjointRepresentation (GroupPoints)
open GeometricRadicals (GeometricGroup)
open Pinning (AttachedDatum SplitBorelPair)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open LieAlgebrasAndRepresentations.RealForms (Conjugation)

noncomputable section

abbrev realPointsAlgebra := CommAlgCat.of ℝ ℂ
abbrev complexPointsAlgebra := CommAlgCat.of ℂ ℂ

abbrev ComplexPoints (G : AffineAlgebraicGroup ℝ) := GroupPoints G.val realPointsAlgebra

abbrev complexGroup (G : AffineAlgebraicGroup ℝ) := (groupBaseChange ℝ ℂ).obj G.val

abbrev coefficientConjugation : realPointsAlgebra ⟶ realPointsAlgebra :=
  CommAlgCat.ofHom Complex.conjAe.toAlgHom

abbrev realConjugation (G : AffineAlgebraicGroup ℝ) : ComplexPoints G →* ComplexPoints G :=
  (((groupPointsFunctor ℝ).obj G.val).map coefficientConjugation).hom

abbrev onDual (G : AffineAlgebraicGroup ℝ) :=
  baseChangePoint ℝ ℂ G.val.X (CommAlgCat.of ℂ (DualNumber ℂ))

/-- Conjugate both coefficients of a dual number, fixing its square-zero
generator. The comparison identifies restriction before and after taking dual numbers. -/
abbrev dualConjugation :=
  let d := AdjointRepresentation.dualRestriction (k := ℝ) ℂ complexPointsAlgebra
  d.hom ≫ AdjointRepresentation.dualMap coefficientConjugation ≫ d.inv

/-- The antilinear operator comes from the original real structure under the
scalar comparison on the actual identity tangent. -/
def IsGroundFieldConjugation (G : AffineAlgebraicGroup ℝ) (s : IdentityLieStructure (complexGroup G)) :
    letI := s.lieRing; letI := s.lieAlgebra; Conjugation (Lie ℂ (complexGroup G)) → Prop :=
  letI := s.lieRing
  letI := s.lieAlgebra
  fun σ => ∀ x : Lie ℂ (complexGroup G),
    onDual G (σ.map x).toMul.val =
      mapPoints dualConjugation (onDual G x.toMul.val)

def GroundFieldConjugationStatement : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (s : IdentityLieStructure (complexGroup G)),
    letI := s.lieRing
    letI := s.lieAlgebra
    ∃ σ : Conjugation (Lie ℂ (complexGroup G)), IsGroundFieldConjugation G s σ

/-- Polar reduction at the identity Lie algebra of the complex base change. -/
def LiePolarStatement : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ), GeometricRadicals.IsSemisimple G →
    ∀ s : IdentityLieStructure (complexGroup G),
      letI := s.lieRing; letI := s.lieAlgebra
      let L := Lie ℂ (complexGroup G)
      ∃ (σ ω : Conjugation L) (θ c : L ≃ₗ⁅ℂ⁆ L),
        IsGroundFieldConjugation G s σ ∧
        _root_.Specs.LieAlgebrasAndRepresentations.PolarRealStructures.IsCompact ω ∧
        Function.Involutive θ ∧ Function.Commute θ ω.map ∧
        ∀ x, c (σ.map x) = θ (ω.map (c x))

/-- Integration of the complex bracket automorphisms on the specified
simply connected real group after scalar extension. -/
def LieLiftStatement : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ), GeometricRadicals.IsSemisimple G →
    GeometricallySimplyConnected G →
    ∀ s : IdentityLieStructure (complexGroup G),
      letI := s.lieRing; letI := s.lieAlgebra
      ∀ b : Lie ℂ (complexGroup G) ≃ₗ⁅ℂ⁆ Lie ℂ (complexGroup G),
        ∃ a : Aut (complexGroup G), ∀ x, mapPointKernel a.asIso.hom x = b x

/-- The exceptional Cartan types, read on a Borel pair of the geometric group. -/
def HasExceptionalType (G : AffineAlgebraicGroup ℝ) : Prop :=
  ∃ (P : SplitBorelPair (AlgebraicClosure ℝ)) (_ : P.G = GeometricGroup G)
    (D : AttachedDatum P),
    letI := D.comm
    let C := RootData.integralCartan D.datum.rootDatum D.base
    HasDynkinType C .E6 ∨ HasDynkinType C .E7 ∨ HasDynkinType C .E8

/-- The complex point map of a real group-scheme morphism. -/
abbrev pointMap {G Q : AffineAlgebraicGroup ℝ} (f : G.val ⟶ Q.val) :
    ComplexPoints G →* ComplexPoints Q :=
  (((groupPointsFunctor ℝ).map f).app realPointsAlgebra).hom

/-- The given complex algebraic automorphism acts on the original points
by base-change comparison. -/
def ActsOnComplexPoints (G : AffineAlgebraicGroup ℝ)
    (a : Aut (complexGroup G)) (f : ComplexPoints G → ComplexPoints G) : Prop :=
  ∀ z : GroupPoints (complexGroup G) complexPointsAlgebra,
    f (baseChangePoint ℝ ℂ G.val.X complexPointsAlgebra z) =
      baseChangePoint ℝ ℂ G.val.X complexPointsAlgebra
        (((groupPointsFunctor ℂ).map a.asIso.hom).app complexPointsAlgebra z)

/-- The lifted actions on the original complex points and their precise
differentials on dual numbers. -/
def PointLiftStatement : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ), GeometricRadicals.IsSemisimple G →
    GeometricallySimplyConnected G →
    ∃ s : IdentityLieStructure (complexGroup G),
      letI := s.lieRing
      letI := s.lieAlgebra
      let L := Lie ℂ (complexGroup G)
      ∃ (σL ωL : Conjugation L) (θL cL : L ≃ₗ⁅ℂ⁆ L)
        (ω θ c : MulAut (ComplexPoints G))
        (aω aθ ac : Aut (complexGroup G)),
        IsGroundFieldConjugation G s σL ∧
        _root_.Specs.LieAlgebrasAndRepresentations.PolarRealStructures.IsCompact ωL ∧
        Function.Involutive θL ∧ Function.Commute θL ωL.map ∧
        (∀ x, cL (σL.map x) = θL (ωL.map (cL x))) ∧
        ActsOnComplexPoints G aω (fun x => ω (realConjugation G x)) ∧
        ActsOnComplexPoints G aθ θ ∧ ActsOnComplexPoints G ac c ∧
        (∀ x, ωL.map x = mapPointKernel aω.asIso.hom (σL.map x)) ∧
        (∀ x, θL x = mapPointKernel aθ.asIso.hom x) ∧
        (∀ x, cL x = mapPointKernel ac.asIso.hom x) ∧
        Function.Involutive θ ∧ Function.Involutive ω ∧ Function.Commute θ ω ∧
        ∀ x, c (realConjugation G x) = θ (ω (c x))

/-- Evaluation in a closed matrix realization. The topology used below is
the topology induced from the entries of this matrix. -/
abbrev matrixPoint {ι : Type} [Fintype ι] [DecidableEq ι]
    {G M : AffineAlgebraicGroup ℝ} (j : G.val ⟶ M.val)
    (l : (groupPointsFunctor ℝ).obj M.val ≅ StandardGroups.generalLinearPoints ℝ ι) :
    ComplexPoints G →* Matrix.GeneralLinearGroup ι ℂ :=
  (l.hom.app realPointsAlgebra).hom.comp (pointMap j)

abbrev matrixPointValue {ι : Type} [Fintype ι] [DecidableEq ι]
    {G M : AffineAlgebraicGroup ℝ} (j : G.val ⟶ M.val)
    (l : (groupPointsFunctor ℝ).obj M.val ≅ StandardGroups.generalLinearPoints ℝ ι) :
    ComplexPoints G → Matrix ι ι ℂ := fun x => (matrixPoint j l x).val

/-- The matrix acts as adjoint conjugation on dual-number points, in the
specified basis of the identity tangent of the complex base change. -/
def ActsByAdjoint {ι : Type} [Fintype ι] [DecidableEq ι]
    {G Q M : AffineAlgebraicGroup ℝ} (q : G.val ⟶ Q.val) (j : Q.val ⟶ M.val)
    (l : (groupPointsFunctor ℝ).obj M.val ≅ StandardGroups.generalLinearPoints ℝ ι)
    (s : IdentityLieStructure (complexGroup G))
    (b : letI := s.lieRing; letI := s.lieAlgebra;
      Module.Basis ι ℂ (Lie ℂ (complexGroup G))) : Prop :=
  letI := s.lieRing
  letI := s.lieAlgebra
  ∀ (g : GroupPoints (complexGroup G) complexPointsAlgebra) (x : Lie ℂ (complexGroup G)),
    let z := baseChangePoint ℝ ℂ G.val.X complexPointsAlgebra g
    let N := matrixPoint j l (pointMap q z)
    (b.equivFun.symm (N.val *ᵥ b.equivFun x)).toMul.val =
      AdjointRepresentation.conjugate g x

/-- The algebraic adjoint quotient and its matrix action on the complex
identity tangent, with the bracket equations transported from the real basis. -/
def ComplexAdjointStatement : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ), GeometricRadicals.IsSemisimple G →
    ∀ s : IdentityLieStructure (complexGroup G),
      letI := s.lieRing; letI := s.lieAlgebra
      ∃ (Z : ClosedSubgroup G.val) (Q : AffineAlgebraicGroup ℝ) (q : G.val ⟶ Q.val)
        (d : ℕ) (N A : AffineAlgebraicGroup ℝ) (i : Q.val ⟶ A.val) (j : A.val ⟶ N.val)
        (l : (groupPointsFunctor ℝ).obj N.val ≅
          StandardGroups.generalLinearPoints ℝ (ULift.{0} (Fin d)))
        (b : Module.Basis (ULift.{0} (Fin d)) ℂ (Lie ℂ (complexGroup G))),
        AdjointCocharacters.IsAdjointQuotient Z q ∧ CentralIsogenies.IsCentralIsogeny q ∧
        IsFinite Z.group.X.hom ∧ IsClosedImmersion (i ≫ j).hom.hom.left ∧
        IsClosedImmersion j.hom.hom.left ∧
        Function.Surjective (pointMap q) ∧ AdjointLieAutomorphisms.IsGeometricIdentityComponent i ∧
        ActsByAdjoint q (i ≫ j) l s b ∧
        (∀ y, AdjointLieAutomorphisms.PreservesBracket
          (fun r t u => b.repr ⁅b r, b t⁆ u) (RingHom.id ℂ) (matrixPoint (i ≫ j) l y) ∧
          (matrixPoint (i ≫ j) l y).val.det = 1) ∧
        (∀ m, AdjointLieAutomorphisms.PreservesBracket
          (fun r t u => b.repr ⁅b r, b t⁆ u) (RingHom.id ℂ) m ↔
          ∃ z : ComplexPoints A, matrixPoint j l z = m)

/-- Transport to the given simply connected group and to its real adjoint
quotient. The two actions on the matrix subgroup are conjugation by the
chosen (possibly outer) Lie automorphisms. -/
def Statement : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (n : ℕ) (M : AffineAlgebraicGroup ℝ)
    (j : G.val ⟶ M.val)
    (_ : (groupPointsFunctor ℝ).obj M.val ≅ StandardGroups.generalLinearPoints ℝ (Fin n)),
    IsClosedImmersion j.hom.hom.left →
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → HasExceptionalType G →
    ∃ s : IdentityLieStructure (complexGroup G),
      letI := s.lieRing
      letI := s.lieAlgebra
      let L := Lie ℂ (complexGroup G)
      ∃ (σL ωL : Conjugation L) (θL cL : L ≃ₗ⁅ℂ⁆ L)
        (ω θ c : MulAut (ComplexPoints G))
        (aω aθ ac : Aut (complexGroup G)),
        IsGroundFieldConjugation G s σL ∧
        _root_.Specs.LieAlgebrasAndRepresentations.PolarRealStructures.IsCompact ωL ∧
        Function.Involutive θL ∧ Function.Commute θL ωL.map ∧
        (∀ x, cL (σL.map x) = θL (ωL.map (cL x))) ∧
        ActsOnComplexPoints G aω (fun x => ω (realConjugation G x)) ∧
        ActsOnComplexPoints G aθ θ ∧ ActsOnComplexPoints G ac c ∧
        (∀ x, ωL.map x = mapPointKernel aω.asIso.hom (σL.map x)) ∧
        (∀ x, θL x = mapPointKernel aθ.asIso.hom x) ∧
        (∀ x, cL x = mapPointKernel ac.asIso.hom x) ∧
        Function.Involutive ω ∧ Function.Involutive θ ∧ Function.Commute θ ω ∧
        (∀ x, c (realConjugation G x) = θ (ω (c x))) ∧
        ∃ (Z : ClosedSubgroup G.val) (Q : AffineAlgebraicGroup ℝ) (q : G.val ⟶ Q.val)
          (d : ℕ) (N : AffineAlgebraicGroup ℝ) (i : Q.val ⟶ N.val)
          (l : (groupPointsFunctor ℝ).obj N.val ≅
            StandardGroups.generalLinearPoints ℝ (ULift.{0} (Fin d)))
          (b : Module.Basis (ULift.{0} (Fin d)) ℂ L)
          (B : Subgroup (Matrix.GeneralLinearGroup (ULift.{0} (Fin d)) ℂ)),
          let f := matrixPoint i l
          let coeff := fun r t u => b.repr ⁅b r, b t⁆ u
          letI : TopologicalSpace (ComplexPoints Q) :=
            TopologicalSpace.induced (matrixPointValue i l) inferInstance
          letI : TopologicalSpace B :=
            TopologicalSpace.induced
              (fun p : B => (p.val.val : Matrix (ULift.{0} (Fin d)) (ULift.{0} (Fin d)) ℂ))
              inferInstance
          AdjointCocharacters.IsAdjointQuotient Z q ∧ CentralIsogenies.IsCentralIsogeny q ∧
          IsFinite Z.group.X.hom ∧ IsClosedImmersion i.hom.hom.left ∧
          Function.Surjective (pointMap q) ∧ ActsByAdjoint q i l s b ∧
          (∀ g, g ∈ B ↔ AdjointLieAutomorphisms.PreservesBracket coeff (RingHom.id ℂ) g) ∧
          ∃ hB : ∀ y, f y ∈ B,
            let ρ : ComplexPoints Q →* B := f.codRestrict B hB
            IsClosedEmbedding ρ ∧ connectedComponent (1 : B) ⊆ Set.range ρ ∧
            Function.Injective (MulAut.conj : ComplexPoints Q →* MulAut (ComplexPoints Q)) ∧
            ∃ ωQ θQ : MulAut (ComplexPoints Q),
              (∀ x, pointMap q (ω x) = ωQ (pointMap q x)) ∧
              (∀ x, pointMap q (θ x) = θQ (pointMap q x)) ∧
              (∀ y v, b.equivFun.symm ((f (ωQ y)).val *ᵥ b.equivFun v) =
                ωL.map (b.equivFun.symm ((f y).val *ᵥ b.equivFun (ωL.map v)))) ∧
              (∀ y v, b.equivFun.symm ((f (θQ y)).val *ᵥ b.equivFun v) =
                θL (b.equivFun.symm ((f y).val *ᵥ b.equivFun (θL.symm v))))

end

end LinearAlgebraicGroups.Specs.ExceptionalLieAutomorphismTransport
