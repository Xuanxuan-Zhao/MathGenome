import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.NonabelianCohomology
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.NormOneTorus

open CategoryTheory AlgebraicGeometry
open LinearAlgebraicGroups.WeilRestriction
open LinearAlgebraicGroups.Descent.NonabelianCohomology
open LinearAlgebraicGroups.Specs.StandardGroups (multiplicativePoints)
open scoped TensorProduct CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Specs.NormOneCohomology

universe u

noncomputable section

/-- The B04 scheme kernel and its rank-one splitting and character action. -/
def KernelGeometry : Prop :=
  NormOneTorus.NormKernel.{u} ∧ NormOneTorus.KernelSplitting.{u} ∧
    NormOneTorus.CharacterAction.{u}

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The field norm on units. -/
abbrev fieldNorm : Kˣ →* kˣ := Units.map (Algebra.norm k)

variable {W H : AffineAlgebraicGroup k}
  (e : (groupPointsFunctor k).obj W.val ≅ extendedUnits k K)
  {n : W.val ⟶ H.val} (T : NormOneTorus.KernelModel e n)

abbrev KernelPoints (S : Type u) [Field S] [Algebra k S] :=
  Descent.NonabelianCohomology.Points k S (specGroup T.coordinate).X

abbrev WeilPoints (S : Type u) [Field S] [Algebra k S] :=
  Descent.NonabelianCohomology.Points k S W.val.X

/-- The scheme kernel inclusion on points. -/
abbrev includePoint (S : Type u) [Field S] [Algebra k S] :
    KernelPoints e T S →* WeilPoints (W := W) S :=
  (((groupPointsFunctor k).map T.inclusion).app (CommAlgCat.of k S)).hom

/-- The determinant norm on the points of the Weil restriction. -/
abbrev normOnPoints (S : Type u) [Field S] [Algebra k S] :
    WeilPoints (W := W) S →* Sˣ :=
  (Units.map (pointNorm k K (CommAlgCat.of k S))).comp
    ((e.app (CommAlgCat.of k S)).groupIsoToMulEquiv.toMonoidHom)

/-- The isomorphism as groups, with the map from the norm quotient specified by
taking the cocycle of any lift of a base-field unit. The group operation on
cohomology is the one induced by pointwise multiplication of cocycles. The type
`H1 ρ` with the indicated topology and point action is `groupH1`. -/
def CohomologyIso : Prop :=
  ∀ (k K S : Type u) [Field k] [Field K] [Field S] [Algebra k K] [Algebra k S]
    [Algebra.IsQuadraticExtension k K] [Algebra.IsSeparable k K] [IsSepClosure k S]
    (W H : AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj W.val ≅ extendedUnits k K)
    (t : (groupPointsFunctor k).obj H.val ≅ multiplicativePoints k)
    (n : W.val ⟶ H.val), NormOneTorus.RealizesNorm e t n →
    ∀ (T : NormOneTorus.KernelModel e n),
      letI : TopologicalSpace (KernelPoints e T S) := ⊥
      let ρ := pointAction k S (specGroup T.coordinate).X
      (∀ a : kˣ, ∃ w : WeilPoints (W := W) S,
        normOnPoints e S w = Units.map (algebraMap k S) a) ∧
      ∃ G : CommGroup (H1 ρ),
        letI := G
        ∃ E : H1 ρ ≃*
            kˣ ⧸ (fieldNorm (k := k) (K := K)).range,
          (1 : H1 ρ) = basepoint ρ ∧
          (∀ a b c : Cocycle ρ, (∀ σ, c σ = a σ * b σ) →
            classOf c = classOf a * classOf b) ∧
          ∀ (a : kˣ) (w : WeilPoints (W := W) S),
            normOnPoints e S w = Units.map (algebraMap k S) a →
            ∃ c : Cocycle ρ,
              (∀ σ, includePoint e T S (c σ) = w⁻¹ * pointAction k S W.val.X σ w) ∧
              E (classOf c) = QuotientGroup.mk a

/-- The norms of nonzero complex numbers are exactly the positive real units. -/
def ComplexNormRange : Prop :=
  ∀ a : ℝˣ, a ∈ (fieldNorm (k := ℝ) (K := ℂ)).range ↔ 0 < (a : ℝ)

/-- For the real norm-one torus the first Galois cohomology group has order two. -/
def RealCohomology : Prop :=
  ∀ (S : Type) [Field S] [Algebra ℝ S] [IsSepClosure ℝ S]
    (W H : AffineAlgebraicGroup ℝ)
    (e : (groupPointsFunctor ℝ).obj W.val ≅ extendedUnits ℝ ℂ)
    (t : (groupPointsFunctor ℝ).obj H.val ≅ multiplicativePoints ℝ)
    (n : W.val ⟶ H.val), NormOneTorus.RealizesNorm e t n →
    ∀ (T : NormOneTorus.KernelModel e n),
      Nat.card (groupH1 ℝ (specGroup T.coordinate).X S) = 2

end

end LinearAlgebraicGroups.Specs.NormOneCohomology
