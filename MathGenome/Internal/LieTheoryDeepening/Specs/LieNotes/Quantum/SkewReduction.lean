import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.ClassicalLimit

noncomputable section

open scoped TensorProduct

namespace Specs.LieNotes.Quantum.SkewReduction

open ClassicalLimit (ClassicalReduction firstLevel modParameter)
open Completion (AtLevel CompletedSquare HopfMaps Level Square Uh project)
open MatrixSpecialization (Classical)
open scoped ClassicalLimit MatrixSpecialization

universe u

abbrev ClassicalSquare (k : Type u) [Field k] :=
  Classical k ⊗[k] Classical k

variable {k : Type u} [Field k]

/-- Tensor-factor exchange on the ordinary enveloping tensor square. -/
abbrev classicalFlip : ClassicalSquare k ≃ₐ[k] ClassicalSquare k :=
  Algebra.TensorProduct.comm k (Classical k) (Classical k)

variable [CharZero k]

def levelFlip (N : Level) : Square k N ≃ₐ[Completion.A k N] Square k N :=
  Algebra.TensorProduct.comm (Completion.A k N) (Completion.U k N) (Completion.U k N)

@[simp] theorem levelFlip_tmul (N : Level) (a b : Completion.U k N) :
    levelFlip N (a ⊗ₜ[Completion.A k N] b) = b ⊗ₜ[Completion.A k N] a := rfl

set_option maxHeartbeats 500000 in
private theorem reduce_levelFlip {M N : Level} (e : M ≤ N) (z : Square k N) :
    Completion.reduce .square e (levelFlip N z) =
      levelFlip M (Completion.reduce .square e z) := by
  let red : Square k N →+* Square k M := Completion.reduce .square e
  change red (levelFlip N z) = levelFlip M (red z)
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a b
    change Coproduct.tensorReduce e (levelFlip N (a ⊗ₜ[Completion.A k N] b)) =
      levelFlip M (Coproduct.tensorReduce e (a ⊗ₜ[Completion.A k N] b))
    simp only [levelFlip_tmul, Coproduct.tensorReduce_tmul]
  · intro a b ha hb
    calc
      red (levelFlip N (a + b)) = red (levelFlip N a) + red (levelFlip N b) :=
        (congrArg red ((levelFlip N).map_add a b)).trans
          (red.map_add (levelFlip N a) (levelFlip N b))
      _ = levelFlip M (red a) + levelFlip M (red b) := congrArg₂ (· + ·) ha hb
      _ = levelFlip M (red (a + b)) :=
        ((congrArg (levelFlip M) (red.map_add a b)).trans
          ((levelFlip M).map_add (red a) (red b))).symm

private local instance squarePowerSeriesAlgebra (N : Level) :
    Algebra (PowerSeries k) (Square k N) :=
  Completion.levelPowerSeriesAlgebra k .square N

private def levelFlipSeries (N : Level) : Square k N →ₐ[PowerSeries k] Square k N where
  __ := (levelFlip (k := k) N).toRingEquiv.toRingHom
  commutes' f := (levelFlip (k := k) N).commutes (Truncations.truncate N f)

/-- The exchange of the two tensor factors at every finite level of the completed square. -/
def completedFlip : CompletedSquare k →ₐ[PowerSeries k] CompletedSquare k :=
  (AlgHom.pi (A := Square k) (fun N => (levelFlipSeries N).comp (project k .square N))).codRestrict
    (Completion.compatibleTuples k .square) (fun z => by
      intro M N e
      change Completion.reduce .square e (levelFlip N (project k .square N z)) =
        levelFlip M (project k .square M z)
      exact (reduce_levelFlip e (project k .square N z)).trans
        (congrArg (levelFlip M) (z.property M N e)))

@[simp] theorem project_completedFlip (z : CompletedSquare k) (N : Level) :
    project k .square N (completedFlip z) = levelFlip N (project k .square N z) := rfl

variable {D : HopfMaps k}

/-- Specialization of the completed algebra into the ordinary enveloping algebra. -/
def specialize (r : ClassicalReduction D) : Uh k →ₐ[k] Classical k :=
  r.equiv.toAlgHom.comp (modParameter k .single)

/-- Specialization of the completed square via the comparison on both factors. -/
def specializeSquare (r : ClassicalReduction D) : CompletedSquare k →ₐ[k] ClassicalSquare k :=
  let t : AtLevel k .square firstLevel →ₐ[k] ClassicalSquare k :=
    { r.tensorComparison.toRingHom with
      commutes' := fun a => by
        change r.tensorComparison
          ((algebraMap k (MatrixSpecialization.LevelOne k) a) ⊗ₜ[Completion.A k firstLevel] 1) =
            algebraMap k (ClassicalSquare k) a
        calc
          _ = r.comparison (algebraMap k (MatrixSpecialization.LevelOne k) a) ⊗ₜ[k]
              r.comparison 1 := r.tensorComparison_tmul _ _
          _ = _ := by rw [r.comparison.commutes, map_one, Algebra.TensorProduct.algebraMap_apply] }
  t.comp ((r.levelEquiv .square).toAlgHom.comp (modParameter k .square))

/-- The associative commutator. -/
abbrev commutator {A : Type*} [Mul A] [Sub A] (a b : A) : A := a * b - b * a

/-- The action on both factors of the enveloping tensor square. -/
def diagonalAdjoint (x : Classical k) : ClassicalSquare k →ₗ[k] ClassicalSquare k :=
  let ad := LinearMap.mulLeft k x - LinearMap.mulRight k x
  TensorProduct.map ad (LinearMap.id : Classical k →ₗ[k] Classical k) +
    TensorProduct.map (LinearMap.id : Classical k →ₗ[k] Classical k) ad

/-- Division in the completed square and its lift-independent classical value. -/
structure DividedSkew (r : ClassicalReduction D) where
  divided : Uh k →ₗ[PowerSeries k] CompletedSquare k
  skew : Classical k →ₗ[k] ClassicalSquare k
  specialize_surjective : Function.Surjective (specialize r)
  cocommutative (x : Classical k) :
    classicalFlip (r.hopf.comul x) = r.hopf.comul x
  division_eq (X : Uh k) (Z : CompletedSquare k) :
    (PowerSeries.X : PowerSeries k) • Z = D.comul X - completedFlip (D.comul X) ↔
      Z = divided X
  reduce_divided (X : Uh k) :
    specializeSquare r (divided X) = skew (specialize r X)
  flip_skew (x : Classical k) : classicalFlip (skew x) = -skew x
  skew_commutator (x y : Classical k) :
    skew (commutator x y) =
      commutator (r.hopf.comul x) (skew y) + commutator (skew x) (r.hopf.comul y)
  primitive_cocycle (x y : Classical k)
      (hx : r.hopf.comul x = x ⊗ₜ[k] 1 + 1 ⊗ₜ[k] x)
      (hy : r.hopf.comul y = y ⊗ₜ[k] 1 + 1 ⊗ₜ[k] y) :
    skew (commutator x y) = diagonalAdjoint x (skew y) - diagonalAdjoint y (skew x)

/-- The first-order skew map for the actual completed type-A₂ specialization. -/
def SkewReductionProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    ∃ (d : ∀ N : Level, Coproduct.TruncatedData k N)
      (s : ∀ N : Level, Hopf.TruncatedData k N (d N)) (D : HopfMaps k),
      Completion.ProjectsTo D d s ∧ Completion.HopfIdentities D ∧
      Completion.ContinuousHopfMaps D ∧ ∃ r : ClassicalReduction D, Nonempty (DividedSkew r)

end Specs.LieNotes.Quantum.SkewReduction
