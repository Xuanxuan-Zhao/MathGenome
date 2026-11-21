import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.TorusHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.CupProduct
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.TopologicalKunneth
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.UniversalCoefficientsCohomology
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-! The torus assertion of paper.tex, Proposition `prop:p202-cohomology-rings`.
All groups below are the fixed ordinary singular groups. An orientation of the
circle means a choice of integral generator, encoded by an isomorphism to ℤ;
existence of this choice is a separate unconditional obligation. The result is
required for every choice of orientation, including m = 0 and all degrees. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped TensorProduct DirectSum
namespace P202Specs.TorusRing
open P202Specs.SingularChains P202Specs.AlexanderWhitney
open P202Specs.CohomologyPairs P202Specs.CupProduct
open P202Specs.EilenbergZilber P202Specs.TopologicalKunneth

abbrev Torus := P202Specs.TorusHomology.Torus
abbrev ActiveSet := P202Specs.TorusHomology.ActiveSet
abbrev space (m : ℕ) : TopCat.{0} := TopCat.of (Torus m)
abbrev circle : TopCat.{0} := TopCat.of Circle
abbrev Hm (X : TopCat.{0}) (n : ℕ) := P202Specs.TopologicalKunneth.H ℤ X n
abbrev Hc (X : TopCat.{0}) (n : ℕ) := P202Specs.CupProduct.H ℤ X n
abbrev Orientation := Hm circle 1 ≃ₗ[ℤ] ℤ

/-- Canonical Kronecker evaluation on ordinary singular classes. -/
abbrev evaluate (X : TopCat.{0}) (n : ℕ) : Hc X n →ₗ[ℤ] (Hm X n →ₗ[ℤ] ℤ) :=
  P202Specs.UniversalCoefficientsCohomology.evaluation ℤ ℤ
    (ordinaryComplex ℤ ℤ X) (n : ℤ)

def projection (m : ℕ) (i : Fin m) : space m ⟶ circle :=
  TopCat.ofHom ⟨fun z => z i, continuous_apply i⟩

def circleTorus : circle ≃ₜ space 1 where
  toFun z := fun _ => z
  invFun z := z 0
  left_inv _ := rfl
  right_inv z := by funext i; exact congrArg z (Subsingleton.elim _ _)
  continuous_toFun := continuous_pi fun _ => continuous_id
  continuous_invFun := continuous_apply 0

/-- The product identification appends the last, positively ordered coordinate. -/
def append (m : ℕ) : productSpace (space m) circle ⟶ space (m+1) :=
  TopCat.ofHom ⟨fun z => Fin.snoc z.1 z.2,
    continuous_pi fun i => Fin.lastCases (by simpa [Function.comp_def] using continuous_snd)
      (fun j => by simpa [Function.comp_def] using (continuous_apply j).comp continuous_fst) i⟩

def pointSimplex (X : TopCat.{0}) (x : X) : Simplex X 0 :=
  (simplexEquiv X 0).symm ⟨fun _ => x, continuous_const⟩

/-- The ordinary homology class of the point x, with coefficient +1. -/
def pointClass (X : TopCat.{0}) (x : X) : Hm X 0 :=
  (ordinaryHomologyIso ℤ X 0).inv
    (P202Specs.UniversalCoefficientsCohomology.cycleClass ℤ (complex ℤ ℤ X) 0
      ⟨Finsupp.single (pointSimplex X x) 1, by
        change ((complex ℤ ℤ X).d 0 ((ComplexShape.down ℕ).next 0)).hom _ = 0
        rw [ChainComplex.next_nat_zero]
        rw [(complex ℤ ℤ X).shape 0 0 (by decide)]
        rfl⟩)

def inactive {m n : ℕ} (s : ActiveSet m n) : ActiveSet (m+1) n :=
  ⟨s.val.map Fin.castSuccEmb, by simpa using s.property⟩

def active {m n : ℕ} (s : ActiveSet m n) : ActiveSet (m+1) (n+1) :=
  ⟨insert (Fin.last m) (s.val.map Fin.castSuccEmb), by
    classical
    rw [Finset.card_insert_of_notMem, Finset.card_map, s.property]
    simp⟩

/-- A simultaneous basis, fixed on points and on every iterated external
product. These equations determine the orientation and order of each cycle. -/
structure ProductBasis (e : ExternalProduct ℤ) (o : Orientation) where
  basis : ∀ m n, Module.Basis (ActiveSet m n) ℤ (Hm (space m) n)
  zero : basis 0 0 ⟨∅, rfl⟩ = pointClass (space 0) (fun _ => 1)
  inactive : ∀ m n (s : ActiveSet m n),
    basis (m+1) n (TorusRing.inactive s) =
      hMap ℤ (append m) n
        (ordinaryExternal ℤ e (space m) circle n 0
          (basis m n s ⊗ₜ[ℤ] pointClass circle 1))
  active : ∀ m n (s : ActiveSet m n),
    basis (m+1) (n+1) (TorusRing.active s) =
      hMap ℤ (append m) (n+1)
        (ordinaryExternal ℤ e (space m) circle n 1
          (basis m n s ⊗ₜ[ℤ] o.symm 1))

abbrev coordinateClass (a : Hc circle 1) (m : ℕ) (i : Fin m) : Hc (space m) 1 :=
  hPullback ℤ (projection m i) 1 a

def generator (a : Hc circle 1) (m : ℕ) (i : Fin m) : HStar ℤ (space m) :=
  DirectSum.of (H ℤ (space m)) 1 (coordinateClass a m i)

/-- The empty word is the unit; each nonempty word is ordered by Fin m. -/
def monomial (C : NaturalCohomologyRing ℤ) (a : Hc circle 1) (m : ℕ)
    (s : Finset (Fin m)) : HStar ℤ (space m) :=
  letI := (C.ring (space m)).gradedRing
  ((s.sort (· ≤ ·)).map (generator a m)).prod

/-- The complete graded exterior presentation, including its prescribed
coordinate generators, homogeneous pieces, and the cycle-dual monomials. -/
def Presentation (C : NaturalCohomologyRing ℤ) (e : ExternalProduct ℤ)
    (o : Orientation) (a : Hc circle 1) (B : ProductBasis e o) (m : ℕ) : Prop :=
  letI := (C.ring (space m)).gradedRing
  letI := (C.ring (space m)).algebra
  ∃ E : ExteriorAlgebra ℤ (Fin m → ℤ) ≃ₐ[ℤ] HStar ℤ (space m),
    (∀ i : Fin m, E (ExteriorAlgebra.ι ℤ (Pi.single i 1)) = generator a m i) ∧
    (∀ n : ℕ,
      E '' (↑(⋀[ℤ]^n (Fin m → ℤ)) : Set (ExteriorAlgebra ℤ (Fin m → ℤ))) =
        Set.range (DirectSum.of (H ℤ (space m)) n)) ∧
    (∀ i : Fin m, generator a m i * generator a m i = 0) ∧
    (∀ i j : Fin m, generator a m i * generator a m j =
      -(generator a m j * generator a m i)) ∧
    ∀ n : ℕ, ∃ b : Module.Basis (ActiveSet m n) ℤ (Hc (space m) n),
      (∀ s, DirectSum.of (H ℤ (space m)) n (b s) = monomial C a m s.val) ∧
      (∀ s t, evaluate (space m) n (b s) (B.basis m n t) = if s = t then 1 else 0)

namespace Expected

def orientation : Prop := Nonempty Orientation

def evaluation : Prop := ∀ m n : ℕ, Function.Bijective (evaluate (space m) n)

def circleEvaluation : Prop := ∀ n : ℕ, Function.Bijective (evaluate circle n)

def aboveDimension : Prop := ∀ m n : ℕ, m < n → Subsingleton (Hc (space m) n)

def circleAboveOne : Prop := ∀ n : ℕ, 1 < n → Subsingleton (Hc circle n)

def anticommutation : Prop := ∀ (C : NaturalCohomologyRing ℤ) (X : TopCat.{0})
    (a b : Hc X 1),
  letI := (C.ring X).gradedRing
  DirectSum.of (H ℤ X) 1 a * DirectSum.of (H ℤ X) 1 b =
    -(DirectSum.of (H ℤ X) 1 b * DirectSum.of (H ℤ X) 1 a)

def squares : Prop := ∀ (C : NaturalCohomologyRing ℤ) (a : Hc circle 1)
    (m : ℕ) (i : Fin m),
  letI := (C.ring (space m)).gradedRing
  generator a m i * generator a m i = 0

def exteriorMap : Prop := ∀ (C : NaturalCohomologyRing ℤ) (a : Hc circle 1) (m : ℕ),
  letI := (C.ring (space m)).gradedRing
  letI := (C.ring (space m)).algebra
  ∃ f : ExteriorAlgebra ℤ (Fin m → ℤ) →ₐ[ℤ] HStar ℤ (space m),
    ∀ i : Fin m, f (ExteriorAlgebra.ι ℤ (Pi.single i 1)) = generator a m i

def negative : Prop := ∀ (m : ℕ) (q : ℤ), q < 0 →
  Subsingleton (ordinaryCohomology ℤ ℤ (space m) q)

def ring : Prop :=
  Nonempty Orientation ∧
  ∀ (C : NaturalCohomologyRing ℤ) (e : ExternalProduct ℤ) (o : Orientation),
    ∃ (a : Hc circle 1) (B : ProductBasis e o),
      evaluate circle 1 a = o.toLinearMap ∧ ∀ m : ℕ, Presentation C e o a B m

end Expected
end P202Specs.TorusRing
