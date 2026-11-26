import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SquareZeroLiftTorsor
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Homology.Double

noncomputable section

namespace CommutativeAlgebraNotes.SquareZeroLift.Lift

universe u v w n l
variable {A' : Type u} {A : Type v} {B : Type w} {N : Type n}
  [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
  {c : e.CoefficientMap (B := B) N} (L : Lift.{u,v,w,n,l} e c)

/-- The inclusion of the prescribed coefficient module into a marked lift. -/
def coefficientInclusion : N →+ L.Ring :=
  L.ker.subtype.toAddMonoidHom.comp L.marking.symm.toAddMonoidHom

/-- The group of algebra automorphisms fixing both the reduction and its marked kernel. -/
def markedAutomorphisms : Subgroup (L.Ring ≃ₐ[A'] L.Ring) where
  carrier := { f | (∀ x, L.map (f x) = L.map x) ∧ ∀ x : L.ker, f x = x }
  one_mem' := ⟨fun _ => rfl, fun _ => rfl⟩
  mul_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    exact ⟨fun x => (hf (g x)).trans (hg x), fun x => by rw [AlgEquiv.mul_apply, hg', hf']⟩
  inv_mem' := by
    rintro f ⟨hf, hf'⟩
    refine ⟨fun x => ?_, fun x => ?_⟩
    · change L.map (f.symm x) = L.map x
      simpa only [AlgEquiv.apply_symm_apply] using (hf (f.symm x)).symm
    · change f.symm (x : L.Ring) = x
      exact (congrArg f.symm (hf' x)).symm.trans (f.symm_apply_apply x)

end CommutativeAlgebraNotes.SquareZeroLift.Lift

namespace Specs.CommutativeAlgebraNotes.SquareZeroLiftAutomorphismsAndExt

open CommutativeAlgebraNotes.SquareZeroLift
universe u v w t n l m
variable {A' : Type u} {A : Type v} {B : Type w} {N : Type n}
  [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
  {c : e.CoefficientMap (B := B) N}

local notation "Der" => @Derivation A B N _ _ _ _ _ (Module.compHom N (algebraMap A B))

/-- The additive derivation group identifies with the marked automorphism group via
translation by the derivation of the residue. The formula commutes with transport by
any isomorphism of marked lifts. -/
def AutomorphismComparison : Prop :=
  ∃ E : ∀ (L : Lift.{u,v,w,n,l} e c),
      Multiplicative Der ≃* L.markedAutomorphisms,
    (∀ (L : Lift.{u,v,w,n,l} e c) (d : Multiplicative Der) (x : L.Ring),
      (E L d).val x =
        x + L.coefficientInclusion (d.toAdd (L.map x))) ∧
    (∀ (L M : Lift.{u,v,w,n,l} e c) (f : L.Iso M)
      (d : Multiplicative Der) (x : L.Ring),
      f.equiv ((E L d).val x) =
        (E M d).val (f.equiv x))

def automorphismsType : Prop :=
  ∀ {A' : Type u} {A : Type v} {B : Type w} {N : Type n}
    [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
    {c : e.CoefficientMap (B := B) N},
    AutomorphismComparison.{u,v,w,n,l} (c := c)

/-- The torsor assertion uses the established action on marked lift classes. -/
abbrev torsorType := SquareZeroLiftTorsor.torsorType.{u,v,w,t,n,l}

end Specs.CommutativeAlgebraNotes.SquareZeroLiftAutomorphismsAndExt

namespace Specs.CommutativeAlgebraNotes.SquareZeroLiftAutomorphismsAndExt

open CategoryTheory CategoryTheory.Pretriangulated CommutativeAlgebraNotes.SquareZeroLift
open scoped CategoryTheory

section Cone

universe r k j
variable {R : Type r} [CommRing R] [HasDerivedCategory.{j} (ModuleCat.{k} R)]
  {X Y M : ModuleCat.{k} R}

/-- The two-term cochain complex with differential from degree -1 to degree 0. -/
abbrev twoTermComplex (d : X ⟶ Y) : CochainComplex (ModuleCat.{k} R) ℤ :=
  HomologicalComplex.double d (i₀ := -1) (i₁ := 0) (by decide)

abbrev degreeZeroMap (d : X ⟶ Y) := (CochainComplex.singleFunctor _ 0).map d

/-- The derived triangle of the map from X in degree zero to Y in degree zero. -/
abbrev coneTriangle (d : X ⟶ Y) : Triangle (DerivedCategory (ModuleCat.{k} R)) :=
  DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (degreeZeroMap d))

/-- Shift the map between degree zero complexes by one. -/
abbrev shiftedSingleMap (f : X ⟶ M) :=
  ((DerivedCategory.singleFunctor (ModuleCat.{k} R) 0).map f)⟦(1 : ℤ)⟧'

universe i h

/-- Transport maps along the canonical equivalences of modules with their universe lifts. -/
def liftHomEquiv {U : Type i} {V : Type h}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    {X Y : ModuleCat.{k} R} (a : X ≃ₗ[R] U) (b : Y ≃ₗ[R] V) :
    (U →ₗ[R] V) ≃ₗ[R] (X ⟶ Y) :=
  (LinearEquiv.arrowCongr a.symm b.symm).trans
    (ModuleCat.homLinearEquiv (R := R) (S := R) (M := X) (N := Y)).symm

end Cone

section Presentation

universe u v w t n k
variable {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
  [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup N] [Module B N] {e : BaseExtension A' A} (p : Presentation e B σ)

-- The lifts let all three modules lie in the same category, even when the original data
-- inhabit different universes.
abbrev conormalObject : ModuleCat.{max u w t n} B :=
  ModuleCat.of B (ULift.{max u w t n} p.BarConormal)

abbrev differentialObject : ModuleCat.{max u w t n} B :=
  ModuleCat.of B (ULift.{max u w t n} p.barExtension.CotangentSpace)

abbrev coefficientObject (B : Type w) [CommRing B] (N : Type n)
    [AddCommGroup N] [Module B N] : ModuleCat.{max w n k} B :=
  ModuleCat.of B (ULift.{max w n k} N)

def conormalHomEquiv : (p.BarConormal →ₗ[B] N) ≃ₗ[B]
    (conormalObject.{u,v,w,t,n} p ⟶ coefficientObject.{w,n,max u t} B N) :=
  liftHomEquiv ULift.moduleEquiv ULift.moduleEquiv

def differentialHomEquiv : (p.barExtension.CotangentSpace →ₗ[B] N) ≃ₗ[B]
    (differentialObject.{u,v,w,t,n} p ⟶ coefficientObject.{w,n,max u t} B N) :=
  liftHomEquiv ULift.moduleEquiv ULift.moduleEquiv

/-- The differential of the reduced conormal complex, bundled as a module morphism. -/
abbrev conormalDifferential :
    conormalObject.{u,v,w,t,n} p ⟶ differentialObject.{u,v,w,t,n} p :=
  liftHomEquiv ULift.moduleEquiv ULift.moduleEquiv p.barExtension.cotangentComplex

/-- The first Ext in the derived category is a morphism to the shifted degree-zero coefficient
complex. The equivalence sends a conormal map to its pullback along the third arrow of the
standard cone triangle. -/
def DerivedExtComparison : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{max u w t n} B)
  let d := conormalDifferential.{u,v,w,t,n} p
  let T := coneTriangle d
  let M := coefficientObject.{w,n,max u t} B N
  ∃ i : twoTermComplex d ≅ CochainComplex.mappingCone (degreeZeroMap d),
    ∃ E : SquareZeroLiftTorsor.T1 p N ≃ₗ[B]
        (DerivedCategory.Q.obj (twoTermComplex d) ⟶
          ((DerivedCategory.singleFunctor _ 0).obj M)⟦(1 : ℤ)⟧),
      ∀ g : p.BarConormal →ₗ[B] N,
        E ((SquareZeroLiftTorsor.conormalRestriction p N).range.mkQ g) =
          DerivedCategory.Q.map i.hom ≫ T.mor₃ ≫ shiftedSingleMap (conormalHomEquiv p g)

def derivedExtType : Prop :=
  ∀ {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
    [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
    (p : Presentation e B σ),
    DerivedExtComparison p (N := N)

end Presentation

end Specs.CommutativeAlgebraNotes.SquareZeroLiftAutomorphismsAndExt
