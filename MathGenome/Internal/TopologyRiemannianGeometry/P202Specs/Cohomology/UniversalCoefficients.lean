import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.UniversalCoefficientsHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.UniversalCoefficientsCohomology

/-! Singular universal coefficients over a PID, paper.tex 1998–2038.
The two upstream Specs use the fixed ordinary absolute and relative complexes,
standard coefficient actions, and genuine induced Tor/Ext maps. This module
assembles their natural split sequences and the full-dual field conclusion.
All singular chains have finite support; the cochains are unrestricted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
namespace P202Specs.UniversalCoefficients
universe u v w t
open P202Specs.SingularChains P202Specs.RelativeSingularChains
namespace Algebraic
export P103.Specs.Ch10.Complexes
  (cycles boundaries cycleBoundaries Homology homologyClass cyclesMap homologyMap)
end Algebraic

variable (R : Type u) [CommRing R]
variable (A : Type v) [AddCommGroup A] [Module R A]

/-- Reuse the canonical unrestricted dual and evaluation from the
cohomological UCT interface. The field theorem concerns this same right arrow. -/
abbrev dualChain (K : ChainComplex (ModuleCat.{t} R) ℤ) :=
  P202Specs.UniversalCoefficientsCohomology.dualChain R A K

abbrev quotientHomologyEquiv {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{t} R) c) (n : ι) :
    K.homology n ≃ₗ[R] Algebraic.Homology K n :=
  P202Specs.UniversalCoefficientsCohomology.quotientHomologyEquiv R K n

abbrev cycleEvaluation (K : ChainComplex (ModuleCat.{t} R) ℤ) (n : ℤ) :
    Algebraic.cycles (dualChain R A K) n →ₗ[R] (Algebraic.Homology K n →ₗ[R] A) :=
  P202Specs.UniversalCoefficientsCohomology.cycleEvaluation R A K n

abbrev quotientEvaluation (K : ChainComplex (ModuleCat.{t} R) ℤ) (n : ℤ) :
    Algebraic.Homology (dualChain R A K) n →ₗ[R] (Algebraic.Homology K n →ₗ[R] A) :=
  P202Specs.UniversalCoefficientsCohomology.quotientEvaluation R A K n

abbrev evaluation (K : ChainComplex (ModuleCat.{t} R) ℤ) (n : ℤ) :
    (dualChain R A K).homology n →ₗ[R] (K.homology n →ₗ[R] A) :=
  P202Specs.UniversalCoefficientsCohomology.evaluation R A K n

abbrev cycleClass {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{t} R) c) (n : ι)
    (z : Algebraic.cycles K n) : K.homology n :=
  P202Specs.UniversalCoefficientsCohomology.cycleClass R K n z

namespace Expected

def evaluationFormula : Prop :=
  ∀ (K : ChainComplex (ModuleCat.{t} R) ℤ) (n : ℤ)
    (a : Algebraic.cycles (dualChain R A K) n) (z : Algebraic.cycles K n),
    evaluation R A K n (cycleClass R (dualChain R A K) n a) (cycleClass R K n z) =
      (show K.X n →ₗ[R] A from a.val) z.val

def ordinaryFree : Prop :=
  ∀ (X : TopCat.{w}) (n : ℕ), Module.Free R ((complex R R X).X n)

def relativeFree : Prop :=
  ∀ (P : Pair.{w}) (n : ℕ), Module.Free R ((nonnegative R R P).X n)

def integerFree : Prop :=
  (∀ (X : TopCat.{w}) (n : ℤ), Module.Free R ((ordinaryComplex R R X).X n)) ∧
  (∀ (P : Pair.{w}) (n : ℤ), Module.Free R ((ordinary R R P).X n))

def pidFree [IsDomain R] [IsPrincipalIdealRing R] : Prop :=
  (∀ (X : TopCat.{w}) (n : ℕ),
    Module.Free R (Algebraic.cycles (complex R R X) n) ∧
    Module.Free R (Algebraic.boundaries (complex R R X) n)) ∧
  (∀ (P : Pair.{w}) (n : ℕ),
    Module.Free R (Algebraic.cycles (nonnegative R R P) n) ∧
    Module.Free R (Algebraic.boundaries (nonnegative R R P) n))

def projectiveHypotheses [IsDomain R] [IsPrincipalIdealRing R] : Prop :=
  (∀ X : TopCat.{w},
    P103.Specs.Ch11.UniversalCoefficientsCohomology.ProjectiveTermsAndBoundaries
      (complex R R X)) ∧
  (∀ P : Pair.{w},
    P103.Specs.Ch11.UniversalCoefficientsCohomology.ProjectiveTermsAndBoundaries
      (nonnegative R R P))

end Expected

/-- The field conclusion, on the fixed absolute and relative cohomology objects,
uses the full linear dual of the homology module. -/
def fieldDuality_type : Prop :=
  ∀ (K : Type u) [Field K],
    (∀ (X : TopCat.{w}) (n : ℕ),
      Function.Bijective (evaluation K K (ordinaryComplex K K X) (n : ℤ))) ∧
    (∀ (P : Pair.{w}) (n : ℕ),
      Function.Bijective (evaluation K K (ordinary K K P) (n : ℤ)))

/-! Full expected types for the freeness and evaluation declarations. -/
def ordinary_free_type : Prop :=
  ∀ (R : Type u) [CommRing R], Expected.ordinaryFree.{u,w} R

def relative_free_type : Prop :=
  ∀ (R : Type u) [CommRing R], Expected.relativeFree.{u,w} R

def integer_free_type : Prop :=
  ∀ (R : Type u) [CommRing R], Expected.integerFree.{u,w} R

def pid_free_type : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R],
    Expected.pidFree.{u,w} R

def projective_hypotheses_type : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R],
    Expected.projectiveHypotheses.{u,w} R

def evaluation_formula_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    Expected.evaluationFormula.{u,v,t} R A

def quotientEvaluation_bijective_type : Prop :=
  ∀ (K : Type u) [Field K] (C : ChainComplex (ModuleCat.{t} K) ℤ) (n : ℤ),
    Function.Bijective (quotientEvaluation K K C n)

def evaluation_bijective_type : Prop :=
  ∀ (K : Type u) [Field K] (C : ChainComplex (ModuleCat.{t} K) ℤ) (n : ℤ),
    Function.Bijective (evaluation K K C n)

namespace CohomologyNaturality
open P202Specs.UniversalCoefficientsCohomology

/-- The Ext square for specified chain and coefficient maps, with the
normalized arrows of the actual singular cohomological sequence. -/
def NaturalOn (B : Type v) [AddCommGroup B] [Module R B]
    {C D : ChainComplex (ModuleCat.{t} R) ℤ} (f : D ⟶ C) (g : A →ₗ[R] B) : Prop :=
  ∀ (hC : C.d 0 (-1) = 0) (hD : D.d 0 (-1) = 0) (n : ℕ)
    (α : actualExt R A C n →ₗ[R] (dualChain R A C).homology ((n+1 : ℕ) : ℤ))
    (α' : actualExt R B D n →ₗ[R] (dualChain R B D).homology ((n+1 : ℕ) : ℤ)),
    ActualEdge R A C hC n α → ActualEdge R B D hD n α' →
    ∀ x, HomologicalComplex.homologyMap (dualMap R A f B g) ((n+1 : ℕ) : ℤ) (α x) =
      α' (AlgebraicExt.extMapLinear R 1 (HomologicalComplex.homologyMap f n)
        (ModuleCat.ofHom g) x)

/-- At degree zero the Ext domain is zero. This records the same naturality
square using the actual Ext object of H_(-1). -/
def ZeroNaturalOn (B : Type v) [AddCommGroup B] [Module R B]
    {C D : ChainComplex (ModuleCat.{t} R) ℤ} (f : D ⟶ C) (g : A →ₗ[R] B) : Prop :=
  ∀ (α : actualExt R A C (-1) →ₗ[R] (dualChain R A C).homology 0)
    (α' : actualExt R B D (-1) →ₗ[R] (dualChain R B D).homology 0) x,
    HomologicalComplex.homologyMap (dualMap R A f B g) 0 (α x) =
      α' (AlgebraicExt.extMapLinear R 1 (HomologicalComplex.homologyMap f (-1))
        (ModuleCat.ofHom g) x)

/-- Naturality of the evaluation arrow, in every nonnegative degree. -/
def EvaluationNaturalOn (B : Type v) [AddCommGroup B] [Module R B]
    {C D : ChainComplex (ModuleCat.{t} R) ℤ} (f : D ⟶ C) (g : A →ₗ[R] B) : Prop :=
  ∀ (n : ℕ) (a : (dualChain R A C).homology (n : ℤ)) (z : D.homology (n : ℤ)),
    P202Specs.UniversalCoefficients.evaluation R B D (n : ℤ)
      (HomologicalComplex.homologyMap (dualMap R A f B g) (n : ℤ) a) z =
        g (P202Specs.UniversalCoefficients.evaluation R A C (n : ℤ) a
          (HomologicalComplex.homologyMap f (n : ℤ) z))

/-- Both naturality squares in all nonnegative degrees. -/
def Squares (B : Type v) [AddCommGroup B] [Module R B]
    {C D : ChainComplex (ModuleCat.{t} R) ℤ} (f : D ⟶ C) (g : A →ₗ[R] B) : Prop :=
  NaturalOn R A B f g ∧ ZeroNaturalOn R A B f g ∧ EvaluationNaturalOn R A B f g

end CohomologyNaturality

/-- Both cohomological naturality squares for every continuous map and every
map of subspace pairs, simultaneously with every coefficient homomorphism.
The freeness hypotheses of the algebraic theorem have been discharged, and
degree zero uses the actual Ext object of H_(-1). -/
def cohomology_natural_type : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (A B : Type v) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B],
    (∀ {X Y : TopCat.{w}} (f : X ⟶ Y) (g : A →ₗ[R] B),
      CohomologyNaturality.Squares R A B ((ordinaryFunctor R R).map f) g) ∧
    (∀ {P Q : Pair.{w}} (f : P ⟶ Q) (g : A →ₗ[R] B),
      CohomologyNaturality.Squares R A B (relativeMap (ordinaryFunctor R R) f) g)

/-- The full T27 conclusion.

The homological family contains R-linear split exact sequences, the cycle-tensor
formula, both naturality squares, and the zero Tor tail. Its `absoluteAll` and
`relativeAll` give the sequences in every n ≥ 0 with H_(n-1) literally the fixed
ordinary homology object.

`singular_uct_type` supplies normalized Ext arrows on those same homology
objects. `cohomology_natural_type` supplies their naturality for every space or pair
map and every coefficient map, with freeness discharged. The stronger generic
`actual_natural_type` also applies to all degreewise free ordinary complexes.
`evaluation_natural_type` gives the Hom square, with no projectivity hypothesis.
`all_degrees_type` includes the R-linear sections and actual Ext endpoint at n=0;
`previousDegree_eq` identifies its index with (n : ℤ)-1. The zero-tail and
evaluation-isomorphism clauses record the endpoint explicitly.

Only the existence of sections is asserted, without naturality of their choice.
The field clause identifies cohomology with the full linear dual. -/
def universal_coefficients_type : Prop :=
  P202Specs.UniversalCoefficientsHomology.topological_uct_type.{u,v,w} ∧
  P202Specs.UniversalCoefficientsCohomology.singular_uct_type.{u,v,w} ∧
  P202Specs.UniversalCoefficientsCohomology.all_degrees_type.{u,v,w} ∧
  P202Specs.UniversalCoefficientsCohomology.actual_natural_type.{u,v,max u w} ∧
  P202Specs.UniversalCoefficientsCohomology.evaluation_natural_type.{u,v,max u w} ∧
  P202Specs.UniversalCoefficientsCohomology.zero_tail_type.{u,v,w} ∧
  P202Specs.UniversalCoefficientsCohomology.topological_zero_type.{u,v,w} ∧
  fieldDuality_type.{u,w} ∧
  cohomology_natural_type.{u,v,w}

end P202Specs.UniversalCoefficients
