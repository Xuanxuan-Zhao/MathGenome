import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.Pairs
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.Complexes
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.UniversalCoefficientsCohomology
import Mathlib.RingTheory.PrincipalIdealDomain
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtTorDefinitions
import Mathlib.Algebra.Homology.Embedding.Restriction

/-! Cohomological singular UCT, paper.tex 1998–2038. Ordinary and relative
chains are the fixed upstream complexes. Cochains are unrestricted R-linear
functionals. The natural grading, scalar and Ext adapters preserve representatives;
`ActualSplit` uses Ext of the actual categorical homology object. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
namespace P202Specs.UniversalCoefficientsCohomology
universe u v w t
open P202Specs.SingularChains P202Specs.RelativeSingularChains
namespace Algebraic
export P103.Specs.Ch10.Complexes
  (cycles boundaries cycleBoundaries Homology homologyClass cyclesMap homologyMap)
end Algebraic

variable (R : Type u) [CommRing R]
variable (A : Type v) [AddCommGroup A] [Module R A]

abbrev dualChain (K : ChainComplex (ModuleCat.{t} R) ℤ) :=
  (P202Specs.CohomologyPairs.dualComplexFunctor R A (ComplexShape.down ℤ)).obj (op K)

/-- The categorical quotient homology agrees with the explicit quotient of
cycles by boundaries used by P103. -/
def quotientHomologyEquiv {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{t} R) c) (n : ι) :
    K.homology n ≃ₗ[R] Algebraic.Homology K n := by
  let e := (K.sc n).moduleCatHomologyIso.toLinearEquiv
  have h : (K.sc n).moduleCatToCycles.range = Algebraic.cycleBoundaries K n := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  exact e.trans (Submodule.quotEquivOfEq _ _ h)

/-- A cocycle evaluates on a homology class by applying its functional to a
cycle. It descends because cocycles annihilate all incoming boundaries. -/
def cycleEvaluation (K : ChainComplex (ModuleCat.{t} R) ℤ) (n : ℤ) :
    Algebraic.cycles (dualChain R A K) n →ₗ[R] (Algebraic.Homology K n →ₗ[R] A) where
  toFun a := (Algebraic.cycleBoundaries K n).liftQ
    ((show K.X n →ₗ[R] A from a.val).comp (Algebraic.cycles K n).subtype) (by
      rintro z ⟨b, hb⟩
      change (show K.X n →ₗ[R] A from a.val) z.val = 0
      change (K.d ((ComplexShape.down ℤ).prev n) n).hom b = z.val at hb
      rw [← hb]
      have ha := congrArg (fun f : K.X ((ComplexShape.down ℤ).prev n) →ₗ[R] A => f b) a.property
      exact ha)
  map_add' a b := by
    apply (Algebraic.cycleBoundaries K n).quot_hom_ext
    intro z
    rfl
  map_smul' r a := by
    apply (Algebraic.cycleBoundaries K n).quot_hom_ext
    intro z
    rfl

/-- The canonical evaluation map on the explicit cohomology quotient. -/
def quotientEvaluation (K : ChainComplex (ModuleCat.{t} R) ℤ) (n : ℤ) :
    Algebraic.Homology (dualChain R A K) n →ₗ[R] (Algebraic.Homology K n →ₗ[R] A) :=
  (Algebraic.cycleBoundaries (dualChain R A K) n).liftQ (cycleEvaluation R A K n) (by
    rintro a ⟨b, hb⟩
    apply (Algebraic.cycleBoundaries K n).quot_hom_ext
    intro z
    change (show K.X n →ₗ[R] A from a.val) z.val = 0
    change ((dualChain R A K).d ((ComplexShape.up ℤ).prev n) n).hom b = a.val at hb
    rw [← hb]
    change (show K.X ((ComplexShape.down ℤ).next n) →ₗ[R] A from b)
      ((K.d n ((ComplexShape.down ℤ).next n)) z.val) = 0
    rw [z.property, map_zero])

/-- Evaluation on the actual categorical homology and cohomology modules. -/
def evaluation (K : ChainComplex (ModuleCat.{t} R) ℤ) (n : ℤ) :
    (dualChain R A K).homology n →ₗ[R] (K.homology n →ₗ[R] A) :=
  (LinearMap.lcomp R A (quotientHomologyEquiv R K n).toLinearMap).comp
    ((quotientEvaluation R A K n).comp
      (quotientHomologyEquiv R (dualChain R A K) n).toLinearMap)

/-- A specified cycle gives its class in the categorical homology object. -/
def cycleClass {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{t} R) c) (n : ι)
    (z : Algebraic.cycles K n) : K.homology n :=
  (quotientHomologyEquiv R K n).symm (Algebraic.homologyClass K n z)


/-- Truncation at degree zero, used only for ordinary complexes. -/
def nonnegativeEmbedding :
    (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) :=
  ComplexShape.Embedding.mk' _ _ (fun n => (n : ℤ))
    (by intros i j h; change (i : ℤ) = (j : ℤ) at h; exact_mod_cast h)
    (by intros; change _ + 1 = _ ↔ _ + 1 = _; omega)

instance : nonnegativeEmbedding.IsRelIff := by
  unfold nonnegativeEmbedding
  infer_instance

abbrev trunc (C : ChainComplex (ModuleCat.{t} R) ℤ) :=
  C.restriction nonnegativeEmbedding

theorem trunc_cycles (C : ChainComplex (ModuleCat.{t} R) ℤ)
    (h0 : C.d 0 (-1) = 0) (n : ℕ) :
    Algebraic.cycles (trunc R C) n = Algebraic.cycles C (n : ℤ) := by
  cases n with
  | zero =>
    unfold Algebraic.cycles
    rw [ChainComplex.next_nat_zero, ChainComplex.next ℤ]
    change (C.d 0 0).hom.ker = (C.d 0 (-1)).hom.ker
    rw [C.shape 0 0 (by decide), h0]
    simp only [ModuleCat.hom_zero, LinearMap.ker_zero]
  | succ n =>
    unfold Algebraic.cycles
    have hh : (ComplexShape.down ℤ).next ((n+1 : ℕ) : ℤ) = (n : ℤ) := by
      rw [ChainComplex.next]
      omega
    rw [ChainComplex.next_nat_succ, hh]
    rfl

theorem trunc_boundaries (C : ChainComplex (ModuleCat.{t} R) ℤ) (n : ℕ) :
    Algebraic.boundaries (trunc R C) n = Algebraic.boundaries C (n : ℤ) := by
  unfold Algebraic.boundaries
  rw [ChainComplex.prev ℕ, ChainComplex.prev ℤ]
  change (C.d (n+1 : ℕ) (n : ℤ)).hom.range =
    (C.d ((n : ℤ)+1) (n : ℤ)).hom.range
  simp

/-- The cycles are identified by the identity on the actual chain module. -/
def truncCyclesEquiv (C : ChainComplex (ModuleCat.{t} R) ℤ)
    (h0 : C.d 0 (-1) = 0) (n : ℕ) :
    Algebraic.cycles (trunc R C) n ≃ₗ[R] Algebraic.cycles C (n : ℤ) :=
  LinearEquiv.ofEq _ _ (trunc_cycles R C h0 n)

/-- The truncation adapter on the explicit homology quotients. -/
def truncHomologyEquiv (C : ChainComplex (ModuleCat.{t} R) ℤ)
    (h0 : C.d 0 (-1) = 0) (n : ℕ) :
    Algebraic.Homology (trunc R C) n ≃ₗ[R] Algebraic.Homology C (n : ℤ) :=
  Submodule.Quotient.equiv _ _ (truncCyclesEquiv R C h0 n) (by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change x.val ∈ Algebraic.boundaries C (n : ℤ)
      rw [← trunc_boundaries R C n]
      exact hx
    · intro hz
      refine ⟨(truncCyclesEquiv R C h0 n).symm z, ?_, by simp⟩
      change z.val ∈ Algebraic.boundaries (trunc R C) n
      rw [trunc_boundaries R C n]
      exact hz)

/-- R-linear Hom in natural degrees, before taking cohomology. -/
abbrev dualNat (C : ChainComplex (ModuleCat.{t} R) ℕ) :=
  (P202Specs.CohomologyPairs.dualComplexFunctor R A (ComplexShape.down ℕ)).obj (op C)

/-- P103's integer-linear Hom complex has the same additive cohomology
quotient as the R-linear Hom complex. -/
def homAddEquiv (C : ChainComplex (ModuleCat.{t} R) ℕ) (n : ℕ) :
    Algebraic.Homology (P103.Specs.Ch11.ExtTorDefinitions.homComplex C A) n ≃+
      Algebraic.Homology (dualNat R A C) n :=
  AddEquiv.refl _


/-- The P103 coefficient-induced R-action is the standard pointwise action,
verified on every cocycle representative. -/
def homLinearEquiv (C : ChainComplex (ModuleCat.{t} R) ℕ) (n : ℕ) :
    letI := P103.Specs.Ch11.UniversalCoefficientsCohomology.cohomologyModule
      C (ModuleCat.of R A) n
    Algebraic.Homology (P103.Specs.Ch11.ExtTorDefinitions.homComplex C A) n ≃ₗ[R]
      Algebraic.Homology (dualNat R A C) n := by
  letI := P103.Specs.Ch11.UniversalCoefficientsCohomology.cohomologyModule
    C (ModuleCat.of R A) n
  exact { homAddEquiv R A C n with
    map_smul' := by
      intro r x
      obtain ⟨z, rfl⟩ :=
        (Algebraic.cycleBoundaries (P103.Specs.Ch11.ExtTorDefinitions.homComplex C A) n).mkQ_surjective x
      rfl }

theorem dual_trunc_cycles (C : ChainComplex (ModuleCat.{t} R) ℤ) (n : ℕ) :
    Algebraic.cycles (dualNat R A (trunc R C)) n =
      Algebraic.cycles (dualChain R A C) (n : ℤ) := by
  unfold Algebraic.cycles
  rw [show (ComplexShape.down ℕ).symm.next n = n+1 from ChainComplex.prev ℕ n,
    show (ComplexShape.down ℤ).symm.next (n : ℤ) = (n : ℤ)+1 from ChainComplex.prev ℤ n]
  change LinearMap.ker _ = LinearMap.ker _
  congr 1

theorem dual_trunc_boundaries (C : ChainComplex (ModuleCat.{t} R) ℤ)
    (h0 : C.d 0 (-1) = 0) (n : ℕ) :
    Algebraic.boundaries (dualNat R A (trunc R C)) n =
      Algebraic.boundaries (dualChain R A C) (n : ℤ) := by
  cases n with
  | zero =>
    unfold Algebraic.boundaries
    rw [show (ComplexShape.down ℕ).symm.prev 0 = 0 from ChainComplex.next_nat_zero]
    change ((dualNat R A (trunc R C)).d 0 0).hom.range =
      ((dualChain R A C).d ((ComplexShape.down ℤ).symm.prev 0) 0).hom.range
    rw [show (ComplexShape.down ℤ).symm.prev (0 : ℤ) = -1 from by
        change (ComplexShape.down ℤ).next 0 = -1; rw [ChainComplex.next]; rfl]
    have h1 : (dualNat R A (trunc R C)).d 0 0 = 0 :=
      HomologicalComplex.shape _ _ _ (by change ¬ ((0 : ℕ)+1 = 0); omega)
    have h2 : (dualChain R A C).d (-1) 0 = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change C.X (-1) →ₗ[R] A at a
      apply LinearMap.ext
      intro x
      change a (C.d 0 (-1) x) = 0
      rw [h0]
      exact a.map_zero
    rw [h1, h2]
    simp only [ModuleCat.hom_zero, LinearMap.range_zero]
  | succ n =>
    unfold Algebraic.boundaries
    have hh : (ComplexShape.down ℤ).symm.prev ((n+1 : ℕ) : ℤ) = (n : ℤ) := by
      change (ComplexShape.down ℤ).next ((n+1 : ℕ) : ℤ) = (n : ℤ)
      rw [ChainComplex.next]
      omega
    rw [show (ComplexShape.down ℕ).symm.prev (n+1) = n from
      ChainComplex.next_nat_succ n, hh]
    rfl

def dualTruncCyclesEquiv (C : ChainComplex (ModuleCat.{t} R) ℤ) (n : ℕ) :
    Algebraic.cycles (dualNat R A (trunc R C)) n ≃ₗ[R]
      Algebraic.cycles (dualChain R A C) (n : ℤ) :=
  LinearEquiv.ofEq _ _ (dual_trunc_cycles R A C n)

/-- The Hom adapter includes the differential and the degree-zero endpoint. -/
def dualTruncHomologyEquiv (C : ChainComplex (ModuleCat.{t} R) ℤ)
    (h0 : C.d 0 (-1) = 0) (n : ℕ) :
    Algebraic.Homology (dualNat R A (trunc R C)) n ≃ₗ[R]
      Algebraic.Homology (dualChain R A C) (n : ℤ) :=
  Submodule.Quotient.equiv _ _ (dualTruncCyclesEquiv R A C n) (by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change x.val ∈ Algebraic.boundaries (dualChain R A C) (n : ℤ)
      rw [← dual_trunc_boundaries R A C h0 n]
      exact hx
    · intro hz
      refine ⟨(dualTruncCyclesEquiv R A C n).symm z, ?_,
        (dualTruncCyclesEquiv R A C n).apply_symm_apply z⟩
      change z.val ∈ Algebraic.boundaries (dualNat R A (trunc R C)) n
      rw [dual_trunc_boundaries R A C h0 n]
      exact hz)

/-- Homology of the truncated ordinary chains, on the actual categorical object. -/
def chainHomologyEquiv (C : ChainComplex (ModuleCat.{t} R) ℤ)
    (h0 : C.d 0 (-1) = 0) (n : ℕ) :
    Algebraic.Homology (trunc R C) n ≃ₗ[R] C.homology (n : ℤ) :=
  (truncHomologyEquiv R C h0 n).trans (quotientHomologyEquiv R C (n : ℤ)).symm

/-- The actual unrestricted cohomology is identified with P103's Hom model,
using its standard coefficient scalar action. -/
def cohomologyEquiv (C : ChainComplex (ModuleCat.{t} R) ℤ)
    (h0 : C.d 0 (-1) = 0) (n : ℕ) :
    letI := P103.Specs.Ch11.UniversalCoefficientsCohomology.cohomologyModule
      (trunc R C) (ModuleCat.of R A) n
    Algebraic.Homology (P103.Specs.Ch11.ExtTorDefinitions.homComplex (trunc R C) A) n ≃ₗ[R]
      (dualChain R A C).homology (n : ℤ) :=
  (homLinearEquiv R A (trunc R C) n).trans
    ((dualTruncHomologyEquiv R A C h0 n).trans
      (quotientHomologyEquiv R (dualChain R A C) (n : ℤ)).symm)


namespace Q
export P103.Specs.Ch11.UniversalCoefficientsCohomology
  (ProjectiveTermsAndBoundaries IsRestriction IsExtCoker CokerSequence BoundaryCoker
   cohomologyModule)
end Q
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch10.Comparison

/-- The Ext term is computed by a projective resolution of the explicit
homology module. `chainHomologyEquiv` identifies that module with the fixed
categorical homology object. The edge is normalized by the genuine Ext connector. -/
def SplitSequence (C : ChainComplex (ModuleCat.{t} R) ℤ)
    (h0 : C.d 0 (-1) = 0) (n : ℕ) (E : ExtMaps.{u,t,v} R 1)
    (N : LeftResolution R (Algebraic.Homology (trunc R C) n)) (hN : N.IsProjective) : Prop :=
  letI := extModule E (A := ModuleCat.of R (Algebraic.Homology (trunc R C) n)) ⟨N,hN⟩ (ModuleCat.of R A)
  letI := Q.cohomologyModule (trunc R C) (ModuleCat.of R A) (n+1)
  ∃ (α : ExtWith N A 1 →ₗ[R] (dualChain R A C).homology ((n+1 : ℕ) : ℤ))
    (σ : (C.homology ((n+1 : ℕ) : ℤ) →ₗ[R] A) →ₗ[R]
      (dualChain R A C).homology ((n+1 : ℕ) : ℤ)),
    Function.Injective α ∧ Function.Exact α (evaluation R A C ((n+1 : ℕ) : ℤ)) ∧
    Function.Surjective (evaluation R A C ((n+1 : ℕ) : ℤ)) ∧
    (evaluation R A C ((n+1 : ℕ) : ℤ)).comp σ = LinearMap.id ∧
    ∃ (e : ExtWith N A 1 ≃ₗ[ℤ] Q.BoundaryCoker (trunc R C) (ModuleCat.of R A) n)
      (a : Q.BoundaryCoker (trunc R C) (ModuleCat.of R A) n →ₗ[ℤ]
        Algebraic.Homology (homComplex (trunc R C) A) (n+1))
      (b : Algebraic.Homology (homComplex (trunc R C) A) (n+1) →ₗ[ℤ]
        (Algebraic.Homology (trunc R C) (n+1) →ₗ[R] A)),
      Q.IsExtCoker (trunc R C) (ModuleCat.of R A) n N e ∧
      Q.CokerSequence (trunc R C) (ModuleCat.of R A) n a b ∧
      ∀ x, α x = cohomologyEquiv R A C h0 (n+1) (a (e x))

namespace Expected

def genericSplit [IsDomain R] [IsPrincipalIdealRing R] : Prop :=
  ∀ (C : ChainComplex (ModuleCat.{t} R) ℤ) (h0 : C.d 0 (-1) = 0),
    (∀ n : ℕ, Module.Free R (C.X (n : ℤ))) →
    ∀ (n : ℕ) (E : ExtMaps.{u,t,v} R 1)
      (N : LeftResolution R (Algebraic.Homology (trunc R C) n)) (hN : N.IsProjective),
      SplitSequence R A C h0 n E N hN

def degreeZero : Prop :=
  ∀ (C : ChainComplex (ModuleCat.{t} R) ℤ) (_h0 : C.d 0 (-1) = 0),
    Function.Bijective (evaluation R A C 0)

def ordinaryFree : Prop :=
  ∀ (X : TopCat.{w}) (n : ℕ), Module.Free R ((ordinaryComplex R R X).X (n : ℤ))

def relativeFree : Prop :=
  ∀ (P : Pair.{w}) (n : ℕ), Module.Free R ((ordinary R R P).X (n : ℤ))

def ordinaryZero : Prop :=
  ∀ (X : TopCat.{w}), (ordinaryComplex R R X).d 0 (-1) = 0

def relativeZero : Prop :=
  ∀ (P : Pair.{w}), (ordinary R R P).d 0 (-1) = 0

end Expected


/-- Positive-degree singular UCT, on the actual absolute and relative
cohomology objects, including an R-linear section. -/
def topological_split_type : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (A : Type v) [AddCommGroup A] [Module R A],
    (∀ X : TopCat.{w}, ∃ h0 : (ordinaryComplex R R X).d 0 (-1) = 0,
      ∀ (n : ℕ) (E : ExtMaps.{u,max u w,v} R 1)
        (N : LeftResolution R (Algebraic.Homology (trunc R (ordinaryComplex R R X)) n))
        (hN : N.IsProjective), SplitSequence R A (ordinaryComplex R R X) h0 n E N hN) ∧
    (∀ P : Pair.{w}, ∃ h0 : (ordinary R R P).d 0 (-1) = 0,
      ∀ (n : ℕ) (E : ExtMaps.{u,max u w,v} R 1)
        (N : LeftResolution R (Algebraic.Homology (trunc R (ordinary R R P)) n))
        (hN : N.IsProjective), SplitSequence R A (ordinary R R P) h0 n E N hN)

/-- The complete degree-zero evaluation conclusion on ordinary singular and
relative cohomology. No connectedness, nonemptiness, or PID hypothesis is needed. -/
def topological_zero_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    (∀ X : TopCat.{w}, Function.Bijective (evaluation R A (ordinaryComplex R R X) 0)) ∧
    (∀ P : Pair.{w}, Function.Bijective (evaluation R A (ordinary R R P) 0))


/-- Change coefficients by postcomposition, for the unrestricted linear dual. -/
def coefficientMap (B : Type v) [AddCommGroup B] [Module R B]
    (C : ChainComplex (ModuleCat.{t} R) ℤ) (g : A →ₗ[R] B) :
    dualChain R A C ⟶ dualChain R B C where
  f n := ModuleCat.ofHom {
    toFun := fun a => g.comp a
    map_add' := by
      intro a b
      ext x
      exact g.map_add (a x) (b x)
    map_smul' := by
      intro r a
      ext x
      exact g.map_smul r (a x) }
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro x
    rfl

/-- Simultaneous pullback of the space and pushforward of coefficients. -/
def dualMap {C D : ChainComplex (ModuleCat.{t} R) ℤ} (f : D ⟶ C)
    (B : Type v) [AddCommGroup B] [Module R B] (g : A →ₗ[R] B) :
    dualChain R A C ⟶ dualChain R B D :=
  (P202Specs.CohomologyPairs.dualComplexFunctor R A (ComplexShape.down ℤ)).map f.op ≫
    coefficientMap R A B D g

def evaluation_natural_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A B : Type v) [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    {C D : ChainComplex (ModuleCat.{t} R) ℤ} (f : D ⟶ C) (g : A →ₗ[R] B)
    (n : ℤ) (a : (dualChain R A C).homology n) (z : D.homology n),
    evaluation R B D n (HomologicalComplex.homologyMap (dualMap R A f B g) n a) z =
      g (evaluation R A C n a (HomologicalComplex.homologyMap f n z))

/-- Naturality of the normalized Ext edge for genuine induced Ext maps.
Both homology and cohomology are connected to the fixed objects by the
representative-preserving natural adapters. -/
def edge_natural_type : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (A B : Type v) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (C D : ChainComplex (ModuleCat.{t} R) ℤ)
    (hC : C.d 0 (-1) = 0) (hD : D.d 0 (-1) = 0),
    (∀ k : ℕ, Module.Free R (C.X (k : ℤ))) →
    (∀ k : ℕ, Module.Free R (D.X (k : ℤ))) →
    ∀ (f : D ⟶ C) (g : A →ₗ[R] B) (n : ℕ) (E : ExtMaps.{u,t,v} R 1)
      (N : LeftResolution R (Algebraic.Homology (trunc R C) n))
      (N' : LeftResolution R (Algebraic.Homology (trunc R D) n))
      (hN : N.IsProjective) (hN' : N'.IsProjective)
      (e : ExtWith N A 1 ≃ₗ[ℤ] Q.BoundaryCoker (trunc R C) (ModuleCat.of R A) n)
      (e' : ExtWith N' B 1 ≃ₗ[ℤ] Q.BoundaryCoker (trunc R D) (ModuleCat.of R B) n)
      (a : Q.BoundaryCoker (trunc R C) (ModuleCat.of R A) n →ₗ[ℤ]
        Algebraic.Homology (homComplex (trunc R C) A) (n+1))
      (b : Algebraic.Homology (homComplex (trunc R C) A) (n+1) →ₗ[ℤ]
        (Algebraic.Homology (trunc R C) (n+1) →ₗ[R] A))
      (a' : Q.BoundaryCoker (trunc R D) (ModuleCat.of R B) n →ₗ[ℤ]
        Algebraic.Homology (homComplex (trunc R D) B) (n+1))
      (b' : Algebraic.Homology (homComplex (trunc R D) B) (n+1) →ₗ[ℤ]
        (Algebraic.Homology (trunc R D) (n+1) →ₗ[R] B)),
      Q.IsExtCoker (trunc R C) (ModuleCat.of R A) n N e →
      Q.IsExtCoker (trunc R D) (ModuleCat.of R B) n N' e' →
      Q.CokerSequence (trunc R C) (ModuleCat.of R A) n a b →
      Q.CokerSequence (trunc R D) (ModuleCat.of R B) n a' b' →
      letI := Q.cohomologyModule (trunc R C) (ModuleCat.of R A) (n+1)
      letI := Q.cohomologyModule (trunc R D) (ModuleCat.of R B) (n+1)
      ∀ x, HomologicalComplex.homologyMap (dualMap R A f B g) ((n+1 : ℕ) : ℤ)
        (cohomologyEquiv R A C hC (n+1) (a (e x))) =
        cohomologyEquiv R B D hD (n+1)
          (a' (e' (E.map ⟨N,hN⟩ ⟨N',hN'⟩
            (ModuleCat.ofHom (Algebraic.homologyMap
              (HomologicalComplex.restrictionMap f nonnegativeEmbedding) n))
            (ModuleCat.ofHom g) x)))


namespace AlgebraicExt
export P103.Ch11.ExtTorDefinitions (Ext extMap extMapLinear resolutionFamily extMaps)
end AlgebraicExt

instance canonicalExtModule (V : ModuleCat.{t} R) :
    Module R (AlgebraicExt.Ext R V (ModuleCat.of R A) 1) :=
  P103.Ch11.ExtTorDefinitions.canonicalExtModule R V (ModuleCat.of R A) 1

/-- The genuine Ext functor takes a linear equivalence of first arguments to
an equivalence, with its canonical coefficient scalar actions. -/
def extFirstEquiv {V W : ModuleCat.{t} R} (e : V ≃ₗ[R] W) :
    AlgebraicExt.Ext R W (ModuleCat.of R A) 1 ≃ₗ[R] AlgebraicExt.Ext R V (ModuleCat.of R A) 1 where
  __ := AlgebraicExt.extMapLinear R 1 e.toModuleIso.hom (𝟙 (ModuleCat.of R A))
  invFun := AlgebraicExt.extMapLinear R 1 e.toModuleIso.inv (𝟙 (ModuleCat.of R A))
  left_inv x := by
    have h := (AlgebraicExt.extMaps (R := R) 1).comp
      (AlgebraicExt.resolutionFamily R W) (AlgebraicExt.resolutionFamily R V) (AlgebraicExt.resolutionFamily R W)
      e.toModuleIso.hom e.toModuleIso.inv (𝟙 (ModuleCat.of R A)) (𝟙 (ModuleCat.of R A))
    rw [Iso.inv_hom_id, Category.id_comp, (AlgebraicExt.extMaps (R := R) 1).id] at h
    exact (LinearMap.congr_fun h x).symm
  right_inv x := by
    have h := (AlgebraicExt.extMaps (R := R) 1).comp
      (AlgebraicExt.resolutionFamily R V) (AlgebraicExt.resolutionFamily R W) (AlgebraicExt.resolutionFamily R V)
      e.toModuleIso.inv e.toModuleIso.hom (𝟙 (ModuleCat.of R A)) (𝟙 (ModuleCat.of R A))
    rw [Iso.hom_inv_id, Category.id_comp, (AlgebraicExt.extMaps (R := R) 1).id] at h
    exact (LinearMap.congr_fun h x).symm

/-- A specified Ext model for the actual ordinary homology module. -/
abbrev actualExt (C : ChainComplex (ModuleCat.{t} R) ℤ) (n : ℤ) :=
  AlgebraicExt.Ext R (C.homology n) (ModuleCat.of R A) 1

def extComparison (C : ChainComplex (ModuleCat.{t} R) ℤ)
    (h0 : C.d 0 (-1) = 0) (n : ℕ) :
    actualExt R A C n ≃ₗ[R]
      AlgebraicExt.Ext R (ModuleCat.of R (Algebraic.Homology (trunc R C) n)) (ModuleCat.of R A) 1 :=
  extFirstEquiv R A (V := ModuleCat.of R (Algebraic.Homology (trunc R C) n))
    (W := C.homology n) (chainHomologyEquiv R C h0 n)


/-- The ordinary negative homology and the degree-zero Ext term both vanish. -/
def zero_tail_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    (∀ X : TopCat.{w}, IsZero ((ordinaryComplex R R X).homology (-1)) ∧
      Subsingleton (actualExt R A (ordinaryComplex R R X) (-1))) ∧
    (∀ P : Pair.{w}, IsZero ((ordinary R R P).homology (-1)) ∧
      Subsingleton (actualExt R A (ordinary R R P) (-1)))


/-- Normalization of the left arrow with Ext of the fixed homology object. -/
def ActualEdge (C : ChainComplex (ModuleCat.{t} R) ℤ)
    (h0 : C.d 0 (-1) = 0) (n : ℕ)
    (α : actualExt R A C n →ₗ[R] (dualChain R A C).homology ((n+1 : ℕ) : ℤ)) : Prop :=
  let N := (AlgebraicExt.resolutionFamily R
    (ModuleCat.of R (Algebraic.Homology (trunc R C) n))).val
  letI := Q.cohomologyModule (trunc R C) (ModuleCat.of R A) (n+1)
  ∃ (e : ExtWith N A 1 ≃ₗ[ℤ] Q.BoundaryCoker (trunc R C) (ModuleCat.of R A) n)
    (a : Q.BoundaryCoker (trunc R C) (ModuleCat.of R A) n →ₗ[ℤ]
      Algebraic.Homology (homComplex (trunc R C) A) (n+1))
    (b : Algebraic.Homology (homComplex (trunc R C) A) (n+1) →ₗ[ℤ]
      (Algebraic.Homology (trunc R C) (n+1) →ₗ[R] A)),
    Q.IsExtCoker (trunc R C) (ModuleCat.of R A) n N e ∧
    Q.CokerSequence (trunc R C) (ModuleCat.of R A) n a b ∧
    ∀ x, α x = cohomologyEquiv R A C h0 (n+1) (a (e (extComparison R A C h0 n x)))

/-- A split short exact sequence on the literal fixed homology/cohomology
objects, with the usual Ext coefficient action and prescribed evaluation. -/
def ActualSplit (C : ChainComplex (ModuleCat.{t} R) ℤ)
    (h0 : C.d 0 (-1) = 0) (n : ℕ) : Prop :=
  ∃ (α : actualExt R A C n →ₗ[R] (dualChain R A C).homology ((n+1 : ℕ) : ℤ))
    (σ : (C.homology ((n+1 : ℕ) : ℤ) →ₗ[R] A) →ₗ[R]
      (dualChain R A C).homology ((n+1 : ℕ) : ℤ)),
    Function.Injective α ∧ Function.Exact α (evaluation R A C ((n+1 : ℕ) : ℤ)) ∧
    Function.Surjective (evaluation R A C ((n+1 : ℕ) : ℤ)) ∧
    (evaluation R A C ((n+1 : ℕ) : ℤ)).comp σ = LinearMap.id ∧
    ActualEdge R A C h0 n α

def actual_split_type : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (A : Type v) [AddCommGroup A] [Module R A]
    (C : ChainComplex (ModuleCat.{t} R) ℤ) (h0 : C.d 0 (-1) = 0),
    (∀ k : ℕ, Module.Free R (C.X (k : ℤ))) → ∀ n, ActualSplit R A C h0 n


def actual_natural_type : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (A B : Type v) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (C D : ChainComplex (ModuleCat.{t} R) ℤ)
    (hC : C.d 0 (-1) = 0) (hD : D.d 0 (-1) = 0),
    (∀ k : ℕ, Module.Free R (C.X (k : ℤ))) →
    (∀ k : ℕ, Module.Free R (D.X (k : ℤ))) →
    ∀ (f : D ⟶ C) (g : A →ₗ[R] B) (n : ℕ)
      (α : actualExt R A C n →ₗ[R] (dualChain R A C).homology ((n+1 : ℕ) : ℤ))
      (α' : actualExt R B D n →ₗ[R] (dualChain R B D).homology ((n+1 : ℕ) : ℤ)),
      ActualEdge R A C hC n α → ActualEdge R B D hD n α' →
      ∀ x, HomologicalComplex.homologyMap (dualMap R A f B g) ((n+1 : ℕ) : ℤ) (α x) =
        α' (AlgebraicExt.extMapLinear R 1 (HomologicalComplex.homologyMap f n)
          (ModuleCat.ofHom g) x)


/-- The positive-degree cohomological half of T27 for every space and every
subspace pair. Degree zero is `topological_zero_type` and `zero_tail_type`;
`actual_natural_type` and `evaluation_natural_type` give its two naturality squares.
The section is only asserted to exist for each sequence. -/
def singular_uct_type : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (A : Type v) [AddCommGroup A] [Module R A],
    (∀ X : TopCat.{w}, ∃ h0 : (ordinaryComplex R R X).d 0 (-1) = 0,
      ∀ n, ActualSplit R A (ordinaryComplex R R X) h0 n) ∧
    (∀ P : Pair.{w}, ∃ h0 : (ordinary R R P).d 0 (-1) = 0,
      ∀ n, ActualSplit R A (ordinary R R P) h0 n)

def evaluation_formula_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    (C : ChainComplex (ModuleCat.{t} R) ℤ) (n : ℤ)
    (a : Algebraic.cycles (dualChain R A C) n) (z : Algebraic.cycles C n),
    evaluation R A C n (cycleClass R (dualChain R A C) n a) (cycleClass R C n z) =
      (show C.X n →ₗ[R] A from a.val) z.val

def ordinary_free_type : Prop :=
  ∀ (R : Type u) [CommRing R], Expected.ordinaryFree.{u,w} R

def relative_free_type : Prop :=
  ∀ (R : Type u) [CommRing R], Expected.relativeFree.{u,w} R

/-- The split exact sequence in degree n, including the actual Ext term
of H_(n-1) at the endpoint n = 0. -/
def previousDegree : ℕ → ℤ
  | 0 => -1
  | n+1 => (n : ℤ)

theorem previousDegree_eq (n : ℕ) : previousDegree n = (n : ℤ)-1 := by
  cases n <;> simp only [previousDegree] <;> omega

def SplitExactAt (C : ChainComplex (ModuleCat.{t} R) ℤ) (n : ℕ) : Prop :=
  ∃ (α : actualExt R A C (previousDegree n) →ₗ[R] (dualChain R A C).homology (n : ℤ))
    (σ : (C.homology (n : ℤ) →ₗ[R] A) →ₗ[R] (dualChain R A C).homology (n : ℤ)),
    Function.Injective α ∧ Function.Exact α (evaluation R A C (n : ℤ)) ∧
    Function.Surjective (evaluation R A C (n : ℤ)) ∧
    (evaluation R A C (n : ℤ)).comp σ = LinearMap.id

/-- The cohomological sequence of T27 in every nonnegative degree, for
all spaces and all subspace pairs, with a linear section in each degree. -/
def all_degrees_type : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (A : Type v) [AddCommGroup A] [Module R A],
    (∀ (X : TopCat.{w}) (n : ℕ), SplitExactAt R A (ordinaryComplex R R X) n) ∧
    (∀ (P : Pair.{w}) (n : ℕ), SplitExactAt R A (ordinary R R P) n)

end P202Specs.UniversalCoefficientsCohomology
