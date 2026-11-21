import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.LieHochschildSerre
import Mathlib.Algebra.Category.ModuleCat.Ulift

noncomputable section

open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Complexes

namespace AdvancedHomologicalAlgebra.LieHochschildSerre.Original

universe u v w a b c s t r

attribute [local instance 100] LieRing.ofAssociativeRing
set_option backward.isDefEq.respectTransparency false

section Quotients

variable {R : Type u} [Ring R]
variable {A : CochainComplex (ModuleCat.{s} R) ℕ}
  {B : CochainComplex (ModuleCat.{t} R) ℕ}

/-- Termwise linear maps of complexes can have source and target in different universes. -/
structure CochainMap (A : CochainComplex (ModuleCat.{s} R) ℕ)
    (B : CochainComplex (ModuleCat.{t} R) ℕ) where
  term : ∀ n, A.X n →ₗ[R] B.X n
  comm : ∀ i j x, (B.d i j).hom (term i x) = term j ((A.d i j).hom x)

def CochainMap.onCycles (f : CochainMap A B) (n : ℕ) :
    cycles A n →ₗ[R] cycles B n :=
  ((f.term n).comp (cycles A n).subtype).codRestrict (cycles B n) fun z => by
    change (B.d n ((ComplexShape.up ℕ).next n)).hom (f.term n z.val) = 0
    rw [f.comm]
    exact (congrArg (f.term _) z.property).trans (map_zero _)

def CochainMap.homology (f : CochainMap A B) (n : ℕ) :
    Homology A n →ₗ[R] Homology B n :=
  (cycleBoundaries A n).mapQ (cycleBoundaries B n) (f.onCycles n) <| by
    rintro z ⟨x, hx⟩
    refine ⟨f.term ((ComplexShape.up ℕ).prev n) x, ?_⟩
    change (B.d _ n).hom (f.term _ x) = f.term n z.val
    rw [f.comm]
    exact congrArg (f.term n) hx

def CochainMap.ofHom {B : CochainComplex (ModuleCat.{s} R) ℕ} (f : A ⟶ B) :
    CochainMap A B where
  term n := (f.f n).hom
  comm i j x := congrArg (fun m => m.hom x) (f.comm i j)

def CochainMap.comp {C : CochainComplex (ModuleCat.{r} R) ℕ}
    (g : CochainMap B C) (f : CochainMap A B) : CochainMap A C where
  term n := (g.term n).comp (f.term n)
  comm i j x := by
    change (C.d i j).hom (g.term i (f.term i x)) = g.term j (f.term j ((A.d i j).hom x))
    rw [g.comm, f.comm]

def CochainMap.IsTermEquiv (f : CochainMap A B)
    (e : ∀ n, A.X n ≃ₗ[R] B.X n) : Prop :=
  ∀ n, f.term n = (e n).toLinearMap

theorem CochainMap.homology_class (f : CochainMap A B) (n : ℕ) (z : cycles A n) :
    f.homology n (homologyClass A n z) = homologyClass B n (f.onCycles n z) := rfl

private theorem homology_inverse (f : CochainMap A B) (g : CochainMap B A)
    (h : ∀ n x, g.term n (f.term n x) = x) (n : ℕ) :
    (g.homology n).comp (f.homology n) = LinearMap.id := by
  apply (cycleBoundaries A n).quot_hom_ext
  intro z
  change g.homology n (f.homology n (homologyClass A n z)) = homologyClass A n z
  simp only [CochainMap.homology_class]
  exact congrArg (homologyClass A n) (Subtype.ext (h n z.val))

/-- Commuting termwise equivalences induce equivalences on the actual
quotients of cycles, without forcing the carriers into one universe. -/
def CochainMap.inverse (f : CochainMap A B) (e : ∀ n, A.X n ≃ₗ[R] B.X n)
    (h : f.IsTermEquiv e) : CochainMap B A where
  term n := (e n).symm.toLinearMap
  comm i j x := by
    apply (e j).injective
    change e j ((A.d i j).hom ((e i).symm x)) =
      e j ((e j).symm ((B.d i j).hom x))
    rw [LinearEquiv.apply_symm_apply]
    have hs := f.comm i j ((e i).symm x)
    rw [h i, h j] at hs
    simpa using hs.symm

def CochainMap.homologyEquiv (f : CochainMap A B) (e : ∀ n, A.X n ≃ₗ[R] B.X n)
    (h : f.IsTermEquiv e) (n : ℕ) : Homology A n ≃ₗ[R] Homology B n :=
  LinearEquiv.ofLinearMap (f.homology n) ((f.inverse e h).homology n)
    (homology_inverse (f.inverse e h) f (fun i x => by
      rw [h i]; exact (e i).apply_symm_apply x) n)
    (homology_inverse f (f.inverse e h) (fun i x => by
      rw [h i]; exact (e i).symm_apply_apply x) n)

/-- A map commuting with successors commutes also with the zero
differentials at all other pairs of indices. -/
def CochainMap.ofSucc (f : ∀ n, A.X n →ₗ[R] B.X n)
    (h : ∀ n x, (B.d n (n+1)).hom (f n x) = f (n+1) ((A.d n (n+1)).hom x)) :
    CochainMap A B where
  term := f
  comm i j x := by
    by_cases hij : (ComplexShape.up ℕ).Rel i j
    · change i + 1 = j at hij
      subst j
      exact h i x
    · rw [A.shape i j hij, B.shape i j hij]
      simp

/-- The quotient map's action on each original cocycle class. -/
def Induced (f : ∀ n, A.X n →ₗ[R] B.X n)
    (h : ∀ n, Homology A n →ₗ[R] Homology B n) : Prop :=
  ∀ n (z : cycles A n), ∃ y : cycles B n,
    y.val = f n z.val ∧ h n (homologyClass A n z) = homologyClass B n y

end Quotients

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]

/-- A common carrier lift keeps the scalar ring and the action on representatives. -/
abbrev lift (M : ModuleCat.{a} (U k g)) : ModuleCat.{max a w} (U k g) :=
  ModuleCat.of (U k g) (ULift.{w} M)

abbrev up (M : ModuleCat.{a} (U k g)) : M ≃ₗ[U k g] ModuleCat.of (U k g) (ULift.{w} M) :=
  (ULift.moduleEquiv (R := U k g) (M := M)).symm

def underlyingEquiv {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{b} (U k g)}
    (e : M ≃ₗ[U k g] N) :
    (underlying k g).obj M ≃ₗ[k] (underlying k g).obj N :=
  letI : Module k M := inferInstanceAs (Module k ((underlying k g).obj M))
  letI : IsScalarTower k (U k g) M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module k N := inferInstanceAs (Module k ((underlying k g).obj N))
  letI : IsScalarTower k (U k g) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  e.restrictScalars k

/-- Postcomposition with a coefficient equivalence and its inverse on the actual wedges. -/
def exteriorEquiv {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{b} (U k g)}
    (e : M ≃ₗ[U k g] N) (n : ℕ) :
    (CE.W k g n →ₗ[k] (underlying k g).obj M) ≃ₗ[k]
    (CE.W k g n →ₗ[k] (underlying k g).obj N) :=
  LinearEquiv.congrRight (underlyingEquiv e)

def exteriorPost {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{b} (U k g)}
    (f : M →ₗ[U k g] N) (n : ℕ) :
    (CE.W k g n →ₗ[k] (underlying k g).obj M) →ₗ[k]
    (CE.W k g n →ₗ[k] (underlying k g).obj N) :=
  letI : Module k M := inferInstanceAs (Module k ((underlying k g).obj M))
  letI : IsScalarTower k (U k g) M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module k N := inferInstanceAs (Module k ((underlying k g).obj N))
  letI : IsScalarTower k (U k g) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  { toFun := fun t => (f.restrictScalars k).comp t
    map_add' := by intro x y; exact LinearMap.ext fun z => map_add (f.restrictScalars k) (x z) (y z)
    map_smul' := by intro r x; exact LinearMap.ext fun z => (f.restrictScalars k).map_smul r (x z) }

section OriginalComplex

variable (D : CochainTheory.{u,v,w} k g)
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{max u v w} (U k g)}
  (e : M ≃ₗ[U k g] N)

/-- The CE differential on the unlifted cochains, expressed through the two
inverse postcomposition maps. It is characterized by the CE formula. -/
def differential (n : ℕ) : (CE.W k g n →ₗ[k] (underlying k g).obj M) →ₗ[k]
    (CE.W k g (n+1) →ₗ[k] (underlying k g).obj M) :=
  (exteriorEquiv e (n+1)).symm.toLinearMap.comp
    ((D.d N n).comp (exteriorEquiv e n).toLinearMap)

abbrev complex : CochainComplex (ModuleCat.{max u v a} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (CE.W k g n →ₗ[k] (underlying k g).obj M))
    (fun n => ModuleCat.ofHom (differential D e n)) (fun n => by
      apply ModuleCat.hom_ext
      ext1 x
      change (exteriorEquiv e (n + 2)).symm
        (D.d N (n+1) (exteriorEquiv e (n+1)
          ((exteriorEquiv e (n+1)).symm (D.d N n (exteriorEquiv e n x))))) = 0
      rw [LinearEquiv.apply_symm_apply]
      have hz := LinearMap.congr_fun (D.square N n) (exteriorEquiv e n x)
      change D.d N (n+1) (D.d N n (exteriorEquiv e n x)) = 0 at hz
      rw [hz, map_zero])

def exteriorLiftMap (D : CochainTheory.{u,v,w} k g) (e : M ≃ₗ[U k g] N) :
    CochainMap (complex D e) (D.complex N) :=
  CochainMap.ofSucc (fun n => (exteriorEquiv e n).toLinearMap) (by
    intro n t
    simpa only [CochainTheory.complex, complex, CochainComplex.of_d, ModuleCat.hom_ofHom,
      differential, LinearMap.comp_apply, LinearEquiv.coe_coe] using
      ((exteriorEquiv e (n+1)).apply_symm_apply (D.d N n (exteriorEquiv e n t))).symm)

def exteriorHomologyEquiv (D : CochainTheory.{u,v,w} k g) (e : M ≃ₗ[U k g] N)
    (n : ℕ) : Homology (complex D e) n ≃ₗ[k] Homology (D.complex N) n :=
  (exteriorLiftMap D e).homologyEquiv _ (fun _ => rfl) n

/-- The exterior complex on an original module, using the prescribed common lift. -/
abbrev ce (D : CochainTheory.{u,v,max w a} k g) (M : ModuleCat.{a} (U k g)) :=
  complex D (up.{u,v,max u v w a,a} M)

end OriginalComplex

section ExteriorTransport

variable (D : CochainTheory.{u,v,w} k g)
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{max u v w} (U k g)}
  (e : M ≃ₗ[U k g] N)

/-- Both comparisons are given by postcomposition on the original exterior
powers, and induce inverse maps on classes of actual cocycles. -/
def ExteriorTransport : Prop :=
  IsCEDifferential (coefficientRepresentation k g M) (differential D e) ∧
  (∀ n (z : CE.W k g n) t, exteriorEquiv e n t z = e (t z)) ∧
  (∀ n (z : CE.W k g n) t, (exteriorEquiv e n).symm t z = e.symm (t z)) ∧
  ∃ H : ∀ n, Homology (complex D e) n ≃ₗ[k] Homology (D.complex N) n,
    Induced (fun n => (exteriorEquiv e n).toLinearMap) (fun n => (H n).toLinearMap) ∧
    Induced (fun n => (exteriorEquiv e n).symm.toLinearMap) (fun n => (H n).symm.toLinearMap)

/-- The differential on original coefficients agrees with the HA-A06
evaluation differential used by the HA-A07 free-resolution comparison. -/
def ResolutionDifferential : Prop :=
  letI : IsScalarTower k (U k g) ((underlying k g).obj M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  ∀ (B : CE.BoundaryData k g)
    (C : CE.CochainData k g ((underlying k g).obj M) B.differential) (n : ℕ),
    differential D e n = C.differential n

end ExteriorTransport

section CommonLift

variable {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{b} (U k g)}
  {P : ModuleCat.{c} (U k g)}

/-- A coefficient map, conjugated into the common category with the
same enveloping algebra. -/
def commonMap (f : M →ₗ[U k g] N) :
    ModuleCat.of (U k g) (ULift.{max u v w a b} M) ⟶
      ModuleCat.of (U k g) (ULift.{max u v w a b} N) :=
  ModuleCat.ofHom ((up N).toLinearMap.comp (f.comp (up M).symm.toLinearMap))

/-- The common lift of a short exact sequence with three independently
sized carriers uses a single lift level for the three terms. -/
def commonSequence (i : M →ₗ[U k g] N) (p : N →ₗ[U k g] P)
    (h : Function.Exact i p) : ShortComplex (ModuleCat.{max u v w a b c} (U k g)) :=
  ModuleCat.shortComplexOfConj
    (up.{u,v,max u v w a b c,a} M).symm
    (up.{u,v,max u v w a b c,b} N).symm
    (up.{u,v,max u v w a b c,c} P).symm i p h.linearMap_comp_eq_zero

def CommonSequenceExact (M : ModuleCat.{a} (U k g)) (N : ModuleCat.{b} (U k g))
    (P : ModuleCat.{c} (U k g)) : Prop :=
  ∀ (i : M →ₗ[U k g] N) (p : N →ₗ[U k g] P)
    (h : Function.Exact i p), Function.Injective i → Function.Surjective p →
    (commonSequence.{u,v,w,a,b,c} i p h).ShortExact

end CommonLift

section Boundaries

variable {A : CochainComplex (ModuleCat.{a} k) ℕ}
  {B : CochainComplex (ModuleCat.{b} k) ℕ}
  {C : CochainComplex (ModuleCat.{c} k) ℕ}

/-- The lift-and-differentiate formula on the three actual coefficient
carriers, interpreted as a linear map on their original quotients. -/
def Connecting (i : CochainMap A B) (p : CochainMap B C) (n : ℕ)
    (δ : Homology C n →ₗ[k] Homology A (n+1)) : Prop :=
  ∀ (z : cycles C n) (y : B.X n) (x : cycles A (n+1)),
    p.term n y = z.val →
    i.term (n+1) x.val = (B.d n (n+1)).hom y →
    δ (homologyClass C n z) = homologyClass A (n+1) x

/-- The boundary on original coefficients is conjugate to the actual
derived boundary via the stipulated CE coordinatizations. -/
def ConnectorTransport (i : CochainMap A B) (p : CochainMap B C)
    {A' B' C' : CochainComplex (ModuleCat.{s} k) ℕ}
    (i' : A' ⟶ B') (p' : B' ⟶ C')
    (eA : CochainMap A A') (eB : CochainMap B B') (eC : CochainMap C C')
    (eAt : ∀ n, A.X n ≃ₗ[k] A'.X n)
    (eBt : ∀ n, B.X n ≃ₗ[k] B'.X n)
    (eCt : ∀ n, C.X n ≃ₗ[k] C'.X n)
    (eAh : ∀ n, Homology A n ≃ₗ[k] Homology A' n)
    (eCh : ∀ n, Homology C n ≃ₗ[k] Homology C' n)
    (δ : ∀ n, Homology C' n →ₗ[k] Homology A' (n+1)) : Prop :=
  eA.IsTermEquiv eAt → eB.IsTermEquiv eBt → eC.IsTermEquiv eCt →
  Induced eA.term (fun n => (eAh n).toLinearMap) →
  Induced eC.term (fun n => (eCh n).toLinearMap) →
  (∀ n x, eB.term n (i.term n x) = (i'.f n).hom (eA.term n x)) →
  (∀ n y, eC.term n (p.term n y) = (p'.f n).hom (eB.term n y)) →
  P103.Specs.Ch10.HomologySequence.DegreewiseExact i' p' →
  (∀ n, P103.Specs.Ch10.HomologySequence.Connecting i' p' n (n+1) (δ n)) →
  ∀ n,
    (Function.Injective (i.term n) ∧ Function.Exact (i.term n) (p.term n) ∧
      Function.Surjective (p.term n)) ∧
    Connecting i p n ((eAh (n+1)).symm.toLinearMap.comp ((δ n).comp (eCh n).toLinearMap))

end Boundaries

section ExteriorNaturality

variable (D : CochainTheory.{u,v,w} k g)
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{b} (U k g)}
  {M' N' : ModuleCat.{max u v w} (U k g)}
  (e : M ≃ₗ[U k g] M') (e' : N ≃ₗ[U k g] N')
  (f : M →ₗ[U k g] N)

def conjugateMap : M' ⟶ N' :=
  ModuleCat.ofHom (e'.toLinearMap.comp (f.comp e.symm.toLinearMap))

/-- Cross-universe naturality on the actual exterior cochains and
cohomology classes, using the common coefficient map. -/
def ExteriorNaturality : Prop :=
  ∃ F : CochainMap (complex D e) (complex D e'),
    (∀ n, F.term n = exteriorPost f n) ∧
    (∀ n t, exteriorEquiv e' n (F.term n t) =
      ((D.functor.map (conjugateMap e e' f)).f n).hom (exteriorEquiv e n t)) ∧
    ∃ (H : ∀ n, Homology (complex D e) n ≃ₗ[k] Homology (D.complex M') n)
      (H' : ∀ n, Homology (complex D e') n ≃ₗ[k] Homology (D.complex N') n),
      Induced (fun n => (exteriorEquiv e n).toLinearMap) (fun n => (H n).toLinearMap) ∧
      Induced (fun n => (exteriorEquiv e' n).toLinearMap) (fun n => (H' n).toLinearMap) ∧
      ∀ n, (H' n).toLinearMap.comp (F.homology n) =
        (homologyMap (D.functor.map (conjugateMap e e' f)) n).comp (H n).toLinearMap

open P103.Specs.Ch10.Comparison

/-- Naturality after identifying a diagram entry with cohomology on the
original coefficients. The coefficient map may cross universes. -/
def NaturalCoordinates {X : Type r} [Category X]
    (T : X ⥤ ModuleCat.{max u v w} (U k g)) (V : X ⥤ ModuleCat.{max u v w} k)
    {X₁ X₂ : X} (α : X₁ ⟶ X₂) (n : ℕ)
    (J : V ≅ T ⋙ D.cohomology n)
    (e : M ≃ₗ[U k g] T.obj X₁) (e' : N ≃ₗ[U k g] T.obj X₂) (f : M →ₗ[U k g] N) : Prop :=
  conjugateMap e e' f = T.map α →
  ∃ K : CochainMap (complex D e) (complex D e'),
    (∀ i, K.term i = exteriorPost f i) ∧
    ∀ x : V.obj X₁,
      K.homology n ((exteriorHomologyEquiv D e n).symm ((J.hom.app X₁).hom x)) =
        (exteriorHomologyEquiv D e' n).symm ((J.hom.app X₂).hom ((V.map α).hom x))

end ExteriorNaturality

section Augmentations

open P103.Specs.Ch10.Comparison

variable {X : Type*} [Category X]
  (T : X ⥤ ModuleCat.{max u v w} (U k g)) (D : CochainTheory.{u,v,w} k g)
  {F V : X ⥤ ModuleCat.{max u v w} k} (unit : F ⟶ V)
  (evaluate : ∀ M : X, F.obj M → (underlying k g).obj (T.obj M))
  (J : V ≅ T ⋙ D.cohomology 0)

/-- The original class of the transported derived unit is represented by
the degree-zero exterior cochain with the prescribed empty-wedge value. -/
def AugmentationFormula : Prop :=
  ∀ (M : X) (M₀ : ModuleCat.{a} (U k g)) (e : M₀ ≃ₗ[U k g] T.obj M),
    ∀ m : F.obj M, ∃ z : cycles (complex D e) 0,
      z.val (CE.wedge k g 0 Fin.elim0) = e.symm (evaluate M m) ∧
      (exteriorHomologyEquiv D e 0).symm ((J.hom.app M).hom ((unit.app M).hom m)) =
        homologyClass (complex D e) 0 z

def AugmentationTransport : Prop :=
  PreservesCEAugmentation T D unit evaluate J →
  AugmentationFormula.{u,v,w,a,_,_} T D unit evaluate J

end Augmentations

section NormalizedConnectors

open P103.Specs.Ch10.Comparison

variable {X : Type r} [Category X] [Abelian X]
  (T : X ⥤ ModuleCat.{max u v w} (U k g))
  (D : CochainTheory.{u,v,w} k g)
  (V : ℕ → X ⥤ ModuleCat.{max u v w} k)
  (δ : ∀ {S : ShortComplex X}, S.ShortExact → ∀ n : ℕ,
    (V n).obj S.X₃ ⟶ (V (n+1)).obj S.X₁)
  (J : ∀ n, V n ≅ (T ⋙ D.functor) ⋙ quotientHomology (.up ℕ) n)

/-- The original coefficient boundary in the coordinates of the
given lifted sequence. -/
def NormalizedConnectorFormula {S : ShortComplex X} (hs : S.ShortExact)
    {A : ModuleCat.{a} (U k g)} {B : ModuleCat.{b} (U k g)} {C : ModuleCat.{c} (U k g)}
    (eA : A ≃ₗ[U k g] T.obj S.X₁) (eB : B ≃ₗ[U k g] T.obj S.X₂) (eC : C ≃ₗ[U k g] T.obj S.X₃)
    (i : A →ₗ[U k g] B) (p : B →ₗ[U k g] C) : Prop :=
    ∃ (I : CochainMap (complex D eA) (complex D eB))
      (P : CochainMap (complex D eB) (complex D eC)),
      (∀ n, I.term n = exteriorPost i n) ∧ (∀ n, P.term n = exteriorPost p n) ∧
      ∀ n, (Function.Injective (I.term n) ∧ Function.Exact (I.term n) (P.term n) ∧
          Function.Surjective (P.term n)) ∧
        Connecting I P n ((exteriorHomologyEquiv D eA (n+1)).symm.toLinearMap.comp
          (((J n).inv.app S.X₃ ≫ δ hs n ≫ (J (n+1)).hom.app S.X₁).hom.comp
            (exteriorHomologyEquiv D eC n).toLinearMap))

/-- The same normalized derived comparison identifies the original
coefficient boundary for any compatible short exact lifted sequence. -/
def NormalizedConnectors : Prop :=
  PreservesCEConnectors (T ⋙ D.functor) V δ J →
  ∀ {S : ShortComplex X} (hs : S.ShortExact)
    (A : ModuleCat.{a} (U k g)) (B : ModuleCat.{b} (U k g)) (C : ModuleCat.{c} (U k g))
    (eA : A ≃ₗ[U k g] T.obj S.X₁) (eB : B ≃ₗ[U k g] T.obj S.X₂) (eC : C ≃ₗ[U k g] T.obj S.X₃)
    (i : A →ₗ[U k g] B) (p : B →ₗ[U k g] C),
    conjugateMap eA eB i = T.map S.f → conjugateMap eB eC p = T.map S.g →
    NormalizedConnectorFormula T D V δ J hs eA eB eC i p

variable (D₀ : CochainTheory.{u,v,max w a b c} k g)
  (V₀ : ℕ → ModuleCat.{max u v w a b c} (U k g) ⥤ ModuleCat.{max u v w a b c} k)
  (δ₀ : ∀ {S : ShortComplex (ModuleCat.{max u v w a b c} (U k g))}, S.ShortExact → ∀ n : ℕ,
    (V₀ n).obj S.X₃ ⟶ (V₀ (n+1)).obj S.X₁)
  (J₀ : ∀ n, V₀ n ≅ D₀.cohomology n)

/-- A common lift of the given sequence has the positive connecting map on
the three original exterior cohomologies, in the very same derived comparison. -/
def LiftedConnectorFormula : Prop :=
  ∀ (A : ModuleCat.{a} (U k g)) (B : ModuleCat.{b} (U k g)) (C : ModuleCat.{c} (U k g))
    (i : A →ₗ[U k g] B) (p : B →ₗ[U k g] C)
    (hi : Function.Injective i) (hex : Function.Exact i p) (hp : Function.Surjective p),
    let S := commonSequence.{u,v,w,a,b,c} i p hex
    let eA := up.{u,v,max u v w a b c,a} A
    let eB := up.{u,v,max u v w a b c,b} B
    let eC := up.{u,v,max u v w a b c,c} C
    ∃ hS : S.ShortExact,
      NormalizedConnectorFormula (𝟭 _) D₀ V₀ δ₀ J₀ hS eA eB eC i p

def LiftedConnectors : Prop :=
  PreservesCEConnectors D₀.functor V₀ δ₀ J₀ →
  LiftedConnectorFormula.{u,v,w,a,b,c} D₀ V₀ δ₀ J₀

end NormalizedConnectors

section Ideal

variable (h : LieIdeal k g)
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{b} (U k g)}

abbrev restrictOriginal (M : ModuleCat.{a} (U k g)) : ModuleCat.{a} (U k h) :=
  (ModuleCat.restrictScalars (IdealEnveloping.inducedMap k g h).toRingHom).obj M

/-- Restrict a map of original modules without changing its function or
forcing its source and target into the same universe. -/
def restrictOriginalMap (f : M →ₗ[U k g] N) : restrictOriginal h M →ₗ[U k h] restrictOriginal h N where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := f.map_smul (IdealEnveloping.inducedMap k g h r) x

/-- Restriction along the actual inclusion does not change either carrier. -/
def restrictEquiv (e : M ≃ₗ[U k g] N) : restrictOriginal h M ≃ₗ[U k h] restrictOriginal h N :=
  { e.toAddEquiv with
    map_smul' := fun r x => e.map_smul (IdealEnveloping.inducedMap k g h r) x }

variable {N : ModuleCat.{max u v w} (U k g)}
  (Dh : CochainTheory.{u,v,w} k h) (e : M ≃ₗ[U k g] N)

abbrev idealComplex := complex Dh (restrictEquiv h e)

/-- The quotient action in the normalized coordinates is induced by
the original Lie derivative on exterior cocycles. -/
def IdealActionFormula
    (Q : ℕ → ModuleCat.{max u v w} (U k (g ⧸ h)))
    (J : ∀ n, (underlying k (g ⧸ h)).obj (Q n) ≃ₗ[k]
      Homology (Dh.complex (restrictOriginal h N)) n) : Prop :=
  ∀ n (y : g) (z : cycles (idealComplex h Dh e) n),
    ∃ z' : cycles (idealComplex h Dh e) n,
      (∀ x : Fin n → h, z'.val (CE.wedge k h n x) =
        (show (underlying k h).obj (restrictOriginal h M) from
          coefficientRepresentation k g M y (z.val (CE.wedge k h n x))) -
          ∑ i : Fin n, z.val (CE.wedge k h n (Function.update x i ⁅y, x i⁆))) ∧
      (J n).symm (exteriorHomologyEquiv Dh (restrictEquiv h e) n (homologyClass _ n z')) =
        inclusion k (g ⧸ h) (LieQuotientAction.quotientMap k g h y) •
          (J n).symm (exteriorHomologyEquiv Dh (restrictEquiv h e) n (homologyClass _ n z))

/-- Transport the ambient quotient-action formula to original ideal cocycles. -/
def IdealActionTransport
    (Q : ℕ → ModuleCat.{max u v w} (U k (g ⧸ h)))
    (J : ∀ n, (underlying k (g ⧸ h)).obj (Q n) ≃ₗ[k]
      Homology (Dh.complex (restrictOriginal h N)) n) : Prop :=
  (∀ n (y : g) (z : cycles (Dh.complex (restrictOriginal h N)) n),
    ∃ z' : cycles (Dh.complex (restrictOriginal h N)) n,
      (∀ x : Fin n → h, z'.val (CE.wedge k h n x) =
        (show (underlying k h).obj (restrictOriginal h N) from
          coefficientRepresentation k g N y (z.val (CE.wedge k h n x))) -
          ∑ i : Fin n, z.val (CE.wedge k h n (Function.update x i ⁅y, x i⁆))) ∧
      (J n).symm (homologyClass _ n z') =
        inclusion k (g ⧸ h) (LieQuotientAction.quotientMap k g h y) •
          (J n).symm (homologyClass _ n z)) →
  IdealActionFormula h Dh e Q J

/-- The printed Lie derivative is a cochain operator and is intertwined
by postcomposition with the coefficient equivalence in every degree. -/
def CochainDerivative : Prop :=
  ∀ y : g, ∃ (L : CochainMap (idealComplex h Dh e) (idealComplex h Dh e))
    (L' : CochainMap (Dh.complex (restrictOriginal h N)) (Dh.complex (restrictOriginal h N))),
    (∀ n (t : (idealComplex h Dh e).X n) (x : Fin n → h),
      (L.term n t : CE.W k h n →ₗ[k] (underlying k h).obj (restrictOriginal h M)) (CE.wedge k h n x) =
        (show (underlying k h).obj (restrictOriginal h M) from
          coefficientRepresentation k g M y ((show CE.W k h n →ₗ[k] _ from t) (CE.wedge k h n x))) -
        ∑ i : Fin n, (show CE.W k h n →ₗ[k] _ from t) (CE.wedge k h n (Function.update x i ⁅y, x i⁆))) ∧
    (∀ n (t : (Dh.complex (restrictOriginal h N)).X n) (x : Fin n → h),
      (L'.term n t : CE.W k h n →ₗ[k] (underlying k h).obj (restrictOriginal h N)) (CE.wedge k h n x) =
        (show (underlying k h).obj (restrictOriginal h N) from
          coefficientRepresentation k g N y ((show CE.W k h n →ₗ[k] _ from t) (CE.wedge k h n x))) -
        ∑ i : Fin n, (show CE.W k h n →ₗ[k] _ from t) (CE.wedge k h n (Function.update x i ⁅y, x i⁆))) ∧
    ∀ n t, exteriorEquiv (restrictEquiv h e) n (L.term n t) =
      L'.term n (exteriorEquiv (restrictEquiv h e) n t)

end Ideal

section Rebase

variable {L : Type v} [LieRing L] [LieAlgebra k L]
  {V : Type a} [AddCommGroup V] [Module k V]
  (N : ModuleCat.{b} (U k L)) (e : V ≃ₗ[k] (underlying k L).obj N)

/-- Transport the quotient action onto the original cohomology or invariant
vectors. Its underlying vector operations agree with the original ones. -/
def rebase : ModuleCat.{a} (U k L) :=
  letI := e.toAddEquiv.module (U k L)
  ModuleCat.of (U k L) V

def rebaseEquiv : rebase N e ≃ₗ[U k L] N :=
  e.toAddEquiv.linearEquiv (U k L)

/-- The scalar action underlying the transported enveloping module is
the original scalar action on its carrier. -/
def RebaseScalarAction : Prop :=
  ∀ (z : k) (x : V),
    (show V from z • (show (underlying k L).obj (rebase N e) from x)) = z • x

end Rebase

section Edges

open LieQuotientAction

variable (h : LieIdeal k g)
  (Dg : CochainTheory.{u,v,w} k g) (Dh : CochainTheory.{u,v,w} k h)
  (Dq : CochainTheory.{u,v,w} k (g ⧸ h))
  (E : EdgeCochains h Dg Dh Dq)
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{max u v w} (U k g)}
  (e : M ≃ₗ[U k g] N)

abbrev Invariants (M : ModuleCat.{a} (U k g)) :=
  invariants h (coefficientRepresentation k g M)

abbrev InvariantComparison :=
  Invariants h M ≃ₗ[k] (underlying k (g ⧸ h)).obj ((idealInvariants.{u,v,w} h).obj N)

variable (j : InvariantComparison h (M := M) (N := N))

def InvariantEvaluation : Prop :=
  ∀ z : Invariants h M,
    (show (idealInvariants.{u,v,w} h).obj N from j z) (1 : U k (g ⧸ h)) = e z.val

def InvariantAction : Prop :=
  ∀ y : g, ∀ z : Invariants h M,
    ((show rebase _ j from z) |> fun m =>
      (inclusion k (g ⧸ h) (quotientMap k g h y) • m : rebase _ j)).val =
      coefficientRepresentation k g M y z.val

def InvariantTransport : Prop :=
  ∃ j : InvariantComparison h (M := M) (N := N),
    InvariantEvaluation h e j ∧ InvariantAction h j

/-- Each original coefficient map preserves the quotient action on its
ideal-invariant subspaces and commutes with the carrier comparisons. -/
def InvariantNaturality
    {M' : ModuleCat.{b} (U k g)} {N' : ModuleCat.{max u v w} (U k g)}
    (e' : M' ≃ₗ[U k g] N') (f : M →ₗ[U k g] M')
    (j' : InvariantComparison h (M := M') (N := N')) : Prop :=
  InvariantEvaluation h e j → InvariantEvaluation h e' j' →
  ∃ F : rebase _ j →ₗ[U k (g ⧸ h)] rebase _ j',
    ∀ z : Invariants h M, (show Invariants h M' from F z).val = f z.val ∧
      j' (F z) = (idealInvariants.{u,v,w} h).map (conjugateMap e e' f) (j z)

abbrev invariantComplex := complex Dq (rebaseEquiv _ j)

/-- Inflation and restriction on original exterior arguments and
coefficients, with their ambient cochain maps fixed by commuting squares. -/
def ExteriorEdges
    (inf : CochainMap (invariantComplex h Dq j) (complex Dg e))
    (res : CochainMap (complex Dg e) (idealComplex h Dh e)) : Prop :=
  (∀ n (t : (invariantComplex h Dq j).X n) (x : Fin n → g),
      (show CE.W k g n →ₗ[k] (underlying k g).obj M from inf.term n t)
        (CE.wedge k g n x) =
      ((show CE.W k (g ⧸ h) n →ₗ[k] (underlying k (g ⧸ h)).obj (rebase _ j) from t)
        (CE.wedge k (g ⧸ h) n (quotientMap k g h ∘ x))).val) ∧
  (∀ n (t : (complex Dg e).X n) (x : Fin n → h),
      (show CE.W k h n →ₗ[k] (underlying k h).obj (restrictOriginal h M) from res.term n t)
        (CE.wedge k h n x) =
      (show CE.W k g n →ₗ[k] (underlying k g).obj M from t)
        (CE.wedge k g n (h.incl ∘ x))) ∧
  (∀ n, (exteriorHomologyEquiv Dg e n).toLinearMap.comp (inf.homology n) =
      (homologyMap (E.inflation.app N) n).comp
        (exteriorHomologyEquiv Dq (rebaseEquiv _ j) n).toLinearMap) ∧
  (∀ n, (exteriorHomologyEquiv Dh (restrictEquiv h e) n).toLinearMap.comp (res.homology n) =
       (homologyMap (E.restriction.app N) n).comp (exteriorHomologyEquiv Dg e n).toLinearMap)

def EdgeTransport : Prop :=
  InvariantEvaluation h e j →
  ∃ (inf : CochainMap (invariantComplex h Dq j) (complex Dg e))
    (res : CochainMap (complex Dg e) (idealComplex h Dh e)), ExteriorEdges h Dg Dh Dq E e j inf res

end Edges

section SpectralSequence

open GrothendieckSpectralSequence GrothendieckEdges
open HypercohomologyDerivedNaturality
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open P103.Specs.Ch10.Comparison

variable (h : LieIdeal k g)
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k g))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k (g ⧸ h)))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} k)]
  {Dg : CochainTheory.{u,v,w} k g} {Dh : CochainTheory.{u,v,w} k h}
  {Dq : CochainTheory.{u,v,w} k (g ⧸ h)} {E : EdgeCochains h Dg Dh Dq}
  {P : Package (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h)}
  {O : ObjectEdges (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) P}
  (J : CEComparison h Dg Dh Dq E P O)
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{max u v w} (U k g)}
  (e : M ≃ₗ[U k g] N)

abbrev sequenceDiagram :=
  (objectSequence (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) P).obj N

abbrev idealDerived (n : ℕ) :=
  (rightValue (idealInvariants.{u,v,w} h) n).obj N

/-- The normalized ideal comparison in the direction from original
exterior cohomology to the derived quotient coefficient. -/
def idealCoordinates (n : ℕ) :
    Homology (idealComplex h Dh e) n ≃ₗ[k] (underlying k (g ⧸ h)).obj (idealDerived h (N := N) n) :=
  (exteriorHomologyEquiv Dh (restrictEquiv h e) n).trans (((J.ideal n).app N).toLinearEquiv.symm)

abbrev idealCoefficient (n : ℕ) :=
  rebase (idealDerived h (N := N) n) (idealCoordinates h J e n)

abbrev secondComplex (q : ℕ) :=
  complex Dq (rebaseEquiv _ (idealCoordinates h J e q))

/-- The actual E₂ entry in original exterior cohomology coordinates. -/
def secondCoordinates (p q : ℕ) :
    (sequenceDiagram h (P := P) (N := N)).page 0 (p : ℤ) ((p : ℤ) + (q : ℤ)) ≃ₗ[k]
      Homology (secondComplex h J e q) p :=
  ((J.secondPageIso h p q).app N).toLinearEquiv.trans
    (exteriorHomologyEquiv Dq (rebaseEquiv _ (idealCoordinates h J e q)) p).symm

/-- The target coordinate on the original exterior cohomology. -/
def targetCoordinates (n : ℕ) :
    (sequenceDiagram h (P := P) (N := N)).target (n : ℤ) ≃ₗ[k] Homology (complex Dg e) n :=
  ((J.targetIso h n).app N).toLinearEquiv.trans (exteriorHomologyEquiv Dg e n).symm

def targetStep (p : ℤ) (n : ℕ) : Submodule k (Homology (complex Dg e) n) :=
  LinearMap.range ((targetCoordinates h J e n).toLinearMap.comp
    ((sequenceDiagram h (P := P) (N := N)).inclusion p n).hom)

def FiniteFiltration : Prop :=
  ∀ n : ℕ, (∀ p : ℤ, targetStep h J e (p+1) n ≤ targetStep h J e p n) ∧
    ∃ l r : ℤ, (∀ p ≤ l, targetStep h J e p n = ⊤) ∧
      (∀ p ≥ r, targetStep h J e p n = ⊥)

/-- The associated graded quotient of the filtration on original exterior cohomology. -/
abbrev targetGraded (p : ℤ) (n : ℕ) :=
  (targetStep h J e p n) ⧸
    ((targetStep h J e (p+1) n).comap (targetStep h J e p n).subtype)

/-- The eventual pages agree with the associated graded of the actual original
cohomology filtration. -/
def GradedConvergence : Prop :=
  ∀ n : ℕ, ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ p : ℤ,
    let S := sequenceDiagram h (P := P) (N := N)
    S.differential r p (n : ℤ) = 0 ∧
      Nonempty (S.page r p (n : ℤ) ≃ₗ[k] targetGraded h J e p n)

variable (j : InvariantComparison h (M := M) (N := N))

/-- The bottom-axis isomorphism uses the underived invariant vectors,
with the derived unit from the ambient spectral sequence. -/
def rowCoordinates (n : ℕ) :
    (sequenceDiagram h (P := P) (N := N)).page 0 (n : ℤ) (n : ℤ) ≃ₗ[k]
      Homology (invariantComplex h Dq j) n :=
  ((J.rowIso h n).app N).toLinearEquiv.trans
    (exteriorHomologyEquiv Dq (rebaseEquiv _ j) n).symm

/-- Restriction lands in the original quotient-invariant submodule. -/
def fixedClasses (n : ℕ) : Submodule k (Homology (idealComplex h Dh e) n) :=
  (LinearMap.range (J.quotientInclusion.evaluation.app (idealDerived h (N := N) n)).hom).comap
    (idealCoordinates h J e n).toLinearMap

/-- The map from augmentation-coextended invariants to actual invariant
classes of exterior cocycles, keeping their embedding into cohomology. -/
def fixedClassInclusion (n : ℕ) :
    (quotientInvariants.{u,v,w} h).obj (idealDerived h (N := N) n) →ₗ[k] fixedClasses h J e n :=
  ((idealCoordinates h J e n).symm.toLinearMap.comp
    (J.quotientInclusion.evaluation.app (idealDerived h (N := N) n)).hom).codRestrict
      (fixedClasses h J e n) fun x => by
        change ∃ y, (J.quotientInclusion.evaluation.app (idealDerived h (N := N) n)).hom y =
          idealCoordinates h J e n ((idealCoordinates h J e n).symm
            ((J.quotientInclusion.evaluation.app (idealDerived h (N := N) n)).hom x))
        exact ⟨x, ((idealCoordinates h J e n).apply_symm_apply _).symm⟩

def fixedClassEquiv (n : ℕ) :
    (quotientInvariants.{u,v,w} h).obj (idealDerived h (N := N) n) ≃ₗ[k] fixedClasses h J e n :=
  LinearEquiv.ofBijective (fixedClassInclusion h J e n) ⟨by
    intro x y hxy
    apply J.quotientInclusion.injective (idealDerived h (N := N) n)
    apply (idealCoordinates h J e n).symm.injective
    exact congrArg Subtype.val hxy, by
    intro z
    obtain ⟨x, hx⟩ := z.property
    exact ⟨x, Subtype.ext ((congrArg (idealCoordinates h J e n).symm hx).trans
      ((idealCoordinates h J e n).symm_apply_apply z.val))⟩⟩

def columnCoordinates (n : ℕ) :
    (sequenceDiagram h (P := P) (N := N)).page 0 0 (n : ℤ) ≃ₗ[k] fixedClasses h J e n :=
  ((O.columnPage n).app N).toLinearEquiv.trans (fixedClassEquiv h J e n)

/-- The original degree-zero ideal identification evaluates a cocycle
on the empty wedge and uses the derived unit. -/
def RowAugmentation : Prop :=
  ∀ m : Invariants h M, ∃ z : cycles (idealComplex h Dh e) 0,
    z.val (CE.wedge k h 0 Fin.elim0) = m.val ∧
    (idealCoordinates h J e 0).symm ((O.degreeZeroF.hom.app N).hom (j m)) =
      homologyClass (idealComplex h Dh e) 0 z

/-- Replacing the underived invariant coefficients by degree-zero ideal
cohomology uses the same comparison as the bottom row and the general page. -/
def RowAxis : Prop :=
  ∀ (n : ℕ) (x : (sequenceDiagram h (P := P) (N := N)).page 0 (n : ℤ) ((n : ℤ) + 0)),
    exteriorHomologyEquiv Dq (rebaseEquiv _ (idealCoordinates h J e 0)) n
      (secondCoordinates h J e n 0 x) =
    homologyMap (Dq.functor.map (O.degreeZeroF.hom.app N)) n
      (exteriorHomologyEquiv Dq (rebaseEquiv _ j) n
        (rowCoordinates h J j n ((rowIndexIso _ _ P n).hom.app N x)))

/-- The degree-zero quotient CE identification on the left axis gives the
same invariant class as evaluation at the empty wedge. -/
def ColumnAxis : Prop :=
  ∀ (n : ℕ) (x : (sequenceDiagram h (P := P) (N := N)).page 0 0 (0 + (n : ℤ))),
    ∃ z : cycles (secondComplex h J e n) 0,
      z.val (CE.wedge k (g ⧸ h) 0 Fin.elim0) =
        (columnCoordinates h J e n ((columnIndexIso _ _ P n).hom.app N x)).val ∧
      secondCoordinates h J e 0 n x = homologyClass (secondComplex h J e n) 0 z

/-- Transport the actual filtered d₂ in the left- and bottom-axis coordinates. -/
def transgression :
    fixedClasses h J e 1 →ₗ[k] Homology (invariantComplex h Dq j) 2 :=
  (rowCoordinates h J j 2).toLinearMap.comp
    ((G05FilteredEdges.transgression (sequenceDiagram h (P := P) (N := N))).hom.comp
      (columnCoordinates h J e 1).symm.toLinearMap)

abbrev originalAmbient (n : ℕ) := Homology (complex Dg e) n

/-- The restriction edge as a map into invariant classes, not just the
map to the underlying ideal cohomology space. -/
def restrictionEdge (n : ℕ) : originalAmbient e (Dg := Dg) n →ₗ[k] fixedClasses h J e n :=
  (fixedClassEquiv h J e n).toLinearMap.comp
    (((J.restrictToInvariants h n).app N).hom.comp (exteriorHomologyEquiv Dg e n).toLinearMap)

def FiveTerms {V₁ : Type a} {V₂ : Type b} {V₃ : Type c} {V₄ : Type s} {V₅ : Type t}
    [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃]
    [AddCommGroup V₄] [Module k V₄] [AddCommGroup V₅] [Module k V₅]
    (f : V₁ →ₗ[k] V₂) (g : V₂ →ₗ[k] V₃) (d : V₃ →ₗ[k] V₄) (h : V₄ →ₗ[k] V₅) : Prop :=
  Function.Injective f ∧ Function.Exact f g ∧ Function.Exact g d ∧ Function.Exact d h

def FiveTermsTransport
    (inf : CochainMap (invariantComplex h Dq j) (complex Dg e))
    (res : CochainMap (complex Dg e) (idealComplex h Dh e)) : Prop :=
  ClassicalFiveTerms
      ((quotientHomology (.up ℕ) 1).map (E.inflation.app N))
      ((J.restrictToInvariants h 1).app N) (J.transgression h N)
      ((quotientHomology (.up ℕ) 2).map (E.inflation.app N)) →
  (∀ n, (exteriorHomologyEquiv Dg e n).toLinearMap.comp (inf.homology n) =
      (homologyMap (E.inflation.app N) n).comp
        (exteriorHomologyEquiv Dq (rebaseEquiv _ j) n).toLinearMap) →
  (∀ n, (exteriorHomologyEquiv Dh (restrictEquiv h e) n).toLinearMap.comp (res.homology n) =
       (homologyMap (E.restriction.app N) n).comp (exteriorHomologyEquiv Dg e n).toLinearMap) →
  (∀ n, (fixedClasses h J e n).subtype.comp (restrictionEdge h J e n) = res.homology n) ∧
  FiveTerms (inf.homology 1) (restrictionEdge h J e 1) (transgression h J e j) (inf.homology 2)

/-- The actual filtered edges in the original exterior coordinates. -/
def FilteredEdgeEquations
    (inf : CochainMap (invariantComplex h Dq j) (complex Dg e)) : Prop :=
  (∀ (n : ℕ) (x : (sequenceDiagram h (P := P) (N := N)).page 0 n n),
    inf.homology n (rowCoordinates h J j n x) =
      targetCoordinates h J e n ((O.filtered N).row n x)) ∧
  (∀ (n : ℕ) (x : (sequenceDiagram h (P := P) (N := N)).target n),
    restrictionEdge h J e n (targetCoordinates h J e n x) =
      columnCoordinates h J e n ((O.filtered N).column n x))

/-- The range description equals the fixed vectors for the quotient
action on the original ideal cohomology. -/
def FixedClassesFormula : Prop :=
  ∀ (n : ℕ) (x : Homology (idealComplex h Dh e) n),
    x ∈ fixedClasses h J e n ↔
      ∀ y : g ⧸ h, inclusion k (g ⧸ h) y • (show idealCoefficient h J e n from x) = 0

/-- All the objectwise identifications refer to the same diagram. -/
def ObjectTransport : Prop :=
  (∀ r p n, p < 0 ∨ n < p → CategoryTheory.Limits.IsZero
    ((sequenceDiagram h (P := P) (N := N)).page r p n)) ∧
  Converges (sequenceDiagram h (P := P) (N := N)) ∧
  FiniteFiltration h J e ∧
  GradedConvergence h J e ∧
  ExteriorTransport Dg e ∧
  ResolutionDifferential Dg e ∧
  ExteriorTransport Dh (restrictEquiv h e) ∧
  ResolutionDifferential Dh (restrictEquiv h e) ∧
  (∀ q, let i := idealCoordinates h J e q
    ExteriorTransport Dq (rebaseEquiv _ i) ∧
    ResolutionDifferential Dq (rebaseEquiv _ i) ∧ RebaseScalarAction _ i) ∧
  IdealActionFormula h Dh e (idealDerived h (N := N)) (fun n => ((J.ideal n).app N).toLinearEquiv) ∧
  CochainDerivative h Dh e ∧
  FixedClassesFormula h J e ∧
  ∃ j : InvariantComparison h (M := M) (N := N),
    InvariantEvaluation h e j ∧ InvariantAction h j ∧ ExteriorTransport Dq (rebaseEquiv _ j) ∧
    ResolutionDifferential Dq (rebaseEquiv _ j) ∧ RebaseScalarAction _ j ∧
    RowAugmentation h J e j ∧ RowAxis h J e j ∧ ColumnAxis h J e ∧
    ∃ (inf : CochainMap (invariantComplex h Dq j) (complex Dg e))
      (res : CochainMap (complex Dg e) (idealComplex h Dh e)),
      ExteriorEdges h Dg Dh Dq E e j inf res ∧
      FilteredEdgeEquations h J e j inf ∧
      (∀ n, (fixedClasses h J e n).subtype.comp (restrictionEdge h J e n) = res.homology n) ∧
      FiveTerms (inf.homology 1) (restrictionEdge h J e 1) (transgression h J e j) (inf.homology 2)

section SpectralNaturality

variable {M' : ModuleCat.{b} (U k g)} {N' : ModuleCat.{max u v w} (U k g)}
  (e' : M' ≃ₗ[U k g] N') (f : M →ₗ[U k g] M')

abbrev diagramMap := (objectSequence (idealInvariants.{u,v,w} h)
  (quotientInvariants.{u,v,w} h) P).map (conjugateMap e e' f)

/-- Coefficient maps intertwine the edges of the same filtered diagrams. -/
def SpectralEdgeNaturality : Prop :=
  G05FilteredEdges.EdgeMap (diagramMap h (P := P) e e' f) (O.filtered N) (O.filtered N')

/-- The coefficient morphism in the second page acts on original ideal
cohomology by the cochain map induced from the original module morphism. -/
def IdealCoefficientNaturality : Prop :=
  ∀ (q : ℕ) (fQ : idealCoefficient h J e q →ₗ[U k (g ⧸ h)] idealCoefficient h J e' q),
    (∀ x, idealCoordinates h J e' q (fQ x) =
      (rightValue (idealInvariants.{u,v,w} h) q).map (conjugateMap e e' f)
        (idealCoordinates h J e q x)) →
    ∃ K : CochainMap (idealComplex h Dh e) (idealComplex h Dh e'),
      (∀ i, K.term i = exteriorPost (restrictOriginalMap h f) i) ∧
      ∀ x : Homology (idealComplex h Dh e) q, K.homology q x = fQ x

def SpectralNaturality : Prop :=
  (∃ K : CochainMap (complex Dg e) (complex Dg e'),
    (∀ i, K.term i = exteriorPost f i) ∧
    (∀ (n : ℕ) (x : (sequenceDiagram h (P := P) (N := N)).target (n : ℤ)),
      K.homology n (targetCoordinates h J e n x) =
        targetCoordinates h J e' n ((diagramMap h (P := P) e e' f).target (n : ℤ) x)) ∧
    (∀ n p, Submodule.map (K.homology n) (targetStep h J e p n) ≤ targetStep h J e' p n)) ∧
  ∀ q : ℕ, ∃ fQ : idealCoefficient h J e q →ₗ[U k (g ⧸ h)] idealCoefficient h J e' q,
    (∀ x, idealCoordinates h J e' q (fQ x) =
      (rightValue (idealInvariants.{u,v,w} h) q).map (conjugateMap e e' f)
        (idealCoordinates h J e q x)) ∧
    ∃ K : CochainMap (secondComplex h J e q) (secondComplex h J e' q),
      (∀ i, K.term i = exteriorPost fQ i) ∧
      ∀ (p : ℕ) (x : (sequenceDiagram h (P := P) (N := N)).page 0 (p : ℤ) ((p : ℤ) + (q : ℤ))),
        K.homology p (secondCoordinates h J e p q x) =
          secondCoordinates h J e' p q
            ((diagramMap h (P := P) e e' f).page 0 (p : ℤ) ((p : ℤ) + (q : ℤ)) x)

end SpectralNaturality

end SpectralSequence

section OriginalNormalization

open CategoryTheory.Functor P103.Specs.Ch10.Comparison GrothendieckEdges
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

variable (h : LieIdeal k g)
  [HasDerivedCategory.{(max u v w a b c) + 1} (ModuleCat.{max u v w a b c} (U k g))]
  [HasDerivedCategory.{(max u v w a b c) + 1} (ModuleCat.{max u v w a b c} (U k (g ⧸ h)))]
  [HasDerivedCategory.{(max u v w a b c) + 1} (ModuleCat.{max u v w a b c} k)]
  {Dg : CochainTheory.{u,v,max w a b c} k g}
  {Dh : CochainTheory.{u,v,max w a b c} k h}
  {Dq : CochainTheory.{u,v,max w a b c} k (g ⧸ h)}
  (J : CohomologyComparison.{u,v,max w a b c} h Dg Dh Dq)

/-- The ideal connector starts with the same short exact sequence of
original ambient coefficients, then restricts the action on the three
carriers and their lifts along the ideal inclusion. -/
def LiftedIdealConnectorFormula : Prop :=
  ∀ (A : ModuleCat.{a} (U k g)) (B : ModuleCat.{b} (U k g)) (C : ModuleCat.{c} (U k g))
    (i : A →ₗ[U k g] B) (p : B →ₗ[U k g] C),
    Function.Injective i → ∀ (hex : Function.Exact i p), Function.Surjective p →
    let S := commonSequence.{u,v,w,a,b,c} i p hex
    let eA := restrictEquiv h (up.{u,v,max u v w a b c,a} A)
    let eB := restrictEquiv h (up.{u,v,max u v w a b c,b} B)
    let eC := restrictEquiv h (up.{u,v,max u v w a b c,c} C)
    ∃ hS : S.ShortExact,
      NormalizedConnectorFormula (restrictIdeal.{u,v,max w a b c} h) Dh
        (fun n => rightValue (idealInvariants.{u,v,max w a b c} h) n ⋙ underlying k (g ⧸ h))
        (fun hS n => (underlying k (g ⧸ h)).map
          (rightBoundary (idealInvariants.{u,v,max w a b c} h) hS n))
        J.ideal hS eA eB eC (restrictOriginalMap h i) (restrictOriginalMap h p)

/-- The three comparisons used by one sequence retain their derived
degree-zero units and connecting maps on the original exterior complexes. -/
def OriginalNormalizations : Prop :=
  AugmentationFormula.{u,v,max w a b c,a,_,_} (𝟭 _) Dg
    (degreeZeroUnit (idealInvariants.{u,v,max w a b c} h ⋙ quotientInvariants.{u,v,max w a b c} h))
    (fun M m =>
      (show (idealInvariants.{u,v,max w a b c} h).obj M from
        (show (quotientInvariants.{u,v,max w a b c} h).obj
          ((idealInvariants.{u,v,max w a b c} h).obj M) from m) (1 : k)) (1 : U k (g ⧸ h)))
    (J.ambient 0) ∧
  AugmentationFormula.{u,v,max w a b c,a,_,_} (restrictIdeal.{u,v,max w a b c} h) Dh
    (whiskerRight (degreeZeroUnit (idealInvariants.{u,v,max w a b c} h)) (underlying k (g ⧸ h)))
    (fun M m => (show (idealInvariants.{u,v,max w a b c} h).obj M from m) (1 : U k (g ⧸ h)))
    (J.ideal 0) ∧
  AugmentationFormula.{u,v,max w a b c,a,_,_} (𝟭 _) Dq
    (degreeZeroUnit (quotientInvariants.{u,v,max w a b c} h))
    (fun M m => (show (quotientInvariants.{u,v,max w a b c} h).obj M from m) (1 : k))
    (J.quotient 0) ∧
  LiftedConnectorFormula.{u,v,w,a,b,c} Dg
    (rightValue (idealInvariants.{u,v,max w a b c} h ⋙ quotientInvariants.{u,v,max w a b c} h))
    (rightBoundary (idealInvariants.{u,v,max w a b c} h ⋙ quotientInvariants.{u,v,max w a b c} h))
    J.ambient ∧
  LiftedIdealConnectorFormula.{u,v,w,a,b,c} h J ∧
  LiftedConnectorFormula.{u,v,w,a,b,c} Dq
    (rightValue (quotientInvariants.{u,v,max w a b c} h))
    (rightBoundary (quotientInvariants.{u,v,max w a b c} h))
    J.quotient

end OriginalNormalization

open GrothendieckSpectralSequence GrothendieckEdges

/-- The original coefficients of either size use one common spectral
sequence functor, and its comparison maps are the normalized ones. -/
def OriginalSequenceStatement : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] (h : LieIdeal k g),
    letI := HasDerivedCategory.standard (ModuleCat.{max u v w a b c} (U k g))
    letI := HasDerivedCategory.standard (ModuleCat.{max u v w a b c} (U k (g ⧸ h)))
    letI := HasDerivedCategory.standard (ModuleCat.{max u v w a b c} k)
    ∃ (Dg : CochainTheory.{u,v,max w a b c} k g) (Dh : CochainTheory.{u,v,max w a b c} k h)
      (Dq : CochainTheory.{u,v,max w a b c} k (g ⧸ h)) (E : EdgeCochains h Dg Dh Dq)
      (P : Package (idealInvariants.{u,v,max w a b c} h) (quotientInvariants.{u,v,max w a b c} h))
      (O : ObjectEdges (idealInvariants.{u,v,max w a b c} h) (quotientInvariants.{u,v,max w a b c} h) P)
      (J : CEComparison h Dg Dh Dq E P O),
      OriginalNormalizations.{u,v,w,a,b,c} h J.toCohomologyComparison ∧
      (∀ M : ModuleCat.{a} (U k g), ObjectTransport h J (up.{u,v,max u v w a b c,a} M)) ∧
      (∀ N : ModuleCat.{b} (U k g), ObjectTransport h J (up.{u,v,max u v w a b c,b} N)) ∧
      (∀ (M : ModuleCat.{a} (U k g)) (N : ModuleCat.{b} (U k g)) (f : M →ₗ[U k g] N),
        let e := up.{u,v,max u v w a b c,a} M
        let e' := up.{u,v,max u v w a b c,b} N
        ExteriorNaturality Dg e e' f ∧
        ExteriorNaturality Dh (restrictEquiv h e) (restrictEquiv h e') (restrictOriginalMap h f) ∧
        SpectralNaturality h J e e' f ∧ IdealCoefficientNaturality h J e e' f ∧
        SpectralEdgeNaturality.{u,v,max w a b c,a,b} h (O := O) e e' f ∧
        ∀ j j', InvariantNaturality.{u,v,max w a b c,a,b} h e j e' f j')

end AdvancedHomologicalAlgebra.LieHochschildSerre.Original
