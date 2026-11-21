import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtTorDefinitions
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.HomFlatBaseChange
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! Finite resolutions, cochain comparison, flat cohomology, and natural
Ext base change for paper.tex 3202–3206, 3230–3248. These statements are
independent of the candidate implementation and use the existing ordinary
resolution and Ext interfaces. -/
namespace P103.Specs.Ch12.ExtBaseChange
universe u v w x
open P103.Specs.Ch10.ProjectiveResolutions

/-- Finite means degreewise finite; the resolution need not have finite length. -/
def exists_finite_free_resolutionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Type v) [AddCommGroup A] [Module R A] [Module.Finite R A],
    ∃ P : Resolution R A, P.IsFree ∧ ∀ n, Module.Finite R (P.complex.X n)

/-- The specified comparison is an isomorphism for each finite free term.
The target coefficient is arbitrary. -/
def finite_free_hom_bijectiveType : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    [Module.Flat R S] (P : Type w) [AddCommGroup P] [Module R P]
    [Module.Free R P] [Module.Finite R P]
    (B : Type x) [AddCommGroup B] [Module R B],
    Function.Bijective (P103.Specs.Ch04.HomFlatBaseChange.canonicalValue R S P B)


noncomputable section
open CategoryTheory Opposite TensorProduct

/-- Hom as an R-linear functor in the commutative-ring case. -/
def linearHomFunctor {R : Type u} [CommRing R]
    (B : Type x) [AddCommGroup B] [Module R B] :
    (ModuleCat.{w} R)ᵒᵖ ⥤ ModuleCat.{max w x} R where
  obj M := ModuleCat.of R (M.unop →ₗ[R] B)
  map f := ModuleCat.ofHom (f.unop.hom.lcomp R B)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

instance {R : Type u} [CommRing R] (B : Type x) [AddCommGroup B] [Module R B] :
    (linearHomFunctor (R := R) B : (ModuleCat.{w} R)ᵒᵖ ⥤ ModuleCat.{max w x} R).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    exact LinearMap.comp_add _ _ _

/-- This uses the same precomposition differential as the upstream integer
Hom complex, but retains the R-linear structure. -/
abbrev linearHomComplex {R : Type u} [CommRing R]
    (C : ChainComplex (ModuleCat.{w} R) ℕ)
    (B : Type x) [AddCommGroup B] [Module R B] :=
  ((linearHomFunctor B).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    ((HomologicalComplex.opFunctor (ModuleCat.{w} R) (ComplexShape.down ℕ)).obj (op C))

/-- Extension using the given algebra structure, with no change of its instances. -/
def scalarExtension (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    ModuleCat.{w} R ⥤ ModuleCat.{max v w} S where
  obj M := ModuleCat.of S (S ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.baseChange S)
  map_id _ := ModuleCat.hom_ext LinearMap.baseChange_id
  map_comp f g := ModuleCat.hom_ext (LinearMap.baseChange_comp _ _)

instance (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    (scalarExtension R S : ModuleCat.{w} R ⥤ ModuleCat.{max v w} S).Additive where
  map_add := by
    intro M N f g
    exact ModuleCat.hom_ext (LinearMap.baseChange_add _ _)

abbrev baseChangeComplex {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{w} R) c) :=
  ((scalarExtension R S).mapHomologicalComplex c).obj C

/-- A cochain comparison means existence of a cochain map with these specified
components; it is not an assumption of cochain compatibility. -/
def hom_cochain_comparisonType : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (C : ChainComplex (ModuleCat.{w} R) ℕ)
    (B : Type x) [AddCommGroup B] [Module R B],
    ∃ F : baseChangeComplex S (linearHomComplex C B) ⟶
      linearHomComplex (baseChangeComplex S C) (S ⊗[R] B),
      ∀ n, (F.f n).hom = P103.Specs.Ch04.HomFlatBaseChange.canonicalValue R S (C.X n) B

/-- Degreewise finite free terms give an isomorphism of cochain complexes. -/
def hom_cochain_isomorphismType : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    [Module.Flat R S] (C : ChainComplex (ModuleCat.{w} R) ℕ)
    (B : Type x) [AddCommGroup B] [Module R B],
    (∀ n, Module.Free R (C.X n)) → (∀ n, Module.Finite R (C.X n)) →
    ∃ F : baseChangeComplex S (linearHomComplex C B) ≅
      linearHomComplex (baseChangeComplex S C) (S ⊗[R] B),
      ∀ n, (F.hom.f n).hom = P103.Specs.Ch04.HomFlatBaseChange.canonicalValue R S (C.X n) B

open P103.Specs.Ch10.Complexes

/-- The canonical tensor of a cocycle, viewed as a cocycle after extension. -/
def baseChangeCycle {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{w} R) c)
    (n : ι) (s : S) (z : cycles C n) : cycles (baseChangeComplex S C) n :=
  ⟨s ⊗ₜ[R] z.val, by
    change (C.d n (c.next n)).hom.baseChange S (s ⊗ₜ[R] z.val) = 0
    rw [LinearMap.baseChange_tmul, show (C.d n (c.next n)).hom z.val = 0 from z.property,
      TensorProduct.tmul_zero]⟩

/-- Flat extension commutes with the existing explicit quotient homology,
with its canonical value specified on every tensor of a cycle class. -/
def flat_cohomologyType : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    [Module.Flat R S] {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{w} R) c) (n : ι),
    ∃ e : (S ⊗[R] Homology C n) ≃ₗ[S] Homology (baseChangeComplex S C) n,
      ∀ s z, e (s ⊗ₜ[R] homologyClass C n z) =
        homologyClass _ n (baseChangeCycle S C n s z)


section ResolutionExtension
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  [Module.Flat R S] {A : Type v} [AddCommGroup A] [Module R A]

/-- The scalar-extended ordinary resolution. Exactness follows directly from
flat tensor exactness, including the augmented degree zero. -/
def extendResolution (P : Resolution R A) : Resolution S (S ⊗[R] A) where
  complex := baseChangeComplex S P.complex
  ε := P.ε.baseChange S
  surjective := LinearMap.baseChange_surjective S P.surjective
  exact_zero := by
    ext x
    exact (Module.Flat.lTensor_exact S (LinearMap.exact_iff.mpr P.exact_zero.symm) x).symm
  exact_succ n := by
    ext x
    exact (Module.Flat.lTensor_exact S (LinearMap.exact_iff.mpr (P.exact_succ n).symm) x).symm

end ResolutionExtension

open P103.Specs.Ch10.Comparison P103.Specs.Ch11.ExtTorDefinitions

/-- The finite-free resolutions among the existing ordinary resolutions. -/
abbrev FiniteFreeChoice (R : Type u) [CommRing R] (A : ModuleCat.{v} R) :=
  {P : Resolution R A // P.IsFree ∧ ∀ n, Module.Finite R (P.complex.X n)}

/-- The existing projective-resolution interface, without changing its objects. -/
def FiniteFreeChoice.projective {R : Type u} [CommRing R] {A : ModuleCat.{v} R}
    (P : FiniteFreeChoice R A) : ProjectiveChoice R A :=
  ⟨P.val, fun n => by
    let : Module.Free R (P.val.complex.X n) := P.property.1 n
    exact Module.Projective.of_free⟩

/-- The specified Hom comparison applied to a cocycle is again a cocycle. -/
def homTensorCycle {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (C : ChainComplex (ModuleCat.{w} R) ℕ)
    (B : Type x) [AddCommGroup B] [Module R B]
    (n : ℕ) (s : S) (z : cycles (homComplex C B) n) :
    cycles (homComplex (baseChangeComplex S C) (S ⊗[R] B)) n :=
  ⟨P103.Specs.Ch04.HomFlatBaseChange.canonicalValue R S (C.X n) B (s ⊗ₜ[R] z.val), by
    change (P103.Specs.Ch04.HomFlatBaseChange.canonicalValue R S (C.X n) B
      (s ⊗ₜ[R] z.val)).comp ((C.d ((ComplexShape.up ℕ).next n) n).hom.baseChange S) = 0
    apply TensorProduct.AlgebraTensorModule.ext
    intro t p
    let f : C.X n →ₗ[R] B := z.val
    have hz : f ((C.d ((ComplexShape.up ℕ).next n) n).hom p) = 0 :=
      LinearMap.congr_fun z.property p
    change s • (t ⊗ₜ[R] f
      ((C.d ((ComplexShape.up ℕ).next n) n).hom p)) = 0
    rw [hz, TensorProduct.tmul_zero, smul_zero]⟩


/-- Extension preserves the finite-free resolution data, without Noetherianity
of S. Only exactness uses flatness. -/
def FiniteFreeChoice.extend {R : Type u} [CommRing R] (S : Type u) [CommRing S]
    [Algebra R S] [Module.Flat R S] {A : ModuleCat.{v} R}
    (P : FiniteFreeChoice R A) : FiniteFreeChoice S (ModuleCat.of S (S ⊗[R] A)) := by
  refine ⟨extendResolution S P.val, ?_, ?_⟩
  · intro n
    let : Module.Free R (P.val.complex.X n) := P.property.1 n
    change Module.Free S (S ⊗[R] P.val.complex.X n)
    infer_instance
  · intro n
    let : Module.Finite R (P.val.complex.X n) := P.property.2 n
    change Module.Finite S (S ⊗[R] P.val.complex.X n)
    infer_instance

/-- The isomorphism is between the existing Ext objects, with the existing
coefficient actions. The representative formula makes its construction canonical. -/
structure ExtComparison {R : Type u} [CommRing R] (S : Type u) [CommRing S]
    [Algebra R S] [Module.Flat R S] {n : ℕ}
    (ER : ExtMaps.{u,v,w} R n) (ES : ExtMaps.{u,max u v,max u w} S n)
    {A : ModuleCat.{v} R} (P : FiniteFreeChoice R A) (B : ModuleCat.{w} R) where
  equiv :
    letI : Module R (ExtWith P.val B n) := extModule ER P.projective B
    letI : Module S (ExtWith (extendResolution S P.val) (S ⊗[R] B) n) :=
      extModule ES (P.extend S).projective (ModuleCat.of S (S ⊗[R] B))
    (S ⊗[R] ExtWith P.val B n) ≃ₗ[S] ExtWith (extendResolution S P.val) (S ⊗[R] B) n
  formula :
    letI : Module R (ExtWith P.val B n) := extModule ER P.projective B
    ∀ s (z : cycles (homComplex P.val.complex B) n),
      equiv.toFun (s ⊗ₜ[R] homologyClass _ n z) =
        homologyClass _ n (homTensorCycle S P.val.complex B n s z)

/-- This is the source theorem with its original Noetherian and finite-A
hypotheses. The resolution witness is ordinary and finite free in every degree. -/
def ext_base_changeType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Module.Flat R S]
    (A : ModuleCat.{v} R) [Module.Finite R A] (B : ModuleCat.{w} R) (n : ℕ)
    (ER : ExtMaps.{u,v,w} R n) (ES : ExtMaps.{u,max u v,max u w} S n),
    ∃ P : FiniteFreeChoice R A, Nonempty (ExtComparison S ER ES P B)

/-- Simultaneous naturality in the contravariant and covariant variables.
The equation on all pure tensors specifies the equality of S-linear maps.
Identity coefficient maps give the resolution-comparison diagram. -/
def ext_naturalityType : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    [Module.Flat R S] (n : ℕ)
    (ER : ExtMaps.{u,v,w} R n) (ES : ExtMaps.{u,max u v,max u w} S n)
    {A A' : ModuleCat.{v} R} (P : FiniteFreeChoice R A) (Q : FiniteFreeChoice R A')
    {B B' : ModuleCat.{w} R} (f : A' ⟶ A) (g : B ⟶ B')
    (l : Q.val.complex ⟶ P.val.complex), ChainLift Q.val P.val f.hom l →
    ∀ (eP : ExtComparison S ER ES P B) (eQ : ExtComparison S ER ES Q B'),
    letI : Module R (ExtWith P.val B n) := extModule ER P.projective B
    letI : Module R (ExtWith Q.val B' n) := extModule ER Q.projective B'
    ∀ (s : S) (x : ExtWith P.val B n), eQ.equiv.toFun (s ⊗ₜ[R] ER.map P.projective Q.projective f g x) =
      ES.map (P.extend S).projective (Q.extend S).projective
        ((scalarExtension R S).map f) ((scalarExtension R S).map g)
        (eP.equiv.toFun (s ⊗ₜ[R] x))


/-- Naturality for the canonical groups of any two already constructed ordinary
Ext theories. This explicitly transports out of the chosen finite free resolution. -/
structure CanonicalComparison {R : Type u} [CommRing R] (S : Type u) [CommRing S]
    [Algebra R S] [Module.Flat R S]
    (TR : CanonicalTheory.{u,v,w} R)
    (TS : CanonicalTheory.{u,max u v,max u w} S) (n : ℕ) where
  equiv : ∀ (A : ModuleCat.{v} R) [Module.Finite R A] (B : ModuleCat.{w} R),
    letI : Module R (TR.Ext A B n) := extModule (TR.extMaps n) (TR.leftResolutions A) B
    letI : Module S (TS.Ext (ModuleCat.of S (S ⊗[R] A)) (ModuleCat.of S (S ⊗[R] B)) n) :=
      extModule (TS.extMaps n) (TS.leftResolutions (ModuleCat.of S (S ⊗[R] A)))
        (ModuleCat.of S (S ⊗[R] B))
    (S ⊗[R] TR.Ext A B n) ≃ₗ[S]
      TS.Ext (ModuleCat.of S (S ⊗[R] A)) (ModuleCat.of S (S ⊗[R] B)) n
  naturality : ∀ {A A' : ModuleCat.{v} R} [Module.Finite R A] [Module.Finite R A']
      {B B' : ModuleCat.{w} R} (f : A' ⟶ A) (g : B ⟶ B'),
    letI : Module R (TR.Ext A B n) := extModule (TR.extMaps n) (TR.leftResolutions A) B
    letI : Module R (TR.Ext A' B' n) := extModule (TR.extMaps n) (TR.leftResolutions A') B'
    ∀ (s : S) (x : TR.Ext A B n),
      (equiv A' B').toFun (s ⊗ₜ[R] TR.extMap n f g x) =
        TS.extMap n ((scalarExtension R S).map f) ((scalarExtension R S).map g)
          ((equiv A B).toFun (s ⊗ₜ[R] x))

def canonical_ext_base_changeType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Module.Flat R S]
    (TR : CanonicalTheory.{u,v,w} R) (TS : CanonicalTheory.{u,max u v,max u w} S) (n : ℕ),
    Nonempty (CanonicalComparison S TR TS n)

end
end P103.Specs.Ch12.ExtBaseChange
