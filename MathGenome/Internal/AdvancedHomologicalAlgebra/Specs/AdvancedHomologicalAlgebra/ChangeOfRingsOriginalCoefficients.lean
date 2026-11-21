import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ChangeOfRingsTor
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TorBalance
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.ModuleCat.Subobject

/-! Carrier comparisons for HA-B07. The resolutions and the modules they
resolve can have independently sized carriers. -/
noncomputable section

open CategoryTheory
open P103.Specs.Ch10
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.BalancedTensor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsOriginalCoefficients

universe u v w x y z i

abbrev TermMap := @TorBalance.LinearChainMap

namespace TermMap

variable {R : Type u} [Ring R] {I : Type i} {c : ComplexShape I}
variable {C : HomologicalComplex (ModuleCat.{v} R) c}
variable {D : HomologicalComplex (ModuleCat.{w} R) c}
variable {E : HomologicalComplex (ModuleCat.{x} R) c}

theorem comm_apply (f : TermMap C D) (m n : I) (a : C.X m) :
    (D.d m n).hom (f.app m a) = f.app n ((C.d m n).hom a) :=
  DFunLike.congr_fun (f.comm m n) a

def id (C : HomologicalComplex (ModuleCat.{v} R) c) : TermMap C C where
  app _ := LinearMap.id
  comm _ _ := rfl

def comp (g : TermMap D E) (f : TermMap C D) : TermMap C E where
  app n := (g.app n).comp (f.app n)
  comm m n := LinearMap.ext fun a => by
    change (E.d m n).hom (g.app m (f.app m a)) = g.app n (f.app n ((C.d m n).hom a))
    rw [comm_apply g, comm_apply f]

def ofHom {D : HomologicalComplex (ModuleCat.{v} R) c} (f : C ⟶ D) :
    TermMap C D where
  app n := (f.f n).hom
  comm m n := congrArg ModuleCat.Hom.hom (f.comm m n)

def toHom {D : HomologicalComplex (ModuleCat.{v} R) c} (f : TermMap C D) :
    C ⟶ D where
  f n := ModuleCat.ofHom (f.app n)
  comm' m n _ := ModuleCat.hom_ext (f.comm m n)

end TermMap

/-- A chain or cochain equivalence between distinct carrier universes. -/
structure TermIso {R : Type u} [Ring R] {I : Type i} {c : ComplexShape I}
    (C : HomologicalComplex (ModuleCat.{v} R) c)
    (D : HomologicalComplex (ModuleCat.{w} R) c) where
  app : ∀ n, C.X n ≃ₗ[R] D.X n
  comm : ∀ m n a, (D.d m n).hom (app m a) = app n ((C.d m n).hom a)

namespace TermIso

variable {R : Type u} [Ring R] {I : Type i} {c : ComplexShape I}
variable {C : HomologicalComplex (ModuleCat.{v} R) c}
variable {D : HomologicalComplex (ModuleCat.{w} R) c}

def hom (e : TermIso C D) : TermMap C D :=
  ⟨fun n => (e.app n).toLinearMap, fun m n => LinearMap.ext (e.comm m n)⟩

def symm (e : TermIso C D) : TermIso D C where
  app n := (e.app n).symm
  comm m n a := by
    apply (e.app n).injective
    rw [LinearEquiv.apply_symm_apply, ← e.comm, LinearEquiv.apply_symm_apply]

end TermIso

/-- The common augmented resolution interface, also used for Tor balance. -/
abbrev AugmentedResolution := @TorBalance.AugmentedResolution

namespace AugmentedResolution
variable {R : Type u} [Ring R] {A : Type v} {B : Type w}
variable [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

abbrev ofP103 (P : LeftResolution R A) (h : P.IsProjective) :
    AugmentedResolution.{u,v,max u v} R A :=
  TorBalance.AugmentedResolution.ofP103 P h

abbrev Lifts (P : AugmentedResolution.{u,v,x} R A) (Q : AugmentedResolution.{u,w,y} R B)
    (g : A →ₗ[R] B) (l : TermMap P.complex Q.complex) : Prop :=
  TorBalance.AugmentedResolution.Lifts P Q g l
end AugmentedResolution

abbrev resolutionTor {R : Type u} [Ring R] {A : Type v}
    [AddCommGroup A] [Module Rᵐᵒᵖ A] (P : AugmentedResolution.{u,v,w} Rᵐᵒᵖ A)
    (B : Type x) [AddCommGroup B] [Module R B] (n : ℕ) :=
  Homology (tensorComplex P.complex B) n

section Lifting

variable {R : Type u} [Ring R] {A : Type v} {B : Type w}
variable [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-- The scalar-preserving copy uses the original ring at every universe level. -/
abbrev carrierUp (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A] :
    A ≃ₗ[R] ULift.{z} A := ULift.moduleEquiv.symm

/-- Conjugation also applies to a map between two different carrier universes. -/
def conjugate (g : A →ₗ[R] B) (eA : A ≃ₗ[R] ULift.{x} A)
    (eB : B ≃ₗ[R] ULift.{y} B) : ULift.{x} A →ₗ[R] ULift.{y} B :=
  eB.toLinearMap.comp (g.comp eA.symm.toLinearMap)

variable {I : Type i} {c : ComplexShape I}

abbrev liftComplex (C : HomologicalComplex (ModuleCat.{v} R) c) :=
  ((ModuleCat.uliftFunctor.{z,v} R).mapHomologicalComplex c).obj C

def liftComplexIso (C : HomologicalComplex (ModuleCat.{v} R) c) :
    TermIso C (liftComplex.{u,v,z,i} C) where
  app n := carrierUp R (C.X n)
  comm _ _ _ := rfl

/-- The lifted augmented resolution has the exact lifted term complex and
the augmentation obtained by conjugating the original augmentation. -/
structure LiftedResolutionData (P : AugmentedResolution.{u,v,w} R A) where
  resolution : LeftResolution R (ULift.{max u w z} A)
  complex_eq : resolution.complex = liftComplex.{u,w,max u v z,0} P.complex
  augmentation_eq : ∀ a,
    resolution.ε ((eqToHom complex_eq.symm).f 0 |>.hom (ULift.up a)) = ULift.up (P.ε a)
  projective : resolution.IsProjective

def ResolutionLiftType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A]
    (P : AugmentedResolution.{u,v,w} R A), Nonempty (LiftedResolutionData.{u,v,w,z} P)

def ResolutionExistenceType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A],
    Nonempty (AugmentedResolution.{u,v,max u v z} R A)

end Lifting

section Tensor

variable {R : Type u} [Ring R] {A : Type v} {B : Type w} {A' : Type x} {B' : Type y}
variable [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup A'] [Module Rᵐᵒᵖ A']
variable [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']

/-- Signed total transports use this ordinary map of the two balanced factors
on each summand. -/
def TensorEquivType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) (B : Type w) (A' : Type x) (B' : Type y)
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup A'] [Module Rᵐᵒᵖ A']
    [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (a : A ≃ₗ[Rᵐᵒᵖ] A') (b : B ≃ₗ[R] B'),
    ∃ e : Tensor R A B ≃ₗ[ℤ] Tensor R A' B',
      (∀ x y, e (tmul R x y) = tmul R (a x) (b y)) ∧
      (∀ x y, e.symm (tmul R x y) = tmul R (a.symm x) (b.symm y))

end Tensor

section Total

open P103.Specs.Ch11.TorBalance
variable {R : Type u} [Ring R]

/-- Increasing row filtration on the original signed sum total. Its first
index is the degree in the left resolution. -/
def rowPiece (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (a : ℤ) (n : ℕ) :
    Submodule ℤ ((ordinaryTotal C D).X n) :=
  ⨆ k : { ij : ℕ × ℕ // ij.1 + ij.2 = n ∧ (ij.2 : ℤ) ≤ a },
    LinearMap.range (ordinaryInclusion C D k.1.1 k.1.2 n k.2.1)

variable {C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
variable {D : ChainComplex (ModuleCat.{w} R) ℕ}
variable {C' : ChainComplex (ModuleCat.{x} Rᵐᵒᵖ) ℕ}
variable {D' : ChainComplex (ModuleCat.{y} R) ℕ}

/-- The comparison is an equivalence of the signed totals and preserves the
row pieces. The summand formula fixes its normalization. -/
structure TotalTransport (a : TermIso C C') (b : TermIso D D') where
  iso : TermIso (ordinaryTotal C D) (ordinaryTotal C' D')
  on_tensor : ∀ i j n (h : i + j = n) (x : C.X i) (y : D.X j),
    iso.app n (ordinaryInclusion C D i j n h (tmul R x y)) =
      ordinaryInclusion C' D' i j n h (tmul R (a.app i x) (b.app j y))
  row : ∀ p n, (rowPiece C D p n).map (iso.app n).toLinearMap = rowPiece C' D' p n

def TotalTransportType : Prop :=
  ∀ (R : Type u) [Ring R]
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ)
    (C' : ChainComplex (ModuleCat.{x} Rᵐᵒᵖ) ℕ)
    (D' : ChainComplex (ModuleCat.{y} R) ℕ)
    (a : TermIso C C') (b : TermIso D D'), Nonempty (TotalTransport a b)

end Total


section QuotientTransport

open ChangeOfRingsTor
variable {R : Type u} {S : Type v} [Ring R] [Ring S]
variable (f : R →+* S)
variable {C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ}
variable {D : ChainComplex (ModuleCat.{x} Rᵐᵒᵖ) ℕ}

/-- A right S-module structure on the actual inner Tor quotient, normalized
using the complex with the original right multiplication on S. -/
structure InnerQuotient (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ) where
  model : InnerHomologyData f C
  action : ∀ q, Module Sᵐᵒᵖ (Homology (tensorComplex C (Restricted f S)) q)
  linear : ∀ q, letI := action q
    ∀ (s : Sᵐᵒᵖ) z, model.homologyEquiv q (s • z) = s • model.homologyEquiv q z

/-- The same additive transport is linear over the right S action and has
the specified formula on the quotient of original cycles. -/
structure InnerTransport (e : TermIso C D) (P : InnerQuotient f C)
    (Q : InnerQuotient f D) where
  terms : TermIso P.model.complex Q.model.complex
  pure_tensor : ∀ n x s,
    Q.model.termEquiv n ((terms.app n) ((P.model.termEquiv n).symm
      (tmul R x (Restricted.of f S s)))) =
    tmul R (e.app n x) (Restricted.of f S s)
  quotient : ∀ q, letI := P.action q; letI := Q.action q
    Homology (tensorComplex C (Restricted f S)) q ≃ₗ[Sᵐᵒᵖ]
      Homology (tensorComplex D (Restricted f S)) q
  quotient_class : ∀ q (z : cycles (tensorComplex C (Restricted f S)) q),
    ∃ t : cycles (tensorComplex D (Restricted f S)) q,
      t.val = tensorMap (e.app q).toLinearMap LinearMap.id z.val ∧
      quotient q (homologyClass (tensorComplex C (Restricted f S)) q z) =
        homologyClass (tensorComplex D (Restricted f S)) q t

def InnerTransportType : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S)
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{x} Rᵐᵒᵖ) ℕ) (e : TermIso C D),
    ∃ (P : InnerQuotient f C) (Q : InnerQuotient f D), Nonempty (InnerTransport f e P Q)

end QuotientTransport


section Restriction

open ChangeOfRingsTor

variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
variable {A : Type w} {B : Type x} [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]

/-- Exact scalar restriction gives the same underlying map for heterogeneous carriers. -/
def restrictLinear (g : A →ₗ[S] B) : Restricted f A →ₗ[R] Restricted f B where
  toFun := g
  map_add' := g.map_add
  map_smul' r := g.map_smul (f r)

def restrictEquiv (e : A ≃ₗ[S] B) : Restricted f A ≃ₗ[R] Restricted f B where
  __ := restrictLinear f e.toLinearMap
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv

theorem restrict_lift_smul (r : R) (a : A) :
    (r • (Restricted.of f (ULift.{z} A) (ULift.up a))).down =
       Restricted.val f A (r • Restricted.of f A a) := rfl

variable {I : Type i} {c : ComplexShape I}
variable {C : HomologicalComplex (ModuleCat.{w} S) c}
variable {D : HomologicalComplex (ModuleCat.{x} S) c}

def restrictChainMap (l : TermMap C D) :
    TermMap (restrictionComplex f c C) (restrictionComplex f c D) where
  app n := restrictLinear f (A := C.X n) (B := D.X n) (l.app n)
  comm m n := LinearMap.ext (TermMap.comm_apply l m n)

def restrictChainIso (e : TermIso C D) :
    TermIso (restrictionComplex f c C) (restrictionComplex f c D) where
  app n := restrictEquiv f (A := C.X n) (B := D.X n) (e.app n)
  comm m n := e.comm m n

end Restriction

section TargetTransport

open ChangeOfRingsTor P103.Specs.Ch11.TorBalance
universe a b c d
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
variable {A : Type a} {M : Type b} {A' : Type c} {M' : Type (max u v d)}
variable [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup M] [Module S M]
variable [AddCommGroup A'] [Module Rᵐᵒᵖ A'] [AddCommGroup M'] [Module S M']
variable {P : AugmentedResolution.{u,a,w} Rᵐᵒᵖ A} {Q : AugmentedResolution.{v,b,x} S M}
variable {P' : LeftResolution Rᵐᵒᵖ A'} {Q' : LeftResolution S M'}

/-- A comparison with the actual degree-zero augmentation on the original
complex, including its effect on representatives of the resulting Tor quotient. -/
structure TargetTransport
    (e : TermIso P.complex P'.complex)
    (e' : TermIso Q.complex Q'.complex) (m : M ≃ₗ[S] M')
    (T : TargetComparisonData.{u,v,c,d} f A' M' P' Q') where
  total : TotalTransport e (restrictChainIso f e')
  tensor : TermIso (tensorComplex P.complex (Restricted f M))
    (tensorComplex P'.complex (Restricted f M'))
  tensor_formula : ∀ n x y, tensor.app n (tmul R x y) =
    tmul R (e.app n x) (restrictEquiv f m y)
  augmentation : TermMap
    (ordinaryTotal P.complex (restrictionComplex f (ComplexShape.down ℕ) Q.complex))
    (tensorComplex P.complex (Restricted f M))
  augmentation_zero : ∀ n (x : P.complex.X n) (y : Q.complex.X 0),
    (augmentation.app n) (ordinaryInclusion P.complex
      (restrictionComplex f (ComplexShape.down ℕ) Q.complex) n 0 n (Nat.add_zero n)
      (tmul R x (Restricted.of f (Q.complex.X 0) y))) =
    tmul R x (Restricted.of f M (Q.ε y))
  augmentation_positive : ∀ i j n (h : i+j=n), j ≠ 0 →
    (augmentation.app n).comp (ordinaryInclusion P.complex
      (restrictionComplex f (ComplexShape.down ℕ) Q.complex) i j n h) = 0
  augmentation_square : ∀ n z, (T.augmentation.f n).hom (total.iso.app n z) =
    tensor.app n ((augmentation.app n) z)
  quasi : ∀ n, ∃ e : Homology
    (ordinaryTotal P.complex (restrictionComplex f (ComplexShape.down ℕ) Q.complex)) n ≃+
      resolutionTor P (Restricted f M) n,
    ∀ z : cycles (ordinaryTotal P.complex
      (restrictionComplex f (ComplexShape.down ℕ) Q.complex)) n,
      ∃ t : cycles (tensorComplex P.complex (Restricted f M)) n,
        t.val = augmentation.app n z.val ∧ e (homologyClass _ n z) = homologyClass _ n t
  quotient : ∀ n, resolutionTor P (Restricted f M) n ≃ₗ[ℤ] TorWith P' (Restricted f M') n
  quotient_class : ∀ n (z : cycles (tensorComplex P.complex (Restricted f M)) n),
    ∃ t : cycles (tensorComplex P'.complex (Restricted f M')) n,
      t.val = tensor.app n z.val ∧
      quotient n (homologyClass _ n z) = homologyClass _ n t

end TargetTransport


section OriginalSequence

open ChangeOfRingsTor DoubleTotalization
universe a b
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
variable {A : Type a} {M : Type b}
variable [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup M] [Module S M]
variable (P : AugmentedResolution.{u,a,w} Rᵐᵒᵖ A)
variable (Q : AugmentedResolution.{v,b,x} S M)

/-- Common ambient resolutions over the same rings, including the actual
coefficient lifts and the termwise lifted augmentations. -/
structure AmbientPair where
  pair : ResolutionPair.{u,v,max u v a b w x z,max u v a b w x z} f
    (ModuleCat.of Rᵐᵒᵖ (ULift.{max u v b w x z} A))
    (ModuleCat.of S (ULift.{max u v a w x z} M))
  rightTerm : TermIso P.complex pair.right.complex
  leftTerm : TermIso Q.complex pair.left.complex
  rightComplex : pair.right.complex = liftComplex.{u,w,max u v a b x z,0} P.complex
  leftComplex : pair.left.complex = liftComplex.{v,x,max u v a b w z,0} Q.complex
  rightUp : ∀ n t, ((eqToHom rightComplex).f n).hom (rightTerm.app n t) = ULift.up t
  leftUp : ∀ n t, ((eqToHom leftComplex).f n).hom (leftTerm.app n t) = ULift.up t
  rightAugmentation : ∀ a, pair.right.ε (rightTerm.app 0 a) = ULift.up (P.ε a)
  leftAugmentation : ∀ m, pair.left.ε (leftTerm.app 0 m) = ULift.up (Q.ε m)

variable {P Q}

/-- The E² comparison uses any chosen original right S resolution together
with its augmentation rebased by the right S-linear inner Tor comparison. -/
structure OuterTransport (L : AmbientPair.{u,v,w,x,max y z,a,b} f P Q)
    (q : ℕ)
    [Module Sᵐᵒᵖ (resolutionTor P (Restricted f S) q)]
    [Module Sᵐᵒᵖ (TorWith L.pair.right (Restricted f S) q)]
    (e : resolutionTor P (Restricted f S) q ≃ₗ[Sᵐᵒᵖ] TorWith L.pair.right (Restricted f S) q)
    (U : AugmentedResolution.{v,max w v,y} Sᵐᵒᵖ (resolutionTor P (Restricted f S) q)) where
  ambient : LeftResolution Sᵐᵒᵖ (TorWith L.pair.right (Restricted f S) q)
  projective : ambient.IsProjective
  terms : TermIso U.complex ambient.complex
  complex_eq : ambient.complex = liftComplex.{v,y,max u v a b w x z,0} U.complex
  on_terms : ∀ n t,
    ((eqToHom complex_eq).f n).hom (terms.app n t) = ULift.up t
  aug : ∀ t, ambient.ε (terms.app 0 t) = e (U.ε t)
  tensor : TermIso (tensorComplex U.complex M)
    (tensorComplex ambient.complex (ULift.{max u v a w x y z} M))
  pure_tensor : ∀ n t m, tensor.app n (tmul S t m) =
    tmul S (terms.app n t) (ULift.up m)
  quotient : ∀ p, resolutionTor U M p ≃ₗ[ℤ]
    TorWith ambient (ULift.{max u v a w x y z} M) p
  quotient_class : ∀ p (z : cycles (tensorComplex U.complex M) p),
    ∃ t : cycles (tensorComplex ambient.complex (ULift.{max u v a w x y z} M)) p,
      t.val = tensor.app p z.val ∧
      quotient p (homologyClass _ p z) = homologyClass _ p t


/-- Use the inner complex and action of the same ambient sequence whose pages
are being transported. -/
def resolvedInner
    {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}
    {L : ResolutionPair.{u,v,w,x} f A M}
    (E : Resolved.{u,v,w,x} f A M L) : InnerQuotient f L.right.complex where
  model := E.inner
  action := E.innerModule
  linear := E.innerLinear

/-- The sequence on a particular pair of original resolutions. All Tor
identifications use those same augmented resolutions and the original S-action. -/
structure OriginalSequenceData
    (system : NaturalSystem.{u,v,max u v a b w x y z,max u v a b w x y z} f) where
  lift : AmbientPair.{u,v,w,x,max y z,a,b} f P Q
  originalInner : InnerQuotient f P.complex
  inner : InnerTransport f lift.rightTerm originalInner (resolvedInner f (system.sequence lift.pair))
  target : TargetTransport f lift.rightTerm lift.leftTerm
    (carrierUp.{v,b,max u v a w x y z} S M) (system.sequence lift.pair).augmentation
  outer : ∀ q,
    letI := originalInner.action q
    letI := (system.sequence lift.pair).innerModule q
    ∀ U : AugmentedResolution.{v,max w v,y} Sᵐᵒᵖ (resolutionTor P (Restricted f S) q),
      OuterTransport.{u,v,w,x,y,z,a,b} f lift q (inner.quotient q) U

namespace OriginalSequenceData

variable {T : NaturalSystem.{u,v,max u v a b w x y z,max u v a b w x y z} f}
variable (V : OriginalSequenceData.{u,v,w,x,y,z,a,b} f (P := P) (Q := Q) T)

abbrev pages := T.sequence V.lift.pair

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in
/-- The second page identifies with the P103 quotient of the original outer
right resolution after using its specified lifted augmentation. -/
def secondEquiv (p q : ℕ) :
    letI := V.originalInner.action q
    ∀ U : AugmentedResolution.{v,max w v,y} Sᵐᵒᵖ (resolutionTor P (Restricted f S) q),
      ↥(chainPage (V := ModuleCat.{max u v a b w x y z} ℤ)
        (V.pages f).filtration (V.pages f).pages 2 p (p+q)) ≃ₗ[ℤ]
        resolutionTor U M p := by
  letI := V.originalInner.action q
  letI := (V.pages f).innerModule q
  intro U
  let O := V.outer q U
  exact (((V.pages f).secondIso p q O.ambient O.projective).toLinearEquiv).trans
    (O.quotient p).symm

/-- The original abutment is the quotient on P ⊗ᵣ Res(M).
The final carrier lift permits a categorical subobject of that same quotient. -/
def targetIso (n : ℕ) :
    (sumTotal (tensorCochainBicomplex V.lift.pair.right.complex
      (restrictionResolution f _ V.lift.pair.left).complex)).homology (-(n : ℤ)) ≅
    ModuleCat.of ℤ (ULift.{max u v a b w x y z} (resolutionTor P (Restricted f M) n)) :=
  (V.pages f).targetIso n ≪≫
    (((V.target.quotient n).symm.trans (carrierUp ℤ _)).toModuleIso)

def targetPiece (p : ℤ) (n : ℕ) :
    Subobject (ModuleCat.of ℤ (ULift.{max u v a b w x y z} (resolutionTor P (Restricted f M) n))) :=
  Subobject.mapIsoToOrderIso (V.targetIso f n) (chainTargetPiece (V.pages f).filtration p n)

/-- The same filtration on the unlifted Tor group, via the actual carrier
equivalence over the integers. -/
def targetSubmoduleOrder (n : ℕ) :
    Subobject (ModuleCat.of ℤ (ULift.{max u v a b w x y z} (resolutionTor P (Restricted f M) n)))
      ≃o Submodule ℤ (resolutionTor P (Restricted f M) n) :=
  (ModuleCat.subobjectModule _).trans
    (Submodule.orderIsoMapComap (carrierUp.{0,max w b,max u v a b w x y z} ℤ _)).symm

def targetSubmodule (p : ℤ) (n : ℕ) : Submodule ℤ (resolutionTor P (Restricted f M) n) :=
  targetSubmoduleOrder.{u,v,w,x,y,z,a,b} (P := P) (M := M) f n (V.targetPiece f p n)

end OriginalSequenceData

/-- For each pair of original choices, the target filtration is finite and
the actual successive quotients agree with the stabilized pages. -/
structure OriginalLimitData
    {T : NaturalSystem.{u,v,max u v a b w x y z,max u v a b w x y z} f}
    (V : OriginalSequenceData.{u,v,w,x,y,z,a,b} f (P := P) (Q := Q) T) :
    Prop where
  increasing : ∀ p n, V.targetPiece f (p-1) n ≤ V.targetPiece f p n
  finite : ∀ n, ∃ a b : ℤ, (∀ p, p ≤ a → V.targetPiece f p n = ⊥) ∧
    (∀ p, b ≤ p → V.targetPiece f p n = ⊤)
  limit : ∀ (n : ℕ) (r p : ℤ), 0 ≤ r →
    FiniteFiltrationConvergence.Stabilized (V.pages f).filtration r (-p) (-(n : ℤ)) →
    Nonempty (chainPage (V.pages f).filtration (V.pages f).pages r p (n : ℤ) ≅
      Limits.cokernel (Subobject.ofLE (V.targetPiece f (p-1) n)
        (V.targetPiece f p n) (increasing p n)))

def OriginalSequenceType : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S)
    (A : Type a) (M : Type b) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup M] [Module S M]
    (P : AugmentedResolution.{u,a,w} Rᵐᵒᵖ A)
    (Q : AugmentedResolution.{v,b,x} S M),
    ∃ (T : NaturalSystem.{u,v,max u v a b w x y z,max u v a b w x y z} f)
      (V : OriginalSequenceData.{u,v,w,x,y,z,a,b} f (P := P) (Q := Q) T),
      OriginalLimitData f V

/-- A genuine cycle of the original signed total represents the corresponding
ambient homology class after the specified tensor lift and inverse regrading.
The abutment sends it to the original augmentation class in the P103 quotient. -/
def TargetRepresentativesType : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S)
    (A : Type a) (M : Type b) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup M] [Module S M]
    (P : AugmentedResolution.{u,a,w} Rᵐᵒᵖ A)
    (Q : AugmentedResolution.{v,b,x} S M)
    (T : NaturalSystem.{u,v,max u v a b w x y z,max u v a b w x y z} f)
    (V : OriginalSequenceData.{u,v,w,x,y,z,a,b} f T (P := P) (Q := Q))
    (n : ℕ) (z : cycles (P103.Specs.Ch11.TorBalance.ordinaryTotal P.complex
      (restrictionComplex f (ComplexShape.down ℕ) Q.complex)) n),
    let C := V.lift.pair.right.complex
    let D := (restrictionResolution f _ V.lift.pair.left).complex
    let O := P103.Specs.Ch11.TorBalance.ordinaryTotal C D
    let K := sumTotal (tensorCochainBicomplex C D)
    ∃ (z' : cycles K (-(n : ℤ))) (t : cycles (tensorComplex P.complex (Restricted f M)) n),
      z'.val = ((V.pages f).totalRegrading.iso.inv.f (-(n : ℤ))).hom
        ((O.extendXIso negativeChainEmbedding (i := n) rfl).inv.hom
          (V.target.total.iso.app n z.val)) ∧
      t.val = V.target.augmentation.app n z.val ∧
      ((V.targetIso f n).hom).hom (explicitClass K (-(n : ℤ)) z') =
        ULift.up (homologyClass (tensorComplex P.complex (Restricted f M)) n t)

/-- The convergence comparison on the actual successive submodule
quotient of the original Tor group. -/
def UnliftedLimitType : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S)
    (A : Type a) (M : Type b) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup M] [Module S M]
    (P : AugmentedResolution.{u,a,w} Rᵐᵒᵖ A)
    (Q : AugmentedResolution.{v,b,x} S M)
    (T : NaturalSystem.{u,v,max u v a b w x y z,max u v a b w x y z} f)
    (V : OriginalSequenceData.{u,v,w,x,y,z,a,b} f (P := P) (Q := Q) T),
    (∀ p n, V.targetSubmodule f (p-1) n ≤ V.targetSubmodule f p n) ∧
    (∀ n, ∃ lo hi : ℤ, (∀ p, p ≤ lo → V.targetSubmodule f p n = ⊥) ∧
      (∀ p, hi ≤ p → V.targetSubmodule f p n = ⊤)) ∧
    ∀ (n : ℕ) (r p : ℤ), 0 ≤ r →
      FiniteFiltrationConvergence.Stabilized (V.pages f).filtration r (-p) (-(n : ℤ)) →
      Nonempty (↥(chainPage (V := ModuleCat.{max u v a b w x y z} ℤ)
        (V.pages f).filtration (V.pages f).pages r p (n : ℤ)) ≃ₗ[ℤ]
        V.targetSubmodule f p n ⧸
          ((V.targetSubmodule f (p-1) n).comap (V.targetSubmodule f p n).subtype))

end OriginalSequence


section Naturality

open ChangeOfRingsTor DoubleTotalization
universe a b a' b' w' x' y'

variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
variable {A : ModuleCat.{a} Rᵐᵒᵖ} {M : ModuleCat.{b} S}
variable {A' : ModuleCat.{a'} Rᵐᵒᵖ} {M' : ModuleCat.{b'} S}
variable {P : AugmentedResolution.{u,a,w} Rᵐᵒᵖ A} {Q : AugmentedResolution.{v,b,x} S M}
variable {P' : AugmentedResolution.{u,a',w'} Rᵐᵒᵖ A'}
variable {Q' : AugmentedResolution.{v,b',x'} S M'}

variable {T : NaturalSystem.{u,v,max u v a b w x y a' b' w' x' y' z,max u v a b w x y a' b' w' x' y' z} f}
variable (V : OriginalSequenceData.{u,v,w,x,y,max a' b' w' x' y' z,a,b} f (P := P) (Q := Q) T)
variable (V' : OriginalSequenceData.{u,v,w',x',y',max a b w x y z,a',b'} f (P := P') (Q := Q') T)

/-- The given original maps use literal carrier conjugation in the ambient category. -/
def ambientRightMap (g : A →ₗ[Rᵐᵒᵖ] A') :
    ModuleCat.of Rᵐᵒᵖ (ULift.{max u v b w x y a' b' w' x' y' z} A) ⟶
      ModuleCat.of Rᵐᵒᵖ (ULift.{max u v b' w' x' y' a b w x y z} A') :=
  ModuleCat.ofHom (conjugate g (carrierUp _ _) (carrierUp _ _))

def ambientLeftMap (h : M →ₗ[S] M') :
    ModuleCat.of S (ULift.{max u v a w x y a' b' w' x' y' z} M) ⟶
      ModuleCat.of S (ULift.{max u v a' w' x' y' a b w x y z} M') :=
  ModuleCat.ofHom (conjugate h (carrierUp _ _) (carrierUp _ _))

def ambientTargetMap (n : ℕ)
    (g : resolutionTor P (Restricted f M) n →ₗ[ℤ] resolutionTor P' (Restricted f M') n) :
    ModuleCat.of ℤ (ULift.{max u v a b w x y a' b' w' x' y' z}
      (resolutionTor P (Restricted f M) n)) ⟶
    ModuleCat.of ℤ (ULift.{max u v a b w x y a' b' w' x' y' z}
      (resolutionTor P' (Restricted f M') n)) :=
  ModuleCat.ofHom (conjugate g (carrierUp _ _) (carrierUp _ _))

open P103.Specs.Ch11.TorBalance

/-- Coefficient maps and every augmented comparison lift give the actual
signed-total map, the corresponding page maps, and the map on the original
abutment quotient. -/
structure TargetNaturality
    (g : A →ₗ[Rᵐᵒᵖ] A') (h : M →ₗ[S] M')
    (l : TermMap P.complex P'.complex) (m : TermMap Q.complex Q'.complex) where
  ambientRight : V.lift.pair.right.complex ⟶ V'.lift.pair.right.complex
  ambientLeft : V.lift.pair.left.complex ⟶ V'.lift.pair.left.complex
  termwise_right : ∀ n a, (ambientRight.f n).hom (V.lift.rightTerm.app n a) =
    V'.lift.rightTerm.app n (l.app n a)
  termwise_left : ∀ n a, (ambientLeft.f n).hom (V.lift.leftTerm.app n a) =
    V'.lift.leftTerm.app n (m.app n a)
  aug_right : ChainLift V.lift.pair.right V'.lift.pair.right
    (ambientRightMap.{u,v,w,x,y,z,a,b,a',b',w',x',y'} g).hom ambientRight
  aug_left : ChainLift V.lift.pair.left V'.lift.pair.left
    (ambientLeftMap.{u,v,w,x,y,z,a,b,a',b',w',x',y'} h).hom ambientLeft
  page : ∀ r p n, 2 ≤ r →
    T.map V.lift.pair V'.lift.pair
      (ambientRightMap.{u,v,w,x,y,z,a,b,a',b',w',x',y'} g)
      (ambientLeftMap.{u,v,w,x,y,z,a,b,a',b',w',x',y'} h) r p n =
    (T.liftedPages V.lift.pair V'.lift.pair ambientRight ambientLeft).map r (-p) (-n)
  originalTotal : TermMap
    (ordinaryTotal P.complex (restrictionComplex f (ComplexShape.down ℕ) Q.complex))
    (ordinaryTotal P'.complex (restrictionComplex f (ComplexShape.down ℕ) Q'.complex))
  total_formula : ∀ i j n (hn : i+j=n) a b, originalTotal.app n
      (ordinaryInclusion P.complex (restrictionComplex f (ComplexShape.down ℕ) Q.complex)
        i j n hn (tmul R a b)) =
    ordinaryInclusion P'.complex (restrictionComplex f (ComplexShape.down ℕ) Q'.complex)
      i j n hn (tmul R (l.app i a) (restrictChainMap f m |>.app j b))
  total_square : ∀ n z, V'.target.total.iso.app n (originalTotal.app n z) =
    ((ordinaryTotalMap ambientRight (((restrictionFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map ambientLeft)).f n).hom
      (V.target.total.iso.app n z)
  originalTarget : TermMap (tensorComplex P.complex (Restricted f M))
    (tensorComplex P'.complex (Restricted f M'))
  target_formula : ∀ n, originalTarget.app n = tensorMap (l.app n) (restrictLinear f h)
  augmentation_square : ∀ n z,
    V'.target.augmentation.app n (originalTotal.app n z) =
      originalTarget.app n (V.target.augmentation.app n z)
  targetMap : ∀ n, resolutionTor P (Restricted f M) n →ₗ[ℤ]
    resolutionTor P' (Restricted f M') n
  target_class : originalTarget.InducesHomology (fun n z => targetMap n z)
  quotient_square : ∀ (n : ℕ) (z : resolutionTor P (Restricted f M) n),
    (T.targetMap V.lift.pair V'.lift.pair
      (ambientRightMap.{u,v,w,x,y,z,a,b,a',b',w',x',y'} g)
      (ambientLeftMap.{u,v,w,x,y,z,a,b,a',b',w',x',y'} h) n).hom (V.target.quotient n z) =
    V'.target.quotient n (targetMap n z)
  target_square : ∀ n : ℕ,
    HomologicalComplex.homologyMap (T.lifted V.lift.pair V'.lift.pair
      ambientRight ambientLeft).hom (-(n : ℤ)) ≫ (V'.targetIso f n).hom =
    (V.targetIso f n).hom ≫ ambientTargetMap.{u,v,w,x,y,z,a,b,a',b',w',x',y'} f n (targetMap n)
  filtration : ∀ p n,
    ∃ k : (V.targetPiece f p n : ModuleCat ℤ) ⟶ (V'.targetPiece f p n : ModuleCat ℤ),
      k ≫ (V'.targetPiece f p n).arrow = (V.targetPiece f p n).arrow ≫
        ambientTargetMap.{u,v,w,x,y,z,a,b,a',b',w',x',y'} f n (targetMap n)


/-- Target and page naturality simultaneously for independently sized source
and target resolutions and for every augmented lift of the original maps. -/
def TargetNaturalityType : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S)
    (A : ModuleCat.{a} Rᵐᵒᵖ) (M : ModuleCat.{b} S)
    (A' : ModuleCat.{a'} Rᵐᵒᵖ) (M' : ModuleCat.{b'} S)
    (P : AugmentedResolution.{u,a,w} Rᵐᵒᵖ A)
    (Q : AugmentedResolution.{v,b,x} S M)
    (P' : AugmentedResolution.{u,a',w'} Rᵐᵒᵖ A')
    (Q' : AugmentedResolution.{v,b',x'} S M'),
    ∃ (T : NaturalSystem.{u,v,max u v a b w x y a' b' w' x' y' z,
      max u v a b w x y a' b' w' x' y' z} f)
      (V : OriginalSequenceData.{u,v,w,x,y,max a' b' w' x' y' z,a,b} f (P := P) (Q := Q) T)
      (V' : OriginalSequenceData.{u,v,w',x',y',max a b w x y z,a',b'} f (P := P') (Q := Q') T),
      OriginalLimitData f V ∧ OriginalLimitData f V' ∧
      ∀ (g : A →ₗ[Rᵐᵒᵖ] A') (h : M →ₗ[S] M')
        (l : TermMap P.complex P'.complex) (m : TermMap Q.complex Q'.complex),
        P.Lifts P' g l → Q.Lifts Q' h m →
        Nonempty (TargetNaturality.{u,v,w,x,y,z,a,b,a',b',w',x',y'} f V V' g h l m)


variable {V V'}
variable {g : A →ₗ[Rᵐᵒᵖ] A'} {h : M →ₗ[S] M'}
variable {l : TermMap P.complex P'.complex} {m : TermMap Q.complex Q'.complex}

/-- Naturality of the actual E² identification. The inner map preserves the
right S-action and both levels of Tor use the original quotient maps. -/
def SecondNaturality
    (_N : TargetNaturality.{u,v,w,x,y,z,a,b,a',b',w',x',y'} f V V' g h l m) : Prop :=
  ∀ q : ℕ,
    letI := V.originalInner.action q
    letI := V'.originalInner.action q
    ∃ j : resolutionTor P (Restricted f S) q →ₗ[Sᵐᵒᵖ] resolutionTor P' (Restricted f S) q,
      (∃ F : TermMap (tensorComplex P.complex (Restricted f S))
          (tensorComplex P'.complex (Restricted f S)),
        (∀ n, F.app n = tensorMap (l.app n) LinearMap.id) ∧
        ∀ z : cycles (tensorComplex P.complex (Restricted f S)) q,
          ∃ t : cycles (tensorComplex P'.complex (Restricted f S)) q,
            t.val = F.app q z.val ∧ j (homologyClass _ q z) = homologyClass _ q t) ∧
      ∀ (U : AugmentedResolution.{v,max w v,y} Sᵐᵒᵖ (resolutionTor P (Restricted f S) q))
        (U' : AugmentedResolution.{v,max w' v,y'} Sᵐᵒᵖ (resolutionTor P' (Restricted f S) q))
        (k : TermMap U.complex U'.complex), U.Lifts U' j k →
        ∃ (F : TermMap (tensorComplex U.complex M) (tensorComplex U'.complex M'))
          (t : ∀ p, resolutionTor U M p →ₗ[ℤ] resolutionTor U' M' p),
          (∀ n, F.app n = tensorMap (k.app n) h) ∧ F.InducesHomology (fun p z => t p z) ∧
          ∀ (p : ℕ) (z : ↥(chainPage
            (V := ModuleCat.{max u v a b w x y a' b' w' x' y' z} ℤ)
            (V.pages f).filtration (V.pages f).pages 2 p (p+q))),
            V'.secondEquiv f p q U'
              ((T.map V.lift.pair V'.lift.pair
                (ambientRightMap.{u,v,w,x,y,z,a,b,a',b',w',x',y'} g)
                (ambientLeftMap.{u,v,w,x,y,z,a,b,a',b',w',x',y'} h) 2 p (p+q)).hom z) =
            t p (V.secondEquiv f p q U z)

/-- Preservation of the filtration as actual submodules of the original
Tor quotient, with all augmentation lifts allowed. -/
def OriginalTargetLaws
    (N : TargetNaturality.{u,v,w,x,y,z,a,b,a',b',w',x',y'} f V V' g h l m) : Prop :=
  (∀ p n, (V.targetSubmodule f p n).map (N.targetMap n) ≤ V'.targetSubmodule f p n) ∧
  ∀ {l' : TermMap P.complex P'.complex} {m' : TermMap Q.complex Q'.complex}
    (N' : TargetNaturality.{u,v,w,x,y,z,a,b,a',b',w',x',y'} f V V' g h l' m'),
    (∀ n, N.targetMap n = N'.targetMap n) ∧
    ∀ r p n, 2 ≤ r →
      (T.liftedPages V.lift.pair V'.lift.pair N.ambientRight N.ambientLeft).map r (-p) (-n) =
      (T.liftedPages V.lift.pair V'.lift.pair N'.ambientRight N'.ambientLeft).map r (-p) (-n)

/-- The page, target, and E² comparisons all use the same pair of lifted
resolutions and agree for every augmented comparison lift. -/
def FullNaturalityType : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S)
    (A : ModuleCat.{a} Rᵐᵒᵖ) (M : ModuleCat.{b} S)
    (A' : ModuleCat.{a'} Rᵐᵒᵖ) (M' : ModuleCat.{b'} S)
    (P : AugmentedResolution.{u,a,w} Rᵐᵒᵖ A)
    (Q : AugmentedResolution.{v,b,x} S M)
    (P' : AugmentedResolution.{u,a',w'} Rᵐᵒᵖ A')
    (Q' : AugmentedResolution.{v,b',x'} S M'),
    ∃ (T : NaturalSystem.{u,v,max u v a b w x y a' b' w' x' y' z,
      max u v a b w x y a' b' w' x' y' z} f)
      (V : OriginalSequenceData.{u,v,w,x,y,max a' b' w' x' y' z,a,b} f (P := P) (Q := Q) T)
      (V' : OriginalSequenceData.{u,v,w',x',y',max a b w x y z,a',b'} f (P := P') (Q := Q') T),
      OriginalLimitData f V ∧ OriginalLimitData f V' ∧
      ∀ (g : A →ₗ[Rᵐᵒᵖ] A') (h : M →ₗ[S] M'), (∃ l : TermMap P.complex P'.complex, P.Lifts P' g l) ∧
          (∃ m : TermMap Q.complex Q'.complex, Q.Lifts Q' h m) ∧
          ∀ (l : TermMap P.complex P'.complex) (m : TermMap Q.complex Q'.complex),
            P.Lifts P' g l → Q.Lifts Q' h m →
            ∃ N : TargetNaturality.{u,v,w,x,y,z,a,b,a',b',w',x',y'} f V V' g h l m,
              SecondNaturality f N ∧ OriginalTargetLaws f N

end Naturality

section Composition

open ChangeOfRingsTor
universe a b c a' b' c'

/-- Scalar-linear coordinates on a module in the ambient category. -/
structure CoefficientCoordinates {R : Type u} [Ring R] (X : ModuleCat.{w} R) where
  original : ModuleCat.{a} R
  equiv : original ≃ₗ[R] X

def CoefficientCoordinates.map {R : Type u} [Ring R] {X Y : ModuleCat.{w} R}
    (E : CoefficientCoordinates.{u,w,a} X) (F : CoefficientCoordinates.{u,w,b} Y)
    (g : E.original →ₗ[R] F.original) : X ⟶ Y :=
  ModuleCat.ofHom (F.equiv.toLinearMap.comp (g.comp E.equiv.symm.toLinearMap))

/-- Identity and composition in the original coordinates, allowing all six
input carriers in the two composable coefficient maps to be independent. -/
def CoordinateFunctorialityType : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S)
    (T : NaturalSystem.{u,v,w,x} f)
    {A B C : ModuleCat.{w} Rᵐᵒᵖ} {M N L : ModuleCat.{max u v x} S}
    (P : ResolutionPair.{u,v,w,x} f A M) (Q : ResolutionPair.{u,v,w,x} f B N)
    (U : ResolutionPair.{u,v,w,x} f C L)
    (a₁ : CoefficientCoordinates.{u,w,a} A) (a₂ : CoefficientCoordinates.{u,w,b} B)
    (a₃ : CoefficientCoordinates.{u,w,c} C)
    (b₁ : CoefficientCoordinates.{v,max u v x,a'} M)
    (b₂ : CoefficientCoordinates.{v,max u v x,b'} N)
    (b₃ : CoefficientCoordinates.{v,max u v x,c'} L)
    (g : a₁.original →ₗ[Rᵐᵒᵖ] a₂.original) (g' : a₂.original →ₗ[Rᵐᵒᵖ] a₃.original)
    (h : b₁.original →ₗ[S] b₂.original) (h' : b₂.original →ₗ[S] b₃.original),
    (∀ r p n, 2 ≤ r →
      T.map P P (a₁.map a₁ LinearMap.id) (b₁.map b₁ LinearMap.id) r p n = 𝟙 _) ∧
    (∀ r p n, 2 ≤ r →
      T.map P U (a₁.map a₃ (g'.comp g)) (b₁.map b₃ (h'.comp h)) r p n =
      T.map P Q (a₁.map a₂ g) (b₁.map b₂ h) r p n ≫
        T.map Q U (a₂.map a₃ g') (b₂.map b₃ h') r p n) ∧
    (∀ n, T.targetMap P P (a₁.map a₁ LinearMap.id) (b₁.map b₁ LinearMap.id) n = 𝟙 _) ∧
    (∀ n, T.targetMap P U (a₁.map a₃ (g'.comp g)) (b₁.map b₃ (h'.comp h)) n =
      T.targetMap P Q (a₁.map a₂ g) (b₁.map b₂ h) n ≫
        T.targetMap Q U (a₂.map a₃ g') (b₂.map b₃ h') n) ∧
    ∀ r (hr : 0 ≤ r) p n, 2 ≤ r →
      T.map P Q (a₁.map a₂ g) (b₁.map b₂ h) r p n ≫
        chainDifferential (T.sequence Q).filtration (T.sequence Q).pages r hr p n =
      chainDifferential (T.sequence P).filtration (T.sequence P).pages r hr p n ≫
        T.map P Q (a₁.map a₂ g) (b₁.map b₂ h) r (p-r) (n-1)

end Composition


section ResolutionChange

open ChangeOfRingsTor
universe a b w' x' y'

/-- Changing either augmented resolution acts by the identity on the
coefficients. The resulting isomorphism preserves the actual filtration
on the original Tor quotient in both directions. -/
def ResolutionChangeType : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S)
    (A : ModuleCat.{a} Rᵐᵒᵖ) (M : ModuleCat.{b} S)
    (P : AugmentedResolution.{u,a,w} Rᵐᵒᵖ A)
    (Q : AugmentedResolution.{v,b,x} S M)
    (P' : AugmentedResolution.{u,a,w'} Rᵐᵒᵖ A)
    (Q' : AugmentedResolution.{v,b,x'} S M)
    (T : NaturalSystem.{u,v,max u v a b w x y w' x' y' z,
      max u v a b w x y w' x' y' z} f)
    (V : OriginalSequenceData.{u,v,w,x,y,max a b w' x' y' z,a,b} f (P := P) (Q := Q) T)
    (V' : OriginalSequenceData.{u,v,w',x',y',max a b w x y z,a,b} f (P := P') (Q := Q') T),
    (∀ r p n, 2 ≤ r →
      ∃ e : chainPage (V.pages f).filtration (V.pages f).pages r p n ≅
          chainPage (V'.pages f).filtration (V'.pages f).pages r p n,
        e.hom = T.map V.lift.pair V'.lift.pair (𝟙 _) (𝟙 _) r p n) ∧
    ∀ n, ∃ e : resolutionTor P (Restricted f M) n ≃ₗ[ℤ]
        resolutionTor P' (Restricted f M) n,
      (∀ z, V'.target.quotient n (e z) =
        (T.targetMap V.lift.pair V'.lift.pair (𝟙 _) (𝟙 _) n).hom (V.target.quotient n z)) ∧
      ∀ p, (V.targetSubmodule f p n).map e.toLinearMap = V'.targetSubmodule f p n

end ResolutionChange

section RowFiltration

open ChangeOfRingsTor DoubleTotalization P103.Specs.Ch11.TorBalance

/-- The chain regrading is the summand-preserving map used on the abutment.
It carries the actual ambient row steps to the row pieces of the ordinary total. -/
def RegradedRowsType : Prop :=
  ∀ (R : Type u) [Ring R]
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ)
    [(tensorCochainBicomplex C D).HasTotal (ComplexShape.up ℤ)]
    (B : TensorPagesData C D),
    Nonempty (TotalRegrading C D) ∧
    ∀ (e : TotalRegrading C D) (p : ℤ) (n : ℕ),
      ((ModuleCat.subobjectModule _) (B.filtration.piece (-p) (-(n : ℤ)))).map
        ((e.iso.hom.f (-(n : ℤ))) ≫
          ((ordinaryTotal C D).extendXIso negativeChainEmbedding (i := n) rfl).hom).hom =
        rowPiece C D p n

end RowFiltration

end AdvancedHomologicalAlgebra.ChangeOfRingsOriginalCoefficients
