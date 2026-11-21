import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.TorBalance
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.FlatnessTests

/-! Opposite-ring transport for the second-factor version of Künneth.
The base ring is associative and unital; neither action uses commutativity.
The double opposite action is restriction along `(RingEquiv.opOp R).symm`.
All homology groups are the shared explicit quotient of cycles by boundaries.
-/
namespace P103.Specs.Ch11.KunnethOppositeInterchange
open CategoryTheory
open P103.BalancedTensor
open P103.Specs.Ch02.FlatnessTests
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.TorBalance
noncomputable section
universe u v w t
variable {R : Type u} [Ring R]

abbrev doubleOppositeFunctor (R : Type u) [Ring R] :
    ModuleCat.{v} R ⥤ ModuleCat.{v} Rᵐᵒᵖᵐᵒᵖ :=
  ModuleCat.restrictScalars (RingEquiv.opOp R).symm.toRingHom

abbrev doubleOppositeComplex {ι : Type t} {c : ComplexShape ι}
    (D : HomologicalComplex (ModuleCat.{v} R) c) :=
  ((doubleOppositeFunctor R).mapHomologicalComplex c).obj D

abbrev doubleOppositeMap {ι : Type t} {c : ComplexShape ι}
    {D D' : HomologicalComplex (ModuleCat.{v} R) c} (g : D ⟶ D') :=
  ((doubleOppositeFunctor R).mapHomologicalComplex c).map g

def doubleOppositeLinear {A B : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (g : A →ₗ[R] B) :
    letI := doubleOppositeModule R A
    letI := doubleOppositeModule R B
    A →ₗ[Rᵐᵒᵖᵐᵒᵖ] B := by
  letI := doubleOppositeModule R A
  letI := doubleOppositeModule R B
  exact { g.toAddMonoidHom with map_smul' := fun r a => g.map_smul r.unop.unop a }

/-- The quotient map that exchanges the tensor factors and the ring. -/
def tensorFlipMap (A : Type v) (B : Type w)
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module R B] :
    letI := doubleOppositeModule R B
    Tensor R A B →ₗ[ℤ] Tensor Rᵐᵒᵖ B A := by
  letI := doubleOppositeModule R B
  exact (relations R A B).mapQ (relations Rᵐᵒᵖ B A)
    (TensorProduct.comm ℤ A B).toLinearMap (by
      apply Submodule.span_le.mpr
      rintro z ⟨r, a, b, rfl⟩
      change (TensorProduct.comm ℤ A B)
        (TensorProduct.tmul ℤ (MulOpposite.op r • a) b -
          TensorProduct.tmul ℤ a (r • b)) ∈ relations Rᵐᵒᵖ B A
      rw [map_sub, TensorProduct.comm_tmul, TensorProduct.comm_tmul]
      have h : TensorProduct.tmul ℤ (MulOpposite.op (MulOpposite.op r) • b) a -
          TensorProduct.tmul ℤ b (MulOpposite.op r • a) ∈ relations Rᵐᵒᵖ B A :=
        Submodule.subset_span ⟨MulOpposite.op r, b, a, rfl⟩
      change TensorProduct.tmul ℤ (r • b) a -
        TensorProduct.tmul ℤ b (MulOpposite.op r • a) ∈ relations Rᵐᵒᵖ B A at h
      simpa only [neg_sub] using (Submodule.neg_mem (relations Rᵐᵒᵖ B A) h))

/-- The inverse quotient map, retaining the original right-left orientation. -/
def tensorUnflipMap (A : Type v) (B : Type w)
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module R B] :
    letI := doubleOppositeModule R B
    Tensor Rᵐᵒᵖ B A →ₗ[ℤ] Tensor R A B := by
  letI := doubleOppositeModule R B
  exact (relations Rᵐᵒᵖ B A).mapQ (relations R A B)
    (TensorProduct.comm ℤ B A).toLinearMap (by
      apply Submodule.span_le.mpr
      rintro z ⟨r, b, a, rfl⟩
      change (TensorProduct.comm ℤ B A)
        (TensorProduct.tmul ℤ (MulOpposite.op r • b) a -
          TensorProduct.tmul ℤ b (r • a)) ∈ relations R A B
      rw [map_sub, TensorProduct.comm_tmul, TensorProduct.comm_tmul]
      have h : TensorProduct.tmul ℤ (MulOpposite.op r.unop • a) b -
          TensorProduct.tmul ℤ a (r.unop • b) ∈ relations R A B :=
        Submodule.subset_span ⟨r.unop, a, b, rfl⟩
      change TensorProduct.tmul ℤ a (r.unop • b) -
        TensorProduct.tmul ℤ (r • a) b ∈ relations R A B
      simpa only [MulOpposite.op_unop, neg_sub] using
        (Submodule.neg_mem (relations R A B) h))

/-- Canonical unsigned interchange on the balanced quotient. -/
def tensorFlip (A : Type v) (B : Type w)
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module R B] :
    letI := doubleOppositeModule R B
    Tensor R A B ≃ₗ[ℤ] Tensor Rᵐᵒᵖ B A := by
  letI := doubleOppositeModule R B
  exact LinearEquiv.ofLinearMap (tensorFlipMap A B) (tensorUnflipMap A B)
    (by apply tensor_hom_ext; intro b a; rfl)
    (by apply tensor_hom_ext; intro a b; rfl)

/-- The tensor flip applied termwise to an ordinary left resolution complex. -/
def tensorComplexFlip (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (D : ChainComplex (ModuleCat.{w} R) ℕ) :
    leftOrdinaryTensorComplex A D ≅ tensorComplex (doubleOppositeComplex D) A where
  hom :=
    { f q := ModuleCat.ofHom (tensorFlip A (D.X q)).toLinearMap
      comm' q q' _ := by
        apply ModuleCat.hom_ext
        apply tensor_hom_ext
        intro a b
        rfl }
  inv :=
    { f q := ModuleCat.ofHom (tensorFlip A (D.X q)).symm.toLinearMap
      comm' q q' _ := by
        apply ModuleCat.hom_ext
        apply tensor_hom_ext
        intro b a
        rfl }
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro b a
    rfl

def doubleOppositeResolution {B : Type w} [AddCommGroup B] [Module R B]
    (Q : LeftResolution R B) :
    letI := doubleOppositeModule R B
    LeftResolution Rᵐᵒᵖᵐᵒᵖ B := by
  letI := doubleOppositeModule R B
  exact
    { complex := doubleOppositeComplex Q.complex
      ε := doubleOppositeLinear (A := Q.complex.X 0) (B := B) Q.ε
      surjective := Q.surjective
      exact_zero := by
        ext b
        exact Iff.of_eq (congrArg (fun S : Submodule R (Q.complex.X 0) => b ∈ S) Q.exact_zero)
      exact_succ := by
        intro n
        ext b
        exact Iff.of_eq (congrArg (fun S : Submodule R (Q.complex.X (n+1)) => b ∈ S)
          (Q.exact_succ n)) }

/-- Transport back along the inverse equivalence, for completely arbitrary
projective models over the double opposite ring. -/
abbrev recoverFunctor (R : Type u) [Ring R] :
    ModuleCat.{v} Rᵐᵒᵖᵐᵒᵖ ⥤ ModuleCat.{v} R :=
  ModuleCat.restrictScalars (RingEquiv.opOp R).toRingHom

abbrev recoverComplex {ι : Type t} {c : ComplexShape ι}
    (D : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖᵐᵒᵖ) c) :=
  ((recoverFunctor R).mapHomologicalComplex c).obj D

abbrev recoverMap {ι : Type t} {c : ComplexShape ι}
    {D D' : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖᵐᵒᵖ) c} (m : D ⟶ D') :=
  ((recoverFunctor R).mapHomologicalComplex c).map m

def recoverResolution {B : Type w} [AddCommGroup B] [Module R B] :
    letI := doubleOppositeModule R B
    LeftResolution Rᵐᵒᵖᵐᵒᵖ B → LeftResolution R B := by
  letI := doubleOppositeModule R B
  intro S
  exact
    { complex := recoverComplex S.complex
      ε := { S.ε.toAddMonoidHom with
        map_smul' := fun r b => S.ε.map_smul (MulOpposite.op (MulOpposite.op r)) b }
      surjective := S.surjective
      exact_zero := by
        ext b
        exact Iff.of_eq (congrArg
          (fun U : Submodule Rᵐᵒᵖᵐᵒᵖ (S.complex.X 0) => b ∈ U) S.exact_zero)
      exact_succ := by
        intro n
        ext b
        exact Iff.of_eq (congrArg
          (fun U : Submodule Rᵐᵒᵖᵐᵒᵖ (S.complex.X (n+1)) => b ∈ U) (S.exact_succ n)) }

/-- One simultaneous signed interchange for all ordinary complexes. -/
structure SignedInterchange (R : Type u) [Ring R] where
  iso : ∀ (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ),
    ordinaryTotal C D ≅ ordinaryTotal (doubleOppositeComplex D) C
  formula : ∀ C D (p q n : ℕ) (h : p + q = n) (a : C.X p) (b : D.X q),
    ((iso C D).hom.f n).hom (ordinaryInclusion C D p q n h (tmul R a b)) =
      ((p : ℤ) * (q : ℤ)).negOnePow •
        ordinaryInclusion (doubleOppositeComplex D) C q p n (by omega) (tmul Rᵐᵒᵖ b a)
  naturality : ∀ {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
    {D D' : ChainComplex (ModuleCat.{w} R) ℕ} (f : C ⟶ C') (g : D ⟶ D'),
    ordinaryTotalMap f g ≫ (iso C' D').hom =
      (iso C D).hom ≫ ordinaryTotalMap (doubleOppositeMap g) f
  homology_naturality : ∀ {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
    {D D' : ChainComplex (ModuleCat.{w} R) ℕ} (f : C ⟶ C') (g : D ⟶ D') (n : ℕ),
    (homologyMap (iso C' D').hom n).comp (homologyMap (ordinaryTotalMap f g) n) =
      (homologyMap (ordinaryTotalMap (doubleOppositeMap g) f) n).comp
        (homologyMap (iso C D).hom n)

def signed_interchangeType : Prop :=
  ∀ (R : Type u) [Ring R], Nonempty (SignedInterchange.{u,v,w} R)

/-- Tor interchange in every degree, for every pair of projective models.
The displayed formula fixes the isomorphism by the actual balanced
augmentation comparison, rather than just asserting an abstract isomorphism.
-/
structure TorTransport (R : Type u) [Ring R] where
  equiv : ∀ (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{w} R)
    (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution R B)
    (hP : P.IsProjective) (hQ : Q.IsProjective) (n : ℕ),
    letI := doubleOppositeModule R B
    TorWith (doubleOppositeResolution Q) A n ≃ₗ[ℤ] TorWith P B n
  normalization : ∀ A B P Q hP hQ (n : ℕ)
    (α : Augmentations P Q) (hL : QuasiIsomorphism α.left) (hR : QuasiIsomorphism α.right),
    (equiv A B P Q hP hQ n).symm =
      (balanceEquiv α hL hR n).trans
        (((P103.Specs.Ch10.Comparison.quotientHomology (ComplexShape.down ℕ) n).mapIso
          (tensorComplexFlip A Q.complex)).toLinearEquiv)
  naturality : ∀ (A A' : ModuleCat.{v} Rᵐᵒᵖ) (B B' : ModuleCat.{w} R)
    (P : LeftResolution Rᵐᵒᵖ A) (P' : LeftResolution Rᵐᵒᵖ A')
    (Q : LeftResolution R B) (Q' : LeftResolution R B')
    (hP : P.IsProjective) (hP' : P'.IsProjective)
    (hQ : Q.IsProjective) (hQ' : Q'.IsProjective)
    (f : A ⟶ A') (g : B ⟶ B') (l : P.complex ⟶ P'.complex)
    (m : Q.complex ⟶ Q'.complex),
    ChainLift P P' f.hom l → ChainLift Q Q' g.hom m → ∀ n,
    (equiv A' B' P' Q' hP' hQ' n).toLinearMap.comp
      (homologyMap (tensorFirstMap (doubleOppositeMap m) A ≫
        tensorSecondMap (doubleOppositeComplex Q'.complex) f.hom) n) =
      (homologyMap (tensorFirstMap l B ≫ tensorSecondMap P'.complex g.hom) n).comp
        (equiv A B P Q hP hQ n).toLinearMap

def tor_transportType : Prop :=
  ∀ (R : Type u) [Ring R], Nonempty (TorTransport.{u,v,w} R)

/-- Restriction along R≃Rᵐᵒᵖᵐᵒᵖ preserves flatness, in the original tensor test. -/
def flat_transportType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    letI := doubleOppositeModule R M
    Flat.{u,v,w} R M ↔ RightFlat.{u,v,w} Rᵐᵒᵖ M

/-- Under scalar transport the terms and both distinguished submodules retain
exactly their underlying elements; their flatness transfers as well. -/
def complex_transportType : Prop :=
  ∀ {R : Type u} [Ring R] (D : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ),
    (∀ x : D.X n,
      x ∈ cycles (doubleOppositeComplex D) n ↔ x ∈ cycles D n) ∧
    (∀ x : D.X n,
      x ∈ boundaries (doubleOppositeComplex D) n ↔ x ∈ boundaries D n) ∧
    (Flat.{u,v,w} R (D.X n) ↔
      RightFlat.{u,v,w} Rᵐᵒᵖ ((doubleOppositeComplex D).X n)) ∧
    (Flat.{u,v,w} R (cycles D n) ↔
      RightFlat.{u,v,w} Rᵐᵒᵖ (cycles (doubleOppositeComplex D) n)) ∧
    (Flat.{u,v,w} R (boundaries D n) ↔
      RightFlat.{u,v,w} Rᵐᵒᵖ (boundaries (doubleOppositeComplex D) n))

/-- This square relates the signed total map to the unsigned flip used to
normalize the Tor identification. No projectivity is needed for this identity. -/
def signed_augmentationType : Prop :=
  ∀ (R : Type u) [Ring R] (S : SignedInterchange.{u,max u v,max u w} R)
    (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{w} R)
    (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution R B),
    letI := doubleOppositeModule R B
    ∀ (α : Augmentations P Q) (β : Augmentations (doubleOppositeResolution Q) P),
    (S.iso P.complex Q.complex).hom ≫ β.left =
      α.right ≫ (tensorComplexFlip A Q.complex).hom

/-- All double-opposite projective models are covered, with their actual
augmentations and complexes, by the scalar-transported models above. -/
def opposite_projective_modelsType : Prop :=
  ∀ (R : Type u) [Ring R] (B : Type w) [AddCommGroup B] [Module R B],
    letI := doubleOppositeModule R B
    ∀ (S : LeftResolution Rᵐᵒᵖᵐᵒᵖ B),
      doubleOppositeResolution (recoverResolution S) = S ∧
      (S.IsProjective ↔ (recoverResolution S).IsProjective)

/-- Explicit transport on every independently chosen projective model on
both sides, not only on models initially written as scalar restrictions. -/
structure AllModelTorTransport (R : Type u) [Ring R] where
  equiv : ∀ (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{w} R)
    (P : LeftResolution Rᵐᵒᵖ A) (hP : P.IsProjective),
    letI := doubleOppositeModule R B
    ∀ (S : LeftResolution Rᵐᵒᵖᵐᵒᵖ B) (hS : S.IsProjective) (n : ℕ),
      TorWith S A n ≃ₗ[ℤ] TorWith P B n
  normalization : ∀ (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{w} R)
    (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution R B) (hP : P.IsProjective),
    letI := doubleOppositeModule R B
    ∀ (hQ : (doubleOppositeResolution Q).IsProjective) (n : ℕ)
      (α : Augmentations P Q) (hL : QuasiIsomorphism α.left)
      (hR : QuasiIsomorphism α.right),
      (equiv A B P hP (doubleOppositeResolution Q) hQ n).symm =
        (balanceEquiv α hL hR n).trans
          (((quotientHomology (ComplexShape.down ℕ) n).mapIso
            (tensorComplexFlip A Q.complex)).toLinearEquiv)
  naturality : ∀ (A A' : ModuleCat.{v} Rᵐᵒᵖ) (B B' : ModuleCat.{w} R)
    (P : LeftResolution Rᵐᵒᵖ A) (P' : LeftResolution Rᵐᵒᵖ A')
    (hP : P.IsProjective) (hP' : P'.IsProjective),
    letI := doubleOppositeModule R B
    letI := doubleOppositeModule R B'
    ∀ (S : LeftResolution Rᵐᵒᵖᵐᵒᵖ B) (S' : LeftResolution Rᵐᵒᵖᵐᵒᵖ B')
      (hS : S.IsProjective) (hS' : S'.IsProjective)
      (f : A ⟶ A') (g : B ⟶ B') (l : P.complex ⟶ P'.complex)
      (m : S.complex ⟶ S'.complex),
      ChainLift P P' f.hom l → ChainLift S S' (doubleOppositeLinear g.hom) m → ∀ n,
      (equiv A' B' P' hP' S' hS' n).toLinearMap.comp
        (homologyMap (tensorFirstMap m A ≫ tensorSecondMap S'.complex f.hom) n) =
      (homologyMap (tensorFirstMap l B ≫ tensorSecondMap P'.complex g.hom) n).comp
        (equiv A B P hP S hS n).toLinearMap

def tor_transport_all_modelsType : Prop :=
  ∀ (R : Type u) [Ring R], Nonempty (AllModelTorTransport.{u,v,w} R)

/-- Both induced Tor arrows are independent of the resolution lifts. -/
def tor_lifts_independentType : Prop :=
  ∀ (R : Type u) [Ring R] (A A' : ModuleCat.{v} Rᵐᵒᵖ) (B B' : ModuleCat.{w} R)
    (P : LeftResolution Rᵐᵒᵖ A) (P' : LeftResolution Rᵐᵒᵖ A')
    (hP : P.IsProjective),
    letI := doubleOppositeModule R B
    letI := doubleOppositeModule R B'
    ∀ (S : LeftResolution Rᵐᵒᵖᵐᵒᵖ B) (S' : LeftResolution Rᵐᵒᵖᵐᵒᵖ B')
      (hS : S.IsProjective) (f : A ⟶ A') (g : B ⟶ B')
      (l l' : P.complex ⟶ P'.complex) (m m' : S.complex ⟶ S'.complex),
      ChainLift P P' f.hom l → ChainLift P P' f.hom l' →
      ChainLift S S' (doubleOppositeLinear g.hom) m →
      ChainLift S S' (doubleOppositeLinear g.hom) m' → ∀ n,
      homologyMap (tensorFirstMap l B ≫ tensorSecondMap P'.complex g.hom) n =
        homologyMap (tensorFirstMap l' B ≫ tensorSecondMap P'.complex g.hom) n ∧
      homologyMap (tensorFirstMap m A ≫ tensorSecondMap S'.complex f.hom) n =
        homologyMap (tensorFirstMap m' A ≫ tensorSecondMap S'.complex f.hom) n

/-- Canonical scalar transport on the quotient homology itself. The quotient
and all representative classes retain their underlying elements. -/
def homologyScalarEquiv (D : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    letI := doubleOppositeModule R (Homology D n)
    Homology (doubleOppositeComplex D) n ≃ₗ[Rᵐᵒᵖᵐᵒᵖ] Homology D n := by
  letI := doubleOppositeModule R (Homology D n)
  exact LinearEquiv.refl _ _

def homology_scalar_naturalType : Prop :=
  ∀ {R : Type u} [Ring R] {D D' : ChainComplex (ModuleCat.{v} R) ℕ}
    (g : D ⟶ D') (n : ℕ) (z : Homology (doubleOppositeComplex D) n),
    homologyScalarEquiv D' n (homologyMap (doubleOppositeMap g) n z) =
      homologyMap g n (homologyScalarEquiv D n z)

/-- Unsigned tensor interchange in the requested orientation, with the
simultaneous naturality square on the shared balanced quotient. -/
def unsigned_tensorType : Prop :=
  ∀ (R : Type u) [Ring R] (A A' : Type v) (B B' : Type w)
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup A'] [Module Rᵐᵒᵖ A']
    [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B'),
    letI := doubleOppositeModule R B
    letI := doubleOppositeModule R B'
    (∀ (b : B) (a : A), (tensorFlip A B).symm (tmul Rᵐᵒᵖ b a) = tmul R a b) ∧
    (∀ (a : A) (b : B), tensorFlip A B (tmul R a b) = tmul Rᵐᵒᵖ b a) ∧
    (tensorFlip A' B').symm.toLinearMap.comp (tensorMap (doubleOppositeLinear g) f) =
      (tensorMap f g).comp (tensorFlip A B).symm.toLinearMap

end
end P103.Specs.Ch11.KunnethOppositeInterchange
