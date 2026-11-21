import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtTorDefinitions
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.AugmentedAssembly
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Embedding.Restriction

/-! Tensor bicomplexes for the balance theorem (paper.tex 2619–2674).
The tensor is the shared right-left balanced quotient, even when R is
noncommutative. Integer indices permit direct use of augmented assembly.
Ordinary resolutions are extended by zero before taking their tensor total.
-/
namespace P103.Specs.Ch11.TorBalance
open CategoryTheory
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.TotalComplexAssembly
open P103.Specs.Ch11.ExtTorDefinitions
noncomputable section
universe u v w
variable {R : Type u} [Ring R]

@[simp] theorem tensorMap_tmul {A A' B B' : Type*}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ A'] [Module R B] [Module R B']
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B') (a : A) (b : B) :
    tensorMap f g (tmul R a b) = tmul R (f a) (g b) := rfl

/-- Tensoring left modules with a fixed right module. -/
def leftTensorFunctor (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A] :
    ModuleCat.{w} R ⥤ ModuleCat.{max v w} ℤ where
  obj B := ModuleCat.of ℤ (Tensor R A B)
  map g := ModuleCat.ofHom (tensorMap LinearMap.id g.hom)
  map_id _ := by
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl

instance (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A] :
    (leftTensorFunctor (R := R) A : ModuleCat.{w} R ⥤ ModuleCat.{max v w} ℤ).Additive where
  map_add := by
    intro B B' f g
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    change tmul R a (f.hom b + g.hom b) = tmul R a (f.hom b) + tmul R a (g.hom b)
    simp [tmul, TensorProduct.tmul_add]

abbrev leftTensorComplex (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (D : ChainComplex (ModuleCat.{w} R) ℤ) :=
  ((leftTensorFunctor A).mapHomologicalComplex (ComplexShape.down ℤ)).obj D

/-- Unsigned commuting differentials, with horizontal degree first. -/
def tensorBicomplex (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (D : ChainComplex (ModuleCat.{w} R) ℤ) : ChainBicomplex.{0,max v w} ℤ where
  X p := leftTensorComplex (C.X p) D
  d p p' :=
    { f q := ModuleCat.ofHom (tensorMap (C.d p p').hom LinearMap.id)
      comm' q q' _ := by
        apply ModuleCat.hom_ext
        apply tensor_hom_ext
        intro a b
        rfl }
  shape p p' h := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    change tmul R ((C.d p p').hom a) b = 0
    rw [C.shape p p' h]
    simp [tmul]
  d_comp_d' p p' p'' _ _ := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    change tmul R ((C.d p' p'').hom ((C.d p p').hom a)) b = 0
    have h := congrArg ModuleCat.Hom.hom (C.d_comp_d p p' p'')
    have ha := LinearMap.congr_fun h a
    change (C.d p' p'').hom ((C.d p p').hom a) = 0 at ha
    rw [ha]
    simp [tmul]

abbrev tensorTotal (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (D : ChainComplex (ModuleCat.{w} R) ℤ) := total (tensorBicomplex C D)

/-- The total of ordinary complexes, retained as an integer complex. -/
abbrev ordinaryTensorTotal (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) :=
  tensorTotal (extendNonnegativeChain C) (extendNonnegativeChain D)

instance nonnegativeChainEmbedding_relIff : nonnegativeChainEmbedding.IsRelIff where
  rel' i j h := by
    change (j : ℤ) + 1 = (i : ℤ) at h
    change j + 1 = i
    exact_mod_cast h

/-- The same first-quadrant total indexed in ordinary nonnegative degrees. -/
abbrev ordinaryTotal (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) :=
  (ordinaryTensorTotal C D).restriction nonnegativeChainEmbedding

def ordinaryInclusion (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p + q = n) :
    Tensor R (C.X p) (D.X q) →ₗ[ℤ] (ordinaryTotal C D).X n :=
  (totalInclusion (tensorBicomplex (extendNonnegativeChain C)
      (extendNonnegativeChain D)) p q n (by exact_mod_cast h)).hom.comp
    (tensorMap (C.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom
      (D.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom)

abbrev leftOrdinaryTensorComplex (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (D : ChainComplex (ModuleCat.{w} R) ℕ) :=
  ((leftTensorFunctor A).mapHomologicalComplex (ComplexShape.down ℕ)).obj D

/-- The two actual augmentation maps, uniquely specified on all summands.
This structure does not assert they are quasi-isomorphisms. -/
structure Augmentations {A : Type v} {B : Type w}
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module R B]
    (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution R B) where
  left : ordinaryTotal P.complex Q.complex ⟶ tensorComplex P.complex B
  right : ordinaryTotal P.complex Q.complex ⟶ leftOrdinaryTensorComplex A Q.complex
  left_zero : ∀ (p : ℕ) (a : P.complex.X p) (b : Q.complex.X 0),
    (left.f p).hom (ordinaryInclusion P.complex Q.complex p 0 p (by omega) (tmul R a b)) =
      tmul R a (Q.ε b)
  left_positive : ∀ (p q n : ℕ) (h : p + q = n), q ≠ 0 →
    (left.f n).hom.comp (ordinaryInclusion P.complex Q.complex p q n h) = 0
  right_zero : ∀ (q : ℕ) (a : P.complex.X 0) (b : Q.complex.X q),
    (right.f q).hom (ordinaryInclusion P.complex Q.complex 0 q q (by omega) (tmul R a b)) =
      tmul R (P.ε a) b
  right_positive : ∀ (p q n : ℕ) (h : p + q = n), p ≠ 0 →
    (right.f n).hom.comp (ordinaryInclusion P.complex Q.complex p q n h) = 0

/-- Balance in every ordinary degree, over arbitrary associative unital rings. -/
def balanceType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) (B : Type w)
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module R B]
    (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution R B),
    P.IsProjective → Q.IsProjective →
    ∃ α : Augmentations P Q, QuasiIsomorphism α.left ∧ QuasiIsomorphism α.right

/-- The balanced identification is induced by the two augmentation maps. -/
def balanceEquiv {A : Type v} {B : Type w}
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module R B]
    {P : LeftResolution Rᵐᵒᵖ A} {Q : LeftResolution R B}
    (α : Augmentations P Q) (hL : QuasiIsomorphism α.left)
    (hR : QuasiIsomorphism α.right) (n : ℕ) :
    TorWith P B n ≃ₗ[ℤ] Homology (leftOrdinaryTensorComplex A Q.complex) n :=
  (LinearEquiv.ofBijective (homologyMap α.left n) (hL n)).symm.trans
    (LinearEquiv.ofBijective (homologyMap α.right n) (hR n))

/-- Pure tensors in a specified total summand. -/
def tensorInclusion (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (D : ChainComplex (ModuleCat.{w} R) ℤ) (p q n : ℤ) (h : p + q = n) :
    Tensor R (C.X p) (D.X q) →ₗ[ℤ] (tensorTotal C D).X n :=
  (totalInclusion (tensorBicomplex C D) p q n h).hom

/-- Simultaneous maps in the two tensor factors. -/
def tensorBicomplexMap
    {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {D D' : ChainComplex (ModuleCat.{w} R) ℤ} (f : C ⟶ C') (g : D ⟶ D') :
    tensorBicomplex C D ⟶ tensorBicomplex C' D' where
  f p :=
    { f q := ModuleCat.ofHom (tensorMap (f.f p).hom (g.f q).hom)
      comm' q q' _ := by
        apply ModuleCat.hom_ext
        apply tensor_hom_ext
        intro a b
        change tmul R _ ((D'.d q q').hom ((g.f q).hom b)) =
          tmul R _ ((g.f q').hom ((D.d q q').hom b))
        exact congrArg (tmul R ((f.f p).hom a))
          (congrArg (fun k => k.hom b) (g.comm q q')) }
  comm' p p' _ := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    change tmul R ((C'.d p p').hom ((f.f p).hom a)) _ =
      tmul R ((f.f p').hom ((C.d p p').hom a)) _
    exact congrArg (fun x => tmul R x ((g.f q).hom b))
      (congrArg (fun k => k.hom a) (f.comm p p'))

abbrev tensorTotalMap
    {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {D D' : ChainComplex (ModuleCat.{w} R) ℤ} (f : C ⟶ C') (g : D ⟶ D') :=
  HomologicalComplex₂.total.map (tensorBicomplexMap f g) (ComplexShape.down ℤ)

abbrev ordinaryTotalMap
    {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
    {D D' : ChainComplex (ModuleCat.{w} R) ℕ} (f : C ⟶ C') (g : D ⟶ D') :=
  HomologicalComplex.restrictionMap
    (tensorTotalMap (HomologicalComplex.extendMap f nonnegativeChainEmbedding)
      (HomologicalComplex.extendMap g nonnegativeChainEmbedding)) nonnegativeChainEmbedding

def leftTensorFirstMap {A A' : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup A'] [Module Rᵐᵒᵖ A'] (f : A →ₗ[Rᵐᵒᵖ] A')
    (D : ChainComplex (ModuleCat.{w} R) ℕ) :
    leftOrdinaryTensorComplex A D ⟶ leftOrdinaryTensorComplex A' D where
  f q := ModuleCat.ofHom (tensorMap f LinearMap.id)
  comm' q q' _ := by
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl

abbrev leftTensorMap {A A' : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup A'] [Module Rᵐᵒᵖ A'] (f : A →ₗ[Rᵐᵒᵖ] A')
    {D D' : ChainComplex (ModuleCat.{w} R) ℕ} (g : D ⟶ D') :=
  leftTensorFirstMap f D ≫
    ((leftTensorFunctor A').mapHomologicalComplex (ComplexShape.down ℕ)).map g

/-- These diagrams specify simultaneous naturality in both modules for every
map of augmented resolutions. Identity coefficient maps give comparison diagrams. -/
def augmentation_naturalType : Prop :=
  ∀ (R : Type u) [Ring R] (A A' : Type v) (B B' : Type w)
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup A'] [Module Rᵐᵒᵖ A']
    [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (P : LeftResolution Rᵐᵒᵖ A) (P' : LeftResolution Rᵐᵒᵖ A')
    (Q : LeftResolution R B) (Q' : LeftResolution R B')
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B')
    (l : P.complex ⟶ P'.complex) (m : Q.complex ⟶ Q'.complex),
    ChainLift P P' f l → ChainLift Q Q' g m →
    ∀ (α : Augmentations P Q) (β : Augmentations P' Q'),
      (ordinaryTotalMap l m ≫ β.left =
        α.left ≫ tensorFirstMap l B ≫ tensorSecondMap P'.complex g) ∧
      (ordinaryTotalMap l m ≫ β.right = α.right ≫ leftTensorMap f m)

/-- Naturality of the induced identification on the actual quotient homology
models, for arbitrary choices of augmentation maps and resolution lifts. -/
def balanceEquiv_naturalType : Prop :=
  ∀ (R : Type u) [Ring R] (A A' : Type v) (B B' : Type w)
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup A'] [Module Rᵐᵒᵖ A']
    [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (P : LeftResolution Rᵐᵒᵖ A) (P' : LeftResolution Rᵐᵒᵖ A')
    (Q : LeftResolution R B) (Q' : LeftResolution R B')
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B')
    (l : P.complex ⟶ P'.complex) (m : Q.complex ⟶ Q'.complex),
    ChainLift P P' f l → ChainLift Q Q' g m →
    ∀ (α : Augmentations P Q) (β : Augmentations P' Q')
      (hαL : QuasiIsomorphism α.left) (hαR : QuasiIsomorphism α.right)
      (hβL : QuasiIsomorphism β.left) (hβR : QuasiIsomorphism β.right) (n : ℕ),
      (balanceEquiv β hβL hβR n).toLinearMap.comp
          (homologyMap (tensorFirstMap l B ≫ tensorSecondMap P'.complex g) n) =
        (homologyMap (leftTensorMap f m) n).comp
          (balanceEquiv α hαL hαR n).toLinearMap

/-- The outer homology maps do not depend on either chosen lift. Together
with the preceding diagrams and balance, this gives choice independence of
the middle comparison and of the induced balanced identification. -/
def lift_independentType : Prop :=
  ∀ (R : Type u) [Ring R] (A A' : Type v) (B B' : Type w)
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup A'] [Module Rᵐᵒᵖ A']
    [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (P : LeftResolution Rᵐᵒᵖ A) (P' : LeftResolution Rᵐᵒᵖ A')
    (Q : LeftResolution R B) (Q' : LeftResolution R B'),
    P.IsProjective → Q.IsProjective →
    ∀ (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B')
      (l l' : P.complex ⟶ P'.complex) (m m' : Q.complex ⟶ Q'.complex),
    ChainLift P P' f l → ChainLift P P' f l' →
    ChainLift Q Q' g m → ChainLift Q Q' g m' → ∀ n : ℕ,
      homologyMap (tensorFirstMap l B ≫ tensorSecondMap P'.complex g) n =
        homologyMap (tensorFirstMap l' B ≫ tensorSecondMap P'.complex g) n ∧
      homologyMap (leftTensorMap f m) n = homologyMap (leftTensorMap f m') n

section Commutative
variable {K : Type u} [CommRing K]

/-- The canonical right action associated with a commutative left action. -/
abbrev commRightFunctor (K : Type u) [CommRing K] :
    ModuleCat.{v} K ⥤ ModuleCat.{v} Kᵐᵒᵖ :=
  ModuleCat.restrictScalars (R := Kᵐᵒᵖ) (S := K)
    ((RingHom.id K).fromOpposite (fun _ _ => Commute.all _ _))

abbrev commRightComplex (C : ChainComplex (ModuleCat.{v} K) ℤ) :=
  ((commRightFunctor K).mapHomologicalComplex (ComplexShape.down ℤ)).obj C

/-- The unsigned flip on the shared balanced quotient. Both right actions
are specifically the canonical actions from commutativity. -/
def commTensorFlip (A : Type v) (B : Type w) [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] :
    letI := commRightModule K A
    letI := commRightModule K B
    Tensor K A B →ₗ[ℤ] Tensor K B A := by
  letI := commRightModule K A
  letI := commRightModule K B
  exact (relations K A B).mapQ (relations K B A)
    (TensorProduct.comm ℤ A B).toAddEquiv.toAddMonoidHom.toIntLinearMap (by
      apply Submodule.span_le.mpr
      rintro z ⟨r, a, b, rfl⟩
      change (TensorProduct.comm ℤ A B)
        (TensorProduct.tmul ℤ (MulOpposite.op r • a) b -
          TensorProduct.tmul ℤ a (r • b)) ∈ relations K B A
      rw [map_sub, TensorProduct.comm_tmul, TensorProduct.comm_tmul]
      change TensorProduct.tmul ℤ b (r • a) - TensorProduct.tmul ℤ (r • b) a ∈
        relations K B A
      have h : TensorProduct.tmul ℤ (MulOpposite.op r • b) a -
          TensorProduct.tmul ℤ b (r • a) ∈ relations K B A :=
        Submodule.subset_span ⟨r, b, a, rfl⟩
      have hb : MulOpposite.op r • b = r • b := rfl
      rw [hb] at h
      simpa only [neg_sub] using (Submodule.neg_mem (relations K B A) h))

def signedFlipType : Prop :=
  ∀ {K : Type u} [CommRing K]
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (D : ChainComplex (ModuleCat.{w} K) ℤ),
    ∃ e : tensorTotal (commRightComplex C) D ≅ tensorTotal (commRightComplex D) C,
      ∀ (p q n : ℤ) (h : p + q = n) (a : C.X p) (b : D.X q),
        e.hom.f n (tensorInclusion (commRightComplex C) D p q n h (tmul K a b)) =
          (p * q).negOnePow •
            tensorInclusion (commRightComplex D) C q p n (by omega) (tmul K b a)

def commRightLinear {A : Type v} {B : Type w} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (f : A →ₗ[K] B) :
    letI := commRightModule K A
    letI := commRightModule K B
    A →ₗ[Kᵐᵒᵖ] B := by
  letI := commRightModule K A
  letI := commRightModule K B
  exact { toFun := f, map_add' := f.map_add, map_smul' := fun r a => f.map_smul r.unop a }

abbrev commRightOrdinaryComplex (C : ChainComplex (ModuleCat.{v} K) ℕ) :=
  ((commRightFunctor K).mapHomologicalComplex (ComplexShape.down ℕ)).obj C

abbrev commRightOrdinaryMap {C D : ChainComplex (ModuleCat.{v} K) ℕ} (f : C ⟶ D) :=
  ((commRightFunctor K).mapHomologicalComplex (ComplexShape.down ℕ)).map f

def commRightResolution {A : Type v} [AddCommGroup A] [Module K A]
    (P : LeftResolution K A) :
    letI := commRightModule K A
    LeftResolution Kᵐᵒᵖ A := by
  letI := commRightModule K A
  exact
    { complex := commRightOrdinaryComplex P.complex
      ε := commRightLinear (K := K) (A := P.complex.X 0) (B := A) P.ε
      surjective := P.surjective
      exact_zero := by
        ext a
        have h := congrArg (fun S : Submodule K (P.complex.X 0) => a ∈ S) P.exact_zero
        exact Iff.of_eq h
      exact_succ := by
        intro n
        ext a
        have h := congrArg (fun S : Submodule K (P.complex.X (n + 1)) => a ∈ S) (P.exact_succ n)
        exact Iff.of_eq h }


/-- The flip of the two tensor factors in a single ordinary complex. -/
def commOrdinaryTensorFlip (A : Type v) [AddCommGroup A] [Module K A]
    (D : ChainComplex (ModuleCat.{w} K) ℕ) :
    letI := commRightModule K A
    leftOrdinaryTensorComplex A D ≅ tensorComplex (commRightOrdinaryComplex D) A := by
  letI := commRightModule K A
  exact
    { hom :=
        { f q := ModuleCat.ofHom (commTensorFlip A (D.X q))
          comm' q q' _ := by
            apply ModuleCat.hom_ext
            apply tensor_hom_ext
            intro a b
            rfl }
      inv :=
        { f q := ModuleCat.ofHom (commTensorFlip (D.X q) A)
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
        intro a b
        rfl }

/-- A simultaneous natural symmetry for every pair of ordinary projective
resolutions. The two sides are the same chosen-resolution `TorWith` groups
used in the definition of Tor. -/
structure TorSymmetry (K : Type u) [CommRing K] where
  equivalence : ∀ (A : ModuleCat.{v} K) (B : ModuleCat.{w} K)
    (P : LeftResolution K A) (Q : LeftResolution K B)
    (hP : P.IsProjective) (hQ : Q.IsProjective) (n : ℕ),
    letI := commRightModule K A
    letI := commRightModule K B
    TorWith (commRightResolution P) B n ≃ₗ[ℤ]
      TorWith (commRightResolution Q) A n
  augmentation_formula : ∀ (A : ModuleCat.{v} K) (B : ModuleCat.{w} K)
    (P : LeftResolution K A) (Q : LeftResolution K B)
    (hP : P.IsProjective) (hQ : Q.IsProjective) (n : ℕ),
    letI := commRightModule K A
    letI := commRightModule K B
    ∃ (α : Augmentations (commRightResolution P) Q)
      (hL : QuasiIsomorphism α.left) (hR : QuasiIsomorphism α.right),
      equivalence A B P Q hP hQ n =
        (balanceEquiv α hL hR n).trans
          (((quotientHomology (ComplexShape.down ℕ) n).mapIso
            (commOrdinaryTensorFlip A Q.complex)).toLinearEquiv)
  naturality : ∀ (A A' : ModuleCat.{v} K) (B B' : ModuleCat.{w} K)
    (P : LeftResolution K A) (P' : LeftResolution K A')
    (Q : LeftResolution K B) (Q' : LeftResolution K B')
    (hP : P.IsProjective) (hP' : P'.IsProjective)
    (hQ : Q.IsProjective) (hQ' : Q'.IsProjective)
    (f : A ⟶ A') (g : B ⟶ B') (l : P.complex ⟶ P'.complex)
    (m : Q.complex ⟶ Q'.complex),
    ChainLift P P' f.hom l → ChainLift Q Q' g.hom m → ∀ n,
    letI := commRightModule K A
    letI := commRightModule K A'
    letI := commRightModule K B
    letI := commRightModule K B'
    (equivalence A' B' P' Q' hP' hQ' n).toLinearMap.comp
        (homologyMap (tensorFirstMap (commRightOrdinaryMap l) B ≫
          tensorSecondMap (commRightResolution P').complex g.hom) n) =
      (homologyMap (tensorFirstMap (commRightOrdinaryMap m) A ≫
          tensorSecondMap (commRightResolution Q').complex f.hom) n).comp
        (equivalence A B P Q hP hQ n).toLinearMap

def tor_symmetryType : Prop :=
  ∀ (K : Type u) [CommRing K], Nonempty (TorSymmetry.{u,v,w} K)




/-- The canonical change of side preserves an ordinary projective choice. -/
abbrev commRightProjectiveChoice {A : ModuleCat.{v} K} (P : ProjectiveChoice K A) :
    letI := commRightModule K A
    ProjectiveChoice Kᵐᵒᵖ (ModuleCat.of Kᵐᵒᵖ A) := by
  letI := commRightModule K A
  refine ⟨commRightResolution P.val, ?_⟩
  intro n
  letI := commRightModule K (P.val.complex.X n)
  letI := P.property n
  let σ := (RingHom.id K).toOpposite (fun _ _ => Commute.all _ _)
  let σ' := (RingHom.id K).fromOpposite (fun _ _ => Commute.all _ _)
  letI : RingHomInvPair σ σ' := ⟨rfl, rfl⟩
  letI : RingHomInvPair σ' σ := ⟨rfl, rfl⟩
  let e : P.val.complex.X n ≃ₛₗ[σ] P.val.complex.X n :=
    { toFun := id
      invFun := id
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact Module.Projective.of_equiv e

/-- The natural symmetry respects the actual upstream coefficient-functor
K-module structures on Tor, for every coherent choice of the Tor maps. -/
def tor_symmetry_linearType : Prop :=
  ∀ (K : Type u) [CommRing K] (S : TorSymmetry.{u,v,w} K) (n : ℕ)
    (E : TorMaps.{u,v,w} K n) (E' : TorMaps.{u,w,v} K n)
    (A : ModuleCat.{v} K) (B : ModuleCat.{w} K)
    (P : ProjectiveChoice K A) (Q : ProjectiveChoice K B),
    letI := commRightModule K A
    letI := commRightModule K B
    letI := torModule E (commRightProjectiveChoice P) B
    letI := torModule E' (commRightProjectiveChoice Q) A
    ∀ (r : K) x,
      S.equivalence A B P.val Q.val P.property Q.property n (r • x) =
        r • S.equivalence A B P.val Q.val P.property Q.property n x



/-- The ordinary signed interchange, together with its augmentation square.
Consequently its induced homology isomorphism is the symmetry obtained by
balance and termwise tensor interchange. -/
def signed_flip_inducesType : Prop :=
  ∀ (K : Type u) [CommRing K] (A : Type v) (B : Type w)
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    (P : LeftResolution K A) (Q : LeftResolution K B),
    letI := commRightModule K A
    letI := commRightModule K B
    ∃ e : ordinaryTotal (commRightResolution P).complex Q.complex ≅
        ordinaryTotal (commRightResolution Q).complex P.complex,
      (∀ (p q n : ℕ) (h : p + q = n) (a : P.complex.X p) (b : Q.complex.X q),
        (e.hom.f n).hom
            (ordinaryInclusion (commRightResolution P).complex Q.complex p q n h (tmul K a b)) =
          ((p : ℤ) * (q : ℤ)).negOnePow •
            ordinaryInclusion (commRightResolution Q).complex P.complex q p n (by omega) (tmul K b a)) ∧
      ∀ (α : Augmentations (commRightResolution P) Q)
        (β : Augmentations (commRightResolution Q) P),
        (e.hom ≫ β.left = α.right ≫ (commOrdinaryTensorFlip A Q.complex).hom) ∧
        ∀ (hL : QuasiIsomorphism α.left) (hR : QuasiIsomorphism α.right)
          (n : ℕ) (z : Homology (ordinaryTotal (commRightResolution P).complex Q.complex) n),
          homologyMap (commOrdinaryTensorFlip A Q.complex).hom n
              (balanceEquiv α hL hR n (homologyMap α.left n z)) =
            homologyMap (e.hom ≫ β.left) n z

end Commutative

def tensorBicomplexType :=
  ∀ {R : Type u} [Ring R],
    ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ →
    ChainComplex (ModuleCat.{w} R) ℤ → ChainBicomplex.{0,max v w} ℤ
abbrev tensorBicomplexValue := @tensorBicomplex.{u,v,w}

def tensor_differentialsType : Prop :=
  ∀ {R : Type u} [Ring R]
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (D : ChainComplex (ModuleCat.{w} R) ℤ) (p p' q q' : ℤ),
    ((tensorBicomplex C D).d p p').f q =
      ModuleCat.ofHom (tensorMap (C.d p p').hom LinearMap.id) ∧
    ((tensorBicomplex C D).X p).d q q' =
      ModuleCat.ofHom (tensorMap LinearMap.id (D.d q q').hom)

def tensorTotal_dType : Prop :=
  ∀ {R : Type u} [Ring R]
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (D : ChainComplex (ModuleCat.{w} R) ℤ) (p q n : ℤ) (h : p + q = n)
    (a : C.X p) (b : D.X q),
    ((tensorTotal C D).d n (n - 1)).hom (tensorInclusion C D p q n h (tmul R a b)) =
      tensorInclusion C D (p - 1) q (n - 1) (by omega)
        (tmul R ((C.d p (p - 1)).hom a) b) +
      p.negOnePow • tensorInclusion C D p (q - 1) (n - 1) (by omega)
        (tmul R a ((D.d q (q - 1)).hom b))

def tensor_supportedType : Prop :=
  ∀ {R : Type u} [Ring R]
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (D : ChainComplex (ModuleCat.{w} R) ℤ) (a b : ℤ),
    SupportedIn C (Set.Ici a) → SupportedIn D (Set.Ici b) →
    SupportedQuadrant (tensorBicomplex C D) a b

end
end P103.Specs.Ch11.TorBalance
