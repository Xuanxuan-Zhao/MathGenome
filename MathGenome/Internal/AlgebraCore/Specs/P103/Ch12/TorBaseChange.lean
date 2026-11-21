import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.TorBalance
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! Flat base change, paper.tex 3186–3201, 3212–3228.
All rings here are commutative, including the zero ring. An `Algebra R S`
represents the arbitrary identity-preserving homomorphism R → S.
The complexes below retain their ordinary nonnegative indices and use the
explicit quotient homology of Chapter 10. -/
namespace P103.Specs.Ch12.TorBaseChange
open CategoryTheory
open scoped TensorProduct
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch10.Comparison
noncomputable section
set_option maxHeartbeats 1000000
universe u v w

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The scalar extension functor uses the supplied algebra structure verbatim. -/
def extensionFunctor (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} S where
  obj M := ModuleCat.of S (S ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.baseChange S)
  map_id M := ModuleCat.hom_ext (LinearMap.baseChange_id)
  map_comp f g := ModuleCat.hom_ext (LinearMap.baseChange_comp _ _)

instance : (extensionFunctor R S : ModuleCat.{max u v} R ⥤ _).Additive where
  map_add := by intros; exact ModuleCat.hom_ext (LinearMap.baseChange_add _ _)

/-- Extension with its actual S-linear differentials. -/
abbrev extendComplex (S : Type u) [CommRing S] [Algebra R S]
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) :=
  ((extensionFunctor R S).mapHomologicalComplex (ComplexShape.down ℕ)).obj K

/-- The S-action is on the coefficient, which also works for Res C. -/
def coefficientTensorFunctor (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (C : Type w) [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C] :
    ModuleCat.{max u v} R ⥤ ModuleCat.{max u v w} S where
  obj M := ModuleCat.of S (C ⊗[R] M)
  map f := ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.map
    (LinearMap.id : C →ₗ[S] C) f.hom)
  map_id M := by ext; rfl
  map_comp f g := by ext; rfl

instance (C : Type w) [AddCommGroup C] [Module S C] [Module R C]
    [IsScalarTower R S C] : (coefficientTensorFunctor R S C :
    ModuleCat.{max u v} R ⥤ ModuleCat.{max u v w} S).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change TensorProduct.AlgebraTensorModule.map (LinearMap.id : C →ₗ[S] C)
      (f.hom + g.hom) x =
      TensorProduct.AlgebraTensorModule.map (LinearMap.id : C →ₗ[S] C) f.hom x +
      TensorProduct.AlgebraTensorModule.map (LinearMap.id : C →ₗ[S] C) g.hom x
    induction x using TensorProduct.inductionOn with
    | tmul c m => exact TensorProduct.tmul_add _ _ _
    | add x y hx hy => simp only [map_add, hx, hy]; abel

abbrev coefficientComplex (K : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (C : Type w) [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C] :=
  ((coefficientTensorFunctor R S C).mapHomologicalComplex (ComplexShape.down ℕ)).obj K

/-- Over a commutative ring we put the coefficient first to keep its outer
scalar action definitional. The bridge below explicitly identifies this with
Chapter 11's right-left Tor, including its cycle formula. -/
abbrev commutativeTor {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ) :=
  Homology (coefficientComplex (S := R) P.complex B) n

abbrev restrictedTor {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (C : Type w) [AddCommGroup C] [Module S C]
    [Module R C] [IsScalarTower R S C] (n : ℕ) :=
  Homology (coefficientComplex (S := S) P.complex C) n

/-- The canonical right resolution attached to a commutative left resolution. -/
abbrev rightResolution {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) :=
  P103.Specs.Ch11.TorBalance.commRightResolution P

/-- The ordinary projective resolution obtained by extension, with no
finiteness hypotheses. Its complex and augmentation are prescribed. -/
structure ExtendedResolution {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) where
  resolution : LeftResolution S (S ⊗[R] A)
  projective : resolution.IsProjective
  complexIso : resolution.complex ≅ extendComplex S P.complex
  augmentation : ∀ (s : S) (p : P.complex.X 0),
    resolution.ε ((complexIso.inv.f 0).hom (s ⊗ₜ[R] p)) = s ⊗ₜ[R] P.ε p

/-- Formula for the first chain comparison, with the coefficient-first
convention converted explicitly to the order in the manuscript. -/
def FirstComparison (K : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (C : Type w) [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (e : coefficientComplex (S := S) (R := S) (extendComplex S K) C ≅
      coefficientComplex (S := S) K C) : Prop :=
  (∀ n (s : S) (p : K.X n) (c : C),
    (e.hom.f n).hom (c ⊗ₜ[S] (s ⊗ₜ[R] p)) = (s • c) ⊗ₜ[R] p) ∧
  (∀ n (p : K.X n) (c : C),
    (e.inv.f n).hom (c ⊗ₜ[R] p) = c ⊗ₜ[S] ((1 : S) ⊗ₜ[R] p))

def first_tensor_comparisonType : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (C : Type w)
    [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C],
    ∃ e : coefficientComplex (S := S) (R := S) (extendComplex S K) C ≅
      coefficientComplex (S := S) K C, FirstComparison K C e

def extension_resolutionType : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (A : Type v) [AddCommGroup A] [Module R A] (P : LeftResolution R A),
    P.IsProjective → Nonempty (ExtendedResolution (S := S) P)

/-- Exact extension commutes with the concrete quotient homology. Naturality
and the representative formula are included, rather than an arbitrary iso. -/
structure HomologyExtension (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  equiv : ∀ (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (n : ℕ),
    S ⊗[R] Homology K n ≃ₗ[S] Homology (extendComplex S K) n
  cycle : ∀ K n (s : S) (z : cycles K n),
    ∃ z' : cycles (extendComplex S K) n,
      z'.val = s ⊗ₜ[R] z.val ∧
      equiv K n (s ⊗ₜ[R] homologyClass K n z) = homologyClass _ n z'
  natural : ∀ {K L : ChainComplex (ModuleCat.{max u v} R) ℕ} (f : K ⟶ L) n x,
    equiv L n ((homologyMap f n).baseChange S x) =
      homologyMap (((extensionFunctor R S).mapHomologicalComplex
        (ComplexShape.down ℕ)).map f) n (equiv K n x)

def homology_extensionType : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S],
    Nonempty (HomologyExtension.{u,v} R S)

/-- Simultaneous maps of the resolution complex and the coefficient. -/
def coefficientMap {K L : ChainComplex (ModuleCat.{max u v} R) ℕ}
    (f : K ⟶ L) {C D : Type w} [AddCommGroup C] [AddCommGroup D]
    [Module S C] [Module S D] [Module R C] [Module R D]
    [IsScalarTower R S C] [IsScalarTower R S D] (g : C →ₗ[S] D) :
    coefficientComplex (S := S) K C ⟶ coefficientComplex (S := S) L D where
  f n := ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.map g (f.f n).hom)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change TensorProduct.AlgebraTensorModule.map (LinearMap.id : D →ₗ[S] D)
      (L.d i j).hom (TensorProduct.AlgebraTensorModule.map g (f.f i).hom x) =
      TensorProduct.AlgebraTensorModule.map g (f.f j).hom
        (TensorProduct.AlgebraTensorModule.map (LinearMap.id : C →ₗ[S] C) (K.d i j).hom x)
    have h : (L.d i j).hom.comp (f.f i).hom = (f.f j).hom.comp (K.d i j).hom :=
      congrArg ModuleCat.Hom.hom (f.comm i j)
    have hn : ∀ c p, TensorProduct.tmul R (g c) ((L.d i j).hom ((f.f i).hom p)) =
        TensorProduct.tmul R (g c) ((f.f j).hom ((K.d i j).hom p)) :=
      fun c p => congrArg (TensorProduct.tmul R (g c)) (LinearMap.congr_fun h p)
    induction x using TensorProduct.inductionOn with
    | tmul c p => exact hn c p
    | add x y hx hy =>
      simp only [LinearMap.map_add, hx, hy]

abbrev extensionMap {K L : ChainComplex (ModuleCat.{max u v} R) ℕ} (f : K ⟶ L) :=
  ((extensionFunctor R S).mapHomologicalComplex (ComplexShape.down ℕ)).map f

/-- The canonical map from the common right-left tensor to the ordinary
commutative tensor, with the coefficient first. -/
def balancedToTensor (A : Type v) (B : Type w) [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] :
    letI := P103.BalancedTensor.commRightModule R A
    P103.BalancedTensor.Tensor R A B →ₗ[ℤ] B ⊗[R] A := by
  letI := P103.BalancedTensor.commRightModule R A
  let h := (TensorProduct.comm R A B).toLinearMap.restrictScalars ℤ
    |>.comp (TensorProduct.mapOfCompatibleSMul R ℤ ℤ A B)
  exact (P103.BalancedTensor.relations R A B).liftQ h (by
    apply Submodule.span_le.mpr
    rintro z ⟨r, a, b, rfl⟩
    change h (TensorProduct.tmul ℤ (r • a) b - TensorProduct.tmul ℤ a (r • b)) = 0
    rw [map_sub]
    change TensorProduct.tmul R b (r • a) - TensorProduct.tmul R (r • b) a = 0
    rw [TensorProduct.smul_tmul, sub_self])


/-- The representation is linked to the exact shared Chapter 11 Tor object,
not merely to an abstract isomorphic group. -/
structure TorBridge (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  equiv : ∀ {A : Type v} [AddCommGroup A] [Module R A] (P : LeftResolution R A)
    (C : Type w) [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C] (n : ℕ),
    letI := P103.BalancedTensor.commRightModule R A
    P103.Specs.Ch11.ExtTorDefinitions.TorWith (rightResolution P) C n ≃+
      restrictedTor (S := S) P C n
  cycle : ∀ {A : Type v} [AddCommGroup A] [Module R A] (P : LeftResolution R A)
    (C : Type w) [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C] n,
    letI := P103.BalancedTensor.commRightModule R A
    ∀ z : cycles (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex (rightResolution P).complex C) n,
    ∃ z' : cycles (coefficientComplex (S := S) P.complex C) n,
      z'.val = balancedToTensor (P.complex.X n) C z.val ∧
      equiv P C n (homologyClass _ n z) = homologyClass _ n z'
  scalar : ∀ {A : Type v} [AddCommGroup A] [Module R A] (P : LeftResolution R A)
    (C : Type w) [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C] n (s : S),
    letI := P103.BalancedTensor.commRightModule R A
    ∀ x, equiv P C n
      (homologyMap (P103.Specs.Ch11.ExtTorDefinitions.tensorSecondMap (rightResolution P).complex
        ((s • (LinearMap.id : C →ₗ[S] C)).restrictScalars R)) n x) =
      s • equiv P C n x
  projective : ∀ {A : Type v} [AddCommGroup A] [Module R A] (P : LeftResolution R A),
    P.IsProjective →
    letI := P103.BalancedTensor.commRightModule R A
    (rightResolution P).IsProjective
  natural : ∀ {A A' : Type v} [AddCommGroup A] [AddCommGroup A'] [Module R A] [Module R A']
    (P : LeftResolution R A) (Q : LeftResolution R A')
    {C D : Type w} [AddCommGroup C] [AddCommGroup D] [Module S C] [Module S D]
    [Module R C] [Module R D] [IsScalarTower R S C] [IsScalarTower R S D]
    (l : P.complex ⟶ Q.complex) (g : C →ₗ[S] D) n,
    letI := P103.BalancedTensor.commRightModule R A
    letI := P103.BalancedTensor.commRightModule R A'
    ∀ x, equiv Q D n
      (homologyMap (P103.Specs.Ch11.ExtTorDefinitions.tensorFirstMap
          (((P103.Specs.Ch11.TorBalance.commRightFunctor R).mapHomologicalComplex
            (ComplexShape.down ℕ)).map l) C ≫
        P103.Specs.Ch11.ExtTorDefinitions.tensorSecondMap (rightResolution Q).complex
          (g.restrictScalars R)) n x) =
      homologyMap (coefficientMap (S := S) l g) n (equiv P C n x)

/-- A single natural comparison, simultaneously for all modules and all
ordinary projective resolutions. Naturality for lifts of the identity is the
canonical independence of resolution choices. The separate `lift_independent`
field ensures that changing a lift cannot alter those comparisons. -/
structure FlatTorBaseChange (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  extension : ∀ {A : Type v} [AddCommGroup A] [Module R A] (P : LeftResolution R A),
    P.IsProjective → ExtendedResolution (S := S) P
  homology : HomologyExtension.{u,max v w} R S
  bridgeR : TorBridge.{u,v,w} R R
  bridgeS : TorBridge.{u,max u v,max u w} S S
  bridgeSOriginalCoefficient : TorBridge.{u,max u v,w} S S
  bridgeRestricted : TorBridge.{u,v,w} R S
  firstChain : ∀ (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (C : Type w)
    [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C],
    coefficientComplex (R := S) (S := S) (extendComplex S K) C ≅
      coefficientComplex (S := S) K C
  first_formula : ∀ (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (C : Type w) [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C],
    FirstComparison (S := S) K C (firstChain K C)
  secondChain : ∀ (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (B : Type w)
    [AddCommGroup B] [Module R B],
    extendComplex.{u,max v w} S (coefficientComplex (S := R) K B) ≅
      coefficientComplex (R := S) (S := S) (extendComplex S K) (S ⊗[R] B)
  second_formula : ∀ (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (B : Type w)
    [AddCommGroup B] [Module R B] (n : ℕ) (s : S) (b : B) (p : K.X n),
    ((secondChain K B).hom.f n).hom (s ⊗ₜ[R] (b ⊗ₜ[R] p)) =
      (s ⊗ₜ[R] b) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] p)
  first : ∀ {A : Type v} [AddCommGroup A] [Module R A] (P : LeftResolution R A)
    (C : Type w) [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C] n,
    Homology (coefficientComplex (R := S) (S := S) (extendComplex S P.complex) C) n ≃ₗ[S]
      restrictedTor (S := S) P C n
  first_induced : ∀ {A : Type v} [AddCommGroup A] [Module R A] (P : LeftResolution R A)
    (C : Type w) [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C] n,
    (first P C n).toLinearMap = homologyMap (firstChain P.complex C).hom n
  second : ∀ {A : Type v} [AddCommGroup A] [Module R A] (P : LeftResolution R A)
    (B : Type w) [AddCommGroup B] [Module R B] n,
    S ⊗[R] commutativeTor P B n ≃ₗ[S]
      Homology (coefficientComplex (R := S) (S := S) (extendComplex S P.complex) (S ⊗[R] B)) n
  second_induced : ∀ {A : Type v} [AddCommGroup A] [Module R A] (P : LeftResolution R A)
    (B : Type w) [AddCommGroup B] [Module R B] n,
    (second P B n).toLinearMap =
      (homologyMap (secondChain P.complex B).hom n).comp
        (homology.equiv (coefficientComplex (S := R) P.complex B) n).toLinearMap
  first_natural : ∀ {A A' : Type v} [AddCommGroup A] [AddCommGroup A']
    [Module R A] [Module R A'] (P : LeftResolution R A) (Q : LeftResolution R A')
    {C D : Type w} [AddCommGroup C] [AddCommGroup D] [Module S C] [Module S D]
    [Module R C] [Module R D] [IsScalarTower R S C] [IsScalarTower R S D]
    (l : P.complex ⟶ Q.complex) (g : C →ₗ[S] D) n x,
    first Q D n (homologyMap (coefficientMap (R := S) (S := S) (extensionMap (S := S) l) g) n x) =
      homologyMap (coefficientMap (R := R) (S := S) l g) n (first P C n x)
  second_natural : ∀ {A A' : Type v} [AddCommGroup A] [AddCommGroup A']
    [Module R A] [Module R A'] (P : LeftResolution R A) (Q : LeftResolution R A')
    {B D : Type w} [AddCommGroup B] [AddCommGroup D] [Module R B] [Module R D]
    (l : P.complex ⟶ Q.complex) (g : B →ₗ[R] D) n x,
    second Q D n ((homologyMap (coefficientMap (S := R) l g) n).baseChange S x) =
      homologyMap (coefficientMap (R := S) (S := S) (extensionMap (S := S) l) (g.baseChange S)) n (second P B n x)
  lift_independent : ∀ {A A' : Type v} [AddCommGroup A] [AddCommGroup A']
    [Module R A] [Module R A'] (P : LeftResolution R A) (Q : LeftResolution R A'),
    P.IsProjective → ∀ (f : A →ₗ[R] A') (l l' : P.complex ⟶ Q.complex),
    ChainLift P Q f l → ChainLift P Q f l' →
    ∀ (C : Type w) [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C] n,
      homologyMap (coefficientMap (S := S) l (LinearMap.id : C →ₗ[S] C)) n =
        homologyMap (coefficientMap (S := S) l' (LinearMap.id : C →ₗ[S] C)) n
  original_lift_independent : ∀ {A A' : Type v} [AddCommGroup A] [AddCommGroup A']
    [Module R A] [Module R A'] (P : LeftResolution R A) (Q : LeftResolution R A'),
    P.IsProjective → ∀ (f : A →ₗ[R] A') (l l' : P.complex ⟶ Q.complex),
    ChainLift P Q f l → ChainLift P Q f l' →
    ∀ (B : Type w) [AddCommGroup B] [Module R B] n,
      homologyMap (coefficientMap (S := R) l (LinearMap.id : B →ₗ[R] B)) n =
        homologyMap (coefficientMap (S := R) l' (LinearMap.id : B →ₗ[R] B)) n

def flat_base_changeType : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S],
    Nonempty (FlatTorBaseChange.{u,v,w} R S)

end
end P103.Specs.Ch12.TorBaseChange
