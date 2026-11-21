import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.TorBalance
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.HorseshoeNaturality

/-! Tor exact sequences, paper.tex 2715–2717, 2736–2759, 2773–2777.
All tensors are the original right-left balanced quotients, over arbitrary
unital rings. Resolutions are ordinary nonnegative resolutions. The predicate
`Connecting` fixes the positive lift-and-differentiate sign of paper.tex 2311–2319.
These specifications contain no candidate imports or assumed proof certificates.
-/
namespace P103.Specs.Ch11.TorExactSequences
open CategoryTheory
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.HomologySequence
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
noncomputable section
universe u v w

/-- A complete nonnegative homology sequence, including its final surjection.
Using `n+1,n` includes every positive degree and avoids truncated subtraction. -/
def LongExact {S : Type u} [Ring S]
    {U V W : ChainComplex (ModuleCat.{v} S) ℕ}
    (i : U ⟶ V) (p : V ⟶ W) : Prop :=
  (∃ δ : ∀ n : ℕ, Homology W (n+1) →ₗ[S] Homology U n,
    ∀ n, Connecting i p (n+1) n (δ n) ∧ SequenceExact i p (n+1) n (δ n)) ∧
  Function.Exact (homologyMap i 0) (homologyMap p 0) ∧
  Function.Surjective (homologyMap p 0)

/-- Existence of a horseshoe and the whole first-variable sequence for every
prescribed pair of outside resolutions. The second clause allows every
horseshoe, which is needed for canonical independence. -/
def first_sequenceType : Prop :=
  ∀ (R : Type u) [Ring R] (A M C : Type v)
    [AddCommGroup A] [AddCommGroup M] [AddCommGroup C]
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ C]
    (i : A →ₗ[Rᵐᵒᵖ] M) (p : M →ₗ[Rᵐᵒᵖ] C),
    Function.Injective i → Function.Exact i p → Function.Surjective p →
    ∀ (L : LeftResolution Rᵐᵒᵖ A) (N : LeftResolution Rᵐᵒᵖ C),
    L.IsProjective → N.IsProjective →
    ∀ (B : Type w) [AddCommGroup B] [Module R B],
      Nonempty (P103.Specs.Ch10.Horseshoe.ProjectiveData i p L N) ∧
      ∀ H : P103.Specs.Ch10.Horseshoe.ProjectiveData i p L N,
        LongExact (tensorFirstMap H.inclusion B) (tensorFirstMap H.projection B)

/-- Second-variable Tor uses the same right projective resolution as the
original definition, with no flatness hypothesis on any coefficient. -/
def second_sequenceType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (P : LeftResolution Rᵐᵒᵖ A), P.IsProjective →
    ∀ (B M C : Type w) [AddCommGroup B] [AddCommGroup M] [AddCommGroup C]
      [Module R B] [Module R M] [Module R C]
      (i : B →ₗ[R] M) (p : M →ₗ[R] C),
      Function.Injective i → Function.Exact i p → Function.Surjective p →
      LongExact (tensorSecondMap P.complex i) (tensorSecondMap P.complex p)

/-- The stated terminal tensor sequences, with their actual tensor arrows.
The canonical zero-degree identifications below connect these to `LongExact`. -/
def terminalType : Prop :=
  (∀ (R : Type u) [Ring R] (A M C : Type v) (B : Type w)
    [AddCommGroup A] [AddCommGroup M] [AddCommGroup C] [AddCommGroup B]
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ C] [Module R B]
    (i : A →ₗ[Rᵐᵒᵖ] M) (p : M →ₗ[Rᵐᵒᵖ] C),
    Function.Exact i p → Function.Surjective p →
    Function.Exact (tensorMap i (LinearMap.id : B →ₗ[R] B))
      (tensorMap p (LinearMap.id : B →ₗ[R] B)) ∧
    Function.Surjective (tensorMap p (LinearMap.id : B →ₗ[R] B))) ∧
  (∀ (R : Type u) [Ring R] (A : Type v) (B M C : Type w)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup M] [AddCommGroup C]
    [Module Rᵐᵒᵖ A] [Module R B] [Module R M] [Module R C]
    (i : B →ₗ[R] M) (p : M →ₗ[R] C),
    Function.Exact i p → Function.Surjective p →
    Function.Exact (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) i)
      (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) p) ∧
    Function.Surjective (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) p))

/-- These are the canonical quotient identifications at zero, together with
every simultaneous resolution/coefficient naturality square. -/
def zero_identificationType : Prop :=
  tor_zeroType.{u,v,w} ∧ tor_zero_naturalType.{u,v,w}

/-- Canonical naturality for the first-variable connecting maps. All
horseshoes and resolutions, and every Tor action satisfying the established
bifunctor interface, are retained. Identity diagrams give canonical transport
when resolutions or horseshoes change. The other sequence squares are
already part of the `TorMaps.comp` law. -/
def first_naturalityType : Prop :=
  ∀ (R : Type u) [Ring R]
    (A M C A' M' C' : ModuleCat.{v} Rᵐᵒᵖ)
    (i : A ⟶ M) (p : M ⟶ C) (i' : A' ⟶ M') (p' : M' ⟶ C')
    (a : A ⟶ A') (b : M ⟶ M') (c : C ⟶ C'),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    Function.Injective i'.hom → Function.Exact i'.hom p'.hom → Function.Surjective p'.hom →
    i ≫ b = a ≫ i' → p ≫ c = b ≫ p' →
    ∀ (L : ProjectiveChoice Rᵐᵒᵖ A) (N : ProjectiveChoice Rᵐᵒᵖ C)
      (L' : ProjectiveChoice Rᵐᵒᵖ A') (N' : ProjectiveChoice Rᵐᵒᵖ C')
      (H : P103.Specs.Ch10.Horseshoe.ProjectiveData i.hom p.hom L.val N.val)
      (H' : P103.Specs.Ch10.Horseshoe.ProjectiveData i'.hom p'.hom L'.val N'.val)
      (B B' : ModuleCat.{w} R) (g : B ⟶ B') (n : ℕ)
      (Tn : TorMaps.{u,v,w} R (n+1)) (Tm : TorMaps.{u,v,w} R n)
      (δ : TorWith N.val B (n+1) →ₗ[ℤ] TorWith L.val B n)
      (ε : TorWith N'.val B' (n+1) →ₗ[ℤ] TorWith L'.val B' n),
      Connecting (tensorFirstMap H.inclusion B) (tensorFirstMap H.projection B) (n+1) n δ →
      Connecting (tensorFirstMap H'.inclusion B') (tensorFirstMap H'.projection B') (n+1) n ε →
      (Tm.map L L' a g).comp δ = ε.comp (Tn.map N N' c g)

/-- The second-variable connecting map is natural simultaneously in its
short exact diagram and the fixed right variable. This also gives transport
between every two projective resolutions of that variable. -/
def second_naturalityType : Prop :=
  ∀ (R : Type u) [Ring R] (A A' : ModuleCat.{v} Rᵐᵒᵖ)
    (P : ProjectiveChoice Rᵐᵒᵖ A) (P' : ProjectiveChoice Rᵐᵒᵖ A') (a : A ⟶ A')
    (B M C B' M' C' : ModuleCat.{w} R)
    (i : B ⟶ M) (p : M ⟶ C) (i' : B' ⟶ M') (p' : M' ⟶ C')
    (b : B ⟶ B') (m : M ⟶ M') (c : C ⟶ C'),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    Function.Injective i'.hom → Function.Exact i'.hom p'.hom → Function.Surjective p'.hom →
    i ≫ m = b ≫ i' → p ≫ c = m ≫ p' →
    ∀ (n : ℕ) (Tn : TorMaps.{u,v,w} R (n+1)) (Tm : TorMaps.{u,v,w} R n)
      (δ : TorWith P.val C (n+1) →ₗ[ℤ] TorWith P.val B n)
      (ε : TorWith P'.val C' (n+1) →ₗ[ℤ] TorWith P'.val B' n),
      Connecting (tensorSecondMap P.val.complex i.hom)
        (tensorSecondMap P.val.complex p.hom) (n+1) n δ →
      Connecting (tensorSecondMap P'.val.complex i'.hom)
        (tensorSecondMap P'.val.complex p'.hom) (n+1) n ε →
      (Tm.map P P' a b).comp δ = ε.comp (Tn.map P P' a c)

/-- A morphism of homology sequences, retaining both ordinary squares and
all connecting squares with the source's positive sign. -/
def SequenceComparison {S : Type u} [Ring S]
    {U V W U' V' W' : ChainComplex (ModuleCat.{v} S) ℕ}
    (i : U ⟶ V) (p : V ⟶ W) (i' : U' ⟶ V') (p' : V' ⟶ W')
    (a : U ⟶ U') (b : V ⟶ V') (c : W ⟶ W') : Prop :=
  i ≫ b = a ≫ i' ∧ p ≫ c = b ≫ p' ∧
  ∀ (n : ℕ) (δ : Homology W (n+1) →ₗ[S] Homology U n)
    (ε : Homology W' (n+1) →ₗ[S] Homology U' n),
    Connecting i p (n+1) n δ → Connecting i' p' (n+1) n ε →
    (homologyMap a n).comp δ = ε.comp (homologyMap c (n+1))

abbrev leftResolutionMap {R : Type u} [Ring R]
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {D E : ChainComplex (ModuleCat.{w} R) ℕ} (f : D ⟶ E) :=
  ((leftTensorFunctor A).mapHomologicalComplex (ComplexShape.down ℕ)).map f

section FirstBalance
variable {R : Type u} [Ring R] {A M C : Type v} {B : Type w}
  [AddCommGroup A] [AddCommGroup M] [AddCommGroup C] [AddCommGroup B]
  [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ C] [Module R B]
  {i : A →ₗ[Rᵐᵒᵖ] M} {p : M →ₗ[Rᵐᵒᵖ] C}
  {L : LeftResolution Rᵐᵒᵖ A} {N : LeftResolution Rᵐᵒᵖ C}

/-- Both actual balance augmentations are morphisms of the first-variable
sequences. No extra sign or arbitrary identification enters the comparison.
The property is stated for every augmentation map. The upstream balance
theorem supplies the quasi-isomorphisms used by `balanced_connectingType`. -/
def FirstBalance (H : P103.Specs.Ch10.Horseshoe.ProjectiveData i p L N)
    (Q : LeftResolution R B) : Prop :=
  ∀ (α : Augmentations L Q) (β : Augmentations H.middle Q) (γ : Augmentations N Q),
    LongExact (ordinaryTotalMap H.inclusion (𝟙 Q.complex))
      (ordinaryTotalMap H.projection (𝟙 Q.complex)) ∧
    LongExact (leftTensorFirstMap i Q.complex) (leftTensorFirstMap p Q.complex) ∧
    SequenceComparison
      (ordinaryTotalMap H.inclusion (𝟙 Q.complex))
      (ordinaryTotalMap H.projection (𝟙 Q.complex))
      (tensorFirstMap H.inclusion B) (tensorFirstMap H.projection B)
      α.left β.left γ.left ∧
    SequenceComparison
      (ordinaryTotalMap H.inclusion (𝟙 Q.complex))
      (ordinaryTotalMap H.projection (𝟙 Q.complex))
      (leftTensorFirstMap i Q.complex) (leftTensorFirstMap p Q.complex)
      α.right β.right γ.right
end FirstBalance

section SecondBalance
variable {R : Type u} [Ring R] {A : Type v} {B M C : Type w}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup M] [AddCommGroup C]
  [Module Rᵐᵒᵖ A] [Module R B] [Module R M] [Module R C]
  {i : B →ₗ[R] M} {p : M →ₗ[R] C}
  {L : LeftResolution R B} {N : LeftResolution R C}

/-- The analogous comparison for the second-variable sequence constructed
in the original right-resolution model and the balanced left-resolution model. -/
def SecondBalance (P : LeftResolution Rᵐᵒᵖ A)
    (H : P103.Specs.Ch10.Horseshoe.ProjectiveData i p L N) : Prop :=
  ∀ (α : Augmentations P L) (β : Augmentations P H.middle) (γ : Augmentations P N),
    LongExact (ordinaryTotalMap (𝟙 P.complex) H.inclusion)
      (ordinaryTotalMap (𝟙 P.complex) H.projection) ∧
    LongExact (leftResolutionMap A H.inclusion) (leftResolutionMap A H.projection) ∧
    SequenceComparison
      (ordinaryTotalMap (𝟙 P.complex) H.inclusion)
      (ordinaryTotalMap (𝟙 P.complex) H.projection)
      (tensorSecondMap P.complex i) (tensorSecondMap P.complex p)
      α.left β.left γ.left ∧
    SequenceComparison
      (ordinaryTotalMap (𝟙 P.complex) H.inclusion)
      (ordinaryTotalMap (𝟙 P.complex) H.projection)
      (leftResolutionMap A H.inclusion) (leftResolutionMap A H.projection)
      α.right β.right γ.right
end SecondBalance

def balance_compatibilityType : Prop :=
  (∀ (R : Type u) [Ring R] (A M C : Type v) (B : Type w)
    [AddCommGroup A] [AddCommGroup M] [AddCommGroup C] [AddCommGroup B]
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ C] [Module R B]
    (i : A →ₗ[Rᵐᵒᵖ] M) (p : M →ₗ[Rᵐᵒᵖ] C),
    Function.Injective i → Function.Exact i p → Function.Surjective p →
    ∀ (L : LeftResolution Rᵐᵒᵖ A) (N : LeftResolution Rᵐᵒᵖ C) (Q : LeftResolution R B),
    L.IsProjective → N.IsProjective → Q.IsProjective →
    ∀ H : P103.Specs.Ch10.Horseshoe.ProjectiveData i p L N, FirstBalance H Q) ∧
  (∀ (R : Type u) [Ring R] (A : Type v) (B M C : Type w)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup M] [AddCommGroup C]
    [Module Rᵐᵒᵖ A] [Module R B] [Module R M] [Module R C]
    (i : B →ₗ[R] M) (p : M →ₗ[R] C),
    Function.Injective i → Function.Exact i p → Function.Surjective p →
    ∀ (P : LeftResolution Rᵐᵒᵖ A) (L : LeftResolution R B) (N : LeftResolution R C),
    P.IsProjective → L.IsProjective → N.IsProjective →
    ∀ H : P103.Specs.Ch10.Horseshoe.ProjectiveData i p L N, SecondBalance P H)

/-- In the commutative case the first connecting arrow is linear for the
actual natural scalar actions induced by coefficient endomorphisms. -/
def first_connecting_linearType : Prop :=
  ∀ (K : Type u) [CommRing K] (A M C : ModuleCat.{v} Kᵐᵒᵖ)
    (i : A ⟶ M) (p : M ⟶ C),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    ∀ (L : ProjectiveChoice Kᵐᵒᵖ A) (N : ProjectiveChoice Kᵐᵒᵖ C)
      (H : P103.Specs.Ch10.Horseshoe.ProjectiveData i.hom p.hom L.val N.val)
      (B : ModuleCat.{w} K) (n : ℕ)
      (Tn : TorMaps.{u,v,w} K (n+1)) (Tm : TorMaps.{u,v,w} K n)
      (δ : TorWith N.val B (n+1) →ₗ[ℤ] TorWith L.val B n),
      Connecting (tensorFirstMap H.inclusion B) (tensorFirstMap H.projection B) (n+1) n δ →
      letI := torModule Tn N B
      letI := torModule Tm L B
      ∀ (r : K) x, δ (r • x) = r • δ x

/-- The same natural scalar linearity for the second connecting arrow. -/
def second_connecting_linearType : Prop :=
  ∀ (K : Type u) [CommRing K] (A : ModuleCat.{v} Kᵐᵒᵖ)
    (P : ProjectiveChoice Kᵐᵒᵖ A) (B M C : ModuleCat.{w} K)
    (i : B ⟶ M) (p : M ⟶ C),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    ∀ (n : ℕ) (Tn : TorMaps.{u,v,w} K (n+1)) (Tm : TorMaps.{u,v,w} K n)
      (δ : TorWith P.val C (n+1) →ₗ[ℤ] TorWith P.val B n),
      Connecting (tensorSecondMap P.val.complex i.hom)
        (tensorSecondMap P.val.complex p.hom) (n+1) n δ →
      letI := torModule Tn P C
      letI := torModule Tm P B
      ∀ (r : K) x, δ (r • x) = r • δ x

def connecting_linearType : Prop :=
  first_connecting_linearType.{u,v,w} ∧ second_connecting_linearType.{u,v,w}

/-- The last positive connecting arrow is explicitly spliced to the tensor
term. Its representative formula fixes the sign after the Tor₀ identification. -/
def first_tensor_spliceType : Prop :=
  ∀ (R : Type u) [Ring R] (A M C : Type v)
    [AddCommGroup A] [AddCommGroup M] [AddCommGroup C]
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ C]
    (i : A →ₗ[Rᵐᵒᵖ] M) (p : M →ₗ[Rᵐᵒᵖ] C),
    Function.Injective i → Function.Exact i p → Function.Surjective p →
    ∀ (L : LeftResolution Rᵐᵒᵖ A) (N : LeftResolution Rᵐᵒᵖ C),
    L.IsProjective → N.IsProjective →
    ∀ (B : Type w) [AddCommGroup B] [Module R B]
      (H : P103.Specs.Ch10.Horseshoe.ProjectiveData i p L N),
    ∃ δ : TorWith N B 1 →+ Tensor R A B,
      Function.Exact (homologyMap (tensorFirstMap H.projection B) 1) δ ∧
      Function.Exact δ (tensorMap i (LinearMap.id : B →ₗ[R] B)) ∧
      Function.Exact (tensorMap i (LinearMap.id : B →ₗ[R] B))
        (tensorMap p (LinearMap.id : B →ₗ[R] B)) ∧
      Function.Surjective (tensorMap p (LinearMap.id : B →ₗ[R] B)) ∧
      ∀ (z : cycles (tensorComplex N.complex B) 1)
        (b : (tensorComplex H.middle.complex B).X 1)
        (a : cycles (tensorComplex L.complex B) 0),
        (tensorFirstMap H.projection B).f 1 b = z.val →
        (tensorFirstMap H.inclusion B).f 0 a.val =
          (tensorComplex H.middle.complex B).d 1 0 b →
        δ (homologyClass _ 1 z) = tensorMap L.ε LinearMap.id a.val

/-- The original right resolution also supplies the second-variable tensor
splice, with the same explicit positive representative formula. -/
def second_tensor_spliceType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (P : LeftResolution Rᵐᵒᵖ A), P.IsProjective →
    ∀ (B M C : Type w) [AddCommGroup B] [AddCommGroup M] [AddCommGroup C]
      [Module R B] [Module R M] [Module R C]
      (i : B →ₗ[R] M) (p : M →ₗ[R] C),
      Function.Injective i → Function.Exact i p → Function.Surjective p →
      ∃ δ : TorWith P C 1 →+ Tensor R A B,
        Function.Exact (homologyMap (tensorSecondMap P.complex p) 1) δ ∧
        Function.Exact δ (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) i) ∧
        Function.Exact (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) i)
          (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) p) ∧
        Function.Surjective (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) p) ∧
        ∀ (z : cycles (tensorComplex P.complex C) 1)
          (b : (tensorComplex P.complex M).X 1)
          (a : cycles (tensorComplex P.complex B) 0),
          (tensorSecondMap P.complex p).f 1 b = z.val →
          (tensorSecondMap P.complex i).f 0 a.val = (tensorComplex P.complex M).d 1 0 b →
          δ (homologyClass _ 1 z) = tensorMap P.ε LinearMap.id a.val

/-- The two models' connecting arrows commute with actual balanced
identifications, in both variables and with the positive connecting sign. -/
def balanced_connectingType : Prop :=
  (∀ (R : Type u) [Ring R] (A M C : Type v) (B : Type w)
    [AddCommGroup A] [AddCommGroup M] [AddCommGroup C] [AddCommGroup B]
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ C] [Module R B]
    (i : A →ₗ[Rᵐᵒᵖ] M) (p : M →ₗ[Rᵐᵒᵖ] C),
    Function.Injective i → Function.Exact i p → Function.Surjective p →
    ∀ (L : LeftResolution Rᵐᵒᵖ A) (N : LeftResolution Rᵐᵒᵖ C)
      (Q : LeftResolution R B),
    L.IsProjective → N.IsProjective → Q.IsProjective →
    ∀ H : P103.Specs.Ch10.Horseshoe.ProjectiveData i p L N,
    ∃ (α : Augmentations L Q) (γ : Augmentations N Q)
      (hαL : QuasiIsomorphism α.left) (hαR : QuasiIsomorphism α.right)
      (hγL : QuasiIsomorphism γ.left) (hγR : QuasiIsomorphism γ.right),
      ∀ (n : ℕ) (δ : TorWith N B (n+1) →ₗ[ℤ] TorWith L B n)
        (ε : Homology (leftOrdinaryTensorComplex C Q.complex) (n+1) →ₗ[ℤ]
          Homology (leftOrdinaryTensorComplex A Q.complex) n),
      Connecting (tensorFirstMap H.inclusion B) (tensorFirstMap H.projection B)
        (n+1) n δ →
      Connecting (leftTensorFirstMap i Q.complex) (leftTensorFirstMap p Q.complex)
        (n+1) n ε →
      (balanceEquiv α hαL hαR n).toLinearMap.comp δ =
        ε.comp (balanceEquiv γ hγL hγR (n+1)).toLinearMap) ∧
  (∀ (R : Type u) [Ring R] (A : Type v) (B M C : Type w)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup M] [AddCommGroup C]
    [Module Rᵐᵒᵖ A] [Module R B] [Module R M] [Module R C]
    (i : B →ₗ[R] M) (p : M →ₗ[R] C),
    Function.Injective i → Function.Exact i p → Function.Surjective p →
    ∀ (P : LeftResolution Rᵐᵒᵖ A) (L : LeftResolution R B)
      (N : LeftResolution R C),
    P.IsProjective → L.IsProjective → N.IsProjective →
    ∀ H : P103.Specs.Ch10.Horseshoe.ProjectiveData i p L N,
    ∃ (α : Augmentations P L) (γ : Augmentations P N)
      (hαL : QuasiIsomorphism α.left) (hαR : QuasiIsomorphism α.right)
      (hγL : QuasiIsomorphism γ.left) (hγR : QuasiIsomorphism γ.right),
      ∀ (n : ℕ) (δ : TorWith P C (n+1) →ₗ[ℤ] TorWith P B n)
        (ε : Homology (leftOrdinaryTensorComplex A N.complex) (n+1) →ₗ[ℤ]
          Homology (leftOrdinaryTensorComplex A L.complex) n),
      Connecting (tensorSecondMap P.complex i) (tensorSecondMap P.complex p)
        (n+1) n δ →
      Connecting (leftResolutionMap A H.inclusion) (leftResolutionMap A H.projection)
        (n+1) n ε →
      (balanceEquiv α hαL hαR n).toLinearMap.comp δ =
        ε.comp (balanceEquiv γ hγL hγR (n+1)).toLinearMap)

end
end P103.Specs.Ch11.TorExactSequences
