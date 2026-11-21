import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtExactSequences
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.TorExactSequences
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.VanishingAndFlatness
import Mathlib.LinearAlgebra.Isomorphisms

/-! Dimension shifting, paper.tex 2792–2833. The equivalences are fixed by the
positive connecting maps, including at degree zero. All choices of ordinary
projective resolutions and horseshoes are retained. Positive degrees are n+1,
so that the excluded edge is never asserted to be a positive-degree shift.
The second Ext sequence permits arbitrary coefficient universes by enlargement,
as required by the frozen injective-vanishing interface. -/
namespace P103.Specs.Ch11.DimensionShifting
open CategoryTheory
open P103.Specs.Ch10
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.HomologySequence P103.Specs.Ch10.Horseshoe
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch02.FlatnessTests
noncomputable section
universe u v w

/-- Cokernel in abelian groups, with its canonical integer module structure. -/
abbrev Coker {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (f : X →ₗ[ℤ] Y) := Y ⧸ LinearMap.range f

/-- The inverse of the source's displayed Ext shift is the connector. The
edge is prescribed on every Hom representative, not merely an abstract iso. -/
def ExtFirstOver (R : Type u) [Ring R] : Prop :=
  ∀ (K M A : ModuleCat.{v} R) (i : K ⟶ M) (p : M ⟶ A),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    Module.Projective R M →
    ∀ (B : ModuleCat.{w} R) (L : LeftResolution R K) (N : LeftResolution R A),
    L.IsProjective → N.IsProjective →
    Nonempty (ProjectiveData i.hom p.hom L N) ∧
    ∀ H : ProjectiveData i.hom p.hom L N,
    ∃ δ : ∀ n, ExtWith L B n →ₗ[ℤ] ExtWith N B (n+1),
      (∀ n, ExtExactSequences.FirstConnecting H B n (δ n)) ∧
      (∀ n, ∃ e : ExtWith N B (n+1+1) ≃ₗ[ℤ] ExtWith L B (n+1),
        e.symm.toLinearMap = δ (n+1)) ∧
      ∃ e : ExtWith N B 1 ≃ₗ[ℤ]
          Coker (P103.HomTensorExactness.pre (Q := B) i.hom).toIntLinearMap,
        ∀ h : K →ₗ[R] B,
          e.symm (Submodule.Quotient.mk h) = δ 0 (ExtExactSequences.homClass L B h)

def ext_firstType : Prop := ∀ (R : Type u) [Ring R], ExtFirstOver.{u,v,w} R

/-- Injectivity is used only for the middle coefficient, not for A or L. -/
def ExtSecondOver (R : Type u) [Ring R] : Prop :=
  ∀ (A : ModuleCat.{v} R) (P : LeftResolution R A), P.IsProjective →
    ∀ (B I L : ModuleCat.{max u w} R) (i : B ⟶ I) (p : I ⟶ L),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    Module.Injective R I →
    ∃ δ : ∀ n, ExtWith P L n →ₗ[ℤ] ExtWith P B (n+1),
      (∀ n, ExtExactSequences.SecondConnecting P i p n (δ n)) ∧
      (∀ n, ∃ e : ExtWith P B (n+1+1) ≃ₗ[ℤ] ExtWith P L (n+1),
        e.symm.toLinearMap = δ (n+1)) ∧
      ∃ e : ExtWith P B 1 ≃ₗ[ℤ]
          Coker (P103.HomTensorExactness.post (P := A) p.hom).toIntLinearMap,
        ∀ h : A →ₗ[R] L,
          e.symm (Submodule.Quotient.mk h) = δ 0 (ExtExactSequences.homClass P L h)

def ext_secondType : Prop := ∀ (R : Type u) [Ring R], ExtSecondOver.{u,v,w} R

def tor_firstType : Prop :=
  ∀ (R : Type u) [Ring R] (K F A : ModuleCat.{v} Rᵐᵒᵖ)
    (i : K ⟶ F) (p : F ⟶ A),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    RightFlat.{u,v,w} R F →
    ∀ (B : ModuleCat.{w} R) (L : LeftResolution Rᵐᵒᵖ K)
      (N : LeftResolution Rᵐᵒᵖ A), L.IsProjective → N.IsProjective →
    Nonempty (ProjectiveData i.hom p.hom L N) ∧
    ∀ H : ProjectiveData i.hom p.hom L N,
    ∃ δ : ∀ n, TorWith N B (n+1) →ₗ[ℤ] TorWith L B n,
      (∀ n, Connecting (tensorFirstMap H.inclusion B)
        (tensorFirstMap H.projection B) (n+1) n (δ n)) ∧
      (∀ n, ∃ e : TorWith N B (n+1+1) ≃ₗ[ℤ] TorWith L B (n+1),
        e.toLinearMap = δ (n+1)) ∧
      ∃ (z : TorWith L B 0 ≃+ P103.BalancedTensor.Tensor R K B)
        (e : TorWith N B 1 ≃ₗ[ℤ]
          LinearMap.ker (tensorMap i.hom (LinearMap.id : B →ₗ[R] B))),
        (∀ a, z (homologyClass _ 0 a) = tensorMap L.ε LinearMap.id a.val) ∧
        ∀ x, (e x).val = z (δ 0 x)

def tor_secondType : Prop :=
  ∀ (R : Type u) [Ring R] (A : ModuleCat.{v} Rᵐᵒᵖ)
    (P : LeftResolution Rᵐᵒᵖ A), P.IsProjective →
    ∀ (K F B : ModuleCat.{w} R) (i : K ⟶ F) (p : F ⟶ B),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    Flat.{u,w,v} R F →
    ∃ δ : ∀ n, TorWith P B (n+1) →ₗ[ℤ] TorWith P K n,
      (∀ n, Connecting (tensorSecondMap P.complex i.hom)
        (tensorSecondMap P.complex p.hom) (n+1) n (δ n)) ∧
      (∀ n, ∃ e : TorWith P B (n+1+1) ≃ₗ[ℤ] TorWith P K (n+1),
        e.toLinearMap = δ (n+1)) ∧
      ∃ (z : TorWith P K 0 ≃+ P103.BalancedTensor.Tensor R A K)
        (e : TorWith P B 1 ≃ₗ[ℤ]
          LinearMap.ker (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) i.hom)),
        (∀ a, z (homologyClass _ 0 a) = tensorMap P.ε LinearMap.id a.val) ∧
        ∀ x, (e x).val = z (δ 0 x)

/-- Full simultaneous naturality of the canonical connectors. It includes
identity diagrams (comparison of resolutions), changes in the short exact
sequence, and changes in the remaining coefficient. The next three laws
transport these squares to the displayed inverse, cokernel and kernel isos. -/
def connector_naturalityType : Prop :=
  ExtExactSequences.first_naturalType.{u,v,w} ∧
  ExtExactSequences.second_naturalType.{u,v,max u w} ∧
  TorExactSequences.first_naturalityType.{u,v,w} ∧
  TorExactSequences.second_naturalityType.{u,v,w} ∧
  ext_zero_naturalType.{u,v,w} ∧ ext_zero_naturalType.{u,v,max u w} ∧
  tor_zero_naturalType.{u,v,w}

/-- A square of connecting isomorphisms also commutes for their inverses. -/
def inverse_naturalityType : Prop :=
  ∀ (X Y X' Y' : Type (max u v w))
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y'],
  ∀ (e : X ≃ₗ[ℤ] Y) (e' : X' ≃ₗ[ℤ] Y')
    (a : X →ₗ[ℤ] X') (b : Y →ₗ[ℤ] Y'),
    b.comp e.toLinearMap = e'.toLinearMap.comp a →
      a.comp e.symm.toLinearMap = e'.symm.toLinearMap.comp b

/-- The actual induced map on cokernels commutes with any equivalences
prescribed on representatives by the connecting maps. -/
def cokernel_naturalityType : Prop :=
  ∀ (X Y Z X' Y' Z' : Type (max u v w))
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z'],
  ∀ (f : X →ₗ[ℤ] Y) (f' : X' →ₗ[ℤ] Y') (a : Y →ₗ[ℤ] Y')
    (h : LinearMap.range f ≤ (LinearMap.range f').comap a)
    (d : Y →ₗ[ℤ] Z) (d' : Y' →ₗ[ℤ] Z') (c : Z →ₗ[ℤ] Z')
    (e : Coker f ≃ₗ[ℤ] Z) (e' : Coker f' ≃ₗ[ℤ] Z'),
    (∀ y, e (Submodule.Quotient.mk y) = d y) →
    (∀ y, e' (Submodule.Quotient.mk y) = d' y) →
    c.comp d = d'.comp a →
    ∀ q, e' ((LinearMap.range f).mapQ (LinearMap.range f') a h q) = c (e q)

/-- Naturality in actual kernel submodules, including the degree-zero tensor
identifications. The equality in the ambient module determines the kernel map. -/
def kernel_naturalityType : Prop :=
  ∀ (X Y Z X' Y' Z' : Type (max u v w))
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z'],
  ∀ (g : Y →ₗ[ℤ] Z) (g' : Y' →ₗ[ℤ] Z')
    (d : X →ₗ[ℤ] Y) (d' : X' →ₗ[ℤ] Y')
    (a : X →ₗ[ℤ] X') (b : Y →ₗ[ℤ] Y')
    (e : X ≃ₗ[ℤ] LinearMap.ker g) (e' : X' ≃ₗ[ℤ] LinearMap.ker g'),
    (∀ x, (e x).val = d x) → (∀ x, (e' x).val = d' x) →
    b.comp d = d'.comp a → ∀ x, (e' (a x)).val = b (e x).val

/-- Both Ext formulas, with their edges, on right modules over the opposite
ring. -/
def right_extType : Prop :=
  ∀ (R : Type u) [Ring R], ExtFirstOver.{u,v,w} Rᵐᵒᵖ ∧ ExtSecondOver.{u,v,w} Rᵐᵒᵖ

/-- The canonical connecting maps are also linear for the natural coefficient
scalar actions when R is commutative, hence so are the shift isomorphisms. -/
def scalar_compatibilityType : Prop :=
  ExtExactSequences.connectors_linearType.{u,v,w} ∧
  ExtExactSequences.connectors_linearType.{u,v,max u w} ∧
  TorExactSequences.first_connecting_linearType.{u,v,w} ∧
  TorExactSequences.second_connecting_linearType.{u,v,w} ∧
  ext_zero_linearType.{u,v,w} ∧ ext_zero_linearType.{u,v,max u w} ∧
  tor_zero_linearType.{u,v,w}

open P103.Specs.Ch11.ExtExactSequences

/-- Naturality of the displayed inverse Ext shift, for every compatible diagram. -/
def ext_first_shift_naturalType : Prop :=
  ∀ (R : Type u) [Ring R],
  ∀ (n : ℕ)
    (E : ExtMaps.{u,v,w} R n) (F : ExtMaps.{u,v,w} R (n + 1))
    (A₁ A₂ A₃ A₁' A₂' A₃' : ModuleCat.{v} R)
    (i : A₁ ⟶ A₂) (p : A₂ ⟶ A₃) (i' : A₁' ⟶ A₂') (p' : A₂' ⟶ A₃')
    (a : A₁' ⟶ A₁) (b : A₂' ⟶ A₂) (c : A₃' ⟶ A₃),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    Function.Injective i'.hom → Function.Exact i'.hom p'.hom → Function.Surjective p'.hom →
    i' ≫ b = a ≫ i → p' ≫ c = b ≫ p →
    ∀ (L : LeftResolution R A₁) (N : LeftResolution R A₃)
      (L' : LeftResolution R A₁') (N' : LeftResolution R A₃')
      (hL : L.IsProjective) (hN : N.IsProjective)
      (hL' : L'.IsProjective) (hN' : N'.IsProjective)
      (H : Horseshoe.ProjectiveData i.hom p.hom L N)
      (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N')
      (B B' : ModuleCat.{w} R) (g : B ⟶ B')
      (e : ExtWith N B (n+1) ≃ₗ[ℤ] ExtWith L B n)
      (e' : ExtWith N' B' (n+1) ≃ₗ[ℤ] ExtWith L' B' n),
    FirstConnecting H B n e.symm.toLinearMap →
    FirstConnecting H' B' n e'.symm.toLinearMap →
      (E.map ⟨L, hL⟩ ⟨L', hL'⟩ a g).comp e.toLinearMap =
        e'.toLinearMap.comp (F.map ⟨N, hN⟩ ⟨N', hN'⟩ c g)

/-- Naturality of the displayed inverse Ext shift, for every compatible diagram. -/
def ext_second_shift_naturalType : Prop :=
  ∀ (R : Type u) [Ring R],
  ∀ (n : ℕ)
    (E : ExtMaps.{u,v,w} R n) (F : ExtMaps.{u,v,w} R (n + 1))
    (A A' : ModuleCat.{v} R) (P : LeftResolution R A) (Q : LeftResolution R A')
    (hP : P.IsProjective) (hQ : Q.IsProjective) (f : A' ⟶ A)
    (B₁ B₂ B₃ B₁' B₂' B₃' : ModuleCat.{w} R)
    (i : B₁ ⟶ B₂) (p : B₂ ⟶ B₃) (i' : B₁' ⟶ B₂') (p' : B₂' ⟶ B₃')
    (a : B₁ ⟶ B₁') (b : B₂ ⟶ B₂') (c : B₃ ⟶ B₃'),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    Function.Injective i'.hom → Function.Exact i'.hom p'.hom → Function.Surjective p'.hom →
    i ≫ b = a ≫ i' → p ≫ c = b ≫ p' →
    ∀ (e : ExtWith P B₁ (n+1) ≃ₗ[ℤ] ExtWith P B₃ n)
      (e' : ExtWith Q B₁' (n+1) ≃ₗ[ℤ] ExtWith Q B₃' n),
    SecondConnecting P i p n e.symm.toLinearMap →
    SecondConnecting Q i' p' n e'.symm.toLinearMap →
      (E.map ⟨P, hP⟩ ⟨Q, hQ⟩ f c).comp e.toLinearMap =
        e'.toLinearMap.comp (F.map ⟨P, hP⟩ ⟨Q, hQ⟩ f a)

/-- Naturality on all cokernel representatives; quotient surjectivity covers every class. -/
def ext_first_edge_naturalType : Prop :=
  ∀ (R : Type u) [Ring R],
  ∀ (E : ExtMaps.{u,v,w} R 0) (F : ExtMaps.{u,v,w} R 1)
    (A₁ A₂ A₃ A₁' A₂' A₃' : ModuleCat.{v} R)
    (i : A₁ ⟶ A₂) (p : A₂ ⟶ A₃) (i' : A₁' ⟶ A₂') (p' : A₂' ⟶ A₃')
    (a : A₁' ⟶ A₁) (b : A₂' ⟶ A₂) (c : A₃' ⟶ A₃),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    Function.Injective i'.hom → Function.Exact i'.hom p'.hom → Function.Surjective p'.hom →
    i' ≫ b = a ≫ i → p' ≫ c = b ≫ p →
    ∀ (L : LeftResolution R A₁) (N : LeftResolution R A₃)
      (L' : LeftResolution R A₁') (N' : LeftResolution R A₃')
      (hL : L.IsProjective) (hN : N.IsProjective)
      (hL' : L'.IsProjective) (hN' : N'.IsProjective)
      (H : Horseshoe.ProjectiveData i.hom p.hom L N)
      (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N')
      (B B' : ModuleCat.{w} R) (g : B ⟶ B')
      (δ : ExtWith L B 0 →ₗ[ℤ] ExtWith N B 1)
      (ε : ExtWith L' B' 0 →ₗ[ℤ] ExtWith N' B' 1)
      (e : ExtWith N B 1 ≃ₗ[ℤ] Coker (P103.HomTensorExactness.pre (Q := B) i.hom).toIntLinearMap)
      (e' : ExtWith N' B' 1 ≃ₗ[ℤ] Coker (P103.HomTensorExactness.pre (Q := B') i'.hom).toIntLinearMap),
    FirstConnecting H B 0 δ → FirstConnecting H' B' 0 ε →
    (∀ h, e.symm (Submodule.Quotient.mk h) = δ (homClass L B h)) →
    (∀ h, e'.symm (Submodule.Quotient.mk h) = ε (homClass L' B' h)) →
    ∀ h : A₁ →ₗ[R] B,
      F.map ⟨N, hN⟩ ⟨N', hN'⟩ c g (e.symm (Submodule.Quotient.mk h)) =
        e'.symm (Submodule.Quotient.mk (g.hom.comp (h.comp a.hom)))

/-- Naturality on all cokernel representatives; quotient surjectivity covers every class. -/
def ext_second_edge_naturalType : Prop :=
  ∀ (R : Type u) [Ring R],
  ∀ (E : ExtMaps.{u,v,w} R 0) (F : ExtMaps.{u,v,w} R 1)
    (A A' : ModuleCat.{v} R) (P : LeftResolution R A) (Q : LeftResolution R A')
    (hP : P.IsProjective) (hQ : Q.IsProjective) (f : A' ⟶ A)
    (B₁ B₂ B₃ B₁' B₂' B₃' : ModuleCat.{w} R)
    (i : B₁ ⟶ B₂) (p : B₂ ⟶ B₃) (i' : B₁' ⟶ B₂') (p' : B₂' ⟶ B₃')
    (a : B₁ ⟶ B₁') (b : B₂ ⟶ B₂') (c : B₃ ⟶ B₃'),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    Function.Injective i'.hom → Function.Exact i'.hom p'.hom → Function.Surjective p'.hom →
    i ≫ b = a ≫ i' → p ≫ c = b ≫ p' →
    ∀ (δ : ExtWith P B₃ 0 →ₗ[ℤ] ExtWith P B₁ 1)
      (ε : ExtWith Q B₃' 0 →ₗ[ℤ] ExtWith Q B₁' 1)
      (e : ExtWith P B₁ 1 ≃ₗ[ℤ] Coker (P103.HomTensorExactness.post (P := A) p.hom).toIntLinearMap)
      (e' : ExtWith Q B₁' 1 ≃ₗ[ℤ] Coker (P103.HomTensorExactness.post (P := A') p'.hom).toIntLinearMap),
    SecondConnecting P i p 0 δ → SecondConnecting Q i' p' 0 ε →
    (∀ h, e.symm (Submodule.Quotient.mk h) = δ (homClass P B₃ h)) →
    (∀ h, e'.symm (Submodule.Quotient.mk h) = ε (homClass Q B₃' h)) →
    ∀ h : A →ₗ[R] B₃,
      F.map ⟨P, hP⟩ ⟨Q, hQ⟩ f a (e.symm (Submodule.Quotient.mk h)) =
        e'.symm (Submodule.Quotient.mk (c.hom.comp (h.comp f.hom)))

/-- Naturality of the actual degree-one tensor kernel identification. -/
def tor_first_edge_naturalType : Prop :=
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
      (B B' : ModuleCat.{w} R) (g : B ⟶ B')
      (T1 : TorMaps.{u,v,w} R 1) (T0 : TorMaps.{u,v,w} R 0)
      (δ : TorWith N.val B 1 →ₗ[ℤ] TorWith L.val B 0)
      (ε : TorWith N'.val B' 1 →ₗ[ℤ] TorWith L'.val B' 0)
      (z : TorWith L.val B 0 ≃+ P103.BalancedTensor.Tensor R A B)
      (z' : TorWith L'.val B' 0 ≃+ P103.BalancedTensor.Tensor R A' B')
      (e : TorWith N.val B 1 ≃ₗ[ℤ] LinearMap.ker (tensorMap i.hom (LinearMap.id : B →ₗ[R] B)))
      (e' : TorWith N'.val B' 1 ≃ₗ[ℤ] LinearMap.ker (tensorMap i'.hom (LinearMap.id : B' →ₗ[R] B'))),
    Connecting (tensorFirstMap H.inclusion B) (tensorFirstMap H.projection B) 1 0 δ →
    Connecting (tensorFirstMap H'.inclusion B') (tensorFirstMap H'.projection B') 1 0 ε →
    (∀ a, z (homologyClass _ 0 a) = tensorMap L.val.ε LinearMap.id a.val) →
    (∀ a, z' (homologyClass _ 0 a) = tensorMap L'.val.ε LinearMap.id a.val) →
    (∀ x, (e x).val = z (δ x)) → (∀ x, (e' x).val = z' (ε x)) →
    ∀ x, (e' (T1.map N N' c g x)).val = tensorMap a.hom g.hom (e x).val

/-- Naturality of the actual degree-one tensor kernel identification. -/
def tor_second_edge_naturalType : Prop :=
  ∀ (R : Type u) [Ring R] (A A' : ModuleCat.{v} Rᵐᵒᵖ)
    (P : ProjectiveChoice Rᵐᵒᵖ A) (P' : ProjectiveChoice Rᵐᵒᵖ A') (a : A ⟶ A')
    (B M C B' M' C' : ModuleCat.{w} R)
    (i : B ⟶ M) (p : M ⟶ C) (i' : B' ⟶ M') (p' : M' ⟶ C')
    (b : B ⟶ B') (m : M ⟶ M') (c : C ⟶ C'),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    Function.Injective i'.hom → Function.Exact i'.hom p'.hom → Function.Surjective p'.hom →
    i ≫ m = b ≫ i' → p ≫ c = m ≫ p' →
    ∀ (T1 : TorMaps.{u,v,w} R 1) (T0 : TorMaps.{u,v,w} R 0)
      (δ : TorWith P.val C 1 →ₗ[ℤ] TorWith P.val B 0)
      (ε : TorWith P'.val C' 1 →ₗ[ℤ] TorWith P'.val B' 0)
      (z : TorWith P.val B 0 ≃+ P103.BalancedTensor.Tensor R A B)
      (z' : TorWith P'.val B' 0 ≃+ P103.BalancedTensor.Tensor R A' B')
      (e : TorWith P.val C 1 ≃ₗ[ℤ] LinearMap.ker (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) i.hom))
      (e' : TorWith P'.val C' 1 ≃ₗ[ℤ] LinearMap.ker (tensorMap (LinearMap.id : A' →ₗ[Rᵐᵒᵖ] A') i'.hom)),
    Connecting (tensorSecondMap P.val.complex i.hom) (tensorSecondMap P.val.complex p.hom) 1 0 δ →
    Connecting (tensorSecondMap P'.val.complex i'.hom) (tensorSecondMap P'.val.complex p'.hom) 1 0 ε →
    (∀ q, z (homologyClass _ 0 q) = tensorMap P.val.ε LinearMap.id q.val) →
    (∀ q, z' (homologyClass _ 0 q) = tensorMap P'.val.ε LinearMap.id q.val) →
    (∀ x, (e x).val = z (δ x)) → (∀ x, (e' x).val = z' (ε x)) →
    ∀ x, (e' (T1.map P P' a c x)).val = tensorMap a.hom b.hom (e x).val

end
end P103.Specs.Ch11.DimensionShifting
