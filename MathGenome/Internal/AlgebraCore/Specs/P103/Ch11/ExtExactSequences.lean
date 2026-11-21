import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtBalance
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.Horseshoe
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.HomologySequence

/-! Ext coefficient sequences, paper.tex 2715–2717, 2736–2759, 2767–2777.
All Hom groups and cohomology groups have their canonical integer action.
R is arbitrary, including zero rings; taking Rᵐᵒᵖ gives the same-side right
module version. Every resolution and every horseshoe below is ordinary.
The predicates `Connecting` fix the positive lift/differentiate sign.
-/
namespace P103.Specs.Ch11.ExtExactSequences
open CategoryTheory
open P103.Specs.Ch10 P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.HomologySequence
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.ExtBalance
noncomputable section
universe u v w
variable {R : Type u} [Ring R]

/-- The canonical degree-zero map sends h to [h ε], with no arbitrary
choice of a group isomorphism. -/
def homClass {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (B : Type w) [AddCommGroup B] [Module R B] :
    (A →ₗ[R] B) →ₗ[ℤ] ExtWith P B 0 :=
  (homologyClass _ 0).comp
    ((P103.HomTensorExactness.pre P.ε).toIntLinearMap.codRestrict _ (by
      intro h
      change ((homComplex P.complex B).d 0 ((ComplexShape.up ℕ).next 0)).hom _ = 0
      rw [CochainComplex.next]
      change (h.comp P.ε).comp (P.complex.d 1 0).hom = 0
      ext x
      have hx : (P.complex.d 1 0).hom x ∈ LinearMap.ker P.ε := by
        rw [← P.exact_zero]
        exact ⟨x, rfl⟩
      change h (P.ε ((P.complex.d 1 0).hom x)) = 0
      rw [hx, map_zero]))

section First
variable {A₁ A₂ A₃ : ModuleCat.{v} R} {i : A₁ ⟶ A₂} {p : A₂ ⟶ A₃}
  {L : LeftResolution R A₁} {N : LeftResolution R A₃}

/-- The first variable reverses the coefficient order. -/
def FirstConnecting (H : Horseshoe.ProjectiveData i.hom p.hom L N)
    (B : ModuleCat.{w} R) (n : ℕ)
    (δ : ExtWith L B n →ₗ[ℤ] ExtWith N B (n + 1)) : Prop :=
  Connecting (homPreMap H.projection B) (homPreMap H.inclusion B) n (n + 1) δ

def FirstExact (H : Horseshoe.ProjectiveData i.hom p.hom L N)
    (B : ModuleCat.{w} R) (n : ℕ)
    (δ : ExtWith L B n →ₗ[ℤ] ExtWith N B (n + 1)) : Prop :=
  SequenceExact (homPreMap H.projection B) (homPreMap H.inclusion B) n (n + 1) δ

/-- The literal initial Hom terms and the degree-raising connector. -/
def FirstBottom (B : ModuleCat.{w} R)
    (δ : ExtWith L B 0 →ₗ[ℤ] ExtWith N B 1) : Prop :=
  Function.Injective (P103.HomTensorExactness.pre (Q := B) p.hom) ∧
  Function.Exact (P103.HomTensorExactness.pre (Q := B) p.hom)
    (P103.HomTensorExactness.pre (Q := B) i.hom) ∧
  Function.Exact (P103.HomTensorExactness.pre (Q := B) i.hom)
    (δ.comp (homClass L B))
end First

/-- Outside projective resolutions are arbitrary and retained by the horseshoe.
Exactness in all nonnegative degrees includes the three terms on either side
of each connecting map. -/
def FirstSequenceOver (R : Type u) [Ring R] : Prop :=
  ∀ (A₁ A₂ A₃ : ModuleCat.{v} R)
    (i : A₁ ⟶ A₂) (p : A₂ ⟶ A₃),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    ∀ (B : ModuleCat.{w} R) (L : LeftResolution R A₁) (N : LeftResolution R A₃),
    L.IsProjective → N.IsProjective →
    Nonempty (Horseshoe.ProjectiveData i.hom p.hom L N) ∧
    ∀ H : Horseshoe.ProjectiveData i.hom p.hom L N,
    ∃ δ : ∀ n, ExtWith L B n →ₗ[ℤ] ExtWith N B (n + 1),
      (∀ n, FirstConnecting H B n (δ n) ∧ FirstExact H B n (δ n)) ∧
      FirstBottom (i := i) (p := p) B (δ 0)

def first_sequenceType : Prop :=
  ∀ (R : Type u) [Ring R], FirstSequenceOver.{u,v,w} R

section Second
variable {B₁ B₂ B₃ : ModuleCat.{w} R} {i : B₁ ⟶ B₂} {p : B₂ ⟶ B₃}
  {A : ModuleCat.{v} R}

def SecondConnecting (P : LeftResolution R A) (i : B₁ ⟶ B₂) (p : B₂ ⟶ B₃)
    (n : ℕ) (δ : ExtWith P B₃ n →ₗ[ℤ] ExtWith P B₁ (n + 1)) : Prop :=
  Connecting (homPostMap P.complex i.hom) (homPostMap P.complex p.hom) n (n + 1) δ

def SecondExact (P : LeftResolution R A) (i : B₁ ⟶ B₂) (p : B₂ ⟶ B₃)
    (n : ℕ) (δ : ExtWith P B₃ n →ₗ[ℤ] ExtWith P B₁ (n + 1)) : Prop :=
  SequenceExact (homPostMap P.complex i.hom) (homPostMap P.complex p.hom) n (n + 1) δ

def SecondBottom (P : LeftResolution R A) (i : B₁ ⟶ B₂) (p : B₂ ⟶ B₃)
    (δ : ExtWith P B₃ 0 →ₗ[ℤ] ExtWith P B₁ 1) : Prop :=
  Function.Injective (P103.HomTensorExactness.post (P := A) i.hom) ∧
  Function.Exact (P103.HomTensorExactness.post (P := A) i.hom)
    (P103.HomTensorExactness.post (P := A) p.hom) ∧
  Function.Exact (P103.HomTensorExactness.post (P := A) p.hom)
    (δ.comp (homClass P B₃))
end Second

def SecondSequenceOver (R : Type u) [Ring R] : Prop :=
  ∀ (A : ModuleCat.{v} R) (P : LeftResolution R A),
    P.IsProjective → ∀ (B₁ B₂ B₃ : ModuleCat.{w} R) (i : B₁ ⟶ B₂) (p : B₂ ⟶ B₃),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    ∃ δ : ∀ n, ExtWith P B₃ n →ₗ[ℤ] ExtWith P B₁ (n + 1),
      (∀ n, SecondConnecting P i p n (δ n) ∧ SecondExact P i p n (δ n)) ∧
      SecondBottom P i p (δ 0)

def second_sequenceType : Prop :=
  ∀ (R : Type u) [Ring R], SecondSequenceOver.{u,v,w} R

/-- Simultaneous naturality in the short exact first coefficient and in the
fixed second coefficient. Identity coefficient diagrams give independence of
every horseshoe and outside resolution under the canonical Ext comparisons.
`ExtMaps.formula` makes the maps independent of all chosen lifts. -/
def FirstNaturalityOver (R : Type u) [Ring R] : Prop :=
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
      (δ : ExtWith L B n →ₗ[ℤ] ExtWith N B (n + 1))
      (ε : ExtWith L' B' n →ₗ[ℤ] ExtWith N' B' (n + 1)),
    FirstConnecting H B n δ → FirstConnecting H' B' n ε →
      (F.map ⟨N, hN⟩ ⟨N', hN'⟩ c g).comp δ =
        ε.comp (E.map ⟨L, hL⟩ ⟨L', hL'⟩ a g)

def first_naturalType : Prop :=
  ∀ (R : Type u) [Ring R], FirstNaturalityOver.{u,v,w} R

/-- Simultaneous naturality for a commuting coefficient diagram and a map in
the fixed first variable, allowing arbitrary projective resolution choices.
Identity diagrams in particular give the canonical resolution transport. -/
def SecondNaturalityOver (R : Type u) [Ring R] : Prop :=
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
    ∀ (δ : ExtWith P B₃ n →ₗ[ℤ] ExtWith P B₁ (n + 1))
      (ε : ExtWith Q B₃' n →ₗ[ℤ] ExtWith Q B₁' (n + 1)),
    SecondConnecting P i p n δ → SecondConnecting Q i' p' n ε →
      (F.map ⟨P, hP⟩ ⟨Q, hQ⟩ f a).comp δ =
        ε.comp (E.map ⟨P, hP⟩ ⟨Q, hQ⟩ f c)

def second_naturalType : Prop :=
  ∀ (R : Type u) [Ring R], SecondNaturalityOver.{u,v,w} R

/-- The nonconnecting arrows in both sequences are the canonical two-variable
Ext arrows; their naturality and all comparison cocycle laws are consequently
the laws of `ExtMaps`, not additional choices of homology maps. -/
def CoefficientArrowsOver (R : Type u) [Ring R] : Prop :=
  ∀ (n : ℕ) (E : ExtMaps.{u,v,w} R n),
    (∀ (A₁ A₂ A₃ : ModuleCat.{v} R) (i : A₁ ⟶ A₂) (p : A₂ ⟶ A₃)
      (L : LeftResolution R A₁) (N : LeftResolution R A₃)
      (hL : L.IsProjective) (hN : N.IsProjective)
      (H : Horseshoe.ProjectiveData i.hom p.hom L N) (B : ModuleCat.{w} R),
      homologyMap (homPreMap H.projection B) n =
        E.map ⟨N, hN⟩ ⟨H.middle, H.projective⟩ p (𝟙 B) ∧
      homologyMap (homPreMap H.inclusion B) n =
        E.map ⟨H.middle, H.projective⟩ ⟨L, hL⟩ i (𝟙 B)) ∧
    (∀ (A : ModuleCat.{v} R) (P : LeftResolution R A) (hP : P.IsProjective)
      (B B' : ModuleCat.{w} R) (g : B ⟶ B'),
      homologyMap (homPostMap P.complex g.hom) n = E.map ⟨P, hP⟩ ⟨P, hP⟩ (𝟙 A) g)

def coefficient_arrowsType : Prop :=
  ∀ (R : Type u) [Ring R], CoefficientArrowsOver.{u,v,w} R

/-- The injective-horseshoe computation of the second-variable sequence.
No exactness of Hom(A,-) on arbitrary short exact sequences is assumed:
the sequence of resolutions is split in every degree. -/
def InjectiveSequenceOver (R : Type u) [Ring R] : Prop :=
  ∀ (A : ModuleCat.{v} R)
    (B₁ B₂ B₃ : ModuleCat.{w} R) (i : B₁ ⟶ B₂) (p : B₂ ⟶ B₃),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    ∀ (L : InjectiveResolution R B₁) (N : InjectiveResolution R B₃),
    Nonempty (Horseshoe.InjectiveData i.hom p.hom L N) ∧
    ∀ H : Horseshoe.InjectiveData i.hom p.hom L N,
    ∃ δ : ∀ n, Homology (injectiveHom A N.complex) n →ₗ[ℤ]
      Homology (injectiveHom A L.complex) (n + 1),
      (∀ n, Connecting (injectiveHomMap (LinearMap.id : A →ₗ[R] A) H.inclusion)
        (injectiveHomMap (LinearMap.id : A →ₗ[R] A) H.projection) n (n + 1) (δ n) ∧
      SequenceExact (injectiveHomMap (LinearMap.id : A →ₗ[R] A) H.inclusion)
        (injectiveHomMap (LinearMap.id : A →ₗ[R] A) H.projection) n (n + 1) (δ n)) ∧
      Function.Injective
        (homologyMap (injectiveHomMap (LinearMap.id : A →ₗ[R] A) H.inclusion) 0)

def injective_sequenceType : Prop :=
  ∀ (R : Type u) [Ring R], InjectiveSequenceOver.{u,v,w} R

/-- The comparison is prescribed by the actual augmentation maps. Its
quasi-isomorphism hypotheses are precisely those established by Ext balance.
This predicate defines which comparison is meant, not a new assumed theorem. -/
def BalancedComparison {A : ModuleCat.{v} R} {B : ModuleCat.{w} R}
    (P : LeftResolution R A) (I : InjectiveResolution R B) (n : ℕ)
    (e : Homology (injectiveHom A I.complex) n ≃ₗ[ℤ] ExtWith P B n) : Prop :=
  ∃ (α : homComplex P.complex B ⟶ homTotal P.complex I.complex)
    (β : injectiveHom A I.complex ⟶ homTotal P.complex I.complex),
    IsProjectiveAugmentation P I α ∧ IsInjectiveAugmentation P I β ∧
    QuasiIsomorphism α ∧ QuasiIsomorphism β ∧
    (homologyMap α n).comp e.toLinearMap = homologyMap β n

/-- The canonical comparisons used below exist simultaneously in every degree
for every projective and injective resolution. -/
def BalancedComparisonsOver (R : Type u) [Ring R] : Prop :=
  ∀ (A : ModuleCat.{v} R) (B : ModuleCat.{w} R)
    (P : LeftResolution R A) (I : InjectiveResolution R B), P.IsProjective →
    ∃ e : ∀ n, Homology (injectiveHom A I.complex) n ≃ₗ[ℤ] ExtWith P B n,
      ∀ n, BalancedComparison P I n (e n)

def balanced_comparisonsType : Prop :=
  ∀ (R : Type u) [Ring R], BalancedComparisonsOver.{u,v,w} R

/-- Balance identifies every ordinary coefficient arrow, including the two
nonconnecting arrows in the injective horseshoe sequence, with the canonical
Ext arrow. Identity coefficient maps include all resolution comparisons. -/
def BalanceArrowsOver (R : Type u) [Ring R] : Prop :=
  ∀ (n : ℕ) (E : ExtMaps.{u,v,w} R n)
    (A A' : ModuleCat.{v} R) (B B' : ModuleCat.{w} R)
    (P : LeftResolution R A) (Q : LeftResolution R A')
    (hP : P.IsProjective) (hQ : Q.IsProjective)
    (I : InjectiveResolution R B) (J : InjectiveResolution R B')
    (f : A' ⟶ A) (g : B ⟶ B') (m : I.complex ⟶ J.complex),
    CochainLift (ofInjective I) J g.hom m →
    ∀ (e : Homology (injectiveHom A I.complex) n ≃ₗ[ℤ] ExtWith P B n)
      (e' : Homology (injectiveHom A' J.complex) n ≃ₗ[ℤ] ExtWith Q B' n),
    BalancedComparison P I n e → BalancedComparison Q J n e' →
      e'.toLinearMap.comp (homologyMap (injectiveHomMap f.hom m) n) =
        (E.map ⟨P, hP⟩ ⟨Q, hQ⟩ f g).comp e.toLinearMap

def balance_arrowsType : Prop :=
  ∀ (R : Type u) [Ring R], BalanceArrowsOver.{u,v,w} R

/-- The positive connecting maps computed by a fixed projective resolution
agree with those from every injective horseshoe under the canonical balance
comparisons. These are comparisons of connectors, not only of group objects. -/
def BalanceConnectingOver (R : Type u) [Ring R] : Prop :=
  ∀ (A : ModuleCat.{v} R) (P : LeftResolution R A),
    P.IsProjective → ∀ (B₁ B₂ B₃ : ModuleCat.{w} R)
      (i : B₁ ⟶ B₂) (p : B₂ ⟶ B₃),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    ∀ (L : InjectiveResolution R B₁) (N : InjectiveResolution R B₃)
      (H : Horseshoe.InjectiveData i.hom p.hom L N) (n : ℕ)
      (δ : ExtWith P B₃ n →ₗ[ℤ] ExtWith P B₁ (n + 1))
      (ε : Homology (injectiveHom A N.complex) n →ₗ[ℤ]
        Homology (injectiveHom A L.complex) (n + 1)),
    SecondConnecting P i p n δ →
    Connecting (injectiveHomMap (LinearMap.id : A →ₗ[R] A) H.inclusion)
      (injectiveHomMap (LinearMap.id : A →ₗ[R] A) H.projection) n (n + 1) ε →
    ∀ (eN : Homology (injectiveHom A N.complex) n ≃ₗ[ℤ] ExtWith P B₃ n)
      (eL : Homology (injectiveHom A L.complex) (n + 1) ≃ₗ[ℤ] ExtWith P B₁ (n + 1)),
    BalancedComparison P N n eN → BalancedComparison P L (n + 1) eL →
      eL.toLinearMap.comp ε = δ.comp eN.toLinearMap

def balance_connectingType : Prop :=
  ∀ (R : Type u) [Ring R], BalanceConnectingOver.{u,v,w} R

/-- Over a commutative ring the connecting arrows are linear for the scalar
actions supplied by the canonical coefficient functors. The other arrows
are already linear by the upstream two-variable Ext interface. -/
def connectors_linearType : Prop :=
  ∀ (K : Type u) [CommRing K] (n : ℕ)
    (E : ExtMaps.{u,v,w} K n) (F : ExtMaps.{u,v,w} K (n + 1)),
    (∀ (A₁ A₂ A₃ : ModuleCat.{v} K) (i : A₁ ⟶ A₂) (p : A₂ ⟶ A₃),
      Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
      ∀ (L : LeftResolution K A₁) (N : LeftResolution K A₃)
        (hL : L.IsProjective) (hN : N.IsProjective)
        (H : Horseshoe.ProjectiveData i.hom p.hom L N) (B : ModuleCat.{w} K)
        (δ : ExtWith L B n →ₗ[ℤ] ExtWith N B (n + 1)),
      FirstConnecting H B n δ →
      letI := extModule E ⟨L, hL⟩ B
      letI := extModule F ⟨N, hN⟩ B
      ∀ (r : K) x, δ (r • x) = r • δ x) ∧
    (∀ (A : ModuleCat.{v} K) (P : LeftResolution K A) (hP : P.IsProjective)
      (B₁ B₂ B₃ : ModuleCat.{w} K) (i : B₁ ⟶ B₂) (p : B₂ ⟶ B₃),
      Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
      ∀ (δ : ExtWith P B₃ n →ₗ[ℤ] ExtWith P B₁ (n + 1)),
      SecondConnecting P i p n δ →
      letI := extModule E ⟨P, hP⟩ B₃
      letI := extModule F ⟨P, hP⟩ B₁
      ∀ (r : K) x, δ (r • x) = r • δ x)

/-- Explicit same-side right-module specialization, including exactness,
naturality, canonical arrows, and agreement of the two second-variable models. -/
def right_sequencesType : Prop :=
  ∀ (R : Type u) [Ring R],
    FirstSequenceOver.{u,v,w} Rᵐᵒᵖ ∧ SecondSequenceOver.{u,v,w} Rᵐᵒᵖ ∧
    FirstNaturalityOver.{u,v,w} Rᵐᵒᵖ ∧ SecondNaturalityOver.{u,v,w} Rᵐᵒᵖ ∧
    CoefficientArrowsOver.{u,v,w} Rᵐᵒᵖ ∧ InjectiveSequenceOver.{u,v,w} Rᵐᵒᵖ ∧
    BalancedComparisonsOver.{u,v,w} Rᵐᵒᵖ ∧ BalanceArrowsOver.{u,v,w} Rᵐᵒᵖ ∧
    BalanceConnectingOver.{u,v,w} Rᵐᵒᵖ

end
end P103.Specs.Ch11.ExtExactSequences
