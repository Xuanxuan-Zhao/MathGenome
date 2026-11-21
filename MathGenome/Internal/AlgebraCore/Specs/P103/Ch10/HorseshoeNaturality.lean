import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.Horseshoe
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.Comparison
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
Horseshoe naturality, paper.tex 2528–2530 and 2554–2573.
The splitting below is only degreewise: its sections need not be complex maps.
All rings, including the zero ring and opposite rings, are allowed.
The generic functor statements allow covariant and, after `op`, contravariant
functors. Abelian group targets are covered by the canonical integer module
functor in the comparison interface.
-/
namespace P103.Specs.Ch10.HorseshoeNaturality
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.HomologySequence
universe u v w x y z t q

/-- A split short exact sequence in each degree of the nonaugmented complexes.
The witnesses impose no compatibility of the splittings with differentials. -/
def DegreewiseSplit {D : Type u} [Category.{v} D] [Preadditive D]
    {ι : Type w} {c : ComplexShape ι} {A B C : HomologicalComplex D c}
    (i : A ⟶ B) (p : B ⟶ C) : Prop :=
  ∀ n, ∃ h : i.f n ≫ p.f n = 0,
    Nonempty (ShortComplex.mk (i.f n) (p.f n) h).Splitting

def split_mapType : Prop :=
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {E : Type x} [Category.{y} E] [Preadditive E]
    {ι : Type w} {c : ComplexShape ι} {A B C : HomologicalComplex D c}
    (F : D ⥤ E) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p → DegreewiseSplit
      ((F.mapHomologicalComplex c).map i) ((F.mapHomologicalComplex c).map p)

def split_opType : Prop :=
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {ι : Type w} {c : ComplexShape ι} {A B C : HomologicalComplex D c}
    (i : A ⟶ B) (p : B ⟶ C), DegreewiseSplit i p →
    DegreewiseSplit ((HomologicalComplex.opFunctor D c).map p.op)
      ((HomologicalComplex.opFunctor D c).map i.op)

def split_exactType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex (ModuleCat.{v} R) c}
    (i : A ⟶ B) (p : B ⟶ C), DegreewiseSplit i p → DegreewiseExact i p

def projective_splitType : Prop :=
  ∀ (R : Type u) [Ring R] (A B C : Type v)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
    (H : Horseshoe.ProjectiveData i p L N), DegreewiseSplit H.inclusion H.projection

def injective_splitType : Prop :=
  ∀ (R : Type u) [Ring R] (A B C : Type v)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
    (H : Horseshoe.InjectiveData i p L N), DegreewiseSplit H.inclusion H.projection

/-- The whole exact homology sequence after any additive functor, without an
exactness assumption on that functor. Generic shapes include both chain and
cochain complexes, as well as their opposites. -/
def applied_sequenceType : Prop :=
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {R : Type x} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex D c}
    (F : D ⥤ ModuleCat.{y} R) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p → ∀ n m, c.Rel n m →
    ∃! δ : Homology ((F.mapHomologicalComplex c).obj C) n →ₗ[R]
        Homology ((F.mapHomologicalComplex c).obj A) m,
      Connecting ((F.mapHomologicalComplex c).map i)
        ((F.mapHomologicalComplex c).map p) n m δ ∧
      SequenceExact ((F.mapHomologicalComplex c).map i)
        ((F.mapHomologicalComplex c).map p) n m δ

/-- Naturality of the connecting map for every compatible diagram, not only a
specified choice of comparison maps. The outside maps determine this square. -/
def applied_naturalityType : Prop :=
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {R : Type x} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C A' B' C' : HomologicalComplex D c}
    (F : D ⥤ ModuleCat.{y} R) [F.Additive]
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (α : A ⟶ A') (β : B ⟶ B') (γ : C ⟶ C'),
    i ≫ β = α ≫ i' → p ≫ γ = β ≫ p' →
    DegreewiseSplit i p → DegreewiseSplit i' p' →
    ∀ n m, c.Rel n m →
    ∀ (δ : Homology ((F.mapHomologicalComplex c).obj C) n →ₗ[R]
        Homology ((F.mapHomologicalComplex c).obj A) m)
      (ε : Homology ((F.mapHomologicalComplex c).obj C') n →ₗ[R]
        Homology ((F.mapHomologicalComplex c).obj A') m),
      Connecting ((F.mapHomologicalComplex c).map i)
        ((F.mapHomologicalComplex c).map p) n m δ →
      Connecting ((F.mapHomologicalComplex c).map i')
        ((F.mapHomologicalComplex c).map p') n m ε →
      (homologyMap ((F.mapHomologicalComplex c).map α) m).comp δ =
        ε.comp (homologyMap ((F.mapHomologicalComplex c).map γ) n)

/-- Reversing arrows exchanges the ends of a split sequence and reverses the
complex shape. This is the actual contravariant functor specialization. -/
def contravariant_sequenceType : Prop :=
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {R : Type x} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex D c}
    (F : Dᵒᵖ ⥤ ModuleCat.{y} R) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p → ∀ n m, c.symm.Rel n m →
    ∃! δ : Homology ((F.mapHomologicalComplex c.symm).obj A.op) n →ₗ[R]
        Homology ((F.mapHomologicalComplex c.symm).obj C.op) m,
      Connecting
        ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map p.op))
        ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map i.op)) n m δ ∧
      SequenceExact
        ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map p.op))
        ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map i.op)) n m δ

section Coherence
variable {D : Type u} [Category.{v} D] [Preadditive D]
  {E : Type x} [Category.{y} E] [Preadditive E]
  {R : Type z} [Ring R] {ι : Type w} {c : ComplexShape ι}
  (I : D → Type t) (K : ∀ A, I A → HomologicalComplex E c)
  (L : ∀ {A B} (P : I A) (Q : I B), (A ⟶ B) → (K A P ⟶ K B Q) → Prop)
  (F : E ⥤ ModuleCat.{q} R) [F.Additive]

/-- Express the connecting square using the lift-independent coefficient maps
of the comparison theorem. Its comparison isomorphisms therefore give transport
between arbitrary horseshoes and outside resolutions. Existence of these
coherent comparisons is supplied by the upstream comparison theorem. -/
def CoherentConnecting : Prop :=
  ∀ (n m : ι) (_hnm : c.Rel n m)
    (Cn : Comparison.CoherentComparison I K L
      (F.mapHomologicalComplex c ⋙ Comparison.quotientHomology c n))
    (Cm : Comparison.CoherentComparison I K L
      (F.mapHomologicalComplex c ⋙ Comparison.quotientHomology c m))
    {A B C A' B' C' : D}
    (PA : I A) (PB : I B) (PC : I C) (QA : I A') (QB : I B') (QC : I C')
    (i : K A PA ⟶ K B PB) (p : K B PB ⟶ K C PC)
    (i' : K A' QA ⟶ K B' QB) (p' : K B' QB ⟶ K C' QC)
    (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
    (α : K A PA ⟶ K A' QA) (β : K B PB ⟶ K B' QB) (γ : K C PC ⟶ K C' QC),
    L PA QA a α → L PB QB b β → L PC QC cc γ →
    i ≫ β = α ≫ i' → p ≫ γ = β ≫ p' →
    DegreewiseSplit i p → DegreewiseSplit i' p' →
    ∀ (δ : Homology ((F.mapHomologicalComplex c).obj (K C PC)) n →ₗ[R]
        Homology ((F.mapHomologicalComplex c).obj (K A PA)) m)
      (ε : Homology ((F.mapHomologicalComplex c).obj (K C' QC)) n →ₗ[R]
        Homology ((F.mapHomologicalComplex c).obj (K A' QA)) m),
      Connecting ((F.mapHomologicalComplex c).map i)
        ((F.mapHomologicalComplex c).map p) n m δ →
      Connecting ((F.mapHomologicalComplex c).map i')
        ((F.mapHomologicalComplex c).map p') n m ε →
      (Cm.map PA QA a).hom.comp δ = ε.comp (Cn.map PC QC cc).hom

/-- For identity coefficient maps, the square is transport by the canonical
comparison isomorphisms. The horseshoes, resolutions and compatible lifts may
all differ. -/
def CoherentTransport : Prop :=
  ∀ (n m : ι) (_hnm : c.Rel n m)
    (Cn : Comparison.CoherentComparison I K L
      (F.mapHomologicalComplex c ⋙ Comparison.quotientHomology c n))
    (Cm : Comparison.CoherentComparison I K L
      (F.mapHomologicalComplex c ⋙ Comparison.quotientHomology c m))
    {A B C : D} (PA QA : I A) (PB QB : I B) (PC QC : I C)
    (i : K A PA ⟶ K B PB) (p : K B PB ⟶ K C PC)
    (i' : K A QA ⟶ K B QB) (p' : K B QB ⟶ K C QC)
    (α : K A PA ⟶ K A QA) (β : K B PB ⟶ K B QB) (γ : K C PC ⟶ K C QC),
    L PA QA (𝟙 A) α → L PB QB (𝟙 B) β → L PC QC (𝟙 C) γ →
    i ≫ β = α ≫ i' → p ≫ γ = β ≫ p' →
    DegreewiseSplit i p → DegreewiseSplit i' p' →
    ∀ (δ : Homology ((F.mapHomologicalComplex c).obj (K C PC)) n →ₗ[R]
        Homology ((F.mapHomologicalComplex c).obj (K A PA)) m)
      (ε : Homology ((F.mapHomologicalComplex c).obj (K C QC)) n →ₗ[R]
        Homology ((F.mapHomologicalComplex c).obj (K A QA)) m),
      Connecting ((F.mapHomologicalComplex c).map i)
        ((F.mapHomologicalComplex c).map p) n m δ →
      Connecting ((F.mapHomologicalComplex c).map i')
        ((F.mapHomologicalComplex c).map p') n m ε →
      (Cm.comparison PA QA).hom.hom.comp δ = ε.comp (Cn.comparison PC QC).hom.hom

end Coherence

/-- Closed expected propositions include every parameter of the generic
comparison interfaces. -/
def coherent_connectingType : Prop :=
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {E : Type x} [Category.{y} E] [Preadditive E]
    {R : Type z} [Ring R] {ι : Type w} {c : ComplexShape ι}
    (I : D → Type t) (K : ∀ A, I A → HomologicalComplex E c)
    (L : ∀ {A B} (P : I A) (Q : I B), (A ⟶ B) → (K A P ⟶ K B Q) → Prop)
    (F : E ⥤ ModuleCat.{q} R) [F.Additive], CoherentConnecting I K L F

def coherent_transportType : Prop :=
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {E : Type x} [Category.{y} E] [Preadditive E]
    {R : Type z} [Ring R] {ι : Type w} {c : ComplexShape ι}
    (I : D → Type t) (K : ∀ A, I A → HomologicalComplex E c)
    (L : ∀ {A B} (P : I A) (Q : I B), (A ⟶ B) → (K A P ⟶ K B Q) → Prop)
    (F : E ⥤ ModuleCat.{q} R) [F.Additive], CoherentTransport I K L F

/-- Projective diagram construction. Both horseshoes and all four
outside resolutions are prescribed. No compatible maps are assumed. -/
def projective_diagramType : Prop :=
  ∀ (R : Type u) [Ring R] (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C'),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    Function.Injective i'.hom → Function.Exact i'.hom p'.hom → Function.Surjective p'.hom →
    i ≫ b = a ≫ i' → p ≫ c = b ≫ p' →
    ∀ (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
      (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C'),
    L.IsProjective → N.IsProjective → L'.IsProjective → N'.IsProjective →
    ∀ (H : Horseshoe.ProjectiveData i.hom p.hom L N)
      (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N'),
    ∃ (α : L.complex ⟶ L'.complex) (β : H.middle.complex ⟶ H'.middle.complex)
      (γ : N.complex ⟶ N'.complex),
      Comparison.ChainLift L L' a.hom α ∧ Comparison.ChainLift H.middle H'.middle b.hom β ∧
      Comparison.ChainLift N N' c.hom γ ∧
      H.inclusion ≫ β = α ≫ H'.inclusion ∧ H.projection ≫ γ = β ≫ H'.projection

/-- Dual diagram construction; all terms of the injective resolutions are
injective by their upstream definition. -/
def injective_diagramType : Prop :=
  ∀ (R : Type u) [Ring R] (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C'),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    Function.Injective i'.hom → Function.Exact i'.hom p'.hom → Function.Surjective p'.hom →
    i ≫ b = a ≫ i' → p ≫ c = b ≫ p' →
    ∀ (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
      (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
      (H : Horseshoe.InjectiveData i.hom p.hom L N)
      (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N'),
    ∃ (α : L.complex ⟶ L'.complex) (β : H.middle.complex ⟶ H'.middle.complex)
      (γ : N.complex ⟶ N'.complex),
      Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α ∧
      Comparison.CochainLift (Comparison.ofInjective H.middle) H'.middle b.hom β ∧
      Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ ∧
      H.inclusion ≫ β = α ≫ H'.inclusion ∧ H.projection ≫ γ = β ≫ H'.projection

/-- Abelian-group-valued functors are represented by their canonical integer
module structures. This changes neither elements nor additive maps, and agrees
with the upstream `appliedAbHomology` comparison functor after forgetting scalars. -/
def abelian_sequenceType : Prop :=
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex D c}
    (F : D ⥤ AddCommGrpCat.{y}) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p → ∀ n m, c.Rel n m →
    ∃! δ : Homology (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).obj C) n →ₗ[ℤ]
        Homology (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).obj A) m,
      Connecting (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map i)
        (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map p) n m δ ∧
      SequenceExact (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map i)
        (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map p) n m δ

def abelian_naturalityType : Prop :=
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {ι : Type w} {c : ComplexShape ι}
    {A B C A' B' C' : HomologicalComplex D c}
    (F : D ⥤ AddCommGrpCat.{y}) [F.Additive]
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (α : A ⟶ A') (β : B ⟶ B') (γ : C ⟶ C'),
    i ≫ β = α ≫ i' → p ≫ γ = β ≫ p' →
    DegreewiseSplit i p → DegreewiseSplit i' p' →
    ∀ n m, c.Rel n m →
    ∀ (δ : Homology (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).obj C) n →ₗ[ℤ]
        Homology (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).obj A) m)
      (ε : Homology (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).obj C') n →ₗ[ℤ]
        Homology (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).obj A') m),
      Connecting (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map i)
        (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map p) n m δ →
      Connecting (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map i')
        (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map p') n m ε →
      (homologyMap (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map α) m).comp δ =
        ε.comp (homologyMap (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map γ) n)

def abelian_contravariant_sequenceType : Prop :=
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex D c}
    (F : Dᵒᵖ ⥤ AddCommGrpCat.{y}) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p → ∀ n m, c.symm.Rel n m →
    ∃! δ : Homology (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c.symm).obj A.op) n →ₗ[ℤ]
        Homology (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c.symm).obj C.op) m,
      Connecting
        (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map p.op))
        (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map i.op)) n m δ ∧
      SequenceExact
        (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map p.op))
        (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map i.op)) n m δ

def injective_lifts_independentType : Prop :=
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
    (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
    (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
    (H : Horseshoe.InjectiveData i.hom p.hom L N)
    (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N')
    (α₁ α₂ : L.complex ⟶ L'.complex)
    (β₁ β₂ : H.middle.complex ⟶ H'.middle.complex)
    (γ₁ γ₂ : N.complex ⟶ N'.complex) (n : ℕ),
    Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α₁ →
    Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α₂ →
    Comparison.CochainLift (Comparison.ofInjective H.middle) H'.middle b.hom β₁ →
    Comparison.CochainLift (Comparison.ofInjective H.middle) H'.middle b.hom β₂ →
    Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ₁ →
    Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ₂ →
    (Comparison.appliedHomology F (ComplexShape.up ℕ) n).map α₁ =
      (Comparison.appliedHomology F (ComplexShape.up ℕ) n).map α₂ ∧
    (Comparison.appliedHomology F (ComplexShape.up ℕ) n).map β₁ =
      (Comparison.appliedHomology F (ComplexShape.up ℕ) n).map β₂ ∧
    (Comparison.appliedHomology F (ComplexShape.up ℕ) n).map γ₁ =
      (Comparison.appliedHomology F (ComplexShape.up ℕ) n).map γ₂

def injective_contravariant_lifts_independentType : Prop :=
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
    (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
    (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
    (H : Horseshoe.InjectiveData i.hom p.hom L N)
    (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N')
    (α₁ α₂ : L.complex ⟶ L'.complex)
    (β₁ β₂ : H.middle.complex ⟶ H'.middle.complex)
    (γ₁ γ₂ : N.complex ⟶ N'.complex) (n : ℕ),
    Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α₁ →
    Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α₂ →
    Comparison.CochainLift (Comparison.ofInjective H.middle) H'.middle b.hom β₁ →
    Comparison.CochainLift (Comparison.ofInjective H.middle) H'.middle b.hom β₂ →
    Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ₁ →
    Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ₂ →
    (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map α₁ =
      (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map α₂ ∧
    (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map β₁ =
      (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map β₂ ∧
    (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map γ₁ =
      (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map γ₂

def injective_ab_lifts_independentType : Prop :=
  ∀ (R : Type u) [Ring R] 
    (F : ModuleCat.{max u v} R ⥤ AddCommGrpCat.{y}) [F.Additive]
    (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
    (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
    (H : Horseshoe.InjectiveData i.hom p.hom L N)
    (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N')
    (α₁ α₂ : L.complex ⟶ L'.complex)
    (β₁ β₂ : H.middle.complex ⟶ H'.middle.complex)
    (γ₁ γ₂ : N.complex ⟶ N'.complex) (n : ℕ),
    Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α₁ →
    Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α₂ →
    Comparison.CochainLift (Comparison.ofInjective H.middle) H'.middle b.hom β₁ →
    Comparison.CochainLift (Comparison.ofInjective H.middle) H'.middle b.hom β₂ →
    Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ₁ →
    Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ₂ →
    (Comparison.appliedAbHomology F (ComplexShape.up ℕ) n).map α₁ =
      (Comparison.appliedAbHomology F (ComplexShape.up ℕ) n).map α₂ ∧
    (Comparison.appliedAbHomology F (ComplexShape.up ℕ) n).map β₁ =
      (Comparison.appliedAbHomology F (ComplexShape.up ℕ) n).map β₂ ∧
    (Comparison.appliedAbHomology F (ComplexShape.up ℕ) n).map γ₁ =
      (Comparison.appliedAbHomology F (ComplexShape.up ℕ) n).map γ₂

def injective_ab_contravariant_lifts_independentType : Prop :=
  ∀ (R : Type u) [Ring R] 
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ AddCommGrpCat.{y}) [F.Additive]
    (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
    (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
    (H : Horseshoe.InjectiveData i.hom p.hom L N)
    (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N')
    (α₁ α₂ : L.complex ⟶ L'.complex)
    (β₁ β₂ : H.middle.complex ⟶ H'.middle.complex)
    (γ₁ γ₂ : N.complex ⟶ N'.complex) (n : ℕ),
    Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α₁ →
    Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α₂ →
    Comparison.CochainLift (Comparison.ofInjective H.middle) H'.middle b.hom β₁ →
    Comparison.CochainLift (Comparison.ofInjective H.middle) H'.middle b.hom β₂ →
    Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ₁ →
    Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ₂ →
    (Comparison.appliedAbContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map α₁ =
      (Comparison.appliedAbContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map α₂ ∧
    (Comparison.appliedAbContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map β₁ =
      (Comparison.appliedAbContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map β₂ ∧
    (Comparison.appliedAbContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map γ₁ =
      (Comparison.appliedAbContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map γ₂

def projective_lifts_independentType : Prop :=
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
    (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
    (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
    (hL : L.IsProjective) (hN : N.IsProjective)
    (H : Horseshoe.ProjectiveData i.hom p.hom L N)
    (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N')
    (α₁ α₂ : L.complex ⟶ L'.complex)
    (β₁ β₂ : H.middle.complex ⟶ H'.middle.complex)
    (γ₁ γ₂ : N.complex ⟶ N'.complex) (n : ℕ),
    Comparison.ChainLift L L' a.hom α₁ →
    Comparison.ChainLift L L' a.hom α₂ →
    Comparison.ChainLift H.middle H'.middle b.hom β₁ →
    Comparison.ChainLift H.middle H'.middle b.hom β₂ →
    Comparison.ChainLift N N' c.hom γ₁ →
    Comparison.ChainLift N N' c.hom γ₂ →
    (Comparison.appliedHomology F (ComplexShape.down ℕ) n).map α₁ =
      (Comparison.appliedHomology F (ComplexShape.down ℕ) n).map α₂ ∧
    (Comparison.appliedHomology F (ComplexShape.down ℕ) n).map β₁ =
      (Comparison.appliedHomology F (ComplexShape.down ℕ) n).map β₂ ∧
    (Comparison.appliedHomology F (ComplexShape.down ℕ) n).map γ₁ =
      (Comparison.appliedHomology F (ComplexShape.down ℕ) n).map γ₂

def projective_contravariant_lifts_independentType : Prop :=
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
    (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
    (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
    (hL : L.IsProjective) (hN : N.IsProjective)
    (H : Horseshoe.ProjectiveData i.hom p.hom L N)
    (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N')
    (α₁ α₂ : L.complex ⟶ L'.complex)
    (β₁ β₂ : H.middle.complex ⟶ H'.middle.complex)
    (γ₁ γ₂ : N.complex ⟶ N'.complex) (n : ℕ),
    Comparison.ChainLift L L' a.hom α₁ →
    Comparison.ChainLift L L' a.hom α₂ →
    Comparison.ChainLift H.middle H'.middle b.hom β₁ →
    Comparison.ChainLift H.middle H'.middle b.hom β₂ →
    Comparison.ChainLift N N' c.hom γ₁ →
    Comparison.ChainLift N N' c.hom γ₂ →
    (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map α₁ =
      (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map α₂ ∧
    (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map β₁ =
      (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map β₂ ∧
    (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map γ₁ =
      (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map γ₂

def projective_ab_lifts_independentType : Prop :=
  ∀ (R : Type u) [Ring R] 
    (F : ModuleCat.{max u v} R ⥤ AddCommGrpCat.{y}) [F.Additive]
    (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
    (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
    (hL : L.IsProjective) (hN : N.IsProjective)
    (H : Horseshoe.ProjectiveData i.hom p.hom L N)
    (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N')
    (α₁ α₂ : L.complex ⟶ L'.complex)
    (β₁ β₂ : H.middle.complex ⟶ H'.middle.complex)
    (γ₁ γ₂ : N.complex ⟶ N'.complex) (n : ℕ),
    Comparison.ChainLift L L' a.hom α₁ →
    Comparison.ChainLift L L' a.hom α₂ →
    Comparison.ChainLift H.middle H'.middle b.hom β₁ →
    Comparison.ChainLift H.middle H'.middle b.hom β₂ →
    Comparison.ChainLift N N' c.hom γ₁ →
    Comparison.ChainLift N N' c.hom γ₂ →
    (Comparison.appliedAbHomology F (ComplexShape.down ℕ) n).map α₁ =
      (Comparison.appliedAbHomology F (ComplexShape.down ℕ) n).map α₂ ∧
    (Comparison.appliedAbHomology F (ComplexShape.down ℕ) n).map β₁ =
      (Comparison.appliedAbHomology F (ComplexShape.down ℕ) n).map β₂ ∧
    (Comparison.appliedAbHomology F (ComplexShape.down ℕ) n).map γ₁ =
      (Comparison.appliedAbHomology F (ComplexShape.down ℕ) n).map γ₂

def projective_ab_contravariant_lifts_independentType : Prop :=
  ∀ (R : Type u) [Ring R] 
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ AddCommGrpCat.{y}) [F.Additive]
    (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
    (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
    (hL : L.IsProjective) (hN : N.IsProjective)
    (H : Horseshoe.ProjectiveData i.hom p.hom L N)
    (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N')
    (α₁ α₂ : L.complex ⟶ L'.complex)
    (β₁ β₂ : H.middle.complex ⟶ H'.middle.complex)
    (γ₁ γ₂ : N.complex ⟶ N'.complex) (n : ℕ),
    Comparison.ChainLift L L' a.hom α₁ →
    Comparison.ChainLift L L' a.hom α₂ →
    Comparison.ChainLift H.middle H'.middle b.hom β₁ →
    Comparison.ChainLift H.middle H'.middle b.hom β₂ →
    Comparison.ChainLift N N' c.hom γ₁ →
    Comparison.ChainLift N N' c.hom γ₂ →
    (Comparison.appliedAbContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map α₁ =
      (Comparison.appliedAbContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map α₂ ∧
    (Comparison.appliedAbContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map β₁ =
      (Comparison.appliedAbContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map β₂ ∧
    (Comparison.appliedAbContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map γ₁ =
      (Comparison.appliedAbContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map γ₂

/-- Every square in the induced long exact sequences commutes. -/
def applied_full_naturalityType : Prop :=
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {R : Type x} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C A' B' C' : HomologicalComplex D c}
    (F : D ⥤ ModuleCat.{y} R) [F.Additive]
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (α : A ⟶ A') (β : B ⟶ B') (γ : C ⟶ C'),
    i ≫ β = α ≫ i' → p ≫ γ = β ≫ p' →
    DegreewiseSplit i p → DegreewiseSplit i' p' →
    ∀ n m, c.Rel n m →
    ∀ (δ : Homology ((F.mapHomologicalComplex c).obj C) n →ₗ[R]
        Homology ((F.mapHomologicalComplex c).obj A) m)
      (ε : Homology ((F.mapHomologicalComplex c).obj C') n →ₗ[R]
        Homology ((F.mapHomologicalComplex c).obj A') m),
      Connecting ((F.mapHomologicalComplex c).map i)
        ((F.mapHomologicalComplex c).map p) n m δ →
      Connecting ((F.mapHomologicalComplex c).map i')
        ((F.mapHomologicalComplex c).map p') n m ε →
      (homologyMap ((F.mapHomologicalComplex c).map β) n).comp
          (homologyMap ((F.mapHomologicalComplex c).map i) n) =
        (homologyMap ((F.mapHomologicalComplex c).map i') n).comp
          (homologyMap ((F.mapHomologicalComplex c).map α) n) ∧
      (homologyMap ((F.mapHomologicalComplex c).map γ) n).comp
          (homologyMap ((F.mapHomologicalComplex c).map p) n) =
        (homologyMap ((F.mapHomologicalComplex c).map p') n).comp
          (homologyMap ((F.mapHomologicalComplex c).map β) n) ∧
      (homologyMap ((F.mapHomologicalComplex c).map α) m).comp δ =
        ε.comp (homologyMap ((F.mapHomologicalComplex c).map γ) n) ∧
      (homologyMap ((F.mapHomologicalComplex c).map β) m).comp
          (homologyMap ((F.mapHomologicalComplex c).map i) m) =
        (homologyMap ((F.mapHomologicalComplex c).map i') m).comp
          (homologyMap ((F.mapHomologicalComplex c).map α) m) ∧
      (homologyMap ((F.mapHomologicalComplex c).map γ) m).comp
          (homologyMap ((F.mapHomologicalComplex c).map p) m) =
        (homologyMap ((F.mapHomologicalComplex c).map p') m).comp
          (homologyMap ((F.mapHomologicalComplex c).map β) m)

def cochain_zero_exactType : Prop :=
  ∀ {R : Type u} [Ring R] {A B C : CochainComplex (ModuleCat.{v} R) ℕ}
    (i : A ⟶ B) (p : B ⟶ C), DegreewiseExact i p →
    Function.Injective (homologyMap i 0) ∧
      Function.Exact (homologyMap i 0) (homologyMap p 0)

def applied_cochain_zero_exactType : Prop :=
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {R : Type x} [Ring R] {A B C : CochainComplex D ℕ}
    (F : D ⥤ ModuleCat.{y} R) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p →
    Function.Injective (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map i) 0) ∧
    Function.Exact (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map i) 0)
      (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map p) 0)

def applied_contravariant_chain_zero_exactType : Prop :=
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {R : Type x} [Ring R] {A B C : ChainComplex D ℕ}
    (F : Dᵒᵖ ⥤ ModuleCat.{y} R) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p →
    Function.Injective (homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((HomologicalComplex.opFunctor D (ComplexShape.down ℕ)).map p.op)) 0) ∧
    Function.Exact (homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((HomologicalComplex.opFunctor D (ComplexShape.down ℕ)).map p.op)) 0)
      (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((HomologicalComplex.opFunctor D (ComplexShape.down ℕ)).map i.op)) 0)


section Square
variable {D : Type u} [Category.{v} D] [Preadditive D]
  {E : Type x} [Category.{y} E] [Preadditive E]
  {R : Type z} [Ring R] {ι : Type w} {c : ComplexShape ι}
  (I : D → Type t) (K : ∀ A, I A → HomologicalComplex E c)
  (L : ∀ {A B} (P : I A) (Q : I B), (A ⟶ B) → (K A P ⟶ K B Q) → Prop)

/-- Naturality in terms of the canonical comparison maps; no complex lifts
appear among the hypotheses of this property. -/
def ConnectingSquare (F : E ⥤ ModuleCat.{q} R) [F.Additive]
    (n m : ι)
    (Cn : Comparison.CoherentComparison I K L
      (F.mapHomologicalComplex c ⋙ Comparison.quotientHomology c n))
    (Cm : Comparison.CoherentComparison I K L
      (F.mapHomologicalComplex c ⋙ Comparison.quotientHomology c m))
    {A B C A' B' C' : D}
    (PA : I A) (PB : I B) (PC : I C) (QA : I A') (QB : I B') (QC : I C')
    (i : K A PA ⟶ K B PB) (p : K B PB ⟶ K C PC)
    (i' : K A' QA ⟶ K B' QB) (p' : K B' QB ⟶ K C' QC)
    (a : A ⟶ A') (cc : C ⟶ C') : Prop :=
  ∀ (δ : Homology ((F.mapHomologicalComplex c).obj (K C PC)) n →ₗ[R]
        Homology ((F.mapHomologicalComplex c).obj (K A PA)) m)
    (ε : Homology ((F.mapHomologicalComplex c).obj (K C' QC)) n →ₗ[R]
        Homology ((F.mapHomologicalComplex c).obj (K A' QA)) m),
    Connecting ((F.mapHomologicalComplex c).map i)
      ((F.mapHomologicalComplex c).map p) n m δ →
    Connecting ((F.mapHomologicalComplex c).map i')
      ((F.mapHomologicalComplex c).map p') n m ε →
    (Cm.map PA QA a).hom.comp δ = ε.comp (Cn.map PC QC cc).hom

/-- Under a contravariant additive functor, the connecting map goes from the
old left end to the old right end, and all comparison arrows reverse. -/
def ContravariantConnectingSquare (F : Eᵒᵖ ⥤ ModuleCat.{q} R) [F.Additive]
    (n m : ι)
    (Cn : Comparison.CoherentComparison I K L
      (HomologicalComplex.opFunctor E c ⋙ F.mapHomologicalComplex c.symm ⋙
        Comparison.quotientHomology c.symm n).rightOp)
    (Cm : Comparison.CoherentComparison I K L
      (HomologicalComplex.opFunctor E c ⋙ F.mapHomologicalComplex c.symm ⋙
        Comparison.quotientHomology c.symm m).rightOp)
    {A B C A' B' C' : D}
    (PA : I A) (PB : I B) (PC : I C) (QA : I A') (QB : I B') (QC : I C')
    (i : K A PA ⟶ K B PB) (p : K B PB ⟶ K C PC)
    (i' : K A' QA ⟶ K B' QB) (p' : K B' QB ⟶ K C' QC)
    (a : A ⟶ A') (cc : C ⟶ C') : Prop :=
  ∀ (δ : Homology ((F.mapHomologicalComplex c.symm).obj (K A PA).op) n →ₗ[R]
        Homology ((F.mapHomologicalComplex c.symm).obj (K C PC).op) m)
    (ε : Homology ((F.mapHomologicalComplex c.symm).obj (K A' QA).op) n →ₗ[R]
        Homology ((F.mapHomologicalComplex c.symm).obj (K C' QC).op) m),
    Connecting
      ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor E c).map p.op))
      ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor E c).map i.op)) n m δ →
    Connecting
      ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor E c).map p'.op))
      ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor E c).map i'.op)) n m ε →
    (Cm.map PC QC cc).unop.hom.comp ε = δ.comp (Cn.map PA QA a).unop.hom

end Square

def projective_connectingType : Prop :=
  ∀   (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.down ℕ).Rel n m)
  (Cn : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedHomology F (ComplexShape.down ℕ) n))
  (Cm : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedHomology F (ComplexShape.down ℕ) m))
  (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
  (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
  (hL : L.IsProjective) (hN : N.IsProjective) (hL' : L'.IsProjective) (hN' : N'.IsProjective)
  (H : Horseshoe.ProjectiveData i.hom p.hom L N) (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N'),
  ConnectingSquare (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver
    F n m Cn Cm ⟨L, hL⟩ ⟨H.middle, H.projective⟩ ⟨N, hN⟩ ⟨L', hL'⟩ ⟨H'.middle, H'.projective⟩ ⟨N', hN'⟩
    H.inclusion H.projection H'.inclusion H'.projection a cc

def projective_contravariant_connectingType : Prop :=
  ∀   (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.down ℕ).symm.Rel n m)
  (Cn : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp)
  (Cm : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) m).rightOp)
  (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
  (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
  (hL : L.IsProjective) (hN : N.IsProjective) (hL' : L'.IsProjective) (hN' : N'.IsProjective)
  (H : Horseshoe.ProjectiveData i.hom p.hom L N) (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N'),
  ContravariantConnectingSquare (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver
    F n m Cn Cm ⟨L, hL⟩ ⟨H.middle, H.projective⟩ ⟨N, hN⟩ ⟨L', hL'⟩ ⟨H'.middle, H'.projective⟩ ⟨N', hN'⟩
    H.inclusion H.projection H'.inclusion H'.projection a cc

def injective_connectingType : Prop :=
  ∀   (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.up ℕ).Rel n m)
  (Cn : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedHomology F (ComplexShape.up ℕ) n))
  (Cm : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedHomology F (ComplexShape.up ℕ) m))
  (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
  (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
  (H : Horseshoe.InjectiveData i.hom p.hom L N) (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N'),
  ConnectingSquare (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver
    F n m Cn Cm L H.middle N L' H'.middle N'
    H.inclusion H.projection H'.inclusion H'.projection a cc

def injective_contravariant_connectingType : Prop :=
  ∀   (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.up ℕ).symm.Rel n m)
  (Cn : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp)
  (Cm : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) m).rightOp)
  (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
  (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
  (H : Horseshoe.InjectiveData i.hom p.hom L N) (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N'),
  ContravariantConnectingSquare (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver
    F n m Cn Cm L H.middle N L' H'.middle N'
    H.inclusion H.projection H'.inclusion H'.projection a cc


def projective_canonical_connectingType : Prop :=
  ∀   (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.down ℕ).Rel n m),
  ∃ (Cn : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedHomology F (ComplexShape.down ℕ) n)), ∃ (Cm : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedHomology F (ComplexShape.down ℕ) m)),
  ∀ (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
  (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
  (hL : L.IsProjective) (hN : N.IsProjective) (hL' : L'.IsProjective) (hN' : N'.IsProjective)
  (H : Horseshoe.ProjectiveData i.hom p.hom L N) (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N'),
  ConnectingSquare (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver
    F n m Cn Cm ⟨L, hL⟩ ⟨H.middle, H.projective⟩ ⟨N, hN⟩ ⟨L', hL'⟩ ⟨H'.middle, H'.projective⟩ ⟨N', hN'⟩
    H.inclusion H.projection H'.inclusion H'.projection a cc

def projective_contravariant_canonical_connectingType : Prop :=
  ∀   (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.down ℕ).symm.Rel n m),
  ∃ (Cn : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp), ∃ (Cm : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) m).rightOp),
  ∀ (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
  (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
  (hL : L.IsProjective) (hN : N.IsProjective) (hL' : L'.IsProjective) (hN' : N'.IsProjective)
  (H : Horseshoe.ProjectiveData i.hom p.hom L N) (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N'),
  ContravariantConnectingSquare (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver
    F n m Cn Cm ⟨L, hL⟩ ⟨H.middle, H.projective⟩ ⟨N, hN⟩ ⟨L', hL'⟩ ⟨H'.middle, H'.projective⟩ ⟨N', hN'⟩
    H.inclusion H.projection H'.inclusion H'.projection a cc

def injective_canonical_connectingType : Prop :=
  ∀   (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.up ℕ).Rel n m),
  ∃ (Cn : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedHomology F (ComplexShape.up ℕ) n)), ∃ (Cm : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedHomology F (ComplexShape.up ℕ) m)),
  ∀ (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
  (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
  (H : Horseshoe.InjectiveData i.hom p.hom L N) (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N'),
  ConnectingSquare (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver
    F n m Cn Cm L H.middle N L' H'.middle N'
    H.inclusion H.projection H'.inclusion H'.projection a cc

def injective_contravariant_canonical_connectingType : Prop :=
  ∀   (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.up ℕ).symm.Rel n m),
  ∃ (Cn : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp), ∃ (Cm : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) m).rightOp),
  ∀ (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
  (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
  (H : Horseshoe.InjectiveData i.hom p.hom L N) (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N'),
  ContravariantConnectingSquare (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver
    F n m Cn Cm L H.middle N L' H'.middle N'
    H.inclusion H.projection H'.inclusion H'.projection a cc

def projective_transportType : Prop :=
  ∀   (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.down ℕ).Rel n m)
  (Cn : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedHomology F (ComplexShape.down ℕ) n))
  (Cm : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedHomology F (ComplexShape.down ℕ) m))
  (A B C : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C)
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
  (L' : ProjectiveResolutions.Resolution R A) (N' : ProjectiveResolutions.Resolution R C)
  (hL : L.IsProjective) (hN : N.IsProjective) (hL' : L'.IsProjective) (hN' : N'.IsProjective)
  (H : Horseshoe.ProjectiveData i.hom p.hom L N) (H' : Horseshoe.ProjectiveData i.hom p.hom L' N')
  (δ : Homology ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj N.complex) n →ₗ[S] Homology ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj L.complex) m)
  (ε : Homology ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj N'.complex) n →ₗ[S] Homology ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj L'.complex) m)
  (hδ : Connecting ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map H.inclusion) ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map H.projection) n m δ)
  (hε : Connecting ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map H'.inclusion) ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map H'.projection) n m ε),
  (Cm.comparison ⟨L, hL⟩ ⟨L', hL'⟩).hom.hom.comp δ =
      ε.comp (Cn.comparison ⟨N, hN⟩ ⟨N', hN'⟩).hom.hom

def projective_contravariant_transportType : Prop :=
  ∀   (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.down ℕ).symm.Rel n m)
  (Cn : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp)
  (Cm : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) m).rightOp)
  (A B C : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C)
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
  (L' : ProjectiveResolutions.Resolution R A) (N' : ProjectiveResolutions.Resolution R C)
  (hL : L.IsProjective) (hN : N.IsProjective) (hL' : L'.IsProjective) (hN' : N'.IsProjective)
  (H : Horseshoe.ProjectiveData i.hom p.hom L N) (H' : Horseshoe.ProjectiveData i.hom p.hom L' N')
  (δ : Homology ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).obj L.complex.op) n →ₗ[S] Homology ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).obj N.complex.op) m)
  (ε : Homology ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).obj L'.complex.op) n →ₗ[S] Homology ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).obj N'.complex.op) m)
  (hδ : Connecting ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map ((HomologicalComplex.opFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).map H.projection.op))
      ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map ((HomologicalComplex.opFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).map H.inclusion.op)) n m δ)
  (hε : Connecting ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map ((HomologicalComplex.opFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).map H'.projection.op))
      ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map ((HomologicalComplex.opFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).map H'.inclusion.op)) n m ε),
  (Cm.comparison ⟨N, hN⟩ ⟨N', hN'⟩).hom.unop.hom.comp ε =
      δ.comp (Cn.comparison ⟨L, hL⟩ ⟨L', hL'⟩).hom.unop.hom

def injective_transportType : Prop :=
  ∀   (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.up ℕ).Rel n m)
  (Cn : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedHomology F (ComplexShape.up ℕ) n))
  (Cm : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedHomology F (ComplexShape.up ℕ) m))
  (A B C : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C)
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
  (L' : InjectiveResolutions.Resolution R A) (N' : InjectiveResolutions.Resolution R C)
  (H : Horseshoe.InjectiveData i.hom p.hom L N) (H' : Horseshoe.InjectiveData i.hom p.hom L' N')
  (δ : Homology ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj N.complex) n →ₗ[S] Homology ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L.complex) m)
  (ε : Homology ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj N'.complex) n →ₗ[S] Homology ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L'.complex) m)
  (hδ : Connecting ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map H.inclusion) ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map H.projection) n m δ)
  (hε : Connecting ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map H'.inclusion) ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map H'.projection) n m ε),
  (Cm.comparison L L').hom.hom.comp δ =
      ε.comp (Cn.comparison N N').hom.hom

def injective_contravariant_transportType : Prop :=
  ∀   (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.up ℕ).symm.Rel n m)
  (Cn : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp)
  (Cm : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) m).rightOp)
  (A B C : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C)
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
  (L' : InjectiveResolutions.Resolution R A) (N' : InjectiveResolutions.Resolution R C)
  (H : Horseshoe.InjectiveData i.hom p.hom L N) (H' : Horseshoe.InjectiveData i.hom p.hom L' N')
  (δ : Homology ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).obj L.complex.op) n →ₗ[S] Homology ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).obj N.complex.op) m)
  (ε : Homology ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).obj L'.complex.op) n →ₗ[S] Homology ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).obj N'.complex.op) m)
  (hδ : Connecting ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).map ((HomologicalComplex.opFunctor (ModuleCat.{max u v} R) (ComplexShape.up ℕ)).map H.projection.op))
      ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).map ((HomologicalComplex.opFunctor (ModuleCat.{max u v} R) (ComplexShape.up ℕ)).map H.inclusion.op)) n m δ)
  (hε : Connecting ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).map ((HomologicalComplex.opFunctor (ModuleCat.{max u v} R) (ComplexShape.up ℕ)).map H'.projection.op))
      ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).map ((HomologicalComplex.opFunctor (ModuleCat.{max u v} R) (ComplexShape.up ℕ)).map H'.inclusion.op)) n m ε),
  (Cm.comparison N N').hom.unop.hom.comp ε =
      δ.comp (Cn.comparison L L').hom.unop.hom


def coherent_maps_transportType : Prop :=
  ∀     {D : Type u} [Category.{v} D] [Preadditive D]
    {E : Type x} [Category.{y} E] [Preadditive E]
    {W : Type z} [Category.{q} W] [Preadditive W]
    {I : D → Type t} {K : ∀ A, I A → E}
    {L : ∀ {A B} (P : I A) (Q : I B), (A ⟶ B) → (K A P ⟶ K B Q) → Prop}
    {H : E ⥤ W} (C : Comparison.CoherentComparison I K L H)
    {A B : D} (P P' : I A) (Q Q' : I B) (a : A ⟶ B)
    (f : K A P ⟶ K B Q) (g : K A P' ⟶ K B Q')
    (hf : L P Q a f) (hg : L P' Q' a g),
    H.map f ≫ (C.comparison Q Q').hom =
      (C.comparison P P').hom ≫ H.map g


def contravariant_naturalityType : Prop :=
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
  {R : Type x} [Ring R] {ι : Type w} {c : ComplexShape ι}
  {A B C A' B' C' : HomologicalComplex D c}
  (F : Dᵒᵖ ⥤ ModuleCat.{y} R) [F.Additive]
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (α : A ⟶ A') (β : B ⟶ B') (γ : C ⟶ C')
  (hi : i ≫ β = α ≫ i') (hp : p ≫ γ = β ≫ p')
  (hs : DegreewiseSplit i p) (hs' : DegreewiseSplit i' p')
  (n m : ι) (hnm : c.symm.Rel n m)
  (δ : Homology ((F.mapHomologicalComplex c.symm).obj A.op) n →ₗ[R]
      Homology ((F.mapHomologicalComplex c.symm).obj C.op) m)
  (ε : Homology ((F.mapHomologicalComplex c.symm).obj A'.op) n →ₗ[R]
      Homology ((F.mapHomologicalComplex c.symm).obj C'.op) m)
  (hδ : Connecting
    ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map p.op))
    ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map i.op)) n m δ)
  (hε : Connecting
    ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map p'.op))
    ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map i'.op)) n m ε),
  (homologyMap ((F.mapHomologicalComplex c.symm).map
    ((HomologicalComplex.opFunctor D c).map γ.op)) m).comp ε =
  δ.comp (homologyMap ((F.mapHomologicalComplex c.symm).map
    ((HomologicalComplex.opFunctor D c).map α.op)) n)

def coherent_contravariant_connectingType : Prop :=
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
  {E : Type x} [Category.{y} E] [Preadditive E]
  {R : Type z} [Ring R] {ι : Type w} {c : ComplexShape ι}
  (I : D → Type t) (K : ∀ A, I A → HomologicalComplex E c)
  (L : ∀ {A B} (P : I A) (Q : I B), (A ⟶ B) → (K A P ⟶ K B Q) → Prop)
  (F : Eᵒᵖ ⥤ ModuleCat.{q} R) [F.Additive]
  (n m : ι) (hnm : c.symm.Rel n m)
  (Cn : Comparison.CoherentComparison I K L
    (HomologicalComplex.opFunctor E c ⋙ F.mapHomologicalComplex c.symm ⋙
      Comparison.quotientHomology c.symm n).rightOp)
  (Cm : Comparison.CoherentComparison I K L
    (HomologicalComplex.opFunctor E c ⋙ F.mapHomologicalComplex c.symm ⋙
      Comparison.quotientHomology c.symm m).rightOp)
  {A B C A' B' C' : D}
  (PA : I A) (PB : I B) (PC : I C) (QA : I A') (QB : I B') (QC : I C')
  (i : K A PA ⟶ K B PB) (p : K B PB ⟶ K C PC)
  (i' : K A' QA ⟶ K B' QB) (p' : K B' QB ⟶ K C' QC)
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (α : K A PA ⟶ K A' QA) (β : K B PB ⟶ K B' QB) (γ : K C PC ⟶ K C' QC)
  (ha : L PA QA a α) (_hb : L PB QB b β) (hc : L PC QC cc γ)
  (hi : i ≫ β = α ≫ i') (hp : p ≫ γ = β ≫ p')
  (hs : DegreewiseSplit i p) (hs' : DegreewiseSplit i' p'),
  ContravariantConnectingSquare I K L F n m Cn Cm PA PB PC QA QB QC i p i' p' a cc

/-- Canonical connecting squares for abelian-group-valued functors, using
the canonical integer module representation of their homology. -/
def projective_ab_canonical_connectingType : Prop :=
  ∀   (R : Type u) [Ring R]
  (F : ModuleCat.{max u v} R ⥤ AddCommGrpCat.{y}) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.down ℕ).Rel n m),
  ∃ (Cn : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedHomology (F ⋙ Comparison.abelianGroupsToModules) (ComplexShape.down ℕ) n)), ∃ (Cm : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedHomology (F ⋙ Comparison.abelianGroupsToModules) (ComplexShape.down ℕ) m)),
  ∀ (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
  (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
  (hL : L.IsProjective) (hN : N.IsProjective) (hL' : L'.IsProjective) (hN' : N'.IsProjective)
  (H : Horseshoe.ProjectiveData i.hom p.hom L N) (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N'),
  ConnectingSquare (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver
    (F ⋙ Comparison.abelianGroupsToModules) n m Cn Cm ⟨L, hL⟩ ⟨H.middle, H.projective⟩ ⟨N, hN⟩ ⟨L', hL'⟩ ⟨H'.middle, H'.projective⟩ ⟨N', hN'⟩
    H.inclusion H.projection H'.inclusion H'.projection a cc

def projective_contravariant_ab_canonical_connectingType : Prop :=
  ∀   (R : Type u) [Ring R]
  (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ AddCommGrpCat.{y}) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.down ℕ).symm.Rel n m),
  ∃ (Cn : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedContravariantHomology (F ⋙ Comparison.abelianGroupsToModules) (ComplexShape.down ℕ) n).rightOp), ∃ (Cm : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedContravariantHomology (F ⋙ Comparison.abelianGroupsToModules) (ComplexShape.down ℕ) m).rightOp),
  ∀ (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
  (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
  (hL : L.IsProjective) (hN : N.IsProjective) (hL' : L'.IsProjective) (hN' : N'.IsProjective)
  (H : Horseshoe.ProjectiveData i.hom p.hom L N) (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N'),
  ContravariantConnectingSquare (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver
    (F ⋙ Comparison.abelianGroupsToModules) n m Cn Cm ⟨L, hL⟩ ⟨H.middle, H.projective⟩ ⟨N, hN⟩ ⟨L', hL'⟩ ⟨H'.middle, H'.projective⟩ ⟨N', hN'⟩
    H.inclusion H.projection H'.inclusion H'.projection a cc

def injective_ab_canonical_connectingType : Prop :=
  ∀   (R : Type u) [Ring R]
  (F : ModuleCat.{max u v} R ⥤ AddCommGrpCat.{y}) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.up ℕ).Rel n m),
  ∃ (Cn : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedHomology (F ⋙ Comparison.abelianGroupsToModules) (ComplexShape.up ℕ) n)), ∃ (Cm : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedHomology (F ⋙ Comparison.abelianGroupsToModules) (ComplexShape.up ℕ) m)),
  ∀ (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
  (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
  (H : Horseshoe.InjectiveData i.hom p.hom L N) (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N'),
  ConnectingSquare (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver
    (F ⋙ Comparison.abelianGroupsToModules) n m Cn Cm L H.middle N L' H'.middle N'
    H.inclusion H.projection H'.inclusion H'.projection a cc

def injective_contravariant_ab_canonical_connectingType : Prop :=
  ∀   (R : Type u) [Ring R]
  (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ AddCommGrpCat.{y}) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.up ℕ).symm.Rel n m),
  ∃ (Cn : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedContravariantHomology (F ⋙ Comparison.abelianGroupsToModules) (ComplexShape.up ℕ) n).rightOp), ∃ (Cm : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedContravariantHomology (F ⋙ Comparison.abelianGroupsToModules) (ComplexShape.up ℕ) m).rightOp),
  ∀ (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
  (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
  (H : Horseshoe.InjectiveData i.hom p.hom L N) (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N'),
  ContravariantConnectingSquare (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver
    (F ⋙ Comparison.abelianGroupsToModules) n m Cn Cm L H.middle N L' H'.middle N'
    H.inclusion H.projection H'.inclusion H'.projection a cc

def chain_bottom_exactType : Prop :=
  ∀ {R : Type u} [Ring R] {A B C : ChainComplex (ModuleCat.{v} R) ℕ}
    (i : A ⟶ B) (p : B ⟶ C), DegreewiseExact i p →
    Function.Exact (homologyMap i 0) (homologyMap p 0) ∧
      Function.Surjective (homologyMap p 0)

def applied_chain_bottomType : Prop :=
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {R : Type x} [Ring R] {A B C : ChainComplex D ℕ}
    (F : D ⥤ ModuleCat.{y} R) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p →
    Function.Exact (homologyMap ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map i) 0)
      (homologyMap ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map p) 0) ∧
    Function.Surjective (homologyMap ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map p) 0)

def applied_contravariant_cochain_bottomType : Prop :=
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {R : Type x} [Ring R] {A B C : CochainComplex D ℕ}
    (F : Dᵒᵖ ⥤ ModuleCat.{y} R) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p →
    Function.Exact
      (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).map
        ((HomologicalComplex.opFunctor D (ComplexShape.up ℕ)).map p.op)) 0)
      (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).map
        ((HomologicalComplex.opFunctor D (ComplexShape.up ℕ)).map i.op)) 0) ∧
    Function.Surjective
      (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).map
        ((HomologicalComplex.opFunctor D (ComplexShape.up ℕ)).map i.op)) 0)

end P103.Specs.Ch10.HorseshoeNaturality
