import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.ProjectiveResolutions
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.InjectiveResolutions
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.Opposite

/-! Comparison, paper.tex 2475–2519. No projectivity is required of the
chain target; no injectivity is required of the cochain source. All rings,
including zero rings and opposite rings, are allowed. -/
namespace P103.Specs.Ch10.Comparison
open CategoryTheory
noncomputable section
universe u v w x y
abbrev LeftResolution := ProjectiveResolutions.Resolution
abbrev InjectiveResolution := InjectiveResolutions.Resolution

/-- An ordinary exact augmented cochain resolution, without injectivity. -/
structure RightResolution (R : Type u) [Ring R] (A : Type v)
    [AddCommGroup A] [Module R A] where
  complex : CochainComplex (ModuleCat.{max u v} R) ℕ
  η : A →ₗ[R] complex.X 0
  injective_η : Function.Injective η
  exact_zero : Function.Exact η (complex.d 0 1).hom
  exact_succ : ∀ n, Function.Exact (complex.d n (n + 1)).hom
    (complex.d (n + 1) (n + 2)).hom

abbrev ofInjective {R : Type u} [Ring R] {A : Type v} [AddCommGroup A] [Module R A]
    (I : InjectiveResolution R A) : RightResolution R A where
  complex := I.complex
  η := I.η
  injective_η := I.injective_η
  exact_zero := I.exact_zero
  exact_succ := I.exact_succ

variable {R : Type u} [Ring R] {A B : Type v}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

def ChainLift (P : LeftResolution R A) (Q : LeftResolution R B)
    (u : A →ₗ[R] B) (f : P.complex ⟶ Q.complex) : Prop :=
  Q.ε.comp (f.f 0).hom = u.comp P.ε

def CochainLift (J : RightResolution R A) (I : InjectiveResolution R B)
    (u : A →ₗ[R] B) (f : J.complex ⟶ I.complex) : Prop :=
  (f.f 0).hom.comp J.η = I.η.comp u

def chain_existsType : Prop :=
  ∀ (R : Type u) [Ring R] (A B : Type v) [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (P : LeftResolution R A) (Q : LeftResolution R B),
    P.IsProjective → ∀ u : A →ₗ[R] B,
    ∃ f : P.complex ⟶ Q.complex, ChainLift P Q u f

def chain_uniqueType : Prop :=
  ∀ (R : Type u) [Ring R] (A B : Type v) [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (P : LeftResolution R A) (Q : LeftResolution R B),
    P.IsProjective → ∀ (u : A →ₗ[R] B) (f g : P.complex ⟶ Q.complex),
    ChainLift P Q u f → ChainLift P Q u g → Nonempty (Homotopy f g)

def cochain_existsType : Prop :=
  ∀ (R : Type u) [Ring R] (A B : Type v) [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (J : RightResolution R A) (I : InjectiveResolution R B)
    (u : A →ₗ[R] B), ∃ f : J.complex ⟶ I.complex, CochainLift J I u f

def cochain_uniqueType : Prop :=
  ∀ (R : Type u) [Ring R] (A B : Type v) [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (J : RightResolution R A) (I : InjectiveResolution R B)
    (u : A →ₗ[R] B) (f g : J.complex ⟶ I.complex),
    CochainLift J I u f → CochainLift J I u g → Nonempty (Homotopy f g)

def projective_equivType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A]
    (P Q : LeftResolution R A), P.IsProjective → Q.IsProjective →
    ∃ e : HomotopyEquiv P.complex Q.complex,
      ChainLift P Q LinearMap.id e.hom ∧ ChainLift Q P LinearMap.id e.inv

def injective_equivType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A]
    (I J : InjectiveResolution R A),
    ∃ e : HomotopyEquiv I.complex J.complex,
      CochainLift (ofInjective I) J LinearMap.id e.hom ∧
      CochainLift (ofInjective J) I LinearMap.id e.inv

/-! The final assertion is expressed simultaneously for all resolutions, so
its composition law includes the cocycle law for comparison isomorphisms. -/
section Coherence
universe u₁ v₁ u₂ v₂ u₃ v₃ t
variable {D : Type u₁} [Category.{v₁} D] [Preadditive D]
  {E : Type u₂} [Category.{v₂} E] [Preadditive E]
  {W : Type u₃} [Category.{v₃} W] [Preadditive W]

/-- A family of maps independent of all lifts and all resolutions, with
specified comparison isomorphisms and their naturality and cocycle laws. -/
structure CoherentComparison (I : D → Type t) (K : ∀ A, I A → E)
    (L : ∀ {A B} (P : I A) (Q : I B), (A ⟶ B) → (K A P ⟶ K B Q) → Prop)
    (H : E ⥤ W) where
  map : ∀ {A B} (P : I A) (Q : I B), (A ⟶ B) → (H.obj (K A P) ⟶ H.obj (K B Q))
  map_eq : ∀ {A B} (P : I A) (Q : I B) (u : A ⟶ B) (f : K A P ⟶ K B Q),
    L P Q u f → map P Q u = H.map f
  map_id : ∀ A (P : I A), map P P (𝟙 A) = 𝟙 _
  map_comp : ∀ {A B C} (P : I A) (Q : I B) (T : I C) (u : A ⟶ B) (v : B ⟶ C),
    map P T (u ≫ v) = map P Q u ≫ map Q T v
  map_add : ∀ {A B} (P : I A) (Q : I B) (u v : A ⟶ B),
    map P Q (u + v) = map P Q u + map P Q v
  comparison : ∀ {A} (P Q : I A), H.obj (K A P) ≅ H.obj (K A Q)
  comparison_hom : ∀ {A} (P Q : I A), (comparison P Q).hom = map P Q (𝟙 A)
  comparison_inv : ∀ {A} (P Q : I A), (comparison P Q).inv = map Q P (𝟙 A)
  comparison_refl : ∀ {A} (P : I A), comparison P P = Iso.refl _
  comparison_trans : ∀ {A} (P Q T : I A), comparison P Q ≪≫ comparison Q T = comparison P T
  naturality : ∀ {A B} (P P' : I A) (Q Q' : I B) (u : A ⟶ B),
    map P Q u ≫ (comparison Q Q').hom = (comparison P P').hom ≫ map P' Q' u
end Coherence

/-- The explicit quotient homology, as a functor. It applies to arbitrary
module complexes, whether or not the additive functor preserves exactness. -/
def quotientHomology {S : Type w} [Ring S] {ι : Type x} (c : ComplexShape ι) (n : ι) :
    HomologicalComplex (ModuleCat.{v} S) c ⥤ ModuleCat.{v} S where
  obj K := ModuleCat.of S (Complexes.Homology K n)
  map f := ModuleCat.ofHom (Complexes.homologyMap f n)
  map_id K := by
    apply ModuleCat.hom_ext
    apply (Complexes.cycleBoundaries K n).quot_hom_ext
    intro z
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply (Complexes.cycleBoundaries _ n).quot_hom_ext
    intro z
    rfl

instance quotientHomology_additive {S : Type w} [Ring S] {ι : Type x}
    (c : ComplexShape ι) (n : ι) : (quotientHomology c n : HomologicalComplex (ModuleCat.{v} S) c ⥤ ModuleCat.{v} S).Additive where
  map_add {K T} f g := by
    apply ModuleCat.hom_ext
    apply (Complexes.cycleBoundaries K n).quot_hom_ext
    intro z
    change Complexes.homologyClass T n (Complexes.cyclesMap (f + g) n z) =
      Complexes.homologyClass T n (Complexes.cyclesMap f n z) +
      Complexes.homologyClass T n (Complexes.cyclesMap g n z)
    rw [← map_add]
    congr 1

abbrev ProjectiveChoice (R : Type u) [Ring R] (A : ModuleCat.{v} R) :=
  {P : LeftResolution R A // P.IsProjective}

abbrev projectiveComplex (R : Type u) [Ring R] (A : ModuleCat.{v} R)
    (P : ProjectiveChoice R A) := P.val.complex

abbrev projectiveOver {R : Type u} [Ring R] {A B : ModuleCat.{v} R}
    (P : ProjectiveChoice R A) (Q : ProjectiveChoice R B) (u : A ⟶ B)
    (f : P.val.complex ⟶ Q.val.complex) := ChainLift P.val Q.val u.hom f

abbrev injectiveComplex (R : Type u) [Ring R] (A : ModuleCat.{v} R)
    (I : InjectiveResolution R A) := I.complex

abbrev injectiveOver {R : Type u} [Ring R] {A B : ModuleCat.{v} R}
    (I : InjectiveResolution R A) (J : InjectiveResolution R B) (u : A ⟶ B)
    (f : I.complex ⟶ J.complex) := CochainLift (ofInjective I) J u.hom f

/-- Applying an additive covariant functor and then taking quotient homology. -/
abbrev appliedHomology {R : Type u} [Ring R] {S : Type w} [Ring S]
    {ι : Type x} (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
    (c : ComplexShape ι) (n : ι) := F.mapHomologicalComplex c ⋙ quotientHomology c n

/-- Opposing reverses all differentials and all chain-map arrows, so a
contravariant functor on a chain resolution produces a cochain complex. -/
abbrev appliedContravariantHomology {R : Type u} [Ring R] {S : Type w} [Ring S]
    {ι : Type x} (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
    (c : ComplexShape ι) (n : ι) :=
  HomologicalComplex.opFunctor (ModuleCat.{max u v} R) c ⋙
    F.mapHomologicalComplex c.symm ⋙ quotientHomology c.symm n

def chain_homology_functorialType : Prop :=
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive] (n : ℕ),
    Nonempty (CoherentComparison (ProjectiveChoice R) (projectiveComplex R) projectiveOver
      (appliedHomology F (ComplexShape.down ℕ) n))

def cochain_homology_functorialType : Prop :=
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive] (n : ℕ),
    Nonempty (CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolution R A)
      (injectiveComplex R) injectiveOver (appliedHomology F (ComplexShape.up ℕ) n))

/-- The target opposite records that the homology map for u goes from the
resolution of B to the resolution of A. `rightOp` reverses these arrows. -/
def chain_contravariant_functorialType : Prop :=
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive] (n : ℕ),
    Nonempty (CoherentComparison (ProjectiveChoice R) (projectiveComplex R) projectiveOver
      (appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp)

def cochain_contravariant_functorialType : Prop :=
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive] (n : ℕ),
    Nonempty (CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolution R A)
      (injectiveComplex R) injectiveOver
      (appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp)

/-- An abelian group carries its canonical integer-module structure. This
functor changes neither elements nor additive maps. -/
def abelianGroupsToModules : AddCommGrpCat.{y} ⥤ ModuleCat.{y} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap
  map_id _ := rfl
  map_comp _ _ := rfl

instance abelianGroupsToModules_additive : abelianGroupsToModules.{y}.Additive where
  map_add := rfl

/-- Homology of an abelian-group-valued functor, returned in the category of
abelian groups. The quotient is the usual cycles modulo boundaries quotient. -/
abbrev appliedAbHomology {R : Type u} [Ring R] {ι : Type x}
    (F : ModuleCat.{max u v} R ⥤ AddCommGrpCat.{y}) [F.Additive]
    (c : ComplexShape ι) (n : ι) :=
  appliedHomology (F ⋙ abelianGroupsToModules) c n ⋙
    forget₂ (ModuleCat ℤ) AddCommGrpCat

abbrev appliedAbContravariantHomology {R : Type u} [Ring R] {ι : Type x}
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ AddCommGrpCat.{y}) [F.Additive]
    (c : ComplexShape ι) (n : ι) :=
  appliedContravariantHomology (F ⋙ abelianGroupsToModules) c n ⋙
    forget₂ (ModuleCat ℤ) AddCommGrpCat

def chain_ab_homology_functorialType : Prop :=
  ∀ (R : Type u) [Ring R]
    (F : ModuleCat.{max u v} R ⥤ AddCommGrpCat.{y}) [F.Additive] (n : ℕ),
    Nonempty (CoherentComparison (ProjectiveChoice R) (projectiveComplex R) projectiveOver (appliedAbHomology F (ComplexShape.down ℕ) n))

def chain_ab_contravariant_functorialType : Prop :=
  ∀ (R : Type u) [Ring R]
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ AddCommGrpCat.{y}) [F.Additive] (n : ℕ),
    Nonempty (CoherentComparison (ProjectiveChoice R) (projectiveComplex R) projectiveOver (appliedAbContravariantHomology F (ComplexShape.down ℕ) n).rightOp)

def cochain_ab_homology_functorialType : Prop :=
  ∀ (R : Type u) [Ring R]
    (F : ModuleCat.{max u v} R ⥤ AddCommGrpCat.{y}) [F.Additive] (n : ℕ),
    Nonempty (CoherentComparison ((fun A : ModuleCat.{v} R => InjectiveResolution R A)) (injectiveComplex R) injectiveOver (appliedAbHomology F (ComplexShape.up ℕ) n))

def cochain_ab_contravariant_functorialType : Prop :=
  ∀ (R : Type u) [Ring R]
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ AddCommGrpCat.{y}) [F.Additive] (n : ℕ),
    Nonempty (CoherentComparison ((fun A : ModuleCat.{v} R => InjectiveResolution R A)) (injectiveComplex R) injectiveOver (appliedAbContravariantHomology F (ComplexShape.up ℕ) n).rightOp)

def chain_homology_independentType : Prop :=
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
    (A B : Type v) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : LeftResolution R A) (Q : LeftResolution R B) (_hP : P.IsProjective) (u : A →ₗ[R] B) (f g : P.complex ⟶ Q.complex) (n : ℕ),
    ChainLift P Q u f → ChainLift P Q u g → (appliedHomology F (ComplexShape.down ℕ) n).map f = (appliedHomology F (ComplexShape.down ℕ) n).map g

def chain_contravariant_independentType : Prop :=
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
    (A B : Type v) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : LeftResolution R A) (Q : LeftResolution R B) (_hP : P.IsProjective) (u : A →ₗ[R] B) (f g : P.complex ⟶ Q.complex) (n : ℕ),
    ChainLift P Q u f → ChainLift P Q u g → (appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map f = (appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map g

def cochain_homology_independentType : Prop :=
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
    (A B : Type v) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : RightResolution R A) (Q : InjectiveResolution R B) (u : A →ₗ[R] B) (f g : P.complex ⟶ Q.complex) (n : ℕ),
    CochainLift P Q u f → CochainLift P Q u g → (appliedHomology F (ComplexShape.up ℕ) n).map f = (appliedHomology F (ComplexShape.up ℕ) n).map g

def cochain_contravariant_independentType : Prop :=
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
    (A B : Type v) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : RightResolution R A) (Q : InjectiveResolution R B) (u : A →ₗ[R] B) (f g : P.complex ⟶ Q.complex) (n : ℕ),
    CochainLift P Q u f → CochainLift P Q u g → (appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map f = (appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map g


def chain_ab_homology_independentType : Prop :=
  ∀ (R : Type u) [Ring R]
    (F : ModuleCat.{max u v} R ⥤ AddCommGrpCat.{y}) [F.Additive]
    (A B : Type v) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : LeftResolution R A) (Q : LeftResolution R B) (_hP : P.IsProjective) (u : A →ₗ[R] B) (f g : P.complex ⟶ Q.complex) (n : ℕ),
    ChainLift P Q u f → ChainLift P Q u g → (appliedAbHomology F (ComplexShape.down ℕ) n).map f = (appliedAbHomology F (ComplexShape.down ℕ) n).map g

def chain_ab_contravariant_independentType : Prop :=
  ∀ (R : Type u) [Ring R]
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ AddCommGrpCat.{y}) [F.Additive]
    (A B : Type v) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : LeftResolution R A) (Q : LeftResolution R B) (_hP : P.IsProjective) (u : A →ₗ[R] B) (f g : P.complex ⟶ Q.complex) (n : ℕ),
    ChainLift P Q u f → ChainLift P Q u g → (appliedAbContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map f = (appliedAbContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map g

def cochain_ab_homology_independentType : Prop :=
  ∀ (R : Type u) [Ring R]
    (F : ModuleCat.{max u v} R ⥤ AddCommGrpCat.{y}) [F.Additive]
    (A B : Type v) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : RightResolution R A) (Q : InjectiveResolution R B) (u : A →ₗ[R] B) (f g : P.complex ⟶ Q.complex) (n : ℕ),
    CochainLift P Q u f → CochainLift P Q u g → (appliedAbHomology F (ComplexShape.up ℕ) n).map f = (appliedAbHomology F (ComplexShape.up ℕ) n).map g

def cochain_ab_contravariant_independentType : Prop :=
  ∀ (R : Type u) [Ring R]
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ AddCommGrpCat.{y}) [F.Additive]
    (A B : Type v) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : RightResolution R A) (Q : InjectiveResolution R B) (u : A →ₗ[R] B) (f g : P.complex ⟶ Q.complex) (n : ℕ),
    CochainLift P Q u f → CochainLift P Q u g → (appliedAbContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map f = (appliedAbContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map g

end
end P103.Specs.Ch10.Comparison
