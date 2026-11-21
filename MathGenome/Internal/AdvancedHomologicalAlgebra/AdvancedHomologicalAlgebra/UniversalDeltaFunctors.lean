import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ClassicalDerivedValues

noncomputable section
set_option linter.checkUnivs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors

namespace AdvancedHomologicalAlgebra.UniversalDeltaFunctors

lemma cohomologicalMorphism_ext {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] {T U : CohomologicalSystem A B}
    {φ ψ : CohomologicalMorphism T U} (h : φ.component = ψ.component) : φ = ψ := by
  cases φ
  cases ψ
  cases h
  rfl

section Effaceable
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [EnoughInjectives A]

/-- The chosen dimension-shifting short exact sequence. -/
abbrev injectiveSequence (X : A) : ShortComplex A :=
  ShortComplex.mk (Injective.ι X) (cokernel.π (Injective.ι X)) (by simp)

lemma injectiveSequence_shortExact (X : A) : (injectiveSequence X).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := by change Mono (Injective.ι X); infer_instance
  epi_g := by change Epi (cokernel.π (Injective.ι X)); infer_instance

/-- A short exact sequence maps to the chosen injective sequence on its
first object, by extending the embedding across its middle object. -/
def toInjectiveSequence {S : ShortComplex A} (hS : S.ShortExact) :
    S ⟶ injectiveSequence S.X₁ := by
  letI := hS.mono_f
  letI := hS.epi_g
  let b := Injective.factorThru (Injective.ι S.X₁) S.f
  have hb : S.f ≫ b = Injective.ι S.X₁ := Injective.comp_factorThru _ _
  let c := hS.exact.desc (b ≫ cokernel.π (Injective.ι S.X₁)) (by rw [← Category.assoc, hb]; simp)
  exact { τ₁ := 𝟙 _
          τ₂ := b
          τ₃ := c
          comm₁₂ := by simpa [injectiveSequence] using hb.symm
          comm₂₃ := by dsimp [c, injectiveSequence]; simp }

/-- A morphism extends between the chosen injective presentations. -/
def injectiveSequenceMap {X Y : A} (f : X ⟶ Y) :
    injectiveSequence X ⟶ injectiveSequence Y := by
  let b := Injective.factorThru (f ≫ Injective.ι Y) (Injective.ι X)
  have hb : Injective.ι X ≫ b = f ≫ Injective.ι Y := Injective.comp_factorThru _ _
  exact { τ₁ := f
          τ₂ := b
          τ₃ := cokernel.desc (Injective.ι X) (b ≫ cokernel.π (Injective.ι Y))
            (by rw [← Category.assoc, hb, Category.assoc]; simp)
          comm₁₂ := hb.symm
          comm₂₃ := by simp [injectiveSequence] }

variable (T U : CohomologicalSystem A B) (hT : IsCohomological T)
  (hU : IsCohomological U)
  (vanish : ∀ (I : A) [Injective I] (n : ℕ), IsZero ((T.value (n + 1)).obj I))

include hT vanish in
lemma dimensionShift_epi (X : A) (n : ℕ) :
    Epi (T.δ (injectiveSequence_shortExact X) n) := by
  let e := hT.exact₁ (injectiveSequence_shortExact X) n
  apply e.exact.epi_f_iff.mpr
  exact (vanish (Injective.under X) n).eq_of_tgt _ _

/-- The unique next component forced by the connecting epimorphism. -/
def nextComponent (n : ℕ) (α : T.value n ⟶ U.value n) (X : A) :
    (T.value (n + 1)).obj X ⟶ (U.value (n + 1)).obj X := by
  letI := dimensionShift_epi T hT vanish X n
  exact (hT.exact₃ (injectiveSequence_shortExact X) n).exact.desc
    (α.app _ ≫ U.δ (injectiveSequence_shortExact X) n) (by
      rw [← Category.assoc, α.naturality, Category.assoc,
        (hU.exact₃ (injectiveSequence_shortExact X) n).zero, comp_zero])

@[reassoc]
lemma nextComponent_fac (n : ℕ) (α : T.value n ⟶ U.value n) (X : A) :
    T.δ (injectiveSequence_shortExact X) n ≫ nextComponent T U hT hU vanish n α X =
      α.app _ ≫ U.δ (injectiveSequence_shortExact X) n := by
  letI := dimensionShift_epi T hT vanish X n
  unfold nextComponent
  exact (hT.exact₃ (injectiveSequence_shortExact X) n).exact.g_desc _ _

/-- Compatibility with every boundary follows from mapping its sequence to
the chosen presentation, without any dependence on the choice of extension. -/
lemma nextComponent_comm (n : ℕ) (α : T.value n ⟶ U.value n)
    {S : ShortComplex A} (hS : S.ShortExact) :
    T.δ hS n ≫ nextComponent T U hT hU vanish n α S.X₁ = α.app _ ≫ U.δ hS n := by
  let f := toInjectiveSequence hS
  have ht := hT.naturality hS (injectiveSequence_shortExact S.X₁) f n
  have hu := hU.naturality hS (injectiveSequence_shortExact S.X₁) f n
  have hf : f.τ₁ = 𝟙 _ := rfl
  rw [hf, CategoryTheory.Functor.map_id, Category.comp_id] at ht hu
  rw [← ht, Category.assoc, nextComponent_fac, ← Category.assoc, α.naturality,
    Category.assoc, hu]

/-- Naturality is tested after the epic dimension-shifting boundary. -/
def nextTransformation (n : ℕ) (α : T.value n ⟶ U.value n) :
    T.value (n + 1) ⟶ U.value (n + 1) where
  app := nextComponent T U hT hU vanish n α
  naturality {X Y} f := by
    let e := injectiveSequenceMap f
    letI := dimensionShift_epi T hT vanish X n
    apply (cancel_epi (T.δ (injectiveSequence_shortExact X) n)).mp
    have ht := hT.naturality (injectiveSequence_shortExact X)
      (injectiveSequence_shortExact Y) e n
    have hu := hU.naturality (injectiveSequence_shortExact X)
      (injectiveSequence_shortExact Y) e n
    change _ = _ at ht hu
    dsimp only [e, injectiveSequenceMap] at ht hu
    rw [← Category.assoc, ← ht, Category.assoc, nextComponent_fac,
      ← Category.assoc, α.naturality, Category.assoc, hu]
    simp only [nextComponent_fac_assoc]

include hT vanish in
/-- A system vanishing on injectives is universal, by dimension shifting. -/
theorem universal_of_injective_vanishing : IsUniversalCohomological T := by
  intro U hU α
  let a : ∀ n, T.value n ⟶ U.value n := fun n =>
    Nat.rec α (fun n a => nextTransformation T U hT hU vanish n a) n
  let φ : CohomologicalMorphism T U :=
    { component := a, comm := fun hS n => nextComponent_comm T U hT hU vanish n (a n) hS }
  refine ⟨φ, rfl, ?_⟩
  intro ψ hψ
  have he : ∀ n, ψ.component n = φ.component n := by
    intro n
    induction n with
    | zero => exact hψ
    | succ n ih =>
      ext X
      letI := dimensionShift_epi T hT vanish X n
      apply (cancel_epi (T.δ (injectiveSequence_shortExact X) n)).mp
      rw [ψ.comm, φ.comm, ih]
  exact cohomologicalMorphism_ext (funext he)

end Effaceable

lemma homologicalMorphism_ext {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] {T U : HomologicalSystem A B}
    {φ ψ : HomologicalMorphism T U} (h : φ.component = ψ.component) : φ = ψ := by
  cases φ
  cases ψ
  cases h
  rfl

section Coeffaceable
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [EnoughProjectives A]

/-- The projective dimension-shifting sequence. -/
abbrev projectiveSequence (X : A) : ShortComplex A :=
  ShortComplex.mk (kernel.ι (Projective.π X)) (Projective.π X) (by simp)

lemma projectiveSequence_shortExact (X : A) : (projectiveSequence X).ShortExact where
  exact := ShortComplex.exact_kernel _

/-- A projective presentation maps to any SES ending in its last object. -/
def fromProjectiveSequence {S : ShortComplex A} (hS : S.ShortExact) :
    projectiveSequence S.X₃ ⟶ S := by
  letI := hS.mono_f
  letI := hS.epi_g
  let b := Projective.factorThru (Projective.π S.X₃) S.g
  have hb : b ≫ S.g = Projective.π S.X₃ := Projective.factorThru_comp _ _
  let a := hS.exact.lift (kernel.ι (Projective.π S.X₃) ≫ b)
    (by rw [Category.assoc, hb]; simp)
  exact { τ₁ := a
          τ₂ := b
          τ₃ := 𝟙 _
          comm₁₂ := by dsimp [a]; simp
          comm₂₃ := by simpa using hb }

/-- A morphism lifts between chosen projective presentations. -/
def projectiveSequenceMap {X Y : A} (f : X ⟶ Y) :
    projectiveSequence X ⟶ projectiveSequence Y := by
  let b := Projective.factorThru (Projective.π X ≫ f) (Projective.π Y)
  have hb : b ≫ Projective.π Y = Projective.π X ≫ f := Projective.factorThru_comp _ _
  exact { τ₁ := kernel.lift (Projective.π Y) (kernel.ι (Projective.π X) ≫ b)
            (by rw [Category.assoc, hb, ← Category.assoc]; simp)
          τ₂ := b
          τ₃ := f
          comm₁₂ := by simp
          comm₂₃ := hb }

variable (T U : HomologicalSystem A B) (hT : IsHomological T)
  (hU : IsHomological U)
  (vanish : ∀ (P : A) [Projective P] (n : ℕ), IsZero ((T.value (n + 1)).obj P))

include hT vanish in
lemma dimensionShift_mono (X : A) (n : ℕ) :
    Mono (T.δ (projectiveSequence_shortExact X) n) := by
  let e := hT.exact₃ (projectiveSequence_shortExact X) n
  apply e.exact.mono_g_iff.mpr
  exact (vanish (Projective.over X) n).eq_of_src _ _

/-- The next map into the derived system is forced by the connecting monomorphism. -/
def nextHomologicalComponent (n : ℕ) (α : U.value n ⟶ T.value n) (X : A) :
    (U.value (n + 1)).obj X ⟶ (T.value (n + 1)).obj X := by
  letI := dimensionShift_mono T hT vanish X n
  exact (hT.exact₁ (projectiveSequence_shortExact X) n).exact.lift
    (U.δ (projectiveSequence_shortExact X) n ≫ α.app _) (by
      rw [Category.assoc, ← α.naturality, ← Category.assoc,
        (hU.exact₁ (projectiveSequence_shortExact X) n).zero, zero_comp])

@[reassoc]
lemma nextHomologicalComponent_fac (n : ℕ) (α : U.value n ⟶ T.value n) (X : A) :
    nextHomologicalComponent T U hT hU vanish n α X ≫ T.δ (projectiveSequence_shortExact X) n =
      U.δ (projectiveSequence_shortExact X) n ≫ α.app _ := by
  letI := dimensionShift_mono T hT vanish X n
  unfold nextHomologicalComponent
  exact (hT.exact₁ (projectiveSequence_shortExact X) n).exact.lift_f _ _

lemma nextHomologicalComponent_comm (n : ℕ) (α : U.value n ⟶ T.value n)
    {S : ShortComplex A} (hS : S.ShortExact) :
    U.δ hS n ≫ α.app S.X₁ = nextHomologicalComponent T U hT hU vanish n α S.X₃ ≫ T.δ hS n := by
  let f := fromProjectiveSequence hS
  have ht := hT.naturality (projectiveSequence_shortExact S.X₃) hS f n
  have hu := hU.naturality (projectiveSequence_shortExact S.X₃) hS f n
  have hf : f.τ₃ = 𝟙 _ := rfl
  rw [hf, CategoryTheory.Functor.map_id, Category.id_comp] at ht hu
  rw [ht, ← Category.assoc, nextHomologicalComponent_fac, Category.assoc,
    ← α.naturality, ← Category.assoc, ← hu]

def nextHomologicalTransformation (n : ℕ) (α : U.value n ⟶ T.value n) :
    U.value (n + 1) ⟶ T.value (n + 1) where
  app := nextHomologicalComponent T U hT hU vanish n α
  naturality {X Y} f := by
    let e := projectiveSequenceMap f
    letI := dimensionShift_mono T hT vanish Y n
    apply (cancel_mono (T.δ (projectiveSequence_shortExact Y) n)).mp
    have ht := hT.naturality (projectiveSequence_shortExact X)
      (projectiveSequence_shortExact Y) e n
    have hu := hU.naturality (projectiveSequence_shortExact X)
      (projectiveSequence_shortExact Y) e n
    dsimp only [e, projectiveSequenceMap] at ht hu
    rw [Category.assoc, nextHomologicalComponent_fac, ← Category.assoc, hu,
      Category.assoc, α.naturality]
    rw [Category.assoc, ht]
    simp only [← Category.assoc, nextHomologicalComponent_fac]

include hT vanish in
/-- Projective vanishing gives the terminal homological universal property. -/
theorem universal_of_projective_vanishing : IsUniversalHomological T := by
  intro U hU α
  let a : ∀ n, U.value n ⟶ T.value n := fun n =>
    Nat.rec α (fun n a => nextHomologicalTransformation T U hT hU vanish n a) n
  let φ : HomologicalMorphism U T :=
    { component := a, comm := fun hS n => nextHomologicalComponent_comm T U hT hU vanish n (a n) hS }
  refine ⟨φ, rfl, ?_⟩
  intro ψ hψ
  have he : ∀ n, ψ.component n = φ.component n := by
    intro n
    induction n with
    | zero => exact hψ
    | succ n ih =>
      ext X
      letI := dimensionShift_mono T hT vanish X n
      apply (cancel_mono (T.δ (projectiveSequence_shortExact X) n)).mp
      rw [← ψ.comm (projectiveSequence_shortExact X) n,
        ← φ.comm (projectiveSequence_shortExact X) n, ih]
  exact homologicalMorphism_ext (funext he)

end Coeffaceable

/-- The same injective embedding effaces every positive degree. -/
theorem rightEffacement : rightEffacementType.{u, v, u', v', w, w'} := by
  intro A B _ _ _ _ _ _ _ F _ X
  refine ⟨Injective.under X, Injective.ι X, inferInstance, inferInstance, ?_⟩
  intro n
  exact (ClassicalDerivedValues.rightInjectiveVanishing A B F (Injective.under X) n).eq_of_tgt _ _

theorem leftEffacement : leftEffacementType.{u, v, u', v', w, w'} := by
  intro A B _ _ _ _ _ _ _ hA hB F _ R X
  refine ⟨Projective.over X, Projective.π X, inferInstance, inferInstance, ?_⟩
  intro n
  exact (ClassicalDerivedValues.leftProjectiveVanishing A B hA hB F R
    (Projective.over X) n).eq_of_src _ _

section RightDelta
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive]

lemma right_exact₁ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    ExactPair (rightBoundary F hS n) ((rightValue F (n + 1)).map S.f) := by
  let H := DerivedCategory.Plus.homologyFunctor B 0
  let T := F.rightDerivedFunctorPlus.mapTriangle.obj (plusTriangle A hS)
  have hT : T ∈ distTriang (DerivedCategory.Plus B) :=
    F.rightDerivedFunctorPlus.map_distinguished _ (ClassicalDerivedValues.plusTriangle_distinguished hS)
  exact ⟨H.homologySequenceδ_comp T hT (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega),
    H.homologySequence_exact₁ T hT (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)⟩

lemma right_exact₂ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    ExactPair ((rightValue F n).map S.f) ((rightValue F n).map S.g) := by
  let H := DerivedCategory.Plus.homologyFunctor B 0
  let T := F.rightDerivedFunctorPlus.mapTriangle.obj (plusTriangle A hS)
  have hT : T ∈ distTriang (DerivedCategory.Plus B) :=
    F.rightDerivedFunctorPlus.map_distinguished _ (ClassicalDerivedValues.plusTriangle_distinguished hS)
  exact ⟨H.homologySequence_comp T hT (n : ℤ), H.homologySequence_exact₂ T hT (n : ℤ)⟩

lemma right_exact₃ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    ExactPair ((rightValue F n).map S.g) (rightBoundary F hS n) := by
  let H := DerivedCategory.Plus.homologyFunctor B 0
  let T := F.rightDerivedFunctorPlus.mapTriangle.obj (plusTriangle A hS)
  have hT : T ∈ distTriang (DerivedCategory.Plus B) :=
    F.rightDerivedFunctorPlus.map_distinguished _ (ClassicalDerivedValues.plusTriangle_distinguished hS)
  exact ⟨H.comp_homologySequenceδ T hT (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega),
    H.homologySequence_exact₃ T hT (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)⟩

lemma right_mono_zero [PreservesFiniteLimits F] {S : ShortComplex A} (hS : S.ShortExact) :
    Mono ((rightValue F 0).map S.f) := by
  letI := hS.mono_f
  letI := ClassicalDerivedValues.rightZero A B F
  let e := inv (rightDegreeZeroUnit F)
  have hm : Mono ((rightValue F 0).map S.f ≫ e.app S.X₂) := by
    rw [e.naturality]
    infer_instance
  exact mono_of_mono ((rightValue F 0).map S.f) (e.app S.X₂)

end RightDelta

theorem rightDelta : rightDeltaType.{u, v, u', v', w, w'} := by
  intro A B _ _ _ _ _ _ _ F _ _
  exact {
    additive := fun n => by dsimp [rightSystem, rightValue]; infer_instance
    naturality := fun hS hT f n => ClassicalDerivedValues.rightConnectingNatural A B F _ _ hS hT f n
    exact₁ := right_exact₁ F
    exact₂ := right_exact₂ F
    exact₃ := right_exact₃ F
    mono_zero := right_mono_zero F }

theorem rightUniversal : rightUniversalType.{u, v, u', v', w, w'} := by
  intro A B _ _ _ _ _ _ _ F _ _ U hU α
  let unit : F ⟶ (rightSystem F).value 0 := rightDegreeZeroUnit F
  letI : IsIso unit := ClassicalDerivedValues.rightZero A B F
  obtain ⟨φ, hφ, huniq⟩ :=
    universal_of_injective_vanishing (rightSystem F) (rightDelta A B F)
      (fun I _ n => ClassicalDerivedValues.rightInjectiveVanishing A B F I n)
      U hU (inv unit ≫ α)
  refine ⟨φ, ?_, ?_⟩
  · change unit ≫ φ.component 0 = α
    rw [hφ, IsIso.hom_inv_id_assoc]
  · intro ψ hψ
    change unit ≫ ψ.component 0 = α at hψ
    apply huniq ψ
    apply (cancel_epi unit).mp
    rw [hψ, IsIso.hom_inv_id_assoc]

section LeftDelta
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} B] [(minus A).IsTriangulated] [(minus B).IsTriangulated]
  (F : A ⥤ B) [F.Additive] (R : ExactLeftData.{u, v, u', v', w, w'} F)

lemma left_exact₁ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    ExactPair (leftBoundary F R hS n) ((leftValue F R n).map S.f) := by
  letI := R.commShift
  letI := R.triangulated
  let H := DerivedCategory.homologyFunctor B 0
  let T := (R.functor ⋙ DerivedCategory.Minus.ι).mapTriangle.obj (minusTriangle A hS)
  have hT : T ∈ distTriang (DerivedCategory B) :=
    (R.functor ⋙ DerivedCategory.Minus.ι).map_distinguished _
      (ClassicalDerivedValues.minusTriangle_distinguished hS)
  exact ⟨H.homologySequenceδ_comp T hT (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega),
    H.homologySequence_exact₁ T hT (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)⟩

lemma left_exact₂ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    ExactPair ((leftValue F R n).map S.f) ((leftValue F R n).map S.g) := by
  letI := R.commShift
  letI := R.triangulated
  let H := DerivedCategory.homologyFunctor B 0
  let T := (R.functor ⋙ DerivedCategory.Minus.ι).mapTriangle.obj (minusTriangle A hS)
  have hT : T ∈ distTriang (DerivedCategory B) :=
    (R.functor ⋙ DerivedCategory.Minus.ι).map_distinguished _
      (ClassicalDerivedValues.minusTriangle_distinguished hS)
  exact ⟨H.homologySequence_comp T hT (-(n : ℤ)), H.homologySequence_exact₂ T hT (-(n : ℤ))⟩

lemma left_exact₃ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    ExactPair ((leftValue F R (n + 1)).map S.g) (leftBoundary F R hS n) := by
  letI := R.commShift
  letI := R.triangulated
  let H := DerivedCategory.homologyFunctor B 0
  let T := (R.functor ⋙ DerivedCategory.Minus.ι).mapTriangle.obj (minusTriangle A hS)
  have hT : T ∈ distTriang (DerivedCategory B) :=
    (R.functor ⋙ DerivedCategory.Minus.ι).map_distinguished _
      (ClassicalDerivedValues.minusTriangle_distinguished hS)
  exact ⟨H.comp_homologySequenceδ T hT (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega),
    H.homologySequence_exact₃ T hT (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)⟩

lemma left_epi_zero [EnoughProjectives A] [PreservesFiniteColimits F]
    {S : ShortComplex A} (hS : S.ShortExact) : Epi ((leftValue F R 0).map S.g) := by
  letI := hS.epi_g
  letI := ClassicalDerivedValues.leftZero A B inferInstance inferInstance F R
  let e := inv (leftDegreeZeroCounit F R)
  have hm : Epi (e.app S.X₂ ≫ (leftValue F R 0).map S.g) := by
    rw [← e.naturality]
    infer_instance
  exact epi_of_epi (e.app S.X₂) ((leftValue F R 0).map S.g)

end LeftDelta

theorem leftDelta : leftDeltaType.{u, v, u', v', w, w'} := by
  intro A B _ _ _ _ _ _ _ hA hB F _ R _
  letI := R.commShift
  letI := R.triangulated
  exact {
    additive := fun n => by dsimp [leftSystem, leftValue, minusSingle]; infer_instance
    naturality := fun hS hT f n => ClassicalDerivedValues.leftConnectingNatural A B hA hB F R _ _ hS hT f n
    exact₁ := left_exact₁ F R
    exact₂ := left_exact₂ F R
    exact₃ := left_exact₃ F R
    epi_zero := left_epi_zero F R }

theorem leftUniversal : leftUniversalType.{u, v, u', v', w, w'} := by
  intro A B _ _ _ _ _ _ _ hA hB F _ R _ U hU α
  let counit : (leftSystem F R).value 0 ⟶ F := leftDegreeZeroCounit F R
  letI : IsIso counit := ClassicalDerivedValues.leftZero A B hA hB F R
  obtain ⟨φ, hφ, huniq⟩ :=
    universal_of_projective_vanishing (leftSystem F R) (leftDelta A B hA hB F R)
      (fun P _ n => ClassicalDerivedValues.leftProjectiveVanishing A B hA hB F R P n)
      U hU (α ≫ inv counit)
  refine ⟨φ, ?_, ?_⟩
  · change φ.component 0 ≫ counit = α
    rw [hφ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  · intro ψ hψ
    change ψ.component 0 ≫ counit = α at hψ
    apply huniq ψ
    apply (cancel_mono counit).mp
    rw [hψ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end AdvancedHomologicalAlgebra.UniversalDeltaFunctors
