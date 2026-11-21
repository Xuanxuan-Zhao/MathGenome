import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ExtBoundarySigns
import Mathlib.Algebra.Homology.ShortComplex.Pushout
import Mathlib.Algebra.Homology.ShortComplex.Pullback

/-! HA-R13, lines 2114–2179. Extensions have fixed endpoints in an arbitrary
abelian category. The chosen derived category exists in a sufficiently large
universe; no injective or projective hypothesis is imposed. -/
set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace Specs.AdvancedHomologicalAlgebra.DegreeOneExtensionClasses

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- A short exact extension of C by A, with its endpoints fixed. -/
structure Extension (A C : 𝒜) where
  B : 𝒜
  i : A ⟶ B
  p : B ⟶ C
  zero : i ≫ p = 0
  shortExact : (ShortComplex.mk i p zero).ShortExact

namespace Extension
variable {A A' C C' : 𝒜}
abbrev sequence (E : Extension A C) : ShortComplex 𝒜 := ShortComplex.mk E.i E.p E.zero

/-- Equivalence fixes both endpoints and is an isomorphism of middle objects. -/
def Equivalent (E F : Extension A C) : Prop :=
  ∃ b : E.B ≅ F.B, E.i ≫ b.hom = F.i ∧ b.hom ≫ F.p = E.p

instance extensionSetoid (A C : 𝒜) : Setoid (Extension A C) where
  r := Equivalent
  iseqv := ⟨fun E => ⟨Iso.refl _, by simp, by simp⟩,
    by
      rintro E F ⟨b, hi, hp⟩
      exact ⟨b.symm, by rw [← hi]; simp, by rw [← hp]; simp⟩,
    by
      rintro E F G ⟨b, hi, hp⟩ ⟨c, hj, hq⟩
      exact ⟨b ≪≫ c, by simpa [← Category.assoc, hi] using hj,
        by simpa [Category.assoc, hq] using hp⟩⟩

noncomputable def push (E : Extension A C) (a : A ⟶ A') : Extension A' C where
  B := (E.sequence.push a).X₂
  i := (E.sequence.push a).f
  p := (E.sequence.push a).g
  zero := (E.sequence.push a).zero
  shortExact := E.shortExact.push a

noncomputable def pull (E : Extension A C) (c : C' ⟶ C) : Extension A C' where
  B := (E.sequence.pull c).X₂
  i := (E.sequence.pull c).f
  p := (E.sequence.pull c).g
  zero := (E.sequence.pull c).zero
  shortExact := E.shortExact.pull c

/-- The termwise direct sum of extensions, before diagonal pullback and
codiagonal pushout. -/
noncomputable def directSum (E F : Extension A C) : Extension (A ⊞ A) (C ⊞ C) where
  B := E.B ⊞ F.B
  i := biprod.map E.i F.i
  p := biprod.map E.p F.p
  zero := by
    apply biprod.hom_ext <;> simp [Category.assoc, E.zero, F.zero]
  shortExact := by
    have := E.shortExact.mono_f
    have := F.shortExact.mono_f
    have := E.shortExact.epi_g
    have := F.shortExact.epi_g
    let S := ShortComplex.mk (biprod.map E.i F.i) (biprod.map E.p F.p)
      (by
        apply biprod.hom_ext <;> simp [Category.assoc, E.zero, F.zero])
    have hk : IsLimit (KernelFork.ofι S.f S.zero) := by
      apply Fork.IsLimit.mk'
      intro s
      have hs : s.ι ≫ biprod.map E.p F.p = 0 := KernelFork.condition s
      have h₁ : (s.ι ≫ biprod.fst) ≫ E.p = 0 := by
        simpa only [Category.assoc, biprod.map_fst, zero_comp] using
          congrArg (fun k => k ≫ biprod.fst) hs
      have h₂ : (s.ι ≫ biprod.snd) ≫ F.p = 0 := by
        simpa only [Category.assoc, biprod.map_snd, zero_comp] using
          congrArg (fun k => k ≫ biprod.snd) hs
      let l₁ := E.shortExact.exact.lift (s.ι ≫ biprod.fst) h₁
      let l₂ := F.shortExact.exact.lift (s.ι ≫ biprod.snd) h₂
      have hl₁ : l₁ ≫ E.i = s.ι ≫ biprod.fst := E.shortExact.exact.lift_f _ _
      have hl₂ : l₂ ≫ F.i = s.ι ≫ biprod.snd := F.shortExact.exact.lift_f _ _
      refine ⟨biprod.lift l₁ l₂, ?_, ?_⟩
      · apply biprod.hom_ext <;>
          simp [S, Category.assoc, hl₁, hl₂]
      · intro m hm
        apply biprod.hom_ext
        · apply (cancel_mono E.i).mp
          simpa [S, Category.assoc, hl₁] using
            congrArg (fun k => k ≫ biprod.fst) hm
        · apply (cancel_mono F.i).mp
          simpa [S, Category.assoc, hl₂] using
            congrArg (fun k => k ≫ biprod.snd) hm
    exact ⟨S.exact_of_f_is_kernel hk⟩

/-- Baer sum: direct sum, pullback by the diagonal of C, then pushout
by the codiagonal of A. This definition makes no reference to derived Hom. -/
noncomputable def baer (E F : Extension A C) : Extension A C :=
  (((E.directSum F).pull (biprod.lift (𝟙 C) (𝟙 C))).push
    (biprod.desc (𝟙 A) (𝟙 A)))

section Derived
variable [HasDerivedCategory.{w} 𝒜]
/-- The extension class uses the triangle boundary (negative cone projection). -/
noncomputable abbrev boundary (E : Extension A C) := E.shortExact.singleδ
end Derived
end Extension

abbrev ExtensionClasses (A C : 𝒜) := Quotient (Extension.extensionSetoid A C)

/-- Classification, with its value on every actual short exact extension specified. -/
def classificationType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
  [HasDerivedCategory.{w} 𝒜] (A C : 𝒜),
  ∃ e : ExtensionClasses A C ≃
    ((_root_.DerivedCategory.singleFunctor 𝒜 0).obj C ⟶
      ((_root_.DerivedCategory.singleFunctor 𝒜 0).obj A)⟦(1 : ℤ)⟧),
    ∀ E : Extension A C, e ⟦E⟧ = E.boundary

/-- On equivalence classes the geometric Baer operation is an abelian group
operation, and the boundary is an additive equivalence. -/
def baerClassificationType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
  [HasDerivedCategory.{w} 𝒜] (A C : 𝒜),
  ∃ g : AddCommGroup (ExtensionClasses A C),
    letI := g
    ∃ e : ExtensionClasses A C ≃+
      ((_root_.DerivedCategory.singleFunctor 𝒜 0).obj C ⟶
        ((_root_.DerivedCategory.singleFunctor 𝒜 0).obj A)⟦(1 : ℤ)⟧),
      (∀ E : Extension A C, e ⟦E⟧ = E.boundary) ∧
      (∀ E F : Extension A C, ((⟦E⟧ : ExtensionClasses A C) + (⟦F⟧ : ExtensionClasses A C)) = ⟦E.baer F⟧)

/-- Covariance in A and contravariance in C, by actual pushouts and pullbacks. -/
def naturalityType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
  [HasDerivedCategory.{w} 𝒜] (A A' C C' : 𝒜) (a : A ⟶ A') (c : C' ⟶ C)
  (E : Extension A C),
  ((E.push a).pull c).boundary =
    (_root_.DerivedCategory.singleFunctor 𝒜 0).map c ≫ E.boundary ≫
      ((_root_.DerivedCategory.singleFunctor 𝒜 0).map a)⟦(1 : ℤ)⟧'

/-- The geometric Baer construction corresponds to addition of derived morphisms. -/
def baerType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
  [HasDerivedCategory.{w} 𝒜] (A C : 𝒜) (E F : Extension A C),
    (E.baer F).boundary = E.boundary + F.boundary

/-- The positive-projection convention has the opposite extension class. -/
def positiveProjectionType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
  [HasDerivedCategory.{w} 𝒜] (A C : 𝒜) (E : Extension A C),
  let S := E.sequence.map (CochainComplex.singleFunctor 𝒜 0)
  letI := CochainComplex.mappingCone.quasiIso_descShortComplex
    (E.shortExact.map_of_exact (CochainComplex.singleFunctor 𝒜 0))
  inv (_root_.DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫
    _root_.DerivedCategory.Q.map
      (Specs.AdvancedHomologicalAlgebra.MappingCones.projectionToShift S.f) ≫
    (_root_.DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S.X₁ = -E.boundary

end Specs.AdvancedHomologicalAlgebra.DegreeOneExtensionClasses
