import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DegreeOneExtensionClasses
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ExtBoundarySigns
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ExtInjectiveHorseshoe
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.Algebra.Group.TransferInstance

/-!
HA-R13, full degree-one classification. Complete a derived morphism to a
triangle; extension closure of both standard aisles puts its middle object
in the heart. Degree-zero cohomology recovers a short exact extension.
Full faithfulness of stalks and the triangle morphism axiom identify equal
boundaries precisely with endpoint-fixing equivalence. Naturality for the
two projections of a direct sum proves geometric Baer addition.
-/

set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
universe w v u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Specs.AdvancedHomologicalAlgebra.DegreeOneExtensionClasses

namespace AdvancedHomologicalAlgebra.DegreeOneExtensionClasses
variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [HasDerivedCategory.{w} 𝒜]
variable {A A' C C' : 𝒜}
local notation "J" => _root_.DerivedCategory.singleFunctor 𝒜 0

lemma boundary_naturality (E : Extension A C) (F : Extension A' C')
    (a : A ⟶ A') (b : E.B ⟶ F.B) (c : C ⟶ C')
    (hi : E.i ≫ b = a ≫ F.i) (hp : E.p ≫ c = b ≫ F.p) :
    E.boundary ≫ ((J).map a)⟦(1 : ℤ)⟧' = (J).map c ≫ F.boundary := by
  exact (ShortComplex.ShortExact.singleTriangle.map E.shortExact F.shortExact
    (ShortComplex.Hom.mk a b c hi.symm hp.symm)).comm₃

lemma boundary_eq_of_equivalent (E F : Extension A C) (h : E.Equivalent F) :
    E.boundary = F.boundary := by
  obtain ⟨b, hi, hp⟩ := h
  simpa using boundary_naturality E F (𝟙 A) b.hom (𝟙 C)
    (by simpa using hi) (by simpa using hp.symm)

lemma equivalent_of_boundary_eq (E F : Extension A C) (h : E.boundary = F.boundary) :
    E.Equivalent F := by
  obtain ⟨b, hi, hp⟩ := complete_distinguished_triangle_morphism₂
    E.shortExact.singleTriangle F.shortExact.singleTriangle
    E.shortExact.singleTriangle_distinguished F.shortExact.singleTriangle_distinguished
    (𝟙 _) (𝟙 _) (by simpa using h)
  obtain ⟨b, rfl⟩ := (J).map_surjective b
  have hi' : E.i ≫ b = F.i := (J).map_injective (by simpa using hi)
  have hp' : b ≫ F.p = E.p := (J).map_injective (by simpa using hp.symm)
  let f : E.sequence ⟶ F.sequence :=
    ShortComplex.Hom.mk (𝟙 _) b (𝟙 _) (by simpa using hi'.symm) (by simpa using hp')
  have : IsIso b := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ f E.shortExact F.shortExact
  exact ⟨asIso b, hi', hp'⟩

lemma boundary_push (E : Extension A C) (a : A ⟶ A') :
    (E.push a).boundary = E.boundary ≫ ((J).map a)⟦(1 : ℤ)⟧' := by
  symm
  simpa using boundary_naturality E (E.push a) a (pushout.inl E.i a) (𝟙 C)
    (by simpa [Extension.push] using pushout.condition (f := E.i) (g := a)) (by simp [Extension.push])

lemma boundary_pull (E : Extension A C) (c : C' ⟶ C) :
    (E.pull c).boundary = (J).map c ≫ E.boundary := by
  simpa using boundary_naturality (E.pull c) E (𝟙 A) (pullback.snd c E.p) c
    (by simp [Extension.pull]) (by simpa [Extension.pull] using pullback.condition (f := c) (g := E.p))

theorem naturality : naturalityType := by
  intro 𝒜 _ _ _ A A' C C' a c E
  rw [boundary_pull, boundary_push]

theorem positive_projection : positiveProjectionType := by
  intro 𝒜 _ _ _ A C E
  exact ExtBoundarySigns.positive_projection 𝒜 _
    (E.shortExact.map_of_exact (CochainComplex.singleFunctor 𝒜 0))

lemma boundary_baer (E F : Extension A C) :
    (E.baer F).boundary = E.boundary + F.boundary := by
  have h₁ := boundary_naturality (E.directSum F) E
    (biprod.fst : A ⊞ A ⟶ A) (biprod.fst : E.B ⊞ F.B ⟶ E.B)
    (biprod.fst : C ⊞ C ⟶ C)
    (by simp [Extension.directSum]) (by simp [Extension.directSum])
  have h₂ := boundary_naturality (E.directSum F) F
    (biprod.snd : A ⊞ A ⟶ A) (biprod.snd : E.B ⊞ F.B ⟶ F.B)
    (biprod.snd : C ⊞ C ⟶ C)
    (by simp [Extension.directSum]) (by simp [Extension.directSum])
  have hc : (biprod.desc (𝟙 A) (𝟙 A) : A ⊞ A ⟶ A) =
      biprod.fst + biprod.snd := by
    apply biprod.hom_ext' <;> simp
  dsimp only [Extension.baer]
  rw [boundary_push, boundary_pull, hc]
  simp only [Functor.map_add, Preadditive.comp_add, Category.assoc]
  rw [h₁, h₂]
  simp [← Functor.map_comp_assoc]

theorem baer_sum : baerType := by
  intro 𝒜 _ _ _ A C E F
  exact boundary_baer E F

/-- A triangle of stalks recovers an ordinary short exact sequence. -/
lemma shortExact_of_distinguished {B : 𝒜} (i : A ⟶ B) (p : B ⟶ C)
    (z : i ≫ p = 0) (h : (J).obj C ⟶ ((J).obj A)⟦(1 : ℤ)⟧)
    (ht : Triangle.mk ((J).map i) ((J).map p) h ∈ distTriang _) :
    (ShortComplex.mk i p z).ShortExact := by
  let T := Triangle.mk ((J).map i) ((J).map p) h
  let S := ShortComplex.mk i p z
  let H := _root_.DerivedCategory.homologyFunctor 𝒜 0
  have hm : Mono (H.map T.mor₁) :=
    (_root_.DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      T ht (-1) 0 (by omega)).mpr
        ((_root_.DerivedCategory.isZero_of_isGE ((J).obj C) 0 (-1) (by omega)).eq_of_src _ _)
  have he : Epi (H.map T.mor₂) :=
    (_root_.DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
      T ht 0 1 rfl).mpr
        ((_root_.DerivedCategory.isZero_of_isLE ((J).obj A) 0 1 (by omega)).eq_of_tgt _ _)
  have hs : (S.map ((J) ⋙ H)).ShortExact :=
    { exact := _root_.DerivedCategory.HomologySequence.exact₂ T ht 0
      mono_f := hm
      epi_g := he }
  exact ShortComplex.shortExact_of_iso
    (S.mapNatIso (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso 𝒜 0)) hs

/-- The closing arrow of a distinguished triangle of a short exact sequence
is its canonical boundary. -/
lemma boundary_unique (E : Extension A C)
    (h : (J).obj C ⟶ ((J).obj A)⟦(1 : ℤ)⟧)
    (ht : Triangle.mk ((J).map E.i) ((J).map E.p) h ∈ distTriang _) :
    E.boundary = h := by
  obtain ⟨c, hp, hh⟩ := complete_distinguished_triangle_morphism
    E.shortExact.singleTriangle _ E.shortExact.singleTriangle_distinguished ht
    (𝟙 _) (𝟙 _) (by simp)
  obtain ⟨c, rfl⟩ := (J).map_surjective c
  have hc : E.p ≫ c = E.p := (J).map_injective (by simpa using hp)
  have := E.shortExact.epi_g
  have hc' : c = 𝟙 C := by
    apply (cancel_epi E.p).mp
    simpa using hc
  simpa [hc'] using hh

lemma boundary_surjective (h : (J).obj C ⟶ ((J).obj A)⟦(1 : ℤ)⟧) :
    ∃ E : Extension A C, E.boundary = h := by
  obtain ⟨B, i, p, ht⟩ := distinguished_cocone_triangle₂ h
  have hle := _root_.DerivedCategory.TStructure.t.isLE₂
    (Triangle.mk i p h) ht 0 (by change ((J).obj A).IsLE 0; infer_instance)
      (by change ((J).obj C).IsLE 0; infer_instance)
  have hge := _root_.DerivedCategory.TStructure.t.isGE₂
    (Triangle.mk i p h) ht 0 (by change ((J).obj A).IsGE 0; infer_instance)
      (by change ((J).obj C).IsGE 0; infer_instance)
  have : B.IsLE 0 := hle
  have : B.IsGE 0 := hge
  obtain ⟨B₀, ⟨e⟩⟩ :=
    _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE B 0
  obtain ⟨i₀, hi⟩ := (J).map_surjective (i ≫ e.hom)
  obtain ⟨p₀, hp⟩ := (J).map_surjective (e.inv ≫ p)
  have ht₀ : Triangle.mk ((J).map i₀) ((J).map p₀) h ∈ distTriang _ :=
    isomorphic_distinguished _ ht _
      (Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)
        (by simp [hi]) (by simp [hp]) (by simp))
  have hz : i₀ ≫ p₀ = 0 := (J).map_injective (by
    simpa using comp_distTriang_mor_zero₁₂ _ ht₀)
  let E : Extension A C := ⟨B₀, i₀, p₀, hz, shortExact_of_distinguished i₀ p₀ hz h ht₀⟩
  exact ⟨E, boundary_unique E h ht₀⟩

/-- The quotient by endpoint-fixing equivalence is classified by the boundary. -/
theorem classification : classificationType := by
  intro 𝒜 _ _ _ A C
  let f : ExtensionClasses A C →
      ((_root_.DerivedCategory.singleFunctor 𝒜 0).obj C ⟶ ((_root_.DerivedCategory.singleFunctor 𝒜 0).obj A)⟦(1 : ℤ)⟧) :=
    Quotient.lift (fun E => E.boundary) (boundary_eq_of_equivalent)
  have hinj : Function.Injective f := by
    intro x y
    induction x using Quotient.inductionOn with | _ E =>
      induction y using Quotient.inductionOn with | _ F =>
        intro h
        exact Quotient.sound (equivalent_of_boundary_eq E F h)
  have hsurj : Function.Surjective f := by
    intro h
    obtain ⟨E, hE⟩ := boundary_surjective h
    exact ⟨⟦E⟧, hE⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun E => rfl⟩

/-- The transported group law is the geometric Baer operation on representatives. -/
theorem baer_classification : baerClassificationType := by
  intro 𝒜 _ _ _ A C
  obtain ⟨e, he⟩ := classification 𝒜 A C
  refine ⟨e.addCommGroup, ?_⟩
  let := e.addCommGroup
  refine ⟨e.addEquiv, he, ?_⟩
  intro E F
  apply e.injective
  change e (e.symm (e ⟦E⟧ + e ⟦F⟧)) = e ⟦E.baer F⟧
  rw [e.apply_symm_apply, he, he, he, boundary_baer]

/-- Second-variable triangle boundary, retained with its shift comparison. -/
theorem triangle_second :
    Specs.AdvancedHomologicalAlgebra.ExtBoundarySigns.triangleSecondType :=
  ExtBoundarySigns.triangle_second

/-- First-variable triangle boundary. -/
theorem triangle_first :
    Specs.AdvancedHomologicalAlgebra.ExtBoundarySigns.triangleFirstType :=
  ExtBoundarySigns.triangle_first

/-- Ordinary first-variable injective Hom boundary, including (-1)^(n+1). -/
theorem ordinary_first :
    Specs.AdvancedHomologicalAlgebra.ExtBoundarySigns.ordinaryFirstType :=
  ExtBoundarySigns.ordinary_first

/-- Ordinary second-variable injective Hom boundary on cocycle representatives. -/
theorem ordinary_second :
    Specs.AdvancedHomologicalAlgebra.ExtBoundarySigns.ordinarySecondType :=
  ExtBoundarySigns.ordinary_second

open Specs.AdvancedHomologicalAlgebra.ExtInjectiveHorseshoe in
open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom in
/-- Given the endpoint injective resolutions, there is a compatible horseshoe
whose ordinary Hom connector agrees with the derived second-variable boundary. -/
theorem exists_ordinary_second_connector (S : ShortComplex 𝒜) (hS : S.ShortExact)
    (I₁ I₃ : CochainComplex 𝒜 ℤ) (i : Stalk S.X₁ ⟶ I₁) (j : Stalk S.X₃ ⟶ I₃)
    (hi : QuasiIso i) (hj : QuasiIso j) (hI : BoundedInjective I₁) (hJ : BoundedInjective I₃) :
    ∃ R : ResolvingRow S i j, R.IsHorseshoe ∧
      ∀ (X : 𝒜) (n : ℤ), ∃! d : HomClass X I₃ n →+ HomClass X I₁ (n+1),
        IsOrdinaryConnector R.row X n d ∧ ∀ x : HomClass X I₃ n,
          injectiveClassMap X S.X₁ I₁ i hi (n+1) (d x) =
            ShiftedHom.comp (injectiveClassMap X S.X₃ I₃ j hj n x) hS.singleδ (add_comm 1 n) := by
  obtain ⟨R, hR⟩ := ExtInjectiveHorseshoe.exists_horseshoe 𝒜 S hS I₁ I₃ i j hi hj hI hJ
  refine ⟨R, hR, ?_⟩
  intro X n
  have hT := hR.1
  have hsplit := hR.2.2.2
  obtain ⟨d, hd, huniq⟩ := ExtInjectiveHorseshoe.ordinary_connector 𝒜 R.row hT hsplit X n
  refine ⟨d, ⟨hd, ?_⟩, fun d' hd' => huniq d' hd'.1⟩
  exact ExtInjectiveHorseshoe.connector_comparison 𝒜 S hS I₁ I₃ i j hi hj R hT hsplit X n d hd

end AdvancedHomologicalAlgebra.DegreeOneExtensionClasses
