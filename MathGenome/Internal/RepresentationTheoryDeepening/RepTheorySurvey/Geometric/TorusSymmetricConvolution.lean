import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TorusSymmetricConvolution
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TorusOrderedConvolution
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TorusFusion
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Classical MonoidalCategory BraidedCategory

set_option backward.isDefEq.respectTransparency false

namespace RepTheorySurvey.Geometric.TorusSymmetricConvolution

open Analytic TorusPerverseSpecs TorusOrderedConvolutionSpecs TorusFusionSpecs
open TorusSymmetricConvolutionSpecs
open OrderedProduct (Stalk)
open private includeFiber includeFiber_cast includeFiber_naturality mapStalk mapStalk_id
  stalksFullyFaithful pointUnit_off_zero
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TorusOrderedConvolution

variable {r : ℕ} {D : OrderedGeometry r} {g : StageGeometry r} {c : ContinuousJets r}
variable (P : OrderedProduct D g c)
variable {V W X Y Z : Heart r g c}

local notation:70 V " ⋆ " W => P.convolution.obj (V, W)

private abbrev multiply {V' W' : Heart r g c} (f : V ⟶ V') (h : W ⟶ W') :
    (V ⋆ W) ⟶ (V' ⋆ W') :=
  P.convolution.map (X := (V, W)) (Y := (V', W')) (f, h)

private theorem mapStalk_comp (f : V ⟶ W) (h : W ⟶ X) (a : Labels r) :
    mapStalk (f ≫ h) a = mapStalk f a ≫ mapStalk h a := by
  simp [mapStalk]

private theorem eq_of_stalks (f h : V ⟶ W)
    (hh : ∀ a : Labels r, mapStalk f a = mapStalk h a) : f = h := by
  apply (stalksFullyFaithful r g c).map_injective
  apply NatTrans.ext
  funext a
  exact hh a.as

private structure StalkPiece (V : Heart r g c) where
  weight : Labels r
  coeff : Coeff.{0}
  incl : coeff ⟶ Stalk V weight

namespace StalkPiece

private abbrev atWeight (p : StalkPiece V) {a : Labels r} (h : p.weight = a) :
    p.coeff ⟶ Stalk V a :=
  p.incl ≫ eqToHom (congrArg (Stalk V) h)

@[simp]
private theorem atWeight_rfl (p : StalkPiece V) : p.atWeight rfl = p.incl := by
  simp [atWeight]

private abbrev single (V : Heart r g c) (a : Labels r) : StalkPiece V :=
  ⟨a, Stalk V a, 𝟙 _⟩

private abbrev tensor (p : StalkPiece V) (q : StalkPiece W) : StalkPiece (V ⋆ W) :=
  ⟨p.weight + q.weight, p.coeff ⊗ q.coeff, (p.incl ⊗ₘ q.incl) ≫
    P.includeSummand V W p.weight q.weight⟩

private theorem tensor_atWeight (p : StalkPiece V) (q : StalkPiece W)
    {a b n : Labels r} (ha : p.weight = a) (hb : q.weight = b) (hn : a + b = n) :
    (p.tensor P q).atWeight ((congrArg₂ (· + ·) ha hb).trans hn) =
      (p.atWeight ha ⊗ₘ q.atWeight hb) ≫ includeFiber P V W n ⟨(a, b), hn⟩ := by
  subst a b
  simp only [atWeight, tensor, Category.assoc, eqToHom_refl, Category.comp_id]
  rw [show P.includeSummand V W p.weight q.weight =
    includeFiber P V W (p.weight + q.weight) ⟨(p.weight, q.weight), rfl⟩ from rfl,
    includeFiber_cast P _ _ _ hn]

end StalkPiece

/-- At each weight the indicated inclusions detect equality of maps from the stalk. -/
private def Determines {I : Type} (pieces : I → StalkPiece V) : Prop :=
  ∀ (n : Labels r) (M : Coeff.{0}) (f h : Stalk V n ⟶ M),
    (∀ i (e : (pieces i).weight = n), (pieces i).atWeight e ≫ f =
      (pieces i).atWeight e ≫ h) → f = h

private theorem determines_single (V : Heart r g c) : Determines (StalkPiece.single V) := by
  intro n M f h hh
  simpa only [StalkPiece.atWeight_rfl, StalkPiece.single, Category.id_comp] using hh n rfl

private theorem determines_map {I : Type} {pieces : I → StalkPiece V}
    (hp : Determines pieces) (n : Labels r) (F G : Coeff.{0} ⥤ Coeff.{0}) (A : F ⊣ G)
    {M : Coeff.{0}} (f h : F.obj (Stalk V n) ⟶ M)
    (hh : ∀ i (e : (pieces i).weight = n), F.map ((pieces i).atWeight e) ≫ f =
      F.map ((pieces i).atWeight e) ≫ h) : f = h := by
  apply (A.homEquiv _ _).injective
  apply hp n
  intro i e
  rw [← A.homEquiv_naturality_left, ← A.homEquiv_naturality_left, hh i e]

/-- Tensoring preserves the detecting families in each argument. Composing
with the coproduct inclusions then detects maps out of the convolution stalk. -/
private theorem determines_tensor {I J : Type}
    {p : I → StalkPiece V} {q : J → StalkPiece W}
    (hp : Determines p) (hq : Determines q) :
    Determines (fun ij : I × J ↦ (p ij.1).tensor P (q ij.2)) := by
  intro n M f h hh
  apply (cancel_epi ((P.stalkIso n).hom.app (V, W))).mp
  apply Sigma.hom_ext
  rintro ⟨⟨a, b⟩, hn⟩
  change includeFiber P V W n ⟨(a, b), hn⟩ ≫ f =
    includeFiber P V W n ⟨(a, b), hn⟩ ≫ h
  let F := tensorRight (Stalk W b)
  let Fadj := (ihom.adjunction (Stalk W b)).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight (Stalk W b))
  apply determines_map hp a F _ Fadj
  intro i hi
  let G := tensorLeft (p i).coeff
  apply determines_map hq b G _ (ihom.adjunction (p i).coeff)
  intro j hj
  have test := hh (i, j) ((congrArg₂ (· + ·) hi hj).trans hn)
  rw [StalkPiece.tensor_atWeight P (p i) (q j) hi hj hn] at test
  change (𝟙 _ ⊗ₘ (q j).atWeight hj) ≫ ((p i).atWeight hi ⊗ₘ 𝟙 _) ≫ _ =
    (𝟙 _ ⊗ₘ (q j).atWeight hj) ≫ ((p i).atWeight hi ⊗ₘ 𝟙 _) ≫ _
  simpa only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id, Category.assoc] using test

private theorem convolution_hom_ext {I : Type} {pieces : I → StalkPiece V}
    (hp : Determines pieces) (f h : V ⟶ W)
    (hh : ∀ i, (pieces i).incl ≫ mapStalk f (pieces i).weight =
      (pieces i).incl ≫ mapStalk h (pieces i).weight) : f = h := by
  apply eq_of_stalks
  intro n
  apply hp
  intro i e
  subst n
  simpa using hh i

/-- Restriction of a morphism to a labelled tensor summand. -/
private def Tracks (f : V ⟶ W) (p : StalkPiece V) (q : StalkPiece W)
    (s : p.coeff ⟶ q.coeff) (e : q.weight = p.weight) : Prop :=
  ∀ (n : Labels r) (hn : p.weight = n),
    p.atWeight hn ≫ mapStalk f n = s ≫ q.atWeight (e.trans hn)

namespace Tracks

private theorem of_at_weight {f : V ⟶ W} {p : StalkPiece V} {q : StalkPiece W}
    {s : p.coeff ⟶ q.coeff} {e : q.weight = p.weight}
    (hf : p.incl ≫ mapStalk f p.weight = s ≫ q.atWeight e) :
    Tracks f p q s e := by
  intro n hn
  subst n
  simpa only [StalkPiece.atWeight_rfl] using hf

private theorem of_at_target_weight {f : V ⟶ W} {p : StalkPiece V} {q : StalkPiece W}
    {s : p.coeff ⟶ q.coeff} {e : q.weight = p.weight}
    (hf : p.incl ≫ eqToHom (congrArg (Stalk V) e.symm) ≫ mapStalk f q.weight =
      s ≫ q.incl) :
    Tracks f p q s e := by
  intro n hn
  have ht := e.trans hn
  subst ht
  simpa only [StalkPiece.atWeight_rfl, StalkPiece.atWeight, Category.assoc] using hf

private theorem id (p : StalkPiece V) : Tracks (𝟙 V) p p (𝟙 _) rfl := by
  intro n hn
  simp only [mapStalk_id, Category.comp_id, Category.id_comp]

private theorem comp {f : V ⟶ W} {h : W ⟶ X}
    {p : StalkPiece V} {q : StalkPiece W} {t : StalkPiece X}
    {s : p.coeff ⟶ q.coeff} {u : q.coeff ⟶ t.coeff}
    {e : q.weight = p.weight} {d : t.weight = q.weight}
    (hf : Tracks f p q s e) (hh : Tracks h q t u d) :
    Tracks (f ≫ h) p t (s ≫ u) (d.trans e) := by
  intro n hn
  rw [mapStalk_comp, ← Category.assoc, hf n hn, Category.assoc, hh n (e.trans hn),
    Category.assoc]

private theorem equal {f h : V ⟶ W} {p : StalkPiece V} {q : StalkPiece W}
    {s u : p.coeff ⟶ q.coeff} {e d : q.weight = p.weight}
    (hf : Tracks f p q s e) (hh : Tracks h p q u d) (hcoeff : s = u) :
    p.incl ≫ mapStalk f p.weight = p.incl ≫ mapStalk h p.weight := by
  subst u
  simpa only [StalkPiece.atWeight_rfl] using
    (hf p.weight rfl).trans (hh p.weight rfl).symm

private theorem inv {f : V ≅ W} {p : StalkPiece V} {q : StalkPiece W}
    {s : p.coeff ≅ q.coeff} {e : q.weight = p.weight}
    (hf : Tracks f.hom p q s.hom e) :
    Tracks f.inv q p s.inv e.symm := by
  intro n hn
  have h := congrArg (fun u ↦ s.inv ≫ u ≫ mapStalk f.inv n) (hf n (e.symm.trans hn))
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, ← mapStalk_comp,
    Iso.hom_inv_id, mapStalk_id, Category.comp_id] using h.symm

private theorem tensor {V' W' : Heart r g c} {f : V ⟶ V'} {h : W ⟶ W'}
    {p : StalkPiece V} {q : StalkPiece W} {p' : StalkPiece V'} {q' : StalkPiece W'}
    {s : p.coeff ⟶ p'.coeff} {u : q.coeff ⟶ q'.coeff}
    {e : p'.weight = p.weight} {d : q'.weight = q.weight}
    (hf : Tracks f p p' s e) (hh : Tracks h q q' u d) :
    Tracks (multiply P f h) (p.tensor P q) (p'.tensor P q') (s ⊗ₘ u)
      (congrArg₂ (· + ·) e d) := by
  intro n hn
  rw [StalkPiece.tensor_atWeight P p q rfl rfl hn, Category.assoc,
    includeFiber_naturality P f h n ⟨(p.weight, q.weight), hn⟩]
  rw [← Category.assoc, tensorHom_comp_tensorHom, hf p.weight rfl, hh q.weight rfl,
    ← tensorHom_comp_tensorHom, Category.assoc]
  exact congrArg ((s ⊗ₘ u) ≫ ·) (StalkPiece.tensor_atWeight P p' q' e d hn).symm

end Tracks

variable (U : OrderedConstraints P) (σ : SwapsConvolution P)

private abbrev associate (V W X : Heart r g c) : ((V ⋆ W) ⋆ X) ≅ (V ⋆ (W ⋆ X)) :=
  U.associator.app (V, W, X)

private abbrev flip (V W : Heart r g c) : (V ⋆ W) ≅ (W ⋆ V) := σ.app (V, W)

private abbrev leftUnit (V : Heart r g c) : (U.unit ⋆ V) ≅ V :=
  U.leftUnitor.app V

private abbrev rightUnit (V : Heart r g c) : (V ⋆ U.unit) ≅ V :=
  U.rightUnitor.app V

private theorem tracks_associate (p : StalkPiece V) (q : StalkPiece W) (t : StalkPiece X) :
    Tracks (associate P U V W X).hom ((p.tensor P q).tensor P t)
      (p.tensor P (q.tensor P t)) (α_ p.coeff q.coeff t.coeff).hom
      (add_assoc p.weight q.weight t.weight).symm := by
  apply Tracks.of_at_weight
  let a := p.weight
  let b := q.weight
  let d := t.weight
  have base : P.leftSummand V W X a b d ≫ mapStalk (associate P U V W X).hom (a + b + d) =
      (α_ (Stalk V a) (Stalk W b) (Stalk X d)).hom ≫ P.rightSummand V W X a b d := by
    have h := U.associator_stalk V W X (D.triples.symm (a, b, d))
    dsimp only at h
    rw [D.triples.apply_symm_apply] at h
    exact h
  have left :
      ((p.tensor P q).tensor P t).incl =
        ((p.incl ⊗ₘ q.incl) ⊗ₘ t.incl) ≫ P.leftSummand V W X a b d := by
    have h := tensorHom_comp_tensorHom (p.incl ⊗ₘ q.incl) t.incl
      (P.includeSummand V W a b) (𝟙 (Stalk X d))
    rw [Category.comp_id] at h
    exact (congrArg (· ≫ P.includeSummand (V ⋆ W) X (a + b) d) h.symm).trans
      (Category.assoc _ _ _)
  have right :
      (p.tensor P (q.tensor P t)).atWeight (add_assoc a b d).symm =
        (p.incl ⊗ₘ (q.incl ⊗ₘ t.incl)) ≫ P.rightSummand V W X a b d := by
    have h := tensorHom_comp_tensorHom p.incl (q.incl ⊗ₘ t.incl)
      (𝟙 (Stalk V a)) (P.includeSummand W X b d)
    rw [Category.comp_id] at h
    simp only [StalkPiece.atWeight, StalkPiece.tensor, OrderedProduct.rightSummand, Category.assoc]
    exact (congrArg (fun f ↦ f ≫ P.includeSummand V (W ⋆ X) a (b + d) ≫
      eqToHom (congrArg (Stalk (V ⋆ (W ⋆ X))) (add_assoc a b d).symm)) h.symm).trans
        (Category.assoc _ _ _)
  rw [left, right, Category.assoc, base]
  exact associator_naturality_assoc p.incl q.incl t.incl _

private theorem tracks_flip (hσ : FlipsConvolutionSummands P σ)
    (p : StalkPiece V) (q : StalkPiece W) :
    Tracks (flip P σ V W).hom (p.tensor P q) (q.tensor P p)
      (β_ p.coeff q.coeff).hom (add_comm q.weight p.weight) := by
  apply Tracks.of_at_weight
  simp only [StalkPiece.atWeight, StalkPiece.tensor, Category.assoc]
  rw [show mapStalk (flip P σ V W).hom (p.weight + q.weight) =
    commutorStalk σ V W (p.weight + q.weight) from rfl, hσ V W p.weight q.weight]
  exact BraidedCategory.braiding_naturality_assoc p.incl q.incl _

private abbrev scalar : (𝟙_ Coeff.{0}) ⟶ Stalk U.unit 0 :=
  eqToHom (by simp [pointUnit]) ≫ U.unitStalk.inv.app (Discrete.mk 0)

private abbrev unitPiece : StalkPiece U.unit := ⟨0, 𝟙_ Coeff.{0}, scalar P U⟩

private theorem determines_unit : Determines (fun _ : Unit ↦ unitPiece P U) := by
  intro n M f h hh
  by_cases hn : n = 0
  · subst n
    have : IsIso (scalar P U) := by
      unfold scalar
      infer_instance
    apply (cancel_epi (scalar P U)).mp
    simpa only [StalkPiece.atWeight_rfl] using hh () rfl
  · have hz : IsZero (Stalk U.unit n) :=
      (pointUnit_off_zero n hn).of_iso (U.unitStalk.app (Discrete.mk n))
    exact hz.eq_of_src f h

private theorem tracks_leftUnit (V : Heart r g c) (a : Labels r) :
    Tracks (leftUnit P U V).hom ((unitPiece P U).tensor P (StalkPiece.single V a))
      (StalkPiece.single V a) (λ_ (Stalk V a)).hom (zero_add a).symm := by
  refine Tracks.of_at_target_weight ?_
  let scalarTensor := scalar P U ⊗ₘ 𝟙 (Stalk V a)
  let incl := P.includeSummand U.unit V 0 a
  let tail := eqToHom (congrArg (Stalk (U.unit ⋆ V)) (zero_add a)) ≫
    mapStalk (leftUnit P U V).hom a
  change (scalarTensor ≫ incl) ≫ tail = (λ_ (Stalk V a)).hom ≫ 𝟙 (Stalk V a)
  exact (Category.assoc scalarTensor incl tail).trans
    ((U.leftUnitor_stalk V a).trans (Category.comp_id (λ_ (Stalk V a)).hom).symm)

private theorem tracks_rightUnit (V : Heart r g c) (a : Labels r) :
    Tracks (rightUnit P U V).hom ((StalkPiece.single V a).tensor P (unitPiece P U))
      (StalkPiece.single V a) (ρ_ (Stalk V a)).hom (add_zero a).symm := by
  refine Tracks.of_at_target_weight ?_
  let scalarTensor := 𝟙 (Stalk V a) ⊗ₘ scalar P U
  let incl := P.includeSummand V U.unit a 0
  let tail := eqToHom (congrArg (Stalk (V ⋆ U.unit)) (add_zero a)) ≫
    mapStalk (rightUnit P U V).hom a
  change (scalarTensor ≫ incl) ≫ tail = (ρ_ (Stalk V a)).hom ≫ 𝟙 (Stalk V a)
  exact (Category.assoc scalarTensor incl tail).trans
    ((U.rightUnitor_stalk V a).trans (Category.comp_id (ρ_ (Stalk V a)).hom).symm)

private theorem pentagon (A B C E : Heart r g c) :
    multiply P (associate P U A B C).hom (𝟙 E) ≫
        (associate P U A (B ⋆ C) E).hom ≫
        multiply P (𝟙 A) (associate P U B C E).hom =
      (associate P U (A ⋆ B) C E).hom ≫ (associate P U A B (C ⋆ E)).hom := by
  apply convolution_hom_ext (determines_tensor P
    (determines_tensor P (determines_tensor P (determines_single A) (determines_single B))
      (determines_single C)) (determines_single E))
  rintro ⟨⟨⟨a, b⟩, d⟩, e⟩
  let p := StalkPiece.single A a
  let q := StalkPiece.single B b
  let t := StalkPiece.single C d
  let w := StalkPiece.single E e
  have lhs := Tracks.comp
    (Tracks.tensor P (tracks_associate P U p q t) (Tracks.id w))
    (Tracks.comp (tracks_associate P U p (q.tensor P t) w)
      (Tracks.tensor P (Tracks.id p) (tracks_associate P U q t w)))
  have rhs := Tracks.comp (tracks_associate P U (p.tensor P q) t w)
    (tracks_associate P U p q (t.tensor P w))
  apply Tracks.equal lhs rhs
  simpa only [tensorHom_id, id_tensorHom] using
    MonoidalCategory.pentagon p.coeff q.coeff t.coeff w.coeff

private theorem triangle (A B : Heart r g c) :
    (associate P U A U.unit B).hom ≫ multiply P (𝟙 A) (leftUnit P U B).hom =
      multiply P (rightUnit P U A).hom (𝟙 B) := by
  apply convolution_hom_ext (determines_tensor P
    (determines_tensor P (determines_single A) (determines_unit P U)) (determines_single B))
  rintro ⟨⟨a, _⟩, b⟩
  let p := StalkPiece.single A a
  let t := StalkPiece.single B b
  have lhs := Tracks.comp (tracks_associate P U p (unitPiece P U) t)
    (Tracks.tensor P (Tracks.id p) (tracks_leftUnit P U B b))
  have rhs := Tracks.tensor P (tracks_rightUnit P U A a) (Tracks.id t)
  apply Tracks.equal lhs rhs
  simpa only [tensorHom_id, id_tensorHom] using MonoidalCategory.triangle p.coeff t.coeff

variable (hσ : FlipsConvolutionSummands P σ)

include hσ in
private theorem hexagon_forward (A B C : Heart r g c) :
    (associate P U A B C).hom ≫ (flip P σ A (B ⋆ C)).hom ≫ (associate P U B C A).hom =
      multiply P (flip P σ A B).hom (𝟙 C) ≫ (associate P U B A C).hom ≫
        multiply P (𝟙 B) (flip P σ A C).hom := by
  apply convolution_hom_ext (determines_tensor P
    (determines_tensor P (determines_single A) (determines_single B)) (determines_single C))
  rintro ⟨⟨a, b⟩, d⟩
  let p := StalkPiece.single A a
  let q := StalkPiece.single B b
  let t := StalkPiece.single C d
  have lhs := Tracks.comp (tracks_associate P U p q t)
    (Tracks.comp (tracks_flip P σ hσ p (q.tensor P t)) (tracks_associate P U q t p))
  have rhs := Tracks.comp (Tracks.tensor P (tracks_flip P σ hσ p q) (Tracks.id t))
    (Tracks.comp (tracks_associate P U q p t)
      (Tracks.tensor P (Tracks.id q) (tracks_flip P σ hσ p t)))
  apply Tracks.equal lhs rhs
  simpa only [tensorHom_id, id_tensorHom] using
    BraidedCategory.hexagon_forward p.coeff q.coeff t.coeff

include hσ in
private theorem hexagon_reverse (A B C : Heart r g c) :
    (associate P U A B C).inv ≫ (flip P σ (A ⋆ B) C).hom ≫ (associate P U C A B).inv =
      multiply P (𝟙 A) (flip P σ B C).hom ≫ (associate P U A C B).inv ≫
        multiply P (flip P σ A C).hom (𝟙 B) := by
  apply convolution_hom_ext (determines_tensor P (determines_single A)
    (determines_tensor P (determines_single B) (determines_single C)))
  rintro ⟨a, b, d⟩
  let p := StalkPiece.single A a
  let q := StalkPiece.single B b
  let t := StalkPiece.single C d
  have lhs := Tracks.comp (Tracks.inv (tracks_associate P U p q t))
    (Tracks.comp (tracks_flip P σ hσ (p.tensor P q) t)
      (Tracks.inv (tracks_associate P U t p q)))
  have rhs := Tracks.comp (Tracks.tensor P (Tracks.id p) (tracks_flip P σ hσ q t))
    (Tracks.comp (Tracks.inv (tracks_associate P U p t q))
      (Tracks.tensor P (tracks_flip P σ hσ p t) (Tracks.id q)))
  apply Tracks.equal lhs rhs
  simpa only [tensorHom_id, id_tensorHom] using
    BraidedCategory.hexagon_reverse p.coeff q.coeff t.coeff

include hσ in
private theorem symmetry (A B : Heart r g c) :
    (flip P σ A B).hom ≫ (flip P σ B A).hom = 𝟙 (A ⋆ B) := by
  apply convolution_hom_ext (determines_tensor P (determines_single A) (determines_single B))
  rintro ⟨a, b⟩
  let p := StalkPiece.single A a
  let q := StalkPiece.single B b
  exact Tracks.equal (Tracks.comp (tracks_flip P σ hσ p q) (tracks_flip P σ hσ q p))
    (Tracks.id (p.tensor P q)) (SymmetricCategory.symmetry p.coeff q.coeff)

@[instance_reducible]
private def convolutionMonoidal : MonoidalCategory (Heart r g c) := by
  letI := orderedMonoidalData U
  refine MonoidalCategory.ofTensorHom ?_ ?_ ?_ ?_ ?_ ?_ ?_ (pentagon P U) (triangle P U)
  · intro A B
    exact P.convolution.map_id (A, B)
  · intros
    rfl
  · intros
    rfl
  · intro A B C E F G f h f' h'
    exact (P.convolution.map_comp
      (show (A, E) ⟶ (B, F) from (f, h)) (show (B, F) ⟶ (C, G) from (f', h'))).symm
  · intro A B C A' B' C' f h k
    exact U.associator.hom.naturality
      (show (A, B, C) ⟶ (A', B', C') from (f, h, k))
  · intro A B f
    exact U.leftUnitor.hom.naturality f
  · intro A B f
    exact U.rightUnitor.hom.naturality f

@[instance_reducible]
private def convolutionSymmetric (flips : FlipsConvolutionSummands P σ) :
    @SymmetricCategory (Heart r g c) _ (convolutionMonoidal P U) := by
  letI := convolutionMonoidal P U
  refine
    { braiding := flip P σ
      braiding_naturality_left := ?_
      braiding_naturality_right := ?_
      hexagon_forward := hexagon_forward P U σ flips
      hexagon_reverse := hexagon_reverse P U σ flips
      symmetry := symmetry P σ flips }
  · intro A B C f
    exact σ.hom.naturality (show (A, B) ⟶ (A, C) from (𝟙 A, f))
  · intro A B f C
    exact σ.hom.naturality (show (A, C) ⟶ (B, C) from (f, 𝟙 C))

private def coherentConvolution (flips : FlipsConvolutionSummands P σ) :
    SymmetricConvolution U σ where
  monoidal := convolutionMonoidal P U
  ordered := rfl
  symmetric := convolutionSymmetric P U σ flips
  fusionBraiding := by
    intro V W
    change σ.app (V, W) =
      eqToIso (rfl : (V ⋆ W) = (V ⋆ W)) ≪≫ σ.app (V, W) ≪≫
        (eqToIso (rfl : (W ⋆ V) = (W ⋆ V))).symm
    simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans]
    exact (Iso.trans_refl (σ.app (V, W))).symm

/-- The ordered geometric convolution on the finite-support torus perverse
heart is symmetric monoidal, with the commutor obtained by fusion. -/
theorem torusSymmetricConvolution : TorusSymmetricConvolution := by
  intro r
  obtain ⟨D, g, c, P, ⟨U⟩, geometry, σ, flips, specializes⟩ := TorusFusion.torusFusion r
  exact ⟨D, g, c, P, U, σ, ⟨coherentConvolution P U σ flips⟩, flips, geometry, specializes⟩

end RepTheorySurvey.Geometric.TorusSymmetricConvolution
