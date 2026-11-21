import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedExactCouples
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.PageCohomology
import Mathlib.Order.Monotone.Basic

/-! HA-F05, source lines 316–387. The initial couple is the long exact
cohomology sequence of the first filtration sequence. At stage `t : ℕ`,
the page number is `r=t+1` and the displacement of j is `t`.
All representative statements concern morphisms from arbitrary test objects.
The mono/epi factorization in `DComparison` states the image formula for D,
including its embedding into H(F^p), rather than just an abstract isomorphism.
-/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra
namespace FiltrationExactCouple
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex A ℤ} (F : Filtration K)

/-- The inclusion of any deeper filtration step. -/
def stepInclusion (p q : ℤ) (hpq : p ≤ q) : F.step q ⟶ F.step p where
  f n := Subobject.ofLE _ _ (antitone_int_of_succ_le (f := fun a => F.piece a n) (fun a => F.decreasing a n) hpq)
  comm' i j _ := by
    apply (cancel_mono (F.piece p j).arrow).1
    simp [Filtration.step, Category.assoc]

/-- The three LES maps with explicit endpoint transports. -/
def initialI (p q n : ℤ) (hq : q = p+1) :
    (F.step q).homology n ⟶ (F.step p).homology n :=
  eqToHom (by rw [hq]) ≫ HomologicalComplex.homologyMap (F.transition p) n

def initialJ (p q n : ℤ) (hq : q = p+0) :
    (F.step p).homology n ⟶ (F.graded q).homology n :=
  HomologicalComplex.homologyMap (F.projection p) n ≫ eqToHom (by rw [hq, add_zero])

def initialK (h : ∀ p, (F.firstSequence p).ShortExact)
    (p q n m : ℤ) (hq : q = p+1) (hm : m = n+1) :
    (F.graded p).homology n ⟶ (F.step q).homology m :=
  (h p).δ n (n+1) (by simp) ≫ eqToHom (by rw [hq, hm]; rfl)

/-- The exact couple furnished by the first short exact filtration sequence.
The hypothesis is a witness of short exactness, whose unconditional existence
is part of the statements below. -/
def initial (h : ∀ p, (F.firstSequence p).ShortExact) : ExactCouple A 0 where
  D p n := (F.step p).homology n
  E p n := (F.graded p).homology n
  i := initialI F
  j := initialJ F
  k := initialK F h
  exact_ij p q a n hq ha := by
    have ha' : a = p := by omega
    subst ha'
    subst q
    simp only [initialI, initialJ, eqToHom_refl, Category.id_comp, Category.comp_id]
    refine ⟨?_, (h a).homology_exact₂ n⟩
    rw [← HomologicalComplex.homologyMap_comp]
    change HomologicalComplex.homologyMap ((F.firstSequence a).f ≫
      (F.firstSequence a).g) n = 0
    rw [(F.firstSequence a).zero, HomologicalComplex.homologyMap_zero]
  exact_jk p a b n m ha hb hm := by
    have ha' : a = p := by omega
    subst ha'
    subst b m
    simp only [initialJ, initialK, eqToHom_refl, Category.comp_id]
    exact ⟨(h a).comp_δ n (n+1) (by simp),
      (h a).homology_exact₃ n (n+1) (by simp)⟩
  exact_ki p q n m hq hm := by
    subst q m
    simp only [initialK, initialI, eqToHom_refl, Category.id_comp, Category.comp_id]
    exact ⟨(h p).δ_comp n (n+1) (by simp),
      (h p).homology_exact₁ n (n+1) (by simp)⟩

/-- A tower of actual derivations, starting at the specified initial couple. -/
structure Tower (h : ∀ p, (F.firstSequence p).ShortExact) where
  family : ℕ → Σ s : ℤ, ExactCouple A s
  start : family 0 = ⟨0, initial F h⟩
  step : ∀ t, ∃ R : (family t).2.Derivation,
    family (t+1) = ⟨(family t).1+1, R.toExactCouple⟩
  degree : ∀ t, (family t).1 = (t : ℤ)

variable {F}
/-- At every stage D is the image of cohomology of the deeper step in
cohomology of the original step. The i-maps restrict the original inclusions. -/
structure DComparison {h : ∀ p, (F.firstSequence p).ShortExact} (T : Tower F h) where
  inclusion : ∀ (t : ℕ) (p n : ℤ), (T.family t).2.D p n ⟶ (F.step p).homology n
  projection : ∀ (t : ℕ) (p n : ℤ), (F.step (p+(t:ℤ))).homology n ⟶ (T.family t).2.D p n
  mono : ∀ (t : ℕ) (p n : ℤ), Mono (inclusion t p n)
  epi : ∀ (t : ℕ) (p n : ℤ), Epi (projection t p n)
  factorization : ∀ (t : ℕ) (p n : ℤ), projection t p n ≫ inclusion t p n =
    HomologicalComplex.homologyMap (stepInclusion F p (p+(t:ℤ)) (by omega)) n
  i_formula : ∀ (t : ℕ) (p n : ℤ),
    (T.family t).2.i p (p+1) n rfl ≫ inclusion t p n =
      inclusion t (p+1) n ≫ HomologicalComplex.homologyMap (F.transition p) n

/-- Comparison of all derived E-terms and differentials with the fixed HA-F03
pages, together with the two generalized representative formulas in HA-F05. -/
structure Comparison {h : ∀ p, (F.firstSequence p).ShortExact} (T : Tower F h)
    (D : DComparison T) (P : F03Specs.PageData F) where
  pageIso : ∀ (t : ℕ) (p n : ℤ), (T.family t).2.E p n ≅
    FilteredPage.page F ((t:ℤ)+1) p n (P.containment ((t:ℤ)+1) p n)
  j_formula : ∀ (t : ℕ) (p n : ℤ) {U : A}
    (x : U ⟶ (F.step (p+(t:ℤ))).X n)
    (hx : x ≫ (F.step (p+(t:ℤ))).d n (n+1) = 0)
    (z : U ⟶ (FilteredPage.almost F ((t:ℤ)+1) (p+(t:ℤ)) n : A))
    (hz : z ≫ (FilteredPage.almost F ((t:ℤ)+1) (p+(t:ℤ)) n).arrow =
      x ≫ (F.piece (p+(t:ℤ)) n).arrow),
    (F.step (p+(t:ℤ))).liftCycles x (n+1) (by simp) hx ≫
      (F.step (p+(t:ℤ))).homologyπ n ≫ D.projection t p n ≫
      (T.family t).2.j p (p+(t:ℤ)) n (by rw [T.degree]) ≫
      (pageIso t (p+(t:ℤ)) n).hom =
    z ≫ FilteredPage.toPage F ((t:ℤ)+1) (p+(t:ℤ)) n
      (P.containment ((t:ℤ)+1) (p+(t:ℤ)) n)
  k_formula : ∀ (t : ℕ) (p n : ℤ) {U : A}
    (x : U ⟶ (FilteredPage.almost F ((t:ℤ)+1) p n : A))
    (y : U ⟶ (F.step (p+1)).X (n+1))
    (hy : y ≫ (F.piece (p+1) (n+1)).arrow =
      x ≫ (FilteredPage.almost F ((t:ℤ)+1) p n).arrow ≫ K.d n (n+1))
    (hdy : y ≫ (F.step (p+1)).d (n+1) (n+1+1) = 0),
    x ≫ FilteredPage.toPage F ((t:ℤ)+1) p n (P.containment ((t:ℤ)+1) p n) ≫
      (pageIso t p n).inv ≫ (T.family t).2.k p (p+1) n (n+1) rfl rfl ≫
        D.inclusion t (p+1) (n+1) =
      (F.step (p+1)).liftCycles y (n+1+1) (by simp) hdy ≫
        (F.step (p+1)).homologyπ (n+1)
  differential_formula : ∀ (t : ℕ) (p n : ℤ),
    (T.family t).2.d p (p+((t:ℤ)+1)) n (n+1)
      (by rw [T.degree]; omega) rfl ≫ (pageIso t (p+((t:ℤ)+1)) (n+1)).hom =
    (pageIso t p n).hom ≫ P.differential ((t:ℤ)+1) (by omega) p n

end FiltrationExactCouple

namespace F05Specs
open FiltrationExactCouple
/-- Existence of the initial exact couple and of its full derived tower. -/
def InitialStatement : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K),
  ∃ h : ∀ p, (F.firstSequence p).ShortExact, Nonempty (Tower F h)

/-- The D-image formula and compatibility of all i-maps. -/
def DTerms : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K),
  ∃ (h : ∀ p, (F.firstSequence p).ShortExact) (T : Tower F h), Nonempty (DComparison T)

/-- Full HA-F05, with its original unrestricted abelian-category scope. -/
def FullStatement : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K),
  ∃ (h : ∀ p, (F.firstSequence p).ShortExact) (T : Tower F h)
    (D : DComparison T) (P : F03Specs.PageData F), Nonempty (Comparison T D P)
end F05Specs
end AdvancedHomologicalAlgebra
