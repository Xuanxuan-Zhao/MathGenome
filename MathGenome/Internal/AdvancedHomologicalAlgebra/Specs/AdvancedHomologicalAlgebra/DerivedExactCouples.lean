import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega

/-! The general construction used in HA-F05 (lines 332–365). Indices are
(p,n), where n is total cohomological degree, so the usual second index is n-p.
The integer r is the displacement of j; the initial couple has r=0.
Endpoint equalities in the homogeneous maps avoid choosing transports of objects.
They do not add hypotheses to an exact couple. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
namespace AdvancedHomologicalAlgebra
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Exactness includes the vanishing of the composite. -/
def ExactPair {A B X : C} (f : A ⟶ B) (g : B ⟶ X) : Prop :=
  ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).Exact

namespace ExactPair
variable {A B X : C} {f : A ⟶ B} {g : B ⟶ X}
lemma zero (h : ExactPair f g) : f ≫ g = 0 := h.choose
lemma exact (h : ExactPair f g) : (ShortComplex.mk f g h.zero).Exact := h.choose_spec
end ExactPair

/-- A bigraded exact couple. Its maps have degrees (-1,0), (r,0),
and (1,1) in (p,n) coordinates. In (p,q) coordinates these are
(-1,1), (r,-r), and (1,0), respectively. -/
structure ExactCouple (C : Type u) [Category.{v} C] [Abelian C] (r : ℤ) where
  D : ℤ → ℤ → C
  E : ℤ → ℤ → C
  i : ∀ p q n, q = p + 1 → (D q n ⟶ D p n)
  j : ∀ p q n, q = p + r → (D p n ⟶ E q n)
  k : ∀ p q n m, q = p + 1 → m = n + 1 → (E p n ⟶ D q m)
  exact_ij : ∀ p q a n (hq : q = p+1) (ha : a = p+r),
    ExactPair (i p q n hq) (j p a n ha)
  exact_jk : ∀ p a b n m (ha : a = p+r) (hb : b = a+1) (hm : m = n+1),
    ExactPair (j p a n ha) (k a b n m hb hm)
  exact_ki : ∀ p q n m (hq : q = p+1) (hm : m = n+1),
    ExactPair (k p q n m hq hm) (i p q m hq)

namespace ExactCouple

/-- Build the interface from the usual component maps. The additional endpoint
arguments in `ExactCouple` are just dependent substitutions. -/
def ofComponents {r : ℤ} (D E : ℤ → ℤ → C)
    (i : ∀ p n, D (p+1) n ⟶ D p n)
    (j : ∀ p n, D p n ⟶ E (p+r) n)
    (k : ∀ p n, E p n ⟶ D (p+1) (n+1))
    (hij : ∀ p n, ExactPair (i p n) (j p n))
    (hjk : ∀ p n, ExactPair (j p n) (k (p+r) n))
    (hki : ∀ p n, ExactPair (k p n) (i p (n+1))) : ExactCouple C r where
  D := D
  E := E
  i p q n h := by subst q; exact i p n
  j p q n h := by subst q; exact j p n
  k p q n m h h' := by subst q m; exact k p n
  exact_ij p q a n hq ha := by subst q a; exact hij p n
  exact_jk p a b n m ha hb hm := by subst a b m; exact hjk p n
  exact_ki p q n m hq hm := by subst q m; exact hki p n

variable {r : ℤ} (Q : ExactCouple C r)

/-- The page differential has degree (r+1,1) in (p,n). -/
def d (p q n m : ℤ) (hq : q = p+r+1) (hm : m = n+1) : Q.E p n ⟶ Q.E q m :=
  Q.k p (p+1) n m rfl hm ≫ Q.j (p+1) q m (by omega)

lemma d_squared (p q a n m l : ℤ) (hq : q = p+r+1) (ha : a = q+r+1)
    (hm : m = n+1) (hl : l = m+1) :
    Q.d p q n m hq hm ≫ Q.d q a m l ha hl = 0 := by
  dsimp [d]
  rw [assoc, ← assoc (Q.j _ _ _ _), (Q.exact_jk _ _ _ _ _ _ _ _).zero,
    zero_comp, comp_zero]

/-- The cycles modulo boundaries at a fixed bidegree. -/
def pageComplex (p n : ℤ) : ShortComplex C :=
  ShortComplex.mk
    (Q.d (p-r-1) p (n-1) n (by omega) (by omega))
    (Q.d p (p+r+1) n (n+1) rfl rfl)
    (Q.d_squared _ _ _ _ _ _ _ _ _ _)

def derivedD (p n : ℤ) : C := image (Q.i p (p+1) n rfl)
def derivedE (p n : ℤ) : C := (Q.pageComplex p n).homology

def inclusion (p n : ℤ) : Q.derivedD p n ⟶ Q.D p n :=
  image.ι (Q.i p (p+1) n rfl)

def projection (p n : ℤ) : Q.D (p+1) n ⟶ Q.derivedD p n :=
  factorThruImage (Q.i p (p+1) n rfl)

instance (p n : ℤ) : Mono (Q.inclusion p n) := inferInstanceAs (Mono (image.ι (Q.i p (p+1) n rfl)))
instance (p n : ℤ) : Epi (Q.projection p n) := inferInstanceAs (Epi (factorThruImage (Q.i p (p+1) n rfl)))

@[reassoc (attr := simp)]
lemma projection_inclusion (p n : ℤ) :
    Q.projection p n ≫ Q.inclusion p n = Q.i p (p+1) n rfl := image.fac _

/-- A derived couple with its specified objects, representative formulas, and
all three exactness assertions. These formulas are the categorical meaning of
 i'(a')=i(a'), j'(ia)=[j(a)], k'([e])=k(e). -/
structure Derivation where
  i : ∀ p q n, q = p+1 → (Q.derivedD q n ⟶ Q.derivedD p n)
  j : ∀ p q n, q = p+(r+1) → (Q.derivedD p n ⟶ Q.derivedE q n)
  k : ∀ p q n m, q = p+1 → m = n+1 → (Q.derivedE p n ⟶ Q.derivedD q m)
  i_formula : ∀ p q n (h : q = p+1),
    i p q n h ≫ Q.inclusion p n = Q.inclusion q n ≫ Q.i p q n h
  j_formula : ∀ p q n (h : q = p+(r+1)),
    Q.projection p n ≫ j p q n h =
      (Q.pageComplex q n).liftCycles (Q.j (p+1) q n (by omega))
        (by
          dsimp [pageComplex, d]
          rw [← assoc, (Q.exact_jk _ _ _ _ _ _ _ _).zero, zero_comp]
          rfl) ≫
        (Q.pageComplex q n).homologyπ
  k_formula : ∀ p q n m (hp : q = p+1) (hn : m = n+1),
    (Q.pageComplex p n).homologyπ ≫ k p q n m hp hn ≫ Q.inclusion q m =
      (Q.pageComplex p n).iCycles ≫ Q.k p q n m hp hn
  exact_ij : ∀ p q a n (hq : q = p+1) (ha : a = p+(r+1)),
    ExactPair (i p q n hq) (j p a n ha)
  exact_jk : ∀ p a b n m (ha : a = p+(r+1)) (hb : b = a+1) (hm : m = n+1),
    ExactPair (j p a n ha) (k a b n m hb hm)
  exact_ki : ∀ p q n m (hq : q = p+1) (hm : m = n+1),
    ExactPair (k p q n m hq hm) (i p q m hq)

/-- The output has exactly the same kind of interface, at the next displacement. -/
def Derivation.toExactCouple (R : Q.Derivation) : ExactCouple C (r+1) where
  D := Q.derivedD
  E := Q.derivedE
  i := R.i
  j := R.j
  k := R.k
  exact_ij := R.exact_ij
  exact_jk := R.exact_jk
  exact_ki := R.exact_ki

end ExactCouple
end AdvancedHomologicalAlgebra

namespace Specs.AdvancedHomologicalAlgebra
universe v u
/-- HA-F05: jk is a square-zero homogeneous differential. -/
def differential_squared_type : Prop :=
  ∀ (C : Type u) [Category.{v} C] [Abelian C] (r : ℤ)
    (Q : _root_.AdvancedHomologicalAlgebra.ExactCouple C r)
    (p q a n m l : ℤ) (hq : q = p+r+1) (ha : a = q+r+1)
    (hm : m = n+1) (hl : l = m+1),
    Q.d p q n m hq hm ≫ Q.d q a m l ha hl = 0

/-- HA-F05, general derived-couple construction, including bigrading. -/
def derivation_type : Prop :=
  ∀ (C : Type u) [Category.{v} C] [Abelian C] (r : ℤ)
    (Q : _root_.AdvancedHomologicalAlgebra.ExactCouple C r), Nonempty Q.Derivation

/-- HA-F05: the construction can be repeated, with the j displacement
increasing by one at every step, and the specified image/homology objects. -/
def iteration_type : Prop :=
  ∀ (C : Type u) [Category.{v} C] [Abelian C] (r : ℤ)
    (Q : _root_.AdvancedHomologicalAlgebra.ExactCouple C r),
    ∃ F : ℕ → Σ s : ℤ, _root_.AdvancedHomologicalAlgebra.ExactCouple C s,
      F 0 = ⟨r, Q⟩ ∧
      (∀ t : ℕ, ∃ R : (F t).2.Derivation,
        F (t+1) = ⟨(F t).1+1, R.toExactCouple⟩) ∧
      (∀ t : ℕ, (F t).1 = r + (t : ℤ))
end Specs.AdvancedHomologicalAlgebra
