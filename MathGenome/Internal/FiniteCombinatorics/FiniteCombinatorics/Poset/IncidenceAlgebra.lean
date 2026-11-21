import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Poset.IncidenceAlgebra

/-!
The incidence algebra of a finite poset over a commutative ring.
This realizes paper.tex, p204:W07 using Mathlib's incidence algebra, with
an explicit inverse-pair bridge to functions on comparable pairs.
-/

noncomputable section
open Classical
open scoped FiniteCombinatorics.Poset

namespace FiniteCombinatorics.Poset.IncidenceFunction

variable (R P : Type*) [CommRing R] [PartialOrder P] [Fintype P]

/-- The convolution identity, the source's delta function. -/
def delta : IncidenceFunction R P := 1

/-- The source's function which is one on every comparable pair. -/
def zeta : IncidenceFunction R P := IncidenceAlgebra.zeta R

/-- The canonical ring uses pointwise addition and interval convolution. -/
@[instance_reducible]
def ringStructure : Ring (IncidenceFunction R P) := inferInstance

/-- The coefficient ring acts pointwise, giving the canonical `R`-algebra. -/
@[instance_reducible]
def algebraStructure : Algebra R (IncidenceFunction R P) := inferInstance

/-- Restriction and zero extension are mutually inverse, with no constraints on
functions on comparable pairs. -/
theorem comparablePair_bridge :
    (∀ f : IncidenceFunction R P, extend (restrict f) = f) ∧
    (∀ f : ComparableFunction R P, restrict (extend f) = f) := by
  constructor
  · intro f
    apply IncidenceAlgebra.ext
    intro x z hxz
    simp [extend, restrict, hxz]
  · intro f
    funext p
    rcases p with ⟨⟨x, z⟩, hxz⟩
    simp [restrict, extend, hxz]

/-- Addition, zero, additive inverses, and coefficient scalars act pointwise. -/
theorem pointwise_operations :
    ∀ (f g : IncidenceFunction R P) (r : R) (x z : P),
      (0 : IncidenceFunction R P) x z = 0 ∧
      (f + g) x z = f x z + g x z ∧
      (-f) x z = -f x z ∧
      (r • f) x z = r * f x z := by
  intro f g r x z
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Convolution sums precisely over `x ≤ y ≤ z`, including both endpoints. -/
theorem convolution_apply :
    ∀ (f g : IncidenceFunction R P) (x z : P),
      (f * g) x z = ∑ y ∈ Finset.Icc x z, f x y * g y z := by
  intro f g x z
  exact IncidenceAlgebra.mul_apply f g x z

/-- Delta is one on the diagonal and zero everywhere else. -/
theorem delta_apply :
    ∀ x z : P, delta R P x z = if x = z then 1 else 0 := by
  intro x z
  exact IncidenceAlgebra.one_apply x z

/-- Zeta is one on comparable pairs and zero on the other pairs. -/
theorem zeta_apply :
    ∀ x z : P, zeta R P x z = if x ≤ z then 1 else 0 := by
  intro x z
  exact IncidenceAlgebra.zeta_apply x z

/-- Associativity, both unit laws, distributivity and coefficient bilinearity. -/
theorem convolution_laws :
    ∀ (f g h : IncidenceFunction R P) (r : R),
      (f * g) * h = f * (g * h) ∧
      delta R P * f = f ∧
      f * delta R P = f ∧
      f * (g + h) = f * g + f * h ∧
      (f + g) * h = f * h + g * h ∧
      (r • f) * g = r • (f * g) ∧
      f * (r • g) = r • (f * g) := by
  intro f g h r
  exact ⟨mul_assoc f g h, one_mul f, mul_one f, mul_add f g h,
    add_mul f g h, smul_mul_assoc r f g, Algebra.mul_smul_comm r f g⟩

end FiniteCombinatorics.Poset.IncidenceFunction
