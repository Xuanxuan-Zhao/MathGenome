import MathGenome.Internal.Specs.D05.M15.InteriorProduct
import MathGenome.Internal.Specs.D05.M15.ExteriorPairing

/-! Independent specifications for paper.tex:3136–3138.
Higher contraction uses the canonical exterior algebra of the algebraic dual.
The value is the upstream exterior lift to opposite endomorphisms, so scalars
act as scalar multiples of the identity and products reverse composition.
No dimension or characteristic restriction is imposed on its construction.
-/
noncomputable section
namespace Specs.D05.M15.InteriorProduct.Higher
universe u v

abbrev contraction_type := (K : Type u) → (V : Type v) → [Field K] →
  [AddCommGroup V] → [Module K V] →
  (_root_.ExteriorAlgebra K (Module.Dual K V) →ₗ[K]
    Module.End K (_root_.ExteriorAlgebra K V))

abbrev contraction_value : contraction_type := fun _ _ _ _ _ =>
  Specs.D05.M15.InteriorProduct.higherInterior

def generator : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (φ : Module.Dual K V),
  contraction_value K V (_root_.ExteriorAlgebra.ι K φ) =
    Specs.D05.M15.InteriorProduct.interior φ

def unit : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V],
  contraction_value K V 1 = LinearMap.id

def product : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V]
  (α β : _root_.ExteriorAlgebra K (Module.Dual K V)),
  contraction_value K V (α * β) =
    (contraction_value K V β).comp (contraction_value K V α)

/-- The fold applies the first covector first, including the empty word. -/
def word_formula : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (l : List (Module.Dual K V))
  (a : _root_.ExteriorAlgebra K V),
  contraction_value K V
    (Specs.D05.M15.InteriorProduct.word (_root_.ExteriorAlgebra.ι K) l) a =
    l.foldl (fun a φ => Specs.D05.M15.InteriorProduct.interior φ a) a

/-- The actual iterated composite is multilinear and alternating in the covectors,
expressed by an alternating map valued in endomorphisms. -/
def composite_alternating : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (r : ℕ),
  ∃ A : (Module.Dual K V) [⋀^Fin r]→ₗ[K]
      Module.End K (_root_.ExteriorAlgebra K V),
    ∀ (f : Fin r → Module.Dual K V) (a : _root_.ExteriorAlgebra K V),
      A f a = (List.ofFn f).foldl
        (fun a φ => Specs.D05.M15.InteriorProduct.interior φ a) a

def repeated_input : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (r : ℕ) (f : Fin r → Module.Dual K V)
  (i j : Fin r), i ≠ j → f i = f j → ∀ a : _root_.ExteriorAlgebra K V,
  (List.ofFn f).foldl (fun a φ => Specs.D05.M15.InteriorProduct.interior φ a) a = 0

/-- Unique factorization of the composite through the alternating quotient,
for every degree, including degree zero. -/
def factor_unique : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (r : ℕ),
  ∃! D : (⋀[K]^r (Module.Dual K V)) →ₗ[K]
      Module.End K (_root_.ExteriorAlgebra K V),
    ∀ (f : Fin r → Module.Dual K V) (a : _root_.ExteriorAlgebra K V),
      D (exteriorPower.ιMulti K r f) a = (List.ofFn f).foldl
        (fun a φ => Specs.D05.M15.InteriorProduct.interior φ a) a

def degree : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (r q : ℕ)
  (α : ⋀[K]^r (Module.Dual K V)) (a : ⋀[K]^(r+q) V),
  contraction_value K V α a ∈ ⋀[K]^q V

/-- Adjointness to left exterior multiplication under the determinant pairing.
The witness records the actual homogeneous output of the contraction.
The identity itself requires no finite-dimensionality or perfection assumption. -/
def pairing : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (r q : ℕ)
  (α : ⋀[K]^r (Module.Dual K V)) (β : ⋀[K]^q (Module.Dual K V))
  (a : ⋀[K]^(r+q) V),
  ∃ b : ⋀[K]^q V, (b : _root_.ExteriorAlgebra K V) = contraction_value K V α a ∧
    ExteriorPairing.pairing_value K V q β b =
      ExteriorPairing.pairing_value K V (r+q)
        ⟨(α : _root_.ExteriorAlgebra K (Module.Dual K V)) * β,
          SetLike.GradedMul.mul_mem α.property β.property⟩ a

/-- Any dual pair supplies the concrete degree-two guard in the paper. -/
def dual_pair_guard : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (φ ψ : Module.Dual K V) (v w : V),
  φ v = 1 → φ w = 0 → ψ v = 0 → ψ w = 1 →
  let D := contraction_value K V
    (_root_.ExteriorAlgebra.ι K φ * _root_.ExteriorAlgebra.ι K ψ)
  let a := _root_.ExteriorAlgebra.ι K v
  let b := _root_.ExteriorAlgebra.ι K w
  D (a*b) = 1 ∧ D a = 0 ∧ D b = 0 ∧ D (a*b) ≠ D a*b - a*D b

/-- The guard is instantiated over every field, rather than asserting failure
for every higher contraction (which would incorrectly include zero). -/
def counterexample : Prop := ∀ {K : Type u} [Field K],
  ∃ (α : _root_.ExteriorAlgebra K (Module.Dual K (K × K)))
    (a b : _root_.ExteriorAlgebra K (K × K)),
    contraction_value K (K × K) α (a*b) ≠
      contraction_value K (K × K) α a*b - a*contraction_value K (K × K) α b

end Specs.D05.M15.InteriorProduct.Higher
