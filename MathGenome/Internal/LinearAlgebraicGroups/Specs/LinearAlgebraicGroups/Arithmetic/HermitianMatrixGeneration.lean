import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.UnitaryRankOne
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The adapted coordinates for a hyperbolic plane and its Hermitian complement. -/

universe u v w

namespace LinearAlgebraicGroups.Specs.HermitianMatrixGeneration

open UnitaryRankOne (quadraticConjugation)

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
variable {W : Type w} [AddCommGroup W] [Module E W]

/-- A Hermitian pairing with the scalar action in the second variable. -/
structure HermitianForm (σ : E ≃ₐ[F] E) where
  pairing : W → W → E
  linear_second : ∀ z, IsLinearMap E (pairing z)
  hermitian : ∀ x y, σ (pairing x y) = pairing y x

variable {σ : E ≃ₐ[F] E} (h : HermitianForm (W := W) σ)

/-- The right kernel of a nondegenerate pairing is zero. -/
def HermitianForm.Nondegenerate : Prop :=
  ∀ x, (∀ y, h.pairing y x = 0) → x = 0

/-- The group of all linear isometries of the complement. -/
def HermitianForm.unitaryGroup : Subgroup (W ≃ₗ[E] W) where
  carrier := {g | ∀ x y, h.pairing (g x) (g y) = h.pairing x y}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb x y => (ha (b x) (b y)).trans (hb x y)
  inv_mem' := fun {a} ha x y => by
    change h.pairing (a.symm x) (a.symm y) = h.pairing x y
    simpa only [LinearEquiv.apply_symm_apply] using (ha (a.symm x) (a.symm y)).symm

/-- The reflection in a nonisotropic line scales it by a norm-one scalar. -/
def HermitianForm.reflectionAction (z : W) (η : E) (x : W) : W :=
  x + ((η - 1) * (h.pairing z x / h.pairing z z)) • z

def HermitianForm.reflections : Set (W ≃ₗ[E] W) :=
  {g | ∃ (z : W) (η : E), h.pairing z z ≠ 0 ∧ η * σ η = 1 ∧
    ∀ x, g x = h.reflectionAction z η x}

/-- Pairing with a fixed vector is an E-linear functional. -/
def HermitianForm.linear (x : W) : W →ₗ[E] E :=
  (h.linear_second x).mk' (h.pairing x)

/-- The common perpendicular space of the two hyperbolic vectors. -/
def HermitianForm.hyperbolicComplement (e f : W) : Submodule E W :=
  (h.linear e).ker ⊓ (h.linear f).ker

/-- Restrict the pairing to a subspace. -/
def HermitianForm.restrict (P : Submodule E W) : HermitianForm (W := P) σ where
  pairing x y := h.pairing x.val y.val
  linear_second x := { map_add := fun y z => (h.linear_second x.val).map_add y.val z.val
                       map_smul := fun c y => (h.linear_second x.val).map_smul c y.val }
  hermitian x y := h.hermitian x.val y.val

/-- The coordinates are the first isotropic line, its Hermitian complement
in the hyperbolic splitting, and the second isotropic line. -/
abbrev Space (E : Type v) (W : Type w) := E × W × E

def hyperbolicPairing (p r : Space E W) : E :=
  σ p.1 * r.2.2 + h.pairing p.2.1 r.2.1 + σ p.2.2 * r.1

/-- The adapted coordinate comparison is the actual sum along the given pair
and the common perpendicular space. -/
def HyperbolicCoordinates : Prop :=
  ∀ {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    {W : Type w} [AddCommGroup W] [Module E W]
    (h : HermitianForm (W := W) (quadraticConjugation F E))
    (e f : W), h.pairing e e = 0 → h.pairing f f = 0 → h.pairing e f = 1 →
    let P := h.hyperbolicComplement e f
    let hP := h.restrict P
    (h.Nondegenerate → hP.Nondegenerate) ∧
    ∃ c : Space E P ≃ₗ[E] W,
      (∀ p, c p = p.1 • e + p.2.1.val + p.2.2 • f) ∧
      ∀ p r, h.pairing (c p) (c r) = hyperbolicPairing hP p r

/-- The determinant-one isometry point group in the adapted coordinates. -/
def specialUnitary : Subgroup (Space E W ≃ₗ[E] Space E W) where
  carrier := {g | LinearEquiv.det g = 1 ∧ ∀ p r, hyperbolicPairing h (g p) (g r) =
    hyperbolicPairing h p r}
  one_mem' := ⟨map_one _, fun _ _ => rfl⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [map_mul, ha.1, hb.1, mul_one],
    fun p r => (ha.2 (b p) (b r)).trans (hb.2 p r)⟩
  inv_mem' := fun {a} ha => ⟨by rw [map_inv, ha.1, inv_one], fun p r => by
    change hyperbolicPairing h (a.symm p) (a.symm r) = hyperbolicPairing h p r
    simpa only [LinearEquiv.apply_symm_apply] using (ha.2 (a.symm p) (a.symm r)).symm⟩

def upperAction (z : W) (b : E) (p : Space E W) : Space E W :=
  (p.1 - h.pairing z p.2.1 + b * p.2.2, p.2.1 + p.2.2 • z, p.2.2)

def lowerAction (z : W) (b : E) (p : Space E W) : Space E W :=
  (p.1, p.2.1 + p.1 • z, p.2.2 - h.pairing z p.2.1 + b * p.1)

/-- The two unitriangular families in the blocks of the hyperbolic splitting. -/
def radicalGenerators : Set (Space E W ≃ₗ[E] Space E W) :=
  {g | ∃ (z : W) (b : E), b + σ b = -h.pairing z z ∧
    ((∀ p, g p = upperAction h z b p) ∨ (∀ p, g p = lowerAction h z b p))}

/-- On the first line, the middle graded piece, and the last graded piece,
an upper block unitriangular map induces the identity. -/
def UpperUnitriangular (g : Space E W ≃ₗ[E] Space E W) : Prop :=
  g (1, 0, 0) = (1, 0, 0) ∧
    (∀ w : W, (g (0, w, 0)).2 = (w, 0)) ∧ (g (0, 0, 1)).2.2 = 1

/-- The lower block condition uses the reversed order of the two outer lines. -/
def LowerUnitriangular (g : Space E W ≃ₗ[E] Space E W) : Prop :=
  g (0, 0, 1) = (0, 0, 1) ∧
    (∀ w : W, ((g (0, w, 0)).1, (g (0, w, 0)).2.1) = (0, w)) ∧
    (g (1, 0, 0)).1 = 1

/-- The coordinate families exhaust the two block unitriangular point groups. -/
def UnitriangularCoordinates : Prop :=
  ∀ {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    {W : Type w} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (h : HermitianForm (W := W) (quadraticConjugation F E))
    (g : Space E W ≃ₗ[E] Space E W),
    g ∈ radicalGenerators h ↔
      g ∈ specialUnitary h ∧ (UpperUnitriangular g ∨ LowerUnitriangular g)

/-- The rank-one diagonal words act on the middle block by the specified
reflection, on the first line by s, and on the second by its conjugate inverse. -/
def RankOneDiagonalWords : Prop :=
  ∀ {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [Infinite F]
    {W : Type w} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (h : HermitianForm (W := W) (quadraticConjugation F E))
    (z : W) (_hz : h.pairing z z ≠ 0) (s : Eˣ),
    let σ := quadraticConjugation F E
    ∃ g ∈ Subgroup.closure (radicalGenerators h), ∀ p : Space E W,
      g p = ((s : E) * p.1, h.reflectionAction z (σ (s : E) / (s : E)) p.2.1,
        (σ (s : E))⁻¹ * p.2.2)

/-- In the presence of a nonzero complement, the two unitriangular families
generate the full determinant-one isometry group. Reflection generation
is the premise on the complement only. -/
def Generation : Prop :=
  ∀ {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [Infinite F]
    {W : Type w} [AddCommGroup W] [Module E W] [FiniteDimensional E W] [Nontrivial W]
    (h : HermitianForm (W := W) (quadraticConjugation F E)),
    h.Nondegenerate →
    (∀ A ∈ h.unitaryGroup, A ∈ Subgroup.closure h.reflections) →
    Subgroup.closure (radicalGenerators h) = specialUnitary h

/-- Generation in the original Hermitian space, with the unitriangular
isometries transported by the prescribed hyperbolic splitting. -/
def GenerationForHyperbolicPair : Prop :=
  ∀ {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [Infinite F]
    {W : Type w} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (h : HermitianForm (W := W) (quadraticConjugation F E))
    (e f : W), h.pairing e e = 0 → h.pairing f f = 0 → h.pairing e f = 1 →
    let P := h.hyperbolicComplement e f
    let hP := h.restrict P
    ∀ [Nontrivial P], h.Nondegenerate →
      (∀ A ∈ hP.unitaryGroup, A ∈ Subgroup.closure hP.reflections) →
      ∃ c : Space E P ≃ₗ[E] W,
        (∀ p, c p = p.1 • e + p.2.1.val + p.2.2 • f) ∧
        Subgroup.closure
          ((fun g => (c.symm.trans g).trans c) '' radicalGenerators hP) =
          h.unitaryGroup ⊓ LinearEquiv.det.ker

end LinearAlgebraicGroups.Specs.HermitianMatrixGeneration
