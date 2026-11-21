import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.Complexes
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Data.Int.Interval

/-!
Canonical interfaces for paper.tex 2377–2414. All module objects are over an
arbitrary unital ring R; use R = Sᵐᵒᵖ for right S-modules. Support is a fixed
translate of the first quadrant. The total uses coproducts, identified below
with algebraic direct sums, never unrestricted products.
-/
namespace P103.Specs.Ch10.TotalComplexAssembly
open CategoryTheory CategoryTheory.Limits DirectSum
noncomputable section
universe u v

set_option backward.isDefEq.respectTransparency false in
/-- Integer chain signs, with the same parity convention as integer cochains. -/
instance downTensorSigns : ComplexShape.TensorSigns (ComplexShape.down ℤ) where
  ε' := MonoidHom.mk' Int.negOnePow Int.negOnePow_add
  rel_add p q r (hpq : q + 1 = p) := by change q + r + 1 = p + r; omega
  add_rel p q r (hpq : q + 1 = p) := by change r + q + 1 = r + p; omega
  ε'_succ := by
    rintro _ q rfl
    change q.negOnePow = -(q + 1).negOnePow
    rw [Int.negOnePow_succ, neg_neg]

instance downTotalSymmetry : TotalComplexShapeSymmetry
    (ComplexShape.down ℤ) (ComplexShape.down ℤ) (ComplexShape.down ℤ) where
  symm p q := add_comm q p
  σ p q := (p * q).negOnePow
  σ_ε₁ := by
    rintro _ p rfl q
    change ((p + 1) * q).negOnePow * 1 = q.negOnePow * (p * q).negOnePow
    rw [mul_one, add_mul, one_mul, Int.negOnePow_add, mul_comm]
  σ_ε₂ := by
    rintro p _ q rfl
    change (p * (q + 1)).negOnePow * p.negOnePow = 1 * (p * q).negOnePow
    rw [one_mul, mul_add, mul_one, Int.negOnePow_add, mul_assoc,
      Int.units_mul_self, mul_one]

variable (R : Type u) [Ring R]

/-- Horizontal degree is the outer index. The two original differentials commute. -/
abbrev Bicomplex (c : ComplexShape ℤ) := HomologicalComplex₂ (ModuleCat.{v} R) c c
abbrev ChainBicomplex := Bicomplex.{u,v} R (ComplexShape.down ℤ)
abbrev CochainBicomplex := Bicomplex.{u,v} R (ComplexShape.up ℤ)

variable {R} {c : ComplexShape ℤ}

/-- All terms outside p ≥ a, q ≥ b vanish; there is no finiteness condition inside. -/
def SupportedQuadrant (K : Bicomplex.{u,v} R c) (a b : ℤ) : Prop :=
  ∀ p q, p < a ∨ q < b → Subsingleton ((K.X p).X q)

/-- Column and row acyclicity use the shared explicit quotient homology. -/
def ColumnsAcyclic (K : Bicomplex.{u,v} R c) : Prop :=
  ∀ p, Complexes.Acyclic (K.X p)

def RowsAcyclic (K : Bicomplex.{u,v} R c) : Prop :=
  ∀ q, Complexes.Acyclic (K.flip.X q)

/-- The finite set of potentially nonzero positions in a total diagonal. -/
def quadrantDiagonal (a b n : ℤ) : Set (ℤ × ℤ) :=
  {i | a ≤ i.1 ∧ b ≤ i.2 ∧ i.1 + i.2 = n}

variable [ComplexShape.TensorSigns c]

/-- The direct-sum total, with horizontal sign 1 and vertical sign c.ε p. -/
def total (K : Bicomplex.{u,v} R c) : HomologicalComplex (ModuleCat.{v} R) c :=
  K.total c

/-- The actual coproduct summands, indexed by p+q=n. -/
abbrev diagonalFamily (K : Bicomplex.{u,v} R c) (n : ℤ)
    (i : {i : ℤ × ℤ // i.1 + i.2 = n}) : ModuleCat.{v} R :=
  (K.X i.val.1).X i.val.2

/-- This explicitly identifies each total term with the algebraic direct sum. -/
def totalTermEquiv (K : Bicomplex.{u,v} R c) (n : ℤ) :
    (total K).X n ≃ₗ[R] (⨁ i : {i : ℤ × ℤ // i.1 + i.2 = n}, diagonalFamily K n i) :=
  (ModuleCat.coprodIsoDirectSum (diagonalFamily K n)).toLinearEquiv

/-- Summand inclusion, with the index equality made explicit. -/
def totalInclusion (K : Bicomplex.{u,v} R c) (p q n : ℤ) (h : p + q = n) :
    (K.X p).X q ⟶ (total K).X n := K.ιTotal c p q n h

/-- The coordinate projection in the algebraic direct sum, transported to the total. -/
def totalProjection (K : Bicomplex.{u,v} R c) (p q n : ℤ) (h : p + q = n) :
    (total K).X n ⟶ (K.X p).X q :=
  ModuleCat.ofHom ((DirectSum.component R _ (fun i => diagonalFamily K n i) ⟨(p, q), h⟩).comp
    (totalTermEquiv K n).toLinearMap)

/-- The finite support of an arbitrary total element, without quadrant hypotheses. -/
def totalSupport (K : Bicomplex.{u,v} R c) (n : ℤ) (x : (total K).X n) :
    Finset {i : ℤ × ℤ // i.1 + i.2 = n} := by
  classical
  exact (totalTermEquiv K n x).support

/-- The signed interchange is a chain/cochain isomorphism. -/
def signedInterchange [TotalComplexShapeSymmetry c c c]
    (K : Bicomplex.{u,v} R c) : total K.flip ≅ total K := K.totalFlipIso c

/-! Anticommuting input, before any signs have been inserted. -/

/-- Columns and horizontal differentials of a genuinely anticommuting bicomplex. -/
structure AnticommutingBicomplex (R : Type u) [Ring R] (c : ComplexShape ℤ) where
  column : ℤ → HomologicalComplex (ModuleCat.{v} R) c
  horizontal : ∀ p p' q, (column p).X q ⟶ (column p').X q
  horizontal_shape : ∀ p p' q, ¬ c.Rel p p' → horizontal p p' q = 0
  horizontal_squared : ∀ p p' p'' q, horizontal p p' q ≫ horizontal p' p'' q = 0
  anticommute : ∀ p p' q q',
    horizontal p p' q ≫ (column p').d q q' =
      -((column p).d q q' ≫ horizontal p p' q')

/-- Original horizontal row, before twisting any vertical differential. -/
def AnticommutingBicomplex.row (A : AnticommutingBicomplex.{u,v} R c) (q : ℤ) :
    HomologicalComplex (ModuleCat.{v} R) c where
  X p := (A.column p).X q
  d p p' := A.horizontal p p' q
  shape p p' h := A.horizontal_shape p p' q h
  d_comp_d' p p' p'' _ _ := A.horizontal_squared p p' p'' q

/-- Multiplying every differential in a column by a single sign. -/
def signedColumn (C : HomologicalComplex (ModuleCat.{v} R) c) (s : ℤˣ) :
    HomologicalComplex (ModuleCat.{v} R) c where
  X := C.X
  d i j := s • C.d i j
  shape i j h := by rw [C.shape i j h, smul_zero]
  d_comp_d' i j k _ _ := by
    simp only [Linear.units_smul_comp, Linear.comp_units_smul,
      C.d_comp_d, smul_zero]

/-- Twisting the vertical maps by (-1)^p turns anticommutation into commutation. -/
def AnticommutingBicomplex.toCommuting (A : AnticommutingBicomplex.{u,v} R c) :
    Bicomplex.{u,v} R c where
  X p := signedColumn (A.column p) (c.ε p)
  d p p' :=
    { f := A.horizontal p p'
      comm' := by
        intro q q' _
        change A.horizontal p p' q ≫ (c.ε p' • (A.column p').d q q') =
          (c.ε p • (A.column p).d q q') ≫ A.horizontal p p' q'
        by_cases h : c.Rel p p'
        · rw [Linear.comp_units_smul, Linear.units_smul_comp,
            A.anticommute, c.ε_succ h, Units.neg_smul, smul_neg, neg_neg]
        · rw [A.horizontal_shape p p' q h, A.horizontal_shape p p' q' h,
            zero_comp, comp_zero] }
  shape p p' h := by
    apply HomologicalComplex.Hom.ext
    funext q
    exact A.horizontal_shape p p' q h
  d_comp_d' p p' p'' _ _ := by
    apply HomologicalComplex.Hom.ext
    funext q
    exact A.horizontal_squared p p' p'' q

/-- Signed totalization of the twisted input has ordinary differential dh+dv. -/
def AnticommutingBicomplex.total (A : AnticommutingBicomplex.{u,v} R c) :
    HomologicalComplex (ModuleCat.{v} R) c := P103.Specs.Ch10.TotalComplexAssembly.total A.toCommuting

/-! Full expected theorem propositions. No assembly conclusion is assumed. -/

set_option linter.unusedVariables false
set_option linter.checkUnivs false

def quadrantDiagonal_finiteType : Prop :=
  ∀ a b n : ℤ, (quadrantDiagonal a b n).Finite

/-! Expected types and canonical values for the constructions. -/

abbrev BicomplexValue := @Bicomplex.{u,v}

def BicomplexType := ∀ (R : Type u) [Ring R], ComplexShape ℤ → Type (max u (v + 1))

abbrev ChainBicomplexValue := @ChainBicomplex.{u,v}

def ChainBicomplexType := ∀ (R : Type u) [Ring R], Type (max u (v + 1))

abbrev CochainBicomplexValue := @CochainBicomplex.{u,v}

def CochainBicomplexType := ∀ (R : Type u) [Ring R], Type (max u (v + 1))

abbrev SupportedQuadrantValue := @SupportedQuadrant.{u,v}

def SupportedQuadrantType := ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ}, Bicomplex.{u,v} R c → ℤ → ℤ → Prop

abbrev ColumnsAcyclicValue := @ColumnsAcyclic.{u,v}

def ColumnsAcyclicType := ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ}, Bicomplex.{u,v} R c → Prop

abbrev RowsAcyclicValue := @RowsAcyclic.{u,v}

def RowsAcyclicType := ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ}, Bicomplex.{u,v} R c → Prop

abbrev quadrantDiagonalValue := @quadrantDiagonal

def quadrantDiagonalType := ℤ → ℤ → ℤ → Set (ℤ × ℤ)

abbrev totalValue := @total.{u,v}

def totalType := ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c], Bicomplex.{u,v} R c → HomologicalComplex (ModuleCat.{v} R) c

abbrev diagonalFamilyValue := @diagonalFamily.{u,v}

def diagonalFamilyType := ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} (K : Bicomplex.{u,v} R c) (n : ℤ), {i : ℤ × ℤ // i.1 + i.2 = n} → ModuleCat.{v} R

abbrev totalTermEquivValue := @totalTermEquiv.{u,v}

def totalTermEquivType := ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c] (K : Bicomplex.{u,v} R c) (n : ℤ), (total K).X n ≃ₗ[R] (⨁ i : {i : ℤ × ℤ // i.1 + i.2 = n}, diagonalFamily K n i)

abbrev totalInclusionValue := @totalInclusion.{u,v}

def totalInclusionType := ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c] (K : Bicomplex.{u,v} R c) (p q n : ℤ) (h : p + q = n), (K.X p).X q ⟶ (total K).X n

abbrev totalProjectionValue := @totalProjection.{u,v}

def totalProjectionType := ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c] (K : Bicomplex.{u,v} R c) (p q n : ℤ) (h : p + q = n), (total K).X n ⟶ (K.X p).X q

abbrev totalSupportValue := @totalSupport.{u,v}

def totalSupportType := ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c] (K : Bicomplex.{u,v} R c) (n : ℤ) (x : (total K).X n), Finset {i : ℤ × ℤ // i.1 + i.2 = n}

abbrev signedInterchangeValue := @signedInterchange.{u,v}

def signedInterchangeType := ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c] [TotalComplexShapeSymmetry c c c] (K : Bicomplex.{u,v} R c), total K.flip ≅ total K

abbrev AnticommutingBicomplexValue := @AnticommutingBicomplex.{u,v}

def AnticommutingBicomplexType := ∀ (R : Type u) [Ring R], ComplexShape ℤ → Type (max u (v + 1))

abbrev signedColumnValue := @signedColumn.{u,v}

def signedColumnType := ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} (C : HomologicalComplex (ModuleCat.{v} R) c) (s : ℤˣ), HomologicalComplex (ModuleCat.{v} R) c

abbrev anticommutingToCommutingValue := @AnticommutingBicomplex.toCommuting.{u,v}

def anticommutingToCommutingType := ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c], AnticommutingBicomplex.{u,v} R c → Bicomplex.{u,v} R c

abbrev anticommutingTotalValue := @AnticommutingBicomplex.total.{u,v}

def anticommutingTotalType := ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c], AnticommutingBicomplex.{u,v} R c → HomologicalComplex (ModuleCat.{v} R) c

/-! Remaining expected theorem types. -/

abbrev anticommutingToCommuting := @AnticommutingBicomplex.toCommuting.{u,v}
abbrev anticommutingTotal := @AnticommutingBicomplex.total.{u,v}

def totalInclusion_dType : Prop :=
  ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c] (K : Bicomplex.{u,v} R c) (p q n m : ℤ) (h : p + q = n),
    totalInclusion K p q n h ≫ (total K).d n m =
      (K.d p (c.next p)).f q ≫ K.ιTotalOrZero c (c.next p) q m +
        c.ε p • ((K.X p).d q (c.next q) ≫ K.ιTotalOrZero c p (c.next q) m)

def chain_totalInclusion_dType : Prop :=
  ∀ {R : Type u} [Ring R] (K : ChainBicomplex.{u,v} R) (p q n m : ℤ)
    (h : p + q = n),
    totalInclusion K p q n h ≫ (total K).d n m =
      (K.d p (p - 1)).f q ≫ K.ιTotalOrZero (ComplexShape.down ℤ) (p - 1) q m +
      p.negOnePow • ((K.X p).d q (q - 1) ≫
        K.ιTotalOrZero (ComplexShape.down ℤ) p (q - 1) m)

def cochain_totalInclusion_dType : Prop :=
  ∀ {R : Type u} [Ring R] (K : CochainBicomplex.{u,v} R) (p q n m : ℤ)
    (h : p + q = n),
    totalInclusion K p q n h ≫ (total K).d n m =
      (K.d p (p + 1)).f q ≫ K.ιTotalOrZero (ComplexShape.up ℤ) (p + 1) q m +
      p.negOnePow • ((K.X p).d q (q + 1) ≫
        K.ιTotalOrZero (ComplexShape.up ℤ) p (q + 1) m)

def total_squaredType : Prop :=
  ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c] (K : Bicomplex.{u,v} R c) (i j k : ℤ),
    ((total K).d j k).hom.comp ((total K).d i j).hom = 0

def totalTermEquiv_inclusionType : Prop :=
  ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c] (K : Bicomplex.{u,v} R c) (p q n : ℤ)
    (h : p + q = n) (x : (K.X p).X q),
    totalTermEquiv K n ((totalInclusion K p q n h).hom x) =
      DirectSum.lof R _ (fun i => diagonalFamily K n i) ⟨(p, q), h⟩ x

def totalInclusion_projection_selfType : Prop :=
  ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c]
    (K : Bicomplex.{u,v} R c) (p q n : ℤ) (h : p + q = n),
    totalInclusion K p q n h ≫ totalProjection K p q n h = 𝟙 _

def totalInclusion_projection_neType : Prop :=
  ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c]
    (K : Bicomplex.{u,v} R c) (p q p' q' n : ℤ) (h : p + q = n)
    (h' : p' + q' = n) (hne : p ≠ p' ∨ q ≠ q'),
    totalInclusion K p q n h ≫ totalProjection K p' q' n h' = 0

def total_extType : Prop :=
  ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c]
    (K : Bicomplex.{u,v} R c) (n : ℤ) (x y : (total K).X n)
    (h : ∀ p q (hpq : p + q = n),
      (totalProjection K p q n hpq).hom x = (totalProjection K p q n hpq).hom y),
    x = y

def total_reconstructionType : Prop :=
  ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c]
    (K : Bicomplex.{u,v} R c) (n : ℤ) (x : (total K).X n),
    ∑ i ∈ totalSupport K n x,
      (totalInclusion K i.val.1 i.val.2 n i.property).hom
        ((totalProjection K i.val.1 i.val.2 n i.property).hom x) = x

def total_hom_extType : Prop :=
  ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c]
    (K : Bicomplex.{u,v} R c) (n : ℤ) {M : ModuleCat.{v} R}
    {f g : (total K).X n ⟶ M}
    (h : ∀ p q (hpq : p + q = n),
      totalInclusion K p q n hpq ≫ f = totalInclusion K p q n hpq ≫ g),
    f = g

def chain_totalProjection_dType : Prop :=
  ∀ {R : Type u} [Ring R] (K : ChainBicomplex.{u,v} R) (p q n : ℤ)
    (h : p + q = n - 1),
    (total K).d n (n - 1) ≫ totalProjection K p q (n - 1) h =
      totalProjection K (p + 1) q n (by omega) ≫ (K.d (p + 1) p).f q +
      p.negOnePow • (totalProjection K p (q + 1) n (by omega) ≫ (K.X p).d (q + 1) q)

def cochain_totalProjection_dType : Prop :=
  ∀ {R : Type u} [Ring R] (K : CochainBicomplex.{u,v} R) (p q n : ℤ)
    (h : p + q = n + 1),
    (total K).d n (n + 1) ≫ totalProjection K p q (n + 1) h =
      totalProjection K (p - 1) q n (by omega) ≫ (K.d (p - 1) p).f q +
      p.negOnePow • (totalProjection K p (q - 1) n (by omega) ≫ (K.X p).d (q - 1) q)

def total_supportedBelowType : Prop :=
  ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c] (K : Bicomplex.{u,v} R c) (a b : ℤ)
    (hs : SupportedQuadrant K a b) (n : ℤ) (hn : n < a + b),
    Subsingleton ((total K).X n)

def signedInterchange_chainType : Prop :=
  ∀ {R : Type u} [Ring R] (K : ChainBicomplex.{u,v} R) (p q n : ℤ)
    (h : q + p = n),
    K.flip.ιTotal (ComplexShape.down ℤ) q p n h ≫
        (signedInterchange K).hom.f n =
      (p * q).negOnePow • K.ιTotal (ComplexShape.down ℤ) p q n (by change p + q = n; omega)

def signedInterchange_cochainType : Prop :=
  ∀ {R : Type u} [Ring R] (K : CochainBicomplex.{u,v} R) (p q n : ℤ)
    (h : q + p = n),
    K.flip.ιTotal (ComplexShape.up ℤ) q p n h ≫
        (signedInterchange K).hom.f n =
      (p * q).negOnePow • K.ιTotal (ComplexShape.up ℤ) p q n (by change p + q = n; omega)

def anticommutingTotal_dType : Prop :=
  ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c] (A : AnticommutingBicomplex.{u,v} R c)
    (p q n m : ℤ) (h : p + q = n),
    totalInclusion (anticommutingToCommuting A) p q n h ≫
        (anticommutingTotal A).d n m =
      A.horizontal p (c.next p) q ≫
        (anticommutingToCommuting A).ιTotalOrZero c (c.next p) q m +
      (A.column p).d q (c.next q) ≫
        (anticommutingToCommuting A).ιTotalOrZero c p (c.next q) m

def acyclic_of_isoType : Prop :=
  ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} {C D : HomologicalComplex (ModuleCat.{v} R) c}
    (e : C ≅ D) (hC : Complexes.Acyclic C),
    Complexes.Acyclic D

def signedColumn_cyclesType : Prop :=
  ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} (C : HomologicalComplex (ModuleCat.{v} R) c) (s : ℤˣ)
    (n : ℤ),
    Complexes.cycles (signedColumn C s) n = Complexes.cycles C n

def signedColumn_boundariesType : Prop :=
  ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} (C : HomologicalComplex (ModuleCat.{v} R) c) (s : ℤˣ)
    (n : ℤ),
    Complexes.boundaries (signedColumn C s) n = Complexes.boundaries C n

def signedColumn_acyclic_iffType : Prop :=
  ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} (C : HomologicalComplex (ModuleCat.{v} R) c) (s : ℤˣ),
    Complexes.Acyclic (signedColumn C s) ↔ Complexes.Acyclic C

def anticommuting_columns_acyclic_iffType : Prop :=
  ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c] (A : AnticommutingBicomplex.{u,v} R c),
    ColumnsAcyclic (anticommutingToCommuting A) ↔
      ∀ p, Complexes.Acyclic (A.column p)

def anticommuting_rows_acyclic_iffType : Prop :=
  ∀ {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c] (A : AnticommutingBicomplex.{u,v} R c),
    RowsAcyclic (anticommutingToCommuting A) ↔
      ∀ q, Complexes.Acyclic (A.row q)

end
end P103.Specs.Ch10.TotalComplexAssembly
