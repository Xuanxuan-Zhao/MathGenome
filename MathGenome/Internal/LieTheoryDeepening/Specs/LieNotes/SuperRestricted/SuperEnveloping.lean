import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.SuperLie
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Abel

/-! The enveloping quotient and its filtrations, before any PBW theorem. -/

namespace LieNotes.SuperRestricted.SuperEnveloping.Construction

open scoped DirectSum

universe u v w

noncomputable section

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]

/-- The signed relator, with the bracket included in tensor degree one. -/
def relator [NeZero (2 : k)] (L : LieSuperalgebra k V)
    (i j : ZMod 2) (x y : V) : TensorAlgebra k V :=
  TensorAlgebra.ι k x * TensorAlgebra.ι k y -
    paritySign k i j • (TensorAlgebra.ι k y * TensorAlgebra.ι k x) -
    TensorAlgebra.ι k (L.bracket x y)

/-- All signed relators for homogeneous pairs. -/
def relations [NeZero (2 : k)] (L : LieSuperalgebra k V) : Set (TensorAlgebra k V) :=
  {r | ∃ (i j : ZMod 2) (x y : V), x ∈ L.grading.piece i ∧ y ∈ L.grading.piece j ∧
    r = relator L i j x y}

abbrev relationIdeal [NeZero (2 : k)] (L : LieSuperalgebra k V) :=
  TwoSidedIdeal.span (relations L)

/-- The associative quotient by the two-sided relation ideal. -/
abbrev Enveloping [NeZero (2 : k)] (L : LieSuperalgebra k V) :=
  (relationIdeal L).ringCon.Quotient

abbrev quotientMap [NeZero (2 : k)] (L : LieSuperalgebra k V) :
    TensorAlgebra k V →ₐ[k] Enveloping L :=
  (relationIdeal L).ringCon.mkₐ k

def ι [NeZero (2 : k)] (L : LieSuperalgebra k V) : V →ₗ[k] Enveloping L :=
  (quotientMap L).toLinearMap.comp (TensorAlgebra.ι k)

/-- The character of the parity group with values in the base field. -/
def parityScalar (k : Type u) [Field k] (i : ZMod 2) : k :=
  if i = 0 then 1 else -1

private theorem parity_cases (i : ZMod 2) : i = 0 ∨ i = 1 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem parityScalar_add (i j : ZMod 2) :
    parityScalar k (i + j) = parityScalar k i * parityScalar k j := by
  rcases parity_cases i with rfl | rfl <;> rcases parity_cases j with rfl | rfl <;>
    simp [parityScalar, show (1 : ZMod 2) ≠ 0 by decide, show (1 : ZMod 2) + 1 = 0 by decide]

theorem parityScalar_sq (i : ZMod 2) : parityScalar k i * parityScalar k i = 1 := by
  rcases parity_cases i with rfl | rfl <;>
    simp [parityScalar, show (1 : ZMod 2) ≠ 0 by decide]

/-- The linear sign operator obtained by multiplying each homogeneous summand by its sign. -/
def generatorParity (G : Grading k V) : V →ₗ[k] V :=
  (DirectSum.toModule k (ZMod 2) V
    (fun i => parityScalar k i • (G.piece i).subtype)).comp
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap G.piece) G.isInternal).symm.toLinearMap

theorem generatorParity_apply (G : Grading k V) {i : ZMod 2} {x : V} (hx : x ∈ G.piece i) :
    generatorParity G x = parityScalar k i • x := by
  let x' : G.piece i := ⟨x, hx⟩
  change generatorParity G (x' : V) = parityScalar k i • (x' : V)
  have h : (LinearEquiv.ofBijective (DirectSum.coeLinearMap G.piece) G.isInternal).symm
      (x' : V) = DirectSum.lof k (ZMod 2) (fun j => ↥(G.piece j)) i x' := by
    apply (LinearEquiv.ofBijective (DirectSum.coeLinearMap G.piece) G.isInternal).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (DirectSum.coeLinearMap_lof G.piece i x').symm
  simp [generatorParity, h]

/-- The parity involution on the tensor algebra extends the sign operator on generators. -/
def tensorParity (G : Grading k V) : TensorAlgebra k V →ₐ[k] TensorAlgebra k V :=
  TensorAlgebra.lift k ((TensorAlgebra.ι k).comp (generatorParity G))

theorem tensorParity_ι (G : Grading k V) {i : ZMod 2} {x : V} (hx : x ∈ G.piece i) :
    tensorParity G (TensorAlgebra.ι k x) = parityScalar k i • TensorAlgebra.ι k x := by
  simp [tensorParity, generatorParity_apply G hx]

theorem tensorParity_involutive (G : Grading k V) : Function.Involutive (tensorParity G) := by
  have heq : (tensorParity G).comp (tensorParity G) = AlgHom.id k (TensorAlgebra k V) := by
    apply TensorAlgebra.hom_ext
    have htop := G.isInternal.submodule_iSup_eq_top
    apply LinearMap.ext_on (s := ⋃ i, (G.piece i : Set V))
    · rw [Submodule.span_iUnion]
      simpa using htop
    · intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      change tensorParity G (tensorParity G (TensorAlgebra.ι k x)) = TensorAlgebra.ι k x
      rw [tensorParity_ι G hxi, map_smul, tensorParity_ι G hxi, smul_smul,
        parityScalar_sq, one_smul]
  intro x
  exact DFunLike.congr_fun heq x

variable [NeZero (2 : k)] (L : LieSuperalgebra k V)

theorem tensorParity_relator {i j : ZMod 2} {x y : V}
    (hx : x ∈ L.grading.piece i) (hy : y ∈ L.grading.piece j) :
    tensorParity L.grading (relator L i j x y) = parityScalar k (i+j) • relator L i j x y := by
  simp only [relator, map_sub, map_mul, map_smul, tensorParity_ι _ hx, tensorParity_ι _ hy,
    tensorParity_ι _ (L.bracket_mem hx hy), parityScalar_add, smul_sub,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  simp only [mul_comm]

theorem quotientMap_eq_zero_iff (x : TensorAlgebra k V) :
    quotientMap L x = 0 ↔ x ∈ relationIdeal L := by
  change (relationIdeal L).ringCon.mk' x = 0 ↔ _
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']

private theorem parity_descent :
    (relationIdeal L).ringCon ≤ RingCon.ker ((quotientMap L).comp (tensorParity L.grading)).toRingHom := by
  change (relationIdeal L).ringCon ≤ (TwoSidedIdeal.ker
    ((quotientMap L).comp (tensorParity L.grading))).ringCon
  apply TwoSidedIdeal.ringCon_le_iff.mp
  apply TwoSidedIdeal.span_le.mpr
  rintro x ⟨i, j, a, b, ha, hb, rfl⟩
  apply (TwoSidedIdeal.mem_ker ((quotientMap L).comp (tensorParity L.grading))).mpr
  change (quotientMap L).comp (tensorParity L.grading) (relator L i j a b) = 0
  rw [AlgHom.comp_apply, tensorParity_relator L ha hb, map_smul,
    (quotientMap_eq_zero_iff L _).mpr (TwoSidedIdeal.subset_span ⟨i, j, a, b, ha, hb, rfl⟩),
    smul_zero]

/-- The sign operator induced on the enveloping quotient. -/
def parity : Enveloping L →ₐ[k] Enveloping L :=
  (relationIdeal L).ringCon.liftₐ ((quotientMap L).comp (tensorParity L.grading))
    (parity_descent L)

@[simp] theorem parity_quotientMap (x : TensorAlgebra k V) :
    parity L (quotientMap L x) = quotientMap L (tensorParity L.grading x) := rfl

theorem parity_involutive : Function.Involutive (parity L) := by
  intro x
  obtain ⟨t, rfl⟩ := (relationIdeal L).ringCon.mkₐ_surjective (α := k) x
  rw [parity_quotientMap, parity_quotientMap, tensorParity_involutive]

section Eigenpieces

variable {M : Type w} [AddCommGroup M] [Module k M]

/-- Degree i consists of the vectors on which the sign operator acts by the sign of i. -/
def paritySpace (s : M →ₗ[k] M) (i : ZMod 2) : Submodule k M :=
  (s - parityScalar k i • LinearMap.id).ker

omit [NeZero (2 : k)] in
theorem mem_paritySpace (s : M →ₗ[k] M) (i : ZMod 2) (a : M) :
    a ∈ paritySpace s i ↔ s a = parityScalar k i • a := by
  simp [paritySpace, sub_eq_zero]

theorem paritySpace_internal (s : M →ₗ[k] M) (hs : Function.Involutive s) :
    DirectSum.IsInternal (paritySpace s) := by
  have hn : (1 : ZMod 2) ≠ 0 := by decide
  apply (DirectSum.isInternal_submodule_iff_isCompl (paritySpace s)
    (i := 0) (j := 1) (Ne.symm hn) ?_).mpr
  · refine ⟨?_, ?_⟩
    · rw [disjoint_iff_inf_le]
      rintro a ⟨he, ho⟩
      have hz : a = -a := by
        have he' := (mem_paritySpace ..).mp he
        have ho' := (mem_paritySpace ..).mp ho
        simpa [parityScalar, hn] using he'.symm.trans ho'
      rw [Submodule.mem_bot]
      apply (smul_eq_zero_iff_right (NeZero.ne (2 : k))).mp
      rw [← sub_eq_zero] at hz
      simpa only [two_smul, sub_neg_eq_add] using hz
    · rw [codisjoint_iff_le_sup]
      intro x _
      refine Submodule.mem_sup.mpr ⟨(2 : k)⁻¹ • (x + s x), ?_, (2 : k)⁻¹ • (x - s x), ?_, ?_⟩
      · simp [mem_paritySpace, parityScalar, hs x, add_comm]
      · rw [mem_paritySpace, map_smul, map_sub, hs x]
        simp only [parityScalar, hn, ite_false, neg_one_smul, ← smul_neg, neg_sub]
      · rw [← smul_add, show x + s x + (x - s x) = x + x by abel,
          ← two_smul k, smul_smul, inv_mul_cancel₀ (NeZero.ne (2 : k)), one_smul]
  · ext i
    rcases parity_cases i with rfl | rfl <;> simp

variable {A : Type w} [Ring A] [Algebra k A]

omit [NeZero (2 : k)] in
theorem paritySpace_mul {s : A →ₐ[k] A} {i j : ZMod 2} {a b : A}
    (ha : a ∈ paritySpace s.toLinearMap i) (hb : b ∈ paritySpace s.toLinearMap j) :
    a * b ∈ paritySpace s.toLinearMap (i+j) := by
  have ha' : s a = parityScalar k i • a := (mem_paritySpace ..).mp ha
  have hb' : s b = parityScalar k j • b := (mem_paritySpace ..).mp hb
  apply (mem_paritySpace ..).mpr
  change s (a * b) = _
  rw [map_mul, ha', hb', smul_mul_assoc, mul_smul_comm, smul_smul, parityScalar_add]

end Eigenpieces

/-- The parity piece in the tensor algebra. A homogeneous letter has its original parity. -/
abbrev tensorPiece (G : Grading k V) := paritySpace (tensorParity G).toLinearMap

/-- The parity piece in the enveloping algebra. -/
abbrev piece := paritySpace (parity L).toLinearMap

omit [NeZero (2 : k)] in
instance tensorGradedMonoid (G : Grading k V) : SetLike.GradedMonoid (tensorPiece G) where
  one_mem := by simp [tensorPiece, mem_paritySpace, parityScalar]
  mul_mem := by
    intro i j a b ha hb
    exact paritySpace_mul ha hb

instance envelopingGradedMonoid : SetLike.GradedMonoid (piece L) where
  one_mem := by simp [piece, mem_paritySpace, parityScalar]
  mul_mem := by
    intro i j a b ha hb
    exact paritySpace_mul ha hb

instance tensorGradedAlgebra (G : Grading k V) : GradedAlgebra (tensorPiece G) :=
  (paritySpace_internal (tensorParity G).toLinearMap (tensorParity_involutive G)).gradedAlgebra

instance envelopingGradedAlgebra : GradedAlgebra (piece L) :=
  (paritySpace_internal (parity L).toLinearMap (parity_involutive L)).gradedAlgebra

section WordFiltration

open scoped Pointwise

variable {A : Type w} [Ring A] [Algebra k A]

/-- The product in the given order, with the empty word evaluated at one. -/
def word (f : V →ₗ[k] A) (xs : List V) : A :=
  (xs.map f).prod

/-- The span of products of at most n generators, with zero in negative degrees. -/
def wordFiltration (f : V →ₗ[k] A) (n : ℤ) : Submodule k A :=
  Submodule.span k {a | ∃ xs : List V, (xs.length : ℤ) ≤ n ∧ a = word f xs}

omit [NeZero (2 : k)] in
theorem word_mem (f : V →ₗ[k] A) {n : ℤ} {xs : List V} (hx : (xs.length : ℤ) ≤ n) :
    word f xs ∈ wordFiltration f n :=
  Submodule.subset_span ⟨xs, hx, rfl⟩

omit [NeZero (2 : k)] in
theorem wordFiltration_mono (f : V →ₗ[k] A) : Monotone (wordFiltration f) := by
  intro m n h
  apply Submodule.span_mono
  rintro a ⟨xs, hx, rfl⟩
  exact ⟨xs, hx.trans h, rfl⟩

omit [NeZero (2 : k)] in
theorem wordFiltration_negative (f : V →ₗ[k] A) {n : ℤ} (hn : n < 0) :
    wordFiltration f n = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro a ⟨xs, hx, rfl⟩
  omega

omit [NeZero (2 : k)] in
theorem wordFiltration_mul (f : V →ₗ[k] A) {m n : ℤ} {a b : A}
    (ha : a ∈ wordFiltration f m) (hb : b ∈ wordFiltration f n) :
    a * b ∈ wordFiltration f (m + n) := by
  suffices wordFiltration f m * wordFiltration f n ≤ wordFiltration f (m + n) from
    this (Submodule.mul_mem_mul ha hb)
  rw [wordFiltration, wordFiltration, Submodule.span_mul_span]
  apply Submodule.span_le.mpr
  rintro a ⟨x, ⟨xs, hx, rfl⟩, y, ⟨ys, hy, rfl⟩, rfl⟩
  have h : ((xs ++ ys).length : ℤ) ≤ m + n := by simpa using add_le_add hx hy
  simpa [word] using word_mem f h

omit [NeZero (2 : k)] in
theorem wordFiltration_algebraMap (f : V →ₗ[k] A) (r : k) :
    algebraMap k A r ∈ wordFiltration f 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ (word_mem f (xs := []) (by simp))

omit [NeZero (2 : k)] in
theorem wordFiltration_generator (f : V →ₗ[k] A) (x : V) : f x ∈ wordFiltration f 1 := by
  simpa [word] using word_mem f (xs := [x]) (n := 1) (by simp)

end WordFiltration

/-- The word-length filtration of the enveloping algebra. -/
abbrev filtration := wordFiltration (ι L)

/-- The parity part of a word-length filtration step. -/
def filteredPiece (n : ℤ) (i : ZMod 2) : Submodule k (Enveloping L) :=
  filtration L n ⊓ piece L i

/-- A pair of word degree and parity. -/
abbrev Degree := ℕ × ZMod 2

abbrev filtered (d : Degree) : Submodule k (Enveloping L) :=
  filteredPiece L d.1 d.2

private theorem filtered_mul (d e : Degree) (x : filtered L d) (y : filtered L e) :
    x.1 * y.1 ∈ filtered L (d + e) := by
  rcases x.2 with ⟨hx, hx'⟩
  rcases y.2 with ⟨hy, hy'⟩
  exact ⟨by simpa using wordFiltration_mul (ι L) hx hy, paritySpace_mul hx' hy'⟩

/-- The preceding step, taken as a submodule of the current parity and length step. -/
def lower (d : Degree) : Submodule k (filtered L d) :=
  (filtration L ((d.1 : ℤ) - 1)).comap (filtered L d).subtype

/-- The actual successive quotient at a given word degree and parity. -/
abbrev GradedPiece (d : Degree) := (filtered L d) ⧸ lower L d

instance gradedPieceAddCommGroup (d : Degree) : AddCommGroup (GradedPiece L d) :=
  Submodule.Quotient.addCommGroup (lower L d)

instance gradedPieceModule (d : Degree) : Module k (GradedPiece L d) :=
  Submodule.Quotient.module (lower L d)

/-- Principal symbol in the corresponding successive quotient. -/
abbrev symbol (d : Degree) : filtered L d →ₗ[k] GradedPiece L d := (lower L d).mkQ

private def filteredProduct (d e : Degree) :
    filtered L d →ₗ[k] filtered L e →ₗ[k] filtered L (d + e) where
  toFun x := ((LinearMap.mul k (Enveloping L) x.1).comp (filtered L e).subtype).codRestrict
    (filtered L (d + e)) (filtered_mul L d e x)
  map_add' x y := by
    ext z
    exact add_mul x.1 y.1 z.1
  map_smul' r x := by
    ext z
    exact smul_mul_assoc r x.1 z.1

private theorem filteredProduct_lower_left (d e : Degree) (x : filtered L d)
    (hx : x ∈ lower L d) (y : filtered L e) : filteredProduct L d e x y ∈ lower L (d + e) := by
  change x.1 * y.1 ∈ filtration L (((d + e).1 : ℤ) - 1)
  have h := wordFiltration_mul (ι L) (show x.1 ∈ filtration L ((d.1 : ℤ) - 1) from hx) y.2.1
  simpa [sub_add_eq_add_sub] using h

private theorem filteredProduct_lower_right (d e : Degree) (x : filtered L d)
    (y : filtered L e) (hy : y ∈ lower L e) : filteredProduct L d e x y ∈ lower L (d + e) := by
  change x.1 * y.1 ∈ filtration L (((d + e).1 : ℤ) - 1)
  have h := wordFiltration_mul (ι L) x.2.1 (show y.1 ∈ filtration L ((e.1 : ℤ) - 1) from hy)
  simpa [Int.add_sub_assoc] using h

/-- The product of two symbols, induced by multiplication of representatives in U. -/
def gradedProduct (d e : Degree) : GradedPiece L d →ₗ[k] GradedPiece L e →ₗ[k]
    GradedPiece L (d + e) :=
  ((filteredProduct L d e).compr₂ (symbol L (d + e))).liftQ₂ (lower L d) (lower L e)
    (fun x hx => LinearMap.mem_ker.mpr (LinearMap.ext fun y => by
      change Submodule.Quotient.mk (filteredProduct L d e x y) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact filteredProduct_lower_left L d e x hx y))
    (fun y hy => LinearMap.mem_ker.mpr (LinearMap.ext fun x => by
      change Submodule.Quotient.mk (filteredProduct L d e x y) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact filteredProduct_lower_right L d e x y hy))

@[simp] theorem gradedProduct_symbol {d e : Degree} (x : filtered L d) (y : filtered L e) :
    gradedProduct L d e (symbol L d x) (symbol L e y) =
    symbol L (d + e) ⟨x.1 * y.1, filtered_mul L d e x y⟩ := rfl

/-- Scalars sit in degree zero and even parity of the filtration. -/
def filteredScalar (r : k) : filtered L 0 :=
  ⟨algebraMap k (Enveloping L) r, wordFiltration_algebraMap (ι L) r, by
    simp [piece, mem_paritySpace, parityScalar]⟩

private theorem sigma_symbol_eq {d e : Degree} {x : filtered L d} {y : filtered L e}
    (h : d = e) (hxy : (x : Enveloping L) = y) :
    GradedMonoid.mk d (symbol L d x) = GradedMonoid.mk e (symbol L e y) := by
  subst e
  cases Subtype.ext hxy
  rfl

instance gradedPieceMul : GradedMonoid.GMul (GradedPiece L) :=
  ⟨fun {d e} x y => gradedProduct L d e x y⟩

instance gradedPieceOne : GradedMonoid.GOne (GradedPiece L) :=
  ⟨symbol L 0 (filteredScalar L 1)⟩

/-- The graded ring of successive quotients with the product on symbols. -/
instance gradedPieceRing : DirectSum.GRing (GradedPiece L) where
  toGMul := gradedPieceMul L
  toGOne := gradedPieceOne L
  mul_zero x := map_zero (gradedProduct L _ _ x)
  zero_mul y := by
    change gradedProduct L _ _ 0 y = 0
    rw [map_zero]
    rfl
  mul_add x y z := map_add (gradedProduct L _ _ x) y z
  add_mul x y z := by
    change gradedProduct L _ _ (x + y) z = gradedProduct L _ _ x z + gradedProduct L _ _ y z
    rw [map_add]
    rfl
  one_mul := by
    rintro ⟨d, a⟩
    obtain ⟨x, rfl⟩ := (lower L d).mkQ_surjective a
    change GradedMonoid.mk _ (gradedProduct L 0 d (symbol L 0 (filteredScalar L 1))
      (symbol L d x)) = GradedMonoid.mk _ (symbol L d x)
    rw [gradedProduct_symbol]
    exact sigma_symbol_eq L (zero_add d) (by simp [filteredScalar])
  mul_one := by
    rintro ⟨d, a⟩
    obtain ⟨x, rfl⟩ := (lower L d).mkQ_surjective a
    change GradedMonoid.mk _ (gradedProduct L d 0 (symbol L d x)
      (symbol L 0 (filteredScalar L 1))) = GradedMonoid.mk _ (symbol L d x)
    rw [gradedProduct_symbol]
    exact sigma_symbol_eq L (add_zero d) (by simp [filteredScalar])
  mul_assoc := by
    rintro ⟨d, a⟩ ⟨e, b⟩ ⟨f, c⟩
    obtain ⟨x, rfl⟩ := (lower L d).mkQ_surjective a
    obtain ⟨y, rfl⟩ := (lower L e).mkQ_surjective b
    obtain ⟨z, rfl⟩ := (lower L f).mkQ_surjective c
    change GradedMonoid.mk _ (gradedProduct L (d + e) f
      (gradedProduct L d e (symbol L d x) (symbol L e y)) (symbol L f z)) =
      GradedMonoid.mk _ (gradedProduct L d (e + f) (symbol L d x)
        (gradedProduct L e f (symbol L e y) (symbol L f z)))
    simp only [gradedProduct_symbol]
    exact sigma_symbol_eq L (add_assoc d e f) (mul_assoc x.1 y.1 z.1)
  natCast n := n • symbol L 0 (filteredScalar L 1)
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ _
  intCast n := n • symbol L 0 (filteredScalar L 1)
  intCast_ofNat n := natCast_zsmul _ _
  intCast_negSucc_ofNat n := negSucc_zsmul _ _

/-- The graded algebra structure over the original ground field. -/
instance gradedPieceAlgebra : DirectSum.GAlgebra k (GradedPiece L) where
  toFun :=
    { toFun := fun r => symbol L 0 (filteredScalar L r)
      map_zero' := by
        rw [← map_zero (symbol L 0)]
        apply congrArg (symbol L 0)
        apply Subtype.ext
        change algebraMap k (Enveloping L) 0 = 0
        exact map_zero _
      map_add' r t := by
        rw [← map_add (symbol L 0)]
        exact congrArg (symbol L 0) (Subtype.ext (map_add (algebraMap k (Enveloping L)) r t)) }
  map_one := rfl
  map_mul r t := by
    change GradedMonoid.mk _ (symbol L 0 (filteredScalar L (r * t))) =
      GradedMonoid.mk _ (gradedProduct L 0 0 (symbol L 0 (filteredScalar L r))
        (symbol L 0 (filteredScalar L t)))
    rw [gradedProduct_symbol]
    exact sigma_symbol_eq L (zero_add 0).symm (map_mul (algebraMap k (Enveloping L)) r t)
  commutes := by
    rintro r ⟨d, a⟩
    obtain ⟨x, rfl⟩ := (lower L d).mkQ_surjective a
    change GradedMonoid.mk _ (gradedProduct L 0 d (symbol L 0 (filteredScalar L r))
        (symbol L d x)) =
      GradedMonoid.mk _ (gradedProduct L d 0 (symbol L d x) (symbol L 0 (filteredScalar L r)))
    simp only [gradedProduct_symbol]
    exact sigma_symbol_eq L ((zero_add d).trans (add_zero d).symm) (Algebra.commutes r x.1)
  smul_def := by
    rintro r ⟨d, a⟩
    obtain ⟨x, rfl⟩ := (lower L d).mkQ_surjective a
    change GradedMonoid.mk d (r • symbol L d x) =
      GradedMonoid.mk _ (gradedProduct L 0 d (symbol L 0 (filteredScalar L r)) (symbol L d x))
    rw [← map_smul, gradedProduct_symbol]
    exact sigma_symbol_eq L (zero_add d).symm (Algebra.smul_def r x.1)

/-- The associated graded algebra, with its word-degree and parity indices. -/
abbrev AssociatedGraded := ⨁ d : Degree, GradedPiece L d

/-- Insert a symbol into the doubly graded algebra. -/
abbrev ofSymbol (d : Degree) : filtered L d →ₗ[k] AssociatedGraded L :=
  (DirectSum.lof k Degree (GradedPiece L) d).comp (symbol L d)

end

end LieNotes.SuperRestricted.SuperEnveloping.Construction

namespace Specs.LieNotes.SuperRestricted.SuperEnveloping

open _root_.LieNotes.SuperRestricted
open _root_.LieNotes.SuperRestricted.SuperEnveloping.Construction

open scoped DirectSum

universe u v w

noncomputable section

-- Contract signatures can depend on several universes whose maximum is the sort.
set_option linter.checkUnivs false

def relatorType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (_ : LieSuperalgebra k V), ZMod 2 → ZMod 2 → V → V → TensorAlgebra k V

def relatorValue := @relator

def relationsType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (_ : LieSuperalgebra k V), Set (TensorAlgebra k V)

def relationsValue := @relations

def relationIdealType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (_ : LieSuperalgebra k V), TwoSidedIdeal (TensorAlgebra k V)

def relationIdealValue := @relationIdeal

def EnvelopingType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (_ : LieSuperalgebra k V), Type (max u v)

def EnvelopingValue := @Enveloping

def quotientMapType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V), TensorAlgebra k V →ₐ[k] Enveloping L

def quotientMapValue := @quotientMap

def ιType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V), V →ₗ[k] Enveloping L

def ιValue := @ι

def tensorParityType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] (_ : Grading k V),
    TensorAlgebra k V →ₐ[k] TensorAlgebra k V

def tensorParityValue := @tensorParity

def tensorPieceType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] (_ : Grading k V), ZMod 2 → Submodule k (TensorAlgebra k V)

def tensorPieceValue := @tensorPiece

def parityType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V), Enveloping L →ₐ[k] Enveloping L

def parityValue := @parity

def pieceType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V), ZMod 2 → Submodule k (Enveloping L)

def pieceValue := @piece

def wordType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] {A : Type w} [Ring A] [Algebra k A], (V →ₗ[k] A) → List V → A

def wordValue := @word

def wordFiltrationType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] {A : Type w} [Ring A] [Algebra k A], (V →ₗ[k] A) → ℤ → Submodule k A

def wordFiltrationValue := @wordFiltration

def filtrationType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V), ℤ → Submodule k (Enveloping L)

def filtrationValue := @filtration

def filteredPieceType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V), ℤ → ZMod 2 → Submodule k (Enveloping L)

def filteredPieceValue := @filteredPiece

def DegreeType :=
  Type

def DegreeValue := @Degree

def filteredType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V), Degree → Submodule k (Enveloping L)

def filteredValue := @filtered

def lowerType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) (d : Degree), Submodule k (filtered L d)

def lowerValue := @lower

def GradedPieceType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (_ : LieSuperalgebra k V), Degree → Type (max u v)

def GradedPieceValue := @GradedPiece

def symbolType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) (d : Degree), filtered L d →ₗ[k] GradedPiece L d

def symbolValue := @symbol

def gradedProductType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) (d e : Degree),
    GradedPiece L d →ₗ[k] GradedPiece L e →ₗ[k] GradedPiece L (d + e)

def gradedProductValue := @gradedProduct

def AssociatedGradedType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (_ : LieSuperalgebra k V), Type (max u v)

def AssociatedGradedValue := @AssociatedGraded

def ofSymbolType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) (d : Degree), filtered L d →ₗ[k] AssociatedGraded L

def ofSymbolValue := @ofSymbol

def quotientMap_surjectiveType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V), Function.Surjective (quotientMap L)

def quotientMap_eq_zero_iffType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) (x : TensorAlgebra k V),
    quotientMap L x = 0 ↔ x ∈ relationIdeal L

def generator_relationType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) {i j : ZMod 2} {x y : V},
    x ∈ L.grading.piece i → y ∈ L.grading.piece j →
    ι L x * ι L y - paritySign k i j • (ι L y * ι L x) = ι L (L.bracket x y)

def relator_mem_tensorPieceType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) {i j : ZMod 2} {x y : V},
    x ∈ L.grading.piece i → y ∈ L.grading.piece j →
    relator L i j x y ∈ tensorPiece L.grading (i + j)

def tensorWord_memType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] (G : Grading k V) (xs : List (Σ i, G.piece i)),
    word (TensorAlgebra.ι k) (xs.map fun x => (x.2 : V)) ∈ tensorPiece G (xs.map Sigma.fst).sum

def quotientMap_mem_pieceType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) {i : ZMod 2} {x : TensorAlgebra k V},
    x ∈ tensorPiece L.grading i → quotientMap L x ∈ piece L i

def tensorPiece_imageType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) (i : ZMod 2),
    (tensorPiece L.grading i).map (quotientMap L).toLinearMap = piece L i

def ι_mem_pieceType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) {i : ZMod 2} {x : V},
    x ∈ L.grading.piece i → ι L x ∈ piece L i

def filtration_monoType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V), Monotone (filtration L)

def filtration_negativeType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) {n : ℤ}, n < 0 → filtration L n = ⊥

def filtration_mulType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) {m n : ℤ} {x y : Enveloping L},
    x ∈ filtration L m → y ∈ filtration L n → x * y ∈ filtration L (m + n)

def ι_mem_filtrationType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) (x : V), ι L x ∈ filtration L 1

def filtration_imageType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) (n : ℤ),
    (wordFiltration (TensorAlgebra.ι k (M := V)) n).map (quotientMap L).toLinearMap = filtration L n

def filtration_exhaustiveType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) (x : Enveloping L), ∃ n : ℕ, x ∈ filtration L n

def parity_filtrationType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) {n : ℤ} {x : Enveloping L},
    x ∈ filtration L n → parity L x ∈ filtration L n

def filtration_isInternalType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) (n : ℤ),
    DirectSum.IsInternal (fun i => (piece L i).comap (filtration L n).subtype)

def lower_eqType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) (d : Degree),
    lower L d = (filteredPiece L ((d.1 : ℤ) - 1) d.2).comap (filtered L d).subtype

def lower_zeroType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) (i : ZMod 2), lower L (0, i) = ⊥

def gradedProduct_eq_symbolType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) (d e : Degree) (x : filtered L d) (y : filtered L e)
    (h : x.1 * y.1 ∈ filtered L (d + e)),
    gradedProduct L d e (symbol L d x) (symbol L e y) = symbol L (d + e) ⟨x.1 * y.1, h⟩

def ofSymbol_mulType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V) (d e : Degree) (x : filtered L d) (y : filtered L e),
    ofSymbol L d x * ofSymbol L e y =
      DirectSum.lof k Degree (GradedPiece L) (d + e)
        (gradedProduct L d e (symbol L d x) (symbol L e y))

end

end Specs.LieNotes.SuperRestricted.SuperEnveloping
