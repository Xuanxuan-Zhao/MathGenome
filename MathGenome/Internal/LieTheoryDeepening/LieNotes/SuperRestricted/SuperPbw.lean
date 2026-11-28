import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.SuperPbw
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.SuperPbwBasis
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.SuperEnvelopingModules
import Batteries.Tactic.OpenPrivate

namespace LieNotes.SuperRestricted.SuperPbw

open SuperEnveloping
open private filtered_mul from MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.SuperEnveloping
open Definitions (Even Odd SymmetricExterior evenLetter oddLetter assemble tensorGenerator
  HomogeneousLetter homogeneousWordDegree homogeneousWord gradedComponent generatorSymbol parity_cases)
open SuperPbwBasis
open scoped TensorProduct DirectSum

noncomputable section

universe u v w

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
  (L : LieSuperalgebra k V)

private theorem ofSymbol_mul' {d e : Degree} (x : filtered L d) (y : filtered L e)
    (h : x.1 * y.1 ∈ filtered L (d + e)) :
    ofSymbol L d x * ofSymbol L e y = ofSymbol L (d + e) ⟨x.1 * y.1, h⟩ := by
  rw [ofSymbol_mul, gradedProduct_eq_symbol _ _ _ _ _ h]
  rfl

private theorem ofSymbol_congr {d e : Degree} (h : d = e)
    (x : filtered L d) (y : filtered L e) (hxy : x.val = y.val) :
    ofSymbol L d x = ofSymbol L e y := by
  subst e
  exact congrArg (ofSymbol L d) (Subtype.ext hxy)

private theorem ofSymbol_one (h : (1 : Enveloping L) ∈ filtered L 0) :
    ofSymbol L 0 ⟨1, h⟩ = 1 := by
  change ofSymbol L 0 ⟨1, h⟩ = ofSymbol L 0 (Construction.filteredScalar L 1)
  congr 1

private theorem homogeneousWord_mem (xs : List (HomogeneousLetter L)) :
    word (ι L) (homogeneousWord L xs) ∈ filtered L (homogeneousWordDegree L xs) := by
  constructor
  · exact Construction.word_mem (ι L) (by simp [homogeneousWord, homogeneousWordDegree])
  · have h := quotientMap_mem_piece L (tensorWord_mem L.grading xs)
    simpa [homogeneousWord, homogeneousWordDegree, Construction.word, List.map_map,
      ← List.prod_hom, Construction.ι, Function.comp_def] using h

private def wordSymbol (xs : List (HomogeneousLetter L)) : AssociatedGraded L :=
  ofSymbol L (homogeneousWordDegree L xs)
    ⟨word (ι L) (homogeneousWord L xs), homogeneousWord_mem L xs⟩

private theorem wordSymbol_eq_prod (xs : List (HomogeneousLetter L)) :
    wordSymbol L xs = (xs.map fun x => generatorSymbol L x.1 x.2).prod := by
  induction xs with
  | nil => exact ofSymbol_one L _
  | cons x xs ih =>
    rw [List.map_cons, List.prod_cons, ← ih]
    change _ = ofSymbol L (1, x.1) _ * ofSymbol L (homogeneousWordDegree L xs) _
    have hd : (1, x.1) + homogeneousWordDegree L xs = homogeneousWordDegree L (x :: xs) := by
      dsimp [homogeneousWordDegree]
      exact Prod.ext (Nat.add_comm _ _) rfl
    rw [ofSymbol_mul' L _ _ (by
      rw [hd]
      exact homogeneousWord_mem L (x :: xs))]
    unfold wordSymbol
    exact ofSymbol_congr L hd.symm _ _ rfl

section Ordered

variable {I : Type w} [LinearOrder I] (b : Module.Basis I k V) (degree : I → ZMod 2)
  (hb : Homogeneous L b degree)

private def orderedLetters (l : OrderedWord degree) : List (HomogeneousLetter L) :=
  l.val.map fun j => ⟨degree j, ⟨b j, hb j⟩⟩

private def orderedDegree (l : OrderedWord degree) : Degree :=
  (l.val.length, (l.val.map degree).sum)

private theorem orderedLetters_degree (l : OrderedWord degree) :
    homogeneousWordDegree L (orderedLetters L b degree hb l) = orderedDegree degree l := by
  simp [homogeneousWordDegree, orderedLetters, orderedDegree, List.map_map, Function.comp_def]

include hb in
private theorem ordered_mem (l : OrderedWord degree) :
    monomial L b l.val ∈ filtered L (orderedDegree degree l) := by
  have h := homogeneousWord_mem L (orderedLetters L b degree hb l)
  rw [orderedLetters_degree] at h
  simpa [homogeneousWord, orderedLetters, List.map_map, Function.comp_def, monomial] using h

private def orderedSymbol (l : OrderedWord degree) : AssociatedGraded L :=
  ofSymbol L (orderedDegree degree l) ⟨monomial L b l.val, ordered_mem L b degree hb l⟩

private theorem orderedSymbol_eq (l : OrderedWord degree) :
    orderedSymbol L b degree hb l = wordSymbol L (orderedLetters L b degree hb l) := by
  unfold orderedSymbol wordSymbol
  have hd := orderedLetters_degree L b degree hb l
  have hw : word (ι L) (homogeneousWord L (orderedLetters L b degree hb l)) =
      monomial L b l.val := by
    simp [homogeneousWord, orderedLetters, List.map_map, Function.comp_def, monomial]
  exact ofSymbol_congr L hd.symm _ _ hw.symm

variable (B : Module.Basis (OrderedWord degree) k (Enveloping L))
  (hB : ∀ l, B l = monomial L b l.val)

include hb hB in
private theorem filtration_eq_basis_span (n : ℤ) :
    filtration L n = Submodule.span k (B '' {l | (l.val.length : ℤ) ≤ n}) := by
  change Construction.filtration L n = _
  rw [filtration_eq_span L b degree hb]
  congr 1
  ext x
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l.val, l.property, hB _⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, (hB _).symm⟩

private theorem parityScalar_injective :
    Function.Injective (Construction.parityScalar k) := by
  intro i j h
  rcases parity_cases i with rfl | rfl <;> rcases parity_cases j with rfl | rfl
  · rfl
  · exfalso
    have h' : (1 : k) = -1 := by simpa [Construction.parityScalar] using h
    exact two_ne_zero ((one_add_one_eq_two (R := k)).symm.trans (add_eq_zero_iff_eq_neg.mpr h'))
  · exfalso
    have h' : (1 : k) = -1 := by simpa [Construction.parityScalar] using h.symm
    exact two_ne_zero ((one_add_one_eq_two (R := k)).symm.trans (add_eq_zero_iff_eq_neg.mpr h'))
  · rfl

include hb hB

private theorem coord_parity (l : OrderedWord degree) (x : Enveloping L) :
    B.coord l (parity L x) = Construction.parityScalar k (orderedDegree degree l).2 * B.coord l x := by
  have h : (B.coord l).comp (parity L).toLinearMap =
      Construction.parityScalar k (orderedDegree degree l).2 • B.coord l := by
    apply B.ext
    intro j
    have hj : B j ∈ piece L (orderedDegree degree j).2 := by
      rw [hB]
      exact (ordered_mem L b degree hb j).2
    have hp := (Construction.mem_paritySpace ..).mp hj
    change parity L (B j) = _ at hp
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, hp, map_smul, LinearMap.smul_apply]
    by_cases e : j = l
    · subst j
      rfl
    · rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne (Ne.symm e)]
      simp
  exact congrFun (congrArg DFunLike.coe h) x

private theorem filtered_mem_basis_span (d : Degree) (x : filtered L d) :
    x.val ∈ Submodule.span k
      (B '' {l | (l.val.length : ℤ) ≤ d.1 ∧ (orderedDegree degree l).2 = d.2}) := by
  apply B.mem_span_image.mpr
  intro l hl
  have he := B.mem_span_image.mp
    ((filtration_eq_basis_span L b degree hb B hB d.1).le x.property.1) hl
  refine ⟨he, parityScalar_injective (k := k) ?_⟩
  have h := coord_parity L b degree hb B hB l x.val
  have hx := (Construction.mem_paritySpace ..).mp x.property.2
  change parity L x.val = _ at hx
  rw [hx, map_smul, smul_eq_mul] at h
  exact mul_right_cancel₀ (Finsupp.mem_support_iff.mp hl) h.symm

private theorem gradedComponent_le (d : Degree) (R : Submodule k (AssociatedGraded L))
    (hR : ∀ l, orderedDegree degree l = d → orderedSymbol L b degree hb l ∈ R) :
    gradedComponent L d ≤ R := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, rfl⟩ := (lower L d).mkQ_surjective y
  change ofSymbol L d x ∈ R
  let S : Submodule k (filtered L d) := R.comap (ofSymbol L d)
  have hx : x.val ∈ S.map (filtered L d).subtype := by
    apply (Submodule.span_le.mpr ?_) (filtered_mem_basis_span L b degree hb B hB d x)
    rintro _ ⟨l, hl, rfl⟩
    have hm : B l ∈ filtered L d := by
      refine ⟨?_, ?_⟩
      · change B l ∈ filtration L d.1
        rw [filtration_eq_basis_span L b degree hb B hB]
        exact Submodule.subset_span ⟨l, hl.1, rfl⟩
      · rw [hB, ← hl.2]
        exact (ordered_mem L b degree hb l).2
    refine ⟨⟨B l, hm⟩, ?_, rfl⟩
    change ofSymbol L d ⟨B l, hm⟩ ∈ R
    by_cases he : l.val.length = d.1
    · have hd : orderedDegree degree l = d := Prod.ext he hl.2
      have hEq : (⟨B l, hm⟩ : filtered L d) =
          ⟨monomial L b l.val, hd ▸ ordered_mem L b degree hb l⟩ := Subtype.ext (hB l)
      rw [hEq]
      cases hd
      exact hR l rfl
    · have hlow : (⟨B l, hm⟩ : filtered L d) ∈ lower L d := by
        change B l ∈ filtration L ((d.1 : ℤ) - 1)
        rw [filtration_eq_basis_span L b degree hb B hB]
        exact Submodule.subset_span ⟨l, by
          change (l.val.length : ℤ) ≤ (d.1 : ℤ) - 1
          have := hl.1
          omega, rfl⟩
      change DirectSum.lof k Degree (GradedPiece L) d (symbol L d ⟨B l, hm⟩) ∈ R
      have hz : symbol L d ⟨B l, hm⟩ = 0 := by
        change Submodule.Quotient.mk _ = 0
        rwa [Submodule.Quotient.mk_eq_zero]
      rw [hz, map_zero]
      exact R.zero_mem
  obtain ⟨z, hz, he⟩ := hx
  have : z = x := Subtype.ext he
  exact this ▸ hz

private theorem span_orderedSymbol :
    Submodule.span k (Set.range (orderedSymbol L b degree hb)) = ⊤ := by
  let R := Submodule.span k (Set.range (orderedSymbol L b degree hb))
  apply eq_top_iff.mpr
  intro x hx
  clear hx
  change x ∈ R
  induction x using DirectSum.induction_on with
  | zero => exact R.zero_mem
  | add x y hx hy => exact R.add_mem hx hy
  | of d y =>
    exact gradedComponent_le L b degree hb B hB d R
      (fun l _ => Submodule.subset_span ⟨l, rfl⟩) ⟨y, rfl⟩

omit hb hB

private def lengthProjection (n : ℕ) : Enveloping L →ₗ[k] Enveloping L :=
  B.constr k fun l => if l.val.length = n then B l else 0

include hb hB

private theorem lengthProjection_lower (d : Degree) :
    lower L d ≤ LinearMap.ker ((lengthProjection L degree B d.1).comp (filtered L d).subtype) := by
  intro x hx
  have h : filtration L ((d.1 : ℤ) - 1) ≤ LinearMap.ker (lengthProjection L degree B d.1) := by
    rw [filtration_eq_basis_span L b degree hb B hB]
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    change lengthProjection L degree B d.1 (B l) = 0
    have hne : l.val.length ≠ d.1 := by
      change (l.val.length : ℤ) ≤ (d.1 : ℤ) - 1 at hl
      omega
    simp [lengthProjection, hne]
  exact h hx

private def fromSymbols : AssociatedGraded L →ₗ[k] Enveloping L :=
  DirectSum.toModule k Degree (Enveloping L) fun d =>
    (lower L d).liftQ ((lengthProjection L degree B d.1).comp (filtered L d).subtype)
      (lengthProjection_lower L b degree hb B hB d)

private theorem fromSymbols_orderedSymbol (l : OrderedWord degree) :
    fromSymbols L b degree hb B hB (orderedSymbol L b degree hb l) = B l := by
  change fromSymbols L b degree hb B hB
    (DirectSum.lof k Degree (GradedPiece L) (orderedDegree degree l) _) = _
  rw [fromSymbols, DirectSum.toModule_lof]
  change lengthProjection L degree B l.val.length (monomial L b l.val) = _
  rw [← hB l]
  simp [lengthProjection]

private theorem linearIndependent_orderedSymbol :
    LinearIndependent k (orderedSymbol L b degree hb) := by
  apply LinearIndependent.of_comp (f := fromSymbols L b degree hb B hB)
  convert B.linearIndependent using 1
  funext l
  exact fromSymbols_orderedSymbol L b degree hb B hB l

end Ordered

private def filteredGenerator (i : ZMod 2) (x : L.grading.piece i) : filtered L (1, i) :=
  ⟨ι L x, ι_mem_filtration L x, ι_mem_piece L x.property⟩

private theorem leading_relation {i j : ZMod 2}
    (x : L.grading.piece i) (y : L.grading.piece j) :
    generatorSymbol L i x * generatorSymbol L j y =
      paritySign k i j • (generatorSymbol L j y * generatorSymbol L i x) := by
  let d : Degree := (1, i) + (1, j)
  let e : Degree := (1, j) + (1, i)
  have hde : d = e := add_comm _ _
  let a := filteredGenerator L i x
  let b := filteredGenerator L j y
  have ha : a.val * b.val ∈ filtered L d :=
    filtered_mul L (1, i) (1, j) a b
  have hb : b.val * a.val ∈ filtered L e :=
    filtered_mul L (1, j) (1, i) b a
  change ofSymbol L (1, i) a * ofSymbol L (1, j) b =
    paritySign k i j • (ofSymbol L (1, j) b * ofSymbol L (1, i) a)
  rw [ofSymbol_mul' L a b ha, ofSymbol_mul' L b a hb,
    ofSymbol_congr L hde.symm ⟨_, hb⟩ ⟨_, hde.symm ▸ hb⟩ rfl]
  apply sub_eq_zero.mp
  rw [← map_smul, ← map_sub]
  let r : filtered L d := ⟨a.val * b.val, ha⟩ - paritySign k i j •
    (⟨b.val * a.val, hde.symm ▸ hb⟩ : filtered L d)
  have hr : r ∈ lower L d := by
    change ι L x * ι L y - paritySign k i j • (ι L y * ι L x) ∈
      filtration L ((d.1 : ℤ) - 1)
    rw [generator_relation L x.property y.property]
    exact ι_mem_filtration L _
  change DirectSum.lof k Degree (GradedPiece L) d (symbol L d r) = 0
  have hz : symbol L d r = 0 := by
    change Submodule.Quotient.mk r = 0
    rwa [Submodule.Quotient.mk_eq_zero]
  rw [hz, map_zero]

section UniversalProperty

variable {A : Type*} [Ring A] [Algebra k A]

omit [NeZero (2 : k)] in
private theorem assemble_apply (G : Grading k V) (f : ∀ i, G.piece i →ₗ[k] A)
    (i : ZMod 2) (x : G.piece i) : assemble G f x = f i x := by
  let D := LinearEquiv.ofBijective (DirectSum.coeLinearMap G.piece) G.isInternal
  have hx : D.symm x = DirectSum.lof k (ZMod 2) (fun j => G.piece j) i x := by
    apply D.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (DirectSum.coeLinearMap_lof G.piece i x).symm
  change DirectSum.toModule k _ A f (D.symm x) = _
  rw [hx, DirectSum.toModule_lof]

private theorem tensorGenerator_even (x : Even L) :
    tensorGenerator L x = evenLetter L x := by
  unfold tensorGenerator
  rw [assemble_apply]
  simp

private theorem tensorGenerator_odd (x : Odd L) :
    tensorGenerator L x = oddLetter L x := by
  unfold tensorGenerator
  rw [assemble_apply]
  simp [show (1 : ZMod 2) ≠ 0 by decide]

omit [NeZero (2 : k)] in
/-- Maps on all of the parity summands determine the map on the original space. -/
private theorem linearMap_ext_pieces (G : Grading k V) {f g : V →ₗ[k] A}
    (h : ∀ i (x : G.piece i), f x = g x) : f = g := by
  apply LinearMap.ext_on (s := ⋃ i, (G.piece i : Set V))
  · rw [Submodule.span_iUnion]
    simpa using G.isInternal.submodule_iSup_eq_top
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact h i ⟨x, hi⟩

private theorem enveloping_ext {f g : Enveloping L →ₐ[k] A}
    (h : ∀ x : V, f (ι L x) = g (ι L x)) : f = g := by
  apply RingCon.Quotient.hom_extₐ
  apply TensorAlgebra.hom_ext
  exact LinearMap.ext h

/-- The same graded vector space with zero bracket. -/
private def abelian : LieSuperalgebra k V where
  grading := L.grading
  bracket := 0
  bracket_mem := by
    intro i j x y _ _
    simp
  skew := by simp [GradedSkew]
  jacobi := by simp [GradedJacobi]
  oddTriple_char_three := by simp [OddTripleIdentity]

private def Signed (f : V →ₗ[k] A) : Prop :=
  ∀ (i j : ZMod 2) (x : L.grading.piece i) (y : L.grading.piece j),
    f x * f y = paritySign k i j • (f y * f x)

private theorem abelianLift_con (f : V →ₗ[k] A) (hf : Signed L f) :
    (relationIdeal (abelian L)).ringCon ≤ RingCon.ker (TensorAlgebra.lift k f).toRingHom := by
  change (relationIdeal (abelian L)).ringCon ≤
    (TwoSidedIdeal.ker (TensorAlgebra.lift k f)).ringCon
  apply TwoSidedIdeal.ringCon_le_iff.mp
  apply TwoSidedIdeal.span_le.mpr
  rintro a ⟨i, j, x, y, hx, hy, rfl⟩
  apply (TwoSidedIdeal.mem_ker (TensorAlgebra.lift k f)).mpr
  simp only [Construction.relator, map_sub, map_mul, map_smul, TensorAlgebra.lift_ι_apply,
    abelian, LinearMap.zero_apply, map_zero, sub_zero]
  exact sub_eq_zero.mpr (hf i j ⟨x, hx⟩ ⟨y, hy⟩)

private def abelianLift (f : V →ₗ[k] A) (hf : Signed L f) : Enveloping (abelian L) →ₐ[k] A :=
  (relationIdeal (abelian L)).ringCon.liftₐ (TensorAlgebra.lift k f) (abelianLift_con L f hf)

@[simp] private theorem abelianLift_ι (f : V →ₗ[k] A) (hf : Signed L f) (x : V) :
    abelianLift L f hf (ι (abelian L) x) = f x :=
  TensorAlgebra.lift_ι_apply f x

private theorem abelian_signed : Signed L (ι (abelian L)) := by
  intro i j x y
  apply sub_eq_zero.mp
  have h := generator_relation (abelian L) x.property y.property
  rw [show (abelian L).bracket x y = 0 by simp [abelian], (ι (abelian L)).map_zero] at h
  exact h

private theorem tensorGenerator_signed : Signed L (tensorGenerator L) := by
  intro i j
  rcases parity_cases i with rfl | rfl <;> rcases parity_cases j with rfl | rfl <;> intro x y
  · simp only [tensorGenerator_even, paritySign, ZMod.val_zero, zero_mul, pow_zero, one_smul]
    exact (Commute.all (SymmetricAlgebra.ι k _ x) (SymmetricAlgebra.ι k _ y)).map
      (Algebra.TensorProduct.includeLeft : SymmetricAlgebra k (Even L) →ₐ[k] SymmetricExterior L)
  · simp [tensorGenerator_even, tensorGenerator_odd, evenLetter, oddLetter, paritySign,
      Algebra.TensorProduct.tmul_mul_tmul]
  · simp [tensorGenerator_even, tensorGenerator_odd, evenLetter, oddLetter, paritySign,
      Algebra.TensorProduct.tmul_mul_tmul]
  · rw [show paritySign k 1 1 = -(1 : k) by simp [paritySign, ZMod.val_one]]
    have h : ExteriorAlgebra.ι k x * ExteriorAlgebra.ι k y =
        -(ExteriorAlgebra.ι k y * ExteriorAlgebra.ι k x) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap x y)
    have hm := congrArg
      (Algebra.TensorProduct.includeRight : ExteriorAlgebra k (Odd L) →ₐ[k] SymmetricExterior L) h
    have hs : tensorGenerator L x * tensorGenerator L y =
        -(tensorGenerator L y * tensorGenerator L x) := by
      simp only [map_neg] at hm
      simpa only [tensorGenerator_odd, oddLetter, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        ← map_mul] using hm
    exact hs.trans (neg_one_smul k _).symm

private def symmetricLift (f : Even L →ₗ[k] A) (hf : ∀ x y, Commute (f x) (f y)) :
    SymmetricAlgebra k (Even L) →ₐ[k] A :=
  (TensorAlgebra.symRingCon k (Even L)).liftₐ (TensorAlgebra.lift k f) (by
    apply RingCon.ringConGen_le.mpr
    intro a b h
    cases h with
    | mul_comm x y =>
      rw [RingCon.ker_apply]
      change (TensorAlgebra.lift k f) _ = (TensorAlgebra.lift k f) _
      simpa only [map_mul, TensorAlgebra.lift_ι_apply] using (hf x y).eq)

@[simp] private theorem symmetricLift_ι (f : Even L →ₗ[k] A)
    (hf : ∀ x y, Commute (f x) (f y)) (x : Even L) :
    symmetricLift L f hf (SymmetricAlgebra.ι k _ x) = f x :=
  TensorAlgebra.lift_ι_apply f x

private theorem cross_commute {a : SymmetricAlgebra k (Even L) →ₐ[k] A}
    {b : ExteriorAlgebra k (Odd L) →ₐ[k] A}
    (h : ∀ x y, Commute (a (SymmetricAlgebra.ι k _ x)) (b (ExteriorAlgebra.ι k y)))
    (s : SymmetricAlgebra k (Even L)) (t : ExteriorAlgebra k (Odd L)) :
    Commute (a s) (b t) := by
  induction s using SymmetricAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commute_algebraMap_left _ _
  | add s s' hs hs' => rw [map_add]; exact hs.add_left hs'
  | mul s s' hs hs' => rw [map_mul]; exact hs.mul_left hs'
  | ι x =>
    induction t using ExteriorAlgebra.induction with
    | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commute_algebraMap_right _ _
    | ι y => exact h x y
    | add t t' ht ht' => rw [map_add]; exact ht.add_right ht'
    | mul t t' ht ht' => rw [map_mul]; exact ht.mul_right ht'

private theorem square_zero_of_signed {f : V →ₗ[k] A} (hf : Signed L f) (x : Odd L) :
    f x * f x = 0 := by
  have h : f x * f x = -(f x * f x) := by
    simpa [paritySign, ZMod.val_one] using hf 1 1 x x
  have hz : (2 : k) • (f x * f x) = 0 := by
    rw [two_smul, add_eq_zero_iff_eq_neg.mpr h]
  exact (smul_eq_zero.mp hz).resolve_left two_ne_zero

private def exteriorLift (f : V →ₗ[k] A) (hf : Signed L f) : ExteriorAlgebra k (Odd L) →ₐ[k] A :=
  ExteriorAlgebra.lift k ⟨f.comp (Odd L).subtype, by
    intro x
    exact square_zero_of_signed L hf x⟩

private theorem exteriorLift_ι (f : V →ₗ[k] A) (hf : Signed L f) (x : Odd L) :
    exteriorLift L f hf (ExteriorAlgebra.ι k x) = f x :=
  ExteriorAlgebra.lift_ι_apply k (f.comp (Odd L).subtype) (square_zero_of_signed L hf) x

private def tensorLift (f : V →ₗ[k] A) (hf : Signed L f) : SymmetricExterior L →ₐ[k] A :=
  Algebra.TensorProduct.lift
    (symmetricLift L (f.comp (Even L).subtype) (fun x y => by
      simpa [Commute, SemiconjBy, paritySign, ZMod.val_zero] using hf 0 0 x y))
    (exteriorLift L f hf)
    (cross_commute L fun x y => by
      rw [symmetricLift_ι, exteriorLift_ι]
      simpa [Commute, SemiconjBy, paritySign, ZMod.val_zero] using hf 0 1 x y)

@[simp] private theorem tensorLift_even (f : V →ₗ[k] A) (hf : Signed L f) (x : Even L) :
    tensorLift L f hf (evenLetter L x) = f x := by
  change ((tensorLift L f hf).comp Algebra.TensorProduct.includeLeft) _ = _
  rw [tensorLift, Algebra.TensorProduct.lift_comp_includeLeft, symmetricLift_ι]
  rfl

@[simp] private theorem tensorLift_odd (f : V →ₗ[k] A) (hf : Signed L f) (x : Odd L) :
    tensorLift L f hf (oddLetter L x) = f x := by
  change ((tensorLift L f hf).comp Algebra.TensorProduct.includeRight) _ = _
  rw [tensorLift, Algebra.TensorProduct.lift_comp_includeRight', exteriorLift_ι]

private theorem tensorLift_generator (f : V →ₗ[k] A) (hf : Signed L f) (x : V) :
    tensorLift L f hf (tensorGenerator L x) = f x := by
  suffices h : (tensorLift L f hf).toLinearMap.comp (tensorGenerator L) = f from
    congrFun (congrArg DFunLike.coe h) x
  apply linearMap_ext_pieces L.grading
  intro i y
  rcases parity_cases i with rfl | rfl
  · change tensorLift L f hf (tensorGenerator L y) = _
    rw [tensorGenerator_even, tensorLift_even]
  · change tensorLift L f hf (tensorGenerator L y) = _
    rw [tensorGenerator_odd, tensorLift_odd]

private theorem tensor_ext {f g : SymmetricExterior L →ₐ[k] A}
    (h₀ : ∀ x : Even L, f (evenLetter L x) = g (evenLetter L x))
    (h₁ : ∀ x : Odd L, f (oddLetter L x) = g (oddLetter L x)) : f = g := by
  apply Algebra.TensorProduct.ext
  · apply RingCon.Quotient.hom_extₐ
    apply TensorAlgebra.hom_ext
    exact LinearMap.ext h₀
  · apply ExteriorAlgebra.hom_ext
    exact LinearMap.ext h₁

end UniversalProperty

private def abelianEquivTensor : Enveloping (abelian L) ≃ₐ[k] SymmetricExterior L :=
  AlgEquiv.ofAlgHom
    (abelianLift L (tensorGenerator L) (tensorGenerator_signed L))
    (tensorLift L (ι (abelian L)) (abelian_signed L))
    (tensor_ext L (fun x => by simp [tensorGenerator_even]) (fun x => by simp [tensorGenerator_odd]))
    (enveloping_ext (abelian L) (fun x => by simp [tensorLift_generator]))

private theorem abelianEquivTensor_ι (x : V) :
    abelianEquivTensor L (ι (abelian L) x) = tensorGenerator L x :=
  abelianLift_ι L (tensorGenerator L) (tensorGenerator_signed L) x

private def gradedGenerator : V →ₗ[k] AssociatedGraded L :=
  assemble L.grading (generatorSymbol L)

private theorem gradedGenerator_signed : Signed L (gradedGenerator L) := by
  intro i j x y
  simpa only [gradedGenerator, assemble_apply] using leading_relation L x y

private def abelianToGraded : Enveloping (abelian L) →ₐ[k] AssociatedGraded L :=
  abelianLift L (gradedGenerator L) (gradedGenerator_signed L)

omit [NeZero (2 : k)] in
private theorem map_word {A C : Type*} [Ring A] [Algebra k A] [Ring C] [Algebra k C]
    (f : V →ₗ[k] A) (g : A →ₐ[k] C) (l : List V) :
    g (word f l) = word (g.toLinearMap.comp f) l := by
  induction l with
  | nil => exact g.map_one
  | cons x l ih =>
    change g (f x * word f l) = g (f x) * word (g.toLinearMap.comp f) l
    rw [map_mul, ih]

private theorem abelianToGraded_word (xs : List (HomogeneousLetter L)) :
    abelianToGraded L (word (ι (abelian L)) (homogeneousWord L xs)) = wordSymbol L xs := by
  have h : (abelianToGraded L).toLinearMap.comp (ι (abelian L)) = gradedGenerator L :=
    LinearMap.ext fun x => abelianLift_ι L _ (gradedGenerator_signed L) x
  rw [map_word, h, wordSymbol_eq_prod]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change gradedGenerator L x.2 * word (gradedGenerator L) (homogeneousWord L xs) =
      generatorSymbol L x.1 x.2 * (xs.map fun y => generatorSymbol L y.1 y.2).prod
    rw [ih]
    exact congrArg (· * _) (assemble_apply L.grading (generatorSymbol L) x.1 x.2)

private def tensorToGraded : SymmetricExterior L →ₐ[k] AssociatedGraded L :=
  (abelianToGraded L).comp (abelianEquivTensor L).symm.toAlgHom

private theorem tensorToGraded_generator (x : V) :
    tensorToGraded L (tensorGenerator L x) = gradedGenerator L x := by
  have h := (abelianEquivTensor L).symm_apply_apply (ι (abelian L) x)
  rw [abelianEquivTensor_ι] at h
  change abelianToGraded L ((abelianEquivTensor L).symm (tensorGenerator L x)) = _
  rw [h]
  exact abelianLift_ι L _ (gradedGenerator_signed L) x

private theorem tensorToGraded_word (xs : List (HomogeneousLetter L)) :
    tensorToGraded L (word (tensorGenerator L) (homogeneousWord L xs)) = wordSymbol L xs := by
  have h : (tensorToGraded L).toLinearMap.comp (tensorGenerator L) = gradedGenerator L :=
    LinearMap.ext (tensorToGraded_generator L)
  have h' : (abelianToGraded L).toLinearMap.comp (ι (abelian L)) = gradedGenerator L :=
    LinearMap.ext fun x => abelianLift_ι L _ (gradedGenerator_signed L) x
  rw [map_word, h, ← abelianToGraded_word, map_word, h']

section Comparison

variable {I : Type w} [LinearOrder I] (b : Module.Basis I k V) (degree : I → ZMod 2)
  (hb : Homogeneous L b degree)

include hb in
private theorem abelianToGraded_bijective : Function.Bijective (abelianToGraded L) := by
  obtain ⟨B, hB⟩ := orderedBasis_exists L b degree hb
  have hb₀ : Homogeneous (abelian L) b degree := hb
  obtain ⟨B₀, hB₀⟩ := orderedBasis_exists (abelian L) b degree hb₀
  let C : Module.Basis (OrderedWord degree) k (AssociatedGraded L) :=
    Module.Basis.mk (linearIndependent_orderedSymbol L b degree hb B hB)
      (span_orderedSymbol L b degree hb B hB).ge
  let e := B₀.equiv C (Equiv.refl _)
  have he : (abelianToGraded L).toLinearMap = e.toLinearMap := by
    apply B₀.ext
    intro l
    change abelianToGraded L (B₀ l) = e (B₀ l)
    rw [show e (B₀ l) = C l from Module.Basis.equiv_apply _ _ _ _, hB₀ l]
    rw [show C l = orderedSymbol L b degree hb l from Module.Basis.mk_apply _ _ _]
    rw [orderedSymbol_eq, ← abelianToGraded_word]
    simp [monomial, homogeneousWord, orderedLetters, List.map_map, Function.comp_def]
  change Function.Bijective ⇑(abelianToGraded L).toLinearMap
  rw [he]
  exact e.bijective

include hb in
private theorem tensorToGraded_map_piece (B : Module.Basis (OrderedWord degree) k (Enveloping L))
    (hB : ∀ l, B l = monomial L b l.val) (d : Degree) :
    (Definitions.tensorPiece L d).map (tensorToGraded L).toLinearMap = gradedComponent L d := by
  apply le_antisymm
  · rw [Definitions.tensorPiece, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨⟨xs, hxs⟩, rfl⟩, rfl⟩
    change tensorToGraded L (word (tensorGenerator L) (homogeneousWord L xs)) ∈ _
    rw [tensorToGraded_word]
    subst d
    exact ⟨_, rfl⟩
  · apply gradedComponent_le L b degree hb B hB
    intro l hl
    let xs := orderedLetters L b degree hb l
    have hd : homogeneousWordDegree L xs = d := (orderedLetters_degree L b degree hb l).trans hl
    refine ⟨word (tensorGenerator L) (homogeneousWord L xs),
      Submodule.subset_span ⟨⟨xs, hd⟩, rfl⟩, ?_⟩
    change tensorToGraded L (word (tensorGenerator L) (homogeneousWord L xs)) = _
    rw [tensorToGraded_word, orderedSymbol_eq]

end Comparison

/-- The canonical algebra equivalence carries the two generators to their principal symbols
and identifies every length and parity component. -/
theorem associatedGraded :
    Specs.LieNotes.SuperRestricted.SuperPbw.associatedGradedType := by
  intro k V I _ _ _ _ _ L b degree hb
  obtain ⟨B, hB⟩ := orderedBasis_exists L b degree hb
  let e := AlgEquiv.ofBijective (tensorToGraded L)
    ((abelianToGraded_bijective L b degree hb).comp (abelianEquivTensor L).symm.bijective)
  have he (x : Even L) : e (evenLetter L x) = generatorSymbol L 0 x := by
    change tensorToGraded L (evenLetter L x) = generatorSymbol L 0 x
    rw [← tensorGenerator_even L x, tensorToGraded_generator, gradedGenerator, assemble_apply]
  have ho (x : Odd L) : e (oddLetter L x) = generatorSymbol L 1 x := by
    change tensorToGraded L (oddLetter L x) = generatorSymbol L 1 x
    rw [← tensorGenerator_odd L x, tensorToGraded_generator, gradedGenerator, assemble_apply]
  refine ⟨e, ⟨he, ho, tensorToGraded_map_piece L b degree hb B hB⟩, ?_⟩
  intro e' he'
  apply AlgEquiv.coe_toAlgHom_injective
  exact tensor_ext L (fun x => (he'.1 x).trans (he x).symm)
    (fun x => (he'.2.1 x).trans (ho x).symm)

universe z

/-- Super PBW for the enveloping quotient, its associated graded, and its graded modules. -/
theorem superPbw : Specs.LieNotes.SuperRestricted.SuperPbw.superPbwType.{u, v, w, z} :=
  ⟨by
      intro k V I _ _ _ _ _ L b degree hb
      exact orderedBasis_exists L b degree hb,
    associatedGraded, SuperEnvelopingModules.gradedModulesAgree⟩

end

end LieNotes.SuperRestricted.SuperPbw
