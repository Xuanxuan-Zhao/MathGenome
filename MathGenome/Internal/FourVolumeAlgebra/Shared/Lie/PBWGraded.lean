import MathGenome.Internal.FourVolumeAlgebra.Specs.Shared.Lie.PBWGraded
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.PBWOrdered
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort

namespace Shared.Lie.PBW.Graded
/-- The filtration certificate is provided by the accepted enveloping-algebra interface. -/
instance filtrationFact (k g : Type*) [CommRing k] [LieRing g] [LieAlgebra k g] :
    Fact (Specs.Shared.Lie.filtrationType k g) := ⟨filtration_properties k g⟩
end Shared.Lie.PBW.Graded

namespace Shared.Lie.PBW
attribute [local instance 100] LieRing.ofAssociativeRing
universe u v w
variable {k : Type u} {g : Type v} {ι : Type w}
  [CommRing k] [LieRing g] [LieAlgebra k g] [LinearOrder ι]

/-- Straightening never increases word length. This refines the upstream
spanning theorem; independence is supplied by the upstream PBW basis. -/
theorem monomial_mem_boundedSpan (b : Module.Basis ι k g) (l : List ι) (m : ℤ)
    (hm : (l.length : ℤ) ≤ m) : monomial b l ∈ boundedSpan b m := by
  classical
  induction l using (wordBelow_wellFounded (ι := ι)).induction generalizing m with
  | h l ih =>
    by_cases hs : l.Pairwise (· ≤ ·)
    · exact Submodule.subset_span ⟨⟨l, hs⟩, hm, rfl⟩
    obtain ⟨p, i, j, s, rfl, hji⟩ := exists_descent l hs
    rw [monomial_swap]
    apply (boundedSpan b m).add_mem
    · apply ih _ (swapped_word_below p s i j hji) m
      simpa using hm
    · apply map_mem_of_basis b (sandwich b p s) (boundedSpan b m) _ ⁅b i, b j⁆
      intro a
      have h := ih (p ++ a :: s) (bracket_word_below p s i j a) m (by
        simp only [List.length_append, List.length_cons, Nat.cast_add, Nat.cast_one] at hm ⊢
        omega)
      simpa only [monomial_append, monomial_cons, mul_assoc, sandwich_apply] using h

/-- Multilinearity expands an arbitrary word into basis words of the same length. -/
theorem word_mem_boundedSpan (b : Module.Basis ι k g) (xs : List g) (m : ℤ)
    (hm : (xs.length : ℤ) ≤ m) : word k g xs ∈ boundedSpan b m := by
  suffices ∀ (xs : List g) (p : List ι), ((p.length + xs.length : ℕ) : ℤ) ≤ m →
      monomial b p * word k g xs ∈ boundedSpan b m by
    simpa using this xs [] (by simpa using hm)
  intro xs
  induction xs with
  | nil =>
    intro p hp
    simpa [word] using monomial_mem_boundedSpan b p m (by simpa using hp)
  | cons x xs ih =>
    intro p hp
    let f : g →ₗ[k] U k g := (LinearMap.mulRight k (word k g xs)).comp
      ((LinearMap.mulLeft k (monomial b p)).comp (inclusion k g).toLinearMap)
    have hf : ∀ i, f (b i) ∈ boundedSpan b m := by
      intro i
      have h := ih (p ++ [i]) (by simpa [add_assoc, add_comm, add_left_comm] using hp)
      simpa [f, monomial_append, mul_assoc] using h
    have hx := map_mem_of_basis b f (boundedSpan b m) hf x
    simpa [f, word, mul_assoc] using hx

/-- The filtration is precisely the length filtration of the ordered PBW basis. -/
theorem filtration_eq_boundedSpan (b : Module.Basis ι k g) (m : ℤ) :
    filtration k g m = boundedSpan b m := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨xs, hxs, rfl⟩
    exact word_mem_boundedSpan b xs m hxs
  · apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    exact word_mem k g (l.val.map b) (by simpa using hl)

/-- Coefficients of words longer than the filtration step vanish. -/
theorem repr_eq_zero_of_mem_filtration (b : Module.Basis ι k g) {a : U k g} {m : ℤ}
    (ha : a ∈ filtration k g m) (l : OrderedWord ι) (hl : m < (l.val.length : ℤ)) :
    (orderedBasis b).repr a l = 0 := by
  classical
  rw [filtration_eq_boundedSpan b m] at ha
  have hs : a ∈ Submodule.span k ((orderedBasis b) '' {l | (l.val.length : ℤ) ≤ m}) := by
    convert ha using 1
    congr 1
    ext a
    simp only [Set.mem_image, Set.mem_ofPred_eq, orderedBasis_apply]
  have ht := (orderedBasis b).repr_support_subset_of_mem_span _ hs
  apply Finsupp.notMem_support_iff.mp
  intro hmem
  exact (not_le_of_gt hl) (ht hmem)

end Shared.Lie.PBW

namespace Shared.Lie.PBW.Graded
open scoped DirectSum
universe u v w
variable {k : Type u} {g : Type v} {ι : Type w}
  [CommRing k] [LieRing g] [LieAlgebra k g] [LinearOrder ι]
  [hF : Fact (Specs.Shared.Lie.filtrationType k g)]

private noncomputable def topFilter (n : ℕ) :
    (OrderedWord ι →₀ k) →ₗ[k] (OrderedWord ι →₀ k) where
  toFun := Finsupp.filter (fun l => l.val.length = n)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

/-- Projection to the length-n PBW coefficients, descending to F_n/F_(n-1). -/
noncomputable def topCoordinates (b : Module.Basis ι k g) (n : ℕ) :
    Piece k g n →ₗ[k] (OrderedWord ι →₀ k) :=
  (lower k g n).liftQ
    (((topFilter n).comp (orderedBasis b).repr.toLinearMap).comp (Step k g n).subtype) (by
      intro a ha
      apply Finsupp.ext
      intro l
      change ((orderedBasis b).repr a.val).filter (fun l => l.val.length = n) l = 0
      by_cases hl : l.val.length = n
      · rw [Finsupp.filter_apply]
        simp only [hl, ite_true]
        exact repr_eq_zero_of_mem_filtration b ha l (by rw [hl]; omega)
      · exact Finsupp.filter_apply_neg _ _ hl)

omit hF in
@[simp] theorem topCoordinates_principal (b : Module.Basis ι k g) (n : ℕ) (a : Step k g n) :
    topCoordinates b n (principal k g n a) =
      ((orderedBasis b).repr a.val).filter (fun l => l.val.length = n) := rfl

noncomputable def recoverGraded (b : Module.Basis ι k g) :
    Associated k g →ₗ[k] (OrderedWord ι →₀ k) :=
  DirectSum.toModule k ℕ (OrderedWord ι →₀ k) (topCoordinates b)

@[simp] theorem recoverGraded_gradedWord (b : Module.Basis ι k g) (l : OrderedWord ι) :
    recoverGraded b (gradedWord b l) = Finsupp.single l 1 := by
  change recoverGraded b (DirectSum.lof k ℕ (Piece k g) l.val.length
    (principal k g l.val.length _)) = _
  rw [recoverGraded, DirectSum.toModule_lof, topCoordinates_principal]
  change Finsupp.filter (fun t : OrderedWord ι => t.val.length = l.val.length)
    ((orderedBasis b).repr (orderedMonomial b l)) = _
  rw [← orderedBasis_apply b l, (orderedBasis b).repr_self]
  exact Finsupp.filter_single_of_pos _ rfl

theorem gradedWord_independent (b : Module.Basis ι k g) :
    LinearIndependent k (gradedWord b) := by
  apply LinearIndependent.of_comp (recoverGraded b)
  simpa only [Function.comp_def, recoverGraded_gradedWord] using
    (Finsupp.linearIndependent_single_one k (OrderedWord ι) : LinearIndependent k
      (fun l : OrderedWord ι => Finsupp.single l (1 : k)))

/-- Raising the degree of an element from a strictly lower step gives zero. -/
theorem symbol_eq_zero_of_lower {n : ℕ} (a : Step k g n)
    (ha : a.val ∈ filtration k g ((n : ℤ)-1)) : symbol k g n a = 0 := by
  change DirectSum.lof k ℕ (Piece k g) n (principal k g n a) = 0
  rw [show principal k g n a = 0 from (Submodule.Quotient.mk_eq_zero _).mpr ha, map_zero]

theorem symbol_mem_degree_span (b : Module.Basis ι k g) (n : ℕ)
    (a : Step k g n) : symbol k g n a ∈ Submodule.span k ((gradedWord b) '' {l | l.val.length = n}) := by
  have ha := a.property
  change a.val ∈ filtration k g n at ha
  rw [filtration_eq_boundedSpan b n] at ha
  have ht : ∀ (x : U k g) (hx : x ∈ boundedSpan b n),
      symbol k g n ⟨x, (filtration_eq_boundedSpan b n).ge hx⟩ ∈
        Submodule.span k ((gradedWord b) '' {l | l.val.length = n}) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      by_cases he : l.val.length = n
      · subst n
        exact Submodule.subset_span ⟨l, rfl, rfl⟩
      · rw [symbol_eq_zero_of_lower _ (by
          apply filtration_mono k g (show (l.val.length : ℤ) ≤ (n : ℤ)-1 by omega)
          exact word_mem k g (l.val.map b) (by simp))]
        exact Submodule.zero_mem _
    | zero =>
      change symbol k g n (0 : Step k g n) ∈ _
      rw [map_zero]
      exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      change symbol k g n (⟨x, (filtration_eq_boundedSpan b n).ge hx⟩ +
        ⟨y, (filtration_eq_boundedSpan b n).ge hy⟩ : Step k g n) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
    | smul r x hx ih =>
      change symbol k g n (r • ⟨x, (filtration_eq_boundedSpan b n).ge hx⟩ : Step k g n) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ r ih
  exact ht a.val ha

theorem gradedWord_span (b : Module.Basis ι k g) :
    Submodule.span k (Set.range (gradedWord b)) = ⊤ := by
  apply top_unique
  intro a ha
  clear ha
  induction a using DirectSum.induction_on with
  | zero => exact Submodule.zero_mem _
  | add a b ha hb => exact Submodule.add_mem _ ha hb
  | of n q =>
    induction q using Submodule.Quotient.induction_on with
    | _ a =>
      exact (Submodule.span_mono (Set.image_subset_range ..)) (symbol_mem_degree_span b n a)

noncomputable def gradedBasis (b : Module.Basis ι k g) :
    Module.Basis (OrderedWord ι) k (Associated k g) :=
  Module.Basis.mk (gradedWord_independent b) (by rw [gradedWord_span b])

@[simp] theorem gradedBasis_apply (b : Module.Basis ι k g) (l : OrderedWord ι) :
    gradedBasis b l = gradedWord b l := Module.Basis.mk_apply _ _ _

end Shared.Lie.PBW.Graded

namespace Shared.Lie.PBW.Graded
open scoped DirectSum
universe u v w
variable {k : Type u} {g : Type v} {ι : Type w}
  [CommRing k] [LieRing g] [LieAlgebra k g] [LinearOrder ι]

/-- Sorted lists and finite exponent vectors are two indices for the same monomials. -/
noncomputable def orderedWordExponents : OrderedWord ι ≃ (ι →₀ ℕ) where
  toFun l := Multiset.toFinsupp (l.val : Multiset ι)
  invFun d := ⟨d.toMultiset.sort (· ≤ ·), Multiset.pairwise_sort _ _⟩
  left_inv l := by
    apply Subtype.ext
    simp only [Multiset.toFinsupp_toMultiset, Multiset.coe_sort]
    exact List.mergeSort_eq_self _ l.property
  right_inv d := by simp

private theorem polynomial_list_monomial (l : List ι) :
    MvPolynomial.monomial (Multiset.toFinsupp (l : Multiset ι)) (1 : k) =
      (l.map (MvPolynomial.X : ι → MvPolynomial ι k)).prod := by
  induction l with
  | nil => simp [Multiset.toFinsupp_zero]
  | cons i l ih =>
    have he : Multiset.toFinsupp ((i::l : List ι) : Multiset ι) =
        Finsupp.single i 1 + Multiset.toFinsupp (l : Multiset ι) := by
      change Multiset.toFinsupp ({i} + (l : Multiset ι)) = _
      rw [map_add, Multiset.toFinsupp_singleton]
    rw [he, MvPolynomial.monomial_single_add, pow_one, ih]
    rfl

noncomputable def orderedSymmetricBasis (b : Module.Basis ι k g) :
    Module.Basis (OrderedWord ι) k (SymmetricAlgebra k g) :=
  b.symmetricAlgebra.reindex orderedWordExponents.symm

@[simp] theorem orderedSymmetricBasis_apply (b : Module.Basis ι k g) (l : OrderedWord ι) :
    orderedSymmetricBasis b l = symmetricWord (l.val.map b) := by
  apply (SymmetricAlgebra.equivMvPolynomial b).injective
  simp only [orderedSymmetricBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    Module.Basis.symmetricAlgebra, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.apply_symm_apply, MvPolynomial.coe_basisMonomials]
  change MvPolynomial.monomial (orderedWordExponents l) (1 : k) = _
  rw [show orderedWordExponents l = Multiset.toFinsupp (l.val : Multiset ι) from rfl,
    polynomial_list_monomial]
  simp only [symmetricWord, map_list_prod, List.map_map, Function.comp_def,
    SymmetricAlgebra.equivMvPolynomial_ι_apply]

variable [hF : Fact (Specs.Shared.Lie.filtrationType k g)]

/-- A product of generators maps to its principal symbol, in its actual length. -/
theorem canonicalMap_word (xs : List g) :
    canonicalMap (k := k) (g := g) (symmetricWord xs) =
      symbol k g xs.length ⟨word k g xs, Submodule.subset_span ⟨xs, le_rfl, rfl⟩⟩ := by
  induction xs with
  | nil => simp [symmetricWord, word, symbol_one]
  | cons x xs ih =>
    have he : symmetricWord (x::xs) = SymmetricAlgebra.ι k g x * symmetricWord xs := by
      simp [symmetricWord]
    rw [he, map_mul, canonicalMap_generator, ih]
    change symbol k g 1 ⟨inclusion k g x, _⟩ * symbol k g xs.length _ = _
    rw [symbol_mul]
    have hn : 1+xs.length = (x::xs).length := by simp [add_comm]
    apply symbol_congr _ _ hn
    simp [word]

@[simp] theorem canonicalMap_orderedWord (b : Module.Basis ι k g) (l : OrderedWord ι) :
    canonicalMap (k := k) (g := g) (symmetricWord (l.val.map b)) = gradedWord b l := by
  rw [canonicalMap_word]
  apply symbol_congr _ _ (List.length_map ..)
  rfl

end Shared.Lie.PBW.Graded

namespace Shared.Lie.PBW.Graded
open scoped DirectSum
universe u v w
variable {k : Type u} {g : Type v} {ι : Type w}
  [CommRing k] [LieRing g] [LieAlgebra k g] [LinearOrder ι]
  [hF : Fact (Specs.Shared.Lie.filtrationType k g)]

/-- The canonical algebra map is the linear equivalence matching the two monomial bases. -/
theorem canonicalMap_eq_basisEquiv (b : Module.Basis ι k g) :
    (canonicalMap (k := k) (g := g)).toLinearMap =
      ((orderedSymmetricBasis b).equiv (gradedBasis b) (Equiv.refl _)).toLinearMap := by
  apply (orderedSymmetricBasis b).ext
  intro l
  change canonicalMap (k := k) (g := g) (orderedSymmetricBasis b l) =
    (orderedSymmetricBasis b).equiv (gradedBasis b) (Equiv.refl _) (orderedSymmetricBasis b l)
  rw [Module.Basis.equiv_apply, orderedSymmetricBasis_apply, canonicalMap_orderedWord,
    Equiv.refl_apply, gradedBasis_apply]

theorem canonicalMap_bijective_of_basis (b : Module.Basis ι k g) :
    Function.Bijective (canonicalMap (k := k) (g := g)) := by
  change Function.Bijective (canonicalMap (k := k) (g := g)).toLinearMap
  rw [canonicalMap_eq_basisEquiv b]
  exact LinearEquiv.bijective _

/-- Each homogeneous component is mapped onto its actual quotient summand. -/
theorem canonicalMap_degree (b : Module.Basis ι k g) (n : ℕ) :
    Submodule.map (canonicalMap (k := k) (g := g)).toLinearMap
      (symmetricDegree (k := k) (g := g) n) =
        LinearMap.range (DirectSum.lof k ℕ (Piece k g) n) := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨xs, hxs, rfl⟩
    change canonicalMap (k := k) (g := g) (symmetricWord (k := k) xs) ∈
      LinearMap.range (DirectSum.lof k ℕ (Piece k g) n)
    rw [canonicalMap_word]
    subst n
    exact ⟨principal k g xs.length _, rfl⟩
  · rintro _ ⟨q, rfl⟩
    induction q using Submodule.Quotient.induction_on with
    | _ a =>
      have h := symbol_mem_degree_span b n a
      apply (Submodule.span_le.mpr ?_) h
      rintro _ ⟨l, hl, rfl⟩
      refine ⟨symmetricWord (l.val.map b), ?_, canonicalMap_orderedWord b l⟩
      exact Submodule.subset_span ⟨l.val.map b, by simpa using hl, rfl⟩

end Shared.Lie.PBW.Graded

namespace Shared.Lie.PBW.Graded
universe u v
variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]
  [Module.Free k g]

/-- PBW does not require a chosen order in its coordinate-free formulation. -/
theorem canonicalMap_bijective : Function.Bijective (canonicalMap (k := k) (g := g)) := by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex k g) := IsWellOrder.linearOrder WellOrderingRel
  exact canonicalMap_bijective_of_basis (Module.Free.chooseBasis k g)

/-- The canonical graded PBW algebra isomorphism. -/
noncomputable def pbwEquiv : SymmetricAlgebra k g ≃ₐ[k] Associated k g :=
  AlgEquiv.ofBijective (canonicalMap (k := k) (g := g)) canonicalMap_bijective

@[simp] theorem pbwEquiv_generator (x : g) :
    pbwEquiv (k := k) (g := g) (SymmetricAlgebra.ι k g x) = generator (k := k) (g := g) x :=
  canonicalMap_generator x

end Shared.Lie.PBW.Graded

namespace Shared.Lie.PBW
universe u v w

theorem filteredBasis_spec : Specs.Shared.Lie.PBW.filteredBasisExpected.{u,v,w} := by
  intro k g ι _ _ _ _ b m
  exact filtration_eq_boundedSpan b m

theorem graded_spec : Specs.Shared.Lie.PBW.gradedExpected.{u,v,w} := by
  intro k g _ _ _ _
  refine ⟨filtration_properties k g, ?_⟩
  let : Fact (Specs.Shared.Lie.filtrationType k g) := ⟨filtration_properties k g⟩
  refine ⟨Graded.canonicalMap_bijective, ?_, ?_⟩
  · classical
    let : LinearOrder (Module.Free.ChooseBasisIndex k g) := IsWellOrder.linearOrder WellOrderingRel
    exact Graded.canonicalMap_degree (Module.Free.chooseBasis k g)
  · intro ι _ b
    exact ⟨Graded.gradedBasis b, fun l => ⟨Graded.gradedBasis_apply b l,
      Graded.canonicalMap_orderedWord b l⟩⟩

end Shared.Lie.PBW
