import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.SuperEnveloping

namespace LieNotes.SuperRestricted.SuperEnveloping

open scoped DirectSum

noncomputable section

universe u v

abbrev relator := @Construction.relator
abbrev relations := @Construction.relations
abbrev relationIdeal := @Construction.relationIdeal
abbrev Enveloping := @Construction.Enveloping
abbrev quotientMap := @Construction.quotientMap
abbrev ι := @Construction.ι
abbrev tensorParity := @Construction.tensorParity
abbrev tensorPiece := @Construction.tensorPiece
abbrev parity := @Construction.parity
abbrev piece := @Construction.piece
abbrev word := @Construction.word
abbrev wordFiltration := @Construction.wordFiltration
abbrev filtration := @Construction.filtration
abbrev filteredPiece := @Construction.filteredPiece
abbrev Degree := Construction.Degree
abbrev filtered := @Construction.filtered
abbrev lower := @Construction.lower
abbrev GradedPiece := @Construction.GradedPiece
abbrev symbol := @Construction.symbol
abbrev gradedProduct := @Construction.gradedProduct
abbrev AssociatedGraded := @Construction.AssociatedGraded
abbrev ofSymbol := @Construction.ofSymbol

open Construction (parityScalar generatorParity mem_paritySpace paritySpace paritySpace_internal
  tensorParity_ι tensorParity_involutive parity_quotientMap parity_involutive)

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]
  [NeZero (2 : k)] (L : LieSuperalgebra k V)

theorem quotientMap_surjective : Function.Surjective (quotientMap L) :=
  (relationIdeal L).ringCon.mkₐ_surjective

theorem quotientMap_eq_zero_iff (x : TensorAlgebra k V) :
    quotientMap L x = 0 ↔ x ∈ relationIdeal L :=
  Construction.quotientMap_eq_zero_iff L x

theorem generator_relation {i j : ZMod 2} {x y : V} (hx : x ∈ L.grading.piece i)
    (hy : y ∈ L.grading.piece j) :
    ι L x * ι L y - paritySign k i j • (ι L y * ι L x) = ι L (L.bracket x y) := by
  have h := (quotientMap_eq_zero_iff L _).mpr
    (TwoSidedIdeal.subset_span (s := relations L) ⟨i, j, x, y, hx, hy, rfl⟩)
  simp only [Construction.relator, map_sub, map_mul, map_smul] at h
  exact sub_eq_zero.mp h

theorem relator_mem_tensorPiece {i j : ZMod 2} {x y : V} (hx : x ∈ L.grading.piece i)
    (hy : y ∈ L.grading.piece j) :
    relator L i j x y ∈ tensorPiece L.grading (i + j) :=
  (mem_paritySpace ..).mpr (Construction.tensorParity_relator L hx hy)

omit [NeZero (2 : k)] in
/-- Each tensor word in homogeneous letters has the sum of its letters' parities. -/
theorem tensorWord_mem (G : Grading k V) (xs : List (Σ i, G.piece i)) :
    word (TensorAlgebra.ι k) (xs.map fun x => (x.2 : V)) ∈
      tensorPiece G (xs.map Sigma.fst).sum := by
  induction xs with
  | nil =>
    simpa [Construction.word] using
      (SetLike.GradedOne.one_mem (A := tensorPiece G))
  | cons x xs ih =>
    simpa only [Construction.word, List.map_cons, List.prod_cons, List.sum_cons] using
      SetLike.GradedMul.mul_mem
        (show TensorAlgebra.ι k (x.2 : V) ∈ tensorPiece G x.1 from
          (mem_paritySpace ..).mpr (tensorParity_ι G x.2.2)) ih

theorem quotientMap_mem_piece {i : ZMod 2} {x : TensorAlgebra k V}
    (hx : x ∈ tensorPiece L.grading i) : quotientMap L x ∈ piece L i := by
  apply (mem_paritySpace ..).mpr
  change parity L (quotientMap L x) = _
  rw [parity_quotientMap, show tensorParity L.grading x = _ from (mem_paritySpace ..).mp hx,
    map_smul]

/-- Every parity-homogeneous element of the quotient has a lift of the same parity. -/
theorem tensorPiece_image (i : ZMod 2) :
    (tensorPiece L.grading i).map (quotientMap L).toLinearMap = piece L i := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact quotientMap_mem_piece L hx
  · intro y hy
    obtain ⟨x, rfl⟩ := quotientMap_surjective L y
    have hs := Construction.parityScalar_sq (k := k) i
    have hy' : quotientMap L (tensorParity L.grading x) =
        parityScalar k i • quotientMap L x := by
      rw [← parity_quotientMap]
      exact (mem_paritySpace ..).mp hy
    refine ⟨(2 : k)⁻¹ • (x + parityScalar k i • tensorParity L.grading x), ?_, ?_⟩
    · apply (mem_paritySpace ..).mpr
      change tensorParity L.grading ((2 : k)⁻¹ • (x + parityScalar k i • tensorParity L.grading x)) =
        _
      simp only [map_smul, map_add, tensorParity_involutive L.grading x]
      rw [smul_comm (parityScalar k i) ((2 : k)⁻¹), smul_add (parityScalar k i),
        smul_smul, hs, one_smul, add_comm (tensorParity L.grading x)]
    · change quotientMap L ((2 : k)⁻¹ • (x + parityScalar k i • tensorParity L.grading x)) =
        quotientMap L x
      rw [map_smul, map_add, map_smul, hy', smul_smul, hs, one_smul, ← two_smul k,
        smul_smul, inv_mul_cancel₀ (NeZero.ne (2 : k)), one_smul]

theorem ι_mem_piece {i : ZMod 2} {x : V} (hx : x ∈ L.grading.piece i) :
    ι L x ∈ piece L i :=
  quotientMap_mem_piece L ((mem_paritySpace ..).mpr (tensorParity_ι L.grading hx))

theorem filtration_mono : Monotone (filtration L) :=
  Construction.wordFiltration_mono _

theorem filtration_negative {n : ℤ} (hn : n < 0) : filtration L n = ⊥ :=
  Construction.wordFiltration_negative _ hn

theorem filtration_mul {m n : ℤ} {x y : Enveloping L}
    (hx : x ∈ filtration L m) (hy : y ∈ filtration L n) :
    x * y ∈ filtration L (m + n) :=
  Construction.wordFiltration_mul _ hx hy

theorem ι_mem_filtration (x : V) : ι L x ∈ filtration L 1 :=
  Construction.wordFiltration_generator _ x

private theorem quotientMap_word (xs : List V) :
    quotientMap L (word (TensorAlgebra.ι k) xs) = word (ι L) xs :=
  (List.prod_map_hom xs (TensorAlgebra.ι k) (quotientMap L)).symm

/-- The filtration is the image of the tensor algebra's word-length filtration. -/
theorem filtration_image (n : ℤ) :
    (wordFiltration (TensorAlgebra.ι k (M := V)) n).map (quotientMap L).toLinearMap =
      filtration L n := by
  simp only [Construction.wordFiltration, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨xs, h, rfl⟩, rfl⟩
    exact ⟨xs, h, quotientMap_word L xs⟩
  · rintro ⟨xs, h, rfl⟩
    exact ⟨_, ⟨xs, h, rfl⟩, quotientMap_word L xs⟩

theorem filtration_exhaustive (x : Enveloping L) : ∃ n : ℕ, x ∈ filtration L n := by
  obtain ⟨t, rfl⟩ := quotientMap_surjective L x
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    exact ⟨0, by simpa using Construction.wordFiltration_algebraMap (ι L) r⟩
  | ι x =>
    exact ⟨1, ι_mem_filtration L x⟩
  | mul a b ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    exact ⟨m+n, by simpa using filtration_mul L hm hn⟩
  | add a b ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨max m n, ?_⟩
    rw [map_add]
    exact Submodule.add_mem _ (filtration_mono L (by exact_mod_cast le_max_left m n) hm)
      (filtration_mono L (by exact_mod_cast le_max_right m n) hn)

private theorem parity_word (xs : List V) :
    parity L (word (ι L) xs) = word (ι L) (xs.map (generatorParity L.grading)) := by
  induction xs with
  | nil => simp [Construction.word]
  | cons x xs ih =>
    have hx : parity L (ι L x) = ι L (generatorParity L.grading x) := by
      change parity L (quotientMap L (TensorAlgebra.ι k x)) = _
      rw [parity_quotientMap]
      simp [Construction.tensorParity, Construction.ι]
    simp only [Construction.word, List.map_cons, List.prod_cons] at ih ⊢
    rw [map_mul, ih, hx]

theorem parity_filtration {n : ℤ} {x : Enveloping L} (hx : x ∈ filtration L n) :
    parity L x ∈ filtration L n := by
  apply (show filtration L n ≤ (filtration L n).comap (parity L).toLinearMap from ?_) hx
  apply Submodule.span_le.mpr
  rintro _ ⟨xs, h, rfl⟩
  change parity L (word (ι L) xs) ∈ filtration L n
  rw [parity_word]
  exact Construction.word_mem _ (by simpa using h)

/-- Each filtration step splits as the internal sum of its two parity parts. -/
theorem filtration_isInternal (n : ℤ) :
    DirectSum.IsInternal (fun i => (piece L i).comap (filtration L n).subtype) := by
  let F := filtration L n
  let s : F →ₗ[k] F := ((parity L).toLinearMap.comp F.subtype).codRestrict F
    (fun x => parity_filtration L x.2)
  have hs : Function.Involutive s := fun x => Subtype.ext (parity_involutive L x.1)
  have heq : paritySpace s = fun i => (piece L i).comap F.subtype := by
    funext i
    ext x
    rw [mem_paritySpace]
    change s x = _ ↔ x.1 ∈ piece L i
    rw [mem_paritySpace]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [← heq]
  exact paritySpace_internal s hs

/-- The denominator is the entire preceding step of the same parity. -/
theorem lower_eq (d : Degree) :
    lower L d = (filteredPiece L ((d.1 : ℤ) - 1) d.2).comap (filtered L d).subtype := by
  ext x
  change x.1 ∈ filtration L ((d.1 : ℤ) - 1) ↔
    x.1 ∈ filtration L ((d.1 : ℤ) - 1) ∧ x.1 ∈ piece L d.2
  exact ⟨fun hx => ⟨hx, x.2.2⟩, And.left⟩

theorem lower_zero (i : ZMod 2) : lower L (0, i) = ⊥ := by
  change (filtration L (-1)).comap (filtered L (0, i)).subtype = ⊥
  rw [filtration_negative L (n := -1) (by decide)]
  exact Submodule.ker_subtype _

theorem gradedProduct_eq_symbol (d e : Degree) (x : filtered L d) (y : filtered L e)
    (h : x.1 * y.1 ∈ filtered L (d + e)) :
    gradedProduct L d e (symbol L d x) (symbol L e y) =
      symbol L (d + e) ⟨x.1 * y.1, h⟩ :=
  Construction.gradedProduct_symbol L x y

/-- The multiplication on the whole associated graded agrees with that on homogeneous symbols. -/
theorem ofSymbol_mul (d e : Degree) (x : filtered L d) (y : filtered L e) :
    ofSymbol L d x * ofSymbol L e y =
      DirectSum.lof k Degree (GradedPiece L) (d + e)
        (gradedProduct L d e (symbol L d x) (symbol L e y)) := by
  change DirectSum.lof k Degree (GradedPiece L) d (symbol L d x) *
      DirectSum.lof k Degree (GradedPiece L) e (symbol L e y) = _
  simp only [DirectSum.lof_eq_of, DirectSum.of_mul_of]
  rfl

end

end LieNotes.SuperRestricted.SuperEnveloping
