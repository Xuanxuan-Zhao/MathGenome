import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Symmetrization
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PBWSpecialization
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.TrivSqZeroExt.Basic

set_option maxHeartbeats 800000

namespace LieAlgebrasAndRepresentations.Symmetrization
open Shared.Lie Shared.Lie.PBW.Graded
attribute [local instance 100] LieRing.ofAssociativeRing
universe u v
variable {k : Type u} {g : Type v} [Field k] [CharZero k] [LieRing g] [LieAlgebra k g]

theorem average_multilinear :
    Specs.LieAlgebrasAndRepresentations.Symmetrization.averageMultilinearExpected.{u,v} := by
  intro k g _ _ _ _ n
  classical
  let P : MultilinearMap k (fun _ : Fin n => g) (U k g) :=
    (MultilinearMap.mkPiAlgebraFin k n (U k g)).compLinearMap
      (fun _ => (inclusion k g).toLinearMap)
  refine ⟨(n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n), P.domDomCongr σ, ?_⟩
  intro y
  simp only [smul_apply, sum_apply, average]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  simp [P, MultilinearMap.domDomCongr, MultilinearMap.mkPiAlgebraFin_apply,
    word, List.map_ofFn, Function.comp_def]

theorem average_symmetric :
    Specs.LieAlgebrasAndRepresentations.Symmetrization.averageSymmetricExpected.{u,v} := by
  intro k g _ _ _ _ n y τ
  classical
  unfold average
  congr 1
  simpa only [Function.comp_assoc, Equiv.Perm.coe_mul] using
    (Fintype.sum_equiv (Equiv.mulLeft τ)
      (fun σ : Equiv.Perm (Fin n) => word k g (List.ofFn ((y ∘ τ) ∘ σ)))
      (fun σ : Equiv.Perm (Fin n) => word k g (List.ofFn (y ∘ σ)))
      (fun _ => rfl))

theorem average_filtered :
    Specs.LieAlgebrasAndRepresentations.Symmetrization.averageFilteredExpected.{u,v} := by
  intro k g _ _ _ _ n y
  classical
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro σ _
  exact Submodule.subset_span ⟨List.ofFn (y ∘ σ), by simp, rfl⟩

theorem average_empty :
    Specs.LieAlgebrasAndRepresentations.Symmetrization.averageEmptyExpected.{u,v} := by
  intro k g _ _ _ _ y
  simp [average, word]

theorem average_singleton :
    Specs.LieAlgebrasAndRepresentations.Symmetrization.averageSingletonExpected.{u,v} := by
  intro k g _ _ _ _ y
  simp [average, word, List.ofFn_succ]

private theorem tuple_word_symbol [Fact (Specs.Shared.Lie.filtrationType k g)]
    (n : ℕ) (y : Fin n → g) :
    symbol k g n ⟨word k g (List.ofFn y),
      Submodule.subset_span ⟨List.ofFn y, by simp, rfl⟩⟩ =
        canonicalMap (k := k) (g := g) (symmetricWord (List.ofFn y)) := by
  rw [canonicalMap_word]
  apply symbol_congr _ _ (by simp)
  rfl

private theorem symmetricWord_perm (n : ℕ) (y : Fin n → g) (σ : Equiv.Perm (Fin n)) :
    symmetricWord (k := k) (List.ofFn (y ∘ σ)) = symmetricWord (List.ofFn y) :=
  ((σ.ofFn_comp_perm y).map (SymmetricAlgebra.ι k g)).prod_eq

/-- Averaging leaves every principal symbol unchanged, including degree zero. -/
theorem average_symbol [Fact (Specs.Shared.Lie.filtrationType k g)]
    (n : ℕ) (y : Fin n → g) :
    symbol k g n ⟨average n y, average_filtered k g n y⟩ =
      canonicalMap (k := k) (g := g) (symmetricWord (List.ofFn y)) := by
  classical
  let W (σ : Equiv.Perm (Fin n)) : Step k g n :=
    ⟨word k g (List.ofFn (y ∘ σ)),
      Submodule.subset_span ⟨List.ofFn (y ∘ σ), by simp, rfl⟩⟩
  have he : (⟨average n y, average_filtered k g n y⟩ : Step k g n) =
      (n.factorial : k)⁻¹ • ∑ σ, W σ := by
    apply Subtype.ext
    simp [average, W]
  rw [he, map_smul, map_sum]
  have hw (σ : Equiv.Perm (Fin n)) :
      symbol k g n (W σ) = canonicalMap (k := k) (g := g) (symmetricWord (List.ofFn y)) := by
    rw [show W σ = _ from rfl, tuple_word_symbol, symmetricWord_perm]
  have hn : (n.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  simp only [hw, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul k, smul_smul]
  rw [inv_mul_cancel₀ hn, one_smul]

/-- The formula already forces filtration preservation; bijectivity is separate. -/
theorem formula_filtered (s : SymmetricAlgebra k g →ₗ[k] U k g) (hs : HasFormula s)
    (m : ℤ) : symmetricFiltration m ≤ (filtration k g m).comap s := by
  apply Submodule.span_le.mpr
  rintro _ ⟨xs, hxs, rfl⟩
  change s (symmetricWord xs) ∈ filtration k g m
  have hv : s (symmetricWord xs) = average xs.length xs.get := by
    simpa using hs xs.length xs.get
  rw [hv]
  exact (Shared.Lie.filtration_properties k g).1 hxs (average_filtered k g _ _)

/-- Formula (1.2) also determines the map on all homogeneous elements. -/
theorem formula_topSymbol [Fact (Specs.Shared.Lie.filtrationType k g)]
    (s : SymmetricAlgebra k g →ₗ[k] U k g) (hs : HasFormula s) : HasTopSymbol s := by
  intro n a ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨xs, hxs, rfl⟩ := ha
    subst n
    have hv : s (symmetricWord xs) = average xs.length xs.get := by
      simpa using hs xs.length xs.get
    refine ⟨by rw [hv]; exact average_filtered k g _ _, ?_⟩
    simpa only [hv, List.ofFn_get] using average_symbol xs.length xs.get
  | zero =>
    refine ⟨by simp, ?_⟩
    simp only [map_zero]
    change symbol k g n 0 = 0
    exact map_zero _
  | add a b ha hb iha ihb =>
    obtain ⟨ha', hsa⟩ := iha
    obtain ⟨hb', hsb⟩ := ihb
    refine ⟨by simpa only [map_add] using (filtration k g n).add_mem ha' hb', ?_⟩
    simp only [map_add]
    change symbol k g n (⟨s a, ha'⟩ + ⟨s b, hb'⟩) = canonicalMap a + canonicalMap b
    rw [map_add, hsa, hsb]
  | smul r a ha ih =>
    obtain ⟨ha', hsa⟩ := ih
    refine ⟨by simpa only [map_smul] using (filtration k g n).smul_mem r ha', ?_⟩
    simp only [map_smul]
    change symbol k g n (r • ⟨s a, ha'⟩) = r • canonicalMap a
    rw [map_smul, hsa]

/-- There is at most one linear map with the displayed formula. -/
theorem formula_unique (s t : SymmetricAlgebra k g →ₗ[k] U k g)
    (hs : HasFormula s) (ht : HasFormula t) : s = t := by
  classical
  letI : LinearOrder (Module.Free.ChooseBasisIndex k g) := IsWellOrder.linearOrder WellOrderingRel
  apply (orderedSymmetricBasis (Module.Free.chooseBasis k g)).ext
  intro l
  rw [orderedSymmetricBasis_apply]
  have h := (hs (l.val.map (Module.Free.chooseBasis k g)).length
    (l.val.map (Module.Free.chooseBasis k g)).get).trans
    (ht (l.val.map (Module.Free.chooseBasis k g)).length
      (l.val.map (Module.Free.chooseBasis k g)).get).symm
  simpa using h

private theorem average_congr {m n : ℕ} (h : m = n) (y : Fin m → g) (z : Fin n → g)
    (hy : ∀ i, y i = z (Fin.cast h i)) : (average m y : U k g) = average n z := by
  subst n
  congr 1
  exact funext hy

/-- Symmetry and multilinearity descend the average to the entire symmetric algebra.
A basis is used only to construct the linear extension, not in its formula. -/
theorem exists_formula : ∃ s : SymmetricAlgebra k g →ₗ[k] U k g, HasFormula s := by
  classical
  letI : LinearOrder (Module.Free.ChooseBasisIndex k g) := IsWellOrder.linearOrder WellOrderingRel
  let b := Module.Free.chooseBasis k g
  let B := orderedSymmetricBasis b
  let s : SymmetricAlgebra k g →ₗ[k] U k g :=
    B.constr k (fun l => average l.val.length (fun i => b (l.val.get i)))
  refine ⟨s, ?_⟩
  intro n y
  obtain ⟨A, hA⟩ := average_multilinear k g n
  let P : MultilinearMap k (fun _ : Fin n => g) (SymmetricAlgebra k g) :=
    (MultilinearMap.mkPiAlgebraFin k n (SymmetricAlgebra k g)).compLinearMap
      (fun _ => SymmetricAlgebra.ι k g)
  have hP (z : Fin n → g) : P z = symmetricWord (List.ofFn z) := by
    simp [P, MultilinearMap.mkPiAlgebraFin_apply, symmetricWord, List.map_ofFn,
      Function.comp_def]
  have h : s.compMultilinearMap P = A := by
    apply Module.Basis.ext_multilinear (fun _ => b)
    intro v
    let σ := Tuple.sort v
    let l : Shared.Lie.PBW.OrderedWord (Module.Free.ChooseBasisIndex k g) :=
      ⟨List.ofFn (v ∘ σ), (Tuple.monotone_sort v).sortedLE_ofFn.pairwise⟩
    have hl : l.val.map b = List.ofFn ((fun i => b (v i)) ∘ σ) := by
      simp [l, List.map_ofFn, Function.comp_def]
    have he : symmetricWord (List.ofFn (fun i => b (v i))) = B l := by
      rw [orderedSymmetricBasis_apply, hl, symmetricWord_perm]
    rw [LinearMap.compMultilinearMap_apply, hP, he]
    change B.constr k _ (B l) = _
    rw [Module.Basis.constr_basis, hA]
    refine (average_congr (by simp [l]) _ (fun i : Fin n => b (v (σ i))) ?_).trans
      (average_symmetric k g n (fun i => b (v i)) σ)
    intro i
    simp only [l, List.get_eq_getElem, List.getElem_ofFn]
    congr 3
  
  have hh := congrArg (fun f : MultilinearMap k (fun _ : Fin n => g) (U k g) => f y) h
  simpa [hP, hA] using hh

private theorem symbol_eq_iff (n : ℕ) (a b : Step k g n) :
    symbol k g n a = symbol k g n b ↔
      a.val - b.val ∈ filtration k g ((n : ℤ) - 1) := by
  change DirectSum.lof k ℕ (Piece k g) n (principal k g n a) =
    DirectSum.lof k ℕ (Piece k g) n (principal k g n b) ↔ _
  constructor
  · intro h
    exact (Submodule.Quotient.eq (lower k g n)).mp (DirectSum.of_injective (β := Piece k g) n h)
  · intro h
    exact congrArg (DirectSum.lof k ℕ (Piece k g) n) ((Submodule.Quotient.eq (lower k g n)).mpr h)

section Ordered
variable {ι : Type*} [LinearOrder ι] (b : Module.Basis ι k g)
open Shared.Lie.PBW

/-- The ordered PBW comparison, used only for the proof of invertibility. -/
private noncomputable def orderedComparison : SymmetricAlgebra k g ≃ₗ[k] U k g :=
  (orderedSymmetricBasis b).equiv (orderedBasis b) (Equiv.refl _)

private theorem orderedComparison_symm (l : OrderedWord ι) :
    (orderedComparison b).symm (orderedMonomial b l) = symmetricWord (l.val.map b) := by
  rw [← orderedBasis_apply, orderedComparison, Module.Basis.equiv_symm,
    Module.Basis.equiv_apply]
  exact orderedSymmetricBasis_apply b l

private theorem orderedComparison_symm_filtered (m : ℤ) {a : U k g}
    (ha : a ∈ filtration k g m) :
    (orderedComparison b).symm a ∈ symmetricFiltration m := by
  rw [filtration_eq_boundedSpan b m] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    rw [orderedComparison_symm]
    exact Submodule.subset_span ⟨l.val.map b, by simpa using hl, rfl⟩
  | zero => simpa using (symmetricFiltration (k := k) (g := g) m).zero_mem
  | add a c ha hc iha ihc => simpa using (symmetricFiltration m).add_mem iha ihc
  | smul r a ha ih => simpa using (symmetricFiltration m).smul_mem r ih

/-- Relative to the ordered PBW comparison, averaging differs from the identity
by an operator strictly lowering word length. -/
private theorem formula_lowers (s : SymmetricAlgebra k g →ₗ[k] U k g) (hs : HasFormula s)
    (m : ℤ) {a : U k g} (ha : a ∈ filtration k g m) :
    s ((orderedComparison b).symm a) - a ∈ filtration k g (m - 1) := by
  rw [filtration_eq_boundedSpan b m] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    rw [orderedComparison_symm]
    have hdeg : symmetricWord (l.val.map b) ∈
        symmetricDegree (k := k) (g := g) l.val.length :=
      Submodule.subset_span ⟨l.val.map b, List.length_map .., rfl⟩
    obtain ⟨hsa, hsymbol⟩ := formula_topSymbol s hs _ _ hdeg
    have hword : orderedMonomial b l ∈ Step k g l.val.length :=
      word_mem k g (l.val.map b) (by simp)
    have he : symbol k g l.val.length ⟨s (symmetricWord (l.val.map b)), hsa⟩ =
        symbol k g l.val.length ⟨orderedMonomial b l, hword⟩ := by
      rw [hsymbol, canonicalMap_orderedWord]
      rfl
    exact filtration_mono k g (by omega) ((symbol_eq_iff _ _ _).mp he)
  | zero => simpa using (filtration k g (m-1)).zero_mem
  | add a c ha hc iha ihc =>
    simpa only [map_add, add_sub_add_comm] using (filtration k g (m-1)).add_mem iha ihc
  | smul r a ha ih =>
    simpa only [map_smul, ← smul_sub] using (filtration k g (m-1)).smul_mem r ih
end Ordered

/-- A map equal to the identity up to strictly lower degree is invertible
on an exhaustive filtration bounded below by zero. -/
private theorem lowering_bijective (T : U k g →ₗ[k] U k g)
    (hT : ∀ (m : ℤ) (a : U k g), a ∈ filtration k g m →
      T a - a ∈ filtration k g (m-1)) :
    Function.Bijective T ∧
      ∀ (m : ℤ) (a : U k g), a ∈ filtration k g m →
        ∃ c ∈ filtration k g m, T c = a := by
  have hz : ∀ a : U k g, a ∈ filtration k g (-1) → a = 0 := by
    intro a ha
    rw [(filtration_properties k g).2.1 (-1) (by omega)] at ha
    exact ha
  have hker : ∀ n : ℕ, ∀ a : U k g, a ∈ filtration k g n → T a = 0 → a = 0 := by
    intro n
    induction n with
    | zero =>
      intro a ha h
      have hd := hT 0 a ha
      simp only [h, zero_sub] at hd
      exact neg_eq_zero.mp (hz (-a) hd)
    | succ n ih =>
      intro a ha h
      have hd := hT ((n+1 : ℕ) : ℤ) a ha
      simp only [h, zero_sub] at hd
      apply ih a
      · simpa using hd
      · exact h
  have hsurj : ∀ n : ℕ, ∀ a : U k g, a ∈ filtration k g n →
      ∃ c ∈ filtration k g n, T c = a := by
    intro n
    induction n with
    | zero =>
      intro a ha
      refine ⟨a, ha, sub_eq_zero.mp (hz _ (hT 0 a ha))⟩
    | succ n ih =>
      intro a ha
      obtain ⟨c, hc, he⟩ := ih (T a - a) (by simpa using hT ((n+1 : ℕ) : ℤ) a ha)
      refine ⟨a-c, (filtration k g ((n+1 : ℕ) : ℤ)).sub_mem ha
        (filtration_mono k g (by omega) hc), ?_⟩
      rw [map_sub, he]
      abel
  have hex (a : U k g) : ∃ n : ℕ, a ∈ filtration k g n := by
    obtain ⟨m, hm⟩ := (filtration_properties k g).2.2.2.2.2 a
    exact ⟨m.toNat, filtration_mono k g (Int.self_le_toNat m) hm⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply (injective_iff_map_eq_zero T).mpr
    intro a ha
    obtain ⟨n, hn⟩ := hex a
    exact hker n a hn ha
  · intro a
    obtain ⟨n, hn⟩ := hex a
    obtain ⟨c, _, hc⟩ := hsurj n a hn
    exact ⟨c, hc⟩
  · intro m a ha
    by_cases hm : m < 0
    · have he : a = 0 := by
        rw [(filtration_properties k g).2.1 m hm] at ha
        exact ha
      exact ⟨0, Submodule.zero_mem _, by simp [he]⟩
    · have hm' : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (by omega)
      simpa only [hm'] using hsurj m.toNat a (by simpa only [hm'] using ha)

/-- Formula (1.2) gives an isomorphism and equality of every filtration step. -/
theorem formula_bijective_filtered (s : SymmetricAlgebra k g →ₗ[k] U k g)
    (hs : HasFormula s) : Function.Bijective s ∧
      ∀ m : ℤ, Submodule.map s (symmetricFiltration m) = filtration k g m := by
  classical
  letI : LinearOrder (Module.Free.ChooseBasisIndex k g) := IsWellOrder.linearOrder WellOrderingRel
  let b := Module.Free.chooseBasis k g
  let R := orderedComparison b
  let T := s.comp R.symm.toLinearMap
  obtain ⟨hbij, hsurj⟩ := lowering_bijective T (fun m a ha => formula_lowers b s hs m ha)
  have he : s = T.comp R.toLinearMap := by ext a; simp [T]
  refine ⟨?_, ?_⟩
  · rw [he]
    exact hbij.comp R.bijective
  · intro m
    apply le_antisymm
    · exact Submodule.map_le_iff_le_comap.mpr (formula_filtered s hs m)
    · intro a ha
      obtain ⟨c, hc, he⟩ := hsurj m a ha
      exact ⟨R.symm c, orderedComparison_symm_filtered b m hc, he⟩

/-- The dual-number universal property extends arbitrary generator values
uniquely to a derivation on the symmetric algebra. -/
private noncomputable def generatorJet (f : g →ₗ[k] SymmetricAlgebra k g) :
    SymmetricAlgebra k g →ₐ[k]
      TrivSqZeroExt (SymmetricAlgebra k g) (SymmetricAlgebra k g) :=
  SymmetricAlgebra.lift
    { toFun := fun y => (SymmetricAlgebra.ι k g y, f y)
      map_add' := fun y z => Prod.ext ((SymmetricAlgebra.ι k g).map_add y z) (f.map_add y z)
      map_smul' := fun r y => Prod.ext ((SymmetricAlgebra.ι k g).map_smul r y) (f.map_smul r y) }

private theorem generatorJet_fst (f : g →ₗ[k] SymmetricAlgebra k g) (a : SymmetricAlgebra k g) :
    (generatorJet f a).fst = a := by
  have h : (TrivSqZeroExt.fstHom k _ _).comp (generatorJet f) =
      AlgHom.id k (SymmetricAlgebra k g) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro y
    change (generatorJet f (SymmetricAlgebra.ι k g y)).fst = SymmetricAlgebra.ι k g y
    rw [generatorJet, SymmetricAlgebra.lift_ι_apply]
    rfl
  exact AlgHom.congr_fun h a

noncomputable def extendDerivation (f : g →ₗ[k] SymmetricAlgebra k g) :
    Derivation k (SymmetricAlgebra k g) (SymmetricAlgebra k g) where
  toLinearMap := ((TrivSqZeroExt.sndHom _ _).restrictScalars k).comp (generatorJet f).toLinearMap
  map_one_eq_zero' := by simp
  leibniz' a c := by
    change (generatorJet f (a*c)).snd = _
    rw [map_mul, TrivSqZeroExt.snd_mul, generatorJet_fst, generatorJet_fst]
    change a * (generatorJet f c).snd + (generatorJet f a).snd * c =
      a * (generatorJet f c).snd + c * (generatorJet f a).snd
    rw [mul_comm ((generatorJet f a).snd) c]

@[simp] theorem extendDerivation_generator (f : g →ₗ[k] SymmetricAlgebra k g) (y : g) :
    extendDerivation f (SymmetricAlgebra.ι k g y) = f y := by
  change (generatorJet f (SymmetricAlgebra.ι k g y)).snd = _
  simp only [generatorJet, SymmetricAlgebra.lift_ι_apply]
  rfl

/-- Derivations of S(g) are determined by their values on g. -/
theorem symmetric_derivation_ext
    (D E : Derivation k (SymmetricAlgebra k g) (SymmetricAlgebra k g))
    (h : ∀ y, D (SymmetricAlgebra.ι k g y) = E (SymmetricAlgebra.ι k g y)) : D = E := by
  apply Derivation.ext
  intro a
  induction a using SymmetricAlgebra.induction with
  | algebraMap r => simp
  | ι y => exact h y
  | add a c ha hc => simp only [map_add, ha, hc]
  | mul a c ha hc => simp only [Derivation.leibniz, ha, hc]

/-- The canonical adjoint action on S(g), valued in actual derivations. -/
noncomputable def symmetricAdjoint :
    g →ₗ⁅k⁆ Derivation k (SymmetricAlgebra k g) (SymmetricAlgebra k g) where
  toFun x := extendDerivation ((SymmetricAlgebra.ι k g).comp (LieAlgebra.ad k g x))
  map_add' x y := by
    apply symmetric_derivation_ext
    intro z
    simp [Derivation.add_apply, lie_add, add_lie]
  map_smul' r x := by
    apply symmetric_derivation_ext
    intro z
    simp [Derivation.smul_apply]
  map_lie' {x y} := by
    apply symmetric_derivation_ext
    intro z
    simp only [extendDerivation_generator, LinearMap.comp_apply, LieAlgebra.ad_apply,
      Derivation.commutator_apply]
    rw [← map_sub, ← lie_lie]

@[simp] theorem symmetricAdjoint_generator (x y : g) :
    symmetricAdjoint (k := k) (g := g) x (SymmetricAlgebra.ι k g y) =
      SymmetricAlgebra.ι k g ⁅x, y⁆ := by
  exact extendDerivation_generator _ y

private def tupleProduct {A : Type*} [Monoid A] (f : g → A) {n : ℕ} (y : Fin n → g) : A :=
  (List.ofFn (f ∘ y)).prod

private theorem tupleProduct_succ {A : Type*} [Monoid A] (f : g → A)
    {n : ℕ} (y : Fin (n+1) → g) :
    tupleProduct f y = f (y 0) * tupleProduct f (fun i => y i.succ) := by
  simp [tupleProduct, List.ofFn_succ, Function.comp_def]

/-- Leibniz's rule for an ordered product, without commutativity assumptions. -/
private theorem tupleProduct_derivative {A : Type*} [Ring A] [Algebra k A]
    (f : g →ₗ[k] A) (d : g →ₗ[k] g) (D : A →ₗ[k] A)
    (h1 : D 1 = 0) (hm : ∀ a c, D (a*c) = D a * c + a * D c)
    (hf : ∀ y, D (f y) = f (d y)) (n : ℕ) (y : Fin n → g) :
    D (tupleProduct f y) =
      ∑ i, tupleProduct f (Function.update y i (d (y i))) := by
  classical
  induction n with
  | zero => simpa [tupleProduct] using h1
  | succ n ih =>
    rw [tupleProduct_succ, hm, hf, ih, Finset.mul_sum, Fin.sum_univ_succ]
    congr 1
    · simp [tupleProduct_succ, Function.update_apply]
    · apply Finset.sum_congr rfl
      intro i _
      rw [tupleProduct_succ]
      simp only [Function.update_of_ne (Fin.succ_ne_zero i).symm]
      congr 1
      apply congrArg (tupleProduct f)
      funext j
      simp only [Function.update_apply, Fin.succ_inj]

private theorem symmetricProduct_derivative (x : g) (n : ℕ) (y : Fin n → g) :
    symmetricAdjoint (k := k) x (symmetricWord (List.ofFn y)) =
      ∑ i, symmetricWord (List.ofFn (Function.update y i ⁅x, y i⁆)) := by
  have h := tupleProduct_derivative (SymmetricAlgebra.ι k g) (LieAlgebra.ad k g x)
    (symmetricAdjoint (k := k) x).toLinearMap
    (Derivation.map_one_eq_zero _) (fun a c => by
      change symmetricAdjoint (k := k) x (a*c) =
        symmetricAdjoint (k := k) x a * c + a * symmetricAdjoint (k := k) x c
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      ring)
    (fun y => symmetricAdjoint_generator x y) n y
  simpa [tupleProduct, symmetricWord, List.map_ofFn, Function.comp_def] using h

private def envelopingAdjoint (x : g) : U k g →ₗ[k] U k g :=
  LinearMap.mulLeft k (inclusion k g x) - LinearMap.mulRight k (inclusion k g x)

private theorem word_derivative (x : g) (n : ℕ) (y : Fin n → g) :
    envelopingAdjoint x (word k g (List.ofFn y)) =
      ∑ i, word k g (List.ofFn (Function.update y i ⁅x, y i⁆)) := by
  have h := tupleProduct_derivative (inclusion k g).toLinearMap (LieAlgebra.ad k g x)
    (envelopingAdjoint x)
    (by simp [envelopingAdjoint])
    (fun a c => by
      change inclusion k g x * (a*c) - (a*c) * inclusion k g x =
        (inclusion k g x * a - a * inclusion k g x) * c +
          a * (inclusion k g x * c - c * inclusion k g x)
      noncomm_ring)
    (fun y => by
      change inclusion k g x * inclusion k g y - inclusion k g y * inclusion k g x =
        inclusion k g ⁅x, y⁆
      exact ((inclusion k g).map_lie x y).symm) n y
  simpa [tupleProduct, word, List.map_ofFn, Function.comp_def] using h

/-- Differentiating the factors commutes with the permutation average. -/
private theorem average_derivative (x : g) (n : ℕ) (y : Fin n → g) :
    envelopingAdjoint (k := k) x (average n y) =
      ∑ i, average n (Function.update y i ⁅x, y i⁆) := by
  classical
  simp only [average, map_smul, map_sum, word_derivative]
  rw [← Finset.smul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  have he (i : Fin n) :
      Function.update (y ∘ σ) i ⁅x, (y ∘ σ) i⁆ =
        (Function.update y (σ i) ⁅x, y (σ i)⁆) ∘ σ := by
    exact (Function.update_comp_eq_of_injective y σ.injective i _).symm
  simp_rw [he]
  exact Equiv.sum_comp σ (fun i =>
    word k g (List.ofFn ((Function.update y i ⁅x, y i⁆) ∘ σ)))

/-- Every map satisfying the symmetrization formula intertwines the adjoint actions. -/
theorem formula_adjoint (s : SymmetricAlgebra k g →ₗ[k] U k g) (hs : HasFormula s) :
    AdjointEquivariant s := by
  refine ⟨symmetricAdjoint, symmetricAdjoint_generator, ?_⟩
  intro x a
  have h : s.comp (symmetricAdjoint (k := k) x).toLinearMap =
      (envelopingAdjoint x).comp s := by
    classical
    letI : LinearOrder (Module.Free.ChooseBasisIndex k g) := IsWellOrder.linearOrder WellOrderingRel
    apply (orderedSymmetricBasis (Module.Free.chooseBasis k g)).ext
    intro l
    rw [orderedSymmetricBasis_apply]
    let ys := l.val.map (Module.Free.chooseBasis k g)
    change s (symmetricAdjoint (k := k) x (symmetricWord ys)) =
      envelopingAdjoint x (s (symmetricWord ys))
    have hys : ys = List.ofFn ys.get := (List.ofFn_get ys).symm
    rw [hys, symmetricProduct_derivative, map_sum]
    unfold HasFormula at hs
    simp_rw [hs]
    exact (average_derivative x ys.length ys.get).symm
  exact LinearMap.congr_fun h a

/-- Characteristic-zero symmetrization, with its full filtered and equivariant structure. -/
theorem symmetrization_spec :
    Specs.LieAlgebrasAndRepresentations.Symmetrization.symmetrizationExpected.{u,v} := by
  intro k g _ _ _ _
  obtain ⟨s, hs⟩ := exists_formula (k := k) (g := g)
  obtain ⟨hbij, hf⟩ := formula_bijective_filtered s hs
  let e := LinearEquiv.ofBijective s hbij
  refine ⟨e, hs, hf, formula_adjoint s hs, filtration_properties k g, ?_⟩
  exact formula_topSymbol s hs

/-- Formula (1.2) fixes the unit and each degree-one generator. -/
theorem formula_generator (s : SymmetricAlgebra k g →ₗ[k] U k g) (hs : HasFormula s)
    (x : g) : s (SymmetricAlgebra.ι k g x) = inclusion k g x := by
  simpa [symmetricWord] using (hs 1 (fun _ => x)).trans (average_singleton k g _)

/-- A map fixing generators cannot be multiplicative for a nonabelian algebra.
This uses actual injectivity from PBW, not an assumed faithful inclusion. -/
theorem formula_not_multiplicative (s : SymmetricAlgebra k g →ₗ[k] U k g)
    (hs : HasFormula s) (x y : g) (hxy : ⁅x, y⁆ ≠ 0) :
    ∃ a b : SymmetricAlgebra k g, s (a*b) ≠ s a * s b := by
  classical
  by_contra! hm
  have hc : inclusion k g x * inclusion k g y = inclusion k g y * inclusion k g x := by
    rw [← formula_generator s hs x, ← formula_generator s hs y, ← hm, ← hm, mul_comm]
  have hz : inclusion k g ⁅x, y⁆ = inclusion k g 0 := by
    rw [(inclusion k g).map_lie]
    change inclusion k g x * inclusion k g y - inclusion k g y * inclusion k g x = _
    rw [hc, sub_self, map_zero]
  letI : LinearOrder (Module.Free.ChooseBasisIndex k g) := IsWellOrder.linearOrder WellOrderingRel
  exact hxy (Shared.Lie.PBW.inclusionInjective_spec k g _
    (Module.Free.chooseBasis k g) hz)

theorem nonmultiplicative_spec :
    Specs.LieAlgebrasAndRepresentations.Symmetrization.nonmultiplicativeExpected := by
  let x : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 0]
  let y : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 0, 0]
  have hxy : ⁅x, y⁆ ≠ 0 := by
    intro h
    have hh := congrArg (fun a : Matrix (Fin 2) (Fin 2) ℚ => a 0 1) h
    norm_num [Ring.lie_def, x, y, Matrix.mul_apply, Fin.sum_univ_two] at hh
  refine ⟨⟨x, y, hxy⟩, ?_⟩
  intro s hs
  exact formula_not_multiplicative s hs x y hxy

theorem formula_topSymbol_spec :
    Specs.LieAlgebrasAndRepresentations.Symmetrization.formulaTopSymbolExpected.{u,v} := by
  intro k g _ _ _ _ _ s hs
  exact formula_topSymbol s hs

theorem formula_filtered_spec :
    Specs.LieAlgebrasAndRepresentations.Symmetrization.formulaFilteredExpected.{u,v} := by
  intro k g _ _ _ _ s hs m
  exact formula_filtered s hs m

theorem formula_unique_spec :
    Specs.LieAlgebrasAndRepresentations.Symmetrization.formulaUniqueExpected.{u,v} := by
  intro k g _ _ _ _ s t hs ht
  exact formula_unique s t hs ht

end LieAlgebrasAndRepresentations.Symmetrization
