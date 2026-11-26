import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.PowerSeriesLocalCohomology
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedCechComparison
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.GorensteinTopLocalCohomology
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.RegularAndCompleteIntersection
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Specs.CommutativeAlgebraNotes.PowerSeriesLocalCohomology

namespace CommutativeAlgebraNotes.PowerSeriesLocalCohomology

universe u

variable {k : Type u} [Field k] {d : ℕ}

local notation "S" => Series k d
local notation "P" => fullProduct k d
local notation "L" => Localization.Away (fullProduct k d)
local notation "X" => MvPowerSeries.X
local notation "coeff" => MvPowerSeries.coeff (R := k)

private abbrev exponent (a : Fin d → ℕ) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm a

private theorem fullProduct_ne_zero : (P : S) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ hi
  have h := congrArg (coeff (Finsupp.single i 1)) hi
  simp [MvPowerSeries.X] at h

private theorem fullProduct_pow (M : ℕ) :
    P ^ M = (MvPowerSeries.monomial (exponent (fun _ : Fin d => M)) (1 : k)) := by
  rw [MvPowerSeries.monomial_one_eq, Finsupp.prod_fintype _ _ (by simp), ← Finset.prod_pow]
  congr

/-- Laurent coefficient at exponent `-(a+1)` with common denominator `P^N`. -/
private def negativeCoeff (N : ℕ) (f : S) (a : Index d) : k :=
  if ∀ i, a i < N then coeff (exponent (fun i => N - (a i + 1))) f else 0

private theorem negativeCoeff_shift (N M : ℕ) (f : S) (a : Index d) :
    negativeCoeff (N + M) (P ^ M * f) a = negativeCoeff N f a := by
  classical
  by_cases hN : ∀ i, a i < N
  · have hNM : ∀ i, a i < N + M := fun i => by have := hN i; omega
    have hindex : exponent (fun i => N + M - (a i + 1)) =
        exponent (fun _ : Fin d => M) + exponent (fun i => N - (a i + 1)) := by
      ext i
      change N + M - (a i + 1) = M + (N - (a i + 1))
      have := hN i
      omega
    rw [negativeCoeff, ite_eq_left hNM, negativeCoeff, ite_eq_left hN, fullProduct_pow, hindex,
      MvPowerSeries.coeff_add_monomial_mul, one_mul]
  · simp only [negativeCoeff, ite_eq_right hN]
    split_ifs with hNM
    · rw [fullProduct_pow, MvPowerSeries.coeff_monomial_mul, ite_eq_right]
      intro h
      apply hN
      intro i
      have hi : M ≤ N + M - (a i + 1) := (Finsupp.le_def.mp h) i
      have := hNM i
      omega
    · rfl

private theorem fraction_eq_of_cross {p : S} {N M : ℕ} {f g : S}
    (h : p ^ M * f = p ^ N * g) : fraction p N f = fraction p M g :=
  Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq h)

private theorem fraction_cross {N M : ℕ} {f g : S}
    (h : fraction P N f = fraction P M g) : P ^ M * f = P ^ N * g := by
  obtain ⟨c, hc⟩ := Localization.r_iff_exists.mp (Localization.mk_eq_mk_iff.mp h)
  obtain ⟨m, hm⟩ := c.prop
  apply mul_left_cancel₀ (show (c : S) ≠ 0 from hm ▸ pow_ne_zero m fullProduct_ne_zero)
  exact hc

private theorem fraction_shift (p : S) (N M : ℕ) (f : S) :
    fraction p (N + M) (p ^ M * f) = fraction p N f :=
  fraction_eq_of_cross (by rw [pow_add, mul_assoc])

private theorem fraction_surj (p : S) (z : Localization.Away p) : ∃ N f, fraction p N f = z := by
  induction z using Localization.induction_on with
  | H y =>
    obtain ⟨f, s⟩ := y
    obtain ⟨N, hN⟩ := s.prop
    refine ⟨N, f, ?_⟩
    exact congrArg (Localization.mk f) (Subtype.ext hN)

private theorem negativeCoeff_eq_of_fraction_eq {N M : ℕ} {f g : S}
    (h : fraction P N f = fraction P M g) (a : Index d) :
    negativeCoeff N f a = negativeCoeff M g a := by
  rw [← negativeCoeff_shift N M, ← negativeCoeff_shift M N g, add_comm N M, fraction_cross h]

private def coeffVector (N : ℕ) (f : S) : Index d →₀ k := by
  classical
  refine Finsupp.onFinset
    (Finset.univ.image (fun a : Fin d → Fin N => fun i => (a i : ℕ)))
    (negativeCoeff N f) ?_
  intro a ha
  have h : ∀ i, a i < N := by
    by_contra h
    exact ha (ite_eq_right h)
  exact Finset.mem_image.mpr ⟨fun i => ⟨a i, h i⟩, Finset.mem_univ _, rfl⟩

private theorem coeffVector_apply (N : ℕ) (f : S) (a : Index d) :
    coeffVector N f a = negativeCoeff N f a :=
  Finsupp.onFinset_apply

private def laurentCoeffs (z : L) : Index d →₀ k :=
  coeffVector (fraction_surj P z).choose (fraction_surj P z).choose_spec.choose

private theorem laurentCoeffs_fraction (N : ℕ) (f : S) :
    laurentCoeffs (fraction P N f) = coeffVector N f := by
  ext a
  simp only [laurentCoeffs, coeffVector_apply]
  exact negativeCoeff_eq_of_fraction_eq (fraction_surj P (fraction P N f)).choose_spec.choose_spec a

private theorem fraction_add (p : S) (N : ℕ) (f g : S) :
    fraction p N (f + g) = fraction p N f + fraction p N g :=
  (Localization.add_mk_self _ _ _).symm

private theorem fraction_smul (p : S) (N : ℕ) (b : k) (f : S) :
    fraction p N (b • f) = b • fraction p N f := by
  simp only [fraction, Localization.mk_eq_mk'_apply, ← IsScalarTower.algebraMap_smul S b,
    IsLocalization.smul_mk']
  congr 1

private def laurentLinear : L →ₗ[k] (Index d →₀ k) where
  toFun := laurentCoeffs
  map_add' z w := by
    obtain ⟨N, f, rfl⟩ := fraction_surj P z
    obtain ⟨M, g, rfl⟩ := fraction_surj P w
    rw [← fraction_shift P N M f, ← fraction_shift P M N g, add_comm M N,
      ← fraction_add, laurentCoeffs_fraction, laurentCoeffs_fraction, laurentCoeffs_fraction]
    ext a
    simp only [Finsupp.add_apply, coeffVector_apply, negativeCoeff, map_add]
    split_ifs <;> simp
  map_smul' b z := by
    obtain ⟨N, f, rfl⟩ := fraction_surj P z
    rw [RingHom.id_apply, ← fraction_smul, show laurentCoeffs (fraction P N (b • f)) =
      coeffVector N (b • f) from laurentCoeffs_fraction N _, laurentCoeffs_fraction]
    ext a
    simp only [Finsupp.smul_apply, coeffVector_apply, negativeCoeff, map_smul]
    split_ifs <;> simp

private theorem laurentLinear_inverseMonomial (a : Index d) :
    laurentLinear (inverseMonomial k d a) = Finsupp.single a 1 := by
  let N := Finset.univ.sup a + 1
  change laurentCoeffs (fraction P N (MvPowerSeries.monomial
    (exponent fun i => N - (a i + 1)) 1)) = _
  rw [laurentCoeffs_fraction]
  ext b
  rw [coeffVector_apply]
  have ha (i : Fin d) : a i < N :=
    Nat.lt_succ_of_le (Finset.le_sup (f := a) (Finset.mem_univ i))
  by_cases h : b = a
  · subst b
    simp [negativeCoeff, ha]
  · rw [Finsupp.single_eq_of_ne h]
    by_cases hb : ∀ i, b i < N
    · rw [negativeCoeff, ite_eq_left hb, MvPowerSeries.coeff_monomial_ne]
      intro he
      apply h
      funext i
      have hp := congrArg (fun c : Fin d →₀ ℕ => c i) he
      change N - (b i + 1) = N - (a i + 1) at hp
      have := ha i
      have := hb i
      omega
    · exact ite_eq_right hb

private theorem laurentLinear_surj : Function.Surjective (laurentLinear (k := k) (d := d)) := by
  intro v
  induction v using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add f g hf hg =>
    obtain ⟨x, hx⟩ := hf
    obtain ⟨y, hy⟩ := hg
    exact ⟨x + y, by rw [map_add, hx, hy]⟩
  | single a b =>
    exact ⟨b • inverseMonomial k d a, by
      rw [map_smul, laurentLinear_inverseMonomial, Finsupp.smul_single, smul_eq_mul, mul_one]⟩

private theorem faceMap_fraction (j : Fin d) (N : ℕ) (f : S) :
    faceMap k d j (fraction (faceProduct k d j) N f) =
      fraction P N (X j ^ N * f) := by
  simp only [fraction, Localization.mk_eq_mk'_apply]
  change faceMap k d j (IsLocalization.mk' (Localization.Away (faceProduct k d j)) f
    (⟨faceProduct k d j ^ N, ⟨N, rfl⟩⟩ : Submonoid.powers (faceProduct k d j))) =
    IsLocalization.mk' (Localization.Away P) (X j ^ N * f) (⟨P ^ N, ⟨N, rfl⟩⟩ : Submonoid.powers P)
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  let B := Localization.Away (fullProduct k d)
  let A := Localization.Away (faceProduct k d j)
  let denom : Submonoid.powers (faceProduct k d j) := ⟨faceProduct k d j ^ N, ⟨N, rfl⟩⟩
  let v : B := faceMap k d j (IsLocalization.mk' A f denom)
  have hm : v * algebraMap S B (faceProduct k d j ^ N) = algebraMap S B f := by
    have h := congrArg (faceMap k d j) (IsLocalization.mk'_spec A f denom)
    rw [map_mul, (faceMap k d j).commutes, (faceMap k d j).commutes] at h
    exact h
  have hp : (P : S) ^ N = X j ^ N * faceProduct k d j ^ N :=
    (congrArg (· ^ N) (variable_mul_faceProduct k d j).symm).trans (mul_pow _ _ _)
  change v * algebraMap S B (P ^ N) = algebraMap S B (X j ^ N * f)
  calc
    _ = v * algebraMap S B (X j ^ N * faceProduct k d j ^ N) :=
      congrArg (fun a : S => v * algebraMap S B a) hp
    _ = _ := by rw [map_mul, mul_left_comm, hm, map_mul]

private theorem laurentLinear_faceMap (j : Fin d) (z : Localization.Away (faceProduct k d j)) :
    laurentLinear (faceMap k d j z) = 0 := by
  obtain ⟨N, f, rfl⟩ := fraction_surj (faceProduct k d j) z
  change laurentCoeffs (faceMap k d j (fraction (faceProduct k d j) N f)) = 0
  rw [faceMap_fraction, laurentCoeffs_fraction]
  ext a
  rw [Finsupp.zero_apply, coeffVector_apply, negativeCoeff]
  split_ifs with ha
  · exact (MvPowerSeries.X_pow_dvd_iff.mp (dvd_mul_right _ _)) _ (by
      change N - (a j + 1) < N
      have := ha j
      omega)
  · rfl

/-- Partition the discarded coefficients by one variable in which the exponent is too large. -/
private theorem decompose_numerator (N : ℕ) (f : S)
    (hf : ∀ m : Fin d →₀ ℕ, (∀ i, m i < N) → coeff m f = 0) :
    ∃ g : Fin d → S, f = ∑ i, X i ^ N * g i := by
  classical
  let bad (m : Fin d →₀ ℕ) : Option (Fin d) :=
    if h : ∃ i : Fin d, N ≤ m i then some h.choose else none
  let part (i : Fin d) : S := fun m => if bad m = some i then coeff m f else 0
  have hsum : f = ∑ i, part i := by
    ext m
    rw [map_sum]
    change coeff m f = ∑ i : Fin d, (if bad m = some i then coeff m f else 0)
    by_cases h : ∃ i : Fin d, N ≤ m i
    · rw [Finset.sum_eq_single h.choose]
      · simp [bad, h]
      · intro j _ hj
        simp [bad, h, Ne.symm hj]
      · simp
    · rw [hf m (fun i => Nat.lt_of_not_ge fun hi => h ⟨i, hi⟩)]
      simp [bad, h]
  have hdvd (i : Fin d) : X i ^ N ∣ part i := by
    rw [MvPowerSeries.X_pow_dvd_iff]
    intro m hm
    change (if bad m = some i then coeff m f else 0) = 0
    apply ite_eq_right
    intro hi
    by_cases h : ∃ j : Fin d, N ≤ m j
    · have he : h.choose = i := by simpa [bad, h] using hi
      exact (Nat.not_le_of_lt hm (he ▸ h.choose_spec)).elim
    · simp [bad, h] at hi
  choose g hg using hdvd
  exact ⟨g, hsum.trans (Finset.sum_congr rfl (fun i _ => hg i))⟩

private theorem laurentLinear_eq_zero_iff (z : L) :
    laurentLinear z = 0 ↔ z ∈ faceImages k d := by
  constructor
  · obtain ⟨N, f, rfl⟩ := fraction_surj P z
    intro h
    change laurentCoeffs (fraction P N f) = 0 at h
    rw [laurentCoeffs_fraction] at h
    have hf (m : Fin d →₀ ℕ) (hm : ∀ i, m i < N) : coeff m f = 0 := by
      let a : Index d := fun i => N - (m i + 1)
      have ha (i : Fin d) : a i < N := by dsimp [a]; have := hm i; omega
      have he : exponent (fun i => N - (a i + 1)) = m := by
        ext i
        change N - (N - (m i + 1) + 1) = m i
        have := hm i
        omega
      have h' := DFunLike.congr_fun h a
      rwa [coeffVector_apply, negativeCoeff, ite_eq_left ha, he, Finsupp.zero_apply] at h'
    obtain ⟨g, hg⟩ := decompose_numerator N f hf
    rw [hg]
    change Localization.mk (∑ i : Fin d, X i ^ N * g i) _ ∈ _
    rw [Localization.mk_sum]
    apply Submodule.sum_mem_iSup
    intro i
    exact ⟨fraction (faceProduct k d i) N (g i), faceMap_fraction i N (g i)⟩
  · intro hz
    -- Use an S-submodule generated by the face ranges, with k-linear coordinate tests.
    let V : Submodule S L :=
      { carrier := {x | ∀ c : S, laurentLinear (c • x) = 0}
        zero_mem' := by simp
        add_mem' := fun hx hy c => by rw [smul_add, map_add, hx, hy, add_zero]
        smul_mem' := fun c x hx r => by rw [smul_smul]; exact hx _ }
    have hV : faceImages k d ≤ V := by
      refine iSup_le fun j x hx => ?_
      obtain ⟨z, rfl⟩ := hx
      intro c
      change laurentLinear (c • (faceMap k d j).toLinearMap z) = 0
      rw [← map_smul]
      exact laurentLinear_faceMap j (c • z)
    have hv : ∀ c : S, laurentLinear (c • z) = 0 := hV hz
    simpa using hv 1

open Specs.CommutativeAlgebraNotes.AugmentedCechComplex
  (Selection selected preceding product localizationMap term)

private abbrev variableList (k : Type u) [Field k] (d : ℕ) : List (Series k d) :=
  List.ofFn fun i : Fin d => X i

local notation "rs" => variableList k d
local notation "C" => CechComplex rs
local notation "n" => (d : ℤ)
local notation "p" => ((d : ℤ) - 1)
local notation "qtop" => ((d : ℤ) - 1 + 1)

private def variableIndex : Fin (rs).length ≃ Fin d :=
  finCongr List.length_ofFn

private theorem variables_get (i : Fin (rs).length) :
    (rs).get i = (X (variableIndex (k := k) i) : S) :=
  List.get_ofFn _ _

private abbrev chosen {q : ℤ} (s : Selection (rs).length q) : Finset (Fin (rs).length) :=
  Finset.univ.filter (fun i => selected s i = true)

private theorem chosen_top (s : Selection (rs).length qtop) : chosen s = Finset.univ := by
  apply Finset.eq_univ_of_card
  have h : ((chosen s).card : ℤ) = qtop := Cech.selection_card s
  simp only [Fintype.card_fin, List.length_ofFn]
  omega

private def topSelection : Selection (rs).length qtop :=
  (Cech.selectionEquiv (rs).length qtop).symm ⟨Finset.univ, by simp [List.length_ofFn]⟩

private theorem topSelection_unique (s : Selection (rs).length qtop) : s = topSelection := by
  apply (Cech.selectionEquiv (rs).length qtop).injective
  apply Subtype.ext
  change chosen s = chosen (topSelection (k := k))
  rw [chosen_top, chosen_top]

private theorem prod_top (s : Selection (rs).length qtop) : product S rs s = P := by
  rw [Cech.product_eq]
  change (∏ i ∈ chosen s, (rs).get i) = P
  rw [chosen_top]
  exact Fintype.prod_equiv (variableIndex (k := k)) _ _ variables_get

private theorem prod_face (s : Selection (rs).length p) (j : Fin (rs).length)
    (hj : chosen s = Finset.univ.erase j) :
    product S rs s = faceProduct k d (variableIndex j) := by
  rw [Cech.product_eq]
  change (∏ i ∈ chosen s, (rs).get i) = faceProduct k d (variableIndex j)
  rw [hj]
  exact Finset.prod_equiv (variableIndex (k := k))
    (fun i => by simp) (fun i _ => variables_get i)

private noncomputable def localizationIso {a b : S} (h : a = b) :
    ModuleCat.of S (Localization.Away a) ≅ ModuleCat.of S (Localization.Away b) :=
  eqToIso (congrArg (fun x => ModuleCat.of S (Localization.Away x)) h)

private theorem localizationMap_transport {a b a' b' : S} (ha : a = a') (hb : b = b')
    (hab : a ∣ b) (hab' : a' ∣ b') :
    ModuleCat.ofHom (localizationMap S a b hab).toLinearMap ≫ (localizationIso hb).hom =
      (localizationIso ha).hom ≫ ModuleCat.ofHom (localizationMap S a' b' hab').toLinearMap := by
  subst a' b'
  simp [localizationIso]

private noncomputable def toTopLocalization : (C).X qtop ⟶ ModuleCat.of S L :=
  Cofan.IsColimit.desc (Cech.summandCofanIsColimit rs qtop)
    (fun s => (localizationIso (prod_top s)).hom)

@[reassoc]
private theorem summandι_top (s : Selection (rs).length qtop) :
    Cech.summandι rs qtop s ≫ toTopLocalization = (localizationIso (prod_top s)).hom :=
  Cofan.IsColimit.fac (Cech.summandCofanIsColimit rs qtop) _ s

private noncomputable def topTermIso : ModuleCat.of S L ≅ (C).X qtop where
  hom := (localizationIso (prod_top topSelection)).inv ≫ Cech.summandι rs qtop topSelection
  inv := toTopLocalization
  hom_inv_id := by rw [Category.assoc, summandι_top, Iso.inv_hom_id]
  inv_hom_id := by
    apply Cofan.IsColimit.hom_ext (Cech.summandCofanIsColimit rs qtop)
    intro s
    change Cech.summandι rs qtop s ≫ _ ≫ _ = _
    have hs : s = topSelection := topSelection_unique s
    subst s
    rw [summandι_top_assoc, Iso.hom_inv_id_assoc, cofan_mk_inj]
    exact (Category.comp_id _).symm

private theorem chosen_face (s : Selection (rs).length p) :
    ∃ j : Fin (rs).length, chosen s = Finset.univ.erase j := by
  have hc : ((chosen s).card : ℤ) = p := Cech.selection_card s
  have hu : (Finset.univ : Finset (Fin (rs).length)).card = d := by simp [List.length_ofFn]
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (chosen s).card < Fintype.card (Fin (rs).length) from by
      rw [← Finset.card_univ]
      omega)
  refine ⟨j, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro i hi
    exact Finset.mem_erase.mpr ⟨fun h => hj (h ▸ hi), Finset.mem_univ i⟩
  · rw [Finset.card_erase_of_mem (Finset.mem_univ j)]
    omega

private theorem exists_faceSelection (j : Fin (rs).length) :
    ∃ s : Selection (rs).length p, chosen s = Finset.univ.erase j := by
  let J := Finset.univ.erase j
  have hJ : (J.card : ℤ) = p := by
    have hj : j.val < d := by simpa only [List.length_ofFn] using j.isLt
    simp only [J, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
      Fintype.card_fin, List.length_ofFn]
    omega
  let s := (Cech.selectionEquiv (rs).length p).symm ⟨J, hJ⟩
  refine ⟨s, ?_⟩
  change ((Cech.selectionEquiv (rs).length p) s).val = J
  simp [s]

private theorem face_differential (s : Selection (rs).length p) (j : Fin (rs).length)
    (hj : chosen s = Finset.univ.erase j) :
    Cech.summandι rs p s ≫ (C).d p qtop ≫ (topTermIso (k := k)).inv =
      (preceding s j).negOnePow • ((localizationIso (prod_face s j hj)).hom ≫
        ModuleCat.ofHom (faceMap k d (variableIndex j)).toLinearMap) := by
  have hselected (i : Fin (rs).length) : selected s i = true ↔ i ≠ j := by
    have h : i ∈ chosen s ↔ i ≠ j := by rw [hj]; simp
    simpa only [chosen, Finset.mem_filter, Finset.mem_univ, true_and] using h
  have hfalse : selected s j = false := Bool.eq_false_iff.mpr (fun h => (hselected j).mp h rfl)
  obtain ⟨t, ht, _, _, hins⟩ := Cech.summandι_insert_localization rs p s j hfalse
  change _ ≫ _ ≫ toTopLocalization = _
  rw [← Category.assoc, Cech.summandι_differential,
    Preadditive.sum_comp, Finset.sum_eq_single j]
  · rw [Linear.units_smul_comp, hins, Category.assoc, summandι_top]
    apply congrArg ((preceding s j).negOnePow • ·)
    exact localizationMap_transport (prod_face s j hj) (prod_top t) ht _
  · intro i _ hi
    rw [Cech.summandι_insert_eq_zero false rs p s i ((hselected i).mpr hi)]
    simp
  · simp


private theorem faceMap_eq_of_cast {i j : Fin d} (h : i = j)
    (y : Localization.Away (faceProduct k d j)) :
    faceMap k d i (h.symm ▸ y) = faceMap k d j y := by
  subst j
  rfl

private theorem topDifferential_range :
    (((C).d p qtop ≫ toTopLocalization).hom).range = faceImages k d := by
  let f := (C).d p qtop ≫ toTopLocalization
  let Q := ModuleCat.ofHom (faceImages k d).mkQ
  apply le_antisymm
  · have hz : f ≫ Q = 0 := by
      apply Cofan.IsColimit.hom_ext (Cech.summandCofanIsColimit rs p)
      intro s
      obtain ⟨j, hj⟩ := chosen_face s
      change Cech.summandι rs p s ≫ ((C).d p qtop ≫ (topTermIso (k := k)).inv) ≫ Q = _
      rw [← Category.assoc, face_differential s j hj, Linear.units_smul_comp]
      have hQ : ModuleCat.ofHom (faceMap k d (variableIndex j)).toLinearMap ≫ Q = 0 := by
        apply ModuleCat.hom_ext
        ext x
        exact (Submodule.Quotient.mk_eq_zero _).mpr
          (Submodule.mem_iSup_of_mem (variableIndex j) ⟨x, rfl⟩)
      simp [Category.assoc, hQ]
    rintro _ ⟨x, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).mp
      (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hz) x)
  · refine iSup_le fun i z ⟨y, hy⟩ => ?_
    let j := (variableIndex (k := k)).symm i
    have hij : variableIndex j = i := (variableIndex (k := k)).apply_symm_apply i
    obtain ⟨s, hs⟩ := exists_faceSelection j
    have hEq := face_differential s j hs
    let e := localizationIso (prod_face s j hs)
    have hsur : Function.Surjective e.hom := (ModuleCat.epi_iff_surjective _).mp inferInstance
    obtain ⟨w, hw⟩ := hsur (hij.symm ▸ y)
    let m := (preceding s j).negOnePow
    refine ⟨(Cech.summandι rs p s).hom (m • w), ?_⟩
    change (Cech.summandι rs p s ≫ (C).d p qtop ≫ (topTermIso (k := k)).inv).hom (m • w) = z
    rw [hEq]
    change m • (faceMap k d (variableIndex j)) (e.hom (m • w)) = z
    have h₁ : e.hom.hom (m • w) = m • e.hom.hom w := by
      simp only [Units.smul_def, map_zsmul]
    have h₂ (x : Localization.Away (faceProduct k d (variableIndex j))) :
        faceMap k d (variableIndex j) (m • x) = m • faceMap k d (variableIndex j) x := by
      simp only [Units.smul_def, map_zsmul]
    rw [h₁, h₂, smul_smul, Int.units_mul_self, one_smul, hw, faceMap_eq_of_cast hij]
    exact hy

private theorem cechQuotient :
    ∃ π : ModuleCat.of S L ⟶ (C).homology qtop,
      Function.Surjective π ∧ π.hom.ker = faceImages k d := by
  let e := topTermIso (k := k) (d := d)
  have hout : (C).d qtop (qtop + 1) = 0 := by
    apply (Cech.isZero_X rs _ (Or.inr ?_)).eq_of_tgt
    simp [List.length_ofFn]
  have hprev : (ComplexShape.up ℤ).prev qtop = p := by
    rw [CochainComplex.prev]
    omega
  have hnext : (ComplexShape.up ℤ).next qtop = qtop + 1 := CochainComplex.next ℤ _
  let h := (C).isoHomologyι qtop (qtop + 1) hnext hout
  let q₁ := (C).pOpcycles qtop
  let π := e.hom ≫ q₁ ≫ h.inv
  refine ⟨π, (ModuleCat.epi_iff_surjective _).mp (by dsimp [π, q₁]; infer_instance), ?_⟩
  have hker : ((C).d p qtop).hom.range = q₁.hom.ker := by
    let sc := ShortComplex.mk ((C).d p qtop) q₁ ((C).d_pOpcycles p qtop)
    exact (ShortComplex.exact_of_g_is_cokernel sc
      ((C).opcyclesIsCokernel p qtop hprev)).moduleCat_range_eq_ker
  rw [← topDifferential_range]
  ext x
  change π.hom x = 0 ↔ ∃ y, e.inv.hom (((C).d p qtop).hom y) = x
  have hinj : Function.Injective h.inv.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  change h.inv.hom (q₁.hom (e.hom.hom x)) = 0 ↔ _
  rw [← map_zero h.inv.hom, hinj.eq_iff]
  change e.hom.hom x ∈ q₁.hom.ker ↔ _
  rw [← hker]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [hy]
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom e.hom_inv_id) x
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [← hy]
    exact (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom e.inv_hom_id)
      (((C).d p qtop).hom y)).symm

variable (k d) in
private def cohomologyIsoCech :
    top k d ≅ (C).homology qtop := by
  obtain ⟨_, _, _, hgen, _, _, _, _⟩ := CompleteRegularPowerSeries.overField k d
  have hI : Ideal.span {r : S | r ∈ rs} = IsLocalRing.maximalIdeal S := by
    rw [hgen]
    congr 1
    ext r
    exact List.mem_ofFn
  let e := (localCohomologyCechComparison (IsLocalRing.maximalIdeal S) rs hI n).some
  let e₁ : cechCoefficients rs (ModuleCat.of S S) ≅ C :=
    HomologicalComplex.rightUnitor C
  have eLast : (C).homology n ≅ (C).homology qtop :=
    eqToIso (congrArg (fun i : ℤ => (C).homology i) (by omega : n = qtop))
  exact e.app (ModuleCat.of S S) ≪≫ (homologyFunctor _ _ n).mapIso e₁ ≪≫ eLast

private theorem inverseMonomialBasisAux :
    ∃ π : ModuleCat.of S L ⟶ top k d,
      Function.Surjective π ∧ π.hom.ker = faceImages k d ∧
        ∃ b : Module.Basis (Index d) k (topOverField k d),
          ∀ a, b a = π (inverseMonomial k d a) := by
  obtain ⟨π₀, hsurj, hker⟩ := cechQuotient (k := k) (d := d)
  let e := cohomologyIsoCech k d
  let π := π₀ ≫ e.inv
  have he : Function.Injective e.inv.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  have hkerπ : π.hom.ker = faceImages k d := by
    rw [← hker]
    ext x
    change e.inv.hom (π₀.hom x) = 0 ↔ π₀.hom x = 0
    rw [← map_zero e.inv.hom, he.eq_iff]
  have hπ : Function.Surjective π :=
    ((ModuleCat.epi_iff_surjective e.inv).mp inferInstance).comp hsurj
  let f : L →ₗ[k] topOverField k d :=
    { toFun := π
      map_add' := π.hom.map_add
      map_smul' := fun b x => by
        change π.hom (b • x) = (algebraMap k S b) • π.hom x
        rw [← IsScalarTower.algebraMap_smul S, map_smul] }
  have hf : f.ker = laurentLinear.ker := by
    ext x
    change x ∈ π.hom.ker ↔ laurentLinear x = 0
    rw [hkerπ, laurentLinear_eq_zero_iff]
  let ef := f.quotKerEquivOfSurjective hπ
  let el := (laurentLinear (k := k) (d := d)).quotKerEquivOfSurjective laurentLinear_surj
  let eq := Submodule.quotEquivOfEq _ _ hf.symm
  refine ⟨π, hπ, hkerπ, Finsupp.basisSingleOne.map (el.symm.trans (eq.trans ef)), ?_⟩
  intro a
  rw [Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
  change ef (eq (el.symm (Finsupp.single a 1))) = f (inverseMonomial k d a)
  rw [← laurentLinear_inverseMonomial]
  change ef (eq (el.symm (el (Submodule.Quotient.mk (inverseMonomial k d a))))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- The classes of the inverse monomials form a basis in the top local cohomology. -/
theorem inverseMonomialBasis : InverseMonomialBasis.{u} :=
  fun _ _ _ => inverseMonomialBasisAux

open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues (rightValue)
open AdvancedHomologicalAlgebra.CechToCohomology (natRightDerivedIso)
open Specs.CommutativeAlgebraNotes.GorensteinTopLocalCohomology (derivedTorsionOfRing)

private theorem topIsInjectiveEnvelopeAux (E : ResidueFieldEnvelope S) :
    Nonempty (top k d ≅ ModuleCat.of S E.carrier) := by
  obtain ⟨_, hregular, _, _, hd, _, _, _⟩ := CompleteRegularPowerSeries.overField k d
  let : IsRegularLocalRing S := hregular
  let := HasDerivedCategory.standard (ModuleCat.{u} S)
  have hg := AdvCommAlg.Gorenstein.regularLocal_gorenstein S
  obtain ⟨e⟩ := gorenstein_top_localCohomology hg d hd E
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} S) n
  let F := idealTorsionFunctor (IsLocalRing.maximalIdeal S)
  let e' := (DerivedCategory.singleFunctors (ModuleCat.{u} S)).shiftIso
    (-n) n 0 (neg_add_cancel _)
  exact ⟨(natRightDerivedIso F d).symm.app (ModuleCat.of S S) ≪≫
    H.mapIso (e ≪≫ e'.app (ModuleCat.of S E.carrier)) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} S) n).app
      (ModuleCat.of S E.carrier)⟩

/-- Top cohomology is the residue field's injective envelope over the power series ring. -/
theorem topIsInjectiveEnvelope : TopIsInjectiveEnvelope.{u} :=
  fun _ _ _ E => topIsInjectiveEnvelopeAux E

end CommutativeAlgebraNotes.PowerSeriesLocalCohomology
