import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TorusFusion
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TorusOrderedConvolution
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SheafExchangeStalks
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DenseSheetExtension

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite
open scoped Classical MonoidalCategory BraidedCategory

namespace RepTheorySurvey.Geometric.TorusFusion

open Analytic LatticeModelSpecs TorusPerverseSpecs TorusOrderedConvolutionSpecs TorusFusionSpecs
open private skyscrapersProjection from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TorusOrderedConvolution
open private stalkPushforward_naturality from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels
open private constantStalkIso constantStalkIso_germ sheaf_hom_ext_stalk
  pullbackSections inverseImageStalkMap_germ inverseImageStalkMap_naturality
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TorusPerverse

private theorem firstExpansion (p : Marked) (x : ℂ) :
    localExpansion p x firstUnit.val = inclusion (t + PowerSeries.C (x - p.1)) := by
  rw [firstUnit, IsUnit.unit_spec, localExpansion, IsLocalization.Away.lift_eq]
  simp [localPolynomial, firstFactor, sub_eq_add_neg, add_assoc]

private theorem secondExpansion (p : Marked) (x : ℂ) :
    localExpansion p x secondUnit.val = inclusion (t + PowerSeries.C (x - p.2)) := by
  rw [secondUnit, IsUnit.unit_spec, localExpansion, IsLocalization.Away.lift_eq]
  simp [localPolynomial, secondFactor, sub_eq_add_neg, add_assoc]

variable {r : ℕ}

private theorem firstLoop_val (p : Marked) (x : ℂ) (a : Labels r) (i : Fin r) :
    (firstLoop p x a i : K) = inclusion (t + PowerSeries.C (x - p.1)) ^ a i := by
  rw [firstLoop, firstTransition, map_zpow, Units.val_zpow_eq_zpow_val]
  exact congrArg (· ^ a i) (firstExpansion p x)

private theorem secondLoop_val (p : Marked) (x : ℂ) (b : Labels r) (i : Fin r) :
    (secondLoop p x b i : K) = inclusion (t + PowerSeries.C (x - p.2)) ^ b i := by
  rw [secondLoop, secondTransition, map_zpow, Units.val_zpow_eq_zpow_val]
  exact congrArg (· ^ b i) (secondExpansion p x)

private theorem firstLoop_own (p : Marked) (a : Labels r) :
    firstLoop p p.1 a = torusMonomial r a := by
  funext i
  apply Units.ext
  rw [firstLoop_val]
  simpa [torusMonomial] using (monomial_eq_zpow (a i)).symm

private theorem secondLoop_own (p : Marked) (b : Labels r) :
    secondLoop p p.2 b = torusMonomial r b := by
  funext i
  apply Units.ext
  rw [secondLoop_val]
  simpa [torusMonomial] using (monomial_eq_zpow (b i)).symm

private def positiveParameter (x y : ℂ) (h : x ≠ y) : Oˣ :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr (by
    simpa [t, isUnit_iff_ne_zero] using sub_ne_zero.mpr h :
      IsUnit (PowerSeries.constantCoeff (t + PowerSeries.C (x - y))))).unit

private theorem firstLoop_positive (p : Marked) (x : ℂ) (a : Labels r) (h : x ≠ p.1) :
    firstLoop p x a ∈ PositiveTorus r := by
  refine ⟨fun i ↦ positiveParameter x p.1 h ^ a i, ?_⟩
  funext i
  apply Units.ext
  rw [firstLoop_val]
  change (↑((Units.map inclusion.toMonoidHom) (positiveParameter x p.1 h ^ a i)) : K) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

private theorem secondLoop_positive (p : Marked) (x : ℂ) (b : Labels r) (h : x ≠ p.2) :
    secondLoop p x b ∈ PositiveTorus r := by
  refine ⟨fun i ↦ positiveParameter x p.2 h ^ b i, ?_⟩
  funext i
  apply Units.ext
  rw [secondLoop_val]
  change (↑((Units.map inclusion.toMonoidHom) (positiveParameter x p.2 h ^ b i)) : K) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

private theorem torusMonomial_mul (a b : Labels r) :
    torusMonomial r a * torusMonomial r b = torusMonomial r (a + b) := by
  funext i
  apply Units.ext
  exact (monomial_add (a i) (b i)).symm

private theorem zero_monomialPoint :
    monomialPoint r 0 = (fun _ : Fin r ↦ standardLattice 1) := by
  rw [monomialPoint, ← torusMonomial_smul_standard]
  have h : torusMonomial r 0 = 1 := by
    funext i
    apply Units.ext
    change monomial 0 = 1
    simp [monomial_eq_zpow]
  rw [h, one_smul]

theorem localGeometry (D : OrderedGeometry r) : LocalGeometry D where
  ownMark p a b := ⟨firstLoop_own p a, secondLoop_own p b⟩
  positiveElsewhere p x a b := ⟨firstLoop_positive p x a, secondLoop_positive p x b⟩
  factorization p a b hp := by
    let L : TorusLattice r := fun _ ↦ standardLattice 1
    let f : PositiveTorus r := ⟨firstLoop p p.2 a, firstLoop_positive p p.2 a hp.symm⟩
    let s : PositiveTorus r := ⟨secondLoop p p.1 b, secondLoop_positive p p.1 b hp⟩
    have hL (d : Labels r) : torusMonomial r d • L = monomialPoint r d :=
      torusMonomial_smul_standard r d
    refine ⟨(congrArg (· • L) (firstLoop_own p a)).trans (hL a), ?_, ?_, ?_⟩
    · exact (D.coordinates.fixes f L).trans zero_monomialPoint.symm
    · change (firstLoop p p.1 a * (s : Loops r)) • L = _
      rw [mul_smul, D.coordinates.fixes, firstLoop_own, hL]
    · change ((f : Loops r) * secondLoop p p.2 b) • L = _
      rw [mul_smul, D.coordinates.fixes, secondLoop_own, hL]
  diagonal x a b := by
    dsimp only
    rw [show firstLoop (x, x) x a = torusMonomial r a from firstLoop_own (x, x) a,
      show secondLoop (x, x) x b = torusMonomial r b from secondLoop_own (x, x) b,
      torusMonomial_smul_standard]
    have hp : D.wholeMk (torusMonomial r a) (torusLatticeAt r b) = D.wholePair a b := by
      unfold OrderedGeometry.wholeMk OrderedGeometry.wholePair
      rw [← D.coordinates.lattice_monomial]
      rfl
    refine ⟨hp, ?_, ?_⟩
    · change torusMonomial r a • torusLatticeAt r b = _
      unfold terminalLattice
      rw [show firstLoop (x, x) x a = torusMonomial r a from firstLoop_own (x, x) a,
        show secondLoop (x, x) x b = torusMonomial r b from secondLoop_own (x, x) b,
        mul_smul, torusMonomial_smul_standard]
    · unfold terminalLattice
      rw [show firstLoop (x, x) x a = torusMonomial r a from firstLoop_own (x, x) a,
        show secondLoop (x, x) x b = torusMonomial r b from secondLoop_own (x, x) b,
        torusMonomial_mul, torusMonomial_smul_standard]
      rfl

private theorem expansion_linearFactor (x y : ℂ) :
    expandPolynomial x (Polynomial.X - Polynomial.C y) =
      inclusion (t + PowerSeries.C (x - y)) := by
  simp [expandPolynomial, inclusion, sub_eq_add_neg, add_assoc, LaurentSeries.coe_algebraMap,
    HahnSeries.ofPowerSeries_C, LaurentSeries.algebraMap_apply, HahnSeries.C_apply]

theorem clearsPoles {N : ℕ} {A B : Set (Labels r)} (hA : Fits N A) (hB : Fits N B) :
    ClearsPoles N A B := by
  intro p a b x i
  dsimp only
  let u := inclusion (t + PowerSeries.C (x - p.1))
  let v := inclusion (t + PowerSeries.C (x - p.2))
  have hu : u ≠ 0 := by
    intro h
    exact localParameter_ne_zero x p.1
      (HahnSeries.ofPowerSeries_injective (h.trans (map_zero inclusion).symm))
  have hv : v ≠ 0 := by
    intro h
    exact localParameter_ne_zero x p.2
      (HahnSeries.ofPowerSeries_injective (h.trans (map_zero inclusion).symm))
  have hpow (w : K) (hw : w ≠ 0) (m : ℤ) (hm : -(N : ℤ) ≤ m) :
      w ^ ((N : ℤ) + m).toNat = w ^ N * w ^ m := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_add₀ hw, zpow_natCast]
  have mapPow (y : ℂ) (j : ℕ) :
      expandPolynomial x ((Polynomial.X - Polynomial.C y) ^ j) =
        inclusion (t + PowerSeries.C (x - y)) ^ j := by
    exact (map_pow (Polynomial.eval₂RingHom (algebraMap ℂ K) (inclusion (t + PowerSeries.C x)))
      (Polynomial.X - Polynomial.C y) j).trans (congrArg (· ^ j) (expansion_linearFactor x y))
  constructor
  · rw [intermediatePolynomial, mapPow, firstLoop_val, hpow u hu _ (hA _ a.property i).1]
  · have hmap (f g : Polynomial ℂ) :
        expandPolynomial x (f * g) = expandPolynomial x f * expandPolynomial x g :=
      map_mul (Polynomial.eval₂RingHom (algebraMap ℂ K) (inclusion (t + PowerSeries.C x))) f g
    rw [terminalPolynomial, hmap, intermediatePolynomial, mapPow, mapPow]
    change u ^ ((N : ℤ) + a.val i).toNat * v ^ ((N : ℤ) + b.val i).toNat =
      (u * v) ^ N * ((firstLoop p x a.val i : K) * (secondLoop p x b.val i : K))
    rw [hpow u hu _ (hA _ a.property i).1, hpow v hv _ (hB _ b.property i).1,
      firstLoop_val, secondLoop_val, mul_pow]
    change (u ^ N * u ^ a.val i) * (v ^ N * v ^ b.val i) =
      (u ^ N * v ^ N) * (u ^ a.val i * v ^ b.val i)
    ac_rfl


private abbrev offset (N : ℕ) (m : ℤ) := ((N : ℤ) + m).toNat

private theorem offset_bound {N : ℕ} {m : ℤ} (hm : m ≤ N) : offset N m ≤ 2 * N := by
  dsimp [offset]
  omega

private theorem offset_eq_iff {N : ℕ} {m n : ℤ} (hm : -(N : ℤ) ≤ m) (hn : -(N : ℤ) ≤ n) :
    offset N m = offset N n ↔ m = n := by
  dsimp [offset]
  omega

private theorem offset_add_eq_iff {N : ℕ} {a b a' b' : ℤ}
    (ha : -(N : ℤ) ≤ a) (hb : -(N : ℤ) ≤ b)
    (ha' : -(N : ℤ) ≤ a') (hb' : -(N : ℤ) ≤ b') :
    offset N a + offset N b = offset N a' + offset N b' ↔ a + b = a' + b' := by
  dsimp [offset]
  omega

private theorem intermediateDegree {N : ℕ} {A : Set (Labels r)} (hA : Fits N A)
    (p : Marked) (a : A) (i : Fin r) : (intermediatePolynomial N p a.val i).natDegree ≤ 4 * N := by
  have hi := offset_bound (hA _ a.property i).2
  change ((Polynomial.X - Polynomial.C p.1) ^ offset N (a.val i)).natDegree ≤ _
  have h := Polynomial.natDegree_pow_le (p := Polynomial.X - Polynomial.C p.1)
    (n := offset N (a.val i))
  rw [Polynomial.natDegree_X_sub_C, mul_one] at h
  omega

private theorem terminalDegree {N : ℕ} {A B : Set (Labels r)} (hA : Fits N A) (hB : Fits N B)
    (p : Marked) (a : A) (b : B) (i : Fin r) :
    (terminalPolynomial N p a.val b.val i).natDegree ≤ 4 * N := by
  have hpow (x : ℂ) (j : ℕ) : ((Polynomial.X - Polynomial.C x) ^ j).natDegree ≤ j := by
    simp [Polynomial.natDegree_pow]
  have ha := offset_bound (hA _ a.property i).2
  have hb := offset_bound (hB _ b.property i).2
  change (((Polynomial.X - Polynomial.C p.1) ^ offset N (a.val i)) *
    (Polynomial.X - Polynomial.C p.2) ^ offset N (b.val i)).natDegree ≤ _
  refine Polynomial.natDegree_mul_le.trans
    ((Nat.add_le_add (hpow _ _) (hpow _ _)).trans ?_)
  omega

private theorem polynomial_eq_of_bounded_coeff {d : ℕ} {f g : Polynomial ℂ}
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d)
    (h : ∀ i : Fin (d + 1), f.coeff i = g.coeff i) : f = g := by
  ext i
  by_cases hi : i < d + 1
  · exact h ⟨i, hi⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

private theorem intermediateCoefficients_injective {N : ℕ} {A : Set (Labels r)}
    (hA : Fits N A) (p : Marked) {a a' : A}
    (h : intermediateCoefficients N p a.val = intermediateCoefficients N p a'.val) : a = a' := by
  apply Subtype.ext
  funext i
  have he := polynomial_eq_of_bounded_coeff (intermediateDegree hA p a i)
    (intermediateDegree hA p a' i) (fun j ↦ congrFun (congrFun h i) j)
  have hm := congrArg (Polynomial.rootMultiplicity p.1) he
  simp only [intermediatePolynomial, Polynomial.rootMultiplicity_X_sub_C_pow] at hm
  exact (offset_eq_iff (hA _ a.property i).1 (hA _ a'.property i).1).mp hm

private theorem other_rootMultiplicity {x y : ℂ} (h : x ≠ y) (n : ℕ) :
    (((Polynomial.X - Polynomial.C y) ^ n)).rootMultiplicity x = 0 := by
  apply Polynomial.rootMultiplicity_eq_zero
  change ((Polynomial.X - Polynomial.C y) ^ n).eval x ≠ 0
  simpa using pow_ne_zero n (sub_ne_zero.mpr h)

private theorem terminalMultiplicity (p : Marked) (hp : p.1 ≠ p.2)
    (N : ℕ) (a b : Labels r) (i : Fin r) :
    (terminalPolynomial N p a b i).rootMultiplicity p.1 = offset N (a i) ∧
    (terminalPolynomial N p a b i).rootMultiplicity p.2 = offset N (b i) := by
  have hne : terminalPolynomial N p a b i ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))
      (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))
  constructor
  · rw [terminalPolynomial, Polynomial.rootMultiplicity_mul hne, intermediatePolynomial,
      Polynomial.rootMultiplicity_X_sub_C_pow, other_rootMultiplicity hp, add_zero]
  · rw [terminalPolynomial, Polynomial.rootMultiplicity_mul hne, intermediatePolynomial,
      other_rootMultiplicity hp.symm, Polynomial.rootMultiplicity_X_sub_C_pow, zero_add]

private theorem terminalDiagonalPolynomial (p : Marked) (hp : p.1 = p.2)
    (N : ℕ) (a b : Labels r) (i : Fin r) :
    terminalPolynomial N p a b i =
      (Polynomial.X - Polynomial.C p.1) ^ (offset N (a i) + offset N (b i)) := by
  simp only [terminalPolynomial, intermediatePolynomial, ← hp, pow_add]

private theorem terminalCoefficients_distinct {N : ℕ} {A B : Set (Labels r)}
    (hA : Fits N A) (hB : Fits N B) (p : Marked) (hp : p.1 ≠ p.2)
    {a a' : A} {b b' : B}
    (h : terminalCoefficients N p a.val b.val = terminalCoefficients N p a'.val b'.val) :
    a = a' ∧ b = b' := by
  have he (i : Fin r) := polynomial_eq_of_bounded_coeff (terminalDegree hA hB p a b i)
    (terminalDegree hA hB p a' b' i) (fun j ↦ congrFun (congrFun h i) j)
  constructor
  · apply Subtype.ext
    funext i
    apply (offset_eq_iff (hA _ a.property i).1 (hA _ a'.property i).1).mp
    rw [← (terminalMultiplicity p hp N a.val b.val i).1, he i,
      (terminalMultiplicity p hp N a'.val b'.val i).1]
  · apply Subtype.ext
    funext i
    apply (offset_eq_iff (hB _ b.property i).1 (hB _ b'.property i).1).mp
    rw [← (terminalMultiplicity p hp N a.val b.val i).2, he i,
      (terminalMultiplicity p hp N a'.val b'.val i).2]

private theorem terminalCoefficients_diagonal {N : ℕ} {A B : Set (Labels r)}
    (hA : Fits N A) (hB : Fits N B) (p : Marked) (hp : p.1 = p.2)
    (a a' : A) (b b' : B) :
    terminalCoefficients N p a.val b.val = terminalCoefficients N p a'.val b'.val ↔
      a.val + b.val = a'.val + b'.val := by
  have hoff (i : Fin r) := offset_add_eq_iff (hA _ a.property i).1 (hB _ b.property i).1
    (hA _ a'.property i).1 (hB _ b'.property i).1
  constructor
  · intro h
    funext i
    apply (hoff i).mp
    have he := polynomial_eq_of_bounded_coeff (terminalDegree hA hB p a b i)
      (terminalDegree hA hB p a' b' i) (fun j ↦ congrFun (congrFun h i) j)
    rw [terminalDiagonalPolynomial p hp, terminalDiagonalPolynomial p hp] at he
    simpa only [Polynomial.rootMultiplicity_X_sub_C_pow] using
      congrArg (Polynomial.rootMultiplicity p.1) he
  · intro h
    funext i j
    change (terminalPolynomial N p a.val b.val i).coeff j =
      (terminalPolynomial N p a'.val b'.val i).coeff j
    rw [terminalDiagonalPolynomial p hp, terminalDiagonalPolynomial p hp,
      (hoff i).mpr (congrFun h i)]

private theorem terminalPoint_eq_iff {N : ℕ} {A B : Set (Labels r)}
    (hA : Fits N A) (hB : Fits N B) (p : Marked) (a a' : A) (b b' : B) :
    terminalPoint (N := N) (sectionPoint p a b) = terminalPoint (sectionPoint p a' b') ↔
      if p.1 = p.2 then a.val + b.val = a'.val + b'.val else a = a' ∧ b = b' := by
  have he : terminalPoint (N := N) (sectionPoint p a b) =
      terminalPoint (sectionPoint p a' b') ↔
      terminalCoefficients N p a.val b.val = terminalCoefficients N p a'.val b'.val := by
    exact ⟨fun h ↦ congrArg (fun y : terminalSpace N A B ↦ y.val.2) h,
      fun h ↦ Subtype.ext (Prod.ext rfl h)⟩
  rw [he]
  split_ifs with hp
  · exact terminalCoefficients_diagonal hA hB p hp a a' b b'
  · exact ⟨terminalCoefficients_distinct hA hB p hp, by rintro ⟨rfl, rfl⟩; rfl⟩


private theorem continuous_polynomial_mul_coeff {X : Type*} [TopologicalSpace X]
    {f g : X → Polynomial ℂ} (hf : ∀ j, Continuous (fun x ↦ (f x).coeff j))
    (hg : ∀ j, Continuous (fun x ↦ (g x).coeff j)) (j : ℕ) :
    Continuous (fun x ↦ (f x * g x).coeff j) := by
  simp only [Polynomial.coeff_mul]
  exact continuous_finsetSum _ fun p _ ↦ (hf p.1).mul (hg p.2)

private theorem continuous_linear_pow_coeff (n j : ℕ) :
    Continuous (fun x : ℂ ↦ (((Polynomial.X - Polynomial.C x) ^ n)).coeff j) := by
  induction n generalizing j with
  | zero => simpa only [pow_zero] using continuous_const
  | succ n ih =>
    simp_rw [pow_succ]
    refine continuous_polynomial_mul_coeff ih (fun k ↦ ?_) j
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    split_ifs <;> first | exact continuous_const.sub continuous_id | exact continuous_const

private theorem continuous_intermediateCoefficients (N : ℕ) (a : Labels r) :
    Continuous (fun p : Marked ↦ intermediateCoefficients N p a) := by
  exact continuous_pi fun i ↦ continuous_pi fun j ↦
    (continuous_linear_pow_coeff (offset N (a i)) j).comp continuous_fst

private theorem continuous_terminalCoefficients (N : ℕ) (a b : Labels r) :
    Continuous (fun p : Marked ↦ terminalCoefficients N p a b) := by
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ continuous_polynomial_mul_coeff
    (fun k ↦ (continuous_linear_pow_coeff (offset N (a i)) k).comp continuous_fst)
    (fun k ↦ (continuous_linear_pow_coeff (offset N (b i)) k).comp continuous_snd) j

private theorem isClosedMap_finiteGraphs {X Y J : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace J] [T2Space Y] [Finite J] {f : X → J → Y}
    (hf : ∀ j, Continuous (fun x ↦ f x j)) :
    IsClosedMap (fun z : X × J ↦ (z.1, f z.1 z.2)) := by
  intro s hs
  let s' (j : J) : Set (X × Y) :=
    {y | y.2 = f y.1 j} ∩ (fun y : X × Y ↦ (y.1, j)) ⁻¹' s
  have hs' (j : J) : IsClosed (s' j) :=
    (isClosed_eq continuous_snd ((hf j).comp continuous_fst)).inter
      (hs.preimage (continuous_fst.prodMk continuous_const))
  have he : (fun z : X × J ↦ (z.1, f z.1 z.2)) '' s = ⋃ j, s' j := by
    ext y
    constructor
    · rintro ⟨⟨x, j⟩, hz, rfl⟩
      exact Set.mem_iUnion.mpr ⟨j, rfl, hz⟩
    · intro hy
      obtain ⟨j, h, hj⟩ := Set.mem_iUnion.mp hy
      exact ⟨(y.1, j), hj, Prod.ext rfl h.symm⟩
  rw [he]
  exact isClosed_iUnion_of_finite hs'

private theorem orderedPlot_injective {N : ℕ} {A B : Set (Labels r)}
    (hA : Fits N A) (hB : Fits N B) : Function.Injective (orderedPlot N A B) := by
  rintro ⟨p, a, b⟩ ⟨p', a', b'⟩ h
  have hp : p = p' := congrArg Prod.fst h
  subst p'
  have hi : a = a' := intermediateCoefficients_injective hA p (congrArg (fun z ↦ z.2.1) h)
  subst a'
  have ht : terminalCoefficients N p a.val b.val = terminalCoefficients N p a.val b'.val :=
    congrArg (fun z ↦ z.2.2) h
  have hb : b = b' := by
    by_cases hp : p.1 = p.2
    · apply Subtype.ext
      exact add_left_cancel ((terminalCoefficients_diagonal hA hB p hp a a b b').mp ht)
    · exact (terminalCoefficients_distinct hA hB p hp ht).2
  subst b'
  rfl

theorem sectionGeometry {N : ℕ} {A B : Set (Labels r)} (hA : Fits N A) (hB : Fits N B)
    (fA : A.Finite) (fB : B.Finite) : SectionGeometry N A B := by
  let : Finite A := fA.to_subtype
  let : Finite B := fB.to_subtype
  let : DiscreteTopology (OrderedGeometry.labelSpace A B) := ⟨rfl⟩
  let : Finite (OrderedGeometry.labelSpace A B) := inferInstanceAs (Finite (A × B))
  refine ⟨hA, hB, ?_, ?_, terminalPoint_eq_iff hA hB⟩
  · apply (IsClosedEmbedding.of_continuous_injective_isClosedMap ?_
      (orderedPlot_injective hA hB) ?_).isEmbedding
    · apply continuous_prod_of_discrete_right.mpr
      intro q
      exact continuous_id.prodMk ((continuous_intermediateCoefficients N q.1.val).prodMk
        (continuous_terminalCoefficients N q.1.val q.2.val))
    · exact isClosedMap_finiteGraphs fun q : OrderedGeometry.labelSpace A B ↦
        (continuous_intermediateCoefficients N q.1.val).prodMk
        (continuous_terminalCoefficients N q.1.val q.2.val)
  · apply continuous_prod_of_discrete_right.mpr
    intro q
    exact continuous_id.prodMk (continuous_terminalCoefficients N q.1.val q.2.val)

theorem exists_fits {A B : Set (Labels r)} (fA : A.Finite) (fB : B.Finite) :
    ∃ N : ℕ, Fits N A ∧ Fits N B := by
  let : Finite (A ∪ B : Set (Labels r)) := (fA.union fB).to_subtype
  let m (q : (A ∪ B : Set (Labels r)) × Fin r) := (q.1.val q.2).natAbs
  obtain ⟨N, hN⟩ := (Set.finite_range m).bddAbove
  have h : Fits N (A ∪ B) := by
    intro a ha i
    have hbound := hN (Set.mem_range_self ((⟨a, ha⟩, i) : (A ∪ B : Set _) × Fin r))
    change (a i).natAbs ≤ N at hbound
    omega
  exact ⟨N, fun a ha ↦ h a (Or.inl ha), fun b hb ↦ h b (Or.inr hb)⟩

private theorem terminalPlot_swap {N : ℕ} {A B : Set (Labels r)} (z : sheetSpace A B) :
    terminalPlot N B A (swappedPoint z) = ((terminalPlot N A B z).1.swap, (terminalPlot N A B z).2) := by
  apply Prod.ext
  · rfl
  · funext i j
    simp only [terminalPlot, swappedPoint, sectionPoint, terminalCoefficients,
      terminalPolynomial, intermediatePolynomial, Prod.swap]
    rw [mul_comm]

def sectionExchange {N : ℕ} {A B : Set (Labels r)}
    (G : SectionGeometry N A B) (H : SectionGeometry N B A) : SectionExchange G H := by
  let f {C D : Set (Labels r)} (y : terminalSpace N C D) : terminalSpace N D C :=
    ⟨(y.val.1.swap, y.val.2), by
      obtain ⟨z, hz⟩ := y.property
      exact ⟨swappedPoint z, (terminalPlot_swap z).trans
        (congrArg (fun u ↦ (u.1.swap, u.2)) hz)⟩⟩
  have hf {C D : Set (Labels r)} : Continuous (f (C := C) (D := D)) := by
    exact ((continuous_swap.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _
  let e : terminalSpace N A B ≃ₜ terminalSpace N B A :=
    { toFun := f
      invFun := f
      left_inv := fun y ↦ Subtype.ext (Prod.ext rfl rfl)
      right_inv := fun y ↦ Subtype.ext (Prod.ext rfl rfl)
      continuous_toFun := hf
      continuous_invFun := hf }
  exact ⟨TopCat.isoOfHomeo e, fun z ↦ Subtype.ext (terminalPlot_swap z).symm, fun _ ↦ rfl⟩


private abbrev swapFiber {n : Labels r} (p : SumFiber n) : SumFiber n :=
  ⟨p.val.swap, (add_comm _ _).trans p.property⟩

@[simp] private theorem swapFiber_swap {n : Labels r} (p : SumFiber n) :
    swapFiber (swapFiber p) = p := by
  cases p
  rfl

private def fiberFlip (n : Labels r) (V W : Families r) :
    (fiberSum n).obj (V, W) ⟶ (fiberSum n).obj (W, V) :=
  Sigma.desc fun p : SumFiber n ↦
    (β_ (fiber V p.val.1) (fiber W p.val.2)).hom ≫ summand n W V (swapFiber p)

@[simp, reassoc] private theorem summand_fiberFlip (n : Labels r) (V W : Families r)
    (p : SumFiber n) :
    summand n V W p ≫ fiberFlip n V W =
      (β_ (fiber V p.val.1) (fiber W p.val.2)).hom ≫ summand n W V (swapFiber p) :=
  Sigma.ι_comp_desc _ p

@[reassoc] private theorem summand_fiberSum_map (n : Labels r) {V W V' W' : Families r}
    (f : V ⟶ V') (g : W ⟶ W') (p : SumFiber n) :
    summand n V W p ≫ (fiberSum n).map (f, g) =
      (f.app (Discrete.mk p.val.1) ⊗ₘ g.app (Discrete.mk p.val.2)) ≫ summand n V' W' p :=
  Sigma.ι_map (fun q : SumFiber n ↦ f.app (Discrete.mk q.val.1) ⊗ₘ g.app (Discrete.mk q.val.2)) p

set_option backward.isDefEq.respectTransparency false in
private theorem fiberFlip_inverse (n : Labels r) (V W : Families r) :
    fiberFlip n V W ≫ fiberFlip n W V = 𝟙 _ := by
  apply Sigma.hom_ext
  intro p
  change summand n V W p ≫ (fiberFlip n V W ≫ fiberFlip n W V) = summand n V W p ≫ 𝟙 _
  rw [summand_fiberFlip_assoc, summand_fiberFlip, Category.comp_id]
  exact SymmetricCategory.symmetry_assoc (fiber V p.val.1) (fiber W p.val.2) _

set_option backward.isDefEq.respectTransparency false in
private def fiberFlipIso (n : Labels r) :
    fiberSum n ≅ CategoryTheory.Prod.swap _ _ ⋙ fiberSum n :=
  NatIso.ofComponents (fun (V, W) ↦
    { hom := fiberFlip n V W
      inv := fiberFlip n W V
      hom_inv_id := fiberFlip_inverse n V W
      inv_hom_id := fiberFlip_inverse n W V }) (by
    rintro ⟨V, W⟩ ⟨V', W'⟩ ⟨f, g⟩
    apply Sigma.hom_ext
    intro p
    change summand n V W p ≫ ((fiberSum n).map (f, g) ≫ fiberFlip n V' W') =
      summand n V W p ≫ (fiberFlip n V W ≫ (fiberSum n).map (g, f))
    rw [summand_fiberSum_map_assoc, summand_fiberFlip_assoc]
    rw [summand_fiberFlip n V' W' p, summand_fiberSum_map n g f (swapFiber p)]
    exact BraidedCategory.braiding_naturality_assoc
      (f.app (Discrete.mk p.val.1)) (g.app (Discrete.mk p.val.2)) _)

section Commutor

variable {D : OrderedGeometry r} {g : StageGeometry r} {c : ContinuousJets r}

set_option backward.isDefEq.respectTransparency false in
private def stalkFlipIso (P : OrderedProduct D g c) :
    P.convolution ⋙ stalkFamily r g c ≅
      (CategoryTheory.Prod.swap _ _ ⋙ P.convolution) ⋙ stalkFamily r g c :=
  NatIso.ofComponents (fun (V, W) ↦ Discrete.natIso fun n ↦
    ((P.stalkIso n.as).app (V, W)).symm ≪≫
      (fiberFlipIso n.as).app (PerverseFamily V, PerverseFamily W) ≪≫
      (P.stalkIso n.as).app (W, V)) (by
    rintro ⟨V, W⟩ ⟨V', W'⟩ ⟨f, h⟩
    apply NatTrans.ext
    funext n
    let F := stalkFamily r g c
    let u : (PerverseFamily V, PerverseFamily W) ⟶
        (PerverseFamily V', PerverseFamily W') := (F.map f, F.map h)
    let v : (PerverseFamily W, PerverseFamily V) ⟶
        (PerverseFamily W', PerverseFamily V') := (F.map h, F.map f)
    let f' : ((V, W) : Heart r g c × Heart r g c) ⟶ (V', W') := (f, h)
    let h' : ((W, V) : Heart r g c × Heart r g c) ⟶ (W', V') := (h, f)
    have h₁ : (F.map (P.convolution.map f')).app n ≫ (P.stalkIso n.as).inv.app (V', W') =
        (P.stalkIso n.as).inv.app (V, W) ≫ (fiberSum n.as).map u :=
      (P.stalkIso n.as).inv.naturality f'
    have h₂ : (fiberSum n.as).map u ≫ fiberFlip n.as (PerverseFamily V') (PerverseFamily W') =
        fiberFlip n.as (PerverseFamily V) (PerverseFamily W) ≫ (fiberSum n.as).map v :=
      (fiberFlipIso n.as).hom.naturality u
    have h₃ : (fiberSum n.as).map v ≫ (P.stalkIso n.as).hom.app (W', V') =
        (P.stalkIso n.as).hom.app (W, V) ≫ (F.map (P.convolution.map h')).app n :=
      (P.stalkIso n.as).hom.naturality h'
    change (F.map (P.convolution.map f')).app n ≫ ((P.stalkIso n.as).inv.app (V', W') ≫
      fiberFlip n.as (PerverseFamily V') (PerverseFamily W') ≫ (P.stalkIso n.as).hom.app (W', V')) =
      ((P.stalkIso n.as).inv.app (V, W) ≫ fiberFlip n.as (PerverseFamily V) (PerverseFamily W) ≫
        (P.stalkIso n.as).hom.app (W, V)) ≫ (F.map (P.convolution.map h')).app n
    simp only [Category.assoc, reassoc_of% h₁, reassoc_of% h₂, h₃])


def convolutionCommutor (hF : (stalkFamily r g c).FullyFaithful) (P : OrderedProduct D g c) : SwapsConvolution P :=
  (hF.whiskeringRight _).preimageIso (stalkFlipIso P)

private theorem commutorStalk_eq (hF : (stalkFamily r g c).FullyFaithful) (P : OrderedProduct D g c) (V W : Heart r g c) (n : Labels r) :
    commutorStalk (convolutionCommutor hF P) V W n =
      (P.stalkIso n).inv.app (V, W) ≫ fiberFlip n (PerverseFamily V) (PerverseFamily W) ≫
        (P.stalkIso n).hom.app (W, V) := by
  have h := (hF.whiskeringRight (Heart r g c × Heart r g c)).map_preimage
    (stalkFlipIso P).hom
  exact congrArg (fun τ ↦ (τ.app (V, W)).app (Discrete.mk n)) h

private theorem summand_eqToHom (P : OrderedProduct D g c) (V W : Heart r g c)
    (a b n : Labels r) (h : a + b = n) :
    summand n (PerverseFamily V) (PerverseFamily W) ⟨(a, b), h⟩ ≫
      (P.stalkIso n).hom.app (V, W) =
    P.includeSummand V W a b ≫
      eqToHom (congrArg (OrderedProduct.Stalk (P.convolution.obj (V, W))) h) := by
  subst n
  simp only [eqToHom_refl, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem convolutionCommutor_flips (hF : (stalkFamily r g c).FullyFaithful) (P : OrderedProduct D g c) :
    FlipsConvolutionSummands P (convolutionCommutor hF P) := by
  intro V W a b
  rw [commutorStalk_eq]
  change (summand (a + b) (PerverseFamily V) (PerverseFamily W) ⟨(a, b), rfl⟩ ≫
    (P.stalkIso (a + b)).hom.app (V, W)) ≫ (P.stalkIso (a + b)).inv.app (V, W) ≫
      fiberFlip (a + b) (PerverseFamily V) (PerverseFamily W) ≫
      (P.stalkIso (a + b)).hom.app (W, V) = _
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, summand_fiberFlip_assoc]
  exact congrArg ((β_ (OrderedProduct.Stalk V a) (OrderedProduct.Stalk W b)).hom ≫ ·)
    (summand_eqToHom P W V b a (a + b) (add_comm b a))

end Commutor


section TerminalLocus

variable {N : ℕ} {A B : Set (Labels r)} (G : SectionGeometry N A B)

theorem terminalMap_closed (fA : A.Finite) (fB : B.Finite) :
    IsClosedMap (terminalMap G) := by
  let : Finite A := fA.to_subtype
  let : Finite B := fB.to_subtype
  let : Finite (OrderedGeometry.labelSpace A B) := inferInstanceAs (Finite (A × B))
  have hc : IsClosedMap (terminalPlot N A B) :=
    isClosedMap_finiteGraphs fun q : OrderedGeometry.labelSpace A B ↦
      continuous_terminalCoefficients N q.1.val q.2.val
  intro s hs
  have he : terminalMap G '' s =
      (fun y : terminalSpace N A B ↦ y.val) ⁻¹' (terminalPlot N A B '' s) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, hy⟩
      exact ⟨z, hz, Subtype.ext hy⟩
  rw [he]
  exact (hc s hs).preimage continuous_subtype_val

theorem sectionTerminal_closedEmbedding (a : A) (b : B) :
    IsClosedEmbedding (sectionMap a b ≫ terminalMap G) := by
  apply IsClosedEmbedding.of_comp
    (g := fun y : terminalSpace N A B ↦ y.val) IsEmbedding.subtypeVal
  let v := fun p : Marked ↦ terminalCoefficients N p a.val b.val
  change IsClosedEmbedding (fun p : Marked ↦ (p, v p))
  refine ⟨isEmbedding_graph (continuous_terminalCoefficients N a.val b.val), ?_⟩
  have he : Set.range (fun p : Marked ↦ (p, v p)) = {y | y.2 = v y.1} := by
    ext y
    exact ⟨by rintro ⟨p, rfl⟩; rfl, fun h ↦ ⟨y.1, Prod.ext rfl h.symm⟩⟩
  rw [he]
  exact isClosed_eq continuous_snd ((continuous_terminalCoefficients N a.val b.val).comp continuous_fst)

private theorem incidentLabels_injective (y : terminalSpace N A B) :
    Function.Injective (fun z : IncidentSheets G y ↦ z.val.2) := by
  intro z w h
  have hb (q : IncidentSheets G y) : q.val.1 = y.val.1 :=
    congrArg (fun t : terminalSpace N A B ↦ t.val.1) q.property
  exact Subtype.ext (Prod.ext ((hb z).trans (hb w).symm) h)

theorem incidentSheets_finite (fA : A.Finite) (fB : B.Finite) (y : terminalSpace N A B) :
    Finite (IncidentSheets G y) := by
  let : Finite A := fA.to_subtype
  let : Finite B := fB.to_subtype
  let : Finite (OrderedGeometry.labelSpace A B) := inferInstanceAs (Finite (A × B))
  exact Finite.of_injective _ (incidentLabels_injective G y)

theorem incidentSheets_sum (x : ℂ) (a : A) (b : B)
    (z : IncidentSheets G (terminalMap G (sectionPoint (x, x) a b))) :
    z.val.2.1.val + z.val.2.2.val = a.val + b.val := by
  have hp : z.val.1 = (x, x) :=
    congrArg (fun y : terminalSpace N A B ↦ y.val.1) z.property
  have he : z.val = sectionPoint (x, x) z.val.2.1 z.val.2.2 := Prod.ext hp rfl
  have h := congrArg (terminalMap G) he
  have hs := (G.terminalEquality (x, x) z.val.2.1 a z.val.2.2 b).mp (h.symm.trans z.property)
  simpa using hs

end TerminalLocus


section Diagonal

variable {D : OrderedGeometry r} {g : StageGeometry r} {c : ContinuousJets r}
variable {N : ℕ} {A B : Set (Labels r)} (G : SectionGeometry N A B)
variable (x : ℂ) (a : A) (b : B)

private abbrev collision := terminalMap G (sectionPoint (x, x) a b)
private abbrev collisionWeight := a.val + b.val

private abbrev indexOfSheet (z : IncidentSheets G (collision G x a b)) :
    SumFiber (collisionWeight a b) :=
  ⟨(z.val.2.1.val, z.val.2.2.val), incidentSheets_sum G x a b z⟩

private abbrev sheetOfIndex (p : SumFiber (collisionWeight a b))
    (ha : p.val.1 ∈ A) (hb : p.val.2 ∈ B) : IncidentSheets G (collision G x a b) :=
  ⟨sectionPoint (x, x) ⟨p.val.1, ha⟩ ⟨p.val.2, hb⟩,
    (G.terminalEquality (x, x) ⟨p.val.1, ha⟩ a ⟨p.val.2, hb⟩ b).mpr (by
      simpa using p.property)⟩

private theorem sheetOfIndex_indexOfSheet (z : IncidentSheets G (collision G x a b)) :
    sheetOfIndex G x a b (indexOfSheet G x a b z) z.val.2.1.property z.val.2.2.property = z := by
  apply Subtype.ext
  have h := congrArg (fun y : terminalSpace N A B ↦ y.val.1) z.property
  exact Prod.ext h.symm rfl

private theorem tensor_isZero_left {M N : Coeff.{0}} (h : IsZero M) : IsZero (M ⊗ N) := by
  rw [IsZero.iff_id_eq_zero]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m n
  have hz : (𝟙 M : M ⟶ M) = 0 := (IsZero.iff_id_eq_zero M).mp h
  have hm : m = 0 := by
    simpa using congrArg (fun f : M ⟶ M ↦ f m) hz
  change TensorProduct.tmul ℚ m n = 0
  rw [hm, TensorProduct.zero_tmul]

private theorem tensor_isZero_right {M N : Coeff.{0}} (h : IsZero N) : IsZero (M ⊗ N) :=
  (tensor_isZero_left (N := M) h).of_iso (β_ M N)

variable (V W : Heart r g c)
local notation "VF" => PerverseFamily V
local notation "WF" => PerverseFamily W
local notation "n₀" => collisionWeight a b
local notation "J" => IncidentSheets G (collision G x a b)
local notation "Q" => (∐ fun z : J ↦ SheetValue VF WF (Subtype.val z))

private def includeCollision : Q ⟶ (fiberSum n₀).obj (VF, WF) :=
  Sigma.desc fun z : J ↦ summand n₀ VF WF (indexOfSheet G x a b z)

@[reassoc] private theorem includeCollision_ι (z : J) :
    Sigma.ι (fun w : J ↦ SheetValue VF WF w.val) z ≫ includeCollision G x a b V W =
      summand n₀ VF WF (indexOfSheet G x a b z) :=
  Sigma.ι_comp_desc _ z

private def projectCollisionComponent (p : SumFiber n₀) :
    fiber VF p.val.1 ⊗ fiber WF p.val.2 ⟶ Q :=
  if ha : p.val.1 ∈ A then
    if hb : p.val.2 ∈ B then
      Sigma.ι (fun w : J ↦ SheetValue VF WF w.val) (sheetOfIndex G x a b p ha hb) else 0
  else 0

private def projectCollision : (fiberSum n₀).obj (VF, WF) ⟶ Q :=
  Sigma.desc (projectCollisionComponent G x a b V W)

@[reassoc] private theorem projectCollision_ι (p : SumFiber n₀) :
    summand n₀ VF WF p ≫ projectCollision G x a b V W =
      projectCollisionComponent G x a b V W p :=
  Sigma.ι_comp_desc _ p

set_option backward.isDefEq.respectTransparency false in
private def collisionSummandsIso (hs : supportedPairs r g c A B (V, W)) :
    Q ≅ (fiberSum n₀).obj (VF, WF) where
  hom := includeCollision G x a b V W
  inv := projectCollision G x a b V W
  hom_inv_id := by
    apply Sigma.hom_ext
    intro z
    rw [includeCollision_ι_assoc, projectCollision_ι, Category.comp_id]
    unfold projectCollisionComponent
    rw [dite_eq_left z.val.2.1.property, dite_eq_left z.val.2.2.property]
    congr 1
    exact sheetOfIndex_indexOfSheet G x a b z
  inv_hom_id := by
    apply Sigma.hom_ext
    intro p
    change summand n₀ VF WF p ≫ (projectCollision G x a b V W ≫ includeCollision G x a b V W) =
      summand n₀ VF WF p ≫ 𝟙 _
    rw [projectCollision_ι_assoc, Category.comp_id]
    by_cases ha : p.val.1 ∈ A
    · by_cases hb : p.val.2 ∈ B
      · unfold projectCollisionComponent
        rw [dite_eq_left ha, dite_eq_left hb, includeCollision_ι]
        rfl
      · have hzero : IsZero (fiber WF p.val.2) := by
          by_contra h
          exact hb (hs.2 h)
        exact (tensor_isZero_right hzero).eq_of_src _ _
    · have hzero : IsZero (fiber VF p.val.1) := by
        by_contra h
        exact ha (hs.1 h)
      exact (tensor_isZero_left hzero).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
def diagonalIdentification (P : OrderedProduct D g c) (hs : supportedPairs r g c A B (V, W))
    (F : TerminalFiber D G VF WF (collision G x a b)) :
    DiagonalIdentification P G V W (collision G x a b) n₀ F where
  order := incidentSheets_sum G x a b
  iso := F.iso.symm ≪≫ collisionSummandsIso G x a b V W hs ≪≫ (P.stalkIso n₀).app (V, W)
  onSummand z := by
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
    change Sigma.ι _ z ≫ includeCollision G x a b V W ≫ (P.stalkIso n₀).hom.app (V, W) = _
    rw [includeCollision_ι_assoc]
    exact summand_eqToHom P V W _ _ n₀ (incidentSheets_sum G x a b z)

end Diagonal


section StalkPushforward

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : Sheaves X) (y : Y)

private abbrev PreimagePoint := {x : X // f x = y}

private def pushforwardStalkComponent (x : PreimagePoint f y) :
    (stalk y).obj ((directImage f).obj F) ⟶ (stalk x.val).obj F :=
  eqToHom (congrArg (fun y ↦ (stalk y).obj ((directImage f).obj F)) x.property.symm) ≫
    TopCat.Presheaf.stalkPushforward Coeff.{0} f F.presheaf x.val

private theorem preimagePoint_mem (x : PreimagePoint f y) {U : Opens Y} (hU : y ∈ U) :
    x.val ∈ (Opens.map f).obj U := by
  change f x.val ∈ U
  rw [x.property]
  exact hU

private theorem pushforwardStalkComponent_germ (x : PreimagePoint f y)
    (U : Opens Y) (hU : y ∈ U) :
    ((directImage f).obj F).presheaf.germ U y hU ≫ pushforwardStalkComponent f F y x =
      F.presheaf.germ ((Opens.map f).obj U) x.val (preimagePoint_mem f y x hU) := by
  obtain ⟨x, rfl⟩ := x
  simp only [pushforwardStalkComponent, eqToHom_refl]
  exact TopCat.Presheaf.stalkPushforward_germ _ _ _ _ _ _

private theorem exists_open_preimage_le (hf : IsClosedMap f) (W : Opens X)
    (hW : ∀ x : PreimagePoint f y, x.val ∈ W) :
    ∃ U : Opens Y, y ∈ U ∧ (Opens.map f).obj U ≤ W := by
  let U : Opens Y := ⟨(f '' (W : Set X)ᶜ)ᶜ, (hf _ W.2.isClosed_compl).isOpen_compl⟩
  refine ⟨U, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hx (hW ⟨x, hxy⟩)
  · intro x hx
    by_contra hxW
    exact hx ⟨x, hxW, rfl⟩

private def pushforwardStalkMap :
    (stalk y).obj ((directImage f).obj F) ⟶
      ModuleCat.of ℚ (∀ x : PreimagePoint f y, (stalk x.val).obj F) :=
  ModuleCat.ofHom (LinearMap.pi fun x ↦ (pushforwardStalkComponent f F y x).hom)

set_option backward.isDefEq.respectTransparency false in
private theorem pushforwardStalkMap_injective (hf : IsClosedMap f) :
    Function.Injective (pushforwardStalkMap f F y) := by
  intro s t hst
  let P := ((directImage f).obj F).presheaf
  obtain ⟨U, hU, s, rfl⟩ := P.exists_germ_eq s
  obtain ⟨V, hV, t, rfl⟩ := P.exists_germ_eq t
  have hg (x : PreimagePoint f y) :
      F.presheaf.germ ((Opens.map f).obj U) x.val (preimagePoint_mem f y x hU) s =
      F.presheaf.germ ((Opens.map f).obj V) x.val (preimagePoint_mem f y x hV) t := by
    have h := congrFun hst x
    change pushforwardStalkComponent f F y x (P.germ U y hU s) =
      pushforwardStalkComponent f F y x (P.germ V y hV t) at h
    have h₁ := congrArg (fun k ↦ k s) (pushforwardStalkComponent_germ f F y x U hU)
    have h₂ := congrArg (fun k ↦ k t) (pushforwardStalkComponent_germ f F y x V hV)
    exact h₁.symm.trans (h.trans h₂)
  choose W hx iU iV hW using fun x : PreimagePoint f y ↦
    F.presheaf.germ_eq x.val (preimagePoint_mem f y x hU) (preimagePoint_mem f y x hV) s t (hg x)
  obtain ⟨R, hR, hle⟩ := exists_open_preimage_le f y hf (iSup W)
    (fun x ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩)
  let R' := R ⊓ (U ⊓ V)
  have hR' : y ∈ R' := ⟨hR, hU, hV⟩
  let RU : R' ⟶ U := homOfLE (inf_le_right.trans inf_le_left)
  let RV : R' ⟶ V := homOfLE (inf_le_right.trans inf_le_right)
  apply P.germ_ext R' hR' RU RV
  change F.presheaf.map ((Opens.map f).map RU).op s = F.presheaf.map ((Opens.map f).map RV).op t
  apply TopCat.Presheaf.section_ext F
  intro z hz
  have hz' : z ∈ iSup W := hle hz.1
  obtain ⟨q, hzq⟩ := Opens.mem_iSup.mp hz'
  let U' := (Opens.map f).obj R' ⊓ W q
  have hU' : z ∈ U' := ⟨hz, hzq⟩
  let toR : U' ⟶ (Opens.map f).obj R' := homOfLE inf_le_left
  let toW : U' ⟶ W q := homOfLE inf_le_right
  rw [← F.presheaf.germ_res_apply toR z hU', ← F.presheaf.germ_res_apply toR z hU']
  have heU : ((Opens.map f).map RU).op ≫ toR.op = (iU q).op ≫ toW.op := Subsingleton.elim _ _
  have heV : ((Opens.map f).map RV).op ≫ toR.op = (iV q).op ≫ toW.op := Subsingleton.elim _ _
  have h₁ := congrArg (fun k ↦ F.presheaf.map k s) heU
  have h₂ := congrArg (fun k ↦ F.presheaf.map k t) heV
  simp only [F.presheaf.map_comp, ConcreteCategory.comp_apply] at h₁ h₂
  exact congrArg (fun v ↦ F.presheaf.germ U' z hU' v)
    (h₁.trans ((congrArg (fun v ↦ F.presheaf.map toW.op v) (hW q)).trans h₂.symm))

set_option backward.isDefEq.respectTransparency false in
private theorem pushforwardStalkMap_surjective (hf : IsClosedMap f)
    (O : PreimagePoint f y → Opens X) (hO : ∀ x, x.val ∈ O x)
    (hdisj : Pairwise fun x x' ↦ Disjoint (O x) (O x')) :
    Function.Surjective (pushforwardStalkMap f F y) := by
  intro t
  choose W hWO hx s hs using fun x : PreimagePoint f y ↦
    F.presheaf.exists_le_germ_eq (t x) (hO x)
  obtain ⟨R, hR, hRle⟩ := exists_open_preimage_le f y hf (iSup W)
    (fun x ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩)
  let U := (Opens.map f).obj R
  let W' (x : PreimagePoint f y) := U ⊓ W x
  let i (x : PreimagePoint f y) : W' x ⟶ U := homOfLE inf_le_left
  let j (x : PreimagePoint f y) : W' x ⟶ W x := homOfLE inf_le_right
  let s' (x : PreimagePoint f y) := F.presheaf.map (j x).op (s x)
  have hcover : U ≤ iSup W' := by
    intro z hz
    obtain ⟨x, hx⟩ := Opens.mem_iSup.mp (hRle hz)
    exact Opens.mem_iSup.mpr ⟨x, hz, hx⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf W' s' := by
    intro x x'
    by_cases h : x = x'
    · subst x'
      rfl
    · apply TopCat.Presheaf.section_ext F
      intro z hz
      have hle : O x ⊓ O x' ≤ ⊥ := disjoint_iff_inf_le.mp (hdisj h)
      exact False.elim (hle ⟨hWO x hz.1.2, hWO x' hz.2.2⟩)
  obtain ⟨u, hu, _⟩ := F.existsUnique_gluing' W' U i hcover s' hcompat
  let P := ((directImage f).obj F).presheaf
  refine ⟨P.germ R y hR u, ?_⟩
  funext x
  change pushforwardStalkComponent f F y x (P.germ R y hR u) = t x
  have hg := congrArg (fun k ↦ k u) (pushforwardStalkComponent_germ f F y x R hR)
  apply hg.trans
  have hx' : x.val ∈ W' x := ⟨preimagePoint_mem f y x hR, hx x⟩
  exact (F.presheaf.germ_res_apply (i x) x.val hx' u).symm.trans
    ((congrArg (fun v ↦ F.presheaf.germ (W' x) x.val hx' v) (hu x)).trans
      ((F.presheaf.germ_res_apply (j x) x.val hx' (s x)).trans (hs x)))

end StalkPushforward


section TerminalStalk

variable {N : ℕ} {A B : Set (Labels r)} (G : SectionGeometry N A B)

private theorem terminalPushforwardStalkMap_isIso (fA : A.Finite) (fB : B.Finite)
    (F : Sheaves (sheetSpace A B)) (y : terminalSpace N A B) :
    IsIso (pushforwardStalkMap (terminalMap G) F y) := by
  let : DiscreteTopology (OrderedGeometry.labelSpace A B) := ⟨rfl⟩
  let O (z : IncidentSheets G y) : Opens (sheetSpace A B) :=
    ⟨Prod.snd ⁻¹' {z.val.2}, (isOpen_discrete {z.val.2}).preimage continuous_snd⟩
  have hO : ∀ z : IncidentSheets G y, z.val ∈ O z := fun _ ↦ rfl
  have hd : Pairwise fun z w ↦ Disjoint (O z) (O w) := by
    intro z w hzw
    apply disjoint_iff_inf_le.mpr
    intro q hq
    have hz : q.2 = z.val.2 := hq.1
    have hw : q.2 = w.val.2 := hq.2
    exact False.elim (hzw (incidentLabels_injective G y (hz.symm.trans hw)))
  have hc := terminalMap_closed G fA fB
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨pushforwardStalkMap_injective _ _ _ hc, pushforwardStalkMap_surjective _ _ _ hc O hO hd⟩

/-- The canonical germ map identifies the stalk of the terminal direct image
with the product of the stalks at the incident ordered points. -/
def terminalStalkProduct (fA : A.Finite) (fB : B.Finite) (F : Sheaves (sheetSpace A B))
    (y : terminalSpace N A B) :
    (stalk y).obj ((directImage (terminalMap G)).obj F) ≅
      ModuleCat.of ℚ (∀ z : IncidentSheets G y, (stalk z.val).obj F) :=
  @asIso _ _ _ _ _ (terminalPushforwardStalkMap_isIso G fA fB F y)

theorem terminalStalkProduct_hom_apply (fA : A.Finite) (fB : B.Finite)
    (F : Sheaves (sheetSpace A B)) (y : terminalSpace N A B)
    (v : (stalk y).obj ((directImage (terminalMap G)).obj F)) (z : IncidentSheets G y) :
    (terminalStalkProduct G fA fB F y).hom v z =
      pushforwardStalkComponent (terminalMap G) F y z v := rfl

end TerminalStalk


section Coefficients

private theorem productProjection_isIso {I : Type} (M : I → Coeff.{0}) (i : I)
    (hzero : ∀ j, j ≠ i → IsZero (M j)) :
    IsIso (Pi.π M i) := by
  let m (j : I) : M i ⟶ M j := if h : i = j then eqToHom (congrArg M h) else 0
  let inv := Pi.lift m
  have hi : inv ≫ Pi.π M i = 𝟙 _ := by simp [inv, m]
  refine ⟨⟨inv, ?_, hi⟩⟩
  apply Pi.hom_ext
  intro j
  by_cases h : j = i
  · subst j
    simp [Category.assoc, hi]
  · exact (hzero j h).eq_of_tgt _ _

set_option backward.isDefEq.respectTransparency false in
private theorem skyscrapersProjection_isIso (X : TopCat.{0}) [DiscreteTopology X] [Finite X]
    {C : Type*} [Category C] (T : X → C ⥤ Coeff.{0}) (p : X) (V : C) :
    IsIso (skyscrapersProjection X T p V) := by
  let M (q : X) := (skyscraperSheafFunctor q).obj ((T q).obj V)
  let S := stalk p
  let : PreservesFiniteLimits S := inferInstanceAs
    (PreservesFiniteLimits (TopCat.Sheaf.forget Coeff.{0} X ⋙
      TopCat.Presheaf.stalkFunctor Coeff.{0} p))
  let e := PreservesProduct.iso S M
  have hz (q : X) (h : q ≠ p) : IsZero (S.obj (M q)) := by
    apply (isZero_zero Coeff.{0}).of_iso
    exact (skyscraperPresheafStalkOfNotSpecializesIsTerminal q ((T q).obj V) (y := p)
      (mt specializes_iff_eq.mp h)).uniqueUpToIso (isZero_zero _).isTerminal
  have : IsIso (Pi.π (fun q ↦ S.obj (M q)) p) := productProjection_isIso _ _ hz
  have hproj : S.map (Pi.π M p) = e.hom ≫ Pi.π (fun q ↦ S.obj (M q)) p :=
    (piComparison_comp_π S M p).symm
  have : IsIso (S.map (Pi.π M p)) := by rw [hproj]; infer_instance
  have : IsIso ((stalkSkyscraperSheafAdjunction p).counit.app ((T p).obj V)) :=
    inferInstanceAs (IsIso (skyscraperPresheafStalkOfSpecializes p
      ((T p).obj V) specializes_rfl).hom)
  change IsIso (S.map (Pi.π M p) ≫ (stalkSkyscraperSheafAdjunction p).counit.app ((T p).obj V))
  infer_instance

variable {N : ℕ} {A B : Set (Labels r)} (D : OrderedGeometry r) (G : SectionGeometry N A B)
variable (fA : A.Finite) (fB : B.Finite) (V W : Families r) (y : terminalSpace N A B)

private abbrev totalSectionSheaf := (sectionCoefficients D A B).obj (V, W)
private abbrev CoefficientAt (z : IncidentSheets G y) := SheetValue V W z.val

set_option backward.isDefEq.respectTransparency false in
private def descendedStalkValue (a : A) (b : B) :
    (stalk ((D.labels A B).symm (a, b) : D.space A B)).obj
      ((descendedExterior D A B).obj (V, W)) ≅ fiber V a.val ⊗ fiber W b.val := by
  let p : D.space A B := (D.labels A B).symm (a, b)
  let T (q : D.space A B) := exteriorAt (D.labels A B q).1.val (D.labels A B q).2.val
  letI : Finite A := fA.to_subtype
  letI : Finite B := fB.to_subtype
  letI : Finite (D.space A B) := Finite.of_injective (D.labels A B) (D.labels A B).injective
  letI : DiscreteTopology (D.space A B) := ⟨rfl⟩
  haveI : IsIso (skyscrapersProjection (D.space A B) T p (V, W)) :=
    skyscrapersProjection_isIso _ _ _ _
  have h : D.labels A B p = (a, b) := (D.labels A B).apply_symm_apply _
  exact asIso (skyscrapersProjection _ T p (V, W)) ≪≫
    eqToIso (congrArg (fun q : A × B ↦ fiber V q.1.val ⊗ fiber W q.2.val) h)

private def sectionStalkValue (z : sheetSpace A B) :
    (stalk z).obj (totalSectionSheaf D V W) ≅ SheetValue V W z :=
  (inverseImageStalkIso (orderedProjection D A B) ((descendedExterior D A B).obj (V, W)) z).symm
    ≪≫ descendedStalkValue D fA fB V W z.2.1 z.2.2

private def allFiberGerms :
    (stalk y).obj ((terminalCoefficientsSheaf D G).obj (V, W)) ⟶
      ModuleCat.of ℚ (∀ z : IncidentSheets G y, CoefficientAt G V W y z) :=
  ModuleCat.ofHom (LinearMap.pi fun z ↦ (fiberGerm D G V W y z).hom)

include fA fB in
set_option backward.isDefEq.respectTransparency false in
private theorem allFiberGerms_isIso : IsIso (allFiberGerms D G V W y) := by
  let T := terminalStalkProduct G fA fB (totalSectionSheaf D V W) y
  let e (z : IncidentSheets G y) := sectionStalkValue D fA fB V W z.val
  let U := (LinearEquiv.piCongrRight fun z ↦ (e z).toLinearEquiv).toModuleIso
  have he : allFiberGerms D G V W y = T.hom ≫ U.hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    funext z
    rfl
  rw [he]
  infer_instance

private def moduleProductFan {I : Type} (M : I → Coeff.{0}) : Fan M :=
  Fan.mk (ModuleCat.of ℚ (∀ j, M j)) (fun j ↦ ModuleCat.ofHom (LinearMap.proj j))

private def moduleProductFan_isLimit {I : Type} (M : I → Coeff.{0}) :
    IsLimit (moduleProductFan M) :=
  Fan.IsLimit.mk _ (fun s ↦ ModuleCat.ofHom (LinearMap.pi fun j ↦ (s.proj j).hom))
    (fun _ _ ↦ rfl) (fun _ _ h ↦ ModuleCat.hom_ext (LinearMap.ext fun v ↦ funext fun j ↦
      congrArg (fun k ↦ k v) (h j)))

set_option backward.isDefEq.respectTransparency false in
def terminalFiber : TerminalFiber D G V W y := by
  let I := IncidentSheets G y
  let M := CoefficientAt G V W y
  let hfin : Finite I := incidentSheets_finite G fA fB y
  letI : Finite I := hfin
  letI : HasFiniteBiproducts Coeff.{0} := Abelian.hasFiniteBiproducts
  let hlim := moduleProductFan_isLimit M
  let C := (biproduct.isoCoproduct M).symm ≪≫ biproduct.isoProduct M ≪≫
    (productIsProduct M).conePointUniqueUpToIso hlim
  letI : IsIso (allFiberGerms D G V W y) := allFiberGerms_isIso D G fA fB V W y
  let L := asIso (allFiberGerms D G V W y)
  have hC (z w : I) :
      Sigma.ι M z ≫ C.hom ≫ (moduleProductFan M).proj w =
        biproduct.ι M z ≫ biproduct.π M w := by
    have hl : ((productIsProduct M).conePointUniqueUpToIso hlim).hom ≫
        (moduleProductFan M).proj w = Pi.π M w :=
      IsLimit.conePointUniqueUpToIso_hom_comp (productIsProduct M) hlim (Discrete.mk w)
    have hp : (biproduct.isoProduct M).hom ≫ Pi.π M w = biproduct.π M w := by
      rw [biproduct.isoProduct_hom]
      exact Pi.lift_comp_π _ _
    simp only [C, Iso.trans_hom, Iso.symm_hom, Category.assoc, hl, hp,
      biproduct.isoCoproduct_inv, Sigma.ι_comp_desc_assoc]
  have hL (w : I) : L.hom ≫ (moduleProductFan M).proj w = fiberGerm D G V W y w := rfl
  have hh (z w : I) : Sigma.ι M z ≫ (C ≪≫ L.symm).hom ≫ fiberGerm D G V W y w =
      biproduct.ι M z ≫ biproduct.π M w := by
    rw [← hL w]
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc] using hC z w
  exact ⟨hfin, C ≪≫ L.symm, (fun z ↦ (hh z z).trans (biproduct.ι_π_self M z)),
    fun z w hzw ↦ (hh z w).trans (biproduct.ι_π_ne M hzw)⟩

end Coefficients


set_option backward.isDefEq.respectTransparency false in
private theorem pushforwardStalkComponent_natural {X Y : TopCat.{0}} (f : X ⟶ Y)
    {F F' : Sheaves X} (u : F ⟶ F') (y : Y) (z : PreimagePoint f y) :
    (stalk y).map ((directImage f).map u) ≫ pushforwardStalkComponent f F' y z =
      pushforwardStalkComponent f F y z ≫ (stalk z.val).map u := by
  obtain ⟨z, rfl⟩ := z
  unfold pushforwardStalkComponent
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.id_comp]
  exact stalkPushforward_naturality f u.hom z

set_option backward.isDefEq.respectTransparency false in
private theorem terminalDirectImage_preservesExact {N : ℕ} {A B : Set (Labels r)}
    (G : SectionGeometry N A B) (fA : A.Finite) (fB : B.Finite)
    (S : ShortComplex (Sheaves (sheetSpace A B))) (hS : S.Exact) :
    (S.map (directImage (terminalMap G))).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro y
  let f := terminalMap G
  let J := IncidentSheets G y
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro t ht
  change (stalk y).map ((directImage f).map S.g) t = 0 at ht
  have he (z : J) : ∃ s : (stalk z.val).obj S.X₁,
      (stalk z.val).map S.f s = pushforwardStalkComponent f S.X₂ y z t := by
    have hSz : (S.map (stalk z.val)).Exact :=
      (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mp hS z.val
    apply (ShortComplex.moduleCat_exact_iff _).mp hSz
    change (stalk z.val).map S.g (pushforwardStalkComponent f S.X₂ y z t) = 0
    have h := congrArg (fun k ↦ k t) (pushforwardStalkComponent_natural f S.g y z)
    exact h.symm.trans (by rw [ConcreteCategory.comp_apply, ht]; exact map_zero _)
  choose s hs using he
  have hSurj : Function.Surjective (pushforwardStalkMap f S.X₁ y) :=
    ((ConcreteCategory.isIso_iff_bijective _).mp (terminalPushforwardStalkMap_isIso G fA fB S.X₁ y)).2
  obtain ⟨u, hu⟩ := hSurj s
  refine ⟨u, ?_⟩
  change (stalk y).map ((directImage f).map S.f) u = t
  apply pushforwardStalkMap_injective f S.X₂ y (terminalMap_closed G fA fB)
  funext z
  have hz := congrFun hu z
  change pushforwardStalkComponent f S.X₁ y z u = s z at hz
  have hn := congrArg (fun k ↦ k u) (pushforwardStalkComponent_natural f S.f y z)
  exact hn.trans ((congrArg ((stalk z.val).map S.f) hz).trans (hs z))

/-- The finite terminal direct image is exact on rational sheaves. -/
theorem terminalDirectImage_preservesFiniteColimits {N : ℕ} {A B : Set (Labels r)}
    (G : SectionGeometry N A B) (fA : A.Finite) (fB : B.Finite) :
    PreservesFiniteColimits (directImage (terminalMap G)) := by
  let E := directImage (terminalMap G)
  have h : PreservesFiniteLimits E ∧ PreservesFiniteColimits E :=
    (E.exact_tfae.out 2 4).mp (terminalDirectImage_preservesExact G fA fB)
  exact h.2


section DerivedImage

variable {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory E] [EnoughInjectives C]
variable (P : C ⥤ E) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]

set_option backward.isDefEq.respectTransparency false in
private theorem exactRightDerivedUnit_isIso (K : CochainComplex.Plus C) :
    IsIso (P.rightDerivedFunctorPlusUnit.app K) := by
  obtain ⟨n, hn⟩ := K.property
  have : K.obj.IsStrictlyGE n := hn
  obtain ⟨L, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective K n
  have : QuasiIso i.hom := hi
  have hmap : CochainComplex.Plus.quasiIso E (P.mapCochainComplexPlus.map i) := by
    change QuasiIso ((P.mapHomologicalComplex (ComplexShape.up ℤ)).map i.hom)
    infer_instance
  have : IsIso ((P.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).map i) :=
    Localization.inverts (DerivedCategory.Plus.Q (C := E)) (CochainComplex.Plus.quasiIso E) _ hmap
  have : IsIso ((DerivedCategory.Plus.Q ⋙ P.rightDerivedFunctorPlus).map i) := by
    have : IsIso (DerivedCategory.Plus.Q.map i) :=
      Localization.inverts _ (CochainComplex.Plus.quasiIso C) _ hi
    exact (P.rightDerivedFunctorPlus).map_isIso (DerivedCategory.Plus.Q.map i)
  have : IsIso (P.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι C).mapCochainComplexPlus.obj L)) := inferInstance
  have : IsIso (P.rightDerivedFunctorPlusUnit.app K ≫
      (DerivedCategory.Plus.Q ⋙ P.rightDerivedFunctorPlus).map i) := by
    rw [← P.rightDerivedFunctorPlusUnit.naturality i]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.Plus.Q ⋙ P.rightDerivedFunctorPlus).map i)

private def singleComplexPlus (C : Type*) [Category C] [Abelian C] (n : ℤ) :
    C ⥤ CochainComplex.Plus C :=
  ObjectProperty.lift _ (CochainComplex.singleFunctor C n) (fun _ ↦ ⟨n, inferInstance⟩)

private def complexPlusSingleIso (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    (n : ℤ) :
    singleComplexPlus C n ⋙ DerivedCategory.Plus.Q ≅ DerivedCategory.Plus.singleFunctor C n := by
  apply Functor.fullyFaithfulCancelRight (DerivedCategory.Plus.ι (C := C))
  exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
    (DerivedCategory.Plus.QCompιIso C) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ C n).symm ≪≫
    (DerivedCategory.Plus.singleFunctorιIso C n).symm

private def plusMapSingleIso (n : ℤ) :
    singleComplexPlus C n ⋙ P.mapCochainComplexPlus ≅ P ⋙ singleComplexPlus E n := by
  apply Functor.fullyFaithfulCancelRight (ObjectProperty.ι _)
  exact HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) n

private def exactRightDerivedSingleIso (n : ℤ) :
    DerivedCategory.Plus.singleFunctor C n ⋙ P.rightDerivedFunctorPlus ≅
      P ⋙ DerivedCategory.Plus.singleFunctor E n := by
  let u := P.rightDerivedFunctorPlusUnit
  have : ∀ K, IsIso (u.app K) := exactRightDerivedUnit_isIso P
  have : IsIso u := NatIso.isIso_of_isIso_app u
  exact Functor.isoWhiskerRight (complexPlusSingleIso C n).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (asIso u).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (plusMapSingleIso P n) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (complexPlusSingleIso E n)

end DerivedImage

private theorem terminalInDegreeZero {r N : ℕ} {A B : Set (Labels r)}
    (D : OrderedGeometry r) (G : SectionGeometry N A B) (fA : A.Finite) (fB : B.Finite) :
    Nonempty (sectionCoefficients D A B ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
        derivedDirectImage (terminalMap G) ≅
      terminalCoefficientsSheaf D G ⋙ DerivedCategory.Plus.singleFunctor _ 0) := by
  let P := directImage (terminalMap G)
  have : PreservesFiniteColimits P := terminalDirectImage_preservesFiniteColimits G fA fB
  exact ⟨Functor.isoWhiskerLeft (sectionCoefficients D A B) (exactRightDerivedSingleIso P 0) ≪≫
    (Functor.associator _ _ _).symm⟩


section SheetTrivialization

variable {A B : Set (Labels r)} (D : OrderedGeometry r) (fA : A.Finite) (fB : B.Finite)
variable (V W : Families r)

private def labelOpen (a : A) (b : B) : Opens (D.space A B) :=
  ⟨{(D.labels A B).symm (a, b)}, @isOpen_discrete _ _ ⟨rfl⟩ _⟩

private def labelSheet (a : A) (b : B) : Opens (sheetSpace A B) :=
  (Opens.map (orderedProjection D A B)).obj (labelOpen D a b)

private theorem mem_labelSheet (z : sheetSpace A B) (a : A) (b : B) :
    z ∈ labelSheet D a b ↔ (z.2.1, z.2.2) = (a, b) := by
  change (D.labels A B).symm (z.2.1, z.2.2) = (D.labels A B).symm (a, b) ↔ _
  exact (D.labels A B).symm.injective.eq_iff

private theorem labelOpen_germ_isIso (a : A) (b : B) :
    IsIso (((descendedExterior D A B).obj (V, W)).presheaf.germ
      (labelOpen D a b) ((D.labels A B).symm (a, b)) rfl) := by
  let p : D.space A B := (D.labels A B).symm (a, b)
  let U := labelOpen D a b
  let F := (descendedExterior D A B).obj (V, W)
  let m : OpenNhds p := ⟨U, rfl⟩
  have hm : IsTerminal (op m) := IsTerminal.ofUniqueHom
    (fun n ↦ (homOfLE (show U ≤ n.unop.val from Set.singleton_subset_iff.mpr n.unop.property)).op)
    (fun _ _ ↦ Subsingleton.elim _ _)
  exact (colimit.isColimit ((OpenNhds.inclusion p).op ⋙ F.presheaf)).isIso_ι_app_of_isTerminal _ hm

private def labelCoefficient (a : A) (b : B) :
    ((descendedExterior D A B).obj (V, W)).presheaf.obj (op (labelOpen D a b)) ≅
      fiber V a.val ⊗ fiber W b.val := by
  letI := labelOpen_germ_isIso D V W a b
  exact asIso (((descendedExterior D A B).obj (V, W)).presheaf.germ (labelOpen D a b)
    ((D.labels A B).symm (a, b)) rfl) ≪≫ descendedStalkValue D fA fB V W a b

private def sheetConstant (a : A) (b : B) :
    fiber V a.val ⊗ fiber W b.val ⟶ (totalSectionSheaf D V W).presheaf.obj (op (labelSheet D a b)) :=
  (labelCoefficient D fA fB V W a b).inv ≫
    ((inverseDirectAdjunction (orderedProjection D A B)).unit.app
      ((descendedExterior D A B).obj (V, W))).hom.app (op (labelOpen D a b))

set_option backward.isDefEq.respectTransparency false in
private theorem sheetConstant_germ (z : sheetSpace A B) :
    sheetConstant D fA fB V W z.2.1 z.2.2 ≫
      (totalSectionSheaf D V W).presheaf.germ (labelSheet D z.2.1 z.2.2) z
        ((mem_labelSheet D z z.2.1 z.2.2).mpr rfl) =
      (sectionStalkValue D fA fB V W z).inv := by
  let f := orderedProjection D A B
  let F := (descendedExterior D A B).obj (V, W)
  let U := labelOpen D z.2.1 z.2.2
  let q : D.space A B := (D.labels A B).symm (z.2.1, z.2.2)
  have hu : ((inverseDirectAdjunction f).unit.app F).hom.app (op U) ≫
      ((inverseImage f).obj F).presheaf.germ ((Opens.map f).obj U) z rfl =
        F.presheaf.germ U q rfl ≫ inverseImageStalkMap f F z := by
    let α := ((inverseDirectAdjunction f).unit.app F).hom
    let G := (inverseImage f).obj F
    change α.app (op U) ≫ G.presheaf.germ ((Opens.map f).obj U) z rfl =
      F.presheaf.germ U (f z) rfl ≫ (TopCat.Presheaf.stalkFunctor Coeff.{0} (f z)).map α ≫
        G.presheaf.stalkPushforward Coeff.{0} f z
    erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc U (f z) rfl α,
      TopCat.Presheaf.stalkPushforward_germ]
    rfl
  have he : (labelCoefficient D fA fB V W z.2.1 z.2.2).inv ≫ F.presheaf.germ U q rfl =
      (descendedStalkValue D fA fB V W z.2.1 z.2.2).inv := by
    have : IsIso (F.presheaf.germ U q rfl) := labelOpen_germ_isIso D V W _ _
    change (descendedStalkValue D fA fB V W z.2.1 z.2.2).inv ≫
      (asIso (F.presheaf.germ U q rfl)).inv ≫ F.presheaf.germ U q rfl = _
    simp
  exact (congrArg ((labelCoefficient D fA fB V W z.2.1 z.2.2).inv ≫ ·) hu).trans
    (by
      change _ = (descendedStalkValue D fA fB V W z.2.1 z.2.2).inv ≫ inverseImageStalkMap f F z
      rw [← Category.assoc, he])

end SheetTrivialization


section SwapDiagrams

variable {A B : Set (Labels r)}

private theorem swappedPoint_swap (z : sheetSpace A B) : swappedPoint (swappedPoint z) = z := by
  cases z
  rfl

private theorem continuous_swappedPoint : Continuous (@swappedPoint r A B) := by
  let : DiscreteTopology (OrderedGeometry.labelSpace A B) := ⟨rfl⟩
  let : DiscreteTopology (OrderedGeometry.labelSpace B A) := ⟨rfl⟩
  change Continuous (fun z : Marked × OrderedGeometry.labelSpace A B ↦
    (z.1.swap, (z.2.2, z.2.1)) : Marked × OrderedGeometry.labelSpace A B →
      Marked × OrderedGeometry.labelSpace B A)
  have h : @Continuous (OrderedGeometry.labelSpace A B) (OrderedGeometry.labelSpace B A)
      (OrderedGeometry.labelSpace A B).str (OrderedGeometry.labelSpace B A).str
      (fun q ↦ (q.2, q.1)) := continuous_bot
  exact (continuous_swap.comp continuous_fst).prodMk (h.comp continuous_snd)

private def swapSheets : sheetSpace A B ≅ sheetSpace B A :=
  TopCat.isoOfHomeo
    { toFun := swappedPoint
      invFun := swappedPoint
      left_inv := swappedPoint_swap
      right_inv := swappedPoint_swap
      continuous_toFun := continuous_swappedPoint
      continuous_invFun := continuous_swappedPoint }

private theorem exchangeDiagram {N : ℕ} {G : SectionGeometry N A B} {H : SectionGeometry N B A}
    (S : SectionExchange G H) :
    terminalMap G ≫ S.swap.hom = swapSheets.hom ≫ terminalMap H :=
  TopCat.ext S.onPoint

private def pushforwardEquivalence {X Y : TopCat.{0}} (e : X ≅ Y) :
    Sheaves X ≌ Sheaves Y :=
  CategoryTheory.Equivalence.mk (directImage e.hom) (directImage e.inv)
    (eqToIso (congrArg directImage e.hom_inv_id.symm))
    (eqToIso (congrArg directImage e.inv_hom_id))

private theorem inverseDirectCounit_isIso {X Y : TopCat.{0}} (e : X ≅ Y) :
    IsIso ((inverseDirectAdjunction e.hom).counit) := by
  let : (directImage e.hom).IsEquivalence := (pushforwardEquivalence e).isEquivalence_functor
  infer_instance

end SwapDiagrams

set_option backward.isDefEq.respectTransparency false in
private theorem glueStalkSections {X : TopCat.{0}} (F : Sheaves X) (U : Opens X)
    (v : ∀ x : U, (stalk x.val).obj F)
    (h : ∀ x : U, ∃ (V : Opens X) (_ : x.val ∈ V) (i : V ⟶ U)
      (t : F.presheaf.obj (op V)),
        ∀ (y : X) (hy : y ∈ V), F.presheaf.germ V y hy t = v ⟨y, i.le hy⟩) :
    ∃! s : F.presheaf.obj (op U), ∀ (x : X) (hx : x ∈ U), F.presheaf.germ U x hx s = v ⟨x, hx⟩ := by
  choose V hV i t ht using h
  have hcov : U ≤ iSup V := fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hV ⟨x, hx⟩⟩
  have hc : TopCat.Presheaf.IsCompatible F.presheaf V t := by
    intro a b
    apply TopCat.Presheaf.section_ext F
    intro z hz
    rw [F.presheaf.germ_res_apply _ z hz, F.presheaf.germ_res_apply _ z hz]
    exact (ht a z hz.1).trans (ht b z hz.2).symm
  obtain ⟨s, hs, _⟩ := F.existsUnique_gluing' V U i hcov t hc
  have hG (x : X) (hx : x ∈ U) : F.presheaf.germ U x hx s = v ⟨x, hx⟩ := by
    have hg := F.presheaf.germ_res_apply (i ⟨x, hx⟩) x (hV ⟨x, hx⟩) s
    exact hg.symm.trans ((congrArg (fun s ↦ F.presheaf.germ (V ⟨x, hx⟩) x (hV ⟨x, hx⟩) s)
      (hs ⟨x, hx⟩)).trans (ht ⟨x, hx⟩ x (hV ⟨x, hx⟩)))
  exact ⟨s, hG, fun s' hs' ↦ TopCat.Presheaf.section_ext F U s' s
    (fun x hx ↦ (hs' x hx).trans (hG x hx).symm)⟩


section LocalGerms

variable {A B : Set (Labels r)} (D : OrderedGeometry r) (fA : A.Finite) (fB : B.Finite)
variable (V W : Families r)

private abbrev sheetSheaf := (sectionCoefficients D A B).obj (V, W)

private def sheetValueOfSection (U : Opens (sheetSpace A B))
    (s : (sheetSheaf D V W).presheaf.obj (op U)) (z : U) :
    SheetValue V W z.val :=
  (sectionStalkValue D fA fB V W z.val).hom
    ((sheetSheaf D V W).presheaf.germ U z.val z.property s)

set_option backward.isDefEq.respectTransparency false in
private theorem constantRepresentative (U : Opens (sheetSpace A B))
    (s : (sheetSheaf D V W).presheaf.obj (op U)) (z : U) :
    ∃ (Q : Opens (sheetSpace A B)) (_ : z.val ∈ Q) (i : Q ⟶ U)
      (j : Q ⟶ labelSheet D z.val.2.1 z.val.2.2),
      (sheetSheaf D V W).presheaf.map i.op s =
        (sheetSheaf D V W).presheaf.map j.op
          (sheetConstant D fA fB V W z.val.2.1 z.val.2.2
            (sheetValueOfSection D fA fB V W U s z)) := by
  let F : Sheaves (sheetSpace A B) := sheetSheaf D V W
  let e := sectionStalkValue D fA fB V W z.val
  let v := F.presheaf.germ U z.val z.property s
  let c := e.hom v
  let u := sheetConstant D fA fB V W z.val.2.1 z.val.2.2 c
  let hW := (mem_labelSheet D z.val z.val.2.1 z.val.2.2).mpr rfl
  have he := congrArg (fun k ↦ k c) (sheetConstant_germ D fA fB V W z.val)
  have h : v = F.presheaf.germ (labelSheet D z.val.2.1 z.val.2.2) z.val hW u := by
    exact (congrArg (fun k ↦ k v) e.hom_inv_id).symm.trans he.symm
  exact F.presheaf.germ_eq z.val z.property hW s u h

set_option backward.isDefEq.respectTransparency false in
private theorem sheetValue_locallyConstant (U : Opens (sheetSpace A B))
    (s : (sheetSheaf D V W).presheaf.obj (op U)) (a : A) (b : B)
    (p : Marked) (hp : sectionPoint p a b ∈ U) :
    ∃ Q : Opens (TopCat.of Marked), p ∈ Q ∧ ∃ i : Q ⟶ (Opens.map (sectionMap a b)).obj U,
      ∀ (q : Marked) (hq : q ∈ Q),
        sheetValueOfSection D fA fB V W U s ⟨sectionPoint q a b, i.le hq⟩ =
          sheetValueOfSection D fA fB V W U s ⟨sectionPoint p a b, hp⟩ := by
  let z : U := ⟨sectionPoint p a b, hp⟩
  obtain ⟨Q, hp', iu, is, h⟩ := constantRepresentative D fA fB V W U s z
  let f := sectionMap a b
  let V' := (Opens.map f).obj Q
  refine ⟨V', hp', (Opens.map f).map iu, fun q hq ↦ ?_⟩
  let F : Sheaves (sheetSpace A B) := sheetSheaf D V W
  let z' := sectionPoint q a b
  let c := sheetValueOfSection D fA fB V W U s z
  let t := sheetConstant D fA fB V W a b c
  let e := sectionStalkValue D fA fB V W z'
  have hg := congrArg (fun k ↦ F.presheaf.germ Q z' hq k) h
  have hu := F.presheaf.germ_res_apply iu z' hq s
  have hv := F.presheaf.germ_res_apply is z' hq t
  have ht := congrArg (fun k ↦ k c) (sheetConstant_germ D fA fB V W z')
  exact (congrArg (fun k ↦ e.hom k) (hu.symm.trans (hg.trans (hv.trans ht)))).trans
    (congrArg (fun k ↦ k c) e.inv_hom_id)

end LocalGerms


section CoefficientNaturality

set_option backward.isDefEq.respectTransparency false in
private theorem exteriorMap_label_eq {A B : Set (Labels r)} {V W V' W' : Families r}
    (u : (V, W) ⟶ (V', W')) {q q' : A × B} (h : q = q') :
    (exteriorAt q.1.val q.2.val).map u ≫
      eqToHom (congrArg (fun p : A × B ↦ fiber V' p.1.val ⊗ fiber W' p.2.val) h) =
    eqToHom (congrArg (fun p : A × B ↦ fiber V p.1.val ⊗ fiber W p.2.val) h) ≫
      (exteriorAt q'.1.val q'.2.val).map u := by
  subst q'
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem skyscrapersProjection_natural (X : TopCat.{0}) {C : Type*} [Category C]
    (T : X → C ⥤ Coeff.{0}) (p : X) {V V' : C} (u : V ⟶ V') :
    (stalk p).map ((skyscrapers X T).map u) ≫ skyscrapersProjection X T p V' =
      skyscrapersProjection X T p V ≫ (T p).map u := by
  let S := stalk p
  let K := skyscraperSheafFunctor (C := Coeff.{0}) p
  let a := (stalkSkyscraperSheafAdjunction (C := Coeff.{0}) p).counit
  let M (Z : C) (q : X) := (skyscraperSheafFunctor q).obj ((T q).obj Z)
  have hp : (skyscrapers X T).map u ≫ Pi.π (M V') p = Pi.π (M V) p ≫ K.map ((T p).map u) :=
    Pi.map_π (fun q : X ↦ (skyscraperSheafFunctor q).map ((T q).map u)) p
  have ha : S.map (K.map ((T p).map u)) ≫ a.app ((T p).obj V') =
      a.app ((T p).obj V) ≫ (T p).map u := a.naturality _
  change S.map ((skyscrapers X T).map u) ≫ S.map (Pi.π (M V') p) ≫ a.app ((T p).obj V') =
    (S.map (Pi.π (M V) p) ≫ a.app ((T p).obj V)) ≫ (T p).map u
  rw [← Functor.map_comp_assoc, hp, Functor.map_comp, Category.assoc, ha, Category.assoc]

variable {A B : Set (Labels r)} (D : OrderedGeometry r) (fA : A.Finite) (fB : B.Finite)
variable {V W V' W' : Families r}

set_option backward.isDefEq.respectTransparency false in
private theorem descendedStalkValue_natural (u : (V, W) ⟶ (V', W')) (a : A) (b : B) :
    (stalk ((D.labels A B).symm (a, b) : D.space A B)).map ((descendedExterior D A B).map u) ≫
      (descendedStalkValue D fA fB V' W' a b).hom =
    (descendedStalkValue D fA fB V W a b).hom ≫ (exteriorAt a.val b.val).map u := by
  let p : D.space A B := (D.labels A B).symm (a, b)
  let T (q : D.space A B) := exteriorAt (D.labels A B q).1.val (D.labels A B q).2.val
  let h : D.labels A B p = (a, b) := (D.labels A B).apply_symm_apply _
  change (stalk p).map ((skyscrapers _ T).map u) ≫ skyscrapersProjection _ T p (V', W') ≫
      eqToHom (congrArg (fun q : A × B ↦ fiber V' q.1.val ⊗ fiber W' q.2.val) h) =
    (skyscrapersProjection _ T p (V, W) ≫
      eqToHom (congrArg (fun q : A × B ↦ fiber V q.1.val ⊗ fiber W q.2.val) h)) ≫
      (exteriorAt a.val b.val).map u
  rw [← Category.assoc, skyscrapersProjection_natural, Category.assoc,
    exteriorMap_label_eq u h, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem sectionStalkValue_natural (u : (V, W) ⟶ (V', W')) (z : sheetSpace A B) :
    (stalk z).map ((sectionCoefficients D A B).map u) ≫
      (sectionStalkValue D fA fB V' W' z).hom =
    (sectionStalkValue D fA fB V W z).hom ≫ (exteriorAt z.2.1.val z.2.2.val).map u := by
  let f := orderedProjection D A B
  let F := (descendedExterior D A B).obj (V, W)
  let F' := (descendedExterior D A B).obj (V', W')
  let m : F ⟶ F' := (descendedExterior D A B).map u
  let e := inverseImageStalkIso f F z
  let e' := inverseImageStalkIso f F' z
  have hn : (stalk (f z)).map m ≫ e'.hom =
      e.hom ≫ (stalk z).map ((inverseImage f).map m) := inverseImageStalkMap_naturality f m z
  have hinv : (stalk z).map ((inverseImage f).map m) ≫ e'.inv = e.inv ≫ (stalk (f z)).map m := by
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  change (stalk z).map ((inverseImage f).map m) ≫ e'.inv ≫
      (descendedStalkValue D fA fB V' W' z.2.1 z.2.2).hom =
    (e.inv ≫ (descendedStalkValue D fA fB V W z.2.1 z.2.2).hom) ≫ _
  rw [← Category.assoc, hinv, Category.assoc, Category.assoc]
  exact congrArg (e.inv ≫ ·) (descendedStalkValue_natural D fA fB u z.2.1 z.2.2)

end CoefficientNaturality


section ConstantSheaf

private def constantMap {X : TopCat.{0}} (F : Sheaves X) (M : Coeff.{0})
    (v : M ⟶ F.presheaf.obj (op ⊤)) : constant X M ⟶ F :=
  ((constantSheafAdj (Opens.grothendieckTopology X) Coeff.{0}
    (Preorder.isTerminalTop (Opens X))).homEquiv M F).symm v

set_option backward.isDefEq.respectTransparency false in
private theorem constantMap_stalk {X : TopCat.{0}} (F : Sheaves X) (M : Coeff.{0})
    (v : M ⟶ F.presheaf.obj (op ⊤)) (x : X) :
    (constantStalkIso X x M).hom ≫ (stalk x).map (constantMap F M v) =
      v ≫ F.presheaf.Γgerm x := by
  let α := constantMap F M v
  let J := Opens.grothendieckTopology X
  let P : X.Presheaf Coeff.{0} := (Functor.const (Opens X)ᵒᵖ).obj M
  let c := constantPresheafAdj Coeff.{0} (Preorder.isTerminalTop (Opens X))
  let a := sheafificationAdjunction J Coeff.{0}
  have ha : a.homEquiv P F α = (c.homEquiv M F.presheaf).symm v := by
    change a.homEquiv P F ((c.comp a).homEquiv M F |>.symm v) = _
    rw [Adjunction.comp_homEquiv]
    change a.homEquiv P F ((a.homEquiv P F).symm ((c.homEquiv M F.presheaf).symm v)) = _
    exact (a.homEquiv P F).apply_symm_apply _
  have hη : toSheafify J P ≫ α.hom = (c.homEquiv M F.presheaf).symm v :=
    (a.homEquiv_unit P F α).symm.trans ha
  have hv : ((c.homEquiv M F.presheaf).symm v).app (op ⊤) = v := by
    rw [Adjunction.homEquiv_counit]
    change v ≫ F.presheaf.map ((Preorder.isTerminalTop (Opens X)).from ⊤).op = v
    rw [Subsingleton.elim ((Preorder.isTerminalTop (Opens X)).from ⊤) (𝟙 ⊤)]
    change v ≫ F.presheaf.map (𝟙 (op ⊤)) = v
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [constantStalkIso_germ, Category.assoc]
  change (toSheafify J P).app (op ⊤) ≫ ((constant X M).presheaf.Γgerm x ≫
    (TopCat.Presheaf.stalkFunctor Coeff.{0} x).map α.hom) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ, ← Category.assoc]
  exact congrArg (· ≫ F.presheaf.Γgerm x) ((congrArg (fun u ↦ u.app (op ⊤)) hη).trans hv)

variable {A B : Set (Labels r)} (D : OrderedGeometry r) (fA : A.Finite) (fB : B.Finite)
variable (V W : Families r) (a : A) (b : B)

private theorem section_preimage_labelSheet :
    (Opens.map (sectionMap a b)).obj (labelSheet D a b) = ⊤ := by
  ext x
  exact ⟨fun _ ↦ trivial, fun _ ↦ (mem_labelSheet D (sectionPoint x a b) a b).mpr rfl⟩

private def pulledSheetConstant :
    fiber V a.val ⊗ fiber W b.val ⟶
      ((inverseImage (sectionMap a b)).obj ((sectionCoefficients D A B).obj (V, W))).presheaf.obj
        (op ⊤) :=
  sheetConstant D fA fB V W a b ≫ pullbackSections (sectionMap a b) (sheetSheaf D V W)
      (labelSheet D a b) ≫
    eqToHom (congrArg (fun U ↦ ((inverseImage (sectionMap a b)).obj (sheetSheaf D V W)).presheaf.obj
      (op U)) (section_preimage_labelSheet D a b))

private def constantOnSheetHom :
    (constantCoefficients a.val b.val).obj (V, W) ⟶
      ((sectionCoefficients D A B ⋙ inverseImage (sectionMap a b)).obj (V, W)) :=
  constantMap _ _ (pulledSheetConstant D fA fB V W a b)

private theorem transportSection_germ {X : TopCat.{0}} (F : Sheaves X) {U U' : Opens X}
    (h : U = U') (x : X) (hx : x ∈ U) :
    eqToHom (congrArg (fun U ↦ F.presheaf.obj (op U)) h) ≫
      F.presheaf.germ U' x (h ▸ hx) = F.presheaf.germ U x hx := by
  subst U'
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem constantOnSheet_stalk (x : Marked) :
    (constantStalkIso (TopCat.of Marked) x (fiber V a.val ⊗ fiber W b.val)).hom ≫
      (stalk (X := TopCat.of Marked) x).map (constantOnSheetHom D fA fB V W a b) =
    (sectionStalkValue D fA fB V W (sectionPoint x a b)).inv ≫
      inverseImageStalkMap (sectionMap a b) (sheetSheaf D V W) x := by
  let F : Sheaves (sheetSpace A B) := sheetSheaf D V W
  let s := sectionMap a b
  let U := labelSheet D a b
  let G := (inverseImage s).obj F
  let M := fiber V a.val ⊗ fiber W b.val
  change (constantStalkIso (TopCat.of Marked) x M).hom ≫
    (stalk x).map (constantMap G M (pulledSheetConstant D fA fB V W a b)) = _
  rw [constantMap_stalk]
  let h := (mem_labelSheet D (sectionPoint x a b) a b).mpr rfl
  have hpull := inverseImageStalkMap_germ s F U x h
  have ht := transportSection_germ G (section_preimage_labelSheet D a b) x h
  unfold pulledSheetConstant TopCat.Presheaf.Γgerm
  rw [Category.assoc, Category.assoc, ht, ← hpull, ← Category.assoc]
  exact congrArg (· ≫ inverseImageStalkMap s F x)
    (sheetConstant_germ D fA fB V W (sectionPoint x a b))

set_option backward.isDefEq.respectTransparency false in
private theorem constantOnSheetHom_isIso :
    IsIso (constantOnSheetHom D fA fB V W a b) := by
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
  intro x
  let e := constantStalkIso (TopCat.of Marked) x (fiber V a.val ⊗ fiber W b.val)
  change IsIso ((stalk (X := TopCat.of Marked) x).map (constantOnSheetHom D fA fB V W a b))
  have : IsIso (e.hom ≫ (stalk (X := TopCat.of Marked) x).map
      (constantOnSheetHom D fA fB V W a b)) := by
    rw [constantOnSheet_stalk]
    infer_instance
  exact IsIso.of_isIso_comp_left e.hom _

end ConstantSheaf


private def stalkFamilyFullyFaithful (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    (stalkFamily r g c).FullyFaithful := Classical.choice (by
  obtain ⟨g', c', _, _, _, _, E, ⟨e⟩, _⟩ := TorusPerverse.torusPerverseEquivalence r
  have hg : g' = g := Subsingleton.elim _ _
  have hc : c' = c := Subsingleton.elim _ _
  subst g'
  subst c'
  exact ⟨(E.fullyFaithfulFunctor.comp (IsFiniteFamily r).fullyFaithfulι).ofIso e⟩)

section Specialization

variable {N : ℕ} {A B : Set (Labels r)} {G : SectionGeometry N A B} {H : SectionGeometry N B A}
variable (D : OrderedGeometry r) (S : SectionExchange G H)

private abbrev swapIncident (y : terminalSpace N A B) :
    IncidentSheets G y ≃ IncidentSheets H (S.swap.hom y) where
  toFun z := ⟨swappedPoint z.val, (S.onPoint z.val).symm.trans
    (congrArg (fun w : terminalSpace N A B ↦ S.swap.hom w) z.property)⟩
  invFun w := ⟨swappedPoint w.val, (TopCat.homeoOfIso S.swap).injective
    ((S.onPoint (swappedPoint w.val)).trans ((congrArg (terminalMap H)
       (swappedPoint_swap w.val)).trans w.property))⟩
  left_inv z := Subtype.ext (swappedPoint_swap z.val)
  right_inv w := Subtype.ext (swappedPoint_swap w.val)

set_option backward.isDefEq.respectTransparency false in
private theorem exchangeFiberGerm (τ : ExchangeSource D G ⟶ ExchangeTarget D S)
    (V W : Families r) (y : terminalSpace N A B) (z : IncidentSheets G y)
    (h : ActsByFlipAt D S τ z.val) :
    exchangeStalk D S τ V W y ≫ fiberGerm D H W V (S.swap.hom y) (swapIncident S y z) =
      fiberGerm D G V W y z ≫ (β_ (fiber V z.val.2.1.val) (fiber W z.val.2.2.val)).hom := by
  obtain ⟨z, rfl⟩ := z
  have hsrc : fiberGerm D G V W (terminalMap G z) ⟨z, rfl⟩ = sheetGerm D G V W z := by
    unfold fiberGerm
    rw [eqToHom_refl, Category.id_comp]
  rw [hsrc]
  exact h V W

set_option backward.isDefEq.respectTransparency false in
private theorem fiberGerm_hom_ext {X : Coeff.{0}} (fA : A.Finite) (fB : B.Finite)
    (V W : Families r) (y : terminalSpace N A B)
    {u v : X ⟶ (stalk y).obj ((terminalCoefficientsSheaf D G).obj (V, W))}
    (h : ∀ z : IncidentSheets G y, u ≫ fiberGerm D G V W y z = v ≫ fiberGerm D G V W y z) :
    u = v := by
  have : IsIso (allFiberGerms D G V W y) := allFiberGerms_isIso D G fA fB V W y
  apply (cancel_mono (allFiberGerms D G V W y)).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext z
  exact congrArg (fun k ↦ k x) (h z)

set_option backward.isDefEq.respectTransparency false in
private theorem exchangeSummand (fA : A.Finite) (fB : B.Finite)
    (τ : ExchangeSource D G ⟶ ExchangeTarget D S) (V W : Families r)
    (y : terminalSpace N A B) (h : ∀ z : IncidentSheets G y, ActsByFlipAt D S τ z.val)
    (F : TerminalFiber D G V W y) (F' : TerminalFiber D H W V (S.swap.hom y))
    (z : IncidentSheets G y) :
    Sigma.ι _ z ≫ F.iso.hom ≫ exchangeStalk D S τ V W y =
      (β_ (fiber V z.val.2.1.val) (fiber W z.val.2.2.val)).hom ≫
        Sigma.ι (fun w : IncidentSheets H (S.swap.hom y) ↦ SheetValue W V w.val)
          (swapIncident S y z) ≫ F'.iso.hom := by
  apply fiberGerm_hom_ext D fB fA W V
  intro w
  obtain ⟨w, rfl⟩ := (swapIncident S y).surjective w
  simp only [Category.assoc, exchangeFiberGerm D S τ V W y w (h w)]
  by_cases he : z = w
  · subst w
    let β := (β_ (fiber V z.val.2.1.val) (fiber W z.val.2.2.val)).hom
    calc
      _ = β := by
        simpa only [Category.assoc, Category.id_comp] using congrArg (· ≫ β) (F.sameSheet z)
      _ = _ := by
        have h := (congrArg (β ≫ ·) (F'.sameSheet (swapIncident S y z))).trans (Category.comp_id β)
        exact h.symm
  · let β := (β_ (fiber V z.val.2.1.val) (fiber W z.val.2.2.val)).hom
    let γ := (β_ (fiber V w.val.2.1.val) (fiber W w.val.2.2.val)).hom
    calc
      _ = (0 : SheetValue V W z.val ⟶ SheetValue W V (swapIncident S y w).val) := by
        simpa only [Category.assoc, zero_comp] using congrArg (· ≫ γ) (F.otherSheet z w he)
      _ = _ := by
        simpa only [Category.assoc, comp_zero] using
          (congrArg (β ≫ ·) (F'.otherSheet _ _ ((swapIncident S y).injective.ne he))).symm

end Specialization


section CollisionComparison

variable {D : OrderedGeometry r} {g : StageGeometry r} {c : ContinuousJets r}
variable {N : ℕ} {A B : Set (Labels r)} {G : SectionGeometry N A B} {H : SectionGeometry N B A}
variable {S : SectionExchange G H}

private def diagonalIdentificationOfEq (P : OrderedProduct D g c) (V W : Heart r g c)
    (hs : supportedPairs r g c A B (V, W)) (x : ℂ) (a : A) (b : B)
    (y : terminalSpace N A B) (hy : y = terminalMap G (sectionPoint (x, x) a b))
    (n : Labels r) (hn : n = a.val + b.val)
    (F : TerminalFiber D G (PerverseFamily V) (PerverseFamily W) y) :
    DiagonalIdentification P G V W y n F := by
  subst y
  subst n
  exact diagonalIdentification G x a b V W P hs F

private theorem collision_incident_diagonal (x : ℂ) (a : A) (b : B)
    (z : IncidentSheets G (terminalMap G (sectionPoint (x, x) a b))) :
    z.val = sectionPoint (x, x) z.val.2.1 z.val.2.2 :=
  Prod.ext (congrArg (fun y : terminalSpace N A B ↦ y.val.1) z.property) rfl

set_option backward.isDefEq.respectTransparency false in
private theorem specializesToConvolution (P : OrderedProduct D g c)
    (hF : (stalkFamily r g c).FullyFaithful) (E : CoefficientExchange D S)
    (fA : A.Finite) (fB : B.Finite) :
    SpecializesToConvolution (convolutionCommutor hF P) E := by
  intro V W hVW x a b
  let VF := PerverseFamily V
  let WF := PerverseFamily W
  let y := terminalMap G (sectionPoint (x, x) a b)
  let y' := S.swap.hom y
  let n := a.val + b.val
  let F := E.terminalFibers VF WF y
  let F' := terminalFiber D H fB fA WF VF y'
  let I := diagonalIdentification G x a b V W P hVW F
  let I' := diagonalIdentificationOfEq P W V ⟨hVW.2, hVW.1⟩ x b a y'
    (S.onPoint (sectionPoint (x, x) a b)) n (add_comm _ _) F'
  have hflip (z : IncidentSheets G y) : ActsByFlipAt D S E.exchange.hom z.val := by
    have hz := collision_incident_diagonal (G := G) x a b z
    exact (congrArg (ActsByFlipAt D S E.exchange.hom) hz).mpr
      (E.diagonalFlip x z.val.2.1 z.val.2.2)
  refine ⟨F', I, I', ?_⟩
  apply (cancel_epi F.iso.hom).mp
  apply Sigma.hom_ext
  intro z
  let w := swapIncident S y z
  let q : SumFiber n := ⟨(z.val.2.1.val, z.val.2.2.val), I.order z⟩
  have hLeft : Sigma.ι _ z ≫ F.iso.hom ≫ I.iso.hom =
      summand n VF WF q ≫ (P.stalkIso n).hom.app (V, W) :=
    (I.onSummand z).trans (summand_eqToHom P V W _ _ _ (I.order z)).symm
  have hRight : Sigma.ι _ w ≫ F'.iso.hom ≫ I'.iso.hom =
      summand n WF VF (swapFiber q) ≫ (P.stalkIso n).hom.app (W, V) :=
    (I'.onSummand w).trans (summand_eqToHom P W V _ _ _ (I'.order w)).symm
  have hEx := exchangeSummand D S fA fB E.exchange.hom VF WF y hflip F F' z
  rw [reassoc_of% hEx, hRight, reassoc_of% hLeft, commutorStalk_eq,
    Iso.hom_inv_id_app_assoc, summand_fiberFlip_assoc]

end CollisionComparison


section ExchangeOnSheets

variable {A B : Set (Labels r)} (D : OrderedGeometry r) (fA : A.Finite) (fB : B.Finite)
variable (V W : Families r)

private abbrev sourceSheets : Sheaves (sheetSpace A B) := sheetSheaf D V W
private abbrev targetSheets : Sheaves (sheetSpace B A) := sheetSheaf D W V
private abbrev sheetSwap := @swapSheets r A B

private def swappedGermAt (U : Opens (sheetSpace B A))
    (z : U) :
    (sourceSheets D V W (A := A) (B := B)).presheaf.obj (op ((Opens.map sheetSwap.hom).obj U)) ⟶
      (stalk z.val).obj (targetSheets D V W) :=
  let w := swappedPoint z.val
  let hw : w ∈ (Opens.map sheetSwap.hom).obj U := by
    change swappedPoint (swappedPoint z.val) ∈ U
    rw [swappedPoint_swap]
    exact z.property
  (sourceSheets D V W).presheaf.germ ((Opens.map sheetSwap.hom).obj U) w hw ≫
    (sectionStalkValue D fA fB V W w).hom ≫
    (β_ (fiber V w.2.1.val) (fiber W w.2.2.val)).hom ≫
    (sectionStalkValue D fB fA W V z.val).inv

private def markedSlice (Q : Opens (TopCat.of Marked)) (a : B) (b : A) :
    Opens (sheetSpace B A) :=
  ⟨Prod.fst ⁻¹' Q, Q.2.preimage continuous_fst⟩ ⊓ labelSheet D a b

set_option backward.isDefEq.respectTransparency false in
private theorem swapSection_exists (U : Opens (sheetSpace B A))
    (t : (sourceSheets D V W).presheaf.obj (op ((Opens.map sheetSwap.hom).obj U))) :
    ∃! s : (targetSheets D V W).presheaf.obj (op U),
      ∀ (z : sheetSpace B A) (hz : z ∈ U),
        (targetSheets D V W).presheaf.germ U z hz s = swappedGermAt D fA fB V W U ⟨z, hz⟩ t := by
  refine glueStalkSections (targetSheets D V W) U (fun z ↦ swappedGermAt D fA fB V W U z t) ?_
  rintro ⟨⟨p, b, a⟩, hz⟩
  let U' := (Opens.map sheetSwap.hom).obj U
  let q := p.swap
  have hq : sectionPoint q a b ∈ U' := hz
  obtain ⟨Q, hp, i, he⟩ := sheetValue_locallyConstant D fA fB V W U' t a b q hq
  let Q' : Opens (TopCat.of Marked) := ⟨Prod.swap ⁻¹' Q, Q.2.preimage continuous_swap⟩
  let R := markedSlice D Q' b a
  have hR : sectionPoint p b a ∈ R :=
    ⟨hp, (mem_labelSheet D _ _ _).mpr rfl⟩
  have hle : R ≤ U := by
    rintro ⟨p', b', a'⟩ hp'
    have hab : (b', a') = (b, a) := (mem_labelSheet D _ _ _).mp hp'.2
    have hb := congrArg Prod.fst hab
    have ha := congrArg Prod.snd hab
    dsimp only at hb ha
    subst b'; subst a'
    exact i.le hp'.1
  let j : R ⟶ labelSheet D b a := homOfLE inf_le_right
  let M := sheetValueOfSection D fA fB V W U' t ⟨sectionPoint q a b, hq⟩
  let v := (β_ (fiber V a.val) (fiber W b.val)).hom M
  let F : Sheaves (sheetSpace B A) := targetSheets D V W
  let s := sheetConstant D fB fA W V b a v
  refine ⟨R, hR, homOfLE hle, F.presheaf.map j.op s, ?_⟩
  rintro ⟨p', b', a'⟩ hp'
  have hab : (b', a') = (b, a) := (mem_labelSheet D _ _ _).mp hp'.2
  have hb := congrArg Prod.fst hab
  have ha := congrArg Prod.snd hab
  dsimp only at hb ha
  subst b'; subst a'
  let z' := sectionPoint p' b a
  have hsource := he p'.swap hp'.1
  have ht := congrArg (fun k ↦ k v) (sheetConstant_germ D fB fA W V z')
  calc
    _ = F.presheaf.germ (labelSheet D b a) z' (j.le hp') s :=
      F.presheaf.germ_res_apply j z' hp' s
    _ = (sectionStalkValue D fB fA W V z').inv v := ht
    _ = _ := congrArg (fun m ↦ (sectionStalkValue D fB fA W V z').inv
      ((β_ (fiber V a.val) (fiber W b.val)).hom m)) hsource.symm

private def swapSection (U : Opens (sheetSpace B A))
    (t : (sourceSheets D V W).presheaf.obj (op ((Opens.map sheetSwap.hom).obj U))) :
    (targetSheets D V W).presheaf.obj (op U) :=
  (swapSection_exists D fA fB V W U t).choose

private theorem swapSection_germ (U : Opens (sheetSpace B A))
    (t : (sourceSheets D V W).presheaf.obj (op ((Opens.map sheetSwap.hom).obj U)))
    (z : sheetSpace B A) (hz : z ∈ U) :
    (targetSheets D V W).presheaf.germ U z hz (swapSection D fA fB V W U t) =
      swappedGermAt D fA fB V W U ⟨z, hz⟩ t :=
  (swapSection_exists D fA fB V W U t).choose_spec.1 z hz

set_option backward.isDefEq.respectTransparency false in
private def swapSectionLinear (U : Opens (sheetSpace B A)) :
    (sourceSheets D V W).presheaf.obj (op ((Opens.map sheetSwap.hom).obj U)) ⟶
      (targetSheets D V W).presheaf.obj (op U) :=
  ModuleCat.ofHom
    { toFun := swapSection D fA fB V W U
      map_add' := by
        intro s t
        apply TopCat.Presheaf.section_ext (targetSheets D V W)
        intro z hz
        have hs := swapSection_germ D fA fB V W U s z hz
        have ht := swapSection_germ D fA fB V W U t z hz
        exact (swapSection_germ D fA fB V W U (s + t) z hz).trans
          ((map_add _ _ _).trans ((congrArg₂ (· + ·) hs.symm ht.symm).trans (map_add _ _ _).symm))
      map_smul' := by
        intro q s
        apply TopCat.Presheaf.section_ext (targetSheets D V W)
        intro z hz
        have hs := swapSection_germ D fA fB V W U s z hz
        exact (swapSection_germ D fA fB V W U (q • s) z hz).trans
          ((map_smul _ _ _).trans ((congrArg (q • ·) hs.symm).trans (map_smul _ _ _).symm)) }

set_option backward.isDefEq.respectTransparency false in
private theorem swapSectionLinear_natural {U R : Opens (sheetSpace B A)} (i : R ⟶ U) :
    (sourceSheets D V W).presheaf.map ((Opens.map sheetSwap.hom).map i).op ≫
      swapSectionLinear D fA fB V W R =
    swapSectionLinear D fA fB V W U ≫ (targetSheets D V W).presheaf.map i.op := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change swapSection D fA fB V W R
    ((sourceSheets D V W).presheaf.map ((Opens.map sheetSwap.hom).map i).op s) =
      (targetSheets D V W).presheaf.map i.op (swapSection D fA fB V W U s)
  apply TopCat.Presheaf.section_ext (targetSheets D V W)
  intro z hz
  rw [swapSection_germ, (targetSheets D V W).presheaf.germ_res_apply i z hz, swapSection_germ]
  unfold swappedGermAt
  simp only [ConcreteCategory.comp_apply]
  exact congrArg (fun k ↦ (sectionStalkValue D fB fA W V z).inv
    ((β_ (fiber V (swappedPoint z).2.1.val) (fiber W (swappedPoint z).2.2.val)).hom
      ((sectionStalkValue D fA fB V W (swappedPoint z)).hom k)))
    ((sourceSheets D V W).presheaf.germ_res_apply ((Opens.map sheetSwap.hom).map i)
      (swappedPoint z) (by change swappedPoint (swappedPoint z) ∈ R; rwa [swappedPoint_swap]) s)

private def swappedSheetHom :
    (directImage (sheetSwap (A := A) (B := B)).hom).obj (sourceSheets D V W) ⟶ targetSheets D V W :=
  ⟨{ app := fun U ↦ swapSectionLinear D fA fB V W U.unop
     naturality := fun _ _ i ↦ swapSectionLinear_natural D fA fB V W i.unop }⟩

set_option backward.isDefEq.respectTransparency false in
private theorem swappedSheetHom_stalk (z : sheetSpace A B) :
    (stalk (swappedPoint z)).map (swappedSheetHom D fA fB V W) ≫
      (sectionStalkValue D fB fA W V (swappedPoint z)).hom =
    TopCat.Presheaf.stalkPushforward Coeff.{0} sheetSwap.hom (sourceSheets D V W).presheaf z ≫
      (sectionStalkValue D fA fB V W z).hom ≫
      (β_ (fiber V z.2.1.val) (fiber W z.2.2.val)).hom := by
  let F : Sheaves (sheetSpace A B) := sourceSheets D V W
  let F' : Sheaves (sheetSpace B A) := targetSheets D V W
  let φ := swappedSheetHom D fA fB V W
  let s : sheetSpace A B ⟶ sheetSpace B A := sheetSwap.hom
  let e := sectionStalkValue D fB fA W V (s z)
  apply TopCat.Presheaf.stalk_hom_ext (((directImage s).obj F).presheaf)
  intro U hz
  change ((directImage s).obj F).presheaf.germ U (s z) hz ≫
      (TopCat.Presheaf.stalkFunctor Coeff.{0} (s z)).map φ.hom ≫ e.hom =
    ((directImage s).obj F).presheaf.germ U (s z) hz ≫
      F.presheaf.stalkPushforward Coeff.{0} s z ≫ (sectionStalkValue D fA fB V W z).hom ≫ _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc U (s z) hz φ.hom,
    TopCat.Presheaf.stalkPushforward_germ_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  have ht := swapSection_germ D fA fB V W U t (s z) hz
  change e.hom (F'.presheaf.germ U (s z) hz (swapSection D fA fB V W U t)) =
    (β_ (fiber V z.2.1.val) (fiber W z.2.2.val)).hom
      ((sectionStalkValue D fA fB V W z).hom (F.presheaf.germ ((Opens.map s).obj U) z hz t))
  rw [ht]
  obtain ⟨p, a, b⟩ := z
  unfold swappedGermAt
  simp only [ConcreteCategory.comp_apply]
  let v := (β_ (fiber V a.val) (fiber W b.val)).hom
    ((sectionStalkValue D fA fB V W (p, a, b)).hom
      (F.presheaf.germ ((Opens.map s).obj U) (p, a, b) hz t))
  change e.hom (e.inv v) = v
  exact congrArg (fun f : SheetValue W V (s (p, a, b)) ⟶ _ ↦ f v) e.inv_hom_id

set_option backward.isDefEq.respectTransparency false in
private theorem swappedSheetHom_isIso : IsIso (swappedSheetHom D fA fB V W) := by
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
  intro w
  let s : sheetSpace A B ≅ sheetSpace B A := sheetSwap
  obtain ⟨z, rfl⟩ := (TopCat.homeoOfIso s).surjective w
  let e := sectionStalkValue D fB fA W V (s.hom z)
  have hh := swappedSheetHom_stalk D fA fB V W z
  have hi : IsInducing s.hom := (TopCat.homeoOfIso s).isInducing
  have : IsIso (TopCat.Presheaf.stalkPushforward Coeff.{0} s.hom
      (sourceSheets D V W).presheaf z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing Coeff.{0} hi _ _
  have he : IsIso ((stalk (s.hom z)).map (swappedSheetHom D fA fB V W) ≫ e.hom) := by
    change IsIso ((stalk (swappedPoint z)).map (swappedSheetHom D fA fB V W) ≫
      (sectionStalkValue D fB fA W V (swappedPoint z)).hom)
    rw [hh]
    infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    ((stalk (s.hom z)).map (swappedSheetHom D fA fB V W)) e.hom inferInstance he


set_option backward.isDefEq.respectTransparency false in
private theorem swappedSheetHom_natural {V W V' W' : Families r} (u : (V, W) ⟶ (V', W')) :
    (directImage (sheetSwap (A := A) (B := B)).hom).map ((sectionCoefficients D A B).map u) ≫
      swappedSheetHom D fA fB V' W' =
    swappedSheetHom D fA fB V W ≫
      (sectionCoefficients D B A).map (show (W, V) ⟶ (W', V') from (u.2, u.1)) := by
  let s : sheetSpace A B ≅ sheetSpace B A := sheetSwap
  apply sheaf_hom_ext_stalk
  intro y
  obtain ⟨z, rfl⟩ := (TopCat.homeoOfIso s).surjective y
  let Mf := (sectionStalkValue D fB fA W' V' (swappedPoint z)).hom
  change _ = _
  apply (cancel_mono Mf).mp
  let uX := (sectionCoefficients D A B).map u
  let u' : ((W, V) : Families r × Families r) ⟶ (W', V') := (u.2, u.1)
  let uY := (sectionCoefficients D B A).map u'
  change (stalk (swappedPoint z)).map ((directImage s.hom).map uX ≫
    swappedSheetHom D fA fB V' W') ≫ Mf =
      (stalk (swappedPoint z)).map (swappedSheetHom D fA fB V W ≫ uY) ≫ Mf
  have hX := sectionStalkValue_natural D fA fB u z
  have hY := sectionStalkValue_natural D fB fA u' (swappedPoint z)
  have hp := stalkPushforward_naturality s.hom uX.hom z
  have hP : (stalk (swappedPoint z)).map ((directImage s.hom).map uX) ≫
      (sourceSheets D V' W').presheaf.stalkPushforward Coeff.{0} s.hom z =
    (sourceSheets D V W).presheaf.stalkPushforward Coeff.{0} s.hom z ≫ (stalk z).map uX := hp
  have h₁ := swappedSheetHom_stalk D fA fB V' W' z
  have h₂ := swappedSheetHom_stalk D fA fB V W z
  have hm := BraidedCategory.braiding_naturality
    (u.1.app (Discrete.mk z.2.1.val)) (u.2.app (Discrete.mk z.2.2.val))
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, Mf, uY, hY, h₁,
    reassoc_of% h₂]
  have hP' : (stalk (swappedPoint z)).map ((directImage s.hom).map uX) ≫
      (sourceSheets D V' W').presheaf.stalkPushforward Coeff.{0} sheetSwap.hom z =
    (sourceSheets D V W).presheaf.stalkPushforward Coeff.{0} sheetSwap.hom z ≫ (stalk z).map uX := hP
  have hX' : (stalk z).map uX ≫ (sectionStalkValue D fA fB V' W' z).hom =
      (sectionStalkValue D fA fB V W z).hom ≫ (exteriorAt z.2.1.val z.2.2.val).map u := hX
  rw [reassoc_of% hP', reassoc_of% hX']
  exact congrArg (fun k ↦ (sourceSheets D V W).presheaf.stalkPushforward Coeff.{0} sheetSwap.hom z ≫
    (sectionStalkValue D fA fB V W z).hom ≫ k) hm

private def swappedSheetIso :
    sectionCoefficients D A B ⋙ directImage (sheetSwap (A := A) (B := B)).hom ≅
      CategoryTheory.Prod.swap _ _ ⋙ sectionCoefficients D B A :=
  NatIso.ofComponents
    (fun (V, W) ↦ @asIso _ _ _ _ _ (swappedSheetHom_isIso D fA fB V W))
    (fun u ↦ swappedSheetHom_natural D fA fB u)

end ExchangeOnSheets


section TerminalExchange

variable {N : ℕ} {A B : Set (Labels r)} {G : SectionGeometry N A B} {H : SectionGeometry N B A}
variable (D : OrderedGeometry r) (S : SectionExchange G H) (fA : A.Finite) (fB : B.Finite)

private def exchangePushforward :
    terminalCoefficientsSheaf D G ⋙ directImage S.swap.hom ≅
      CategoryTheory.Prod.swap _ _ ⋙ terminalCoefficientsSheaf D H := by
  let C := sectionCoefficients D A B
  let s : sheetSpace A B ≅ sheetSpace B A := swapSheets
  let h : directImage (terminalMap G) ⋙ directImage S.swap.hom ≅
      directImage s.hom ⋙ directImage (terminalMap H) :=
    eqToIso (congrArg directImage (exchangeDiagram S))
  exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft C h ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (swappedSheetIso D fA fB) _ ≪≫
    Functor.associator _ _ _

private def terminalExchangeIso : ExchangeSource D G ≅ ExchangeTarget D S := by
  haveI := inverseDirectCounit_isIso S.swap
  exact (terminalCoefficientsSheaf D G).rightUnitor.symm ≪≫
    Functor.isoWhiskerLeft _ (asIso (inverseDirectAdjunction S.swap.hom).counit).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (exchangePushforward D S fA fB) _ ≪≫
    Functor.associator _ _ _

end TerminalExchange


set_option backward.isDefEq.respectTransparency false in
private theorem constantStalkIso_natural {X : TopCat.{0}} (x : X) {M M' : Coeff.{0}}
    (u : M ⟶ M') :
    (constantStalkIso X x M).hom ≫ (stalk x).map
      ((constantSheaf (Opens.grothendieckTopology X) Coeff.{0}).map u) =
      u ≫ (constantStalkIso X x M').hom := by
  let J := Opens.grothendieckTopology X
  let P := (Functor.const (Opens X)ᵒᵖ).obj M
  let P' := (Functor.const (Opens X)ᵒᵖ).obj M'
  let α : P ⟶ P' := (Functor.const (Opens X)ᵒᵖ).map u
  let γ := (constantSheaf J Coeff.{0}).map u
  have hη := congrArg (fun k ↦ k.app (op (⊤ : Opens X))) (toSheafify_naturality J α)
  rw [constantStalkIso_germ, constantStalkIso_germ, Category.assoc]
  change (toSheafify J P).app (op ⊤) ≫ ((constant X M).presheaf.germ ⊤ x trivial ≫
    (TopCat.Presheaf.stalkFunctor Coeff.{0} x).map γ.hom) =
      u ≫ (toSheafify J P').app (op ⊤) ≫ (constant X M').presheaf.germ ⊤ x trivial
  erw [TopCat.Presheaf.stalkFunctor_map_germ, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ (constant X M').presheaf.germ ⊤ x trivial) hη.symm

set_option backward.isDefEq.respectTransparency false in
private def constantOnSections {A B : Set (Labels r)} (D : OrderedGeometry r)
    (fA : A.Finite) (fB : B.Finite) (a : A) (b : B) :
    sectionCoefficients D A B ⋙ inverseImage (sectionMap a b) ≅ constantCoefficients a.val b.val :=
  (NatIso.ofComponents
    (fun (V, W) ↦ @asIso _ _ _ _ _ (constantOnSheetHom_isIso D fA fB V W a b))
    (by
      rintro ⟨V, W⟩ ⟨V', W'⟩ u
      apply sheaf_hom_ext_stalk
      intro x
      let M := fiber V a.val ⊗ fiber W b.val
      let M' := fiber V' a.val ⊗ fiber W' b.val
      let s := sectionMap a b
      let z := sectionPoint x a b
      let e := sectionStalkValue D fA fB V W z
      let e' := sectionStalkValue D fA fB V' W' z
      let h := (sectionCoefficients D A B).map u
      let k : M ⟶ M' := (exteriorAt a.val b.val).map u
      let K := constantSheaf (Opens.grothendieckTopology (TopCat.of Marked)) Coeff.{0}
      let T := stalk (X := TopCat.of Marked) x
      let eC := constantStalkIso (TopCat.of Marked) x M
      change T.map (K.map k ≫ constantOnSheetHom D fA fB V' W' a b) =
        T.map (constantOnSheetHom D fA fB V W a b ≫ (inverseImage s).map h)
      apply (cancel_epi eC.hom).mp
      have hS : k ≫ e'.inv = e.inv ≫ (stalk z).map h := by
        have w := sectionStalkValue_natural D fA fB u z
        have hw : (stalk z).map h ≫ e'.hom = e.hom ≫ k := w
        apply (cancel_epi e.hom).mp
        rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← hw,
          Category.assoc, Iso.hom_inv_id, Category.comp_id]
      have hI := inverseImageStalkMap_naturality s h x
      have hI' : (stalk z).map h ≫ inverseImageStalkMap s (sheetSheaf D V' W') x =
          inverseImageStalkMap s (sheetSheaf D V W) x ≫ T.map ((inverseImage s).map h) := hI
      have hC := constantStalkIso_natural (X := TopCat.of Marked) x (show M ⟶ M' from k)
      dsimp only [eC]
      simp only [CategoryTheory.Functor.map_comp, T, K, reassoc_of% hC]
      have ha : (constantStalkIso (TopCat.of Marked) x M).hom ≫
          T.map (constantOnSheetHom D fA fB V W a b) =
        e.inv ≫ inverseImageStalkMap s (sheetSheaf D V W) x := constantOnSheet_stalk D fA fB V W a b x
      have hb : (constantStalkIso (TopCat.of Marked) x M').hom ≫
          T.map (constantOnSheetHom D fA fB V' W' a b) =
        e'.inv ≫ inverseImageStalkMap s (sheetSheaf D V' W') x := constantOnSheet_stalk D fA fB V' W' a b x
      rw [hb, reassoc_of% ha, ← Category.assoc, hS, Category.assoc, hI'])).symm

section ExchangeComparison

variable {N : ℕ} {A B : Set (Labels r)} {G : SectionGeometry N A B} {H : SectionGeometry N B A}
variable (D : OrderedGeometry r) (S : SectionExchange G H) (fA : A.Finite) (fB : B.Finite)

private theorem exchangePushforward_app (V W : Families r) :
    (exchangePushforward D S fA fB).hom.app (V, W) =
      (eqToIso (congrArg directImage (exchangeDiagram S))).hom.app (sourceSheets D V W) ≫
        (directImage (terminalMap H)).map (swappedSheetHom D fA fB V W) := rfl

private theorem terminalExchangeIso_app (V W : Families r) :
    let T := (terminalCoefficientsSheaf D G).obj (V, W)
    let ε := (inverseDirectAdjunction S.swap.hom).counit.app T
    letI : IsIso ε := inducedCounit_isIso (TopCat.homeoOfIso S.swap).isInducing T
    (terminalExchangeIso D S fA fB).hom.app (V, W) =
      inv ε ≫ (inverseImage S.swap.hom).map ((exchangePushforward D S fA fB).hom.app (V, W)) := by
  have := inverseDirectCounit_isIso S.swap
  dsimp only
  simp only [terminalExchangeIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.id_comp, Category.comp_id, asIso_inv, NatIso.isIso_inv_app]

set_option backward.isDefEq.respectTransparency false in
private theorem terminalExchange_actsByFlip (z : sheetSpace A B) :
    ActsByFlipAt D S (terminalExchangeIso D S fA fB).hom z := by
  intro V W
  let F := sourceSheets (A := A) (B := B) D V W
  let F' := targetSheets (A := A) (B := B) D V W
  let y := terminalMap G z
  let z' := swappedPoint z
  let T' := (terminalCoefficientsSheaf D H).obj (W, V)
  let transport := eqToHom (congrArg (fun w ↦ (stalk w).obj T') (S.onPoint z))
  let sourceGerm := TopCat.Presheaf.stalkPushforward Coeff.{0} (terminalMap G) F.presheaf z
  let targetGerm := TopCat.Presheaf.stalkPushforward Coeff.{0} (terminalMap H) F'.presheaf z'
  let swapGerm := TopCat.Presheaf.stalkPushforward Coeff.{0} swapSheets.hom F.presheaf z
  have : IsIso swapGerm :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      Coeff.{0} (TopCat.homeoOfIso swapSheets).isInducing F.presheaf z
  let sourceValue := (sectionStalkValue D fA fB V W z).hom
  let targetValue := (sectionStalkValue D fB fA W V z').hom
  let flip := (β_ (fiber V z.2.1.val) (fiber W z.2.2.val)).hom
  have h :
      exchangeStalk D S (terminalExchangeIso D S fA fB).hom V W y ≫
        transport ≫ targetGerm =
      sourceGerm ≫ inv swapGerm ≫ (stalk z').map (swappedSheetHom D fA fB V W) := by
    unfold exchangeStalk
    rw [terminalExchangeIso_app, exchangePushforward_app, Category.assoc]
    exact SheafExchangeStalks.exchangeStalkFormula (terminalMap G) (terminalMap H)
      swapSheets S.swap (exchangeDiagram S) F F' (swappedSheetHom D fA fB V W) z
  have hflip :
      (stalk z').map (swappedSheetHom D fA fB V W) ≫ targetValue =
        swapGerm ≫ sourceValue ≫ flip :=
    swappedSheetHom_stalk D fA fB V W z
  change exchangeStalk D S (terminalExchangeIso D S fA fB).hom V W y ≫
      (transport ≫ targetGerm ≫ targetValue) = (sourceGerm ≫ sourceValue) ≫ flip
  simp only [Category.assoc, reassoc_of% h, hflip, IsIso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem terminalExchange_unique
    (τ : ExchangeSource D G ⟶ ExchangeTarget D S)
    (hτ : ∀ z : sheetSpace A B, z.1.1 ≠ z.1.2 → ActsByFlipAt D S τ z) :
    τ = (terminalExchangeIso D S fA fB).hom := by
  apply NatTrans.ext
  funext VW
  obtain ⟨V, W⟩ := VW
  let J := OrderedGeometry.labelSpace B A
  let : DiscreteTopology J := ⟨rfl⟩
  let F := targetSheets (A := A) (B := B) D V W
  let M (l : J) := fiber W l.1.val ⊗ fiber V l.2.val
  refine DenseSheetExtension.denseSheetExtension J (terminalSpace N B A) (terminalSpace N A B)
    (terminalMap H) S.swap F ((terminalCoefficientsSheaf D G).obj (V, W)) M
    (fun l ↦ (constantOnSections D fB fA l.1 l.2).app (W, V))
    (τ.app (V, W)) ((terminalExchangeIso D S fA fB).hom.app (V, W)) ?_
  rintro ⟨x, y⟩ hxy ⟨b, a⟩ w hw
  let z : sheetSpace A B := sectionPoint (y, x) a b
  have hw' : w = terminalMap G z :=
    (TopCat.homeoOfIso S.swap).injective (hw.trans (S.onPoint z).symm)
  subst w
  have hflip := (hτ z (Ne.symm hxy) V W).trans
    (terminalExchange_actsByFlip D S fA fB z V W).symm
  let y₀ := terminalMap G z
  let z₀ := swappedPoint z
  let T' := (terminalCoefficientsSheaf D H).obj (W, V)
  let u := (stalk y₀).map (τ.app (V, W))
  let v := (stalk y₀).map ((terminalExchangeIso D S fA fB).hom.app (V, W))
  let pullbackStalk := (inverseImageStalkIso S.swap.hom T' y₀).inv
  let transport := eqToHom (congrArg (fun y ↦ (stalk y).obj T') (S.onPoint z))
  let germ := TopCat.Presheaf.stalkPushforward Coeff.{0} (terminalMap H) F.presheaf z₀
  let sheetValue := (sectionStalkValue D fB fA W V z₀).hom
  have hNormalized : (u ≫ pullbackStalk) ≫ transport ≫ germ ≫ sheetValue =
      (v ≫ pullbackStalk) ≫ transport ≫ germ ≫ sheetValue := hflip
  apply (cancel_mono sheetValue).mp
  change (u ≫ (pullbackStalk ≫ transport ≫ germ)) ≫ sheetValue =
    (v ≫ (pullbackStalk ≫ transport ≫ germ)) ≫ sheetValue
  simpa only [Category.assoc] using hNormalized

private def coefficientExchange : CoefficientExchange D S where
  constantOnSections := constantOnSections D fA fB
  terminalFibers := terminalFiber D G fA fB
  terminalInDegreeZero := terminalInDegreeZero D G fA fB
  exchange := terminalExchangeIso D S fA fB
  awayFlip z _ := terminalExchange_actsByFlip D S fA fB z
  uniqueExtension := terminalExchange_unique D S fA fB
  diagonalFlip x a b := terminalExchange_actsByFlip D S fA fB (sectionPoint (x, x) a b)

end ExchangeComparison

/-- Two-point fusion gives the commutor on the geometric ordered convolution. -/
theorem torusFusion : TorusFusion := by
  intro r
  obtain ⟨D, g, c, _, _, _, _, P, hP⟩ := TorusOrderedConvolution.torusOrderedConvolution r
  let hF := stalkFamilyFullyFaithful r g c
  refine ⟨D, g, c, P, hP, localGeometry D, convolutionCommutor hF P,
    convolutionCommutor_flips hF P, ?_⟩
  intro A B fA fB
  obtain ⟨N, hA, hB⟩ := exists_fits fA fB
  let G := sectionGeometry hA hB fA fB
  let H := sectionGeometry hB hA fB fA
  let S := sectionExchange G H
  let E := coefficientExchange D S fA fB
  exact ⟨N, G, H, S, E, clearsPoles hA hB, specializesToConvolution P hF E fA fB⟩

end RepTheorySurvey.Geometric.TorusFusion
