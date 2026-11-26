import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExtendDerivations
import Mathlib.Algebra.TrivSqZeroExt.Basic

namespace CommutativeAlgebraNotes

section Localization

variable {R L : Type*} [CommRing R] [CommRing L] [Algebra R L]
variable (S : Submonoid R) [IsLocalization S L] (D : Derivation ℤ R R)

/-- A derivation together with the localization map, written as a ring homomorphism
into the trivial square-zero extension. -/
private def toSquareZero : R →+* TrivSqZeroExt L L where
  toFun a := (algebraMap R L a, algebraMap R L (D a))
  map_one' := TrivSqZeroExt.ext (map_one _) (by simp)
  map_zero' := TrivSqZeroExt.ext (map_zero _) (by simp)
  map_add' a b := TrivSqZeroExt.ext (map_add _ a b) (by
    change algebraMap R L (D (a + b)) = algebraMap R L (D a) + algebraMap R L (D b)
    rw [map_add, map_add])
  map_mul' a b := TrivSqZeroExt.ext (map_mul _ a b) (by
    change algebraMap R L (D (a * b)) =
      algebraMap R L a * algebraMap R L (D b) + algebraMap R L (D a) * algebraMap R L b
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
      mul_comm (algebraMap R L b)])

private noncomputable def localizedSquareZero : L →+* TrivSqZeroExt L L :=
  IsLocalization.lift (g := toSquareZero (L := L) D) fun s : S =>
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (IsLocalization.map_units L s)

private theorem localizedSquareZero_algebraMap (a : R) :
    localizedSquareZero S D (algebraMap R L a) = toSquareZero D a :=
  IsLocalization.lift_eq _ a

private theorem localizedSquareZero_fst (x : L) :
    (localizedSquareZero S D x).fst = x := by
  have h : (TrivSqZeroExt.fstHom L L L).toRingHom.comp (localizedSquareZero S D) =
      RingHom.id L := by
    apply IsLocalization.ringHom_ext S
    ext a
    exact congrArg TrivSqZeroExt.fst (localizedSquareZero_algebraMap S D a)
  exact RingHom.congr_fun h x

/-- The extension of an absolute derivation to a localization. -/
noncomputable def localizationDerivation : Derivation ℤ L L :=
  Derivation.mk'
    ((TrivSqZeroExt.sndHom L L).toAddMonoidHom.comp (localizedSquareZero S D).toAddMonoidHom).toIntLinearMap
    (fun x y => by
      change (localizedSquareZero S D (x * y)).snd =
        x • (localizedSquareZero S D y).snd + y • (localizedSquareZero S D x).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, localizedSquareZero_fst, localizedSquareZero_fst,
        op_smul_eq_smul])

@[simp]
theorem localizationDerivation_algebraMap (a : R) :
    localizationDerivation S D (algebraMap R L a) = algebraMap R L (D a) :=
  congrArg TrivSqZeroExt.snd (localizedSquareZero_algebraMap S D a)

theorem localizationDerivation_mk' (a : R) (s : S) :
    localizationDerivation S D (IsLocalization.mk' L a s) =
      IsLocalization.mk' L (D a) s - IsLocalization.mk' L (a * D (s : R)) (s ^ 2) := by
  have h := congrArg (localizationDerivation S D) (IsLocalization.mk'_spec L a s)
  rw [Derivation.leibniz, localizationDerivation_algebraMap, localizationDerivation_algebraMap,
    smul_eq_mul, smul_eq_mul] at h
  apply (IsLocalization.map_units L s).mul_left_inj.mp
  rw [sub_mul, IsLocalization.mk'_spec, pow_two, IsLocalization.mk'_mul, mul_assoc,
    IsLocalization.mk'_spec, mul_comm (localizationDerivation S D _) _]
  exact eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact h)

theorem exists_localization_derivation :
    Specs.CommutativeAlgebraNotes.DerivationLocalization := by
  intro R L _ _ _ S _ D
  exact ⟨localizationDerivation S D, localizationDerivation_algebraMap S D,
    localizationDerivation_mk' S D⟩

end Localization

theorem derivation_mem_ideal_pow :
    Specs.CommutativeAlgebraNotes.DerivationIdealPower := by
  intro R _ D I n
  induction n with
  | zero =>
      intro a _
      simp
  | succ n ih =>
      intro a ha
      rw [pow_succ] at ha
      refine Submodule.mul_induction_on ha (fun b hb c hc => ?_) (fun b c hb hc => ?_)
      · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hb)
          (by
            rw [pow_succ]
            exact Ideal.mul_mem_mul_rev (ih hb) hc)
      · exact map_add D b c ▸ Ideal.add_mem _ hb hc

section Completion

variable {R : Type*} [CommRing R] (D : Derivation ℤ R R) (I : Ideal R)

/-- The differentiated residue modulo the previous power of the ideal. -/
private def residueDerivation (n : ℕ) :
    R ⧸ (I ^ (n + 1) • ⊤ : Ideal R) → R ⧸ (I ^ n • ⊤ : Ideal R) :=
  fun q => Quotient.liftOn' q (fun a => Ideal.Quotient.mk _ (D a)) fun a b hab => by
    apply Ideal.Quotient.eq.mpr
    rw [← map_sub]
    rw [Submodule.quotientRel_def] at hab
    simpa [smul_eq_mul] using
      derivation_mem_ideal_pow D I n (a := a - b) (by simpa [smul_eq_mul] using hab)

private theorem residueDerivation_mk (n : ℕ) (a : R) :
    residueDerivation D I n (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (D a) :=
  rfl

private theorem residueDerivation_add (n : ℕ) (x y : R ⧸ (I ^ (n + 1) • ⊤ : Ideal R)) :
    residueDerivation D I n (x + y) = residueDerivation D I n x + residueDerivation D I n y := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_add, residueDerivation_mk, residueDerivation_mk, residueDerivation_mk,
    map_add, map_add]

private theorem residueDerivation_mul (n : ℕ) (x y : R ⧸ (I ^ (n + 1) • ⊤ : Ideal R)) :
    residueDerivation D I n (x * y) =
      AdicCompletion.transitionMap I R (Nat.le_succ n) x * residueDerivation D I n y +
      AdicCompletion.transitionMap I R (Nat.le_succ n) y * residueDerivation D I n x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, residueDerivation_mk, residueDerivation_mk, residueDerivation_mk]
  rw [AdicCompletion.transitionMap_ideal_mk, AdicCompletion.transitionMap_ideal_mk]
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul]

private theorem transitionMap_residueDerivation {m n : ℕ} (h : m ≤ n)
    (q : R ⧸ (I ^ (n + 1) • ⊤ : Ideal R)) :
    AdicCompletion.transitionMap I R h (residueDerivation D I n q) =
      residueDerivation D I m (AdicCompletion.transitionMap I R (Nat.succ_le_succ h) q) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rfl

private def completionAddHom : AdicCompletion I R →+ AdicCompletion I R where
  toFun x := ⟨fun n => residueDerivation D I n (x.val (n + 1)), fun {m n} h => by
    change AdicCompletion.transitionMap I R h (residueDerivation D I n (x.val (n + 1))) =
      residueDerivation D I m (x.val (m + 1))
    rw [transitionMap_residueDerivation, AdicCompletion.transitionMap_comp_eval_apply]⟩
  map_zero' := by
    apply AdicCompletion.ext
    intro n
    change residueDerivation D I n 0 = 0
    rw [← (Ideal.Quotient.mk _).map_zero, residueDerivation_mk, map_zero, map_zero]
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    exact residueDerivation_add D I n (x.val (n + 1)) (y.val (n + 1))

/-- The extension of an absolute derivation to the adic completion. -/
noncomputable def adicCompletionDerivation : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R) :=
  Derivation.mk' (completionAddHom D I).toIntLinearMap fun x y => by
    rw [smul_eq_mul, smul_eq_mul]
    apply AdicCompletion.ext
    intro n
    change residueDerivation D I n (x.val (n + 1) * y.val (n + 1)) =
      x.val n * residueDerivation D I n (y.val (n + 1)) +
      y.val n * residueDerivation D I n (x.val (n + 1))
    simpa only [AdicCompletion.transitionMap_comp_eval_apply] using
      residueDerivation_mul D I n (x.val (n + 1)) (y.val (n + 1))

theorem adicCompletionDerivation_eval (x : AdicCompletion I R) (n : ℕ) (a : R)
    (ha : AdicCompletion.evalₐ I (n + 1) x = Ideal.Quotient.mk (I ^ (n + 1)) a) :
    AdicCompletion.evalₐ I n (adicCompletionDerivation D I x) =
      Ideal.Quotient.mk (I ^ n) (D a) := by
  have h (k : ℕ) : (I ^ k • ⊤ : Ideal R) = I ^ k := by simp [smul_eq_mul]
  have ha' := congrArg (Ideal.Quotient.factor (le_of_eq (h (n + 1)).symm)) ha
  rw [AdicCompletion.factor_evalₐ_eq_eval, Ideal.Quotient.factor_mk] at ha'
  rw [← AdicCompletion.factor_eval_eq_evalₐ I _ (le_of_eq (h n))]
  change Ideal.Quotient.factor (le_of_eq (h n))
    (residueDerivation D I n (x.val (n + 1))) = _
  rw [← AdicCompletion.eval_apply I R (n + 1) x, ha', residueDerivation_mk,
    Ideal.Quotient.factor_mk]

@[simp]
theorem adicCompletionDerivation_algebraMap (a : R) :
    adicCompletionDerivation D I (algebraMap R (AdicCompletion I R) a) =
      algebraMap R (AdicCompletion I R) (D a) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ I n (adicCompletionDerivation D I (AdicCompletion.of I R a)) =
    AdicCompletion.evalₐ I n (AdicCompletion.of I R (D a))
  rw [AdicCompletion.evalₐ_of]
  exact adicCompletionDerivation_eval D I (AdicCompletion.of I R a) n a
    (AdicCompletion.evalₐ_of I (n + 1) a)

theorem exists_adicCompletion_derivation :
    Specs.CommutativeAlgebraNotes.DerivationAdicCompletion := by
  intro R _ D I
  exact ⟨adicCompletionDerivation D I, adicCompletionDerivation_algebraMap D I,
    adicCompletionDerivation_eval D I⟩

end Completion

end CommutativeAlgebraNotes
