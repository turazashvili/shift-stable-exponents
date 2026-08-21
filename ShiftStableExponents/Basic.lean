/-
END-TO-END verification of Peter Bala's 2023 congruence conjecture.

This file formalizes the
generating-function bridge, so that the final theorem is stated directly about

    bala F G n = n ! * [xⁿ] ( Fⁿ * exp (x * Gⁿ) )

with hypotheses on `F` and `G`, rather than about an abstract combinatorial sum.

CONJECTURE (Peter Bala, OEIS A361036, 13 Mar 2023): for `F, G ∈ ℤ[[x]]` with
`F(0) = G(0) = 1`, `bala F G (n+k) ≡ bala F G n (mod k)`.

STRUCTURE
  §1  `bala` defined literally from `PowerSeries.exp` and `PowerSeries.subst`.
  §2  BRIDGE: `bala = Bint`, an explicit integer sum. (The former gap.)
  §3  Newton expansion of `coeff i (F^A * G^B)` into binomials in `A` and `B`.
  §4  The arithmetic core.
  §5  END-TO-END: `bala` is an integer and satisfies the congruence.

No `sorry`.
-/
import Mathlib

open Finset PowerSeries

namespace ShiftStableExponents

noncomputable section

/-! ## §1  Bala's sequence, defined literally -/

/-- Coercion `ℤ⟦X⟧ → ℚ⟦X⟧`. -/
abbrev toQ : ℤ⟦X⟧ → ℚ⟦X⟧ := PowerSeries.map (Int.castRingHom ℚ)

/-- **Bala's `b n`**, exactly as in the OEIS comment:
`b n = n ! * [xⁿ] ( F(x)ⁿ * exp(x * G(x)ⁿ) )`. The exponential is mathlib's
`PowerSeries.exp` with `x * G(x)ⁿ` substituted for the variable. -/
def bala (W F G : ℚ⟦X⟧) (A M : ℕ → ℕ) (n : ℕ) : ℚ :=
  (Nat.factorial n : ℚ) * coeff n (W * F ^ A n * subst (X * G ^ M n) (exp ℚ))

/-- The explicit integer sum that `bala` will be shown to equal. -/
def Bint (W F G : ℤ⟦X⟧) (A M : ℕ → ℕ) (n : ℕ) : ℤ :=
  ∑ i ∈ range (n + 1),
    (n.descFactorial i : ℤ) * coeff i (W * F ^ A n * G ^ (M n * (n - i)))

/-! ## §2  The bridge -/

lemma hasSubst_X_mul (H : ℚ⟦X⟧) : HasSubst (X * H) :=
  HasSubst.of_constantCoeff_zero' (by simp)

/-- `[xᵉ]((x·H)^d) = [xᵉ⁻ᵈ](H^d)` when `d ≤ e`, and `0` otherwise. -/
lemma coeff_X_mul_pow (H : ℚ⟦X⟧) (d e : ℕ) :
    coeff e ((X * H) ^ d) = if d ≤ e then coeff (e - d) (H ^ d) else 0 := by
  rw [mul_pow, coeff_X_pow_mul']

/-- Substituting into `exp` gives a *finite* sum of coefficients: only `d ≤ e`
contribute, because `x^d` divides `(x·H)^d`. -/
lemma coeff_subst_exp (H : ℚ⟦X⟧) (e : ℕ) :
    coeff e (subst (X * H) (exp ℚ))
      = ∑ d ∈ range (e + 1), (1 / (Nat.factorial d : ℚ)) * coeff e ((X * H) ^ d) := by
  rw [coeff_subst' (hasSubst_X_mul H)]
  rw [finsum_eq_sum_of_support_subset _ (s := range (e + 1))]
  · exact Finset.sum_congr rfl fun d _ => by simp [coeff_exp, smul_eq_mul]
  · intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    have hde : ¬ d ≤ e := by omega
    refine hd ?_
    rw [coeff_exp]
    have : coeff e ((X * H) ^ d) = 0 := by rw [coeff_X_mul_pow]; simp [hde]
    rw [this, smul_zero]

/-- The truncated exponential series, kept to `d ≤ m`. -/
def Sfin (H : ℚ⟦X⟧) (m : ℕ) : ℚ⟦X⟧ :=
  ∑ d ∈ range (m + 1), (1 / (Nat.factorial d : ℚ)) • ((X * H) ^ d)

lemma coeff_Sfin (H : ℚ⟦X⟧) (m e : ℕ) :
    coeff e (Sfin H m) = ∑ d ∈ range (m + 1), (1 / (Nat.factorial d : ℚ)) * coeff e ((X * H) ^ d) := by
  simp [Sfin, map_sum, smul_eq_mul]

/-- Below degree `m`, the truncation agrees with the genuine substitution. -/
lemma coeff_subst_exp_eq_Sfin (H : ℚ⟦X⟧) {m e : ℕ} (hem : e ≤ m) :
    coeff e (subst (X * H) (exp ℚ)) = coeff e (Sfin H m) := by
  rw [coeff_subst_exp, coeff_Sfin]
  refine Finset.sum_subset (by simpa using Nat.succ_le_succ hem) ?_
  intro d _ hd
  simp only [mem_range, not_lt] at hd
  have hde : ¬ d ≤ e := by omega
  rw [coeff_X_mul_pow]
  simp [hde]

/-- If two series agree in all degrees `≤ n`, multiplying by anything cannot change
degree-`n` coefficients. -/
lemma coeff_mul_congr_of_low {A B : ℚ⟦X⟧} (P : ℚ⟦X⟧) (n : ℕ)
    (h : ∀ e ≤ n, coeff e A = coeff e B) :
    coeff n (P * A) = coeff n (P * B) := by
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  rw [h p.2 (by omega)]

/-- **The bridge.** `bala` equals the explicit integer sum, cast to `ℚ`. -/
theorem bala_eq_Bint (W F G : ℤ⟦X⟧) (A M : ℕ → ℕ) (n : ℕ) :
    bala (toQ W) (toQ F) (toQ G) A M n = (Bint W F G A M n : ℚ) := by
  have hagree : ∀ e ≤ n, coeff e (subst (X * (toQ G) ^ M n) (exp ℚ))
      = coeff e (Sfin ((toQ G) ^ M n) n) := fun e he =>
    coeff_subst_exp_eq_Sfin _ he
  rw [bala, coeff_mul_congr_of_low _ n hagree]
  -- expand the finite truncation
  have hstep : coeff n (toQ W * (toQ F) ^ A n * Sfin ((toQ G) ^ M n) n)
      = ∑ d ∈ range (n + 1), (1 / (Nat.factorial d : ℚ))
          * coeff (n - d) (toQ W * (toQ F) ^ A n * ((toQ G) ^ M n) ^ d) := by
    rw [Sfin, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [mem_range] at hd
    have hdn : d ≤ n := by omega
    rw [mul_smul_comm, map_smul, smul_eq_mul]
    congr 1
    have h2 : toQ W * (toQ F) ^ A n * ((X * (toQ G) ^ M n) ^ d)
        = X ^ d * (toQ W * (toQ F) ^ A n * ((toQ G) ^ M n) ^ d) := by
      rw [mul_pow]; ring
    rw [h2, coeff_X_pow_mul']
    simp [hdn]
  rw [hstep, Finset.mul_sum]
  -- reindex d ↦ n - i and identify n!/d! with the falling factorial
  rw [Bint, Int.cast_sum]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  have hin : i ≤ n := by omega
  have hni : n - (n - i) = i := by omega
  have hfac : (Nat.factorial n : ℚ) * (1 / (Nat.factorial (n - i) : ℚ)) = (n.descFactorial i : ℚ) := by
    have h := Nat.factorial_mul_descFactorial hin
    have hne : (Nat.factorial (n - i) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    exact_mod_cast h.symm
  calc (Nat.factorial n : ℚ) * ((1 / (Nat.factorial (n - i) : ℚ)) * coeff (n - (n - i))
          (toQ W * (toQ F) ^ A n * ((toQ G) ^ M n) ^ (n - i)))
      = ((Nat.factorial n : ℚ) * (1 / (Nat.factorial (n - i) : ℚ))) * coeff i
          (toQ W * (toQ F) ^ A n * ((toQ G) ^ M n) ^ (n - i)) := by rw [hni]; ring
    _ = (n.descFactorial i : ℚ)
          * coeff i (toQ W * (toQ F) ^ A n * (toQ G) ^ (M n * (n - i))) := by
          rw [hfac, ← pow_mul]
    _ = (((n.descFactorial i : ℤ)
            * coeff i (W * F ^ A n * G ^ (M n * (n - i))) : ℤ) : ℚ) := by
          push_cast
          congr 1
          simp only [toQ, ← map_pow, ← map_mul, coeff_map]
          simp

/-! ## §3  Arithmetic helpers -/

/-- Falling factorial over `ℤ`. -/
def ff (x : ℤ) (i : ℕ) : ℤ := ∏ t ∈ range i, (x - (t : ℤ))

@[simp] lemma ff_zero (x : ℤ) : ff x 0 = 1 := by simp [ff]

lemma ff_succ (x : ℤ) (i : ℕ) : ff x (i + 1) = ff x i * (x - (i : ℤ)) := by
  simp [ff, prod_range_succ]

/-- The falling factorial is an integer polynomial, so it maps congruent arguments
to congruent values. -/
lemma ff_congr {k : ℕ} {x y : ℤ} (h : (k : ℤ) ∣ y - x) (i : ℕ) :
    (k : ℤ) ∣ ff y i - ff x i := by
  induction i with
  | zero => simp
  | succ i ih =>
      have key : ff y (i + 1) - ff x (i + 1)
          = (ff y i - ff x i) * (y - (i : ℤ)) + ff x i * (y - x) := by
        rw [ff_succ, ff_succ]; ring
      rw [key]
      exact dvd_add (dvd_mul_of_dvd_left ih _) (dvd_mul_of_dvd_right h _)

lemma ff_natCast (n : ℕ) (i : ℕ) : ff (n : ℤ) i = (n.descFactorial i : ℤ) := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [ff_succ, ih, Nat.descFactorial_succ]
      by_cases h : i ≤ n
      · have hc : ((n - i : ℕ) : ℤ) = (n : ℤ) - (i : ℤ) := Nat.cast_sub h
        push_cast [hc]; ring
      · have hlt : n < i := by omega
        simp [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]

lemma descFactorial_congr {k : ℕ} {a a' : ℕ}
    (h : (k : ℤ) ∣ (a' : ℤ) - (a : ℤ)) (i : ℕ) :
    (k : ℤ) ∣ (a'.descFactorial i : ℤ) - (a.descFactorial i : ℤ) := by
  rw [← ff_natCast a' i, ← ff_natCast a i]; exact ff_congr h i

lemma factorial_dvd_descFactorial_of_le (n i m : ℕ) (h : m ≤ i) :
    (Nat.factorial m : ℤ) ∣ (n.descFactorial i : ℤ) :=
  Int.natCast_dvd_natCast.mpr
    (dvd_trans (Nat.factorial_dvd_factorial h) (Nat.factorial_dvd_descFactorial n i))

lemma factorial_mul_choose (a m : ℕ) :
    (Nat.factorial m : ℤ) * (a.choose m : ℤ) = (a.descFactorial m : ℤ) := by
  have := Nat.descFactorial_eq_factorial_mul_choose a m
  exact_mod_cast this.symm

lemma dvd_mul_choose_sub {X : ℤ} {k m a a' : ℕ}
    (hX : (Nat.factorial m : ℤ) ∣ X)
    (hd : (k : ℤ) ∣ (a'.descFactorial m : ℤ) - (a.descFactorial m : ℤ)) :
    (k : ℤ) ∣ X * ((a'.choose m : ℤ) - (a.choose m : ℤ)) := by
  obtain ⟨u, hu⟩ := hX
  have expand : X * ((a'.choose m : ℤ) - (a.choose m : ℤ))
      = u * ((a'.descFactorial m : ℤ) - (a.descFactorial m : ℤ)) := by
    rw [hu, ← factorial_mul_choose a' m, ← factorial_mul_choose a m]; ring
  rw [expand]
  exact dvd_mul_of_dvd_right hd u

/-- `k ∣ (n+k)ᵢ` when `i > n`: the product `∏_{t<i}((n+k)-t)` contains the factor `k`. -/
theorem edge_term (n k i : ℕ) (hn : n < i) :
    (k : ℤ) ∣ ((n + k).descFactorial i : ℤ) := by
  rw [← ff_natCast]
  show (k : ℤ) ∣ ∏ t ∈ range i, (((n + k : ℕ) : ℤ) - (t : ℤ))
  have hdvd : (((n + k : ℕ) : ℤ) - (n : ℤ))
      ∣ ∏ t ∈ range i, (((n + k : ℕ) : ℤ) - (t : ℤ)) :=
    Finset.dvd_prod_of_mem _ (mem_range.mpr hn)
  have hval : (((n + k : ℕ) : ℤ) - (n : ℤ)) = (k : ℤ) := by push_cast; ring
  rwa [hval] at hdvd

/-! ## §4  Newton expansion of `coeff i (F^A * Z)` -/

/-- If `P` has zero constant term then `xʳ ∣ Pʳ`, so low coefficients of `Pʳ * Z` vanish. -/
lemma coeff_pow_mul_eq_zero {P : ℤ⟦X⟧} (hP : constantCoeff P = 0) (Z : ℤ⟦X⟧)
    {i r : ℕ} (h : i < r) : coeff i (P ^ r * Z) = 0 := by
  obtain ⟨c, hc⟩ : X ^ r ∣ P ^ r := pow_dvd_pow_of_dvd (X_dvd_iff.mpr hP) r
  rw [hc, mul_assoc, coeff_X_pow_mul']
  simp [Nat.not_le.mpr h]

/-- **Newton expansion.** `[xⁱ]((1+P)^A · Z)` is an integer combination of `C(A,r)`
for `r ≤ i`, with coefficients independent of `A`. -/
lemma coeff_one_add_pow_mul (P : ℤ⟦X⟧) (hP : constantCoeff P = 0) (Z : ℤ⟦X⟧) (A i : ℕ) :
    coeff i ((1 + P) ^ A * Z)
      = ∑ r ∈ range (i + 1), coeff i (P ^ r * Z) * (A.choose r : ℤ) := by
  have hexp : (1 + P) ^ A = ∑ r ∈ range (A + 1), (A.choose r : ℤ) • P ^ r := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [one_pow, mul_one, zsmul_eq_mul]
    push_cast
    ring
  have hA : coeff i ((1 + P) ^ A * Z)
      = ∑ r ∈ range (A + 1), coeff i (P ^ r * Z) * (A.choose r : ℤ) := by
    rw [hexp, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]
  rw [hA]
  -- both ranges agree once enlarged to `range (A + i + 1)`
  have hsub1 : range (A + 1) ⊆ range (A + i + 1) := by
    intro x hx; simp only [mem_range] at *; omega
  have hsub2 : range (i + 1) ⊆ range (A + i + 1) := by
    intro x hx; simp only [mem_range] at *; omega
  rw [Finset.sum_subset hsub1 ?_, Finset.sum_subset hsub2 ?_]
  · intro x _ hx
    simp only [mem_range, not_lt] at hx
    rw [coeff_pow_mul_eq_zero hP Z (by omega), zero_mul]
  · intro x _ hx
    simp only [mem_range, not_lt] at hx
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- Shifting the exponent `A` by a multiple of `k` changes `(n)ᵢ · [xⁱ]((1+P)^A · Z)`
only by a multiple of `k`. -/
lemma dvd_descFactorial_mul_coeff_sub {P : ℤ⟦X⟧} (hP : constantCoeff P = 0) (Z : ℤ⟦X⟧)
    (n i k A A' : ℕ) (hA : (k : ℤ) ∣ (A' : ℤ) - (A : ℤ)) :
    (k : ℤ) ∣ (n.descFactorial i : ℤ)
      * (coeff i ((1 + P) ^ A' * Z) - coeff i ((1 + P) ^ A * Z)) := by
  rw [coeff_one_add_pow_mul P hP Z A' i, coeff_one_add_pow_mul P hP Z A i,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.dvd_sum (fun r hr => ?_)
  simp only [mem_range] at hr
  have hri : r ≤ i := by omega
  have hrw : (n.descFactorial i : ℤ)
      * (coeff i (P ^ r * Z) * (A'.choose r : ℤ) - coeff i (P ^ r * Z) * (A.choose r : ℤ))
      = coeff i (P ^ r * Z)
        * ((n.descFactorial i : ℤ) * ((A'.choose r : ℤ) - (A.choose r : ℤ))) := by ring
  rw [hrw]
  exact dvd_mul_of_dvd_right
    (dvd_mul_choose_sub (factorial_dvd_descFactorial_of_le n i r hri)
      (descFactorial_congr hA r)) _

/-! ## §5  Shift-stable exponents -/

/-- An exponent function is *shift-stable* if `A (m+k) ≡ A m (mod k)` for all `m, k`.
Every polynomial with natural-number coefficients qualifies (see the closure lemmas),
and this is exactly what the proof consumes. -/
def ShiftStable (A : ℕ → ℕ) : Prop :=
  ∀ m k : ℕ, (k : ℤ) ∣ ((A (m + k) : ℤ) - (A m : ℤ))

lemma ShiftStable.const (c : ℕ) : ShiftStable (fun _ => c) := by
  intro m k; simp

lemma ShiftStable.id : ShiftStable (fun n => n) := by
  intro m k; exact ⟨1, by push_cast; ring⟩

lemma ShiftStable.add {A B : ℕ → ℕ} (hA : ShiftStable A) (hB : ShiftStable B) :
    ShiftStable (fun n => A n + B n) := by
  intro m k
  show (k : ℤ) ∣ ((A (m + k) + B (m + k) : ℕ) : ℤ) - ((A m + B m : ℕ) : ℤ)
  rw [Nat.cast_add, Nat.cast_add]
  have h : ((A (m + k) : ℤ) + (B (m + k) : ℤ)) - ((A m : ℤ) + (B m : ℤ))
      = ((A (m + k) : ℤ) - (A m : ℤ)) + ((B (m + k) : ℤ) - (B m : ℤ)) := by ring
  rw [h]
  exact dvd_add (hA m k) (hB m k)

/-- `k ∣ a' - a` and `k ∣ b' - b` imply `k ∣ a'b' - ab`. -/
lemma dvd_mul_sub {k : ℕ} {a a' b b' : ℤ}
    (ha : (k : ℤ) ∣ a' - a) (hb : (k : ℤ) ∣ b' - b) :
    (k : ℤ) ∣ a' * b' - a * b := by
  have h : a' * b' - a * b = (a' - a) * b' + a * (b' - b) := by ring
  rw [h]
  exact dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hb _)

lemma ShiftStable.mul {A B : ℕ → ℕ} (hA : ShiftStable A) (hB : ShiftStable B) :
    ShiftStable (fun n => A n * B n) := by
  intro m k
  show (k : ℤ) ∣ ((A (m + k) * B (m + k) : ℕ) : ℤ) - ((A m * B m : ℕ) : ℤ)
  rw [Nat.cast_mul, Nat.cast_mul]
  exact dvd_mul_sub (hA m k) (hB m k)

/-! ## §6  The congruence, and the end-to-end theorems -/

/-- The `i`-th block of `Bint`. -/
def Tint (W F G : ℤ⟦X⟧) (A M : ℕ → ℕ) (m i : ℕ) : ℤ :=
  (m.descFactorial i : ℤ) * coeff i (W * F ^ A m * G ^ (M m * (m - i)))

lemma Bint_eq_sum (W F G : ℤ⟦X⟧) (A M : ℕ → ℕ) (n : ℕ) :
    Bint W F G A M n = ∑ i ∈ range (n + 1), Tint W F G A M n i := rfl

/-- Each block is shift-stable mod `k`. Three things move, and each moves by a
multiple of `k`: the falling factorial, the `F`-exponent `A n`, and the `G`-exponent
`M n * (n - i)`. -/
lemma dvd_Tint_sub (W : ℤ⟦X⟧) {F G : ℤ⟦X⟧}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1)
    {A M : ℕ → ℕ} (hA : ShiftStable A) (hM : ShiftStable M)
    (n k i : ℕ) (hi : i ≤ n) :
    (k : ℤ) ∣ Tint W F G A M (n + k) i - Tint W F G A M n i := by
  set P := F - 1 with hPdef
  set Q := G - 1 with hQdef
  have hP : constantCoeff P = 0 := by simp [hPdef, hF]
  have hQ : constantCoeff Q = 0 := by simp [hQdef, hG]
  have hFP : F = 1 + P := by rw [hPdef]; ring
  have hGQ : G = 1 + Q := by rw [hQdef]; ring
  -- the F-exponent shift
  have hshiftA : (k : ℤ) ∣ ((A (n + k) : ℤ) - (A n : ℤ)) := hA n k
  -- the G-exponent shift: M n and (n - i) each shift by a multiple of k
  have hni : (k : ℤ) ∣ (((n + k - i : ℕ)) : ℤ) - (((n - i : ℕ)) : ℤ) := by
    have h1 : n + k - i = (n - i) + k := by omega
    refine ⟨1, ?_⟩
    rw [h1]; push_cast [Nat.cast_sub hi]; ring
  have hshiftB : (k : ℤ)
      ∣ ((M (n + k) * (n + k - i) : ℕ) : ℤ) - ((M n * (n - i) : ℕ) : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    exact dvd_mul_sub (hM n k) hni
  have hdf : (k : ℤ) ∣ ((n + k).descFactorial i : ℤ) - (n.descFactorial i : ℤ) :=
    descFactorial_congr (ShiftStable.id n k) i
  -- telescope: falling factorial, then the F-exponent, then the G-exponent
  set a := A n with hadef
  set a' := A (n + k) with ha'def
  set b := M n * (n - i) with hbdef
  set b' := M (n + k) * (n + k - i) with hb'def
  have key : Tint W F G A M (n + k) i - Tint W F G A M n i
      = (((n + k).descFactorial i : ℤ) - (n.descFactorial i : ℤ))
          * coeff i (W * F ^ a' * G ^ b')
        + (n.descFactorial i : ℤ)
          * (coeff i (W * F ^ a' * G ^ b') - coeff i (W * F ^ a * G ^ b'))
        + (n.descFactorial i : ℤ)
          * (coeff i (W * F ^ a * G ^ b') - coeff i (W * F ^ a * G ^ b)) := by
    simp only [Tint]; ring
  rw [key]
  refine dvd_add (dvd_add (dvd_mul_of_dvd_left hdf _) ?_) ?_
  · -- move the F-exponent; the prefactor W and the G-power ride along in `Z`
    have hF1 : ∀ c : ℕ, coeff i (W * F ^ c * G ^ b') = coeff i ((1 + P) ^ c * (W * G ^ b')) := by
      intro c; rw [← hFP]; ring_nf
    rw [hF1 a', hF1 a]
    exact dvd_descFactorial_mul_coeff_sub hP (W * G ^ b') n i k a a' hshiftA
  · -- move the G-exponent; now W and the F-power ride along
    have hG1 : ∀ c : ℕ, coeff i (W * F ^ a * G ^ c) = coeff i ((1 + Q) ^ c * (W * F ^ a)) := by
      intro c; rw [← hGQ]; ring_nf
    rw [hG1 b', hG1 b]
    exact dvd_descFactorial_mul_coeff_sub hQ (W * F ^ a) n i k b b' hshiftB

/-- **`Bint` satisfies the congruence.** -/
theorem Bint_shift (W : ℤ⟦X⟧) {F G : ℤ⟦X⟧}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1)
    {A M : ℕ → ℕ} (hA : ShiftStable A) (hM : ShiftStable M) (n k : ℕ) :
    (k : ℤ) ∣ Bint W F G A M (n + k) - Bint W F G A M n := by
  have hBn : Bint W F G A M n = ∑ i ∈ range (n + k + 1), Tint W F G A M n i := by
    rw [Bint_eq_sum]
    refine Finset.sum_subset (by intro x hx; simp only [mem_range] at *; omega) ?_
    intro x _ hx
    simp only [mem_range, not_lt] at hx
    simp [Tint, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : n < x)]
  rw [Bint_eq_sum, hBn, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum (fun i _ => ?_)
  by_cases hi : i ≤ n
  · exact dvd_Tint_sub W hF hG hA hM n k i hi
  · have hzero : Tint W F G A M n i = 0 := by
      simp [Tint, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : n < i)]
    rw [hzero, sub_zero, Tint]
    exact dvd_mul_of_dvd_left (edge_term n k i (by omega)) _

/-! ### §7  End-to-end theorems -/

/-- **MAIN THEOREM, formally verified end to end.**

Let `W, F, G` be power series with integer coefficients, with `F(0) = G(0) = 1`
(*no condition on* `W`), and let the exponent functions `A, M : ℕ → ℕ` be shift-stable
(e.g. any polynomial with natural-number coefficients). Then

  `b n = n ! * [xⁿ]( W * F^(A n) * exp(x * G^(M n)) )`

is integer valued and satisfies `b (n+k) ≡ b n (mod k)` for all `n, k`.

`bala` is defined directly from `PowerSeries.exp` and `PowerSeries.subst`; no step is
assumed. -/
theorem bala_congruence (W : ℤ⟦X⟧) {F G : ℤ⟦X⟧}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1)
    {A M : ℕ → ℕ} (hA : ShiftStable A) (hM : ShiftStable M) (n k : ℕ) :
    ∃ u v : ℤ,
      bala (toQ W) (toQ F) (toQ G) A M n = (u : ℚ) ∧
      bala (toQ W) (toQ F) (toQ G) A M (n + k) = (v : ℚ) ∧
      (k : ℤ) ∣ v - u :=
  ⟨Bint W F G A M n, Bint W F G A M (n + k),
    bala_eq_Bint W F G A M n, bala_eq_Bint W F G A M (n + k),
    Bint_shift W hF hG hA hM n k⟩

/-! ### The four OEIS conjectures, as corollaries

Each of the following is a verbatim instance of `bala_congruence`. The OEIS statements
are Peter Bala's, posted March 2023. -/

/-- **A361036** (Bala, 13 Mar 2023): *"let F(x) and G(x) denote power series with integer
coefficients with F(0) = G(0) = 1. Define b(n) = n! * [x^n] exp(x*G(x)^n)*F(x)^n. Then we
conjecture that b(n+k) == b(n) (mod k) for all n and k."* -/
theorem bala_congruence_A361036 {F G : ℤ⟦X⟧}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (n k : ℕ) :
    ∃ u v : ℤ,
      bala 1 (toQ F) (toQ G) (fun n => n) (fun n => n) n = (u : ℚ) ∧
      bala 1 (toQ F) (toQ G) (fun n => n) (fun n => n) (n + k) = (v : ℚ) ∧
      (k : ℤ) ∣ v - u := by
  have h := bala_congruence (1 : ℤ⟦X⟧) hF hG ShiftStable.id ShiftStable.id n k
  simpa [toQ] using h

/-- **A278070**, the general conjecture (Bala, 12 Mar 2023): *"let F(x) and G(x) denote
power series with integer coefficients with F(0) = G(0) = 1. Define
b(n) = n! * [x^n] exp(x*G(x))*F(x)^n."* Here `n` sits only in the prefactor: `M ≡ 1`. -/
theorem bala_congruence_A278070 {F G : ℤ⟦X⟧}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (n k : ℕ) :
    ∃ u v : ℤ,
      bala 1 (toQ F) (toQ G) (fun n => n) (fun _ => 1) n = (u : ℚ) ∧
      bala 1 (toQ F) (toQ G) (fun n => n) (fun _ => 1) (n + k) = (v : ℚ) ∧
      (k : ℤ) ∣ v - u := by
  have h := bala_congruence (1 : ℤ⟦X⟧) hF hG ShiftStable.id (ShiftStable.const 1) n k
  simpa [toQ] using h

/-- **A361281**, the general conjecture (Bala, 12 Mar 2023): *"Let F(x) and G(x) be power
series with integer coefficients with G(0) = 1. Define b(n) = n! * [x^n] F(x)*exp(x*G(x)^n)."*

Note there is **no** condition on `F(0)` here; that `F` is the unconstrained prefactor `W`
of the main theorem, with the constrained base taken to be `1`. -/
theorem bala_congruence_A361281 (W : ℤ⟦X⟧) {G : ℤ⟦X⟧}
    (hG : constantCoeff G = 1) (n k : ℕ) :
    ∃ u v : ℤ,
      bala (toQ W) 1 (toQ G) (fun _ => 0) (fun n => n) n = (u : ℚ) ∧
      bala (toQ W) 1 (toQ G) (fun _ => 0) (fun n => n) (n + k) = (v : ℚ) ∧
      (k : ℤ) ∣ v - u := by
  have h := bala_congruence W (F := 1) (by simp) hG
    (ShiftStable.const 0) ShiftStable.id n k
  simpa [toQ] using h

/-- **A293013** (Bala, 12 Mar 2023): `a(n) = n! * [x^n] exp(x/(1-x)^n)`, the case
`W = F = 1`, `M = id`. Stated here for a general `G` with `G(0) = 1`. -/
theorem bala_congruence_A293013 {G : ℤ⟦X⟧} (hG : constantCoeff G = 1) (n k : ℕ) :
    ∃ u v : ℤ,
      bala 1 1 (toQ G) (fun _ => 0) (fun n => n) n = (u : ℚ) ∧
      bala 1 1 (toQ G) (fun _ => 0) (fun n => n) (n + k) = (v : ℚ) ∧
      (k : ℤ) ∣ v - u := by
  have h := bala_congruence (1 : ℤ⟦X⟧) (F := 1) (by simp) hG
    (ShiftStable.const 0) ShiftStable.id n k
  simpa [toQ] using h

/-- Quadratic exponents are covered too, e.g. `A n = n²`: not previously posed. -/
theorem bala_congruence_sq {F G : ℤ⟦X⟧}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (n k : ℕ) :
    ∃ u v : ℤ,
      bala 1 (toQ F) (toQ G) (fun n => n * n) (fun n => n) n = (u : ℚ) ∧
      bala 1 (toQ F) (toQ G) (fun n => n * n) (fun n => n) (n + k) = (v : ℚ) ∧
      (k : ℤ) ∣ v - u := by
  have h := bala_congruence (1 : ℤ⟦X⟧) hF hG
    (ShiftStable.mul ShiftStable.id ShiftStable.id) ShiftStable.id n k
  simpa [toQ] using h

end

end ShiftStableExponents
