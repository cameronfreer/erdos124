/-
Copyright (c) 2025. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Claude Opus 4.5, GPT 5.1 Pro, GPT 5.2, Cameron Freer
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

/-!
# Erdős Problem 124 (Solved Variant)

This file contains the statement and proof of the "solved/weak" variant of Erdős Problem 124.
This variant, discussed at https://www.erdosproblems.com/forum/thread/124#post-1892, allows
using 1 = d^0 from each base. It is **not** the open BEGL96/gcd/k≥1 conjecture.

## Statement

Given k bases d(i) (each ≥ 2) such that ∑ᵢ 1/(d(i)-1) ≥ 1, every natural number n
can be written as a sum of k numbers a(i) where each a(i) uses only digits 0 and 1
in base d(i).

## Proof Strategy

**Special case:** If any base d_i = 2, use binary representation (trivial).

**Main case (all bases ≥ 3):** The density condition forces k ≥ 2 bases.

By strong induction on n:
- **n = 0:** Use a_i = 0 for all i.
- **n ≤ k:** Use n ones from n different bases (each d_i^0 = 1).
- **n > k:** Apply Brown's completeness machinery via `subset_sum_exists`.

**Brown's approach for n > k:**
1. Define P = {(i, e) : d_i^e ≤ n} with value function (i,e) ↦ d_i^e
2. The density condition ∑ 1/(d_i-1) ≥ 1 implies ∑_{p ∈ P} p.val ≥ n
   (`sum_powers_at_least`)
3. Sort P by value; this sequence satisfies Brown's step condition:
   each power v ≤ 1 + (sum of smaller powers), due to the density condition
   (`power_step_condition`)
4. Apply Brown's finite completeness lemma (`brown_achievable_range`) to find
   S ⊆ P with ∑ S = n
5. Group chosen powers by base index to get the final a_i values

## References

* [Erdős Problem 124](https://www.erdosproblems.com/124)
-/

open Finset BigOperators

/-- Helper: digits[i] = n / b^i % b for i < length -/
lemma digits_getElem_eq {b n i : ℕ} (hb : 1 < b) (hi : i < (Nat.digits b n).length) :
    (Nat.digits b n)[i] = n / b ^ i % b := by
  have hgetD := Nat.getD_digits n i (by omega : 2 ≤ b)
  simp only [List.getD_eq_getElem, hi] at hgetD
  exact hgetD

/-- A natural number uses only digits 0 and 1 in base `b` -/
def usesOnlyZeroOne (b n : ℕ) : Prop :=
  (Nat.digits b n).toFinset ⊆ {0, 1}

/-- Helper: 0 uses only digits 0 and 1 in any base -/
lemma usesOnlyZeroOne_zero (b : ℕ) : usesOnlyZeroOne b 0 := by
  simp [usesOnlyZeroOne, Nat.digits_zero]

/-- Helper: 1 uses only digits 0 and 1 in base ≥ 2 -/
lemma usesOnlyZeroOne_one {b : ℕ} (hb : 2 ≤ b) : usesOnlyZeroOne b 1 := by
  unfold usesOnlyZeroOne
  have h : Nat.digits b 1 = [1] := by
    rw [Nat.digits_eq_cons_digits_div (by omega : 1 < b) (by omega : (1 : ℕ) ≠ 0)]
    simp only [Nat.mod_eq_of_lt (by omega : 1 < b), Nat.div_eq_of_lt (by omega : 1 < b),
      Nat.digits_zero]
  simp [h]

/-- Powers of b use only digits 0 and 1 in base b -/
lemma usesOnlyZeroOne_pow {b : ℕ} (hb : 2 ≤ b) (e : ℕ) : usesOnlyZeroOne b (b ^ e) := by
  induction e with
  | zero => simp [usesOnlyZeroOne_one hb]
  | succ e ih =>
    unfold usesOnlyZeroOne at ih ⊢
    have h1 : 1 < b := by omega
    have hpos : 0 < b := by omega
    rw [pow_succ, Nat.digits_eq_cons_digits_div h1 (by positivity)]
    have hmod : b ^ e * b % b = 0 := by rw [mul_comm]; exact Nat.mul_mod_right b (b ^ e)
    have hdiv : b ^ e * b / b = b ^ e := by rw [mul_comm]; exact Nat.mul_div_right (b ^ e) hpos
    simp only [hmod, hdiv, List.toFinset_cons, insert_subset_iff, mem_insert, mem_singleton,
      true_or, true_and]
    exact ih

/-- Helper: the digits of b^e are e zeros followed by a 1 (for b ≥ 2) -/
lemma digits_pow {b : ℕ} (hb : 2 ≤ b) (e : ℕ) :
    Nat.digits b (b ^ e) = List.replicate e 0 ++ [1] := by
  have h1 : 1 < b := by omega
  induction e with
  | zero =>
    simp only [pow_zero, List.replicate_zero, List.nil_append]
    rw [Nat.digits_of_lt b 1 (by omega) h1]
  | succ e ih =>
    rw [pow_succ, mul_comm, Nat.digits_base_mul h1 (by positivity)]
    simp only [List.replicate_succ, List.cons_append, ih]

/-- Construct a digit list with 1s at positions in s, 0s elsewhere, up to length n -/
def indicatorList (s : Finset ℕ) (n : ℕ) : List ℕ :=
  (List.range n).map (fun i => if i ∈ s then 1 else 0)

/-- The indicator list has entries only 0 or 1 -/
lemma indicatorList_mem_zero_one (s : Finset ℕ) (n : ℕ) (x : ℕ)
    (hx : x ∈ indicatorList s n) : x = 0 ∨ x = 1 := by
  unfold indicatorList at hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨i, _, hi⟩ := hx
  split_ifs at hi <;> simp_all

/-- Sum of powers equals ofDigits of indicator list -/
lemma sum_pow_eq_ofDigits (b : ℕ) (s : Finset ℕ) (n : ℕ) (hn : ∀ e ∈ s, e < n) :
    ∑ e ∈ s, b ^ e = Nat.ofDigits b (indicatorList s n) := by
  unfold indicatorList
  induction n generalizing s with
  | zero =>
    simp only [List.range_zero, List.map_nil, Nat.ofDigits_nil]
    have : s = ∅ := by
      ext x
      simp only [Finset.notMem_empty, iff_false]
      intro hx
      exact Nat.not_lt_zero x (hn x hx)
    simp [this]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, Nat.ofDigits_append]
    simp only [List.length_map, List.length_range]
    -- Split s into elements < n and element = n (if present)
    by_cases hn_in : n ∈ s
    · -- Case: n ∈ s
      -- First prove the sum splits
      have hnotin : n ∉ s.filter (· < n) := by simp [Finset.mem_filter]
      have hsplit_set : s = insert n (s.filter (· < n)) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_filter]
        constructor
        · intro hx
          by_cases hxn : x = n
          · left; exact hxn
          · right; exact ⟨hx, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp (hn x hx)) hxn⟩
        · intro hx
          rcases hx with rfl | ⟨hx, _⟩
          · exact hn_in
          · exact hx
      have hsplit_sum : ∑ e ∈ s, b ^ e = b ^ n + ∑ e ∈ s.filter (· < n), b ^ e := by
        conv_lhs => rw [hsplit_set]
        rw [Finset.sum_insert hnotin]
      -- Show that indicator lists are equal for i < n
      have hlist_eq : (List.range n).map (fun i => if i ∈ s.filter (· < n) then 1 else 0) =
                      (List.range n).map (fun i => if i ∈ s then 1 else 0) := by
        apply List.map_congr_left
        intro i hi
        simp only [List.mem_range] at hi
        simp only [Finset.mem_filter]
        congr 1
        ext
        exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, hi⟩⟩
      have hih : ∀ e ∈ s.filter (· < n), e < n := by simp [Finset.mem_filter]
      rw [hsplit_sum, ih (s.filter (· < n)) hih, hlist_eq]
      simp only [hn_in, ↓reduceIte, Nat.ofDigits_singleton, mul_one, add_comm]
    · -- Case: n ∉ s
      have hsub : ∀ e ∈ s, e < n := fun e he =>
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp (hn e he)) (fun h => hn_in (h ▸ he))
      rw [ih s hsub]
      simp only [hn_in, ↓reduceIte, Nat.ofDigits_singleton, mul_zero, add_zero]

/-- Last element of a non-empty indicator list is the indicator of n-1 ∈ s -/
lemma indicatorList_getLast {s : Finset ℕ} {n : ℕ} (hn : 0 < n)
    (hne : indicatorList s n ≠ []) :
    (indicatorList s n).getLast hne = if n - 1 ∈ s then 1 else 0 := by
  unfold indicatorList at hne ⊢
  rw [List.getLast_eq_getElem]
  rw [List.getElem_map]
  simp only [List.length_map, List.length_range]
  have hlen : n - 1 < (List.range n).length := by simp [List.length_range]; omega
  have h : (List.range n)[n - 1] = n - 1 := List.getElem_range hlen
  simp only [h]

/-- Sum of distinct powers of b uses only 0,1 digits -/
lemma usesOnlyZeroOne_sum_distinct_powers {b : ℕ} (hb : 2 ≤ b)
    (s : Finset ℕ) : usesOnlyZeroOne b (∑ e ∈ s, b ^ e) := by
  classical
  -- Use indicatorList with length = max element + 1
  by_cases hs : s = ∅
  · simp [hs, usesOnlyZeroOne_zero]
  · have hmax : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
    set n := s.sup id + 1 with hn_def
    have hn : ∀ e ∈ s, e < n := fun e he => by
      have : e ≤ s.sup id := Finset.le_sup (f := id) he
      omega
    rw [sum_pow_eq_ofDigits b s n hn]
    -- Now show digits (ofDigits b (indicatorList s n)) ⊆ {0, 1}
    unfold usesOnlyZeroOne
    have h1 : 1 < b := by omega
    have hn_pos : 0 < n := by omega
    have hdigits : Nat.digits b (Nat.ofDigits b (indicatorList s n)) = indicatorList s n ∨
                   Nat.digits b (Nat.ofDigits b (indicatorList s n)) = [] := by
      by_cases hnil : indicatorList s n = []
      · right
        simp [hnil, Nat.ofDigits_nil, Nat.digits_zero]
      · left
        apply Nat.digits_ofDigits b h1
        · intro l hl
          have := indicatorList_mem_zero_one s n l hl
          omega
        · intro hne
          rw [indicatorList_getLast hn_pos hne]
          have : n - 1 ∈ s := by
            -- n = s.sup id + 1, so n - 1 = s.sup id
            -- s.sup id ∈ s for nonempty s
            rw [hn_def]
            simp only [add_tsub_cancel_right]
            have := Finset.exists_mem_eq_sup s hmax id
            obtain ⟨y, hy, hysup⟩ := this
            simp only [id_eq] at hysup
            rw [hysup]
            exact hy
          simp [this]
    rcases hdigits with hdigits | hdigits
    · rw [hdigits]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have := indicatorList_mem_zero_one s n x (List.mem_toFinset.mp hx)
      tauto
    · simp [hdigits]

/-- The count of 1s in the base-b representation -/
def countOnes (b n : ℕ) : ℕ := (Nat.digits b n).count 1

/-- The largest exponent e such that b^e ≤ n -/
def largestExp (b n : ℕ) : ℕ := (Nat.digits b n).length - 1

/-- For n > 0 and b ≥ 2, b^(largestExp b n) ≤ n -/
lemma pow_largestExp_le {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) :
    b ^ (largestExp b n) ≤ n := by
  unfold largestExp
  have h1 : 1 < b := by omega
  have hne : n ≠ 0 := hn.ne'
  have hlen : 0 < (Nat.digits b n).length := by
    rw [List.length_pos_iff_ne_nil]
    exact Nat.digits_ne_nil_iff_ne_zero.mpr hne
  have hle := Nat.base_pow_length_digits_le b n h1 hne
  have hpow : b ^ (Nat.digits b n).length = b ^ ((Nat.digits b n).length - 1 + 1) := by
    congr 1; omega
  rw [hpow, pow_succ] at hle
  have hb_pos : 0 < b := by omega
  calc b ^ ((Nat.digits b n).length - 1) ≤ b ^ ((Nat.digits b n).length - 1) * b / b := by
         rw [Nat.mul_div_cancel _ hb_pos]
       _ ≤ b * n / b := Nat.div_le_div_right hle
       _ = n := Nat.mul_div_cancel_left n hb_pos

/-- For n > 0 and b ≥ 2, n < b^(largestExp b n + 1) -/
lemma lt_pow_largestExp_succ {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) :
    n < b ^ (largestExp b n + 1) := by
  unfold largestExp
  have h1 : 1 < b := by omega
  have hne : n ≠ 0 := hn.ne'
  have hlen : 0 < (Nat.digits b n).length := by
    rw [List.length_pos_iff_ne_nil]
    exact Nat.digits_ne_nil_iff_ne_zero.mpr hne
  have hlt : n < b ^ (Nat.digits b n).length := Nat.lt_base_pow_length_digits h1
  calc n < b ^ (Nat.digits b n).length := hlt
       _ = b ^ ((Nat.digits b n).length - 1 + 1) := by congr 1; omega

/-- Capacity lemma: The total capacity (sum of all powers up to largestExp) is at least n.
This follows from the density condition ∑ 1/(d_i-1) ≥ 1. -/
lemma capacity_lemma {k : ℕ} {d : Fin k → ℕ} (hd : ∀ i, 2 ≤ d i)
    (hsum : 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1))
    {n : ℕ} (hn : 0 < n) :
    (n : ℚ) ≤ ∑ i : Fin k, ((d i) ^ (largestExp (d i) n + 1) - 1 : ℚ) / ((d i) - 1) := by
  -- Each term equals the geometric series sum: 1 + d_i + d_i^2 + ... + d_i^{e_i}
  -- Since d_i^{e_i+1} > n, each term is > n/(d_i - 1)
  -- So the total is ≥ n * ∑ 1/(d_i - 1) ≥ n
  have h1 : ∀ i, (n : ℚ) / ((d i : ℚ) - 1) ≤
      ((d i) ^ (largestExp (d i) n + 1) - 1 : ℚ) / ((d i : ℚ) - 1) := by
    intro i
    have hdi : 2 ≤ d i := hd i
    have hd_pos : 0 < (d i : ℚ) - 1 := by
      have : 1 < d i := by omega
      simp only [sub_pos, Nat.one_lt_cast, this]
    apply div_le_div_of_nonneg_right _ (le_of_lt hd_pos)
    have hlt := lt_pow_largestExp_succ hdi hn
    -- n < d^{e+1} in ℕ means n ≤ d^{e+1} - 1 in ℕ
    have hpow_ge_one : 1 ≤ (d i) ^ (largestExp (d i) n + 1) :=
      Nat.one_le_pow _ _ (by omega : 0 < d i)
    have hle : n ≤ (d i) ^ (largestExp (d i) n + 1) - 1 := by omega
    -- Cast to ℚ
    have hpow_pos : 0 < (d i) ^ (largestExp (d i) n + 1) := by positivity
    calc (n : ℚ) ≤ ((d i) ^ (largestExp (d i) n + 1) - 1 : ℕ) := by exact_mod_cast hle
      _ = (d i : ℚ) ^ (largestExp (d i) n + 1) - 1 := by
          rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega : 0 < d i))]
          simp [Nat.cast_pow]
  have h2 : ∀ i, (1 : ℚ) / ((d i : ℚ) - 1) = 1 / (d i - 1 : ℚ) := fun i => rfl
  calc (n : ℚ) = n * 1 := by ring
    _ ≤ n * ∑ i : Fin k, (1 : ℚ) / (d i - 1) := by
        have hn' : (0 : ℚ) ≤ n := Nat.cast_nonneg n
        nlinarith
    _ = ∑ i : Fin k, n * (1 / ((d i : ℚ) - 1)) := by rw [Finset.mul_sum]
    _ = ∑ i : Fin k, (n : ℚ) / ((d i : ℚ) - 1) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ ≤ ∑ i : Fin k, ((d i) ^ (largestExp (d i) n + 1) - 1 : ℚ) / ((d i : ℚ) - 1) := by
        apply Finset.sum_le_sum
        intro i _
        exact h1 i

/-- Every natural number uses only digits 0 and 1 in base 2 (binary representation) -/
lemma usesOnlyZeroOne_base2 (n : ℕ) : usesOnlyZeroOne 2 n := by
  unfold usesOnlyZeroOne
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have h := Nat.digits_lt_base (by omega : 1 < 2) (List.mem_toFinset.mp hx)
  omega

/-!
## Brown's Completeness Lemma

A key tool: if a nondecreasing sequence `a` satisfies `a(n+1) ≤ 1 + ∑_{i≤n} a(i)`,
then every natural number is representable as a finite subset sum of the sequence.
-/

/-- Partial sum of the first n terms (indices 0 to n-1) -/
def partialSum (a : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, a i

/-- Brown's completeness lemma (finite version):
The set of achievable subset sums from {a(0), ..., a(n-1)} is exactly
{0, 1, ..., partialSum a n} when the step condition holds. -/
lemma brown_achievable_range (a : ℕ → ℕ) (h0 : a 0 = 1)
    (hstep : ∀ m, a (m + 1) ≤ 1 + partialSum a (m + 1)) :
    ∀ n, ∀ k ≤ partialSum a n,
      ∃ s : Finset ℕ, (∀ i ∈ s, i < n) ∧ ∑ i ∈ s, a i = k := by
  intro n
  induction n with
  | zero =>
    intro k hk
    simp only [partialSum, Finset.range_zero, Finset.sum_empty, Nat.le_zero] at hk
    subst hk
    exact ⟨∅, by simp, by simp⟩
  | succ n ih =>
    intro k hk
    -- partialSum a (n+1) = partialSum a n + a n
    have hsum_succ : partialSum a (n + 1) = partialSum a n + a n := by
      simp only [partialSum, Finset.sum_range_succ]
    by_cases hk_small : k ≤ partialSum a n
    · -- k is achievable from first n terms
      obtain ⟨s, hs_bound, hs_sum⟩ := ih k hk_small
      exact ⟨s, fun i hi => Nat.lt_succ_of_lt (hs_bound i hi), hs_sum⟩
    · -- k > partialSum a n, so we need to use a n
      push_neg at hk_small
      have hk_bound : k - a n ≤ partialSum a n := by
        rw [hsum_succ] at hk
        omega
      -- k - a n is achievable from first n terms
      obtain ⟨s, hs_bound, hs_sum⟩ := ih (k - a n) hk_bound
      have hn_notin : n ∉ s := fun h => Nat.lt_irrefl n (hs_bound n h)
      use insert n s
      constructor
      · intro i hi
        simp only [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (hs_bound i hi)
      · rw [Finset.sum_insert hn_notin, hs_sum]
        have han_le : a n ≤ k := by
          -- From step condition: a n ≤ 1 + partialSum a n < k + 1 (since k > partialSum a n)
          have hstep_n : a n ≤ 1 + partialSum a n := by
            have := hstep (n - 1)
            cases n with
            | zero => simp [h0, partialSum]
            | succ n' =>
              simp only [Nat.succ_sub_one] at this
              exact this
          omega
        omega

/-- Brown's completeness lemma: every natural number is a finite subset sum -/
theorem brown_complete (a : ℕ → ℕ) (h0 : a 0 = 1)
    (hpos : ∀ n, 0 < a n)  -- Need positivity assumption
    (hstep : ∀ m, a (m + 1) ≤ 1 + partialSum a (m + 1)) :
    ∀ N, ∃ s : Finset ℕ, ∑ i ∈ s, a i = N := by
  intro N
  -- Find n large enough that partialSum a n ≥ N
  have hgrows : ∀ n, n ≤ partialSum a n := by
    intro n
    induction n with
    | zero => simp [partialSum]
    | succ n ih =>
      have hsum_succ : partialSum a (n + 1) = partialSum a n + a n := by
        simp only [partialSum, Finset.sum_range_succ]
      have han_pos : 0 < a n := hpos n
      omega
  have hN_le : N ≤ partialSum a N := hgrows N
  obtain ⟨s, _, hs_sum⟩ := brown_achievable_range a h0 hstep N N hN_le
  exact ⟨s, hs_sum⟩

/-!
## Global Power Enumeration

For the Brown-based proof, we enumerate all powers d(i)^e across all bases in nondecreasing order.
-/

/-- A power from one of our bases: (base index, exponent) -/
@[ext]
structure BasePower (k : ℕ) where
  idx : Fin k
  exp : ℕ
  deriving DecidableEq

/-- The value of a base power given the bases -/
def BasePower.val {k : ℕ} (d : Fin k → ℕ) (p : BasePower k) : ℕ :=
  d p.idx ^ p.exp

/-- All powers up to value bound M: { (i, e) : d(i)^e ≤ M } -/
def powersUpTo (k : ℕ) (d : Fin k → ℕ) (M : ℕ) : Finset (BasePower k) :=
  (Finset.univ (α := Fin k) ×ˢ Finset.range (M + 1)).filter (fun p => d p.1 ^ p.2 ≤ M)
    |>.map ⟨fun p => ⟨p.1, p.2⟩, fun _ _ h => by
      simp only [BasePower.mk.injEq] at h; ext <;> simp [h.1, h.2]⟩

/-- Geometric series formula in ℚ: (d^(e+1) - 1)/(d-1) = ∑_{j=0}^{e} d^j -/
lemma geom_series_eq_sum (d : ℕ) (_hd : 2 ≤ d) (e : ℕ) :
    ((d : ℚ) ^ (e + 1) - 1) / ((d : ℚ) - 1) =
      ∑ j ∈ Finset.range (e + 1), (d : ℚ) ^ j := by
  have hd_ne_one : (d : ℚ) ≠ 1 := by
    have : (1 : ℕ) < d := by omega
    exact_mod_cast (ne_of_gt this)
  have hd1 : (d : ℚ) - 1 ≠ 0 := by
    linarith [show (1 : ℚ) < d from by exact_mod_cast (by omega : 1 < d)]
  have hgeom := geom_sum_eq hd_ne_one (e + 1)
  -- hgeom : ∑ i ∈ range (e+1), d^i = (d^(e+1) - 1) / (d - 1)
  rw [hgeom]

/-- Each power d^j with j ≤ largestExp is ≤ n -/
lemma pow_le_of_le_largestExp {d n j : ℕ} (hd : 2 ≤ d) (hn : 0 < n)
    (hj : j ≤ largestExp d n) : d ^ j ≤ n := by
  have hle := pow_largestExp_le hd hn
  calc d ^ j ≤ d ^ largestExp d n := Nat.pow_le_pow_right (by omega : 1 ≤ d) hj
       _ ≤ n := hle

/-- Membership criterion for powersUpTo -/
lemma mem_powersUpTo_iff {k : ℕ} {d : Fin k → ℕ} {M : ℕ} (p : BasePower k) :
    p ∈ powersUpTo k d M ↔ d p.idx ^ p.exp ≤ M ∧ p.exp ≤ M := by
  unfold powersUpTo
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    Finset.mem_range, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨i, e⟩, ⟨he_range, hpow⟩, heq⟩
    cases p with | mk idx exp =>
    simp only [BasePower.mk.injEq] at heq
    obtain ⟨hi, he⟩ := heq
    subst hi he
    exact ⟨hpow, Nat.lt_succ_iff.mp he_range⟩
  · intro ⟨hpow, he_range⟩
    exact ⟨⟨p.idx, p.exp⟩, ⟨Nat.lt_succ_of_le he_range, hpow⟩, by simp⟩

/-- The ones in powersUpTo: elements (i, 0) with value 1 -/
def onesInP (k : ℕ) (_d : Fin k → ℕ) (_M : ℕ) : Finset (BasePower k) :=
  (Finset.univ : Finset (Fin k)).map
    ⟨fun i => ⟨i, 0⟩, fun _ _ h => by simp [BasePower.ext_iff] at h; exact h⟩

lemma onesInP_subset {k : ℕ} {d : Fin k → ℕ} {M : ℕ} (hM : 0 < M) :
    onesInP k d M ⊆ powersUpTo k d M := by
  intro p hp
  simp only [onesInP, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk] at hp
  obtain ⟨i, hi⟩ := hp
  rw [← hi, mem_powersUpTo_iff]
  simp only [pow_zero]
  exact ⟨hM, Nat.zero_le M⟩

lemma onesInP_card {k : ℕ} {d : Fin k → ℕ} {M : ℕ} :
    (onesInP k d M).card = k := by
  simp only [onesInP, Finset.card_map, Finset.card_univ, Fintype.card_fin]

lemma onesInP_sum {k : ℕ} {d : Fin k → ℕ} {M : ℕ} :
    ∑ p ∈ onesInP k d M, p.val d = k := by
  simp only [onesInP, Finset.sum_map, Function.Embedding.coeFn_mk, BasePower.val, pow_zero]
  simp

/-!
## Brown-Based Subset Sum

We use Brown's completeness lemma to show that any N ≤ total sum is achievable.
The key is that powers listed in nondecreasing order satisfy the step condition:
each power is ≤ 1 + sum of all smaller powers.
-/

/-- The density condition implies min base ≤ k + 1 -/
lemma density_key' {k : ℕ} {d : Fin k → ℕ} (_hd : ∀ i, 2 ≤ d i) (hk : 2 ≤ k)
    (hsum : 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1)) :
    ∃ i : Fin k, d i ≤ k + 1 := by
  -- Same as density_key but with explicit bound
  by_contra h
  push_neg at h
  have hall_large : ∀ i : Fin k, d i ≥ k + 2 := fun i => Nat.lt_iff_add_one_le.mp (h i)
  have hbound : ∀ i : Fin k, (1 : ℚ) / (d i - 1) ≤ 1 / (k + 1) := by
    intro i
    have hdi : d i ≥ k + 2 := hall_large i
    have hpos : (0 : ℚ) < k + 1 := by positivity
    have hge : (d i : ℚ) - 1 ≥ k + 1 := by
      have : (k + 2 : ℕ) ≤ d i := hdi
      have h1 : (k + 2 : ℚ) ≤ (d i : ℚ) := by exact_mod_cast this
      linarith
    exact one_div_le_one_div_of_le hpos hge
  have htotal : ∑ i : Fin k, (1 : ℚ) / (d i - 1) ≤ k * (1 / (k + 1)) := by
    calc ∑ i : Fin k, (1 : ℚ) / (d i - 1)
        ≤ ∑ _i : Fin k, (1 : ℚ) / (k + 1) := Finset.sum_le_sum (fun i _ => hbound i)
      _ = k * (1 / (k + 1)) := by simp [Finset.sum_const]
  have hlt : k * (1 / (k + 1 : ℚ)) < 1 := by
    have hk_pos : (0 : ℚ) < k + 1 := by positivity
    rw [mul_one_div, div_lt_one hk_pos]
    exact_mod_cast (Nat.lt_succ_self k)
  linarith

/-- If the minimal base is k+1, it cannot be unique (density forces a duplicate). -/
lemma density_duplicate_when_max {k : ℕ} {d : Fin k → ℕ} (hd : ∀ i, 2 ≤ d i)
    (hk : 2 ≤ k) (hsum : 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1)) (i₀ : Fin k)
    (hi₀_eq : d i₀ = k + 1) (hi₀_min : ∀ j, d i₀ ≤ d j) :
    ∃ j : Fin k, j ≠ i₀ ∧ d j = k + 1 := by
  -- If d i₀ = k + 1 is the unique minimum, the density sum < 1, contradiction
  by_contra h
  push_neg at h
  -- All other bases j ≠ i₀ have d_j ≠ k + 1, so d_j ≥ k + 2 (since d i₀ = k + 1 is min)
  have hothers : ∀ j, j ≠ i₀ → d j ≥ k + 2 := by
    intro j hj
    have hne : d j ≠ k + 1 := h j hj
    have hge : d j ≥ d i₀ := hi₀_min j
    rw [hi₀_eq] at hge
    omega
  -- i₀ contributes 1/k
  have hi₀_contrib : (1 : ℚ) / (d i₀ - 1) = 1 / k := by
    rw [hi₀_eq]; simp
  -- Each other base contributes ≤ 1/(k+1)
  have hother_contrib : ∀ j, j ≠ i₀ → (1 : ℚ) / (d j - 1) ≤ 1 / (k + 1) := by
    intro j hj
    have hge : d j ≥ k + 2 := hothers j hj
    have hpos : (0 : ℚ) < k + 1 := by positivity
    have hcast : (d j : ℚ) - 1 ≥ k + 1 := by
      have : (k + 2 : ℕ) ≤ d j := hge
      have h1 : (k + 2 : ℚ) ≤ (d j : ℚ) := by exact_mod_cast this
      linarith
    exact one_div_le_one_div_of_le hpos hcast
  -- Total sum ≤ 1/k + (k-1)/(k+1) < 1 for k ≥ 2
  -- i₀ contributes 1/k, each other j ≠ i₀ contributes ≤ 1/(k+1) (since d j ≥ k + 2)
  -- Total ≤ 1/k + (k-1)/(k+1) = (k² + 1)/(k² + k) < 1 for k ≥ 2
  -- Proof: (k² + 1)/(k² + k) < 1 ⟺ k² + 1 < k² + k ⟺ 1 < k ✓
  have htotal_lt : ∑ i : Fin k, (1 : ℚ) / (d i - 1) < 1 := by
    -- Split sum: i₀ contributes 1/k, others each contribute ≤ 1/(k+1)
    have hsplit := Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i₀)
           (f := fun i : Fin k => (1 : ℚ) / (d i - 1))
    rw [hsplit]
    -- Sum ≤ 1/k + (k-1)/(k+1) < 1
    have hcard : (Finset.univ \ {i₀} : Finset (Fin k)).card = k - 1 := by
      simp [Finset.card_sdiff, Finset.singleton_inter_of_mem (Finset.mem_univ i₀),
        Fintype.card_fin]
    calc 1 / (d i₀ - 1) + ∑ j ∈ Finset.univ \ {i₀}, (1 : ℚ) / (d j - 1)
        = 1 / k + ∑ j ∈ Finset.univ \ {i₀}, (1 : ℚ) / (d j - 1) := by rw [hi₀_contrib]
      _ ≤ 1 / k + ∑ _j ∈ Finset.univ \ {i₀}, (1 : ℚ) / (k + 1) := by
          gcongr with j hj
          simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hj
          -- Need to show (k : ℚ) + 1 ≤ (d j : ℚ) - 1
          have hge := hothers j hj
          have h1 : (k + 2 : ℕ) ≤ d j := hge
          have h2 : (k + 2 : ℚ) ≤ (d j : ℚ) := by exact_mod_cast h1
          have hd_pos : 2 ≤ d j := hd j
          have h3 : (d j : ℚ) - 1 ≥ 1 := by
            have : (2 : ℕ) ≤ d j := hd_pos
            have h4 : (2 : ℚ) ≤ (d j : ℚ) := by exact_mod_cast this
            linarith
          linarith
      _ = 1 / k + (k - 1) / (k + 1) := by
          rw [Finset.sum_const, hcard]
          simp only [nsmul_eq_mul]
          rw [Nat.cast_sub (by omega : 1 ≤ k)]
          ring
      _ < 1 := by
          have hk_pos : (0 : ℚ) < k := by positivity
          have hk1_pos : (0 : ℚ) < k + 1 := by positivity
          have hkk1_pos : (0 : ℚ) < k * (k + 1) := by positivity
          rw [div_add_div _ _ (ne_of_gt hk_pos) (ne_of_gt hk1_pos)]
          rw [div_lt_one hkk1_pos]
          have hk2 : (k : ℚ) ≥ 2 := by exact_mod_cast hk
          ring_nf
          -- Need: k² + 1 < k² + k, i.e., 1 < k
          nlinarith
  linarith

/-- Either the minimal base is ≤ k (can use ones), or there's a duplicate (can use other base) -/
lemma density_small_or_dup {k : ℕ} {d : Fin k → ℕ} (hd : ∀ i, 2 ≤ d i) (hk : 2 ≤ k)
    (hsum : 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1)) (i₀ : Fin k) (hi₀ : d i₀ ≤ k + 1)
    (hi₀_min : ∀ j, d i₀ ≤ d j) :
    d i₀ ≤ k ∨ ∃ j : Fin k, j ≠ i₀ ∧ d j = d i₀ := by
  by_cases hle : d i₀ ≤ k
  · left; exact hle
  · right
    push_neg at hle
    have heq : d i₀ = k + 1 := by omega
    obtain ⟨j, hj_ne, hj_eq⟩ := density_duplicate_when_max hd hk hsum i₀ heq hi₀_min
    exact ⟨j, hj_ne, by rw [heq]; exact hj_eq⟩

/-- The sum of all powers ≤ T is at least T (from density condition).
    This is the key insight: the density ∑ 1/(d_i - 1) ≥ 1 ensures powers "cover" all values. -/
lemma sum_powers_at_least {k : ℕ} {d : Fin k → ℕ} (hd : ∀ i, 2 ≤ d i)
    (hsum : 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1)) (T : ℕ) (hT : 0 < T) :
    T ≤ ∑ p ∈ powersUpTo k d T, p.val d := by
  -- Capacity argument (geometric series + density bound).
  -- For each base i, sum of powers d_i^0 + ... + d_i^{e_i} ≥ T/(d_i - 1)
  -- where e_i = largestExp(d_i, T). Summing: total ≥ T * ∑ 1/(d_i - 1) ≥ T
  have hcap : (T : ℚ) ≤
      ∑ i : Fin k, ((d i) ^ (largestExp (d i) T + 1) - 1 : ℚ) / ((d i) - 1) :=
    capacity_lemma hd hsum hT
  have hcap' : (T : ℚ) ≤
      ∑ i : Fin k, ∑ j ∈ Finset.range (largestExp (d i) T + 1), (d i : ℚ) ^ j := by
    calc (T : ℚ) ≤ ∑ i, ((d i) ^ (largestExp (d i) T + 1) - 1 : ℚ) / ((d i) - 1) := hcap
      _ = ∑ i, ∑ j ∈ Finset.range (largestExp (d i) T + 1), (d i : ℚ) ^ j := by
          apply Finset.sum_congr rfl; intro i _
          exact geom_series_eq_sum (d i) (hd i) (largestExp (d i) T)
  -- Each power d i ^ j with j ≤ largestExp is in powersUpTo k d T
  have hP_contains : ∀ i : Fin k, ∀ j ∈ Finset.range (largestExp (d i) T + 1),
      ⟨i, j⟩ ∈ powersUpTo k d T := by
    intro i j hj
    simp only [Finset.mem_range] at hj
    have hj_le : j ≤ largestExp (d i) T := Nat.lt_succ_iff.mp hj
    have hpow_le := pow_le_of_le_largestExp (hd i) hT hj_le
    rw [mem_powersUpTo_iff]
    constructor
    · exact hpow_le
    · have hd_ge_2 : d i ≥ 2 := hd i
      calc j ≤ largestExp (d i) T := hj_le
           _ ≤ d i ^ largestExp (d i) T := by
               cases' Nat.eq_zero_or_pos (largestExp (d i) T) with hzero hpos
               · simp [hzero]
               · exact Nat.le_of_lt (Nat.lt_pow_self (by omega : 1 < d i))
           _ ≤ T := pow_largestExp_le (hd i) hT
  -- Sum over (i, j) pairs ≤ sum over powersUpTo
  have hle_sum : (∑ i : Fin k, ∑ j ∈ Finset.range (largestExp (d i) T + 1), d i ^ j : ℕ) ≤
      ∑ p ∈ powersUpTo k d T, p.val d := by
    let S := Finset.univ.sigma (fun i : Fin k => Finset.range (largestExp (d i) T + 1))
    have hinj : ∀ x ∈ S, (⟨x.1, x.2⟩ : BasePower k) ∈ powersUpTo k d T := by
      intro ⟨i, j⟩ hx
      simp only [S, Finset.mem_sigma, Finset.mem_univ, true_and] at hx
      exact hP_contains i j hx
    have hsum_eq : ∑ i : Fin k, ∑ j ∈ Finset.range (largestExp (d i) T + 1), d i ^ j =
        ∑ x ∈ S, d x.1 ^ x.2 := by rw [Finset.sum_sigma]
    rw [hsum_eq]
    let f : ((_ : Fin k) × ℕ) → BasePower k := fun x => ⟨x.1, x.2⟩
    let S' := S.image f
    have hf_inj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y := by
      intro ⟨i1, j1⟩ _ ⟨i2, j2⟩ _ hxy
      simp only [f, BasePower.mk.injEq] at hxy
      simp [hxy.1, hxy.2]
    have hS'_sub : S' ⊆ powersUpTo k d T := by
      intro p hp
      simp only [S', Finset.mem_image] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      exact hinj x hx
    have hsum_S_S' : ∑ x ∈ S, d x.1 ^ x.2 = ∑ p ∈ S', p.val d := by
      rw [Finset.sum_image]
      · simp only [f, BasePower.val]
      · intro x hx y hy hxy; exact hf_inj x hx y hy hxy
    rw [hsum_S_S']
    exact Finset.sum_le_sum_of_subset hS'_sub
  -- Combine
  have hnat_eq : (∑ i : Fin k, ∑ j ∈ Finset.range (largestExp (d i) T + 1), d i ^ j : ℕ) =
      (∑ i : Fin k, ∑ j ∈ Finset.range (largestExp (d i) T + 1), (d i : ℚ) ^ j : ℚ) := by
    push_cast; rfl
  have hT_le_nat :
      T ≤ ∑ i : Fin k, ∑ j ∈ Finset.range (largestExp (d i) T + 1), d i ^ j := by
    rw [← hnat_eq] at hcap'; exact_mod_cast hcap'
  exact Nat.le_trans hT_le_nat hle_sum

/-- Key step condition for Brown's lemma: any power v ≤ 1 + sum of smaller powers.
    This follows from the density condition which ensures enough small powers exist. -/
lemma power_step_condition {k : ℕ} {d : Fin k → ℕ} (hd : ∀ i, 2 ≤ d i) (_hk : 2 ≤ k)
    (hsum : 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1))
    {n : ℕ} (_hn : 0 < n) (v : ℕ) (hv_pos : 0 < v) (hv_le : v ≤ n)
    (_hv_in : ∃ p ∈ powersUpTo k d n, p.val d = v) :
    v ≤ 1 + ∑ p ∈ (powersUpTo k d n).filter (fun q => q.val d < v), p.val d := by
  -- Case v = 1: sum of powers < 1 is 0, so 1 ≤ 1 + 0 ✓
  by_cases hv1 : v = 1
  · subst hv1; simp
  -- Case v > 1: use sum_powers_at_least with T = v - 1
  have hv_ge_2 : 2 ≤ v := by omega
  have hvm1_pos : 0 < v - 1 := by omega
  -- Sum of all powers ≤ (v-1) is ≥ (v-1)
  have hkey := sum_powers_at_least hd hsum (v - 1) hvm1_pos
  -- Powers in powersUpTo k d (v-1) are a subset of powers in powersUpTo k d n with value < v
  have hsubset : powersUpTo k d (v - 1) ⊆ (powersUpTo k d n).filter (fun q => q.val d < v) := by
    intro p hp
    rw [mem_powersUpTo_iff] at hp
    simp only [Finset.mem_filter, mem_powersUpTo_iff, BasePower.val]
    constructor
    · constructor
      · have h1 : d p.idx ^ p.exp ≤ v - 1 := hp.1
        have h2 : v - 1 < v := by omega
        have h3 : v ≤ n := hv_le
        omega
      · have h1 : p.exp ≤ v - 1 := hp.2
        have h2 : v - 1 < v := by omega
        have h3 : v ≤ n := hv_le
        omega
    · calc d p.idx ^ p.exp ≤ v - 1 := hp.1
           _ < v := by omega
  -- So sum over filter ≥ sum over powersUpTo k d (v-1) ≥ v - 1
  have hge : v - 1 ≤ ∑ p ∈ (powersUpTo k d n).filter (fun q => q.val d < v), p.val d := by
    calc v - 1 ≤ ∑ p ∈ powersUpTo k d (v - 1), p.val d := hkey
         _ ≤ ∑ p ∈ (powersUpTo k d n).filter (fun q => q.val d < v), p.val d :=
             Finset.sum_le_sum_of_subset hsubset
  omega
set_option maxHeartbeats 2000000 in
/-- Subset sum for `powersUpTo`: find a subset summing to `n`.
    This uses Brown's completeness machinery: the powers sorted by value form a "complete"
    sequence where each power ≤ 1 + sum of smaller powers (by density condition). -/
lemma subset_sum_exists {k : ℕ} {d : Fin k → ℕ} (hd : ∀ i, 2 ≤ d i) (hk : 2 ≤ k)
    (hsum : 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1))
    {n : ℕ} (hn : 0 < n) :
    ∃ S : Finset (BasePower k), S ⊆ powersUpTo k d n ∧ ∑ p ∈ S, p.val d = n := by
  classical
  -- Order base-powers primarily by value, then by (idx, exp) to break ties.
  let key : BasePower k → Lex (ℕ × Lex (Fin k × ℕ)) :=
    fun p => toLex (p.val d, toLex (p.idx, p.exp))
  have key_inj : Function.Injective key := by
    intro p q h
    have h' : (p.idx, p.exp) = (q.idx, q.exp) := by
      have h₁ : (p.val d, toLex (p.idx, p.exp)) = (q.val d, toLex (q.idx, q.exp)) := by
        simpa [key] using congrArg (fun x => (ofLex x)) h
      have h₂ : toLex (p.idx, p.exp) = toLex (q.idx, q.exp) := by
        simpa using congrArg Prod.snd h₁
      simpa using congrArg (fun x => (ofLex x)) h₂
    have h_idx : p.idx = q.idx := congrArg Prod.fst h'
    have h_exp : p.exp = q.exp := congrArg Prod.snd h'
    cases p with
    | mk pidx pexp =>
      cases q with
      | mk qidx qexp =>
        cases h_idx
        cases h_exp
        rfl
  letI : Ord (BasePower k) := ⟨fun p q => compare (key p) (key q)⟩
  let compare_f : ∀ a b : BasePower k, compare a b = compare (key a) (key b) := by
    intro a b; rfl
  letI : LinearOrder (BasePower k) := LinearOrder.liftWithOrd' key key_inj compare_f

  let P : Finset (BasePower k) := powersUpTo k d n
  let m : ℕ := P.card
  have hm : P.card = m := rfl
  let e : Fin m ≃o ↥P := Finset.orderIsoOfFin P hm

  let a : ℕ → ℕ :=
    fun i =>
      if h : i < m then ((e ⟨i, h⟩).1).val d else 1

  have hk_pos : 0 < k := by omega
  let i0 : Fin k := ⟨0, hk_pos⟩
  let p1 : BasePower k := ⟨i0, 0⟩
  have hp1_mem : p1 ∈ P := by
    rw [mem_powersUpTo_iff]
    refine ⟨?_, Nat.zero_le _⟩
    simpa [P, p1, BasePower.val, pow_zero] using (Nat.succ_le_of_lt hn)
  have hp1_val : p1.val d = 1 := by simp [p1, BasePower.val]

  have hm_pos : 0 < m := by
    have : P.Nonempty := ⟨p1, hp1_mem⟩
    exact Nat.pos_of_ne_zero (Finset.card_ne_zero.mpr this)

  have ha0 : a 0 = 1 := by
    have hmin : (e ⟨0, hm_pos⟩).1 ≤ (⟨p1, hp1_mem⟩ : ↥P) := by
      haveI : NeZero m := ⟨Nat.ne_of_gt hm_pos⟩
      have h0 : (0 : Fin m) ≤ e.symm ⟨p1, hp1_mem⟩ := Fin.zero_le _
      have h0' : (⟨0, hm_pos⟩ : Fin m) ≤ e.symm ⟨p1, hp1_mem⟩ := by
        simp [h0]
      simpa using e.monotone h0'
    have hkey_le : key ((e ⟨0, hm_pos⟩).1) ≤ key p1 := by
      -- order on BasePower is the lifted key order
      have : (e ⟨0, hm_pos⟩ : ↥P) ≤ ⟨p1, hp1_mem⟩ := hmin
      have : (e ⟨0, hm_pos⟩).1 ≤ p1 := (Subtype.mk_le_mk).1 this
      -- `≤` is definitional as `key _ ≤ key _` for our lifted order.
      change key ((e ⟨0, hm_pos⟩).1) ≤ key p1
      simpa using this
    have hval_le : ((e ⟨0, hm_pos⟩).1).val d ≤ 1 := by
      have := (Prod.Lex.le_iff).1 hkey_le
      rcases this with hlt | ⟨heq, _⟩
      · exact Nat.le_of_lt hlt
      · exact Nat.le_of_eq heq
    have hval_ge : 1 ≤ ((e ⟨0, hm_pos⟩).1).val d := by
      have hd_pos : 0 < d ((e ⟨0, hm_pos⟩).1).idx := by
        have := hd ((e ⟨0, hm_pos⟩).1).idx; omega
      have : 0 < ((e ⟨0, hm_pos⟩).1).val d := by
        simp [BasePower.val, Nat.pow_pos hd_pos]
      omega
    have hval_eq : ((e ⟨0, hm_pos⟩).1).val d = 1 := Nat.le_antisymm hval_le hval_ge
    simp [a, hm_pos, hval_eq]

  have hstep : ∀ t, a (t + 1) ≤ 1 + partialSum a (t + 1) := by
    intro t
    by_cases ht : t + 1 < m
    · let iFin : Fin m := ⟨t + 1, ht⟩
      let p : BasePower k := (e iFin).1
      let v : ℕ := p.val d
      have hv_pos : 0 < v := by
        have hd_pos : 0 < d p.idx := by have := hd p.idx; omega
        have : 0 < p.val d := by simp [BasePower.val, p, Nat.pow_pos hd_pos]
        simpa [v] using this
      have hv_le : v ≤ n := by
        have hp_mem : p ∈ P := (e iFin).2
        have hp_mem' : p ∈ powersUpTo k d n := by simpa [P] using hp_mem
        exact (mem_powersUpTo_iff p).1 hp_mem' |>.1
      have hv_in : ∃ q ∈ powersUpTo k d n, q.val d = v := by
        have hp_mem : p ∈ powersUpTo k d n := by
          have hp_memP : p ∈ P := (e iFin).2
          simpa [P] using hp_memP
        exact ⟨p, hp_mem, rfl⟩
      have hv_step :
          v ≤ 1 + ∑ q ∈ (powersUpTo k d n).filter (fun q => q.val d < v), q.val d :=
        power_step_condition hd hk hsum hn v hv_pos hv_le hv_in

      -- Relate the sum of powers < v to the partial sum of the first (t+1) terms of `a`.
      let idxSmall : Finset (Fin m) :=
        (Finset.univ : Finset (Fin m)).filter (fun j => ((e j).1).val d < v)

      have hsum_small :
          (∑ q ∈ P.filter (fun q => q.val d < v), q.val d) =
            ∑ j ∈ idxSmall, ((e j).1).val d := by
        classical
        -- Use the order isomorphism to reindex the filtered sum.
        refine Finset.sum_bij (s := P.filter (fun q => q.val d < v)) (t := idxSmall)
          (i := fun q hq => e.symm ⟨q, (Finset.mem_filter.mp hq).1⟩) ?_ ?_ ?_ ?_
        · intro q hq
          have hqP : q ∈ P := (Finset.mem_filter.mp hq).1
          have hqv : q.val d < v := (Finset.mem_filter.mp hq).2
          have heq : (e (e.symm ⟨q, hqP⟩) : ↥P) = ⟨q, hqP⟩ := e.apply_symm_apply _
          have : ((e (e.symm ⟨q, hqP⟩)).1).val d < v := by
            simpa [heq] using hqv
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩
        · intro q1 hq1 q2 hq2 hEq
          have hEq' : (⟨q1, (Finset.mem_filter.mp hq1).1⟩ : ↥P) =
              (⟨q2, (Finset.mem_filter.mp hq2).1⟩ : ↥P) := by
            have := congrArg e hEq
            simpa using this
          have : q1 = q2 := by
            simpa using congrArg Subtype.val hEq'
          exact this
        · intro j hj
          have hj' : ((e j).1).val d < v := by
            simpa [idxSmall] using (Finset.mem_filter.mp hj).2
          refine ⟨(e j).1, ?_, ?_⟩
          · have : (e j).1 ∈ P := (e j).2
            have : (e j).1 ∈ P.filter (fun q => q.val d < v) := by
              exact Finset.mem_filter.mpr ⟨this, hj'⟩
            exact this
          · ext
            simp
        · intro q hq
          have hqP : q ∈ P := (Finset.mem_filter.mp hq).1
          have heq : (e (e.symm ⟨q, hqP⟩) : ↥P) = ⟨q, hqP⟩ := e.apply_symm_apply _
          simp [heq]

      have hidxSmall_sub : idxSmall ⊆ Finset.Iio iFin := by
        intro j hj
        have hjv : ((e j).1).val d < v := (Finset.mem_filter.mp hj).2
        -- If value is smaller, then key is smaller, hence index is smaller.
        have hlt_key : key (e j).1 < key p := by
          have : (ofLex (key (e j).1)).1 < (ofLex (key p)).1 := by
            simpa [key, v, p] using hjv
          -- unfold lexicographic comparison
          have : key (e j).1 < key p := by
            exact (Prod.Lex.lt_iff).2 (Or.inl this)
          exact this
        have hlt : (e j).1 < p := by
          change key (e j).1 < key p
          exact hlt_key
        have hlt' : (e j) < e iFin := by
          -- coe to subtype
          exact (Subtype.mk_lt_mk).2 hlt
        have : j < iFin := by
          simpa using (e.lt_iff_lt).1 hlt'
        simpa [Finset.mem_Iio] using this

      have hsum_small_le :
          (∑ q ∈ P.filter (fun q => q.val d < v), q.val d) ≤ partialSum a (t + 1) := by
        -- sum over P.filter = sum over idxSmall ≤ sum over Iio iFin = partialSum
        have h1 :
            (∑ q ∈ P.filter (fun q => q.val d < v), q.val d) ≤
              ∑ j ∈ Finset.Iio iFin, ((e j).1).val d := by
          rw [hsum_small]
          exact Finset.sum_le_sum_of_subset hidxSmall_sub
        have h2 : ∑ j ∈ Finset.Iio iFin, ((e j).1).val d = partialSum a (t + 1) := by
          unfold partialSum
          -- Reindex `range (t+1)` to `Iio iFin`.
          classical
          refine (Finset.sum_bij (s := Finset.range (t + 1)) (t := Finset.Iio iFin)
            (i := fun j hj => (⟨j, Nat.lt_trans (Finset.mem_range.mp hj) ht⟩ : Fin m))
            ?_ ?_ ?_ ?_).symm
          · intro j hj
            have hj' : j < t + 1 := Finset.mem_range.mp hj
            have : (⟨j, Nat.lt_trans hj' ht⟩ : Fin m) < iFin := by
              simpa [iFin] using hj'
            simpa [Finset.mem_Iio] using this
          · intro j1 hj1 j2 hj2 hEq
            simp only [Fin.ext_iff] at hEq
            exact hEq
          · intro j hj
            have hj' : (j : ℕ) < t + 1 := by
              have : (j : Fin m) < iFin := by simpa [Finset.mem_Iio] using hj
              simpa [iFin] using this
            refine ⟨j.1, ?_, ?_⟩
            · exact Finset.mem_range.mpr hj'
            · ext; simp
          · intro j hj
            have hj' : j < t + 1 := Finset.mem_range.mp hj
            have hjm : j < m := Nat.lt_trans hj' ht
            simp [a, hjm]
        exact le_trans h1 (le_of_eq h2)

      have hv_step' :
          v ≤ 1 + partialSum a (t + 1) := by
        -- combine hv_step and hsum_small_le (after rewriting P = powersUpTo)
        have hsum_rewrite :
            (∑ q ∈ (powersUpTo k d n).filter (fun q => q.val d < v), q.val d) =
              ∑ q ∈ P.filter (fun q => q.val d < v), q.val d := by
          rfl
        -- now
        have : v ≤ 1 + ∑ q ∈ P.filter (fun q => q.val d < v), q.val d := by
          simpa [hsum_rewrite] using hv_step
        exact le_trans this (Nat.add_le_add_left hsum_small_le 1)

      -- Finish: a (t+1) = v
      have hat : a (t + 1) = v := by
        have : t + 1 < m := ht
        simp [a, this, v, p, iFin]
      simpa [hat] using hv_step'
    · -- Beyond the length, a(t+1) = 1
      have : ¬ (t + 1 < m) := ht
      simp [a, this]

  have hn_le_partial : n ≤ partialSum a m := by
    -- partialSum a m is the total sum of values of all elements of P.
    have htot : partialSum a m = ∑ p ∈ P, p.val d := by
      unfold partialSum
      -- ∑ i ∈ range m, a i = ∑ i : Fin m, a i.1
      have hsum_range : (∑ i ∈ Finset.range m, a i) = ∑ i : Fin m, a i := by
        simpa using (Finset.sum_range (f := a) (n := m))
      rw [hsum_range]
      -- unfold a on Fin m indices
      have ha_fin : (∑ i : Fin m, a i) = ∑ i : Fin m, ((e i).1).val d := by
        apply Finset.sum_congr rfl
        intro i _
        simp [a, i.isLt]
      rw [ha_fin]
      -- reindex via the equivalence e : Fin m ≃ ↥P
      have hsum_equiv :
          (∑ i : Fin m, ((e i).1).val d) = ∑ p : ↥P, (p : BasePower k).val d := by
        simpa using (Equiv.sum_comp (e.toEquiv) (fun p : ↥P => (p : BasePower k).val d))
      rw [hsum_equiv]
      -- rewrite sum over subtype as finset sum
      simpa using (Finset.sum_coe_sort (s := P) (f := fun p : BasePower k => p.val d))
    have hn_le : n ≤ ∑ p ∈ P, p.val d := by
      simpa [P] using sum_powers_at_least (k := k) (d := d) hd hsum n hn
    simpa [htot] using hn_le

  obtain ⟨s, hs_bound, hs_sum⟩ :=
    brown_achievable_range a ha0 hstep m n hn_le_partial

  let g : ℕ → BasePower k :=
    fun i => if h : i < m then (e ⟨i, h⟩).1 else (e ⟨0, hm_pos⟩).1
  let S : Finset (BasePower k) := s.image g
  refine ⟨S, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    have hi' : i < m := hs_bound i hi
    simp only [g, dif_pos hi']
    exact (e ⟨i, hi'⟩).property
  · -- sum over S matches the Brown-selected indices
    have hg_inj : Set.InjOn g (↑s : Set ℕ) := by
      intro i hi j hj hij
      have hi' : i < m := hs_bound i (by simpa using hi)
      have hj' : j < m := hs_bound j (by simpa using hj)
      have : (e ⟨i, hi'⟩ : ↥P) = e ⟨j, hj'⟩ := by
        apply Subtype.ext
        simpa [g, hi', hj'] using hij
      have : (⟨i, hi'⟩ : Fin m) = ⟨j, hj'⟩ := e.injective this
      simpa using congrArg Fin.val this
    -- Evaluate the sum using injectivity
    have hsum_image :
        (∑ p ∈ S, p.val d) = ∑ i ∈ s, (g i).val d := by
      simpa [S] using
        (Finset.sum_image (f := fun p : BasePower k => p.val d) (s := s) (g := g) hg_inj)
    rw [hsum_image]
    -- g i is exactly a i on indices from s
    have : (∑ i ∈ s, (g i).val d) = ∑ i ∈ s, a i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < m := hs_bound i hi
      simp [g, a, hi', P]
    rw [this, hs_sum]

/-- The sum of all powers up to M -/
lemma sum_powersUpTo_eq {k : ℕ} {d : Fin k → ℕ} (_hd : ∀ i, 2 ≤ d i) (M : ℕ) :
    ∑ p ∈ powersUpTo k d M, p.val d =
    ∑ i : Fin k, ∑ e ∈ Finset.range (M + 1), if d i ^ e ≤ M then d i ^ e else 0 := by
  unfold powersUpTo BasePower.val
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Finset.sum_filter, Finset.sum_product]

/-- Helper: If one of the bases is 2, the theorem is trivial -/
lemma erdos_124_with_base2 {k : ℕ} {d : Fin k → ℕ} (_hd : ∀ i, 2 ≤ d i)
    (i₀ : Fin k) (hi₀ : d i₀ = 2) (n : ℕ) :
    ∃ a : Fin k → ℕ, (∀ i, usesOnlyZeroOne (d i) (a i)) ∧ n = ∑ i, a i := by
  -- Set a_{i₀} = n (using binary representation) and a_i = 0 for other indices
  use fun i => if i = i₀ then n else 0
  constructor
  · intro i
    by_cases h : i = i₀
    · simp only [h, ↓reduceIte, hi₀]
      exact usesOnlyZeroOne_base2 n
    · simp only [h, ↓reduceIte]
      exact usesOnlyZeroOne_zero (d i)
  · simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- Erdős Problem 124: Given k bases d(i) (each ≥ 2) such that ∑ᵢ 1/(d(i)-1) ≥ 1,
every natural number n can be written as a sum of k numbers a(i) where each a(i)
uses only digits 0 and 1 in base d(i). -/
theorem erdos_124 : ∀ k : ℕ, ∀ d : Fin k → ℕ,
    (∀ i, 2 ≤ d i) →
    1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1) →
    ∀ n : ℕ, ∃ a : Fin k → ℕ,
      (∀ i, usesOnlyZeroOne (d i) (a i)) ∧ n = ∑ i, a i := by
  intro k d hd hsum n
  -- Key simplification: if any base equals 2, use binary representation
  by_cases h2 : ∃ i, d i = 2
  · obtain ⟨i₀, hi₀⟩ := h2
    exact erdos_124_with_base2 hd i₀ hi₀ n
  -- The harder case: no base equals 2 (all bases ≥ 3)
  -- In this case, the density condition ∑ 1/(d_i-1) ≥ 1 requires multiple bases.
  push_neg at h2
  -- Key observation: since all d_i ≥ 3, we have 1/(d_i - 1) ≤ 1/2 for all i.
  -- To achieve ∑ 1/(d_i - 1) ≥ 1, we need at least 2 bases.
  have hk : 2 ≤ k := by
    by_contra hk'
    push_neg at hk'
    interval_cases k
    · -- k = 0: empty sum = 0 < 1, contradiction with hsum
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
      linarith
    · -- k = 1: single base d 0 ≥ 3, so 1/(d 0 - 1) ≤ 1/2 < 1
      simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at hsum
      have hd0 : d 0 ≥ 3 := by
        have := hd 0
        have := h2 0
        omega
      have hge2 : (2 : ℚ) ≤ (d 0 : ℚ) - 1 := by
        have : (3 : ℕ) ≤ d 0 := hd0
        have h1 : (3 : ℚ) ≤ (d 0 : ℚ) := by exact_mod_cast this
        linarith
      have hpos : (0 : ℚ) < (d 0 : ℚ) - 1 := by linarith
      have : (1 : ℚ) / (d 0 - 1) ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by linarith : (0 : ℚ) < 2) hge2
      linarith
  -- Now we have k ≥ 2 bases, each providing d_i^0 = 1
  -- Strong induction on n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    -- Base case: n = 0
    cases' Nat.eq_zero_or_pos n with hn hn
    · refine ⟨fun _ => 0, ?_, ?_⟩
      · intro i
        exact usesOnlyZeroOne_zero (d i)
      · simp [hn]

    -- Case 1: n ≤ k (can use just ones from k bases)
    by_cases hnk : n ≤ k
    · -- Use n ones from n different bases
      -- Since we have k bases and n ≤ k, we can pick n of them to contribute 1 each
      use fun i => if i.val < n then 1 else 0
      constructor
      · intro i
        by_cases hi : i.val < n
        · simp only [hi, ↓reduceIte]
          exact usesOnlyZeroOne_one (hd i)
        · simp only [hi, ↓reduceIte]
          exact usesOnlyZeroOne_zero (d i)
      · -- Sum equals n: we have n ones and (k - n) zeros
        have hsum_eq : ∑ i : Fin k, (if i.val < n then 1 else 0) = n := by
          rw [Finset.sum_boole]
          -- Goal: (Finset.univ.filter fun i : Fin k => i.val < n).card = n
          have hcard :
              (Finset.univ.filter fun i : Fin k => i.val < n).card = n := by
            have h1 : ∀ i : Fin k,
                i ∈ Finset.univ.filter (fun i => i.val < n) ↔ i.val < n := by
              intro i; simp
            -- The filter contains exactly {⟨0, _⟩, ⟨1, _⟩, ..., ⟨n-1, _⟩}
            conv_rhs => rw [← Finset.card_fin n]
            apply Finset.card_bij (fun i _ => ⟨i.val, by simp at *; omega⟩)
            · intro i hi; simp
            · intro i₁ _ i₂ _ h
              simp only [Fin.ext_iff] at h ⊢
              exact h
            · intro j _
              use ⟨j.val, by omega⟩
              simp
          exact hcard
        simp only [hsum_eq]

    -- Case 2: n > k (need larger powers)
    -- Use the Brown-based global power approach
    push_neg at hnk

    -- The proof uses a finite version of Brown's completeness lemma:
    -- 1. Collect all powers d(i)^e ≤ n across all bases
    -- 2. The density condition ensures their sum ≥ n
    -- 3. By the "complete sequence" property, we can achieve any sum up to the total
    -- 4. Group the chosen powers by base

    -- Step 1: Define the finite set of powers to consider
    let P := powersUpTo k d n

    -- Step 2: Find a subset of P that sums to exactly n (Brown completeness + density)
    have hsubset_sum : ∃ S : Finset (BasePower k), S ⊆ P ∧ ∑ p ∈ S, p.val d = n := by
      simpa [P] using subset_sum_exists (k := k) (d := d) hd hk hsum hn

    -- Step 4: Group the chosen powers by base index
    obtain ⟨S, _hS_sub, hS_sum⟩ := hsubset_sum

    -- For each base i, collect the exponents used from that base
    let expsForBase (i : Fin k) : Finset ℕ := (S.filter (fun p => p.idx = i)).image BasePower.exp

    -- Define a(i) as the sum of powers for base i
    let a : Fin k → ℕ := fun i => ∑ e ∈ expsForBase i, d i ^ e

    use a
    constructor
    · -- Each a(i) uses only 0,1 digits (it's a sum of distinct powers)
      intro i
      exact usesOnlyZeroOne_sum_distinct_powers (hd i) (expsForBase i)
    · -- The sum equals n
      -- Need to show: ∑ i, a i = ∑ p ∈ S, p.val d = n
      have hsum_regroup : ∑ i : Fin k, a i = ∑ p ∈ S, p.val d := by
        -- Regroup the double sum by swapping order
        simp only [a, expsForBase, BasePower.val]
        -- Use Finset.sum_fiberwise to regroup by idx
        symm
        rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : BasePower k => p.idx)
            (t := Finset.univ) (by simp)]
        apply Finset.sum_congr rfl
        intro i _
        -- Need: sum over {p ∈ S | p.idx = i} of d p.idx ^ p.exp
        --       = sum over image exp of d i ^ e
        -- First use that p.idx = i for all p in the filtered set
        have hfilter_eq :
            ∀ p ∈ S.filter (fun p => p.idx = i), d p.idx ^ p.exp = d i ^ p.exp := by
          intro p hp
          simp only [Finset.mem_filter] at hp
          rw [hp.2]
        conv_lhs => arg 2; ext p; rw [show d p.idx ^ p.exp = d p.idx ^ p.exp by rfl]
        rw [Finset.sum_congr rfl (fun p hp => hfilter_eq p hp)]
        -- Now sum over filter is sum over image
        rw [Finset.sum_image]
        intro p₁ hp₁ p₂ hp₂ he
        have hp₁' := Finset.mem_filter.mp hp₁
        have hp₂' := Finset.mem_filter.mp hp₂
        have hidx_eq : p₁.idx = p₂.idx := hp₁'.2.trans hp₂'.2.symm
        cases p₁; cases p₂
        simp only [BasePower.mk.injEq]
        exact ⟨hidx_eq, he⟩
      rw [hsum_regroup, hS_sum]
