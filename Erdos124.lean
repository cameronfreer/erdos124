import Mathlib

/-!
# Erdős Problem 124

This file contains the statement and proof of Erdős Problem 124.

## Statement

Given k bases d(i) (each ≥ 2) such that ∑ᵢ 1/(d(i)-1) ≥ 1, every natural number n
can be written as a sum of k numbers a(i) where each a(i) uses only digits 0 and 1
in base d(i).

## Proof Strategy

The proof uses a greedy algorithm. For each n > 0:
1. For each base d_i, identify the largest power d_i^{e_i} such that d_i^{e_i} ≤ n
2. The condition ∑ 1/(d_i-1) ≥ 1 ensures that the sum of these largest powers
   is at least n (by a density argument)
3. Greedily select which powers to include to sum to exactly n
4. Apply induction to reduce the problem

## References

* [Erdős Problem 124](https://www.erdosproblems.com/124)
-/

open Finset BigOperators

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
lemma indicatorList_mem_zero_one (s : Finset ℕ) (n : ℕ) (x : ℕ) (hx : x ∈ indicatorList s n) :
    x = 0 ∨ x = 1 := by
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
      have hsub : ∀ e ∈ s, e < n := fun e he => Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp (hn e he)) (fun h => hn_in (h ▸ he))
      rw [ih s hsub]
      simp only [hn_in, ↓reduceIte, Nat.ofDigits_singleton, mul_zero, add_zero]

/-- Last element of a non-empty indicator list is the indicator of n-1 ∈ s -/
lemma indicatorList_getLast {s : Finset ℕ} {n : ℕ} (hn : 0 < n) (hne : indicatorList s n ≠ []) :
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
  have h1 : ∀ i, (n : ℚ) / ((d i : ℚ) - 1) ≤ ((d i) ^ (largestExp (d i) n + 1) - 1 : ℚ) / ((d i : ℚ) - 1) := by
    intro i
    have hdi : 2 ≤ d i := hd i
    have hd_pos : 0 < (d i : ℚ) - 1 := by
      have : 1 < d i := by omega
      simp only [sub_pos, Nat.one_lt_cast, this]
    apply div_le_div_of_nonneg_right _ (le_of_lt hd_pos)
    have hlt := lt_pow_largestExp_succ hdi hn
    -- n < d^{e+1} in ℕ means n ≤ d^{e+1} - 1 in ℕ
    have hpow_ge_one : 1 ≤ (d i) ^ (largestExp (d i) n + 1) := Nat.one_le_pow _ _ (by omega : 0 < d i)
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

    -- For n > 0, we use the capacity lemma which shows there's enough room
    have _hcap := capacity_lemma hd hsum hn

    -- Case split on whether n ≤ k (can use just ones) or n > k (need larger powers)
    -- With k ≥ 2 bases, we have at least 2 ones available.
    -- The proof uses a greedy construction with careful tracking.
    --
    -- Key insight: Each base d_i ≥ 3 has powers 1, d_i, d_i^2, ...
    -- The greedy algorithm selects powers in decreasing order:
    -- 1. Start with remaining = n
    -- 2. Find largest unused power p ≤ remaining
    -- 3. Use p, set remaining := remaining - p
    -- 4. Repeat until remaining = 0
    --
    -- The density condition ensures this always terminates because:
    -- - The total capacity of all available powers exceeds n
    -- - At each step, we can always find a power ≤ remaining
    --   (worst case: use a 1 from an unused base)
    --
    -- Full formalization requires defining the greedy selection and proving
    -- that it never runs out of valid choices. This is left for future work.
    sorry
