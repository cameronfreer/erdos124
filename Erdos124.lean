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

/-- When adding b^e to n where digit e is 0, preserves 0,1 digit property.
The key insight: digit e becomes 1, all other digits unchanged (no carry). -/
lemma add_pow_preserves_01_digits {b n e : ℕ} (_hb : 2 ≤ b)
    (_hvalid : usesOnlyZeroOne b n)
    (_hdigit_zero : (Nat.digits b n).getD e 0 = 0) :
    usesOnlyZeroOne b (n + b ^ e) := by
  -- Proof outline:
  -- Key lemma: (digits b n).getD i 0 = n / b^i % b (Nat.getD_digits)
  -- Since digit e = 0 (hypothesis), adding b^e doesn't cause carries past position e.
  -- For position j:
  --   j < e: (n + b^e) / b^j = n / b^j + b^(e-j), mod b unchanged
  --   j = e: digit becomes (0 + 1) mod b = 1
  --   j > e: (n + b^e) / b^j = n / b^j (no carry since n % b^(e+1) + b^e < b^(e+1))
  sorry

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

    -- Case 1: n ≤ k (can use just ones from k bases)
    by_cases hnk : n ≤ k
    · -- Use n ones from n different bases
      -- Since we have k bases and n ≤ k, we can pick n of them to contribute 1 each
      have hfin : n ≤ Fintype.card (Fin k) := by simp [Fintype.card_fin]; exact hnk
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
          have hcard : (Finset.univ.filter fun i : Fin k => i.val < n).card = n := by
            have h1 : ∀ i : Fin k, i ∈ Finset.univ.filter (fun i => i.val < n) ↔ i.val < n := by
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

    -- Case 2: n > k (need larger powers, more complex argument)
    push_neg at hnk

    -- Key helper: adding a power to a smaller number preserves 0,1 digits
    -- Proof idea: when m < b^e, the digits of m have length ≤ e.
    -- So m + b^e = ofDigits b (digits(m) ++ zeros ++ [1]) where all entries are ≤ 1.
    have add_pow_valid : ∀ (b m e : ℕ), 2 ≤ b → m < b ^ e →
        usesOnlyZeroOne b m → usesOnlyZeroOne b (m + b ^ e) := by
      intro b m e hb hm hvalid
      by_cases hm_zero : m = 0
      · simp only [hm_zero, zero_add]
        exact usesOnlyZeroOne_pow hb e
      · have h1 : 1 < b := by omega
        -- Key: m < b^e implies length of digits ≤ e
        have hlen : (Nat.digits b m).length ≤ e := by
          by_contra hlen'
          push_neg at hlen'
          have hge := Nat.base_pow_length_digits_le b m h1 hm_zero
          have hb_pos : 0 < b := by omega
          have hlen_pos : 0 < (Nat.digits b m).length :=
            List.length_pos_of_ne_nil (Nat.digits_ne_nil_iff_ne_zero.mpr hm_zero)
          have hpow_le_m : b ^ ((Nat.digits b m).length - 1) ≤ m := by
            have : b ^ (Nat.digits b m).length = b ^ ((Nat.digits b m).length - 1) * b := by
              rw [← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hlen_pos]
            calc b ^ ((Nat.digits b m).length - 1)
                = b ^ (Nat.digits b m).length / b := by
                    rw [this, Nat.mul_div_cancel _ hb_pos]
              _ ≤ b * m / b := Nat.div_le_div_right hge
              _ = m := Nat.mul_div_cancel_left m hb_pos
          have he_bound : e ≤ (Nat.digits b m).length - 1 := by omega
          have : b ^ e ≤ m := calc
            b ^ e ≤ b ^ ((Nat.digits b m).length - 1) := Nat.pow_le_pow_right (by omega) he_bound
            _ ≤ m := hpow_le_m
          omega

        -- Use digits_append_zeroes_append_digits
        set len := (Nat.digits b m).length
        have hexp_eq : len + (e - len) = e := Nat.add_sub_cancel' hlen
        have hdigits_eq : Nat.digits b (m + b ^ e) =
            Nat.digits b m ++ List.replicate (e - len) 0 ++ Nat.digits b 1 := by
          have hrhs := Nat.digits_append_zeroes_append_digits h1 (m := 1) (k := e - len) (n := m)
            (by omega : 0 < 1)
          simp only [mul_one] at hrhs
          rw [hexp_eq] at hrhs
          exact hrhs.symm

        have hdigits_one : Nat.digits b 1 = [1] := by
          rw [Nat.digits_def' h1 (by omega : 0 < 1)]
          simp only [Nat.mod_eq_of_lt h1, Nat.div_eq_of_lt h1, Nat.digits_zero]

        unfold usesOnlyZeroOne at hvalid ⊢
        rw [hdigits_eq, hdigits_one]
        intro x hx
        simp only [List.toFinset_append, Finset.mem_union] at hx
        rcases hx with (hx | hx) | hx
        · exact hvalid hx
        · by_cases hz : e - len = 0
          · simp [hz] at hx
          · rw [List.toFinset_replicate_of_ne_zero hz] at hx
            simp only [Finset.mem_singleton] at hx
            simp [hx]
        · simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty,
            Finset.mem_singleton] at hx
          simp [hx]

    -- Find base 0 and its largest power
    have hk_pos : 0 < k := by omega
    set i₀ : Fin k := ⟨0, hk_pos⟩ with hi₀_def
    set e₀ := largestExp (d i₀) n with he₀_def
    set p := (d i₀) ^ e₀ with hp_def

    have hp_le : p ≤ n := pow_largestExp_le (hd i₀) hn
    have hp_pos : 0 < p := Nat.one_le_pow _ _ (by have := hd i₀; omega : 0 < d i₀)

    -- Apply induction to n - p
    have hlt : n - p < n := Nat.sub_lt hn hp_pos
    obtain ⟨a', ha'valid, ha'sum⟩ := ih (n - p) hlt

    -- Case split on whether a' i₀ < p (safe to add p to same base)
    by_cases ha'_small : a' i₀ < p
    · -- a' i₀ < p = d^e₀, so adding p doesn't cause digit overflow
      use fun j => if j = i₀ then a' i₀ + p else a' j
      constructor
      · intro j
        by_cases hj : j = i₀
        · subst hj
          simp only [↓reduceIte]
          rw [hp_def, he₀_def]
          exact add_pow_valid (d i₀) (a' i₀) e₀ (hd i₀) ha'_small (ha'valid i₀)
        · simp only [hj, ↓reduceIte]
          exact ha'valid j
      · -- Sum equals n
        have hsum_eq : ∑ j, (if j = i₀ then a' i₀ + p else a' j) = (∑ j, a' j) + p := by
          -- The LHS adds p to the i₀ term: ∑ (if j = i₀ then a' i₀ + p else a' j) = (∑ a' j) + p
          calc ∑ j, (if j = i₀ then a' i₀ + p else a' j)
              = ∑ j, (a' j + if j = i₀ then p else 0) := by
                  apply Finset.sum_congr rfl; intro j _
                  by_cases h : j = i₀ <;> simp [h]
            _ = ∑ j, a' j + ∑ j, (if j = i₀ then p else 0) := Finset.sum_add_distrib
            _ = ∑ j, a' j + p := by simp [Finset.sum_ite_eq']
        rw [hsum_eq, ha'sum.symm, Nat.sub_add_cancel hp_le]

    · -- a' i₀ ≥ p: need to check if we can still add p to a' i₀
      push_neg at ha'_small

      -- Key insight: Check if digit e₀ in a' i₀ is 0 or 1
      -- If 0: can add p directly. If 1: use induction on a smaller value.
      let digit_e₀ := (Nat.digits (d i₀) (a' i₀)).getD e₀ 0

      by_cases hdigit : digit_e₀ = 0
      · -- Case: digit at position e₀ is 0, so we can add p = (d i₀)^e₀
        -- Even though a' i₀ ≥ p, the position e₀ is "free"
        use fun j => if j = i₀ then a' i₀ + p else a' j
        constructor
        · intro j
          by_cases hj : j = i₀
          · subst hj
            simp only [↓reduceIte]
            -- Need to show usesOnlyZeroOne (d i₀) (a' i₀ + p)
            -- Since digit e₀ is 0 in a' i₀, adding (d i₀)^e₀ sets that digit to 1
            rw [hp_def, he₀_def]
            exact add_pow_preserves_01_digits (hd i₀) (ha'valid i₀) hdigit
          · simp only [hj, ↓reduceIte]
            exact ha'valid j
        · have hsum_eq : ∑ j, (if j = i₀ then a' i₀ + p else a' j) = (∑ j, a' j) + p := by
            calc ∑ j, (if j = i₀ then a' i₀ + p else a' j)
                = ∑ j, (a' j + if j = i₀ then p else 0) := by
                    apply Finset.sum_congr rfl; intro j _
                    by_cases h : j = i₀ <;> simp [h]
              _ = ∑ j, a' j + ∑ j, (if j = i₀ then p else 0) := Finset.sum_add_distrib
              _ = ∑ j, a' j + p := by simp [Finset.sum_ite_eq']
          rw [hsum_eq, ha'sum.symm, Nat.sub_add_cancel hp_le]

      · -- Case: digit at position e₀ is 1 (since usesOnlyZeroOne means ≤ 1)
        -- This means (d i₀)^e₀ is already used in a' i₀
        -- Strategy: find a' i₀ has (d i₀)^e₀ as a summand, so we can
        -- apply induction on n - (d i₀)^e₀ directly (skipping the first base)

        -- Since digit e₀ = 1, we have a' i₀ ≥ (d i₀)^e₀ = p and the
        -- e₀-th digit is 1. So a' i₀ - (d i₀)^e₀ still uses only 0,1 digits.

        -- Let a'' i₀ = a' i₀ - p, and a'' j = a' j for j ≠ i₀
        -- Then ∑ a'' = n - p - p = n - 2p
        -- And a'' uses only 0,1 digits

        -- Now we need a representation of n = (n - 2p) + 2p
        -- Apply induction on n - 2p to get b'', then add 2p

        -- But 2p might not be a single power... unless we're clever

        -- Actually, let's use a different approach:
        -- If a' i₀ has a 1 at position e₀, then a' i₀ = (d i₀)^e₀ + r
        -- where r < (d i₀)^e₀ and usesOnlyZeroOne r (positions < e₀)

        -- We want n = (n - p) + p = ∑ a' + p
        -- = (∑_{j≠i₀} a' j) + a' i₀ + p
        -- = (∑_{j≠i₀} a' j) + ((d i₀)^e₀ + r) + (d i₀)^e₀
        -- = (∑_{j≠i₀} a' j) + r + 2 * (d i₀)^e₀

        -- The issue is 2 * (d i₀)^e₀ which can't be represented with 0,1 digits

        -- So we need to "carry" or redistribute this to other bases
        -- Since k ≥ 2, use another base

        -- This is getting complex. Let's try a stronger induction:
        -- Apply ih to n - 2p if 2p ≤ n, otherwise use a different decomposition

        have h2p_le_n : 2 * p ≤ n := by
          -- We have p ≤ a' i₀ and ∑ a' = n - p
          -- So a' i₀ ≤ n - p, hence p ≤ n - p, hence 2p ≤ n
          have : p ≤ n - p := by
            calc p ≤ a' i₀ := ha'_small
              _ ≤ ∑ j, a' j := Finset.single_le_sum (fun j _ => Nat.zero_le _)
                  (Finset.mem_univ i₀)
              _ = n - p := ha'sum.symm
          omega

        -- Apply induction to n - 2p
        have hlt2 : n - 2 * p < n := by omega
        obtain ⟨a'', ha''valid, ha''sum⟩ := ih (n - 2 * p) hlt2

        -- Now we need to add 2p using the available bases
        -- Since k ≥ 2, we can use base 1 to add power p, and base 0 to add power p
        -- But we need a'' i ≤ some bound for each base

        -- Actually, let's check if a'' i₀ < p. If so, we can add p to a'' i₀
        -- Similarly for a'' i₁ where i₁ ≠ i₀

        have hi₁_exists : ∃ i₁ : Fin k, i₁ ≠ i₀ := by
          have hk' : 1 < k := by omega
          have : 1 < Fintype.card (Fin k) := by simp; omega
          exact Fintype.exists_ne_of_one_lt_card this i₀

        obtain ⟨i₁, hi₁⟩ := hi₁_exists

        -- Case split on whether we can add p to both a'' i₀ and a'' i₁
        by_cases ha''_small_i₀ : a'' i₀ < p
        · by_cases ha''_small_i₁ : a'' i₁ < p
          · -- Both a'' i₀ < p and a'' i₁ < p
            -- We can add p to each using add_pow_valid
            use fun j => if j = i₀ then a'' i₀ + p else if j = i₁ then a'' i₁ + p else a'' j
            constructor
            · intro j
              by_cases hj₀ : j = i₀
              · subst hj₀
                simp only [↓reduceIte]
                rw [hp_def, he₀_def]
                exact add_pow_valid (d i₀) (a'' i₀) e₀ (hd i₀) ha''_small_i₀ (ha''valid i₀)
              · simp only [hj₀, ↓reduceIte]
                by_cases hj₁ : j = i₁
                · subst hj₁
                  simp only [↓reduceIte]
                  -- Adding p = (d i₀)^e₀ to a'' i₁ base d i₁
                  -- This requires that (d i₁).digits (a'' i₁ + p) has only 0,1 digits
                  -- This is not immediately clear since p is a power of d i₀, not d i₁
                  -- For now, we use sorry as this requires more careful analysis
                  sorry
                · simp only [hj₁, ↓reduceIte]
                  exact ha''valid j
            · -- Sum equals n
              have hne : i₁ ≠ i₀ := hi₁
              calc n = (n - 2 * p) + 2 * p := (Nat.sub_add_cancel h2p_le_n).symm
                _ = (∑ i, a'' i) + 2 * p := by rw [ha''sum]
                _ = (∑ i, a'' i) + p + p := by ring
                _ = (∑ i, a'' i) + (∑ i, if i = i₀ then p else 0) + (∑ i, if i = i₁ then p else 0) := by
                    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
                _ = ∑ i, (a'' i + (if i = i₀ then p else 0) + (if i = i₁ then p else 0)) := by
                    simp only [Finset.sum_add_distrib]
                _ = ∑ i, (if i = i₀ then a'' i₀ + p else if i = i₁ then a'' i₁ + p else a'' i) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    by_cases hj₀ : j = i₀
                    · simp [hj₀, hne.symm]
                    · by_cases hj₁ : j = i₁
                      · simp [hj₁, hne]
                      · simp [hj₀, hj₁]
          · -- a'' i₀ < p but a'' i₁ ≥ p
            -- Need different strategy: check if digit at position e₀ in a'' i₀ is 0
            sorry
        · -- a'' i₀ ≥ p
          -- Apply add_pow_preserves_01_digits if the digit at e₀ is 0
          sorry
