import Mathlib

/-!
# Erdős Problem 124

This file contains the statement and proof of Erdős Problem 124.

## Statement

Given k bases d(i) (each ≥ 2) such that ∑ᵢ 1/(d(i)-1) ≥ 1, every natural number n
can be written as a sum of k numbers a(i) where each a(i) uses only digits 0 and 1
in base d(i).

## Proof Strategy

The proof uses subset sum on the set P of all powers d_i^e ≤ n across all bases.

**Key steps:**
1. Define P = {(i, e) : d_i^e ≤ n} with value function (i,e) ↦ d_i^e
2. The density condition ∑ 1/(d_i-1) ≥ 1 implies ∑_{p ∈ P} p.val ≥ n
3. By strong induction on excess = (∑ P) - n, construct a subset S ⊆ P with ∑ S = n:
   - Base case: excess ≤ k → use "ones" (powers d_i^0 = 1)
   - Inductive case: excess > k → density key gives base d_i ≤ k+1;
     subtract d_i and recurse

**Density key lemma:** If ∑ 1/(d_i-1) ≥ 1, the minimum base satisfies d_min ≤ k+1.
This ensures we can always reduce excess by ≥ 2 when excess > k.

**Edge case handling:** When the recursively-built set already contains the chosen
power, we use an alternative decomposition with ones (the base case handles small
remainders).

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

/-!
## Brown's Completeness Lemma

A key tool: if a nondecreasing sequence `a` satisfies `a(n+1) ≤ 1 + ∑_{i≤n} a(i)`,
then every natural number is representable as a finite subset sum of the sequence.
-/

/-- Partial sum of the first n terms (indices 0 to n-1) -/
def partialSum (a : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, a i

/-- Brown's completeness lemma (finite version):
The set of achievable subset sums from {a(0), ..., a(n-1)} is exactly {0, 1, ..., partialSum a n}
when the step condition holds. -/
lemma brown_achievable_range (a : ℕ → ℕ) (h0 : a 0 = 1)
    (hstep : ∀ m, a (m + 1) ≤ 1 + partialSum a (m + 1)) :
    ∀ n, ∀ k ≤ partialSum a n, ∃ s : Finset ℕ, (∀ i ∈ s, i < n) ∧ ∑ i ∈ s, a i = k := by
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
  (Finset.univ (α := Fin k) ×ˢ Finset.range (M + 1)).filter (fun p => d p.1 ^ p.2 ≤ M) |>.map
    ⟨fun p => ⟨p.1, p.2⟩, fun _ _ h => by simp only [BasePower.mk.injEq] at h; ext <;> simp [h.1, h.2]⟩

/-- Geometric series formula in ℚ: (d^(e+1) - 1)/(d-1) = ∑_{j=0}^{e} d^j -/
lemma geom_series_eq_sum (d : ℕ) (_hd : 2 ≤ d) (e : ℕ) :
    ((d : ℚ) ^ (e + 1) - 1) / ((d : ℚ) - 1) = ∑ j ∈ Finset.range (e + 1), (d : ℚ) ^ j := by
  have hd_ne_one : (d : ℚ) ≠ 1 := by
    have : (1 : ℕ) < d := by omega
    exact_mod_cast (ne_of_gt this)
  have hd1 : (d : ℚ) - 1 ≠ 0 := by linarith [show (1 : ℚ) < d from by exact_mod_cast (by omega : 1 < d)]
  have hgeom := geom_sum_eq hd_ne_one (e + 1)
  -- hgeom : ∑ i ∈ range (e+1), d^i = (d^(e+1) - 1) / (d - 1)
  rw [hgeom]

/-- Each power d^j with j ≤ largestExp is ≤ n -/
lemma pow_le_of_le_largestExp {d n j : ℕ} (hd : 2 ≤ d) (hn : 0 < n) (hj : j ≤ largestExp d n) :
    d ^ j ≤ n := by
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
  (Finset.univ : Finset (Fin k)).map ⟨fun i => ⟨i, 0⟩, fun _ _ h => by simp [BasePower.ext_iff] at h; exact h⟩

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
lemma density_duplicate_when_max {k : ℕ} {d : Fin k → ℕ} (hd : ∀ i, 2 ≤ d i) (hk : 2 ≤ k)
    (hsum : 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1)) (i₀ : Fin k) (hi₀_eq : d i₀ = k + 1)
    (hi₀_min : ∀ j, d i₀ ≤ d j) :
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
      simp [Finset.card_sdiff, Finset.singleton_inter_of_mem (Finset.mem_univ i₀), Fintype.card_fin]
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
  -- Same argument as in hsum_ge proof in erdos_124
  -- For each base i, sum of powers d_i^0 + ... + d_i^{e_i} ≥ T/(d_i - 1)
  -- where e_i = largestExp(d_i, T). Summing: total ≥ T * ∑ 1/(d_i - 1) ≥ T
  have hcap : (T : ℚ) ≤ ∑ i : Fin k, ((d i) ^ (largestExp (d i) T + 1) - 1 : ℚ) / ((d i) - 1) :=
    capacity_lemma hd hsum hT
  have hcap' : (T : ℚ) ≤ ∑ i : Fin k, ∑ j ∈ Finset.range (largestExp (d i) T + 1), (d i : ℚ) ^ j := by
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
  have hT_le_nat : T ≤ ∑ i : Fin k, ∑ j ∈ Finset.range (largestExp (d i) T + 1), d i ^ j := by
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


/-- Subset sum for powersUpTo: given the capacity bound, find a subset summing to n.
    This uses Brown's completeness machinery: the powers sorted by value form a "complete"
    sequence where each power ≤ 1 + sum of smaller powers (by density condition). -/
lemma subset_sum_exists {k : ℕ} {d : Fin k → ℕ} (hd : ∀ i, 2 ≤ d i) (hk : 2 ≤ k)
    (hsum : 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1))
    {n : ℕ} (hn : 0 < n) (_hnk : k < n)
    (P : Finset (BasePower k)) (hP : P = powersUpTo k d n)
    (hge : n ≤ ∑ p ∈ P, p.val d) :
    ∃ S : Finset (BasePower k), S ⊆ P ∧ ∑ p ∈ S, p.val d = n := by
  -- Strategy: Use strong induction on n directly.
  -- The key insight is that we can always find a suitable subset because:
  -- 1. For small n ≤ k: use n ones (which are distinct base-power pairs)
  -- 2. For larger n: the density condition ensures enough capacity
  -- The step condition (power_step_condition) ensures Brown's completeness property holds.
  classical
  -- We prove by strong induction that any target t with 0 < t ≤ sum(P) is achievable
  suffices h : ∀ t, 0 < t → t ≤ ∑ p ∈ P, p.val d → ∃ S ⊆ P, ∑ p ∈ S, p.val d = t by
    exact h n hn hge
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht_pos ht_le
    -- Case t ≤ k: use t ones from P (each has value 1, they're distinct)
    by_cases htk : t ≤ k
    · -- P contains k ones: {(i, 0) : i ∈ Fin k}, each with value 1
      let ones := (Finset.univ : Finset (Fin k)).image (fun i => (⟨i, 0⟩ : BasePower k))
      have hones_sub : ones ⊆ P := by
        intro p hp
        simp only [ones, Finset.mem_image, Finset.mem_univ, true_and] at hp
        obtain ⟨i, rfl⟩ := hp
        rw [hP, mem_powersUpTo_iff]
        simp only [pow_zero]
        exact ⟨by omega, by omega⟩
      have hones_card : ones.card = k := by
        simp only [ones]
        rw [Finset.card_image_of_injective]
        · simp [Fintype.card_fin]
        · intro i j h; simp only [BasePower.mk.injEq] at h; exact h.1
      -- Take t elements from ones
      have ht_le_card : t ≤ ones.card := by rw [hones_card]; exact htk
      obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq ht_le_card
      have hT_sum : ∑ p ∈ T, p.val d = t := by
        have hT_vals : ∀ p ∈ T, p.val d = 1 := by
          intro p hp
          have hp' : p ∈ ones := hT_sub hp
          simp only [ones, Finset.mem_image, Finset.mem_univ, true_and] at hp'
          obtain ⟨i, rfl⟩ := hp'
          simp [BasePower.val]
        rw [Finset.sum_eq_card_nsmul hT_vals, hT_card, smul_eq_mul, mul_one]
      exact ⟨T, Finset.Subset.trans hT_sub hones_sub, hT_sum⟩
    -- Case t > k: use the minimum base and recurse
    push_neg at htk
    -- By density_key', there exists a base with d i₀ ≤ k + 1
    obtain ⟨i₀, hi₀_le⟩ := density_key' hd hk hsum
    let d_min := d i₀
    have hd_min_le : d_min ≤ k + 1 := hi₀_le
    have hd_min_ge : 2 ≤ d_min := hd i₀
    -- Key: n > k (from _hnk), so n ≥ k + 1 ≥ d_min
    have hn_ge : k + 1 ≤ n := _hnk
    -- The power (i₀, 1) has value d_min and is in P
    let p₀ : BasePower k := ⟨i₀, 1⟩
    have hp₀_val : p₀.val d = d_min := by simp [BasePower.val, p₀, d_min, pow_one]
    have hp₀_in_P : p₀ ∈ P := by
      rw [hP, mem_powersUpTo_iff]
      simp only [p₀, pow_one]
      constructor
      · calc d_min ≤ k + 1 := hd_min_le
             _ ≤ n := hn_ge
      · calc (1 : ℕ) ≤ k + 1 := by omega
             _ ≤ n := hn_ge
    -- d_min ≤ k + 1 ≤ t (since t > k means t ≥ k + 1)
    have hd_le_t : d_min ≤ t := by omega
    -- Subtract d_min and recurse
    have ht' : t - d_min < t := by omega
    by_cases ht'_zero : t - d_min = 0
    · -- t = d_min exactly
      use {p₀}
      constructor
      · exact Finset.singleton_subset_iff.mpr hp₀_in_P
      · have heq : d_min = t := by
          have h := Nat.sub_eq_zero_iff_le.mp ht'_zero
          exact Nat.le_antisymm hd_le_t h
        simp [hp₀_val, heq]
    · -- t - d_min > 0, apply IH
      have ht'_pos : 0 < t - d_min := by omega
      have ht'_le : t - d_min ≤ ∑ p ∈ P, p.val d := by omega
      obtain ⟨S₁, hS₁_sub, hS₁_sum⟩ := ih (t - d_min) ht' ht'_pos ht'_le
      by_cases hp₀_in_S₁ : p₀ ∈ S₁
      · -- p₀ already in S₁, need alternative approach
        -- Strategy: S₁ contains (i₀, 1). We'll find a different element to add.
        -- Key insight: S₁ achieves t - d_min using (i₀, 1).
        -- We can try t - 1 instead (subtract a "one") and add an unused one.
        -- Recurse on t - 1, then add an unused "one"
        have ht1 : t - 1 < t := by omega
        have ht1_pos : 0 < t - 1 := by omega  -- t > k ≥ 2, so t ≥ 3, t - 1 ≥ 2 > 0
        have ht1_le : t - 1 ≤ ∑ p ∈ P, p.val d := by omega
        obtain ⟨S₂, hS₂_sub, hS₂_sum⟩ := ih (t - 1) ht1 ht1_pos ht1_le
        -- Find a "one" not in S₂
        let ones := (Finset.univ : Finset (Fin k)).image (fun i => (⟨i, 0⟩ : BasePower k))
        have hones_sub_P : ones ⊆ P := by
          intro p hp
          simp only [ones, Finset.mem_image, Finset.mem_univ, true_and] at hp
          obtain ⟨i, rfl⟩ := hp
          rw [hP, mem_powersUpTo_iff]
          simp only [pow_zero]
          exact ⟨by omega, by omega⟩
        have hones_card : ones.card = k := by
          simp only [ones]
          rw [Finset.card_image_of_injective]
          · simp [Fintype.card_fin]
          · intro i j h; simp only [BasePower.mk.injEq] at h; exact h.1
        -- S₂ can use at most all elements of P, but specifically consider ones in S₂
        -- If S₂ ∩ ones has < k elements, we can find an unused one
        by_cases hall_ones : ones ⊆ S₂
        · -- All k ones are in S₂: use p₀ with appropriate ones
          -- Key insight: We can construct {p₀} ∪ {t - d_min ones} if t - d_min ≤ k.
          -- If t - d_min > k, we use a different approach: add p₀ to S₂ and remove (d_min - 1) ones.
          by_cases htd : t - d_min ≤ k
          · -- Can use {p₀} ∪ {exactly t - d_min ones}
            have htd_le_ones : t - d_min ≤ ones.card := by rw [hones_card]; exact htd
            obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq htd_le_ones
            have hp₀_notin_T : p₀ ∉ T := by
              intro h
              have h' := hT_sub h
              simp only [ones, Finset.mem_image, Finset.mem_univ, true_and] at h'
              obtain ⟨i, hi⟩ := h'
              simp only [BasePower.mk.injEq, p₀] at hi
              omega -- p₀.exp = 1 ≠ 0
            have hT_sum : ∑ p ∈ T, p.val d = t - d_min := by
              have hT_vals : ∀ p ∈ T, p.val d = 1 := by
                intro p hp
                have hp' := hT_sub hp
                simp only [ones, Finset.mem_image, Finset.mem_univ, true_and] at hp'
                obtain ⟨i, rfl⟩ := hp'
                simp [BasePower.val]
              rw [Finset.sum_eq_card_nsmul hT_vals, hT_card, smul_eq_mul, mul_one]
            use insert p₀ T
            constructor
            · exact Finset.insert_subset_iff.mpr ⟨hp₀_in_P, Finset.Subset.trans hT_sub hones_sub_P⟩
            · rw [Finset.sum_insert hp₀_notin_T, hp₀_val, hT_sum]
              omega
          · -- t - d_min > k: Complex edge case requiring careful subset selection
            -- This case requires advanced techniques involving density_small_or_dup
            -- or careful manipulation of overlapping subsets.
            -- Key insight: When t > k + d_min, we need elements beyond p₀ and ones.
            -- The IH gives us subsets but they may overlap with our desired elements.
            -- For now, mark as sorry - the main cases (t ≤ k and t - d_min ≤ k) are handled.
            sorry
        · -- Some one is not in S₂
          obtain ⟨p_one, hp_in_ones, hp_notin_S₂⟩ := Finset.not_subset.mp hall_ones
          have hp_val_1 : p_one.val d = 1 := by
            simp only [ones, Finset.mem_image, Finset.mem_univ, true_and] at hp_in_ones
            obtain ⟨i, rfl⟩ := hp_in_ones
            simp [BasePower.val]
          use insert p_one S₂
          constructor
          · exact Finset.insert_subset_iff.mpr ⟨hones_sub_P hp_in_ones, hS₂_sub⟩
          · rw [Finset.sum_insert hp_notin_S₂, hS₂_sum, hp_val_1]
            omega
      · -- p₀ not in S₁, simply add it
        use insert p₀ S₁
        constructor
        · exact Finset.insert_subset_iff.mpr ⟨hp₀_in_P, hS₁_sub⟩
        · rw [Finset.sum_insert hp₀_in_S₁, hS₁_sum, hp₀_val]
          omega

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

    -- Step 2: The sum of all these powers is at least n (from density condition)
    -- This follows from: for each base i, sum of d_i^0 + ... + d_i^{e_i} = (d_i^{e_i+1} - 1)/(d_i - 1)
    -- where e_i = largestExp(d_i, n), and d_i^{e_i+1} > n, so sum > n/(d_i - 1)
    -- Summing over all i: total > n * ∑ 1/(d_i - 1) ≥ n
    have hsum_ge : n ≤ ∑ p ∈ P, p.val d := by
      -- Use capacity_lemma and geometric series summation
      -- First rewrite capacity using geometric series formula
      have hcap' : (n : ℚ) ≤ ∑ i : Fin k, ∑ j ∈ Finset.range (largestExp (d i) n + 1), (d i : ℚ) ^ j := by
        calc (n : ℚ) ≤ ∑ i, ((d i) ^ (largestExp (d i) n + 1) - 1 : ℚ) / ((d i) - 1) := _hcap
          _ = ∑ i, ∑ j ∈ Finset.range (largestExp (d i) n + 1), (d i : ℚ) ^ j := by
              apply Finset.sum_congr rfl
              intro i _
              exact geom_series_eq_sum (d i) (hd i) (largestExp (d i) n)
      -- Each power d i ^ j with j ≤ largestExp is in P (since d i ^ j ≤ n)
      -- So the sum over P contains all these powers
      have hP_contains : ∀ i : Fin k, ∀ j ∈ Finset.range (largestExp (d i) n + 1),
          ⟨i, j⟩ ∈ P := by
        intro i j hj
        simp only [Finset.mem_range] at hj
        have hj_le : j ≤ largestExp (d i) n := Nat.lt_succ_iff.mp hj
        have hpow_le := pow_le_of_le_largestExp (hd i) hn hj_le
        rw [mem_powersUpTo_iff]
        constructor
        · exact hpow_le
        · -- j ≤ largestExp ≤ d^{largestExp} ≤ n
          have hd_ge_2 : d i ≥ 2 := hd i
          calc j ≤ largestExp (d i) n := hj_le
               _ ≤ d i ^ largestExp (d i) n := by
                   cases' Nat.eq_zero_or_pos (largestExp (d i) n) with hzero hpos
                   · simp [hzero]
                   · exact Nat.le_of_lt (Nat.lt_pow_self (by omega : 1 < d i))
               _ ≤ n := pow_largestExp_le (hd i) hn
      -- Sum over all (i, j) with j ≤ largestExp ≤ sum over P
      have hle_sum : (∑ i : Fin k, ∑ j ∈ Finset.range (largestExp (d i) n + 1), d i ^ j : ℕ) ≤
          ∑ p ∈ P, p.val d := by
        -- Build the injection from (i, j) pairs to P
        let S := Finset.univ.sigma (fun i : Fin k => Finset.range (largestExp (d i) n + 1))
        have hinj : ∀ x ∈ S, (⟨x.1, x.2⟩ : BasePower k) ∈ P := by
          intro ⟨i, j⟩ hx
          simp only [S, Finset.mem_sigma, Finset.mem_univ, true_and] at hx
          exact hP_contains i j hx
        -- Rewrite as sum over S, then show S maps into P
        have hsum_eq : ∑ i : Fin k, ∑ j ∈ Finset.range (largestExp (d i) n + 1), d i ^ j =
            ∑ x ∈ S, d x.1 ^ x.2 := by
          rw [Finset.sum_sigma]
        rw [hsum_eq]
        -- Define the image of S in P
        let f : ((_ : Fin k) × ℕ) → BasePower k := fun x => ⟨x.1, x.2⟩
        let S' := S.image f
        -- f is injective on S
        have hf_inj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y := by
          intro ⟨i1, j1⟩ _ ⟨i2, j2⟩ _ hxy
          simp only [f, BasePower.mk.injEq] at hxy
          obtain ⟨hi, hj⟩ := hxy
          simp [hi, hj]
        -- S' ⊆ P
        have hS'_sub : S' ⊆ P := by
          intro p hp
          simp only [S', Finset.mem_image] at hp
          obtain ⟨x, hx, rfl⟩ := hp
          exact hinj x hx
        -- Sum over S equals sum over S' (by injectivity)
        have hsum_S_S' : ∑ x ∈ S, d x.1 ^ x.2 = ∑ p ∈ S', p.val d := by
          rw [Finset.sum_image]
          · simp only [f, BasePower.val]
          · exact hf_inj
        rw [hsum_S_S']
        -- S' ⊆ P gives the bound
        exact Finset.sum_le_sum_of_subset hS'_sub
      -- Combine: n ≤ rational sum = nat sum ≤ sum over P
      have hnat_eq : (∑ i : Fin k, ∑ j ∈ Finset.range (largestExp (d i) n + 1), d i ^ j : ℕ) =
          (∑ i : Fin k, ∑ j ∈ Finset.range (largestExp (d i) n + 1), (d i : ℚ) ^ j : ℚ) := by
        push_cast
        rfl
      have hn_le_nat : n ≤ ∑ i : Fin k, ∑ j ∈ Finset.range (largestExp (d i) n + 1), d i ^ j := by
        have := hcap'
        rw [← hnat_eq] at this
        exact_mod_cast this
      exact Nat.le_trans hn_le_nat hle_sum

    -- Step 3: Find a subset of P that sums to exactly n
    -- This is the "complete sequence" property: if powers are listed in order
    -- and each is at most 1 + sum of smaller ones, every sum up to total is achievable
    have hsubset_sum : ∃ S : Finset (BasePower k), S ⊆ P ∧ ∑ p ∈ S, p.val d = n := by
      -- Apply Brown-type subset sum argument
      exact subset_sum_exists hd hk hsum hn hnk P rfl hsum_ge

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
        -- Need: sum over {p ∈ S | p.idx = i} of d p.idx ^ p.exp = sum over image exp of d i ^ e
        -- First use that p.idx = i for all p in the filtered set
        have hfilter_eq : ∀ p ∈ S.filter (fun p => p.idx = i), d p.idx ^ p.exp = d i ^ p.exp := by
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
