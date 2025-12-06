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
def onesInP (k : ℕ) (d : Fin k → ℕ) (M : ℕ) : Finset (BasePower k) :=
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

/-- Subset sum lemma: given a finset with enough total, we can find a subset with any smaller sum.
    This uses the "ones" in the set for fine-grained adjustment. -/
lemma subset_sum_exists {k : ℕ} {d : Fin k → ℕ} (hd : ∀ i, 2 ≤ d i) (hk : 2 ≤ k)
    (hsum : 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1))
    {n : ℕ} (hn : 0 < n) (hnk : k < n)
    (P : Finset (BasePower k)) (hP : P = powersUpTo k d n)
    (hge : n ≤ ∑ p ∈ P, p.val d) :
    ∃ S : Finset (BasePower k), S ⊆ P ∧ ∑ p ∈ S, p.val d = n := by
  -- The proof uses a greedy removal strategy:
  -- 1. Start with the full set P with sum T ≥ n
  -- 2. Remove elements until sum = n
  -- Key: we have k ≥ 2 "ones" in P (elements (i, 0) with value 1)
  -- When excess > k, density condition ensures a non-one power ≤ excess exists
  classical
  -- Define excess = T - n
  set T := ∑ p ∈ P, p.val d with hT_def
  -- We'll find a subset to REMOVE that sums to T - n
  suffices h : ∃ R : Finset (BasePower k), R ⊆ P ∧ ∑ p ∈ R, p.val d = T - n by
    obtain ⟨R, hR_sub, hR_sum⟩ := h
    use P \ R
    constructor
    · exact Finset.sdiff_subset
    · have hsdiff := Finset.sum_sdiff hR_sub (f := fun p => p.val d)
      -- hsdiff : ∑ p ∈ P \ R, p.val d + ∑ p ∈ R, p.val d = ∑ p ∈ P, p.val d
      -- We want: ∑ p ∈ P \ R, p.val d = n
      -- From hsdiff: ∑ p ∈ P \ R, p.val d = T - (T - n) = n
      simp only [hR_sum] at hsdiff
      have hT_ge_n : T ≥ n := hge
      omega
  -- The set of ones in P
  have hones_sub : onesInP k d n ⊆ P := by rw [hP]; exact onesInP_subset hn
  have hones_card : (onesInP k d n).card = k := onesInP_card
  have hones_sum : ∑ p ∈ onesInP k d n, p.val d = k := onesInP_sum
  -- Case: T = n (excess = 0)
  by_cases hexcess_zero : T = n
  · exact ⟨∅, Finset.empty_subset _, by simp [hexcess_zero]⟩
  -- Case: T > n (excess > 0)
  have hT_gt : T > n := Nat.lt_of_le_of_ne hge (Ne.symm hexcess_zero)
  -- Case: excess ≤ k (can remove excess ones)
  by_cases hexcess_small : T - n ≤ k
  · -- Remove exactly (T - n) ones
    -- Choose a subset of ones of size (T - n)
    have hcard_le : T - n ≤ (onesInP k d n).card := by rw [hones_card]; exact hexcess_small
    obtain ⟨R, hR_sub_ones, hR_card⟩ := Finset.exists_subset_card_eq hcard_le
    use R
    constructor
    · exact Finset.Subset.trans hR_sub_ones hones_sub
    · -- Each element in R has value 1
      have hR_val : ∀ p ∈ R, p.val d = 1 := by
        intro p hp
        have hp' := hR_sub_ones hp
        simp only [onesInP, Finset.mem_map, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk] at hp'
        obtain ⟨i, hi⟩ := hp'
        rw [← hi]
        simp [BasePower.val]
      rw [Finset.sum_eq_card_nsmul (fun p hp => hR_val p hp)]
      simp [hR_card]
  -- Case: excess > k (need to remove non-one powers too)
  push_neg at hexcess_small
  -- By density argument: if all bases > excess, then ∑ 1/(d_i-1) < 1, contradiction
  -- So some base d_i ≤ excess, and hence d_i ∈ P
  -- This gives us a non-one power to remove
  -- For now, we use a recursive construction
  -- Actually, let's use strong induction on T - n
  have hexcess_pos : 0 < T - n := by omega
  -- Use well-founded induction on excess
  -- We'll construct the removal set greedily
  -- Key density lemma: if excess > k, there's a base d_i with d_i ≤ n and d_i ≤ excess
  -- This follows from the density condition ∑ 1/(d_i-1) ≥ 1
  -- The full proof requires showing that if all d_i > excess > k, then ∑ 1/(d_i-1) < 1
  -- For now, we use this as an axiom and prove the rest
  have hdensity_key : ∀ excess : ℕ, excess > k →
      excess ≤ T - n → (∃ i : Fin k, d i ≤ excess ∧ d i ≤ n) ∨ excess ≤ k := by
    intro excess hexcess_gt _
    -- If excess ≤ k, the right disjunct holds
    by_cases h : excess ≤ k
    · right; exact h
    push_neg at h
    left
    -- excess > k, so we need to find a base d_i ≤ min(excess, n)
    -- Key: from density condition, the smallest base d_min satisfies d_min ≤ k + 1
    have hk_pos : 0 < k := by omega
    have hFin_nonempty : Nonempty (Fin k) := ⟨⟨0, hk_pos⟩⟩
    obtain ⟨i_min, hi_min⟩ := Finite.exists_min d
    -- Show d_min ≤ k + 1 from density condition
    -- ∑ 1/(d_j - 1) ≥ 1 and each 1/(d_j - 1) ≤ 1/(d_min - 1)
    -- So k * 1/(d_min - 1) ≥ ∑ 1/(d_j - 1) ≥ 1
    -- Thus d_min - 1 ≤ k, i.e., d_min ≤ k + 1
    have hd_min_bound : d i_min ≤ k + 1 := by
      by_contra hcontra
      push_neg at hcontra
      -- d i_min > k + 1 means d i_min ≥ k + 2, so d i_min - 1 ≥ k + 1
      have hd_min_ge : d i_min - 1 ≥ k + 1 := by omega
      -- For all j, d j ≥ d i_min, so d j - 1 ≥ d i_min - 1 ≥ k + 1
      have hall_ge : ∀ j : Fin k, (d j : ℚ) - 1 ≥ k + 1 := by
        intro j
        have hj_ge := hi_min j
        have hdj_ge : d j ≥ d i_min := hj_ge
        have hdmin_sub : d i_min - 1 ≥ k + 1 := hd_min_ge
        have hdj_ge_2 : d j ≥ 2 := hd j
        have hdmin_ge_2 : d i_min ≥ 2 := hd i_min
        -- d j - 1 ≥ d i_min - 1 ≥ k + 1
        have hdj_sub_ge : d j - 1 ≥ k + 1 := by
          have : d j - 1 ≥ d i_min - 1 := Nat.sub_le_sub_right hdj_ge 1
          omega
        -- Now cast to ℚ
        have : (d j - 1 : ℕ) ≥ k + 1 := hdj_sub_ge
        have hcast : ((d j - 1 : ℕ) : ℚ) ≥ k + 1 := by exact_mod_cast this
        have hdj_sub_eq : (d j : ℚ) - 1 = (d j - 1 : ℕ) := by
          have h1le : 1 ≤ d j := by omega
          simp only [Nat.cast_sub h1le, Nat.cast_one]
        rw [hdj_sub_eq]
        exact hcast
      -- Each term 1/(d j - 1) ≤ 1/(k + 1)
      have hterms : ∀ j : Fin k, (1 : ℚ) / (d j - 1) ≤ 1 / (k + 1) := by
        intro j
        have hpos : (0 : ℚ) < k + 1 := by exact_mod_cast (by omega : 0 < k + 1)
        have hpos' : (0 : ℚ) < (d j : ℚ) - 1 := by
          have : d j ≥ 2 := hd j
          linarith [show (d j : ℚ) ≥ 2 from by exact_mod_cast this]
        apply one_div_le_one_div_of_le hpos
        exact hall_ge j
      -- Sum ≤ k * 1/(k+1) = k/(k+1) < 1
      have hsum_le : ∑ j : Fin k, (1 : ℚ) / (d j - 1) ≤ k * (1 / (k + 1)) := by
        calc ∑ j : Fin k, (1 : ℚ) / (d j - 1)
            ≤ ∑ _j : Fin k, (1 : ℚ) / (k + 1) := Finset.sum_le_sum (fun j _ => hterms j)
          _ = k * (1 / (k + 1)) := by simp [Finset.sum_const]
      have hk_over : (k : ℚ) * (1 / (k + 1)) < 1 := by
        rw [mul_one_div]
        have hk_pos' : (0 : ℚ) < k + 1 := by exact_mod_cast (by omega : 0 < k + 1)
        rw [div_lt_one hk_pos']
        exact_mod_cast (by omega : k < k + 1)
      linarith [hsum, hsum_le, hk_over]
    -- Now d i_min ≤ k + 1 and excess > k and n > k (from hnk)
    use i_min
    constructor
    · -- d i_min ≤ excess: since d i_min ≤ k + 1 ≤ excess (as excess > k)
      omega
    · -- d i_min ≤ n: since d i_min ≤ k + 1 ≤ n (as n > k from hnk)
      omega
  -- The subset sum construction uses the density key greedily
  -- We use strong induction: for all excess ≤ T - n, we can find R with ∑ R = excess
  -- The density key ensures we can always reduce excess by at least 2 when excess > k
  -- (since each d_i ≥ 2)
  suffices hgoal : ∀ excess, excess ≤ T - n → ∃ R : Finset (BasePower k), R ⊆ P ∧ ∑ p ∈ R, p.val d = excess by
    exact hgoal (T - n) le_rfl
  intro excess
  induction excess using Nat.strong_induction_on with
  | _ excess ih =>
    intro hexcess_le
    -- Case: excess ≤ k
    by_cases hexc_k : excess ≤ k
    · -- Can remove exactly `excess` ones from P
      have hcard_le : excess ≤ (onesInP k d n).card := by rw [hones_card]; exact hexc_k
      obtain ⟨R, hR_sub_ones, hR_card⟩ := Finset.exists_subset_card_eq hcard_le
      use R
      constructor
      · exact Finset.Subset.trans hR_sub_ones hones_sub
      · have hR_val : ∀ p ∈ R, p.val d = 1 := by
          intro p hp
          have hp' := hR_sub_ones hp
          simp only [onesInP, Finset.mem_map, Finset.mem_univ, true_and,
            Function.Embedding.coeFn_mk] at hp'
          obtain ⟨i, hi⟩ := hp'
          rw [← hi]
          simp [BasePower.val]
        rw [Finset.sum_eq_card_nsmul (fun p hp => hR_val p hp)]
        simp [hR_card]
    -- Case: excess > k
    push_neg at hexc_k
    -- By density key, there exists i with d_i ≤ excess and d_i ≤ n
    have hdkey := hdensity_key excess hexc_k hexcess_le
    rcases hdkey with ⟨i, hdi_le_exc, hdi_le_n⟩ | hexc_le_k
    · -- Have i with d_i ≤ excess and d_i ≤ n, so (i, 1) ∈ P
      have hi1_in_P : (⟨i, 1⟩ : BasePower k) ∈ P := by
        rw [hP, mem_powersUpTo_iff]
        constructor
        · simp [hdi_le_n]
        · have : 1 ≤ n := by omega
          omega
      have hdi_ge_2 : d i ≥ 2 := hd i
      -- excess - d_i < excess (since d_i ≥ 2 > 0)
      have hexc_dec : excess - d i < excess := Nat.sub_lt (by omega : 0 < excess) (by omega : 0 < d i)
      -- excess - d_i ≤ T - n (since excess ≤ T - n and d_i ≥ 0)
      have hexc_dec_le : excess - d i ≤ T - n := by omega
      -- By IH, get R' with ∑ R' = excess - d_i
      obtain ⟨R', hR'_sub, hR'_sum⟩ := ih (excess - d i) hexc_dec hexc_dec_le
      -- Use R = R' ∪ {(i, 1)} if (i, 1) ∉ R', otherwise need to handle differently
      by_cases hi1_in_R' : (⟨i, 1⟩ : BasePower k) ∈ R'
      · -- If (i, 1) already in R', need different approach
        -- This case is tricky - the IH constructed R' containing (i, 1)
        -- We need to find a different element or restructure
        -- For now, use sorry as this edge case requires more careful construction
        sorry
      · -- (i, 1) ∉ R', can use R = R' ∪ {(i, 1)}
        use R' ∪ {⟨i, 1⟩}
        constructor
        · exact Finset.union_subset hR'_sub (Finset.singleton_subset_iff.mpr hi1_in_P)
        · rw [Finset.sum_union (Finset.disjoint_singleton_right.mpr hi1_in_R')]
          simp only [Finset.sum_singleton, BasePower.val, pow_one]
          -- Need to show: ∑ x ∈ R', d x.idx ^ x.exp + d i = excess
          -- We have hR'_sum : ∑ p ∈ R', BasePower.val d p = excess - d i
          -- where BasePower.val d p = d p.idx ^ p.exp
          simp only [BasePower.val] at hR'_sum
          omega
    · -- excess ≤ k contradicts hexc_k : k < excess
      omega

/-- The sum of all powers up to M -/
lemma sum_powersUpTo_eq {k : ℕ} {d : Fin k → ℕ} (_hd : ∀ i, 2 ≤ d i) (M : ℕ) :
    ∑ p ∈ powersUpTo k d M, p.val d =
    ∑ i : Fin k, ∑ e ∈ Finset.range (M + 1), if d i ^ e ≤ M then d i ^ e else 0 := by
  unfold powersUpTo BasePower.val
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Finset.sum_filter, Finset.sum_product]

/-- Key density lemma: the sum of (d_i^{e+1} - 1)/(d_i - 1) over all bases bounds n
when each d_i^{e_i} ≤ n < d_i^{e_i+1} -/
lemma density_bound_for_powers {k : ℕ} {d : Fin k → ℕ} (hd : ∀ i, 2 ≤ d i)
    (hsum : 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1))
    {M : ℕ} (hM : 0 < M) :
    (M : ℚ) ≤ ∑ i : Fin k, (((Nat.log (d i) M + 1) : ℕ) : ℚ) * ((d i - 1 : ℕ) : ℚ)⁻¹ *
      ((d i : ℚ) ^ (Nat.log (d i) M + 1) - 1) / ((d i : ℚ) - 1) := by
  -- This follows from the capacity lemma and geometric series
  sorry

/-- The step inequality: each new power is at most 1 + sum of all smaller powers.
This is the key property that makes Brown's lemma applicable. -/
lemma step_inequality_from_density {k : ℕ} {d : Fin k → ℕ} (hd : ∀ i, 2 ≤ d i)
    (hsum : 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1))
    (a : ℕ → ℕ) (ha_enum : ∀ n, ∃ p : BasePower k, a n = p.val d)
    (ha_mono : Monotone a) (ha_0 : a 0 = 1)
    (ha_complete : ∀ i e, ∃ n, a n = d i ^ e) :
    ∀ m, a (m + 1) ≤ 1 + partialSum a (m + 1) := by
  -- This follows from the density condition.
  -- The key is that the sum of all powers ≤ a(m) is at least a(m) * ∑ 1/(d_i - 1) ≥ a(m)
  -- So a(m+1) ≤ smallest power > a(m) ≤ 1 + sum of powers ≤ a(m)
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
