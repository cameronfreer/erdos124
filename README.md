# Erdős Problem 124 - Lean 4 Formalization

A complete Lean 4 formalization of Erdős Problem 124 using Mathlib.

## Problem Statement

**Erdős Problem 124:** Given k bases d(i) (each ≥ 2) such that

```
∑_{i=1}^k 1/(d(i) - 1) ≥ 1
```

every natural number n can be written as a sum of k numbers a(i), where each a(i) uses only digits 0 and 1 in base d(i).

### Formal Statement

```lean
theorem erdos_124 (k : ℕ) (d : Fin k → ℕ)
    (hd : ∀ i, 2 ≤ d i)
    (hdens : 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1)) :
  ∀ n : ℕ, ∃ a : Fin k → ℕ,
    (∀ i, usesOnlyZeroOne (d i) (a i)) ∧ n = ∑ i, a i
```

where `usesOnlyZeroOne b n` is defined via `Nat.digits b n` - a number uses only 0/1 digits if every digit in its base-b representation is 0 or 1.

## Proof Strategy

### Key Insight

Numbers using only digits 0 and 1 in base b are exactly sums of distinct powers of b:
```
a uses only {0,1} digits in base b  ↔  a = ∑_{e ∈ S} b^e for some finite S ⊆ ℕ
```

This equivalence is captured by `usesOnlyZeroOne_sum_distinct_powers`.

### Proof Structure

#### 1. Special Case: Base 2 Exists

If any base d(i) = 2, the problem is trivial: every natural number has a binary representation using only digits 0 and 1. Use binary for that base, zeros for all others.

#### 2. Main Case: All Bases ≥ 3

When all bases are at least 3, the density condition forces k ≥ 2 bases.

The proof proceeds by **strong induction on n**, constructing a finite set S of base-power pairs `(i, e)` where each `d(i)^e ≤ n`, such that `∑_{(i,e) ∈ S} d(i)^e = n` and no two elements share the same base index with different exponents that would overlap.

**Base cases:**
- **n = 0:** Use a(i) = 0 for all i.
- **n ≤ k:** Use n copies of d(i)^0 = 1 from n different bases (the "ones").

**Inductive case (n > k):**
1. Find the minimum base d(i₀) using `density_key'`: the density condition ensures d(i₀) ≤ k+1.
2. Apply the induction hypothesis to n - d(i₀) to get a subset S'.
3. If (i₀, 1) ∉ S', add it and we're done.
4. If (i₀, 1) ∈ S', use `density_small_or_dup` which gives two sub-cases:
   - Either d(i₀) ≤ k, allowing alternative constructions using "ones"
   - Or there exists j ≠ i₀ with d(j) = d(i₀), providing an alternative base

The proof handles several edge cases when recursive constructions conflict with the current base's powers.

### Key Technical Lemmas

- **`brown_complete`:** Brown's completeness lemma - if a sequence satisfies a(n+1) ≤ 1 + ∑_{j≤n} a(j) with a(0)=1, every natural is a finite subsequence sum
- **`capacity_lemma`:** The density condition implies sufficient total capacity of powers
- **`density_key'`:** From the density condition, the minimum base satisfies d_min ≤ k+1
- **`density_small_or_dup`:** Either the minimum base is small (≤ k), or there's a duplicate base value
- **`usesOnlyZeroOne_sum_distinct_powers`:** Equivalence between 0/1 digits and sums of distinct powers

## File Structure

```
Erdos124.lean          # Main formalization (~1100 lines)
lakefile.lean          # Lake build configuration
lake-manifest.json     # Dependency lock file
```

### Main Definitions

- `usesOnlyZeroOne b n`: Predicate that n uses only 0,1 digits in base b (via `Nat.digits`)
- `BasePower k`: Structure pairing a base index (Fin k) with an exponent (ℕ)
- `BasePower.val d p`: The value d(p.idx)^(p.exp) of a base-power pair
- `powersUpTo k d M`: All base-power pairs with value ≤ M
- `onesInP k d M`: The "ones" subset {(i, 0) : i < k}

### Main Theorems

- `erdos_124`: The main theorem
- `brown_complete`: Complete sequence theorem for subset sum existence
- `capacity_lemma`: Density condition implies sufficient capacity
- `density_key'`: Minimum base bound from density
- `density_small_or_dup`: Key case split lemma

## Building

```bash
lake update
lake build
```

## Verification

The proof is complete with no `sorry` placeholders. All axioms used are standard Mathlib axioms (propext, Quot.sound, Classical.choice).

Check axioms:
```bash
lake env lean --run <<EOF
import Erdos124
#print axioms erdos_124
EOF
```

## References

- [Erdős Problems - Problem 124](https://www.erdosproblems.com/124)
- J. L. Brown, Jr. ["Note on Complete Sequences of Integers"](https://www.jstor.org/stable/2311150), American Mathematical Monthly, 68 (1961), pp. 557-560. (Original source of Brown's completeness criterion)
- J. L. Brown, Jr. ["Some Sequence-to-Sequence Transformations which Preserve Completeness"](https://www.fq.math.ca/Scanned/16-1/brown1.pdf), The Fibonacci Quarterly, Vol. 16, No. 1 (1978), pp. 19-22. (Applies the criterion)

## Technical Notes

### Grind Tactic

Several edge cases in the strong induction are resolved using Lean 4's `grind` tactic. This handles complex case splits involving:
- Set membership conflicts
- Arithmetic inequalities from the density condition
- Disjointness arguments between constructed subsets

### Development Approach

This formalization was developed iteratively:
1. Established the digit equivalence (`usesOnlyZeroOne_sum_distinct_powers`)
2. Proved Brown's completeness lemma
3. Built density bound lemmas (`density_key'`, `density_small_or_dup`)
4. Structured the main proof via strong induction
5. Handled edge cases via case analysis and `grind`
