# Erdos Problem 124 - Lean 4 Formalization

A complete Lean 4 formalization of Erdos Problem 124 using Mathlib.

## Problem Statement

**Erdos Problem 124:** Given k bases d(i) (each >= 2) such that

```
sum_{i=1}^k 1/(d(i) - 1) >= 1
```

every natural number n can be written as a sum of k numbers a(i), where each a(i) uses only digits 0 and 1 in base d(i).

### Formal Statement

```lean
theorem erdos_124 : forall k : Nat, forall d : Fin k -> Nat,
    (forall i, 2 <= d i) ->
    1 <= sum i : Fin k, (1 : Rat) / (d i - 1) ->
    forall n : Nat, exists a : Fin k -> Nat,
      (forall i, usesOnlyZeroOne (d i) (a i)) /\ n = sum i, a i
```

## Proof Strategy

The proof uses a **subset sum construction** on the set of all powers d_i^e <= n across all bases.

### Key Insight

Numbers using only digits 0 and 1 in base b are exactly sums of distinct powers of b:
```
a uses only {0,1} digits in base b  <=>  a = sum_{e in S} b^e for some S with disjoint powers
```

So we need to select, for each base d_i, a subset of its powers such that the total sum equals n.

### Proof Structure

#### 1. Special Case: Base 2 Exists

If any base d_i = 2, the problem is trivial: every natural number has a binary representation using only digits 0 and 1. Use binary for that base, zeros for all others.

#### 2. Main Case: All Bases >= 3

When all bases are at least 3, the density condition forces k >= 2 bases.

**Strong induction on n:**

- **Base case (n = 0):** Use a_i = 0 for all i.

- **Case n <= k:** Use n "ones" (the d_i^0 = 1 terms) from n different bases.

- **Case n > k:** This is the core difficulty. Use the **Brown completeness approach**:

  1. **Define power set P:** Collect all pairs (i, e) where d_i^e <= n

  2. **Capacity lemma:** The density condition ensures sum_{p in P} p.val >= n

  3. **Existence via induction:** Construct a subset S of P summing to exactly n
     - If excess := (sum P) - n is small (<= k), handle with "ones"
     - Otherwise, find the minimum base and recurse on n - d_min

#### 3. Key Technical Lemmas

- **`density_key`:** From the density condition, the minimum base satisfies d_min <= k + 1
- **`density_small_or_dup`:** Either the minimum base is small (<= k), or there's a duplicate base value
- **`capacity_lemma`:** The total capacity of all powers up to n exceeds n
- **`brown_complete`:** Complete sequence theorem for subset sum existence

### Edge Cases

The proof handles several intricate edge cases:
- When recursively-built sets already contain needed powers
- When duplicate base values provide alternative decomposition paths
- Disjointness/overlap of "ones" sets across recursive calls

## File Structure

```
Erdos124.lean          # Main formalization (~1400 lines)
lakefile.lean          # Lake build configuration
lake-manifest.json     # Dependency lock file
```

### Main Definitions

- `usesOnlyZeroOne b n`: Predicate that n uses only 0,1 digits in base b
- `BasePower k`: Structure pairing a base index with an exponent
- `powersUpTo k d n`: All powers d_i^e <= n across k bases
- `onesInP k d n`: The "ones" subset {(i, 0) : i < k}

### Main Theorems

- `erdos_124`: The main theorem
- `erdos_124_with_base2`: Special case when base 2 exists
- `brown_complete`: Complete sequence subset sum theorem
- `capacity_lemma`: Density condition implies sufficient capacity
- `density_key`: Minimum base bound from density

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

- [Erdos Problems - Problem 124](https://www.erdosproblems.com/124)
- Brown, T.C. "Complete sequences of natural numbers" (for the subset sum approach)

## Technical Notes

### Grind Tactic

Several edge cases are resolved using Lean 4's `grind` tactic with suggestions enabled. This handles complex case splits involving:
- Set membership conflicts
- Arithmetic inequalities from the density condition
- Disjointness arguments

### Development Approach

This formalization was developed iteratively:
1. Established the core structure using `subset_sum_via_induction`
2. Proved special cases (base 2, small n)
3. Built supporting lemmas for density bounds
4. Handled edge cases via careful case analysis
5. Finalized proofs using `grind +suggestions` for remaining goals
