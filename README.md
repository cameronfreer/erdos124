# Erdős Problem 124 (Solved Variant) - Lean 4 Formalization

A complete Lean 4 formalization of Erdős Problem 124 using Mathlib.

**Note:** This formalizes the "solved/weak" variant discussed in the [forum thread](https://www.erdosproblems.com/forum/thread/124#post-1892), which allows using 1 = d^0 from each base. This is **not** the open BEGL96/gcd/k≥1 conjecture.

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

This direction (sum of distinct powers → uses only 0,1 digits) is shown by `usesOnlyZeroOne_sum_distinct_powers`.

### Proof Structure

#### 1. Special Case: Base 2 Exists

If any base d(i) = 2, the problem is trivial: every natural number has a binary representation using only digits 0 and 1. Use binary for that base, zeros for all others.

#### 2. Main Case: All Bases ≥ 3

When all bases are at least 3, the density condition forces k ≥ 2 bases.

**Cases by n:**
- **n = 0:** Use a(i) = 0 for all i.
- **n ≤ k:** Use n ones from n different bases (each d(i)^0 = 1).
- **n > k:** Apply Brown's completeness machinery via `subset_sum_exists`.

**Brown's approach for n > k:**

The key insight is that powers d(i)^e ≤ n, when sorted by value, form a "complete sequence" satisfying Brown's step condition: each power v ≤ 1 + (sum of all smaller powers). This follows from the density condition ensuring enough small powers exist (`power_step_condition`).

1. Collect all powers P = {(i, e) : d(i)^e ≤ n} across all bases
2. The density condition ensures ∑_{p ∈ P} p.val ≥ n (`sum_powers_at_least`)
3. Sort P by value and apply Brown's finite completeness lemma (`brown_achievable_range`)
4. This yields a subset S ⊆ P with ∑_{p ∈ S} p.val = n
5. Group chosen powers by base index to get the final a(i) values

### Key Technical Lemmas

- **`brown_complete`:** Brown's completeness lemma - if a sequence satisfies a(n+1) ≤ 1 + ∑_{j≤n} a(j) with a(0)=1, every natural is a finite subsequence sum
- **`capacity_lemma`:** The density condition implies sufficient total capacity of powers
- **`density_key'`:** From the density condition, the minimum base satisfies d_min ≤ k+1
- **`density_small_or_dup`:** Either the minimum base is small (≤ k), or there's a duplicate base value
- **`usesOnlyZeroOne_sum_distinct_powers`:** Sums of distinct powers use only 0/1 digits

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
lake build
```

For faster builds with cached Mathlib:
```bash
lake exe cache get
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
- [Problem formulation (forum post)](https://www.erdosproblems.com/forum/thread/124#post-1892) - precise statement this proof addresses
- J. L. Brown, Jr. ["Note on Complete Sequences of Integers"](https://www.jstor.org/stable/2311150), American Mathematical Monthly, 68 (1961), pp. 557-560. (Original source of Brown's completeness criterion)
- J. L. Brown, Jr. ["Some Sequence-to-Sequence Transformations which Preserve Completeness"](https://www.fq.math.ca/Scanned/16-1/brown1.pdf), The Fibonacci Quarterly, Vol. 16, No. 1 (1978), pp. 19-22. (Applies the criterion)

**Note on page typo:** The displayed inequality on the ErdősProblems page currently has a typo (d_r instead of d_i); the correct hypothesis ∑_i 1/(d_i-1) ≥ 1 is used in the thread and here.

**Note on formulation:** The forum post states the problem for strictly increasing bases d₁ < d₂ < ... < dᵣ (each ≥ 3) and asks about "sufficiently large" integers. Our formalization is a slight generalization: it allows any bases ≥ 2 (including duplicates) and proves the result for **all** natural numbers. When any base equals 2, the result is trivial (binary representation); the interesting case with all bases ≥ 3 is handled by Brown's completeness machinery.

## Version Information

- **Lean:** v4.26.0
- **Mathlib:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

## License

MIT License. See [LICENSE](LICENSE) file.

## Acknowledgments

This formalization was developed with AI assistance:
- Primary implementation: Claude Opus 4.5
- Planning: GPT 5.1 Pro
- Final refinements: GPT 5.2

Tools used:
- [Lean 4 Skills for Claude](https://github.com/cameronfreer/lean4-skills/tree/main/plugins/lean4-theorem-proving) - Claude Code plugin for Lean 4 theorem proving
- [Lean LSP MCP](https://github.com/oOo0oOo/lean-lsp-mcp) - Model Context Protocol server for Lean language server integration
