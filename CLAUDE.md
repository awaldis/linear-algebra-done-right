# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Lean 4 formal mathematics project containing selected proofs from Sheldon Axler's "Linear Algebra Done Right" (4th edition). Proofs prioritize **human readability** over brevity—avoid tactics that shorten proofs at the cost of understandability.

Reference: https://linear.axler.net/

## Build Commands

All commands run from repository root:

```bash
# Download and cache Mathlib (after dependency changes)
lake exe cache get

# Full build and type-check (this is the test suite)
lake build

# Quick check of umbrella module
lake env lean --make LinearAlgebraDoneRight.lean

# Check specific file while iterating
lake env lean --make LinearAlgebraDoneRight/LADR4e_1_46_direct_sum_of_two_subspaces.lean
```

## Project Structure

- **LinearAlgebraDoneRight/** - Source directory with individual proof files
- **LinearAlgebraDoneRight.lean** - Umbrella module that imports all published proofs
- **lakefile.toml** - Build configuration with Lean compiler options
- **lean-toolchain** - Pinned Lean version

### File Naming

- Theorems: `LADR4e_<section>_<description>.lean` (e.g., `LADR4e_1_46_direct_sum_of_two_subspaces.lean`)
- Exercises: `LADR4e_<section>_Exercise_<number>.lean` (e.g., `LADR4e_3_Exercise_1A_14.lean`)
- Each theorem/exercise lives in its own file

## Coding Style

### Lean Configuration (from lakefile.toml)

```lean
autoImplicit = false           # Must explicitly declare all implicit arguments
relaxedAutoImplicit = false
pp.unicode.fun = true          # Pretty-prints `fun a ↦ b`
```

### Formatting

- **Indentation**: Two spaces (Mathlib standard)
- **Spacing**: One blank line between declarations
- **Docstrings**: Use `/-! … -/` block comments at file start, referencing Axler's book
- **Variables**: Always spell out implicit arguments and binders due to `autoImplicit = false`

### Naming Conventions

- **Modules**: PascalCase matching filenames
- **Theorems/Functions**: `snake_case_that_reflects_claim`
  - Example: `if_direct_sum_then_2_subspace_intersect_only_zero`
  - For simple exercises: often named `main`

### Proof Style

- **Optimize for human understanding**, not proof length
- **Use explicit tactics** like `calc` that expose proof steps in code (avoid forcing reader to check infoview)
- **Avoid tactics that don't have a specific justification**, e.g. "rfl" and "simp"
- **Generous comments** explaining each step unless very obvious
- **Prefer step-by-step rewrites** over inline tactic chains
- **Add comments** linking helper lemmas to book results

### Example Pattern

```lean
import Mathlib.Algebra.Field.Basic
/-!
# Exercise 1A.14 - distributivity of scalar multiplication
## From:
Sheldon Axler. [Linear Algebra Done Right](https://linear.axler.net),
fourth edition, Springer, 2024
-/

variable {𝔽 : Type*} [Field 𝔽]
variable {n : ℕ}

theorem dist_of_smul_wrt_vec_add : α • (x + y) = α • x + α • y := by
calc α • (x + y)
    -- Unfold pointwise addition
    = α • (fun i => x i + y i) := by rw [Pi.add_def]
  -- Distribute scalar multiplication
  _ = fun i => α • (x i + y i) := by rw [Pi.smul_def]
  ...
```

## Development Workflow

1. Create new file in `LinearAlgebraDoneRight/` following naming convention
2. Add imports from Mathlib
3. Include docstring referencing Axler's book
4. Write proof with explicit variable declarations and comments
5. Add import to `LinearAlgebraDoneRight.lean` when ready to publish
6. Run `lake build` to verify

## Testing

Lean type-checking **is** the test suite. Ensure `lake build` passes before committing. New files must be imported by `LinearAlgebraDoneRight.lean` to be covered by CI.

## Commit Guidelines

Use concise Title Case commit messages:
- "Change 1A.14 to Use More Specific Justifications"
- "Add Proof for Exercise 1B.3"
- Front-load the affected section or topic

## Dependencies

- **Lean**: Version specified in `lean-toolchain` (currently v4.24.0)
- **Mathlib**: Standard library for Lean 4 mathematics
- **Lake**: Lean's build system and package manager
