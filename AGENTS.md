# Repository Guidelines

## Project Structure & Module Organization
This Lean 4 project is driven by `lakefile.toml` and `lean-toolchain` at the repository root; they pin the Lean toolchain and pull in Mathlib. The umbrella module `LinearAlgebraDoneRight.lean` re-exports the proofs housed in `LinearAlgebraDoneRight/`. Each theorem or exercise lives in its own file named `LADR4e_<section>_<short_description>.lean`, mirroring Axler’s section numbers. Keep supporting scratch work in `Basic.lean` or a similarly named staging file, and remove it from the umbrella import list before merging. The `docbuild/` directory mirrors the toolchain configuration used for documentation builds—touch it only when updating the doc pipeline.

## Build, Test, and Development Commands
- `lake exe cache get`: hydrate the Mathlib cache after changing dependencies or switching toolchains.
- `lake build`: compile the entire library and type-check all imported proofs.
- `lake env lean --make LinearAlgebraDoneRight.lean`: quick end-to-end check without rebuilding artifacts.
- `lake env lean --make LinearAlgebraDoneRight/LADR4e_1_46_direct_sum_of_two_subspaces.lean`: targeted check while iterating on one theorem.
Run commands from the repository root so the module paths resolve correctly.

## Coding Style & Naming Conventions
Formatting follows Mathlib’s Lean style: two-space indentation, one blank line between declarations, and docstrings introduced with `/-! … -/`. With `autoImplicit = false`, always spell out implicit arguments and binders. Give modules PascalCase names (matching filenames) and theorem identifiers snake_case that reflects the claim, e.g., `if_direct_sum_then_2_subspace_intersect_only_zero`. Do not optimize for brevity. Instead, optimize for understandability by a human reader who is a novice at both linear algebra and Lean. Be generous with comments that explains the purpose of each line unless it's very obvious. Use tactics like "calc" that explicitly expose the proof steps in the code rather than forcing the reader to look in the infoview.

## Testing Guidelines
Lean type-checking is the test suite. Ensure `lake build` passes before committing. For new files, add them to `LinearAlgebraDoneRight.lean` so they are covered by the aggregated build. When introducing helper lemmas, add a brief comment citing the exact result or exercise they support, and keep proofs minimal so Mathlib upgrades cause fewer merge conflicts.

## Commit & Pull Request Guidelines
Recent history uses concise, Title Case summaries such as “Change 1A.14 to Use More Specific Justifications.” Follow that pattern, front-loading the affected section or topic. For pull requests, include: (1) a bullet summary of new theorems or refactors, (2) links to the corresponding book sections or issue IDs, and (3) screenshots or rendered snippets if you touched documentation. Confirm that CI (or at minimum `lake build`) has run locally, and note any failing obligations that still need review.
