# EcoLean: A Lean 4 Library for Formal Economic Theory

EcoLean is a Lean 4 and mathlib project for formalizing parts of microeconomic theory, social choice theory, and game theory.

The current development has three main areas:

- preference, choice, and utility theory in the style of early graduate microeconomics;
- finite social choice, including Arrow's impossibility theorem and a Gibbard-Satterthwaite derivation;
- foundational game-theory language for relations, correspondences, game forms, and static games.

This repository is a proof-oriented Lean library rather than an executable application.

## Main Definitions and Theorems

### Choice, Preference, and Utility

The `EcoLean/ChoicePreferenceUtility` modules formalize:

- weak preferences, strict preference, indifference, completeness, and transitivity;
- choice functions and basic axioms such as choosing from feasible sets, finite nonemptiness, and choice coherence;
- the passage from preferences to choice functions and back;
- utility representation results on finite and encodable domains;
- utility rationalization results for choice functions;
- invariance of representation and rationalization under strictly increasing transformations.

Some of the main summary theorems live in `EcoLean/ChoicePreferenceUtility/Utility.lean`, including:

- `Preference.exists_represents_iff_complete_transitive_finite`
- `Preference.exists_represents_iff_complete_transitive_encodable`
- `ChoiceFunction.exists_rationalizes_iff_axioms_finite`
- `ChoiceFunction.exists_rationalizesOnFinite_of_axioms_encodable`

### Social Choice Theory

The `EcoLean/SocialChoiceTheory` development provides:

- basic finite-agenda infrastructure and pairwise-comparison lemmas;
- a formalization of Arrow's theorem on finite agendas;
- a strict-ballot Gibbard-Satterthwaite result derived from Arrow-style machinery.

Main theorems include:

- `EcoLean.SocialChoiceTheory.arrow`
- `EcoLean.SocialChoiceTheory.gibbardSatterthwaite`

### Game Theory Foundations

The `EcoLean/GameTheory` tree is currently a foundations layer, including:

- binary relations, strict and symmetric parts, and maximal/minimal sets;
- sets, functions, and correspondences;
- abstract game forms and games with utility;
- static games in strategic form;
- small probability and expectation helper modules.

## File Layout

- `EcoLean.lean`
  - top-level entrypoint for the currently re-exported library surface
- `EcoLean/ChoicePreferenceUtility/`
  - choice, preference, no-better-than, and utility modules
- `EcoLean/SocialChoiceTheory/`
  - finite social-choice infrastructure, Arrow, and Gibbard-Satterthwaite
- `EcoLean/GameTheory/`
  - foundational game-theory definitions and supporting mathematical language
- `lakefile.lean`
  - Lake package definition and mathlib dependency
- `lean-toolchain`
  - pinned Lean toolchain version

At the moment, `import EcoLean` re-exports the choice/preference/utility and social-choice portions of the project. The game-theory files are available, but they are not currently re-exported by `EcoLean.lean`, so they should be imported directly when needed.

## Requirements

- Lean toolchain from `lean-toolchain`:
  - `leanprover/lean4:v4.29.0-rc8`
- `elan`
- `mathlib4` (fetched by Lake)

## Build

If `lake` is already on your `PATH`:

```bash
lake exe cache get
lake build
```

If you use the default `elan` install location:

```bash
~/.elan/bin/lake exe cache get
~/.elan/bin/lake build
```

The cache step is optional, but it usually makes the first build much faster.

## Usage

Import the main re-exported library with:

```lean
import EcoLean
```

If you want the game-theory modules, import them directly, for example:

```lean
import EcoLean.GameTheory.Introduction.AbstractGameModels
import EcoLean.GameTheory.StaticGames.FormalRepresentation
```

## Development Notes

- The library target is `EcoLean`.
- The package currently depends only on `mathlib`.
- There is no executable target yet; the repository is organized around reusable definitions and proofs.

## Contributions

Contributions are welcome.

When possible, keep additions aligned with mathlib conventions:

- prefer small, reusable definitions and theorems;
- add docstrings for major definitions and theorems;
- keep naming and documentation style close to the existing Lean and mathlib ecosystem.

## License

This project is licensed under the Apache License 2.0. See `LICENSE` for details.
