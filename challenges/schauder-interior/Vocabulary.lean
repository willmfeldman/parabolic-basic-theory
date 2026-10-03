/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import Vocabulary.Setting
public import Vocabulary.Classical
public import Vocabulary.Holder
public import Vocabulary.Viscosity

/-!
# Vocabulary

Re-exports the challenge vocabulary `Vocabulary/*.lean`: one Mathlib-only module per restated
library file. The workspace keeps the vocabulary split along the library's module boundaries
(see the `challenge-prep: split vocabulary` line in `Challenge.lean`).
-/

@[expose] public section
