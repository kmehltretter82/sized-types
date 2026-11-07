# V4: V3 plus type polymorphism and bounded size quantifiers inside types

Local only; nothing is published.

This is route 1, step 1: grow V3 one feature at a time and keep every step proved. Next come type operators, then mixed variance and the inference algorithm.

- Statements: `Theorems/Thm_NishtAbel2024V4.lean` (`theorem_15` block soundness, `theorem_5` program SN).
- Proved in `Solutions/V4/Final.lean` with axioms `[propext, Classical.choice, Quot.sound]`.
- Non-vacuity: `Solutions/V4/Example.lean`.
- Design, the one definition fix, and the remaining differences from the thesis: `DESIGN.md`.

Check:

    lake build Solutions.V4.Final Solutions.V4.Example

`Final` imports all of Mathlib through `Solutions/V3/SCT/Ramsey.lean`. With cached oleans it took about 2½ minutes here.
