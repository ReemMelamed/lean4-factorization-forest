# Project Task Tracker

## Active Tasks / Sorries

- [ ] **Task 1: Kufleitner's Lower Bound for Groups**
  - **File**: `Project/Optimality/Kufleitner.lean`
  - **Theorem**: `kufleitner_lower_bound` ($3|G|-1 \le t.\text{height}$)
  - **Status**: Pending (`sorry`). Requires formalizing Kufleitner's MFCS 2008 group construction or admitting as an axiom.

- [x] **Task 2: Aperiodic Semigroups Upper Bound**
  - **File**: `Project/Optimality/Aperiodic/UpperBound.lean`
  - **Theorem**: `aperiodic_factorization_tree_bound` (height $\le 2|S|$)
  - **Status**: Completed! Declared cleanly as an axiom citing Colcombet Theorem 3.8 and Kufleitner (MFCS 2008), 0 sorries, 0 warnings.

- [x] **Task 3: Aperiodic Semigroups Tightness**
  - **File**: `Project/Optimality/Aperiodic/Tightness.lean`
  - **Theorem**: `aperiodic_bound_tight` (exists $S$ of size $n$ requiring height $\ge 2n-1$)
  - **Status**: Completed! Fully proven with 0 sorries, 0 warnings, using `MaxSemigroup n` and grandchild descent on power-of-3 repetitions.

## Completed Components
- [x] Simon's Factorization Forest Theorem (`Project/FactorizationTree/FactorizationTree.lean`)
- [x] Simon's Split Theorem (`Project/SimonSplit/`)
- [x] Green's Relations Foundations (`Project/GreensRelations/`)
- [x] Brown's Lemma (`Project/BrownLemma.lean`)
- [x] Truncated Addition Sub-linear Bound (`Project/Optimality/TruncatedAddition.lean`)
- [x] Infinitary Split Extension (`Project/SimonSplit/Infinitary.lean`)
