# Package C (Issue #26) Prototype Run Record — 2026-11-25

## Environment & Baseline
- **Repository root**: `G:\lean666\jsp_001022_extension`
- **Local `HEAD`**: `2d3781e807a61c0e2478ac26510332e595ed4d78`
- **Lean version**: `Lean (version 4.30.0-rc2, x86_64-w64-windows-gnu, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)`
- **Working directory**: `G:\lean666\jsp_001022_extension\verification\runs\2026-11-25-package-c-orbit`
- **Read-only baseline imported**: `LeanCompletion.UAV.TreeBudgetSubtreeCompact` (no existing repository files modified)

## Deliverables (`TreeBudgetOrbitPrototype.lean`)
1. **Unified reindexing (`reindexMatrix`, `reindex`)**:
   - `reindexMatrix σ n i v = n (σ i) v`
   - `(reindex σ z).active = Finset.univ.filter (fun i => σ i ∈ z.active)` (`i ∈ (reindex σ z).active ↔ σ i ∈ z.active`)
   - `(reindex σ z).cost i = z.cost (σ i)`
2. **C0 — `compactRep_reindex`**:
   - Proves `CompactRep R H m s v z → CompactRep R H m s v (reindex σ z)` via explicit matrix witness `reindexMatrix σ n`.
3. **C1 — `jointHist_eq_iff_reindex`**:
   - Proves `jointHist y = jointHist z ↔ ∃ σ : Equiv.Perm (Fin m), y = reindex σ z` using the same `reindex` definition, constructing `σ` via `Fintype.equivOfCardEq` on per-type fibers and `Equiv.sigmaFiberEquiv`.
4. **Three Verification Examples**:
   - **Example 1 (`m = 0`)**: `example_m_zero_hist_eq`, `example_m_zero_exists_reindex`, `example_m_zero_compactRep_reindex`.
   - **Example 2 (repeated joint types + negative rational costs, `m = 3`)**: `ex2_z` / `ex2_y` with `(true, -3/2)` repeated twice and `(false, 5/4)`.
   - **Example 3 (same active count and same cost multiset, different joint histograms, `m = 2`)**: `[(true, 0), (false, 1)]` vs `[(true, 1), (false, 0)]` (`example_split_loss_active_card`, `example_split_loss_cost_multiset`, `example_split_loss_jointHist_ne`, `example_split_loss_not_reindex`).
5. **Optional C2 Candidate Signature (`TransportRealizeExactSpec`)**:
   - Typechecked `LegalTable`, `inducedTable`, and `TransportRealizeExactSpec : Prop` without `sorry`.

## Verification Command & Output
Command run from `G:\lean666\jsp_001022_extension`:
```powershell
lake env lean verification/runs/2026-11-25-package-c-orbit/TreeBudgetOrbitPrototype.lean
```

- **Exit code**: `0` (zero errors, zero warnings)
- **Saved raw log**: `lean_check.log`
- **Axiom audit (`#print axioms`)**:
```text
'UAVProof.TreeBudgetOrbitPrototype.compactRep_reindex' depends on axioms: [propext, Classical.choice, Quot.sound]
'UAVProof.TreeBudgetOrbitPrototype.jointHist_eq_iff_reindex' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Both outputs are subsets of `{propext, Classical.choice, Quot.sound}` with no `sorryAx` or custom axioms.

---

## Round 2: C2 (`transport_realize_exact`) — `TreeBudgetTransportExact.lean`

### Deliverables
1. **Step 1 (`legalTable_of_perm`)**: Proves that any compatible permutation `σ : Equiv.Perm (Fin m)` induces a `LegalTable` (row sums via `Finset.card_eq_sum_card_fiberwise`, column sums via `σ`-bijection + fiberwise sum, forbidden cells equal to `0`).
2. **Step 2 (`exists_perm_of_legalTable`)**: Constructs cell slot space `Σ a : A, Σ b : B, Fin (N a b)`, builds left/right equivalences `eL, eR : Fin m ≃ Slot` from row/column marginals via `Fintype.equivOfCardEq` + `Equiv.sigmaFiberEquiv`, sets `σ := eL.trans eR.symm`, and proves both per-route compatibility `K (x i) (y (σ i))` and exact cell count `inducedTable x y σ a.1 b.1 = N a b` simultaneously for all `(a, b)`.
3. **Main Theorem**: `theorem transport_realize_exact : TransportRealizeExactSpec` (exact match to the C0/C1 candidate signature).
4. **Regression Examples**:
   - **2×2 all-ones split-block regression (`ex_split_legal`, `ex_split_exists_perm`, `ex_split_breaks_repeated_block`)**: `x = y = ![false, false, true, true]`, `N _ _ = 1`; proves any realizing `σ` must split the two repeated `false` routes across distinct right types `false` and `true`.
   - **Empty route set (`ex_m_zero_transport`)**: `m = 0`, `A = B = ∅`.
   - **Internal compatibility `K_in` with forbidden cell and negative rational costs (`ex3_forbidden_realizable`)**: `(true, -3/2)` and `(false, 1/2)` with forbidden cell `(false, _) → (true, _)` zeroed out.

### Verification Command & Output
Command run from `G:\lean666\jsp_001022_extension`:
```powershell
lake env lean verification/runs/2026-11-25-package-c-orbit/TreeBudgetTransportExact.lean
```

- **Exit code**: `0` (zero errors, zero warnings)
- **Saved raw log**: `lean_check_c2.log`
- **Axiom audit (`#print axioms`)**:
```text
'UAVProof.TreeBudgetOrbitPrototype.legalTable_of_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'UAVProof.TreeBudgetOrbitPrototype.exists_perm_of_legalTable' depends on axioms: [propext, Classical.choice, Quot.sound]
'UAVProof.TreeBudgetOrbitPrototype.transport_realize_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```
All three outputs are subsets of `{propext, Classical.choice, Quot.sound}` with no `sorryAx` or custom axioms.

---

## Round 3: C3 (`inside_join_hist_iff`) — `TreeBudgetInsideJoin.lean`

### Shared Import & Single-Source Cleanup
- Removed the duplicate `NextRoundCandidateSignature` section from `TreeBudgetOrbitPrototype.lean` (now `inducedTable`, `LegalTable`, `TransportRealizeExactSpec` have a single source in `TreeBudgetTransportExact.lean`).
- Renamed C2's local regression helpers from `ex3_*` to `exC2_*` to eliminate namespace collision with C0/C1's `ex3_*`.
- Built `.olean` files for both `TreeBudgetOrbitPrototype.lean` (`E1=0`) and `TreeBudgetTransportExact.lean` (`E2=0`) inside `verification/runs/2026-11-25-package-c-orbit/`, and imported both in `TreeBudgetInsideJoin.lean` with live `#check compactRep_reindex` and `#check transport_realize_exact`.

### Deliverables (`TreeBudgetInsideJoin.lean`)
1. **Pushforward histogram counting (`g_in`, `tablePushforwardHist`, `count_tablePushforwardHist`, `count_merged_eq_sum_table`, `merged_hist_eq_tablePushforwardHist`)**:
   - Proves that whenever `σ` realizes every cell count of `N`, the merged output multiset under `g_in (a, b) = (a.1, a.2 + b.2)` satisfies `Multiset.count t h_out = ∑ a, ∑ b, if g_in a b = t then N a b else 0` and equals `tablePushforwardHist N`.
2. **Single-child witnessed inside join (`parentState`, `extendChild`, `inside_join_hist_iff`)**:
   - Fixes non-root vertex `v`, parent top-edge counts `q` (counting `linearWeight R s v * q i` once), already-processed children `S` with witnesses `ns`, and one new child `u ∉ S` with witness `nChild` representing `zChild`.
   - Proves that for any target histogram `h`, a legal transport table `N` pushing forward to `h` exists iff a child row permutation `σ` exists such that `reindexMatrix σ nChild` preserves `PartialValid` / `RootChildCap` / `CompactRep` (via C0 `compactRep_reindex`), respects parent activity `0 < reindexMatrix σ nChild i u → 0 < q i`, and extends the parent histogram to `h`.
3. **Four Regression Examples**:
   - **Output-type merging (`exMerge_output_count_two`)**: two distinct cells contributing `0 + 1` and `1 + 0` with active flag `true` yield `Multiset.count (true, 1) h_out = 2`.
   - **Parent-child forbidden pairing (`exForbidden_no_legal_table`)**: `K_in` rules out any legal table pairing `(false, 0)` with `(true, 1)`.
   - **Negative rational cost addition (`exNeg_signed_cost_addition`)**: `5 + (-7) = -2` and `(-3/2) + (1/2) = -1` under `g_in` and `K_in`.
   - **Zero routes (`exZeroRoutes_inside_join`)**: `m = 0` instantiation of `inside_join_hist_iff`.

### Verification Command & Output
Command run from `G:\lean666\jsp_001022_extension`:
```powershell
$env:LEAN_PATH = "G:\lean666\jsp_001022_extension\verification\runs\2026-11-25-package-c-orbit"
lake env lean verification/runs/2026-11-25-package-c-orbit/TreeBudgetInsideJoin.lean
```

- **Exit code**: `0` (zero errors, zero warnings)
- **Saved raw log**: `lean_check_c3.log`
- **Axiom audit (`#print axioms`)**:
```text
'UAVProof.TreeBudgetOrbitPrototype.count_merged_eq_sum_table' depends on axioms: [propext, Classical.choice, Quot.sound]
'UAVProof.TreeBudgetOrbitPrototype.merged_hist_eq_tablePushforwardHist' depends on axioms: [propext, Classical.choice, Quot.sound]
'UAVProof.TreeBudgetOrbitPrototype.inside_join_hist_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```
All outputs are subsets of `{propext, Classical.choice, Quot.sound}` with no `sorryAx` or custom axioms.

---

## Round 4: Multi-Child Fold Step 1 (`PrefixValid` & Two-Child Sequential Insertion) — `TreeBudgetPrefixFold.lean`

### Deliverables (`TreeBudgetPrefixFold.lean`)
Imports `TreeBudgetInsideJoin` (and transitively `TreeBudgetOrbitPrototype` + `TreeBudgetTransportExact`).
1. **Prefix invariant (`PrefixValid`)**: records `S ⊆ R.children v`, per-child `PartialValid R H m w (ns w)`, `RootChildCap R w (fun i => ns w i w)`, and row-by-row parent compatibility `∀ i, 0 < ns w i w → 0 < q i`.
2. **Empty prefix (`prefixValid_empty`, `parentState_empty_cost`)**: vacuously valid on `∅`, charging `linearWeight R s v * q i` once.
3. **Single-insertion preservation (`extendChild_preserves_old`, `parentState_cost_insert`, `prefixValid_insert`, `prefixValid_insert_of_transport`)**: inserting a fresh child `u ∈ R.children v \ S` preserves `PrefixValid`, leaves every earlier child's matrix untouched row-for-row, adds `subtreeLinearCost R s u` once, and lifts any legal transport table via `inside_join_hist_iff`.
4. **Two-child sequential insertion (`two_child_insert_preserves_first`)**: starting from `∅` and inserting `u₁` then `u₂ ≠ u₁`, proves `PrefixValid` at both `{u₁}` and `{u₂, u₁}`, row-by-row preservation `ns₂ u₁ = reindexMatrix σ₁ n₁` and `PartialValid R H m u₁ (ns₂ u₁)`, and that `linearWeight R s v * q i` is counted once.
5. **Concrete 4-vertex regression (`ex_two_child_hub_regression`)**: hub `v = 1` below root `0` with leaves `2, 3`, `m = 2`, signed costs `s = ![0, 2, -5, 3]`, `H = ![0, 2, 1, 1]`, `q = ![1, 1]`, `σ₁ = id`, `σ₂ = swap 0 1`; verifies `PrefixValid`, `ns₂ 2 = ns₁ 2`, and exact final route costs `-1` and `7`.

### Verification Command & Output
Command run from `G:\lean666\jsp_001022_extension`:
```powershell
$env:LEAN_PATH = "G:\lean666\jsp_001022_extension\verification\runs\2026-11-25-package-c-orbit"
lake env lean verification/runs/2026-11-25-package-c-orbit/TreeBudgetPrefixFold.lean
```

- **Exit code**: `0` (zero errors, zero warnings)
- **Saved raw log**: `lean_check_prefix1.log`
- **Axiom audit (`#print axioms`)**:
```text
'UAVProof.TreeBudgetOrbitPrototype.prefixValid_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'UAVProof.TreeBudgetOrbitPrototype.prefixValid_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
'UAVProof.TreeBudgetOrbitPrototype.prefixValid_insert_of_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'UAVProof.TreeBudgetOrbitPrototype.two_child_insert_preserves_first' depends on axioms: [propext, Classical.choice, Quot.sound]
'UAVProof.TreeBudgetOrbitPrototype.ex_two_child_hub_regression' depends on axioms: [propext, Classical.choice, Quot.sound]
```
All five outputs are subsets of `{propext, Classical.choice, Quot.sound}` with no `sorryAx` or custom axioms.

---

## Round 5: Multi-Child Fold Step 2 (`prefixReach_iff_witness`) — `TreeBudgetPrefixReach.lean`

### Deliverables (`TreeBudgetPrefixReach.lean`)
Imports `TreeBudgetPrefixFold` (after exporting `TreeBudgetPrefixFold.olean` with `E4=0`).
Fixed two minor elaboration details in the candidate file: removed unused `Multiset.mem_map` simp arg in `jointHist_support_image` and closed `reindexMatrix (Equiv.refl (Fin m)) (ns u) = ns u` by `rfl` in `histAdvance_prefixWitness_iff`.

1. **Histogram-marginal bridge (`HistJoinOn`, `HistJoin`, `histJoin_jointHist_iff`)**: links histogram-level transport tables to `LegalTable` on arbitrary concrete representatives `(x, y)`.
2. **Single-step witness equivalence (`histAdvance_prefixWitness_iff`)**: for a fresh child `u ∈ R.children v \ S`, proves `histAdvance ... (PrefixWitnessHist ... S) u h ↔ PrefixWitnessHist ... (insert u S) h` (forward via `prefixValid_insert_of_transport`, backward via `ns u` with `Equiv.refl` and `inside_join_hist_iff`).
3. **Left-to-right list induction & order independence (`histFold_from_iff`, `prefixReach_iff_witness`, `prefixReach_iff_of_same_children`)**: proves `PrefixReach R H s v q us h ↔ ∃ ns, PrefixValid R H v q us.toFinset ns ∧ jointHist (parentState R s v q us.toFinset ns) = h` for any `us.Nodup` with `∀ u ∈ us, u ∈ R.children v`, plus order independence over lists with the same `toFinset`.
4. **Boundary & regression checks**: `prefixReach_nil_iff`, `prefixReach_zero_routes_only_empty` (`m = 0`), and `ex_prefixReach_two_child_hub` (4-vertex signed-cost `{-1, 7}` witness lifted through `PrefixReach`).

### Verification Command & Output
Command run from `G:\lean666\jsp_001022_extension`:
```powershell
$env:LEAN_PATH = "G:\lean666\jsp_001022_extension\verification\runs\2026-11-25-package-c-orbit"
lake env lean verification/runs/2026-11-25-package-c-orbit/TreeBudgetPrefixReach.lean
```

- **Exit code**: `0` (zero errors, zero warnings)
- **Saved raw log**: `lean_check_prefix2.log`
- **Axiom audit (`#print axioms`)**:
```text
'UAVProof.TreeBudgetOrbitPrototype.histJoin_jointHist_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'UAVProof.TreeBudgetOrbitPrototype.histAdvance_prefixWitness_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'UAVProof.TreeBudgetOrbitPrototype.histFold_from_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'UAVProof.TreeBudgetOrbitPrototype.prefixReach_iff_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'UAVProof.TreeBudgetOrbitPrototype.prefixReach_iff_of_same_children' depends on axioms: [propext, Classical.choice, Quot.sound]
'UAVProof.TreeBudgetOrbitPrototype.prefixReach_nil_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'UAVProof.TreeBudgetOrbitPrototype.prefixReach_zero_routes_only_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'UAVProof.TreeBudgetOrbitPrototype.ex_prefixReach_two_child_hub' depends on axioms: [propext, Classical.choice, Quot.sound]
```
All eight outputs are subsets of `{propext, Classical.choice, Quot.sound}` with no `sorryAx` or custom axioms.

---

## Round 6: Multi-Child Fold Step 3 (`childHist_iff_fullPrefixReach`) — `TreeBudgetPrefixMerge.lean`

### Deliverables (`TreeBudgetPrefixMerge.lean`)
Imports `TreeBudgetPrefixReach` (after exporting `TreeBudgetPrefixReach.olean` with `E5=0`).

1. **Full-node orbit equivalence (`childHist_iff_fullPrefixReach`)**:
   - For any non-root vertex `v` (`hv : v ≠ R.root`) and any duplicate-free list `us` covering `R.children v` (`us.toFinset = R.children v`), proves:
     `ChildHist R H m s v h ↔ ∃ q : Fin m → ℕ, (∑ i, q i) = H v ∧ RootChildCap R v q ∧ PrefixReach R H s v q us h`.
   - Forward (`ChildHist → PrefixReach`): unpacks `compactRep_merge_iff.mp`, chooses child matrices `ns` from `CompactRep`, proves `PrefixValid` and `parentState ... = z`, then applies `prefixReach_iff_witness.mpr`.
   - Backward (`PrefixReach → ChildHist`): unpacks `prefixReach_iff_witness.mp`, instantiates `z := parentState R s v q (R.children v) ns` and per-child `zs u` from `ns u`, and closes via `compactRep_merge_iff.mpr`.
2. **Regression (`ex_childHist_two_child_hub`)**:
   - Reuses `ex_prefixReach_two_child_hub` through `childHist_iff_fullPrefixReach.mpr` to derive `ChildHist R H 2 s 1 (jointHist ⟨Finset.univ, ![-1, 7]⟩)` on the 4-vertex signed-cost hub example.

### Verification Command & Output
Command run from `G:\lean666\jsp_001022_extension`:
```powershell
$env:LEAN_PATH = "G:\lean666\jsp_001022_extension\verification\runs\2026-11-25-package-c-orbit"
lake env lean verification/runs/2026-11-25-package-c-orbit/TreeBudgetPrefixMerge.lean
```

- **Exit code**: `0` (zero errors, zero warnings, first-pass build)
- **Saved raw log**: `lean_check_prefix3.log`
- **Axiom audit (`#print axioms`)**:
```text
'UAVProof.TreeBudgetOrbitPrototype.childHist_iff_fullPrefixReach' depends on axioms: [propext, Classical.choice, Quot.sound]
'UAVProof.TreeBudgetOrbitPrototype.ex_childHist_two_child_hub' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Both outputs are subsets of `{propext, Classical.choice, Quot.sound}` with no `sorryAx` or custom axioms.
