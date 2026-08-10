# The Resolved-Face Crown of the Dual-Rail Carrier

**Won Chul Yang** — public edition v1.0 (2026)

DOI: [10.5281/zenodo.21866741](https://doi.org/10.5281/zenodo.21866741)

Part of the [Dual-Rail Carrier Program](https://github.com/ycmath/dual-rail-carrier-program) &mdash; the series hub (map, citation DAG, DOIs, release standards).

Self-dual completeness of the closed core on the resolved face of the
dual-rail carrier D4, with the exact count and one-constant completion —
fully proved and machine-verified.

**Theorem (crown).** On D4 with closed core G = Clo{∧_k, ∨_k, P}, the
R-valued restrictions of closed-core terms on the resolved face
R = {FAL, TRU} are **exactly the P-equivariant maps Rⁿ → R** —
equivalently, exactly the **self-dual Boolean functions**. Hence

> |G|_R^(n)| = 2^(2^(n−1)).

Odd-arity majority is in the crown (explicit routing term); AND, OR, and
the constants are not. The self-dual reading corrects a natural miscount
(2ⁿ counts per-coordinate routing data, not functions: at n = 3 the crown
has 16 members, not 8). Adjoining a **single resolved constant** completes
the crown to all 2^(2^n) maps Rⁿ → R, by an explicit self-dualization with
one guard variable.

Companion note to *The Price of NOT on D4* (Paper II): it proves in full
the two crown facts used as boundary context in Paper II's
Appendix A.4–A.5.

## Contents

```
paper/            the note (md + LaTeX + PDF)
lean/             the Lean 4 development (core only; no mathlib):
    dec_bridge/   the nested-tower library (as published with Paper II)
    wcy2/         the D4 layer of Paper II, extended by
        Wcy2/Crown.lean   this note:
            crown_necessity      realized face maps are self-dual
            crown_sufficiency    every self-dual map is realized by an
                                 explicit orbit-literal DNF term
            restrictRep/extendSD the count bijection (self-dual maps ↔
                                 free assignments on representatives)
            maj3_realized        ternary majority via the routing term
            and2_not_selfDual    AND is excluded
            sdGuard + one_constant_completion
                                 one-constant completion, term form
verification/     independent exhaustive replay (detector tables, brute-
                  force crown counts n ≤ 4, majority, the 2ⁿ miscount
                  check, completion at n ≤ 2, the |R| = 6 sharpness
                  counterexample) — all pass
```

## Verification status

- **Lean**: core Lean 4 only (toolchain pinned), no `native_decide`, no
  `sorry`, no `axiom` declarations. Kernel axiom profile at most
  `[propext, Quot.sound]` for every theorem (`crown_necessity` needs only
  `[Quot.sound]`). See `lean/wcy2/axcheck.log` for the per-theorem
  `#print axioms` of a clean build (which also re-checks the Paper II
  theorems the development extends).
- **Replay**: `verification/crown_replay_v1.py` — exhaustive; frozen
  output alongside.

To rebuild:

```
cd lean/wcy2
lake build
```

## Companion releases

- *The Price of NOT on D4* (Paper II):
  https://github.com/ycmath/price-of-not-on-d4
  (DOI: 10.5281/zenodo.21800033).
- *Finite-Energy Epistemic Logic with Conservative Pointed Extension and
  Negation Geometry* (Paper I):
  https://github.com/ycmath/finite-energy-epistemic-logic
  (DOI: 10.5281/zenodo.21800031).
- *T₀ Is a Maximal Clone on the Three-Element Domain*:
  https://github.com/ycmath/t0-coatom-ternary
  (DOI: 10.5281/zenodo.21866478).

## Authorship & provenance

Won Chul Yang, independent researcher. The mathematics of this note is
the author's, developed inside the author's dual-rail carrier programme
around Papers I–II; AI assistance (Anthropic Claude family) was used for
the Lean 4 mechanization, the machine replay, and the preparation of the
manuscript, with the Lean 4 kernel as the acceptance gate for the
verification layer. The note records a self-correction of the author's
series: an earlier internal manuscript stated the 2ⁿ count for this
fragment; the corrected function count 2^(2^(n−1)) is proved here.
Corrections are invited.

## License

- Lean artifacts and verification scripts: Apache-2.0 (`LICENSE`)
- Text (paper, README): CC BY 4.0 (`LICENSE-text`)
