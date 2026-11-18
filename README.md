# Verified Image

**From proofs without words to proofs in Lean, keeping the picture's argument.**

A *proof without words* is a picture that makes a theorem evident: nested L-shapes
filling a square show that the odd numbers sum to a square, and four triangles
rearranged inside a square show Pythagoras' theorem. This project builds a
system that takes such a picture and produces a machine-checked Lean proof
**that follows the picture's own argument**, rather than proving the same
theorem by unrelated means. Later, it also aims to go the other way: from a
formal statement to a picture that proves it.

---

## 1. Motivation

- **Diagrams are how many people understand mathematics,** but they have long
  been treated as informal and untrustworthy: a picture shows one instance,
  while the theorem claims something for all of them.
- **Proof assistants can now serve as referees.** Lean checks every inference, so
  the parts of the pipeline that read and interpret pictures can be heuristic
  (including neural models) without compromising soundness.
- **The interesting question is *faithfulness*.** Recognising "this is
  Pythagoras" and citing Mathlib is easy and says nothing about the picture.
  Capturing *why the picture works* in a formal object is the open problem.

## 2. Research questions

1. **Representation.** What is the argument contained in a picture? Can it be
   captured in an intermediate representation (IR) that is precise enough to
   compile to Lean and concrete enough to render back to a picture?
2. **Generality.** A picture shows one instance (n = 5, one particular
   triangle). How do we recover the general argument and certify that it holds
   for every instance?
3. **Faithfulness.** How do we define, and check, that a Lean proof *follows*
   a picture rather than merely proving the same statement?
4. **Recognition.** Can a picture be mapped to its IR automatically, with Lean
   acting as the final judge?
5. **Discovery (reverse direction).** Given a formal statement, can we search
   the space of IR arguments for a visual proof and certify it?

## 3. Background and related work

- **Nelsen, *Proofs Without Words* I and II** (MAA, 1993 and 2000): the
  standard collections, and the main source of examples.
- **Jamnik, *Mathematical Reasoning with Diagrams* (CSLI, 2001), the Diamond
  system.** This is the closest prior work. It is an interactive *proof
  checker* for discrete arithmetic theorems:
  - The user proves two concrete instances by applying diagram operations
    ("split an ell", "cut diagonally", …).
  - Diamond abstracts these into a *schematic proof*: a recursive function of
    n, justified by the constructive ω-rule.
  - It checks that function in a theory of diagrams via the Clam proof
    planner. It only finds a proof plan, without producing an object-level proof.
  - Limitations: one parameter, discrete space only, no image input, no
    mainstream proof assistant, no proof discovery.
  - Contributions reused here: the taxonomy of diagrammatic theorems, the
    operation vocabulary, and the LHS-diagram → operations → RHS-diagram notion
    of proof.
- **Manders, "The Euclidean Diagram" (2008):** exact vs. co-exact properties,
  i.e., which features of a drawing can be trusted.
- **Avigad, Dean & Mumma, "A Formal System for Euclid's Elements" (2009),
  System E:** a sound and complete account of Euclid-style diagrammatic
  inference.
- **LeanEuclid (Murphy et al., 2024):** autoformalising Euclidean geometry in
  Lean using System E.
- **AlphaGeometry (Trinh et al., 2024):** neuro-symbolic synthetic geometry.
  It solves problems; it does not formalise given pictorial arguments.
- **Autoformalisation with LLMs** more broadly: text to Lean. Here the input is
  visual and the requirement is stronger (faithfulness, not just correctness).

## 4. Approach

```
              recognise                      compile
   image  ─────────────────▶    IR    ─────────────────▶  Lean proof
          ◀─────────────────          ◀─────────────────
               render                    search (reverse)
```

### 4.1 A theory of diagrams in Lean
A small library in `VerifiedImage/Diagram/`:
- **Shapes** are definitions. Discrete diagrams are `Finset (ℕ × ℕ)`, one cell
  per dot, with value = cardinality.
- **Operations** are lemmas of the form "this shape is the disjoint union of
  those shapes", or "this map is a bijection between shapes" (rotation,
  reflection, translation).
- **Schematic (recursive) proofs** become ordinary induction over the
  operation, so the ω-rule is not needed.
- **Continuous diagrams** (Category 1, e.g. Pythagoras) will need a separate
  polygon/area theory: area additivity over dissections and invariance under
  isometries. Building on Mathlib's measure theory directly is likely too heavy.

### 4.2 The intermediate representation
An IR document records:
- the **theorem** as an equation (LHS / RHS);
- the **parameters** (n, or a and b) and the **drawn instance**;
- the **objects** (shapes indexed by the parameters);
- the **argument**: a sequence of operations taking the LHS diagram to the RHS
  diagram, possibly recursive;
- the **invariant** being preserved (count, area, length).

The IR is designed under two constraints:
1. it **compiles** mechanically to a Lean proof built from library lemmas;
2. it **renders** mechanically to a picture for any parameter value.

### 4.3 Faithfulness, operationally
A Lean proof counts as faithful to a picture when:
- the main identity is derived **only** from diagram-library operations plus
  counting/measuring. Decision procedures (`omega`, `ring`, `nlinarith`, …)
  may discharge local facts (one cell's membership, `(k+1) + k = 2k+1`) but
  never the identity itself;
- every proof step corresponds to an IR operation, and the IR renders to a
  picture equivalent to the original;
- the statement is a separate `def`, reviewed by a human, so a "faithful proof
  of the wrong theorem" is caught;
- `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`.

Refining this definition (for example, a formal check that a proof term only
uses whitelisted lemmas) is itself a research output.

### 4.4 Scope: Jamnik's taxonomy

| Category | Description | Example | Plan |
|---|---|---|---|
| 2 | inductive, one parameter, discrete, schematic proof | sum of odds | **first** |
| 1 | non-inductive, one general diagram with labelled lengths, continuous | Pythagoras | second (needs area theory) |
| 3 | inherently infinite (ellipsis), continuous | geometric series | last (needs limits) |

## 5. Work plan

| Phase | Goal | Deliverable | Done when |
|---|---|---|---|
| **0** | Setup | Lean + Mathlib project, data layout, design log | ✔ |
| **1** | Three faithful proofs by hand | sum of odds ✔; n(n+1) = 2·Tri(n); (2n+1)² = 8·Tri(n) + 1 | all compile under the faithfulness rules |
| **2** | Diagram library | shapes, views, operations (split, rotate, reflect, translate) | the three proofs share it, with no ad-hoc lemmas |
| **3** | IR v0 + tools | schema; IR → Lean compiler; IR → SVG renderer | the compiler regenerates the hand proofs; renders look right at n = 3, 5, 8 |
| **4** | Diamond benchmark | IRs + Lean for Diamond's 13 theorems (dev + test set) | all 13 verified, including the 2 Diamond could not verify |
| **5** | Wider corpus | 50+ discrete proofs from Nelsen, redrawn | coverage report; IR extended only when forced, with each extension logged |
| **6** | Category 1 | polygon/area theory; Pythagoras by rearrangement | faithful Pythagoras compiles |
| **7** | Recognition | image → IR with a multimodal model, checked by compile/render | accuracy on the redrawn corpus and on original figures |
| **8** | Reverse direction | statement → IR search over argument templates | new visual proofs found and certified |

Phases 1–4 are the core. They are achievable at small scale and already
produce a result: Diamond's benchmark, formalised faithfully in a mainstream
proof assistant.

## 6. Evaluation

Each proof is scored on separate axes, never merged into one number:
- **Statement correctness:** does the Lean statement say what the picture means? (human review)
- **Proof validity:** does it compile with only the standard axioms? (Lean)
- **Faithfulness:** does it satisfy §4.3? (a lemma-whitelist check, then human review)
- **Generality:** does the IR render correctly for several parameter values?
- **Coverage:** what fraction of a corpus the IR and library can express.

For recognition (Phase 7): exact-match and compile-rate of predicted IRs,
by category and by difficulty.

## 7. Risks and mitigations

| Risk | Mitigation |
|---|---|
| The IR keeps changing as new proofs arrive | design it from hand proofs first; version it; keep a log in `NOTES.md` |
| Area reasoning in Lean is expensive | a dedicated, axiomatised polygon theory; postpone to Phase 6 |
| "Faithful" stays vague | the operational rules in §4.3, enforced by tooling |
| A model proposes plausible but wrong IRs | Lean and rendering are the judges; nothing is accepted unchecked |
| Copyright on Nelsen's figures | redraw every figure ourselves; cite originals; never commit scans |
| More than one parameter (n·m = m·n) | allow several parameters in the IR from the start, unlike Diamond |

## 8. Data

Each proof lives in `proofs/<id>/`:
- `meta.yaml`: source, natural-language statement, category, status flags;
- `ir.yaml`: the argument;
- `figure.svg`: our own redrawing (rendered from the IR once the renderer exists);
- a Lean file in `VerifiedImage/Proofs/` with `statement` and `proof`.

## 9. Status

| id | category | Lean | faithful |
|---|---|---|---|
| sum-of-odds | 2 | ✔ | ✔ |

## Repository layout

- `VerifiedImage/Diagram/`: Lean theory of diagrams (shapes and operations).
- `VerifiedImage/Proofs/`: one Lean file per formalised picture proof.
- `proofs/<id>/`: data for each proof.
- `NOTES.md`: design log (decisions, open questions).

## Build

```
lake exe cache get   # first time only: download compiled Mathlib
lake build
```
