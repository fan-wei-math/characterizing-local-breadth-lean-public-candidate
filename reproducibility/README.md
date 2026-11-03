# Reproduce the November 2 formalization — comment-sanitized candidate

This package contains all **133 mathematical Lean modules** of the author-coordinated development, including the standalone triangular-schedule bridge. It does not contain Daniel Zhou's separate Lean development.

## Source and dependency identities

| Origin / dependency | Exact identity |
|---|---|
| Original 1D source | `5fe0e3e25e230f7d0ee59abc98193631ea67a666` |
| Original HD source | `8d87aa226dc6f81a4ec70e45fc584da828bcfc3c` |
| Original standalone bridge SHA-256 | `0c86b8d3dfd697ed1a5bdfc5560cef76b6fcf96d5ee0af6d5aecacdcf6b25a6e` |
| Lean | `leanprover/lean4:v4.35.0` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |

**Those source commits identify the original frozen files, not the comment-sanitized public bytes.** [SOURCE-PROVENANCE.json](manifests/SOURCE-PROVENANCE.json) records both hashes. [Comment projection baselines](manifests/COMMENT-PROJECTION-BASELINES.json) bind every byte outside comments, including literal strings and layout whitespace. All comment newlines were preserved, keeping source line locators stable. Original sources/manifests remain private and unmodified. Pins and mathematical imports/options are unchanged.

## Prerequisites and command

Install Git, Bash, Python >=3.11 with venv/pip, [Elan](https://github.com/leanprover/elan) and Poppler (`pdftotext`, `pdfinfo`). On Ubuntu, install `git python3 python3-venv poppler-utils`. Put `lean` and `lake` on PATH. Then, from this repository's root:

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install --require-hashes -r reproducibility/scripts/requirements-privacy.txt
bash reproducibility/scripts/verify.sh --all --jobs 2
```

No private dependency access is needed. All nine dependency checkouts are pinned public Git sources. A clean-build certification requires absent project `.lake/build` at start; public external caches may be fetched. The runner records cache policy, actual commands, environment, timeouts, raw outputs and exit codes in a new ignored `reproducibility/.runs/<UTC>/` directory. It stops on failure without hidden retries. `--output <new-directory>` selects another unused receipt directory. Avoid concurrent full local builds; allow adequate RAM, disk and public download time.

## Mandatory checks

The complete command retains all previous mathematical checks and adds full elaborated-content comparison:

1. Sealed public source/checker hashes and approved non-comment projection hashes for all 133 mathematical sources; complete import closure and exact pins.
2. File/Git/PDF credential and personal-path screening. This automated gate complements the separate contextual privacy audit; its PASS is not public-release approval.
3. Proof-hole/unauthorized-axiom source checks; full sequential 1D/HD/standalone builds.
4. Actual 65-assertion/14-definition registry, allowed axioms and exact agreement with the preserved 126-declaration register.
5. Full elaborated type AST and type/value dependency-set comparison for every own-library declaration against the approved source query, with source metadata erased.
6. Transitive axiom sweep; original 54 1D and 97 HD fingerprints with zero drift; complete project logical-library kernel replay.
7. Final pin/source checks. Every failure retains its raw evidence.

The fixed-source comment eraser supports the literal forms present in these files, nested comments, escaped/quoted identifiers, strings and characters. It fails closed on unsupported interpolated strings rather than guessing. Comparison retains every non-comment byte, a stronger condition than token spelling equality. The new content checker compares actual full type ASTs and dependency-name sets; it does not compare docstring metadata or raw `.olean` bytes.

## Results and assurance boundary

[Current verification results](evidence/VERIFICATION-RESULTS.md) report actual new executions, distinct from earlier preserved runs. [The certificate](CERTIFICATE.md), [correspondence table](evidence/ASSERTION-CERTIFICATION.md) and [definition register](evidence/DEFINITION-REGISTRY.md) retain the scientific qualifications.

**65 numbered assertion occurrences / 64 distinct results, K65/P0/K*0/Q0 under the recorded correspondence interpretations**. Theorem 5.8 restates Theorem 2.6. **13 of 14 definitions** are represented; Definition 1.2 is unencoded background, not kernel checked. **Five remarks are excluded.** This is AI-assisted manuscript correspondence with selected author review, not independent human sign-off or certification of every manuscript prose proof sentence.

Expected full-scope counts remain 5,298 axiom-audited declarations and 5,274 replayed logical constants / 3,893 theorems. Only `propext`, `Classical.choice`, `Quot.sound` are allowed. The replay API excludes 24 compiler-only `_unsafe_rec` artifacts. The historical optional whole-Mathlib empty-base replay timed out at 900 seconds and is **not passed**; no whole-Mathlib rebuild/replay is claimed.
