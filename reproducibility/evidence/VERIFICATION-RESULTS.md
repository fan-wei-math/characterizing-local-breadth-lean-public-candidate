# Fresh comment-sanitized formalization verification report

**Both complete candidate runs passed: 21/21 on macOS and 21/21 on Linux.** These are new executions on the sanitized mathematical source, not copied success claims from an earlier release. Privacy remains a separate final gate recorded in the [privacy review](PRIVACY-REVIEW.md).

## Exact tested source and transformation

| Identity | Value |
|---|---|
| New private candidate | `fan-wei-math/characterizing-local-breadth-lean-public-candidate` |
| Fresh source/build commit | `a808c1056eff8f95332267967f4f2c02b2602018` |
| Original 1D source | `5fe0e3e25e230f7d0ee59abc98193631ea67a666` |
| Original HD source | `8d87aa226dc6f81a4ec70e45fc584da828bcfc3c` |
| Original standalone bridge SHA-256 | `0c86b8d3dfd697ed1a5bdfc5560cef76b6fcf96d5ee0af6d5aecacdcf6b25a6e` |
| New source/checker/scientific-input manifest SHA-256 | `32436c6b4f1e45767a1a9ec94dc32fa0c48ed508c34bdcff6d5ae6e151db50a8` |
| Sealed verification inputs | 172 |

There are **133 mathematical Lean modules**: 68 1D, 64 HD and one standalone bridge. Privacy sanitization changed **64 comments across 28 files**; the other 105 mathematical files are byte-identical. **Public file hashes differ for the 28 variants.** All bytes outside comments—including string/character literals and layout whitespace—remain unchanged, as do all source line counts, imports, attributes, notation, definitions, hypotheses and proof text. Each changed comment ends before following code on its line, preserving code indentation. Original frozen sources/manifests remain privately preserved.

The [public provenance manifest](../manifests/SOURCE-PROVENANCE.json) distinguishes original and public hashes; [approved non-comment projections](../manifests/COMMENT-PROJECTION-BASELINES.json) bind actual code, not merely filenames. The fixed-corpus eraser supports the literal forms present in all 133 files and fails closed on unsupported interpolation. Positive/negative controls cover nested comments, literal comment delimiters, raw strings, characters and quoted identifiers. The original nine Lean verification drivers, dependency configuration, 54/97 fingerprint baselines and fingerprint/axiom/replay logic remain unchanged. One verification-only driver was added for full elaborated type/dependency comparison; mathematical modules do not import it. All earlier mandatory checks are retained, with stronger source/registry comparisons.

## Actual commands, execution and results

Both environments executed exactly:

```sh
bash reproducibility/scripts/verify.sh --all --jobs 2
```

| Fresh environment | Start UTC | End UTC | Result |
|---|---|---|---|
| clean-mac | 2026-11-03T15:43:42.875875+00:00 | 2026-11-03T16:28:12.658818+00:00 | 21/21, all exit 0 |
| clean-linux | 2026-11-03T15:45:09.584498+00:00 | 2026-11-03T16:21:28.899017+00:00 | 21/21, all exit 0 |

The macOS source was a clean native Git clone of the new root with `--no-local`; the separately fetched GitHub audit clone matched that same root. Linux used the new repository's fresh checkout. Both recorded absent project build objects **and absent external Mathlib caches at start**; public pinned dependencies/caches were then fetched. The Mac privacy utility was installed in a fresh venv from an existing exact-hash public wheel cache; Linux installed that same pinned public wheel from PyPI. Local setup paths/raw setup outputs are retained privately rather than exposed in public logs. No author's private source checkout or dependency credentials are required.

The raw environment, per-check command arrays, working directories, start/end timestamps, limits, stdout, stderr and exit codes are in [Mac receipts](checks/clean-mac/) and [Linux receipts](checks/clean-linux/). [FRESH-VERIFICATION.json](FRESH-VERIFICATION.json) hashes all 131 published raw evidence files, including the exact complete combined CI log. They were copied byte-for-byte, not path-normalized or reformatted. The new [Linux run](https://github.com/fan-wei-math/characterizing-local-breadth-lean-public-candidate/actions/runs/41667056072) completed **success**, attempt **1**, job `126025084483`.

| Mandatory check | macOS | Linux |
|---|---|---|
| Public hashes, approved non-comment projections, imports and pins | Exit 0 | Exit 0 |
| File/history/PDF pattern screening before compilation | Exit 0 | Exit 0 |
| Proof-hole / unauthorized-axiom source screening | Exit 0 | Exit 0 |
| Full 68-module 1D build | Exit 0 | Exit 0 |
| Full 64-module HD build | Exit 0 | Exit 0 |
| Standalone triangular bridge build | Exit 0 | Exit 0 |
| 65-assertion / 14-definition registry, all 126 recorded declaration fields | Identical | Identical |
| Full elaborated type-expression graphs and type/value dependency sets | **5,298 identical** | **5,298 identical** |
| Transitive axiom sweep | **5,298 declarations** | **5,298 declarations** |
| Original 1D frozen check | **54 approved, 0 drift** | **54 approved, 0 drift** |
| Original HD frozen check | **97 approved, 0 drift** | **97 approved, 0 drift** |
| Complete own logical-library kernel replay | **5,274 constants / 3,893 theorems** | **5,274 constants / 3,893 theorems** |
| Final pins/source checks | Exit 0 | Exit 0 |

Only `propext`, `Classical.choice`, `Quot.sound` occur as axioms. No `sorry`/`admit` or unapproved axiom was accepted. Full-type comparison uses sharing-preserving expression graphs, including implicit arguments and universe data, with source metadata omitted. It compares actual expressions and exact dependency sets with a fresh query of the approved unchanged library; it is not just a pretty-printed type/name lookup. All 126 readable registry records also exactly match across platforms and the preserved approved register, including type, locator, proof presence, axioms and direct proof dependencies.

The replay API excludes 24 documented compiler-only `_unsafe_rec` artifacts and rejects other unsafe/partial own constants. Replay uses the pinned Mathlib base and installed Lean checker; it is not a second independently implemented kernel or a whole-Mathlib-from-empty proof rebuild. The **historical optional whole-Mathlib empty-base replay timed out at 900 seconds and remains not passed**.

## Mathematical correspondence and trust boundary

The preserved [65-row correspondence table](ASSERTION-CERTIFICATION.md) records **65 numbered assertion occurrences / 64 distinct results: K65, P0, K*0, Q0 under the documented interpretations**. Theorem 5.8 restates Theorem 2.6. All November 2 upgrades and necessary bridges remain, including the empty-family wrapper, positive thresholds, occurrence-tree representation, Appendix A play/probe/uniform-potential routes, B.1's previous-paper family and the literal triangular schedule. No new mathematical-strength audit or source reformulation was performed for this privacy-only export.

**13 of 14 definitions are represented; Definition 1.2 is unencoded background, not kernel checked. Five remarks remain excluded.** Kernel proof checking, AI-assisted manuscript correspondence, selected author review and written-prose-proof review remain distinct. This certificate is not independent human mathematical sign-off and does not establish every manuscript proof sentence. Original mathematical source proof text is unchanged; no claim is made that docstring metadata or platform-specific `.olean` bytes are identical.

Daniel Zhou's report/certificate remain exact permission-covered originals, including their historical source references. His separate Lean development is not included/replayed. The two reported shared auxiliaries remain credited. Author historical report/certificate copies have explicit privacy/link notices, with mathematical contents and historical source identities preserved. New local links are current navigation aids, not original historical artifacts; see [version boundaries](EVIDENCE-VERSION-NOTES.md).

## Post-run privacy review and development diagnostics

All ten available CI log archive members and all 65 artifact members were opened and screened. The complete combined log and the eight additional system-only lines were contextually read. Masked token placeholders, generic hosted runner paths/ephemeral worker identifiers and provider platform/region data are technical provenance, not actual secrets or a personal workstation location. No unapproved credentials, private personal paths, phone/residential addresses or private hosts were identified. Formal hygienic binder names resembling email addresses were classified against their actual mathematical context. No broad email exclusion was added.

The original/source commits and replaced unsanitized blobs were unavailable through the new repository namespace: 23 commit refs returned HTTP 422 with exact missing-SHA messages; 31 source/report blobs returned HTTP 404. A diagnostic initially expected 404 for commits; the raw failed classification was preserved and corrected offline from the actual responses, without retrying requests or suppressing a privacy finding.

New checker development retained an initial missing-annotation compile error and a 300-second timeout of an unshared full-tree serializer. The final sharing-preserving serializer and both mandatory fresh matrices passed; these earlier diagnostic attempts are not mislabeled as successful matrix runs. PDF rendering had a nonfatal fontconfig cache warning but completed all 22 pages; no font installation or optional PDF troubleshooting was undertaken. GitHub's two platform-deprecation annotations and uploader runtime warnings were inspected; the actual workflow remained successful.

Projects and rulesets were inspected manually by the owner using existing access: no linked Projects, including closed ones, and no configured rulesets. Automated Projects permission remains unavailable and the ruleset endpoint's plan restriction remains recorded, not falsely labeled an API pass. No OAuth scope, project visibility or account permission was expanded. The initial private CI push was separately owner-authorized after an approval-review refusal; no public publication or name swap followed.

The later evidence/documentation commit changes no sealed source/checker/pin/registry input. Final integrity/privacy checks and the externally supplied exact final Git HEAD inventory bind those documentation updates; **no second full mathematical matrix at that documentation-only commit is claimed**. Original repositories, sources, histories, manuscript and approval records remain unchanged and private. No license, repository rename or public visibility change is asserted.
