# Daniel Zhou–coordinated verification documents: version note

These two documents were copied **unchanged** from the previously assembled verification-reports repository, without modifying Daniel Zhou's wording:

- [K-REPORT-Nov1.pdf](K-REPORT-Nov1.pdf) — later **Level K** sign-off for the November 1 manuscript, reporting 64 distinct mathematical results (65 numbered occurrences because Theorem 5.8 repeats Theorem 2.6).
- [CERTIFICATE.md](CERTIFICATE.md) — earlier descriptive certificate, with a useful reader's glossary and full result index.

**Read the later K report as the controlling Daniel Zhou–coordinated Level K assessment.** The earlier certificate was not rewritten to claim the later proof upgrades retrospectively.

In particular, the certificate's description of Lemma A.2's locality/P1–P4 domain (“every consistent game state”) and its discussion of Proposition B.1 under an abstract previous-family hypothesis reflect the earlier formalization stage. The later K report states the prescribed-play-plus-necessary-probes interpretation for A.2/A.5 and reports a direct formal treatment of the previous paper's family for B.1. These statements should not be conflated as identical version descriptions. The later report also discusses the counted-as-one restatement at Theorems 2.6 and 5.8.

**Reproducibility access:** Daniel's complete separate Lean source remains in his own private repository; this consolidated repository contains **Daniel Zhou's reports and certificates only** for his effort; the separate author-coordinated Lean source and reproduction code are included under [`reproducibility/`](../../reproducibility/README.md). The full Lean development and its source commit are identified in the later K report. Neither document is a human sign-off; machine checks and AI statement correspondence have distinct evidentiary roles.

The unchanged originals remain privately preserved. Their Git blob identities are `2c3d8c9cccb4bc485657951c4f5e1648a32d35f1` (PDF) and `1536ab05b8725294f42246017972f41553dc3a52` (certificate).

## Redistribution and shared components

The repository owner explicitly confirmed permission to redistribute these documents. The PDF and certificate are unchanged; their historical confidentiality wording and version limitations are retained. This permission does not include Daniel Zhou's separately maintained Lean source, which is **not copied or replayed here**.

The later PDF itself attributes two auxiliary components to adaptations from the author-coordinated effort:

- Openness of `H_K`, citing HD commit `33488ac`; Daniel's counterpart is `LocalBreadth/K/N1Open.lean`.
- The earlier-paper family for Proposition B.1, citing 1D commit `327ea0f`; Daniel's counterpart is `LocalBreadth/K/PriorZeroPort.lean`.

This is attribution reported by Daniel's supplied document, not a claim that this release inspected or replayed his private source. The two efforts should not be described as entirely disjoint codebases. No full commit identifiers are inferred from those abbreviated citations.

## Explicit inclusion decision

The owner separately authorized these exact report and certificate documents for public inclusion after being informed that they contain historical private-source repository locators. Those locators are intentional provenance disclosures in the unchanged supplied documents, not build dependencies or an inclusion of the private source. No additional personal identity linkage is inferred.
