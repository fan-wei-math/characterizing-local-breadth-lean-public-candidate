# Characterizing Local Breadth in Language Generation — reproducible Lean formalization

Author-coordinated Lean sources for the paper by Jon Kleinberg and Fan Wei, with separately attributed historical verification reports. This public release includes the mathematical sources, verification evidence, and instructions for reproducing the formalization.

## Start here

- [Current portable-source certificate](reproducibility/CERTIFICATE.md).
- [Reproduction instructions](reproducibility/README.md).
- [65-result correspondence table](reproducibility/evidence/ASSERTION-CERTIFICATION.md) and [definition inventory](reproducibility/evidence/DEFINITION-REGISTRY.md).
- [Actual fresh verification results](reproducibility/evidence/VERIFICATION-RESULTS.md).
- [Completed privacy review and final-attestation scope](reproducibility/evidence/PRIVACY-REVIEW.md).

```text
reports/
  author/          Privacy-sanitized historical report/certificate copies
  daniel-zhou/     Original permission-covered report and certificate
reproducibility/
  lean/            All 133 mathematical modules and exact dependency pins
  verification/    Registry, fingerprint, axiom, content-identity and replay drivers
  scripts/         Portable fail-closed verification command
  manifests/       Original identities, new public hashes and approved code hashes
  evidence/        Scientific correspondence and fresh execution receipts
```

## Mathematical and source scope

**65 numbered assertion occurrences / 64 distinct results, K65/P0/K*0/Q0 under the recorded correspondence interpretations**. Theorem 5.8 restates Theorem 2.6. **13 of 14 definitions** are represented; Definition 1.2 is unencoded background, not kernel checked. **Five remarks are excluded.** This is AI-assisted manuscript correspondence with selected author review, not independent human sign-off or certification of every manuscript prose proof sentence.

The approved source origins are 1D `5fe0e3e25e230f7d0ee59abc98193631ea67a666`, HD `8d87aa226dc6f81a4ec70e45fc584da828bcfc3c` and the standalone bridge hash in the certificate. **Public source hashes differ where comments were sanitized.** No byte outside a comment was changed. The original sources/manifests remain unchanged privately. New manifests distinguish original hashes, candidate hashes and approved non-comment projections; builds must validate those projections and original frozen declaration fingerprints.

## Reports and provenance

| Effort | Documents | Context |
|---|---|---|
| Author-coordinated | [PDF](reports/author/Verification-Report.pdf), [Markdown](reports/author/Verification-Report.md), [certificate](reports/author/CERTIFICATE.md) | [Historical versions and explicit privacy changes](reports/author/README.md) |
| Daniel Zhou–coordinated | [PDF](reports/daniel-zhou/K-REPORT-Nov1.pdf), [certificate](reports/daniel-zhou/CERTIFICATE.md) | [Permission, version limits and shared components](reports/daniel-zhou/README.md) |

Daniel's documents are unchanged and owner-authorized for public inclusion, including their historical source locators. His separate Lean source is **not included or replayed**. The two reported shared auxiliary adaptations remain attributed. Author-maintained historical links now point to local reproduction counterparts and must not be mistaken for original historical artifacts.

Historical audit documents are preserved as dated evidence. Statements in those documents about private visibility, candidate status, or publication authorization describe the repository's status when they were written.

The original audited release snapshot is [`494f77aa415ccc2b5c5dc36c10c92b27efcefb47`](https://github.com/fan-wei-math/characterizing-local-breadth-lean-public-candidate/tree/494f77aa415ccc2b5c5dc36c10c92b27efcefb47).

## Reproduce

With Git, Bash, Python 3.11+, Elan and Poppler installed:

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install --require-hashes -r reproducibility/scripts/requirements-privacy.txt
bash reproducibility/scripts/verify.sh --all --jobs 2
```

Only included code and pinned public dependencies are needed. No author's local filesystem, private repository or credentials are a build dependency. Actual results distinguish earlier evidence from new executions.

No software license has been invented. The public repository is [fan-wei-math/characterizing-local-breadth-lean-public-candidate](https://github.com/fan-wei-math/characterizing-local-breadth-lean-public-candidate).
