# Repository content and publication policy

Target: **huam54925-cpu/uav-routing-certification**, normal branch `main`.

## Published material

- Paper source, bibliography, figures, original published PDFs and the separately identified correction.
- Original problem statements and spreadsheet inputs/templates, with attribution.
- Question 1–3 program source, tests, requirements and selected published result attachments used by those programs or the paper.
- Research source, curated reports, and frozen selected witnesses/certificates needed for verification or documented warm starts.
- Lean source, audit source, reproducible project configuration and dependency pins.
- Authored provenance, mathematical status, model correspondence and reproduction instructions.

The selected historical JSON files are fixed reference inputs: problem instances, route witnesses, exact dual certificates and the originally published question 2–3 solution attachments. They are not a destination for new run output. Their embedded historical search metadata is not an additional verification claim. Redundant certificate/instance copies are retained only where unmodified historical programs require a particular adjacent path; these copies must agree.

## Local-only material

Keep raw logs, command/audit dumps, generated run summaries, queue state/progress, snapshot ZIPs, chat/API dumps, credentials, scratch files, downloaded dependencies and build products out of commits. Use ignored `verification/runs/` for new runs. Do not force-add ignored files or rename output to evade this rule. Historical raw archives remain referenced at the original repository; they are not republished here.

## Review and preservation

Preserve proof commit `0d4466cbfacf3fe01ca98494663742f9a612b645` as the historical Lean source baseline. Keep the original paper and its later correction distinct. Never describe an old PASS as a newly performed check. The new standalone Lake package has not yet been rebuilt in a fresh environment.

Stage explicit paths and deletions and inspect the staged diff. Verify the repository URL before publishing. Use ordinary commits and non-forced pushes. A request to publish here does not authorize deleting old repositories/branches, rewriting history, changing visibility or contacting maintainers. Preserve the repository's existing license and attribution.
