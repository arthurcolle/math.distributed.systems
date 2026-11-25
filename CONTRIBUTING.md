# Contribute to the math swarm

## Pick a bounded task

Open a `research-task` issue and comment with your intended deliverable. You can work on a task even when another contributor is assigned; mention that you are testing an independent method. For a new problem, use the task proposal form. A good task has a falsifiable bridge lemma or counterexample target, exact dependencies, and a finite or formal stress test.

Use GitHub issues for discussion and pull requests for artifacts. Joining never requires private machine access. Do not post credentials, private manuscripts, or unpublished work you do not have permission to share.

## Submit a proof artifact

In the pull request, include:

1. **Statement:** domains, quantifiers, assumptions, and conclusion.
2. **Dependencies:** source theorem, version or commit, and any axiom, conjecture, or numerical bound used.
3. **Argument:** proof steps or a minimal counterexample. Mark unproved steps explicitly.
4. **Failure test:** a boundary case or stronger false variant, with reproducible input where possible.
5. **Verification:** commands, toolchain versions, output, and hashes for large generated certificates.
6. **Scope:** what the artifact proves and how it relates to the motivating open problem.

For a new card, edit `data/lemmas.json`, put its linked artifact inside this repository, then run `python3 -I build.py` and `python3 -I validate_public.py`. A `source` field may name a pinned public source or explain local provenance; a status must never overstate verification. Use the task issue number in the PR body.

## Review states

`open` means no primary assignee; `claimed` means a primary assignee is recorded; `review` means a PR or manuscript is under review. Closing an issue means its bounded deliverable was resolved, refuted, or superseded; it does **not** imply the parent conjecture is solved. Maintainers check statements, source scope, counterexamples, reproducibility, and Lean axioms before changing a card to “Lean checked.”

The public index validator is read-only. It does not run arbitrary contributed Lean/Python on the private fleet. Reviewers may run submitted code separately after inspecting it. We do not accept a solver's `UNSAT`, a screenshot, or a compiler exit code alone as proof of a headline theorem; provide the exact checked statement and certificate or derivation.

## Source and credit

Credit contributors in the issue/PR and artifact. Link to upstream work instead of copying PDFs. The MSC-derived area data retains its CC BY-NC-SA attribution; upstream corpora retain their own terms. Contributors retain rights in their original submissions. Please flag any licensing ambiguity before adding third-party material.
