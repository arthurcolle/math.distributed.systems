# math.distributed.systems

An open research swarm around precise mathematical proof obligations. The public [site](https://arthurcolle.github.io/math.distributed.systems/) combines a 1,000-area MSC atlas, a proof-statused lemma ledger, and a live GitHub task board. Its 499,500 unordered field pairs are an exhaustive index, not 499,500 claims of novelty.

## Join

1. [Introduce yourself or propose a task](https://github.com/arthurcolle/math.distributed.systems/issues/new/choose). Researchers, formalizers, source curators, and counterexample hunters are welcome.
2. [Choose an open task](https://github.com/arthurcolle/math.distributed.systems/issues?q=is%3Aissue+is%3Aopen+label%3Aresearch-task) and comment with the exact piece you will attempt. Maintainers may assign a primary owner; independent approaches are welcome.
3. Submit a pull request with a statement, dependencies, derivation or proof, adversarial test, and reproducible artifact. See [CONTRIBUTING.md](CONTRIBUTING.md).

The task board reads open `research-task` issues from GitHub at runtime and falls back to `data/tasks.json` when the API is unavailable. Issue labels and assignees are the live source of claim and review state. The snapshot is updated when tasks are seeded or materially changed.

## Run and validate

```sh
python3 -I build.py
python3 -I validate_public.py
python3 -I verify_finite.py
python3 -m http.server 8765
```

Open `http://localhost:8765/`. The builder needs only files in this repository. It creates `data/areas.json`, `data/lemmas.index.json`, `data/summary.json`, and audit queues from the committed CSV and lemma cards. The site uses no package install or JavaScript build step.

The browser computes a one-based row for sorted IDs `i<j` as `(i−1)·1000 − i(i−1)/2 + (j−i)`. The 499,500-row pair CSV is generated in the original research workspace but is unnecessary for browsing because the formula gives an exact bijection.

## Proof states and scope

A checked Lean theorem certifies only its exact statement and axioms. It does not certify an upstream manuscript or solve the motivating open problem. Paper proofs, conditional reductions, finite checks, open targets, and counterexamples remain visibly distinct. “New” means new to this local analysis unless a literature audit establishes priority.

The source index is a pinned snapshot of 374 OpenAI result-family catalog entries, four Anthropic Lean projects, and two later upstream records. Catalog descriptions are claims, not independent verification. Source PDFs stay in their upstream repositories. The local Lean files under `lean/` and selected small research artifacts under `artifacts/` carry their own stated proof scope.

The public swarm is a contribution and review system. It does not grant access to the private `fleet-mesh` workers or execute issue/PR content on them. Maintainers can independently reproduce a reviewed submission on isolated infrastructure and attach a receipt.

## Provenance

The selected MSC2020 area titles derive from the [official classification](https://msc2020.org/) maintained by Mathematical Reviews and zbMATH, licensed CC BY-NC-SA. `data/manifest1000.json` records the original source hash and selection rule. Public corpus links are pinned to the local checkout commits used for this snapshot; upstream manuscripts and code retain their own licenses. This repository does not relicense those sources.
