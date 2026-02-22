---
agent: agent
---
* Prefer building a single lean file (e.g. `lake build ./CellularAutomatas/examples.lean`).
* Try to decompose proofs. Instead of having one long proof, prefer two shorter ones.
* Use `show` to explicitly state what each proof branch proves — acts as documentation and a correctness check.
* Use `calc` blocks for chains of equivalences/equalities instead of flat sequences of `simp`/`rw`.
* Structure proofs with bullet-separated branches, each with an explicit `show` goal.
* Give meaningful names to `let` bindings (e.g. `combined` not `x`).
* Add comments to explain the main idea.
