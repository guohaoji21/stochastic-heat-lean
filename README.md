# A Counterexample to Single-Control Null Controllability of Stochastic Heat Equations

Lean 4 formalization accompanying the paper by Feizheng Huang and Zhaobo Liu.

## Theorem entry points

- [Dirichlet counterexample](lean/HeatPaperMain.lean) — for a fixed smooth noise multiplier and nonzero initial state satisfying the paper's hypotheses, every positive terminal time and every progressively measurable localized drift control of finite expected energy leave a positive probability of a nonzero terminal state.
- [Periodic Gevrey corollary](lean/HeatPaperGevreyVariational.lean) — null controllability for real Gevrey-1 multipliers and a counterexample for every order greater than one. In the counterexample, the multiplier and initial state are fixed before choosing the terminal time or control.
- [Periodic variational solution](lean/HeatTorusVariationalSolution.lean) — mild and Sobolev variational solutions agree in the predictable product space and at the terminal time. The continuous variational path has a square-integrable supremum norm and predictable square-integrable spatial weak gradients.

The package uses Lean 4.35.0 and the revisions pinned in `dependencies/lake-manifest.json`. The [declaration audit](evidence/owned-declarations-20261125.log) checked 6,885 declarations in 517 project modules. Their axiom dependencies were contained in `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduce

Install Git, Python 3.10 or later, and Elan. Run from the repository root.

```sh
cd dependencies
lake exe cache get
cd ..
python reproduce/rebuild.py dependencies/.lake/packages _build --jobs 1
```

For the two theorem entry modules, add `--target HeatPaperMain --target HeatPaperGevreyVariational`. Target mode checks every declaration in each selected module against the axiom allowlist. Initial dependency preparation requires network access. The script uses content fingerprints to check cached build objects when resuming.

Check the source package with `python reproduce/check_sha256.py`. Upstream revisions and license notices are in [DEPENDENCIES.txt](DEPENDENCIES.txt) and [dependencies](dependencies/).
