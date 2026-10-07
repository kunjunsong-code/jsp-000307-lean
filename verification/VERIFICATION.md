# Verification record — JSP-000307

Toolchain: leanprover/lean4:v4.20.0 (no Mathlib dependency)
Verified: 2026-10-08

## Clean build
```
$ lake build
Build completed successfully.
```

## Axiom audit
```
Jsp/JSP000307.lean:193:0: 'jsp_000307' depends on axioms: [propext, Quot.sound]
Jsp/JSP000307.lean:194:0: 'jsp_000307_counterexample' depends on axioms: [propext, Quot.sound]
```

No `sorry`, `admit`, `native_decide`, or added `axiom` declarations.
