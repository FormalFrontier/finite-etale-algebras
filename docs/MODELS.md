# Basis reconstruction and standard nonreduced models

The finite-etale subalgebra and separable-closure descent results apply even
when the ambient algebra is not reduced.

## Basis-indexed reconstruction

`SeparableClosureDescent.reconstructionMap_surjective_of_basis` accepts a basis
indexed by any type. Under the finite-stage hypotheses, if every ambient basis
vector lies in the range of the finite-stage extension map, the reconstruction
map is surjective. Its linear right inverse is defined by `Module.Basis.constr`;
no `Fintype` instance for the index type is required.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean).

## A nontrivial idempotent in a nonreduced product

Import `FiniteEtaleExamples.IdempotentSubalgebra`.

`IdempotentSubalgebraExample.standard_nonreduced_idempotent` works over every
field `k`. In `B = TrivSqZeroExt k k × k`, it proves that
`η = (TrivSqZeroExt.inr 1, 0)` is nonzero with square zero, so `B` is not reduced.
It also proves that `e = (1, 0)` is idempotent and is neither zero nor one, and
applies `Subalgebra.exists_isFiniteEtale_of_isIdempotentElem` to obtain a
finite-etale `k`-subalgebra containing this `e`. The subalgebra is not required
to contain `η`. Nilpotence is proved, not supplied as a premise.

[Source](../FiniteEtaleExamples/IdempotentSubalgebra.lean).

## Descent of the scalar line in the dual numbers

Import `FiniteEtaleExamples.SeparableClosureDescent`.

For a separable closure `K` of `k`,
`SeparableClosureDescentExample.standard_dual_bot_package` takes
`R = TrivSqZeroExt k k` and the bottom subalgebra of `K ⊗[k] R`.
It proves coefficientwise Galois stability, selects
`SeparableClosureDescent.package` using `Subalgebra.isFiniteEtale_bot`, and
proves that the package's algebra is bottom. It exposes the ambient
reconstruction map, preimage membership and scalar-extension range.

The bottom equality is a separate mathematical conclusion, not a package field.
The augmentation `TrivSqZeroExt.fstHom` identifies the scalar coefficient;
injectivity of the finite-stage extension map detects equality in `R`.
The ambient dual numbers need not be reduced, and their top subalgebra is not
asserted finite etale. The models use Mathlib's square-zero-extension and
tensor-product APIs.

[Source](../FiniteEtaleExamples/SeparableClosureDescent.lean).

## Imports and documentation scope

Both canonical modules are explicit roots of `FiniteEtaleExamples`; the default
build includes that library and `FiniteEtaleAlgebras`.

The Lean sources give the current signatures and proofs. The generated
[API reference](API.md) describes an earlier source snapshot; its exact scope
and reproduction conditions are given in [generation scope](README.md).
