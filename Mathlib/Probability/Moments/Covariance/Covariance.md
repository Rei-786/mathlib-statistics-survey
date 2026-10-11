---
title: "Covariance of real-valued random variables"
source_module: "Mathlib.Probability.Moments.Covariance"
source_path: "Mathlib/Probability/Moments/Covariance.lean"
mathlib_commit: "https://github.com/leanprover-community/mathlib4/commit/5ed2965256430c3649e86755f9576b54eca72435"
last_update: "2026-10-10"
topics:
  - "covariance"
  - "second moments"
  - "independence"
  - "finite sums"
  - "measure maps"
---

# Covariance of real-valued random variables

Mathlib source: [`Mathlib.Probability.Moments.Covariance`](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Probability/Moments/Covariance.lean)

Companion Lean file: [`CovarianceChecks.lean`](CovarianceChecks.lean)

This file defines covariance and proves rules for calculating with it. Its main ingredients are
an expansion into expectations, linearity in each argument, and the fact that independent
square-integrable variables have zero covariance. These results let later proofs reduce a
covariance calculation to smaller calculations already supported by Mathlib.

This survey follows the example's order: mathematical results and their Lean proofs, core
definitions, other public declarations, and scope. It studies the fixed commit above, rather
than claiming to describe the latest version of Mathlib.

| Question answered | Where to read |
| --- | --- |
| What are the core mathematical results? | Sections 1.1–1.3 |
| How does Lean state them precisely? | The Lean blocks and reading guides in Section 1 |
| Where is each assumption used? | The assumption tables under each result; Section 2.3 |
| Which definitions support the results? | Section 2, distinguishing new definitions from imported concepts |
| What other useful APIs does the file provide? | Sections 3.1–3.5, followed by the complete declaration index |

## 1. Mathematical results and Lean translation

### 1.1 Expanding covariance into expectations

**Mathematical statement.** On a probability space, if `X` and `Y` are square-integrable, then

```math
\operatorname{Cov}_\mu(X,Y)
=\mathbb E_\mu[XY]-\mathbb E_\mu[X]\mathbb E_\mu[Y].
```

In words: compute the average of the product, then subtract the product of the two averages.
This is often easier to use than the original definition with two centered variables.

**Lean statement and proof.** The following is the source proof. It uses the surrounding
variables shown here; these declarations explain the otherwise implicit arguments.

```lean
open MeasureTheory
namespace ProbabilityTheory
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {X Y Z T : Ω → ℝ} {μ : Measure Ω}
```

The theorem blocks below are excerpts within this context, not separate standalone files.
The companion file supplies complete executable examples.

```lean
lemma covariance_eq_sub [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
     cov[X, Y; μ] = μ[X * Y] - μ[X] * μ[Y] := by
   simp_rw [covariance, sub_mul, mul_sub]
   repeat rw [integral_sub]
   · simp_rw [integral_mul_const, integral_const_mul, integral_const, probReal_univ,
       one_smul]
     simp
   · exact hY.const_mul _ |>.integrable (by simp)
   · exact integrable_const _
   · exact hX.integrable_mul hY
   · exact hX.mul_const _ |>.integrable (by simp)
   · exact (hX.integrable_mul hY).sub (hX.mul_const _ |>.integrable (by simp))
   · exact (hY.const_mul _ |>.integrable (by simp)).sub (integrable_const _)
```

**How to read the statement.** `X Y : Ω → ℝ` means that each outcome is assigned two real
numbers. `[IsProbabilityMeasure μ]` says the total mass is one. The named hypotheses `hX`
and `hY` say that the variables are square-integrable. Everything after the final colon
and before `:= by` is the conclusion. Here `X * Y` is pointwise multiplication:
`(X * Y) ω = X ω * Y ω`.

**Mathematical proof.** Write `a = E[X]` and `b = E[Y]`. Expand the integrand:

```math
(X-a)(Y-b)=XY-Xb-aY+ab.
```

Taking expectations gives

```math
\mathbb E[XY]-b\mathbb E[X]-a\mathbb E[Y]+ab
=\mathbb E[XY]-ab.
```

The last term stays `ab` because the expectation of a constant on a probability space is
that constant. Splitting the integral is justified by integrability of all the terms.

**How the Lean proof follows these steps.**

| Source step | Plain-language meaning |
| --- | --- |
| `simp_rw [covariance, sub_mul, mul_sub]` | Open the definition and expand the two brackets. |
| `repeat rw [integral_sub]` | Split integrals of differences; this also creates obligations to prove integrability. |
| `integral_mul_const`, `integral_const_mul` | Pull a constant outside an integral. |
| `integral_const`, `probReal_univ`, `one_smul` | Integrate the constant term, using that the total mass is one. |
| `simp` | Cancel the remaining repeated terms. |
| The following `exact` lines | Discharge the integrability obligations generated above. |

**Where the assumptions are used.**

| Assumption | Use in this proof |
| --- | --- |
| `[IsProbabilityMeasure μ]` | Simplifies the integral of a constant; also supplies finiteness of the measure. |
| `hX : MemLp X 2 μ` and `hY : MemLp Y 2 μ` | `hX.integrable_mul hY` makes `X * Y` integrable. |
| The same `MemLp` hypotheses, with finiteness | The `.integrable (by simp)` calls make constant multiples of `X` and `Y` integrable. |
| Measurable space and `μ : Measure Ω` | Provide the common setting in which these integrals are formed. |

### 1.2 Splitting a sum inside covariance

**Mathematical statement.** Under a finite measure, for square-integrable `X`, `Y`, and `Z`,

```math
\operatorname{Cov}_\mu(X+Y,Z)
=\operatorname{Cov}_\mu(X,Z)+\operatorname{Cov}_\mu(Y,Z).
```

In words: the covariance of a sum can be calculated one summand at a time.
This statement needs only a finite measure; its total mass need not be one.

**Lean statement and proof.**

```lean
lemma covariance_add_left [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X + Y, Z; μ] = cov[X, Z; μ] + cov[Y, Z; μ] := by
  simp_rw [covariance, Pi.add_apply]
  rw [← integral_add]
  · congr with x
    rw [integral_add (hX.integrable (by simp)) (hY.integrable (by simp))]
    ring
  · exact (hX.sub (memLp_const _)).integrable_mul (hZ.sub (memLp_const _))
  · exact (hY.sub (memLp_const _)).integrable_mul (hZ.sub (memLp_const _))
```

**Mathematical proof.** First use linearity of the integral to write

```math
(X+Y)-\int(X+Y)\,d\mu
=\left(X-\int X\,d\mu\right)+\left(Y-\int Y\,d\mu\right).
```

Multiply by the centered `Z`, distribute the product, and split the integral into two.
The resulting integrals are exactly the two covariances on the right.

**Reading the proof.** `Pi.add_apply` changes a sum of functions into a sum of their values.
`rw [← integral_add]` combines the two integrals on the right, so Lean can compare the
integrands. `congr with x` reduces this comparison to a fixed outcome `x`, and `ring`
checks the resulting polynomial identity. The final two lines justify combining the integrals.

| Assumption | Use in this proof |
| --- | --- |
| `[IsFiniteMeasure μ]` | Makes constant functions belong to `L²` and allows `L²` functions to be integrated. |
| `hX`, `hY` | Justify splitting the mean of `X + Y`, and keep the centered `X` and `Y` in `L²`. |
| `hZ` | Keeps centered `Z` in `L²`, so each product with it is integrable. |

Together with symmetry and multiplication by a scalar (Section 3.1), this gives bilinearity
on square-integrable functions. Repeating additivity gives the finite-sum rules in Section 3.3.

### 1.3 Independent variables have zero covariance

**Mathematical statement.** If `X` and `Y` are independent and square-integrable, their
covariance is zero. On a probability space, the familiar proof is

```math
\operatorname{Cov}(X,Y)
=\mathbb E[XY]-\mathbb E[X]\mathbb E[Y]
=\mathbb E[X]\mathbb E[Y]-\mathbb E[X]\mathbb E[Y]=0.
```

**Lean statement and proof.**

```lean
lemma IndepFun.covariance_eq_zero (h : X ⟂ᵢ[μ] Y) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
     cov[X, Y; μ] = 0 := by
   by_cases h' : ∀ᵐ ω ∂μ, X ω = 0
   · refine integral_eq_zero_of_ae ?_
     filter_upwards [h'] with ω hω
     simp [hω, integral_eq_zero_of_ae h']
   have := hX.isProbabilityMeasure_of_indepFun X Y (by simp) (by simp) h' h
   rw [covariance_eq_sub hX hY, h.integral_mul_eq_mul_integral
       hX.aestronglyMeasurable hY.aestronglyMeasurable, sub_self]
```

**How to read the statement.** `h : X ⟂ᵢ[μ] Y` is the independence assumption. The theorem
can be called as `h.covariance_eq_zero hX hY`. There is no explicit
`[IsProbabilityMeasure μ]` assumption in this declaration; adding one when describing the
exact Lean statement would hide part of what the source proves.

**Why the proof has two cases.**

1. If `X` is zero almost everywhere, its integral is zero and the centered product is zero
   almost everywhere. `integral_eq_zero_of_ae` finishes this case directly.
2. Otherwise, `hX.isProbabilityMeasure_of_indepFun` derives that `μ` is a probability measure
   from independence and the nonzero `L²` function. The proof then applies the expansion in
   Section 1.1 and the product-expectation identity for independent functions.

Here `∀ᵐ ω ∂μ` means “for almost every outcome with respect to `μ`.” This case split explains
how the implementation obtains the probability-measure condition needed by the expansion.

| Assumption | Use in this proof |
| --- | --- |
| `h : X ⟂ᵢ[μ] Y` | Supplies the product-expectation identity and participates in deriving the probability-measure instance. |
| `hX : MemLp X 2 μ` | Used in that derivation in the nonzero case; also supplies measurability and the expansion's first hypothesis. |
| `hY : MemLp Y 2 μ` | Supplies measurability for the product-expectation identity and the expansion's second hypothesis. |
| The case assumption that `X = 0` almost everywhere | Used only in the first branch to show both its mean and the centered-product integral are zero. |

**Verification.** The companion file checks declaration types with `#check` and applies the
main results in complete Lean examples. The explanations above come from reading the source
proofs; they are not recorded Infoview states. Compilation checks the Lean examples, while
matching the English explanation to the proof requires the source comparisons above.

## 2. Core definitions

### 2.1 The definition introduced here: covariance

**Mathematics.** Let `(Ω, 𝒜)` be a measurable space, let `μ` be a measure on it, and let
`X Y : Ω → ℝ`. Mathlib defines

```math
\operatorname{Cov}_\mu(X,Y)
=
\int_\Omega
  \left(X(\omega)-\int_\Omega X\,d\mu\right)
  \left(Y(\omega)-\int_\Omega Y\,d\mu\right)
\,d\mu(\omega).
```

**Lean.** The exact source declaration is:

```lean
noncomputable def covariance (X Y : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ ω, (X ω - μ[X]) * (Y ω - μ[Y]) ∂μ
```

The expectation-like notation `μ[X]` means `∫ ω, X ω ∂μ`. The file introduces two scoped
notations:

```lean
cov[X, Y; μ]  -- covariance with respect to μ
cov[X, Y]     -- covariance with respect to volume
```

The full probabilistic interpretation applies when `μ` is a probability measure. For a general
measure, the same formula remains a total Lean definition, but `μ[X]` is an integral rather than a
normalized mean.

The companion file confirms the inferred type:

```lean
#check ProbabilityTheory.covariance
```

```text
ProbabilityTheory.covariance
  (X Y : Ω → ℝ) (μ : Measure Ω) : ℝ
```

### 2.2 Imported notation: integrals and expectations

The main new mathematical definition in this file is `covariance`; the notation, measure
classes, integrability predicates, and independence relation are imported from other modules.
They are prerequisites used by the author, not additional definitions created in this file.

`Mathlib.Probability.Notation` defines

```lean
μ[X] = ∫ ω, X ω ∂μ
```

This notation is used in the definition even when `μ` is not known to be a probability measure.
Consequently, the type alone does not assert that `μ[X]` is a probabilistic expectation.

### 2.3 Imported assumptions and their uses

`MemLp X 2 μ` says that `X` is almost-everywhere strongly measurable and has finite `L²` norm.
It supplies three facts repeatedly used by this file:

1. `X` is integrable when `μ` is finite;
2. products of two `L²` functions are integrable;
3. finite sums, differences, and negations remain in `L²`.

**Assumption map.**

| Lean assumption | Mathematical content | Where it is needed |
| --- | --- | --- |
| `{mΩ : MeasurableSpace Ω}` | a measurable structure on the sample space | all integrals and measures |
| `{μ : Measure Ω}` | the measure used for centering and integration | the definition and every theorem |
| `[IsProbabilityMeasure μ]` | `μ univ = 1` | product-minus-means formula, constants, translation invariance |
| `[IsFiniteMeasure μ]` | `μ univ < ∞` | `L² → L¹`, additivity, subtraction, and finite sums |
| `MemLp X 2 μ` | square integrability of `X` | centered-product integrability and finite-sum closure |
| `Integrable X μ` | integrability of `X` | shifting one argument by a constant |
| `AEStronglyMeasurable X (μ.map Z)` | strong measurability modulo null sets | applying `integral_map` to real-valued functions |
| `AEMeasurable Z μ` | measurability of a map modulo null sets | well-behaved pushforward integration |
| `X ⟂ᵢ[μ] Y` | independence of the two functions with respect to `μ` | factorization of the product expectation |
| `[Fintype ι]` or `s : Finset ι` | a finite index collection | covariance of finite sums |

An `IsProbabilityMeasure` is in particular finite, but the file often asks only for
`IsFiniteMeasure` when normalization is irrelevant. This distinction keeps algebraic results
usable for finite non-probability measures.

## 3. Other public declarations and when to use them

### 3.1 Swapping arguments and multiplying by a scalar

The basic structural theorem is symmetry:

```lean
lemma covariance_comm (X Y) : cov[X, Y; μ] = cov[Y, X; μ] := by
  simp_rw [covariance]
  congr with x
  ring
```

It requires no finiteness or integrability assumption: after unfolding the definition, the two
integrands agree pointwise by commutativity of real multiplication.


Multiplication by a scalar is expressed by `covariance_smul_left` and
`covariance_smul_right`. For example, `cov[c • X, Y; μ] = c * cov[X, Y; μ]`.
Here `c • X` is the function whose value at `ω` is `c * X ω`. These homogeneity
results require no finiteness or integrability hypothesis.

### 3.2 Constants, shifts, and differences

Under a probability measure, a constant argument has zero covariance. Adding or subtracting
a constant from one variable also leaves covariance unchanged, provided that variable is
integrable. For example:

```math
\operatorname{Cov}(X+c,Y)=\operatorname{Cov}(X,Y),\qquad
\operatorname{Cov}(c-X,Y)=-\operatorname{Cov}(X,Y).
```

The second formula has a minus sign: `c - X` reverses the centered variable. This is why
`covariance_const_sub_left` differs from `covariance_sub_const_left`.

For `covariance_add_const_left`, the source uses `integral_add hX` to split the mean of
`X + c`, then uses total mass one to cancel `c`. It does not assume that `Y` is integrable:
after cancellation, the two integrands agree pointwise.

For differences of variables, `covariance_sub_left` and `covariance_sub_right` require a
finite measure and `L²` hypotheses. The proof rewrites subtraction as addition of a negative
and reuses additivity. Applying this on both sides gives `covariance_sub_sub`:

```math
\operatorname{Cov}(X-Y,Z-T)
=\operatorname{Cov}(X,Z)-\operatorname{Cov}(X,T)
-\operatorname{Cov}(Y,Z)+\operatorname{Cov}(Y,T).
```

This is useful when both quantities being compared are differences.

### 3.3 Expanding covariance of finite sums

Repeated additivity gives, for finite index types,

```math
\operatorname{Cov}\left(\sum_i X_i,\sum_j Y_j\right)
=\sum_i\sum_j\operatorname{Cov}(X_i,Y_j).
```

The following source declaration inherits `[IsFiniteMeasure μ]`,
`{ι : Type*}`, and `{X : ι → Ω → ℝ}` from `section Sum`. This surrounding condition
is essential even though it is not repeated on the lemma line:

```lean
lemma covariance_sum_sum [Fintype ι] {ι' : Type*} [Fintype ι']
    {Y : ι' → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ) :
    cov[∑ i, X i, ∑ j, Y j; μ] = ∑ i, ∑ j, cov[X i, Y j; μ]
```

The primed declarations use explicit finite sets `s : Finset ι`; the unprimed declarations sum
over every element of a `Fintype`. The proof of `covariance_sum_left'` is induction over a
`Finset`, with `covariance_add_left` as the induction step. The right-hand and double-sum versions
are derived from symmetry and the left-hand result.
**When to use it.** To expand covariance between two totals, apply this theorem once
rather than repeatedly splitting sums by hand. Finiteness of the measure and the `L²`
conditions justify each application of additivity; `memLp_finsetSum'` verifies that
the intermediate finite sums remain in `L²`.

### 3.4 Changing the space on which covariance is calculated

If `Z : Ω' → Ω`, covariance under the pushforward `μ.map Z` agrees with covariance of the pulled
back variables:

```math
\operatorname{Cov}_{Z_*\mu}(X,Y)
=\operatorname{Cov}_\mu(X\circ Z,Y\circ Z).
```

Here `Ω` and `Ω'` are measurable spaces, `X Y : Ω → ℝ`, and `μ : Measure Ω'`.
With this context, Lean provides:

```lean
lemma covariance_map {Z : Ω' → Ω}
    (hX : AEStronglyMeasurable X (μ.map Z))
    (hY : AEStronglyMeasurable Y (μ.map Z))
    (hZ : AEMeasurable Z μ) :
    cov[X, Y; μ.map Z] = cov[X ∘ Z, Y ∘ Z; μ]
```

The proof applies `integral_map` to the expectations and to the centered product. A measurable
equivalence has a separate theorem, `covariance_map_equiv`, whose stronger structure discharges
the change-of-variables conditions automatically. `covariance_map_fun` merely displays the two
compositions as explicit lambdas.
**When to use it.** Use this to move a covariance calculation from a distribution
`μ.map Z` back to the original space where `Z` is defined. The assumptions on `X`
and `Y` also make their centered product almost-everywhere strongly measurable;
`hZ` justifies applying the change-of-variables theorem to the map.

### 3.5 Functions of separate product coordinates

For probability measures `μ` and `ν`, a function of the first coordinate and a function of the
second coordinate have zero covariance under `μ.prod ν`:

The source places this declaration inside a section with
`[IsProbabilityMeasure μ] [IsProbabilityMeasure ν]`, `X : Ω → ℝ`, and `Y : Ω' → ℝ`.
These probability-measure assumptions are part of the theorem, even though inherited.

```lean
lemma covariance_fst_snd_prod
    (hfμ : MemLp X 2 μ) (hgν : MemLp Y 2 ν) :
    cov[fun p ↦ X p.1, fun p ↦ Y p.2; μ.prod ν] = 0
```

The proof uses independence of the two coordinate projections and then invokes
`IndepFun.covariance_eq_zero`. The `MemLp` hypotheses are transported to the product space by
`comp_fst` and `comp_snd`.
### 3.6 Complete declaration index

Use this table to find a name after identifying the calculation you need. All 53 named
`def`/`lemma` declarations in the surveyed source appear below; notation declarations are
explained in Section 2.1.

The file's declarations fall into the following groups. Names containing `fun` state the same
mathematics with an explicit lambda, which is often easier to match against a user's goal.

| Mathematical role | Lean declarations | Main assumptions |
| --- | --- | --- |
| Definition | `covariance` | none beyond measurable space and measure |
| Product-minus-means identity | `covariance_eq_sub` | probability measure; both variables in `L²` |
| Zero arguments and zero measure | `covariance_zero_left`, `covariance_zero_right`, `covariance_zero_measure` | none |
| Symmetry | `covariance_comm` | none |
| Constant argument | `covariance_const_left`, `covariance_const_right` | probability measure |
| Translation invariance | `covariance_add_const_left`, `covariance_const_add_left`, `covariance_add_const_right`, `covariance_const_add_right` | probability measure; shifted variable integrable |
| Additivity | `covariance_add_left`, `covariance_add_right` | finite measure; variables in `L²` |
| Scalar multiplication | `covariance_smul_left`, `covariance_smul_right`, `covariance_const_mul_left`, `covariance_const_mul_right`, `covariance_mul_const_left`, `covariance_mul_const_right` | none |
| Division by a scalar | `covariance_fun_div_left`, `covariance_fun_div_right` | none; division by zero follows the field convention |
| Negation | `covariance_neg_left`, `covariance_fun_neg_left`, `covariance_neg_right`, `covariance_fun_neg_right` | none |
| Subtraction | `covariance_sub_left`, `covariance_fun_sub_left`, `covariance_sub_right`, `covariance_fun_sub_right`, `covariance_sub_sub`, `covariance_fun_sub_fun_sub` | finite measure; variables in `L²` |
| Subtracting constants | `covariance_sub_const_left`, `covariance_const_sub_left`, `covariance_sub_const_right`, `covariance_const_sub_right` | probability measure; relevant variable integrable |
| Finite sum in one argument | `covariance_sum_left'`, `covariance_sum_left`, `covariance_fun_sum_left'`, `covariance_fun_sum_left`, `covariance_sum_right'`, `covariance_sum_right`, `covariance_fun_sum_right'`, `covariance_fun_sum_right` | finite measure; every summand in `L²` |
| Finite sums in both arguments | `covariance_sum_sum'`, `covariance_sum_sum`, `covariance_fun_sum_fun_sum'`, `covariance_fun_sum_fun_sum` | finite measure; every summand in `L²` |
| Measurable change of variables | `covariance_map_equiv`, `covariance_map`, `covariance_map_fun` | appropriate almost-everywhere measurability |
| Independent variables | `IndepFun.covariance_eq_zero` | independence; both variables in `L²` |
| Independent product coordinates | `covariance_fst_snd_prod` | two probability measures; coordinate variables in `L²` |

Several right-hand theorems are intentionally short: they swap the arguments with
`covariance_comm`, apply the left-hand theorem, and swap back. Likewise, most explicit-lambda
variants are compatibility lemmas proved by `convert!` and simplification rather than new
mathematics.

## 4. Scope and boundary conditions

### 4.1 Total definition versus the standard probability concept

The definition has no integrability hypothesis. Mathlib's Bochner integral is a total function and
returns zero for a non-integrable integrand. Therefore `covariance X Y μ` always denotes a real
number, while the familiar probabilistic properties are exposed through theorems whose hypotheses
ensure the required integrability and normalization. Users should not infer from the bare term
`cov[X, Y; μ]` that `X` and `Y` are square-integrable or that `μ` is a probability measure.

### 4.2 Constants require normalization

For an arbitrary finite measure,

```math
\int_\Omega c\,d\mu=c\,\mu(\Omega),
```

so the centered constant is `c - c μ(Ω)`. It vanishes automatically only when `μ(Ω)=1` (or in
special degenerate cases). This explains why `covariance_const_left` and translation invariance
ask for `IsProbabilityMeasure μ`, while symmetry and scalar homogeneity do not.

### 4.3 Variance is downstream

The module docstring lists `covariance_self`, but that declaration is not defined in this source
file. It is defined downstream in
[`Mathlib.Probability.Moments.Variance`](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Probability/Moments/Variance.lean#L197-L201):

```lean
lemma covariance_self {X : Ω → ℝ} (hX : AEMeasurable X μ) :
    cov[X, X; μ] = Var[X; μ]
```

The dependency direction is: `Variance.lean` imports covariance and then connects it to
the already developed variance API. Importing `Covariance.lean` alone does not make
`covariance_self` available. The current module docstring could state the downstream location
explicitly.

### 4.4 Vector-valued covariance is downstream

This file handles pairs of real-valued functions. The later modules
`CovarianceBilinDual.lean` and `CovarianceBilin.lean` build covariance bilinear forms and covariance
operators for measures on normed or inner-product spaces. In finite-dimensional settings these
objects provide the structure behind covariance matrices. Therefore the lack of a matrix-valued
definition in this file is a module boundary rather than a complete absence from Mathlib.

### 4.5 Finite sums only

The API distributes covariance over `Finset` and `Fintype` sums. There is no result in this file for
countable series or limits of covariances. Such a theorem would need convergence and domination
hypotheses, so it belongs to a separate analytic layer.

### 4.6 Zero covariance is weaker than independence

The file proves independence implies zero covariance and does not offer the converse. That is the
correct mathematical boundary: dependent variables can be uncorrelated. A future teaching note
or counterexample would help prevent users from treating `covariance_eq_zero` as an independence
criterion.

## 5. Discussion and possible documentation improvements

The file already supplies the basic tools for scalar covariance calculations. A useful small
improvement would be to clarify that the header's `covariance_self` reference points to
`Variance.lean`. Cross-references to the later covariance modules would also help readers
find related results without mistaking a module boundary for a library-wide omission.

For comparison with a probability textbook such as Kallenberg's *Foundations of Modern
Probability*, the natural topics are the centered-product definition, the expansion in
Section 1.1, bilinearity, independence, and the relation to variance. This survey does not
claim a verified theorem-by-theorem or page-by-page correspondence with that book.

Covariance inequalities, correlation coefficients, and convergence results are possible
follow-up search topics. Their absence from this source file does not establish that they
are missing from Mathlib; that would require a separate library-wide audit. The discussion
here is limited to this file's scope and discoverability.

## 6. References

- Mathlib source at the surveyed commit:
  [`Covariance.lean`](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Probability/Moments/Covariance.lean).
- Mathlib documentation:
  [`Mathlib.Probability.Moments.Covariance`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/Covariance.html).
- Mathlib variance connection:
  [`Variance.lean`](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Probability/Moments/Variance.lean#L197-L201).
- Mathlib vector-valued covariance:
  [`CovarianceBilin.lean`](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Probability/Moments/CovarianceBilin.lean).
- Olav Kallenberg, *Foundations of Modern Probability*, 3rd ed., Springer, 2021,
  DOI: [10.1007/978-3-030-61871-1](https://doi.org/10.1007/978-3-030-61871-1). General background reference; no specific theorem or page correspondence is asserted here.
