# Complex Analysis Topics (Markushevich Textbook Level)

## Undergraduate Complex Analysis Course Syllabus
*Based on A.I. Markushevich's "Theory of Functions of a Complex Variable"*

---

## 1. The Geometric Foundation

### 1.1 Complex Numbers and the Complex Plane
- Complex numbers as ordered pairs and vectors
- Algebraic operations: addition, multiplication, division
- Modulus and argument (polar form)
- De Moivre's theorem
- Roots of complex numbers (nth roots)

### 1.2 The Riemann Sphere and Extended Complex Plane
- Stereographic projection
- The point at infinity ($\infty$)
- Extended complex plane $\mathbb{C} \cup \{\infty\}$
- One-to-one correspondence between $\mathbb{C} \cup \{\infty\}$ and the sphere

### 1.3 Topology of the Complex Plane
- Open and closed sets in $\mathbb{C}$
- Neighborhoods and deleted neighborhoods
- Connectedness and path-connectedness
- Domains and regions (simply connected vs. multiply connected)
- Compact sets and the Heine-Borel theorem
- Convergent sequences and Cauchy sequences
- Completeness of $\mathbb{C}$

### 1.4 Linear Fractional Transformations (Möbius Transformations)
- Definition: $w = \frac{az + b}{cz + d}$ where $ad - bc \neq 0$
- Composition of Möbius transformations
- Fixed points and canonical forms
- Circle preservation: circles map to circles (or lines)
- Cross-ratio and its invariance
- Symmetry with respect to circles and lines
- Applications: conformal mappings of regions

---

## 2. Analytic Functions and Differentiation

### 2.1 Functions of a Complex Variable
- Definition and domain/range
- Limits and continuity
- $\lim_{z \to z_0} f(z) = w_0$ (formal $\epsilon$-$\delta$ definition)
- Continuity: uniform and pointwise

### 2.2 The Derivative
- Complex differentiability
- Definition: $f'(z_0) = \lim_{h \to 0} \frac{f(z_0 + h) - f(z_0)}{h}$
- Differentiation rules (sum, product, quotient, chain rule)
- Higher-order derivatives

### 2.3 The Cauchy-Riemann Equations
- Necessary conditions for differentiability
- Sufficient conditions (continuity of partial derivatives)
- Relation to harmonic functions
- Geometric interpretation: conformality (angle and orientation preservation)

### 2.4 Harmonic Functions
- Definition: $\Delta u = \frac{\partial^2 u}{\partial x^2} + \frac{\partial^2 u}{\partial y^2} = 0$
- Relationship between analytic and harmonic functions
- Real and imaginary parts of analytic functions are harmonic
- Harmonic conjugates
- Maximum and minimum principles for harmonic functions

### 2.5 Elementary Functions
- Exponential function: $e^z = e^{x + iy} = e^x(\cos y + i \sin y)$
  - Properties: $e^{z_1 + z_2} = e^{z_1} e^{z_2}$, periodicity
- Trigonometric functions: $\sin z, \cos z$ (extended to complex domain)
  - Relation to exponential: $\sin z = \frac{e^{iz} - e^{-iz}}{2i}$
- Hyperbolic functions: $\sinh z, \cosh z$
- Logarithmic function: $\log z = \log |z| + i \arg z$
  - Multi-valuedness and branch cuts
  - Principal branch
- Power function: $z^a$ (for complex $a$)
  - Multi-valuedness

---

## 3. Complex Integration and Cauchy Theory

### 3.1 Complex Line Integrals
- Contours and paths in $\mathbb{C}$
- Definition: $\int_C f(z) dz$ as a limit of Riemann sums
- Properties: linearity, reversal of path, bounds on modulus
- Estimation lemmas (ML-inequality)

### 3.2 Antiderivatives and Indefinite Integrals
- Primitive (antiderivative) of $f(z)$
- Fundamental theorem for complex integrals
- Conditions for the existence of antiderivatives

### 3.3 Cauchy-Goursat Theorem (The Central Theorem)
- Statement: If $f$ is analytic in a simply connected domain $D$, then $\oint_C f(z) dz = 0$ for any closed contour $C$ in $D$
- Goursat's proof (without assuming continuity of $f'$)
- Cauchy's original approach (using Green's theorem)
- Extension to multiply connected domains

### 3.4 Cauchy Integral Formula
- Formula: $f(z_0) = \frac{1}{2\pi i} \oint_C \frac{f(z)}{z - z_0} dz$
  - $z_0$ inside $C$, $f$ analytic in simply connected domain
- Derivatives from the integral formula
- $f^{(n)}(z_0) = \frac{n!}{2\pi i} \oint_C \frac{f(z)}{(z - z_0)^{n+1}} dz$
- Cauchy's inequality: $|f^{(n)}(z_0)| \leq \frac{n! M}{r^n}$

### 3.5 Applications of Cauchy's Theorem
- **Liouville's Theorem**: A bounded entire function is constant
- **Fundamental Theorem of Algebra**: Every polynomial of degree $n$ has exactly $n$ zeros (counting multiplicity)
- **Maximum Modulus Principle**: $|f(z)|$ cannot attain its maximum in the interior of a domain
  - Minimum modulus principle (for non-vanishing $f$)
- **Open mapping theorem**: A non-constant analytic function maps open sets to open sets

---

## 4. Series Representations

### 4.1 Convergence of Complex Series
- Infinite series $\sum_{n=0}^{\infty} a_n$ (convergence, absolute convergence)
- Cauchy criterion for convergence
- Geometric series
- Tests for convergence (ratio test, root test, comparison test)

### 4.2 Power Series
- Definition: $\sum_{n=0}^{\infty} a_n (z - z_0)^n$
- Radius of convergence (Cauchy-Hadamard formula)
- Disk of convergence
- Uniform convergence (Weierstrass M-test)
- Continuity and analyticity of power series sums
- Term-by-term differentiation and integration

### 4.3 Taylor Series
- Taylor expansion of analytic functions around $z_0$
- $f(z) = \sum_{n=0}^{\infty} \frac{f^{(n)}(z_0)}{n!} (z - z_0)^n$
- Radius of convergence = distance to nearest singularity
- Taylor series of elementary functions
  - $e^z, \sin z, \cos z, \log(1+z), (1+z)^a$
- Binomial series

### 4.4 Laurent Series
- Laurent expansion around a singularity $z_0$
- $f(z) = \sum_{n=-\infty}^{\infty} a_n (z - z_0)^n = \sum_{n=1}^{\infty} \frac{b_n}{(z-z_0)^n} + \sum_{n=0}^{\infty} a_n (z-z_0)^n$
- Principal part and regular part
- Annulus of convergence
- Uniqueness of Laurent expansion

### 4.5 Singularities and Their Classification
- **Removable singularity**: $f(z) = \sum_{n=0}^{\infty} a_n (z-z_0)^n$ (no negative powers)
  - Riemann's removable singularity theorem
- **Poles of order $m$**: Principal part has finitely many terms, highest power is $(z-z_0)^{-m}$
  - Simple pole, double pole, etc.
- **Essential singularity**: Infinitely many negative powers in Laurent series
  - Casorati-Weierstrass theorem: $f$ takes values arbitrarily close to any complex number near an essential singularity
  - Picard's theorem (great and little): $f$ omits at most one value near an essential singularity
- **Poles at infinity**: Behavior of $f(1/w)$ at $w = 0$

---

## 5. Residue Theory and Applications

### 5.1 Residues
- Definition: Residue $\text{Res}(f, z_0)$ = coefficient of $\frac{1}{z-z_0}$ in Laurent series
- Residue at a simple pole: $\text{Res}(f, z_0) = \lim_{z \to z_0} (z-z_0) f(z)$
- Residue at a pole of order $m$: $\text{Res}(f, z_0) = \frac{1}{(m-1)!} \lim_{z \to z_0} \frac{d^{m-1}}{dz^{m-1}} [(z-z_0)^m f(z)]$
- Residue at essential singularities (extraction from Laurent series)

### 5.2 The Residue Theorem
- **Theorem**: If $f$ is analytic in a simply connected domain except for isolated singularities, then
  $$\oint_C f(z) dz = 2\pi i \sum \text{Res}(f, z_k)$$
  where the sum is over all singularities inside $C$.

### 5.3 Evaluation of Real Integrals
- **Type 1**: Integrals of the form $\int_{-\infty}^{\infty} f(x) dx$
  - Closing the contour with a semicircle in upper half-plane
  - Jordan's lemma for exponential decay
  - Example: $\int_{-\infty}^{\infty} \frac{1}{1+x^2} dx = \pi$

- **Type 2**: Integrals of rational functions of $\cos \theta$ and $\sin \theta$
  - Substitution $z = e^{i\theta}$, converting to residue integral
  - Example: $\int_0^{2\pi} \frac{d\theta}{1 + a\sin\theta}$

- **Type 3**: Integrals involving branch cuts
  - Indenting contours around branch cuts
  - Example: $\int_0^{\infty} \frac{x^{p-1}}{1+x} dx$ (for $0 < p < 1$)

- **Type 4**: Fourier integrals with complex exponentials

### 5.4 Argument Principle
- Argument of a function along a closed contour
- **Argument Principle**: $\frac{1}{2\pi i} \oint_C \frac{f'(z)}{f(z)} dz = N - P$
  - $N$ = number of zeros of $f$ inside $C$ (counting multiplicity)
  - $P$ = number of poles of $f$ inside $C$ (counting multiplicity)

### 5.5 Rouché's Theorem
- **Theorem**: If $f$ and $g$ are analytic inside and on a closed contour $C$, and $|g(z)| < |f(z)|$ on $C$, then $f$ and $f + g$ have the same number of zeros inside $C$.
- Applications: proving existence of zeros, perturbation analysis

---

## 6. Advanced Topics (Markushevich Specialties)

### 6.1 Analytic Continuation
- Concept of function elements and analytic continuation
- Identity theorem: Two analytic functions equal on a set with limit point are identical
- Analytic continuation along a path
- Monodromy theorem (basic statement)
- Riemann surfaces (elementary treatment, geometric intuition)

### 6.2 Infinite Products
- Convergence of infinite products $\prod_{n=1}^{\infty} (1 + u_n)$
- Convergence criteria (similar to series)
- Weierstrass factorization theorem (statement): Every entire function can be written as
  $$f(z) = e^{g(z)} \prod_{n=1}^{\infty} E(z/z_n, p_n)$$
  where $E$ are elementary factors

### 6.3 Riemann Mapping Theorem
- **Statement**: Every simply connected domain $D \neq \mathbb{C}$ is conformally equivalent to the unit disk $|z| < 1$
- Existence and uniqueness (up to Möbius transformations)
- Geometric intuition and significance
- (Full proof likely omitted in undergrad, but statement and implications covered)

### 6.4 Conformal Mapping (Geometric emphasis)
- Definition: Angle-preserving mappings (related to analyticity)
- Conformal mappings preserve local geometry
- Dictionary of standard mappings:
  - Power function $w = z^n$ (local conformal away from origin)
  - Exponential $w = e^z$ (mapping strips to sectors)
  - Logarithm $w = \log z$ (inverse of exponential)
  - Möbius transformations (mapping circles to circles)
  - Joukowski transformation $w = z + \frac{1}{z}$ (airfoil profiles)
  - Schwarz-Christoffel transformation (mapping polygonal regions)

### 6.5 (Optional) Entire Functions and Growth Orders
- Order of an entire function
- Hadamard's theorem on growth
- Picard's theorem on exceptional values

---

## Summary of Key Theorems (Quick Reference)

| Theorem | Statement | Use |
|---------|-----------|-----|
| **Cauchy-Riemann** | $\frac{\partial u}{\partial x} = \frac{\partial v}{\partial y}$, $\frac{\partial u}{\partial y} = -\frac{\partial v}{\partial x}$ | Test analyticity |
| **Cauchy-Goursat** | $\oint_C f(z) dz = 0$ if $f$ analytic in simply connected domain | Simplify integrals |
| **Cauchy Integral Formula** | $f(z_0) = \frac{1}{2\pi i} \oint_C \frac{f(z)}{z-z_0} dz$ | Evaluate $f$ and derivatives |
| **Liouville** | Bounded entire functions are constant | Prove non-existence of certain functions |
| **Maximum Modulus** | $\|f\|$ max on boundary, not interior | Bounds and inequalities |
| **Residue** | $\oint_C f dz = 2\pi i \sum \text{Res}$ | Evaluate real integrals |
| **Argument** | $\frac{1}{2\pi i} \oint \frac{f'}{f} = N - P$ | Count zeros/poles |
| **Rouché** | $\|g\| < \|f\|$ on $C$ ⟹ $N(f) = N(f+g)$ | Prove existence of zeros |
| **Riemann Mapping** | Simply connected $D$ ≅ unit disk $D$ | Bijection between domains |

---

## Typical Exam Topics

1. Prove a function is analytic using Cauchy-Riemann
2. Evaluate $\oint_C f(z) dz$ using residue theorem
3. Find Laurent series around a singularity
4. Classify singularities and find residues
5. Use Rouché or Argument Principle to count zeros
6. Evaluate a definite real integral via contour integration
7. Determine conformal mapping properties of $w = f(z)$
8. Prove properties using Liouville, maximum modulus, etc.
9. Analytic continuation and monodromy
10. Infinite products and factorization theorems

---

## Recommended Problem Areas for Practice

- **Computation**: Residues, Taylor/Laurent series, contour integrals
- **Proofs**: Cauchy-Riemann, Liouville, maximum modulus, argument principle
- **Conceptual**: Singularity classification, conformal mappings, geometric interpretation
- **Applications**: Real integral evaluation, polynomial zeros, mapping properties

