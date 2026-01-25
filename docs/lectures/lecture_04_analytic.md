# Lecture 4: Analytic Functions and Cauchy-Riemann Equations

## Complex Differentiability

A function $f: \mathbb{C} \to \mathbb{C}$ is said to be **differentiable** (or **holomorphic**, or **analytic**) at a point $z_0$ if the limit exists:

$$ f'(z_0) = \lim_{z \to z_0} \frac{f(z) - f(z_0)}{z - z_0} $$

This looks just like the definition in real calculus, but it is much stricter. Since $z$ can approach $z_0$ from any direction in the 2D plane, the limit must be the same regardless of the path.

## The Cauchy-Riemann Equations

Let $z = x + iy$ and write $f(z) = u(x, y) + i v(x, y)$, where $u$ and $v$ are real-valued functions.

For $f$ to be differentiable, $u$ and $v$ must satisfy the **Cauchy-Riemann (CR) equations**:

$$ \frac{\partial u}{\partial x} = \frac{\partial v}{\partial y} $$
$$ \frac{\partial u}{\partial y} = -\frac{\partial v}{\partial x} $$

### Example: $f(z) = z^2$

Let's check if $f(z) = z^2$ is analytic.
$$ z^2 = (x+iy)^2 = x^2 - y^2 + i(2xy) $$

So, $u = x^2 - y^2$ and $v = 2xy$.

Calculate partial derivatives:
*   $\frac{\partial u}{\partial x} = 2x$
*   $\frac{\partial v}{\partial y} = 2x$  (Equal! ✅)

*   $\frac{\partial u}{\partial y} = -2y$
*   $\frac{\partial v}{\partial x} = 2y$
*   So $\frac{\partial u}{\partial y} = -\frac{\partial v}{\partial x}$ (Equal! ✅)

Since the CR equations are satisfied, $f(z) = z^2$ is analytic.
