# Lecture 3: The Complex Plane (Geometry)

## The Argand Plane

A complex number $z = x + iy$ is defined by two real numbers, $x$ and $y$. This naturally suggests identifying $z$ with the point $(x, y)$ in the 2D plane.

This geometric representation is called the **Argand plane** (or complex plane).
*   The **x-axis** is the **real axis**.
*   The **y-axis** is the **imaginary axis**.

## Vector Addition

In this geometric view, adding complex numbers corresponds to adding vectors.
If $z = x + iy$ and $w = u + iv$:
$$ z + w = (x+u) + i(y+v) $$

This follows the "parallelogram rule" familiar from physics or linear algebra.

## Polar Form

Instead of using Cartesian coordinates $(x, y)$, we can use **polar coordinates** $(r, \theta)$:
*   $r = |z| = \sqrt{x^2 + y^2}$ is the distance from the origin (the **modulus**).
*   $\theta = \arg(z)$ is the angle formed with the positive real axis (the **argument**).

Using trigonometry:
$$ x = r \cos \theta $$
$$ y = r \sin \theta $$

Substituting these into $z = x + iy$:
$$ z = r (\cos \theta + i \sin \theta) $$

This is the **polar form** of a complex number. It is incredibly useful for multiplication, as we will see in the next lecture.

### Euler's Formula (Preview)
A famous result by Euler states that $e^{i\theta} = \cos \theta + i \sin \theta$.
This allows us to write the polar form even more compactly as:
$$ z = r e^{i\theta} $$
