# A400997 is always even

For positive integers $w$ and $h$, let $T(w,h)$ count tilings of the
rectangle $[0,w] \times [0,h]$ by isosceles right triangles whose vertices
are lattice points and whose legs are parallel to the sides of the rectangle.
Then $a(n)=T(n,n)$ for A400997.

Reflection in the vertical midline $x=w/2$ is an involution on these tilings.
The tilings exchanged by the reflection come in pairs, so $T(w,h)$ has the
same parity as the number of reflection-invariant tilings.

In a reflection-invariant tiling, no tile can have an interior point on
the midline. Such a point would also lie in the interior of the tile's
reflection, since the point itself is fixed. The two tiles would then
coincide, because distinct tiles have disjoint interiors. However, the
reflection reverses the direction of the horizontal leg from the unique
right-angle vertex, so no allowed tile is invariant under this reflection.

Consequently the midline lies along tile boundaries. If $w$ is odd, the
midline has half-integer $x$-coordinate, while every vertical tile edge has
integer $x$-coordinate. Nonvertical tile edges meet the midline in at
most one point each, so they cannot cover it. Hence there are no
reflection-invariant tilings when $w$ is odd.

If $w$ is even, restricting a reflection-invariant tiling to the left half
gives a tiling counted by $T(w/2,h)$. Conversely, any tiling of the left
half extends uniquely to a reflection-invariant tiling by reflecting it into
the right half. Therefore

```math
T(w,h) \equiv T(w/2,h) \pmod{2} \qquad \text{for even } w.
```

Repeatedly halve $w$ until it is odd. This proves that $T(w,h)$ is even
for all positive integers $w$ and $h$. In particular, $a(n)$ is even
for every $n \ge 1$.
