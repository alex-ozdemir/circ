`ver_trans::to_r1cs` could probably be improved by manipulating quadratic
forms (A * B - C for linear combinations A, B, C) instead of just LCs. With
LCs, the constraint


    x * x = x

would normally be written down as *two* R1 constraints. One for the
multiplication, and one for the equality. Then, they get optimized.
But this has compile-time cost.

We special case bit-constraints like those above, but it would be good to
better in general...
