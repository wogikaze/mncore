# Single precision FMA value domain

`ProofsLean.SingleFMA` models the normal MN-Core floating-point formats. The
MN-Core 2 Development Manual, section 1.3 (PDF p. 12), states that floating
point values consist only of normalized values, signed zero, and signed
infinity; denormalized values and NaNs do not exist. It also specifies that an
all-zero exponent encodes zero regardless of the mantissa. This supports the
`SingleFMA.decode` rule that treats every exponent-zero encoding as zero.

The manual separately describes a denormal-like representation for
half-precision block-floating-point conversion with extended representation
(section 3.6.12.12). That representation is not the ordinary single-precision
MAU format and is outside `SingleFMA`'s scope.

The manual's chapter 4 says its floating-point details are sufficient to
implement an emulator matching the actual RRN and MAU at the bit level, except
for half-precision matrix-vector multiply-add with extended representation.
The existing `gpfn3` differential remains useful implementation evidence, but
it is not a formal equivalence proof between the Lean and Rust implementations.

Source: [MN-Core 2 Development Manual (English), sections 1.3 and 4](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_en.pdf).
