const std = @import("std");
const min = std.math.min;
const max = std.math.max;
const absInt = std.math.absInt;
const testing = std.testing;
const debug = std.debug;

fn SignedInt(comptime bit_count: u16) type {
    return std.meta.Int(.signed, bit_count);
}

fn EuclidDiv(comptime T: type) type {
    return struct {
        q: T, r: T
    };
}

/// Computes the Euclidian division (and requiring b > 0) such that
/// b * q + r = a    0 <= r < b
fn eucliddiv(comptime T: type, a: T, b: T) EuclidDiv(T) {
    const q = @divFloor(a, b);
    const r = @mod(a, b);
    return EuclidDiv(T){ .q = q, .r = r };
}

pub const RationalError = error{ ZeroDenominator, SignedOverflow };

/// Represents a subset of the field of Rationals (commonly referred to as Q). A rational is a number of the form (a / b) with b != 0.
///
/// The range represented is determined by the bit_count comptime variable, which is the number of bits to use for the underlying
/// signed integers.
///
/// A rational is said to be "irreducible", if the numerator and denominator share no common factors other than 1, i.e gcd(a, b) = 1.
///
/// Formally, the rationals are equivalence classes where for example (4/2) and (2/1) represent the same rational (class).
pub fn Rational(comptime bit_count: u16) type {
    return struct {
        const Self = @This();
        // A signed int of bit_count size.
        pub const T = SignedInt(bit_count);

        pub const zero = Self{ .numerator = 0, .denominator = 1 };
        pub const one = Self{ .numerator = 1, .denominator = 1 };
        pub const half = Self{ .numerator = 1, .denominator = 2 };

        /// Sign is stored on the numerator.
        numerator: T,
        denominator: T,

        /// Creates a new Rational, reducing it in the process if possible.
        pub fn new(n: T, d: T) !Self {
            if (d == 0)
                return RationalError.ZeroDenominator;

            if (d == -1 and n < -std.math.maxInt(T))
                return RationalError.SignedOverflow;

            if (n == 0)
                return zero;

            const gcd: T = if (n >= -std.math.maxInt(T)) gcdBinary(T, n, d) else 1;

            var nr = @divTrunc(if (d < 0) -n else n, gcd);
            var dr = @divTrunc(if (d < 0) -d else d, gcd);

            return Self{
                .numerator = nr,
                .denominator = dr,
            };
        }

        /// Adds two Rationals using the identity (a/b) + (c/d) = (ad+bc)/(bd).
        /// If an overflow were to occur, the result is RationalError.SignedOverflow.
        /// The resulting rational may not be irreducible.
        pub fn add(self: Self, other: Self) !Self {
            if (self.denominator == other.denominator) {
                var n: T = 0;
                if (@addWithOverflow(T, self.numerator, other.numerator, &n))
                    return RationalError.SignedOverflow;
                return Self.new(n, other.denominator);
            } else {
                var a: T = 0;
                if (@mulWithOverflow(T, self.numerator, other.denominator, &a))
                    return RationalError.SignedOverflow;
                var b: T = 0;
                if (@mulWithOverflow(T, self.denominator, other.numerator, &b))
                    return RationalError.SignedOverflow;

                var n: T = 0;
                if (@addWithOverflow(T, a, b, &n))
                    return RationalError.SignedOverflow;

                var d: T = 0;
                if (@mulWithOverflow(T, self.denominator, other.denominator, &d))
                    return RationalError.SignedOverflow;

                return Self.new(n, d);
            }
        }

        /// Equivalent to add, but with one rational negated.
        pub fn sub(self: Self, other: Self) !Self {
            var b = try other.negate();
            return self.add(b);
        }

        /// Multiplies two rationals.
        pub fn mul(self: Self, other: Self) !Self {
            var n: T = 1;
            if (@mulWithOverflow(T, self.numerator, other.numerator, &n))
                return RationalError.SignedOverflow;
            var d: T = 1;
            if (@mulWithOverflow(T, self.denominator, other.denominator, &d))
                return RationalError.SignedOverflow;
            return Self.new(n, d);
        }

        /// Returns the order of two rationals (x = a/b, y = c/d) without causing overflows.
        /// The method used may perform many iterations of division.
        /// If speed is an issue, but not memory, consider allocating larger integers and compare ad < bc
        pub fn order(x: Self, y: Self) std.math.Order {
            // x = a/b, y = c/d

            // The following assumes x and y are irreducible.

            // a   = qb + r     where  0 <= r   < b, q integer
            // a/b = q  + r/b   where  0 <= r/b < 1
            // a/b = q  + r/b < q + 1
            // and clearly q < a/b

            // Then a/b = q + r1/b < q + 1    q integer
            //      c/d = p + r2/d < p + 1    p integer
            // Now if q < p then:
            //     a/b < q + 1 <= p <= p + r2/d = c/d
            // Or if q = p then:
            //     if r1 or r2 is 0, stop and return the answer
            //     else:
            //       "recurse" with the comparison d/r2 < b/r1      [1]
            // Or if q > p then:
            //    c/d < a/b
            var u_denom = x.denominator;
            var v_denom = y.denominator;

            var u = eucliddiv(T, x.numerator, u_denom);
            var v = eucliddiv(T, y.numerator, v_denom);

            while (true) {
                if (u.q < v.q) {
                    return std.math.Order.lt;
                } else if (u.q == v.q) {
                    if (u.r == 0 and v.r == 0) {
                        return std.math.Order.eq;
                    } else if (u.r == 0) {
                        return std.math.Order.lt;
                    } else if (v.r == 0) {
                        return std.math.Order.gt;
                    }

                    // "Recurse" on the remainder, using [1] above.
                    const new_u_denom = v.r;
                    const new_v_denom = u.r;

                    const new_u = u;
                    u = eucliddiv(T, v_denom, v.r);
                    v = eucliddiv(T, u_denom, new_u.r);

                    u_denom = new_u_denom;
                    v_denom = new_v_denom;
                } else {
                    return std.math.Order.gt;
                }
            }
        }

        /// Returns the absolute value.
        ///
        /// Preconditions:
        /// - `numerator >= -max(T)`
        ///
        /// `abs(min(T))` on a Two's complement machine may not fit into T.
        pub fn abs(self: Self) !Self {
            return if (self.numerator < 0)
                try self.negate()
            else
                self;
        }

        /// Preconditions:
        /// - `numerator >= -max(T)`
        ///
        /// `-min(T)` on a Two's complement machine may not fit into T.
        pub fn negate(self: Self) !Self {
            return if (self.numerator < -std.math.maxInt(T))
                RationalError.SignedOverflow
            else
                Self{ .numerator = -self.numerator, .denominator = self.denominator };
        }

        /// Computes the mediant of two Rationals, a/b and c/d as:
        /// ```
        /// (a + c)/(b + d)
        /// ```'
        pub fn mediant(self: Self, b: Self) !Self {
            var result: T = 0;
            if (@addWithOverflow(T, self.numerator, b.numerator, &result))
                return RationalError.SignedOverflow;

            const numerator = result;

            if (@addWithOverflow(T, self.denominator, b.denominator, &result))
                return RationalError.SignedOverflow;

            const denominator = result;

            return Self.new(numerator, denominator);
        }

        pub const ApproximationOptions = struct {
            /// Will not allow a denominator larger than this. Must be non-zero. Sign is ignored.
            /// Setting this to 1 effectively forces a rational that corresponds to an integer.
            /// Defaults to max(T) which implies the result is just the same rational.
            largest_denominator: T = std.math.maxInt(T),
        };

        /// Attempts to find a Rational that approximates this one.
        ///
        /// Preconditions:
        ///  - options.largest_denominator != 0
        pub fn approximate(self: Self, options: Self.ApproximationOptions) !Self {
            if (options.largest_denominator == 0)
                return RationalError.ZeroDenominator;
            if (options.largest_denominator < -std.math.maxInt(T))
                return RationalError.SignedOverflow;
            const largest_denominator = absInt(options.largest_denominator) catch unreachable;

            // We'll do a binary search on a Stern-Brocot tree.
            var lower = try Self.new(0, 1);
            var upper: ?Self = null; // null signifies 1/0 which "represents" infinity.
            var s = try self.abs();

            var med = lower;
            while (std.math.Order.eq != Self.order(s, lower)) {
                if (upper) |upper_val| {
                    // standard case.
                    med = try lower.mediant(upper_val);
                } else {
                    // "upper is infinity"
                    var numerator: T = 0;
                    if (@addWithOverflow(T, lower.numerator, 1, &numerator))
                        return RationalError.SignedOverflow;

                    med = Self{ .numerator = numerator, .denominator = lower.denominator };
                }

                if (med.denominator > largest_denominator)
                    break;

                switch (Self.order(s, med)) {
                    std.math.Order.lt => upper = med,
                    std.math.Order.eq => lower = med,
                    std.math.Order.gt => lower = med,
                }
            }

            return if (self.numerator < 0)
                lower.negate()
            else
                lower;
        }

        pub fn format(value: Self, comptime fmt: []const u8, options: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("({}/{})", .{ value.numerator, value.denominator });
        }
    };
}

pub const R8 = Rational(8);
pub const R16 = Rational(16);
pub const R32 = Rational(32);
pub const R64 = Rational(64);

/// Computes the greatest common divisor d using the binary GCD algorithm.
///
/// Always returns a positive number (> 0).
/// On Two's complement machines, this is undefined when a or b is less than -maxInt(T), as it's absolute value is larger than
/// any positive value of T.
///
/// Algorithmic complexity is O(n^2) where n is the bitcount of T.
fn gcdBinary(comptime T: type, a: T, b: T) T {
    comptime {
        if (!std.meta.trait.isSignedInt(T)) {
            @compileError("Not a signed integer.");
        }
    }

    comptime const lesser_maxInt: bool = -std.math.maxInt(T) > std.math.minInt(T);

    if (lesser_maxInt and (a < -std.math.maxInt(T) or b < -std.math.maxInt(T))) {
        unreachable;
    }

    var u = absInt(a) catch unreachable;
    var v = absInt(b) catch unreachable;

    if (u == v) {
        if (u == 0)
            return 1;
        return u;
    }
    if (u == 0)
        return v;
    if (v == 0)
        return u;

    const u_factors_of_two = @intCast(std.math.Log2Int(T), @ctz(T, u));
    const v_factors_of_two = @intCast(std.math.Log2Int(T), @ctz(T, v));
    // The exponent of 2 factors in common.
    var d = min(u_factors_of_two, v_factors_of_two);

    // Remove common 2 factors.
    u = @shrExact(u, d);
    v = @shrExact(v, d);

    // Store these for later, we need to add them back in.
    const common_2_factors = @shlExact(@as(T, 1), d);

    while (true) {
        const u_even = @rem(u, 2) == 0;
        const v_even = @rem(v, 2) == 0;

        // gcd(0, 0) = 1
        if (u == v and u == 0)
            return common_2_factors;
        // gcd(k, k) == k
        if (u == v)
            return common_2_factors * u;
        // gcd(u, 0) == u
        if (u == 0)
            return common_2_factors * v;
        // gcd(0, v) == v
        if (v == 0)
            return common_2_factors * u;

        if (u_even) { // gcd(2u, v) == gcd(u, v)
            u = @shrExact(u, 1);
        } else if (v_even) { // gcd(u, 2v) == gcd(u, v)
            v = @shrExact(v, 1);
        } else { // gcd(u, v) == gcd(|u - v|, min(u, v)) when u and v both are odd.
            const temp = absInt(u - v) catch unreachable;
            v = min(u, v);
            u = temp;
        } // this last branch makes the loop terminate sooner or later, since at some point |u-v| = 0.
    }
}

// first_primes 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97

test "gcdBinary" {
    // Common edge cases.
    testing.expectEqual(gcdBinary(SignedInt(32), 4, 0), 4);
    testing.expectEqual(gcdBinary(SignedInt(32), 0, 4), 4);
    testing.expectEqual(gcdBinary(SignedInt(32), 0, 0), 1);

    const maxInt = std.math.maxInt(SignedInt(32));
    testing.expectEqual(gcdBinary(SignedInt(32), maxInt, 0), maxInt);
    testing.expectEqual(gcdBinary(SignedInt(32), maxInt, 1), 1);

    // General cases.
    testing.expectEqual(gcdBinary(SignedInt(32), 4, 2), 2);
    testing.expectEqual(gcdBinary(SignedInt(32), 7 * 5 * 3, 11 * 2 * 5 * 3), 5 * 3);
    testing.expectEqual(gcdBinary(SignedInt(32), 7, 11), 1);
    testing.expectEqual(gcdBinary(SignedInt(32), 1, 11), 1);
    testing.expectEqual(gcdBinary(SignedInt(32), 2 * 2 * 2, 2 * 3), 2);

    testing.expectEqual(gcdBinary(SignedInt(32), -2 * 11, 11), 11);
    testing.expectEqual(gcdBinary(SignedInt(32), -2 * 11, -11), 11);
    testing.expectEqual(gcdBinary(SignedInt(32), -2 * 11, -2 * 11), 2 * 11);

    testing.expectEqual(gcdBinary(SignedInt(32), 29 * 37 * 41, 37 * 61 * 61), 37);
}

test "Rational.new" {
    const r = try R32.new(2, 3);
    testing.expectEqual(r.numerator, 2);
    testing.expectEqual(r.denominator, 3);

    // Reduce by default:
    const r2 = try R32.new(5 * 2 * 2, 5 * 2);
    testing.expectEqual(r2.numerator, 2);
    testing.expectEqual(r2.denominator, 1);

    // only store sign on the numerator:
    const r3 = try R32.new(-5, -5);
    testing.expectEqual(r3.numerator, 1);
    testing.expectEqual(r3.denominator, 1);

    const r4 = try R32.new(5, -5);
    testing.expectEqual(r4.numerator, -1);
    testing.expectEqual(r4.denominator, 1);

    const r5 = R32.new(3, 0);
    testing.expectError(RationalError.ZeroDenominator, r5);

    // If zero numerator, simplify to zero().
    const r6 = try R32.new(0, 12);
    testing.expectEqual(r6.numerator, 0);
    testing.expectEqual(r6.denominator, 1);

    // -min(T) is troublesome on Two's complement.
    const r7 = R32.new(std.math.minInt(SignedInt(32)), -1);
    testing.expectError(RationalError.SignedOverflow, r7);
}

test "eucliddiv" {
    const S8 = SignedInt(8);

    var val = eucliddiv(S8, 1, 11);
    testing.expectEqual(val.q, 0);
    testing.expectEqual(val.r, 1);

    val = eucliddiv(S8, 11, 1);
    testing.expectEqual(val.q, 11);
    testing.expectEqual(val.r, 0);

    val = eucliddiv(S8, 7, 7);
    testing.expectEqual(val.q, 1);
    testing.expectEqual(val.r, 0);
}

test "Rational.order" {

    // Sign is taken into account.
    var a = try R8.new(1, 2);
    var b = try R8.new(1, -2);
    testing.expectEqual(R8.order(a, b), std.math.Order.gt);
    testing.expectEqual(R8.order(b, a), std.math.Order.lt);

    // Equality.
    a = try R8.new(3, 11);
    b = try R8.new(3, 11);
    testing.expectEqual(R8.order(a, b), std.math.Order.eq);
    testing.expectEqual(R8.order(b, a), std.math.Order.eq);

    // Reduced or not shouldn't matter.
    a = try R8.new(3 * 7, 11 * 7);
    b = try R8.new(3, 11);
    testing.expectEqual(R8.order(a, b), std.math.Order.eq);
    testing.expectEqual(R8.order(b, a), std.math.Order.eq);

    // Reciprocal.
    a = try R8.new(1, 11);
    b = try R8.new(11, 1);
    testing.expectEqual(R8.order(a, b), std.math.Order.lt);
    testing.expectEqual(R8.order(b, a), std.math.Order.gt);

    // Overflow proof.
    a = try R8.new(1, 127);
    b = try R8.new(127, 1);
    testing.expectEqual(R8.order(a, b), std.math.Order.lt);
    testing.expectEqual(R8.order(b, a), std.math.Order.gt);

    a = try R8.new(126, 127);
    b = try R8.new(126, 127);
    testing.expectEqual(R8.order(a, b), std.math.Order.eq);
    testing.expectEqual(R8.order(b, a), std.math.Order.eq);

    a = try R8.new(5, 8);
    b = try R8.new(3, 5);
    testing.expectEqual(R8.order(a, b), std.math.Order.gt);
    testing.expectEqual(R8.order(b, a), std.math.Order.lt);
}

test "Rational.mediant" {

    // Easy cases
    var a = try R8.new(1, 2);
    var b = try R8.new(2, 6);
    var c = try a.mediant(b);
    testing.expectEqual(c.numerator, 2);
    testing.expectEqual(c.denominator, 5);

    a = try R8.new(1, 2);
    b = try R8.new(2, 7);
    c = try a.mediant(b);
    testing.expectEqual(c.numerator, 1);
    testing.expectEqual(c.denominator, 3);

    a = try R8.new(-1, 2);
    b = try R8.new(1, 7);
    c = try a.mediant(b);
    testing.expectEqual(c.numerator, 0);
    testing.expectEqual(c.denominator, 1);

    // Overflow cases.
    a = try R8.new(127, 2);
    b = try R8.new(1, 6);
    var d = a.mediant(b);
    testing.expectError(RationalError.SignedOverflow, d);

    a = try R8.new(126, 127);
    b = try R8.new(1, 1);
    d = a.mediant(b);
    testing.expectError(RationalError.SignedOverflow, d);
}

test "Rational.mul" {
    var a = try R32.new(1, 5);
    var b = try R32.new(3, 5);
    var c = try a.mul(b);
    testing.expectEqual(c.numerator, 3);
    testing.expectEqual(c.denominator, 25);

    a = try R32.new(3, 5);
    b = try R32.new(4, 7);
    c = try a.mul(b);
    testing.expectEqual(c.numerator, 12);
    testing.expectEqual(c.denominator, 35);
}

test "Rational.add" {
    // Common denominator doesn't need cross-multiplication.
    var a = try R32.new(2, 5);
    var b = try R32.new(4, 5);
    var c = try a.add(b);
    testing.expectEqual(c.numerator, 6);
    testing.expectEqual(c.denominator, 5);

    a = try R32.new(2, 5);
    b = try R32.new(4, 7);
    c = try a.add(b);
    testing.expectEqual(c.numerator, 2 * 7 + 4 * 5);
    testing.expectEqual(c.denominator, 5 * 7);
}

test "Rational.negate" {
    var a = try R32.new(2, 5);
    var b = try a.negate();
    testing.expect(b.numerator == -2);
    testing.expect(b.denominator == 5);

    // Clear cut overflow.
    var u = try R8.new(-128, 2);
    testing.expectError(RationalError.SignedOverflow, u.negate());
}

test "Rational.sub" {
    // Same denominators.
    var a = try R32.new(2, 5);
    var b = try R32.new(3, 5);
    var c = try a.sub(b);
    testing.expectEqual(c.numerator, -1);
    testing.expectEqual(c.denominator, 5);

    // Different denominators
    a = try R32.new(2, 3);
    b = try R32.new(3, 5);
    c = try a.sub(b);
    testing.expectEqual(c.numerator, 1);
    testing.expectEqual(c.denominator, 15);

    // Teethering edge of overflow.
    var u = try R8.new(-128, 1);
    var v = try R8.new(-1, 1);
    var w = try u.sub(v);
    testing.expectEqual(w.numerator, -127);
    testing.expectEqual(w.denominator, 1);
    // Definitive overflow.
    testing.expectError(RationalError.SignedOverflow, v.sub(u));
}

test "Rational.approximate" {
    // Trivial cases.
    var a = try R8.new(2, 3);
    var c = try a.approximate(.{ .largest_denominator = 3 });
    testing.expectEqual(std.math.Order.eq, R8.order(a, c));

    a = try R8.new(5, 1);
    c = try a.approximate(.{});
    testing.expectEqual(c.numerator, 5);
    testing.expectEqual(c.denominator, 1);

    // Easier cases.
    // In a Stern-Brocot tree, we can see that 3/5, falls between 1/2 and 2/3, but we limit the denominator to 3,
    // so the algorithm should terminate at 1/2 as this is closer to our lower bound.
    a = try R8.new(3, 5);
    c = try a.approximate(.{ .largest_denominator = 3 });
    testing.expectEqual(c.numerator, 1);
    testing.expectEqual(c.denominator, 2);
    // And now when we allow it to, find an exact match.
    c = try a.approximate(.{ .largest_denominator = 5 });
    testing.expectEqual(c.numerator, 3);
    testing.expectEqual(c.denominator, 5);

    // 5/8 is between 3/5 and 2/3.
    a = try R8.new(5, 8);
    c = try a.approximate(.{ .largest_denominator = 5 });
    testing.expectEqual(c.numerator, 3);
    testing.expectEqual(c.denominator, 5);
    // negative case
    a = try R8.new(-5, 8);
    c = try a.approximate(.{ .largest_denominator = 5 });
    testing.expectEqual(c.numerator, -3);
    testing.expectEqual(c.denominator, 5);

    // Weird edge cases.
    // Here we force the denominator to be at most 1. So can only get integer solutions.
    a = try R8.new(3, 5);
    c = try a.approximate(.{ .largest_denominator = 1 });
    testing.expectEqual(c.numerator, 0);
    testing.expectEqual(c.denominator, 1);
}
