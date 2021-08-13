Proposal for fixed size a Rational type
----------------------------------------

Rational takes a comptime_int bit_count designating the bit-width of the integer T. Rational is always signed. Rational corresponds to a subset of the field of Rationals (Q).

To avoid the nasty special case of bit_count 0, we'll disallow this.

Like std.big.Rational, it stores a numerator and a denominator as two fields. The sign is stored on the numerator.

# Range represented 
Smallest and largest values are min(T)/1 and max(T)/1. The smallest value larger than 0 is 1/max(T). Due to two's complement representation, it is highly likely that min(T) != -max(T) and abs(min(T)) > abs(max(T)) on most computers in use today.

## Equivalence classes
Formally, the rationals consists of equivalence classes of pairs (a, b). An example is the rational 1/2 which is in the same class as 2/4 and thus represent the same number. Since we have limited precision, not all the members of every equivalence class can be represented.

We can get from (a, b) to another equivalent rational simply by multiplying a non-zero integer factor k to both the numerator and denominator. This shows that we can represent all (max(T) - min(T) - 1) members of (1, 1). But only 2 of (1, max(T)), since multiplying this by anything else than +/- 1 overflows.

# Irreducibility
Like std.big.Rational, I propose it keeps the represented rational in a fully reduced form ("lowest terms"), i.e: gcd(a, b) = 1. 

Many types of calculations are simply easier to perform when this can be assumed, and as such, it is assumed the user would likely want to keep them reduced anyway.

# Signed overflow/underflow
Since we are dealing with signed integers, I propose the add, sub and mul functions return an error union, such that overflow can be detected, as signed overflow is considered UB in Zig.

# Library API

## Errors

### RationalError
```
pub const RationalError = error{ ZeroDenominator, SignedOverflow };
```

### Type SignedInt
Convenience type constructor for a signed integer with a given bit count.
```
fn SignedInt(comptime bit_count: u16) type {
    return std.meta.Int(.signed, bit_count);
}
``` 

### Type Rational
We provide a type constructor 
```
pub fn Rational(comptime bit_count: u16) type { ... }
```

#### Fields
```
/// Sign is stored on the numerator.
numerator: T,
denominator: T,
```

#### Constants
```
pub const T = SignedInt(bit_count);
pub const zero = Self{ .numerator = 0, .denominator = 1 };
pub const one = Self{ .numerator = 1, .denominator = 1 };
pub const half = Self{ .numerator = 1, .denominator = 2 };
```

#### new
Returns a new rational that is irreducible.

Preconditions:
 - d != 0
 - if d == -1 then n >= -std.math.maxInt(T)

```
pub fn new(n: T, d: T) !Self { ... }
```

#### add, sub, mul
Adds, subtracts and multiplies two rationals. Checks for overflow.

#### order
Overflow free comparison of two rationals. To do this, many iterations using integer division may be performed.

```
pub fn order(x: Self, y: Self) std.math.Order { ... }
```

#### abs
Returns the absolute value.

Preconditions:
- `numerator >= -max(T)`

`abs(min(T))` on a Two's complement machine may not fit into T.

#### negate 
Preconditions:
- `numerator >= -max(T)`

`-min(T)` on a Two's complement machine may not fit into T.

#### mediant
Computes the mediant of two Rationals, a/b and c/d as:
```
(a + c)/(b + d)
```
If x < y, the mediant is a rational number between them.
```
pub fn mediant(self: Self, b: Self) !Self { ... }
```
    
#### ApproximationOptions
Used to customize the approximate method described below.
```
pub const ApproximationOptions = struct {
    /// Will not allow a denominator larger than this. Must be non-zero. Sign is ignored.
    /// Setting this to 1 effectively forces a rational that corresponds to an integer.
    /// Defaults to max(T) which implies the result is just the same rational.
    largest_denominator: ?T = std.math.maxInt(T),
};
```
#### approximate
Attempts to find a Rational that approximates this one. Can be used to "clean up" floating point numbers, or find an approximation with a lower bit count.

Preconditions:
 - `options.largest_denominator != 0`

```        
pub fn approximate(self: Self, options: Self.ApproximationOptions) !Self { ... }
```

#### format
std.fmt compatible formatting method. Prints equivalent to `"({}/{})"`.

#### toFloat
Returns a floating point value that is closest to this rational.

The result may not be exact, for example if the Rational cannot possibly be represented by a much smaller floating point type.
```
pub fn toFloat(self: Self, comptime F: type) F { ... }
```

### toFloatStrict
Like `toFloat` but returns an error when the value cannot be represented.

Returns a floating point value that is closest to this rational.

```
pub fn toFloatStrict(self: Self, comptime F: type) !F { ... }
```

## Free Functions

### binaryGCD
Computes the greatest common divisor d using the binary GCD algorithm.

Always returns a positive number (> 0).

On Two's complement machines, this is undefined when a or b is less than -maxInt(T), as it's absolute value is larger than any positive value of T.

Algorithmic complexity is O(n^2) where n is the bitcount of T.
```
fn gcdBinary(comptime T: type, a: T, b: T) T { ... }
```

## Constants
```
pub const R8 = Rational(8);
pub const R16 = Rational(16);
pub const R32 = Rational(32);
pub const R64 = Rational(64);
```