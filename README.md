# idris2-Multiset

**A pure, deterministic Run-Length Encoded (RLE) multiset and polynomial algebra library for [Idris 2](https://github.com/idris-lang/Idris2).**

[![Idris2](https://img.shields.io/badge/Idris2-Algebra-blue.svg)](https://github.com/idris-lang/Idris2)
[![Performance](https://img.shields.io/badge/Optimization-RLE_O(1)-orange.svg)]()
[![QuickCheck](https://img.shields.io/badge/QuickCheck-Passed-green.svg)]()

---

## Overview

`idris2-Multiset` provides the core mathematical primitives that power the [Nat-Science](https://github.com/justinkelly-ie/Nat-Science) discrete physics ecosystem. 

In finitist geometry, continuous space is discarded in favor of discrete integer pixels, and physical coordinates are represented as **Multisets** (bags of elements where duplicate items are allowed and tracked via signed integer counts). 

This library implements high-performance, Run-Length Encoded (RLE) multiset operations, enabling complex algebraic addition, subtraction, scalar multiplication, and polynomial convolving to run in optimal time.

---

## Key Modules

| Module | Role |
|---|---|
| **`Math.Multiset`** | The core RLE multiset engine. Implements signed multiplicity, union, intersection, set difference, and list conversions. |
| **`Math.Polynumber`** | Implements standard univariate and multivariate integer polynomial algebra. |
| **`Math.IntPolynumber`** | Specializes polynomial operations for discrete integer spaces. |
| **`Math.SpreadPolynumber`** | Provides primorial spread convolutions used by the physics evolution gates. |
| **`Math.Pixel`** | Defines basic 2D and 3D discrete coordinates. |

---

## Code Example

```idris
import Math.Multiset

-- Define a simple multiset of coordinates
-- e.g., 5 items at coordinate A, and 3 items at coordinate B
let m1 = AddM 'A' 5 (AddM 'B' 3 ZeroM)
let m2 = AddM 'A' (-2) (AddM 'C' 4 ZeroM)

-- Add them together (annihilation occurs automatically for signed counts)
let result = addMultiset m1 m2
-- result is equivalent to: AddM 'A' 3 (AddM 'B' 3 (AddM 'C' 4 ZeroM))
```

---

## Installation & Pack Integration

Resolve locally via `pack.toml`:

```toml
[custom.all.idris2-Multiset]
type = "local"
path = "../idris2-Multiset"
ipkg = "idris2-Multiset.ipkg"
```

Then add to your `.ipkg` file's `depends` list:

```idris
depends = base, contrib, idris2-Multiset
```

---

© Justin Kelly. All rights reserved.
