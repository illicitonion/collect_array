# collect_array

Allows for collecting an Iterator into an exactly sized array.

[![crates.io](https://img.shields.io/crates/v/collect_array.svg)](https://crates.io/crates/collect_array)
[![Documentation](https://docs.rs/collect_array/badge.svg)](https://docs.rs/collect_array)
[![Build Status](https://github.com/illicitonion/collect_array/actions/workflows/presubmit.yml/badge.svg)](https://github.com/illicitonion/collect_array/actions)

## Example

```rust
use collect_array::CollectArrayResult;

let result: CollectArrayResult<_, 2> = vec![1, 2].into_iter().collect();
assert_eq!(CollectArrayResult::Ok([1, 2]), result);
```
