# range-compare
This crate provides a method to compare two ranges and get the overlapping parts of the ranges.

# Status
This crate is not yet published on [crates.io](https://crates.io/)

# Examples
 ```rust
use range_compare::{RangeExt, RangeCmpResult};

// create two ranges
let range1 = 2..10;
let range2 = 5..15;

// compare the original range1 with the other range2
// safe the [RangeCmpResult] of the comparison in a variable
let result = range1.compare(&range2);

assert_eq!(
    result,
    RangeCmpResult::EndIncluded {
        other_after: 10..15,
        original_part_which_is_not_included: 2..5,
        overlapping_part: 5..10,
}
);
```

## Get the matching part of the original range

```rust
use range_compare::{RangeExt, RangeCmpResult};

// create two ranges
let range1 = 29..40;
let range2 = 35..70;

// compare the original range1 with the other range2
// safe the [RangeCmpResult] of the comparison in a variable
let result = range1.compare(&range2);

// get the matching part of the original range
let matching_part = result.get_matching_part();

assert_eq!(matching_part, Some(35..40).as_ref());

```
