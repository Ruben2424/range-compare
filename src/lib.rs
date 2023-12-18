//! # Range Compare
//!
//! This crate provides a method to compare two ranges and get the overlapping parts of the ranges.
//!
//! ## Compare two ranges
//!
//! ```rust
//! use range_compare::{RangeExt, RangeCmpResult};
//!
//! // create two ranges
//! let range1 = 2..10;
//! let range2 = 5..15;
//!
//! // compare the original range1 with the other range2
//! // safe the [RangeCmpResult] of the comparison in a variable
//! let result = range1.compare(&range2);
//!
//! assert_eq!(
//!     result,
//!     RangeCmpResult::EndIncluded {
//!       other_after: 10..15,
//!       original_part_which_is_not_included: 2..5,
//!       overlapping_part: 5..10,
//!   }
//! );
//! ```
//!
//! ## Get the matching part of the original range
//!
//! ```rust
//! use range_compare::{RangeExt, RangeCmpResult};
//!
//! // create two ranges
//! let range1 = 29..40;
//! let range2 = 35..70;
//!
//! // compare the original range1 with the other range2
//! // safe the [RangeCmpResult] of the comparison in a variable
//! let result = range1.compare(&range2);
//!
//! // get the matching part of the original range
//! let matching_part = result.get_matching_part();
//!
//! assert_eq!(matching_part, Some(35..40).as_ref());
//!
//! ```
//!
//! Check the [RangeCmpResult] documentation for more information about the possible results of the comparison.

use std::cmp::Ordering::*;
use std::ops::Range;

/// Extension trait for ranges
///
/// This trait provides a method to compare two ranges and get the result of the comparison.
pub trait RangeExt<T> {
    /// Compare two ranges and get the [RangeCmpResult] of the comparison
    fn compare(&self, other: &Range<T>) -> RangeCmpResult<T>;
}

/// Implementation of the [RangeExt] trait for all types which implement Ord, Eq and Copy
impl<T> RangeExt<T> for Range<T>
where
    T: Ord + Eq + Copy,
{
    /// Compare two ranges and get the [RangeCmpResult] of the comparison
    fn compare(&self, other: &Range<T>) -> RangeCmpResult<T> {
        if self.is_empty() || other.is_empty() {
            // when empty always not included
            return RangeCmpResult::RangeEmpty;
        }

        match (
            self.start.cmp(&other.start),
            self.end.cmp(&other.end),
            self.start.cmp(&other.end),
            self.end.cmp(&other.start),
        ) {
            (Equal, Equal, _, _) => RangeCmpResult::CompletelyTheSame,
            // Greater or Equal because the range is exclusive above
            (_, _, Greater | Equal, _) => RangeCmpResult::NotIncludedAbove,
            (_, _, _, Less | Equal) => RangeCmpResult::NotIncludedBelow,
            (Less, Less, _, _) => RangeCmpResult::EndIncluded {
                other_after: self.end..other.end,
                original_part_which_is_not_included: self.start..other.start,
                overlapping_part: other.start..self.end,
            },
            (Greater, Greater, _, _) => RangeCmpResult::StartIncluded {
                other_before: other.start..self.start,
                original_part_which_is_not_included: other.end..self.end,
                overlapping_part: self.start..other.end,
            },
            (Less, Greater, _, _) => RangeCmpResult::MiddleIncluded {
                overlapping_part: other.start..other.end,
                original_before_not_included: self.start..other.start,
                original_after_not_included: other.end..self.end,
            },
            (Greater, Less, _, _) => RangeCmpResult::CompletelyIncluded {
                other_before: other.start..self.start,
                other_after: self.end..other.end,
                overlapping_part: self.start..self.end,
            },
            (Equal, Less, _, _) => RangeCmpResult::SameStartOriginalShorter {
                overlapping_part: self.start..self.end,
                other_after_not_included: self.end..other.end,
            },
            (Equal, Greater, _, _) => RangeCmpResult::SameStartOtherShorter {
                overlapping_part: other.start..other.end,
                original_after_not_included: other.end..self.end,
            },
            (Less, Equal, _, _) => RangeCmpResult::SameEndOtherShorter {
                overlapping_part: other.start..other.end,
                original_before_not_included: self.start..other.start,
            },
            (Greater, Equal, _, _) => RangeCmpResult::SameEndOriginalShorter {
                overlapping_part: self.start..self.end,
                other_before_not_included: other.start..self.start,
            },
        }
    }
}

/// Result of the comparison of two ranges
///
/// This enum contains all possible results of the comparison of two ranges.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RangeCmpResult<T> {
    /// The ranges have the same `start` and `end` values
    ///
    /// ```rust
    /// use range_compare::{RangeExt, RangeCmpResult};
    /// use std::ops::Range;
    ///
    /// let range1 = 2..10;
    /// let range2 = 2..10;
    ///
    /// let result = range1.compare(&range2);
    ///
    /// assert_eq!(result, RangeCmpResult::CompletelyTheSame);
    /// ```
    CompletelyTheSame,

    /// The ranges are not overlapping and the range is below the other one
    ///
    /// ```rust
    /// use range_compare::{RangeExt, RangeCmpResult};
    /// use std::ops::Range;
    ///
    /// let range1 = 2..10;
    /// let range2 = 11..15;
    ///
    /// let result = range1.compare(&range2);
    ///
    /// assert_eq!(result, RangeCmpResult::NotIncludedBelow);
    /// ```
    NotIncludedBelow,

    /// The ranges are not overlapping and the range is above the other one
    ///
    /// ```rust
    /// use range_compare::{RangeExt, RangeCmpResult};
    /// use std::ops::Range;
    ///
    /// let range1 = 11..15;
    /// let range2 = 2..10;
    ///
    /// let result = range1.compare(&range2);
    ///
    /// assert_eq!(result, RangeCmpResult::NotIncludedAbove);
    /// ```
    NotIncludedAbove,

    /// One range is empty
    ///
    /// ```rust
    /// use range_compare::{RangeExt, RangeCmpResult};
    /// use std::ops::Range;
    ///
    /// let range1 = 2..2;
    /// let range2 = 5..15;
    ///
    /// let result = range1.compare(&range2);
    ///
    /// assert_eq!(result, RangeCmpResult::RangeEmpty);
    /// ```
    RangeEmpty,

    /// The range is completely included in the other one
    ///
    /// ```rust
    /// use range_compare::{RangeExt, RangeCmpResult};
    /// use std::ops::Range;
    ///
    /// let range1 = 5..7;
    /// let range2 = 1..11;
    ///
    /// let result = range1.compare(&range2);
    ///
    /// assert_eq!(
    ///    result,
    ///    RangeCmpResult::CompletelyIncluded {
    ///       other_before: 1..5,
    ///       other_after: 7..11,
    ///       overlapping_part: 5..7,
    ///   }
    /// );
    /// ```
    CompletelyIncluded {
        other_before: Range<T>,
        other_after: Range<T>,
        overlapping_part: Range<T>,
    },

    /// The end of the range is included in the other one
    ///
    /// ```rust
    /// use range_compare::{RangeExt, RangeCmpResult};
    /// use std::ops::Range;
    ///
    /// let range1 = 1..9;
    /// let range2 = 7..10;
    ///
    /// let result = range1.compare(&range2);
    ///
    /// assert_eq!(
    ///   result,
    ///   RangeCmpResult::EndIncluded {
    ///     other_after: 9..10,
    ///     original_part_which_is_not_included: 1..7,
    ///     overlapping_part: 7..9,
    /// }
    /// );
    /// ```
    EndIncluded {
        // The "rest" from the other range which is not included on the original one
        other_after: Range<T>,
        original_part_which_is_not_included: Range<T>,
        overlapping_part: Range<T>,
    },

    /// The start of the range is included in the other one
    ///
    /// ```rust
    /// use range_compare::{RangeExt, RangeCmpResult};
    /// use std::ops::Range;
    ///
    /// let range1 = 4..15;
    /// let range2 = 1..9;
    ///
    /// let result = range1.compare(&range2);
    ///
    /// assert_eq!(
    ///    result,
    ///    RangeCmpResult::StartIncluded {
    ///       other_before: 1..4,
    ///       original_part_which_is_not_included: 9..15,
    ///       overlapping_part: 4..9,
    ///    }
    /// );
    StartIncluded {
        other_before: Range<T>,
        original_part_which_is_not_included: Range<T>,
        overlapping_part: Range<T>,
    },

    /// The middle of the range is included in the other one
    ///
    /// ```rust
    /// use range_compare::{RangeExt, RangeCmpResult};
    /// use std::ops::Range;
    ///
    /// let range1 = 1..20;
    /// let range2 = 4..15;
    ///
    /// let result = range1.compare(&range2);
    ///
    /// assert_eq!(
    ///    result,
    ///    RangeCmpResult::MiddleIncluded {
    ///       overlapping_part: 4..15,
    ///       original_before_not_included: 1..4,
    ///       original_after_not_included: 15..20,
    ///    }
    /// );
    /// ```
    MiddleIncluded {
        overlapping_part: Range<T>,
        original_before_not_included: Range<T>,
        original_after_not_included: Range<T>,
    },

    /// The start of the range is the same as the start of the other range and the range is shorter
    ///
    /// ```rust
    /// use range_compare::{RangeExt, RangeCmpResult};
    /// use std::ops::Range;
    ///
    /// let range1 = 1..10;
    /// let range2 = 1..15;
    ///
    /// let result = range1.compare(&range2);
    ///
    /// assert_eq!(
    ///   result,
    ///   RangeCmpResult::SameStartOriginalShorter {
    ///     overlapping_part: 1..10,
    ///     other_after_not_included: 10..15,
    ///   }
    /// );
    SameStartOriginalShorter {
        overlapping_part: Range<T>,
        other_after_not_included: Range<T>,
    },

    /// The start of the range is the same as the start of the other range and the other range is shorter
    ///
    /// ```rust
    /// use range_compare::{RangeExt, RangeCmpResult};
    /// use std::ops::Range;
    ///
    /// let range1 = 1..15;
    /// let range2 = 1..10;
    ///
    /// let result = range1.compare(&range2);
    ///
    /// assert_eq!(
    ///    result,
    ///    RangeCmpResult::SameStartOtherShorter {
    ///       overlapping_part: 1..10,
    ///       original_after_not_included: 10..15,
    ///    }
    /// );
    /// ```
    SameStartOtherShorter {
        overlapping_part: Range<T>,
        original_after_not_included: Range<T>,
    },

    /// The end of the range is the same as the end of the other range and the range is shorter
    ///
    /// ```rust
    /// use range_compare::{RangeExt, RangeCmpResult};
    /// use std::ops::Range;
    ///
    /// let range1 = 5..15;
    /// let range2 = 1..15;
    ///
    /// let result = range1.compare(&range2);
    ///
    /// assert_eq!(
    ///    result,
    ///    RangeCmpResult::SameEndOriginalShorter {
    ///       overlapping_part: 5..15,
    ///       other_before_not_included: 1..5,
    ///    }
    /// );
    SameEndOriginalShorter {
        overlapping_part: Range<T>,
        other_before_not_included: Range<T>,
    },

    /// The end of the range is the same as the end of the other range and the other range is shorter
    ///
    /// ```rust
    /// use range_compare::{RangeExt, RangeCmpResult};
    /// use std::ops::Range;
    ///
    /// let range1 = 1..15;
    /// let range2 = 5..15;
    ///
    /// let result = range1.compare(&range2);
    ///
    /// assert_eq!(
    ///    result,
    ///    RangeCmpResult::SameEndOtherShorter {
    ///       overlapping_part: 5..15,
    ///       original_before_not_included: 1..5,
    ///    }
    /// );
    SameEndOtherShorter {
        overlapping_part: Range<T>,
        original_before_not_included: Range<T>,
    },
}

impl<T> RangeCmpResult<T> {
    /// Get the matching part of the original range
    ///
    /// This method returns the part of the original range which is matching the other range.
    pub fn get_matching_part(&self) -> Option<&Range<T>> {
        match self {
            RangeCmpResult::RangeEmpty => None,
            RangeCmpResult::CompletelyTheSame => None,
            RangeCmpResult::NotIncludedBelow => None,
            RangeCmpResult::NotIncludedAbove => None,
            RangeCmpResult::CompletelyIncluded {
                other_before: _,
                other_after: _,
                overlapping_part: original_included_part,
            } => Some(original_included_part),
            RangeCmpResult::EndIncluded {
                // The "rest" from the other range which is not included on the original one
                other_after: _,
                original_part_which_is_not_included: _,
                overlapping_part: original_included_part,
            } => Some(original_included_part),
            RangeCmpResult::StartIncluded {
                other_before: _,
                original_part_which_is_not_included: _,
                overlapping_part: original_included_part,
            } => Some(original_included_part),
            RangeCmpResult::MiddleIncluded {
                overlapping_part: original_included_part,
                original_before_not_included: _,
                original_after_not_included: _,
            } => Some(original_included_part),
            RangeCmpResult::SameStartOriginalShorter {
                overlapping_part: original_included_part,
                other_after_not_included: _,
            } => Some(original_included_part),
            RangeCmpResult::SameStartOtherShorter {
                overlapping_part: original_included_part,
                original_after_not_included: _,
            } => Some(original_included_part),
            RangeCmpResult::SameEndOriginalShorter {
                overlapping_part: original_included_part,
                other_before_not_included: _,
            } => Some(original_included_part),
            RangeCmpResult::SameEndOtherShorter {
                overlapping_part: original_included_part,
                original_before_not_included: _,
            } => Some(original_included_part),
        }
    }

    /// Get the parts of the original range which are not matching the other range
    pub fn get_original_not_matching_parts(&self) -> [Option<&Range<T>>; 2] {
        match self {
            RangeCmpResult::CompletelyTheSame => [None, None],
            RangeCmpResult::NotIncludedBelow => [None, None],
            RangeCmpResult::RangeEmpty => [None, None],
            RangeCmpResult::NotIncludedAbove => [None, None],
            // range is completely included, so there is no part which is not included
            RangeCmpResult::CompletelyIncluded {
                other_before: _,
                other_after: _,
                overlapping_part: _,
            } => [None, None],
            RangeCmpResult::EndIncluded {
                // The "rest" from the other range which is not included on the original one
                other_after: _,
                original_part_which_is_not_included,
                overlapping_part: _,
            } => [Some(original_part_which_is_not_included), None],
            RangeCmpResult::StartIncluded {
                other_before: _,
                original_part_which_is_not_included,
                overlapping_part: _,
            } => [Some(original_part_which_is_not_included), None],
            RangeCmpResult::MiddleIncluded {
                overlapping_part: _,
                original_before_not_included,
                original_after_not_included,
            } => [
                Some(original_before_not_included),
                Some(original_after_not_included),
            ],
            RangeCmpResult::SameStartOriginalShorter {
                overlapping_part: _,
                other_after_not_included: _,
            } => [None, None],
            RangeCmpResult::SameStartOtherShorter {
                overlapping_part: _,
                original_after_not_included,
            } => [Some(original_after_not_included), None],
            RangeCmpResult::SameEndOriginalShorter {
                overlapping_part: _,
                other_before_not_included: _,
            } => [None, None],
            RangeCmpResult::SameEndOtherShorter {
                overlapping_part: _,
                original_before_not_included,
            } => [Some(original_before_not_included), None],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Test that all types work
    #[test]
    fn test_i32() {
        let range1 = 2i32..10;
        let range2 = 5i32..15;
        let result = range1.compare(&range2);
        assert_eq!(
            result,
            RangeCmpResult::EndIncluded {
                other_after: 10..15,
                original_part_which_is_not_included: 2..5,
                overlapping_part: 5..10,
            }
        );
    }

    #[test]
    fn test_u8() {
        let range1 = 2u8..10;
        let range2 = 5u8..15;
        let result = range1.compare(&range2);
        assert_eq!(
            result,
            RangeCmpResult::EndIncluded {
                other_after: 10..15,
                original_part_which_is_not_included: 2..5,
                overlapping_part: 5..10,
            }
        );
    }

    #[test]
    fn test_i8() {
        let range1 = 2i8..10;
        let range2 = 5i8..15;
        let result = range1.compare(&range2);
        assert_eq!(
            result,
            RangeCmpResult::EndIncluded {
                other_after: 10..15,
                original_part_which_is_not_included: 2..5,
                overlapping_part: 5..10,
            }
        );
    }

    #[test]
    fn test_u16() {
        let range1 = 2u16..10;
        let range2 = 5u16..15;
        let result = range1.compare(&range2);
        assert_eq!(
            result,
            RangeCmpResult::EndIncluded {
                other_after: 10..15,
                original_part_which_is_not_included: 2..5,
                overlapping_part: 5..10,
            }
        );
    }

    #[test]
    fn test_i16() {
        let range1 = 2i16..10;
        let range2 = 5i16..15;
        let result = range1.compare(&range2);
        assert_eq!(
            result,
            RangeCmpResult::EndIncluded {
                other_after: 10..15,
                original_part_which_is_not_included: 2..5,
                overlapping_part: 5..10,
            }
        );
    }

    #[test]
    fn test_u32() {
        let range1 = 2u32..10;
        let range2 = 5u32..15;
        let result = range1.compare(&range2);
        assert_eq!(
            result,
            RangeCmpResult::EndIncluded {
                other_after: 10..15,
                original_part_which_is_not_included: 2..5,
                overlapping_part: 5..10,
            }
        );
    }

    #[test]
    fn test_u64() {
        let range1 = 2u64..10;
        let range2 = 5u64..15;
        let result = range1.compare(&range2);
        assert_eq!(
            result,
            RangeCmpResult::EndIncluded {
                other_after: 10..15,
                original_part_which_is_not_included: 2..5,
                overlapping_part: 5..10,
            }
        );
    }

    #[test]
    fn test_i64() {
        let range1 = 2i64..10;
        let range2 = 5i64..15;
        let result = range1.compare(&range2);
        assert_eq!(
            result,
            RangeCmpResult::EndIncluded {
                other_after: 10..15,
                original_part_which_is_not_included: 2..5,
                overlapping_part: 5..10,
            }
        );
    }

    #[test]
    fn test_u128() {
        let range1 = 2u128..10;
        let range2 = 5u128..15;
        let result = range1.compare(&range2);
        assert_eq!(
            result,
            RangeCmpResult::EndIncluded {
                other_after: 10..15,
                original_part_which_is_not_included: 2..5,
                overlapping_part: 5..10,
            }
        );
    }

    #[test]
    fn test_i126() {
        let range1 = 2i128..10;
        let range2 = 5i128..15;
        let result = range1.compare(&range2);
        assert_eq!(
            result,
            RangeCmpResult::EndIncluded {
                other_after: 10..15,
                original_part_which_is_not_included: 2..5,
                overlapping_part: 5..10,
            }
        );
    }

    // Test all possible results with just one Type

    #[test]
    fn test_range_empty() {
        let range1 = 2..2;
        let range2 = 5..15;
        let result = range1.compare(&range2);
        assert_eq!(result, RangeCmpResult::RangeEmpty);
    }

    #[test]
    fn test_range_empty2() {
        let range1 = 5..2;
        let range2 = 5..15;
        let result = range1.compare(&range2);
        assert_eq!(result, RangeCmpResult::RangeEmpty);
    }

    #[test]
    fn test_range_empty3() {
        let range1 = 5..20;
        let range2 = 25..15;
        let result = range1.compare(&range2);
        assert_eq!(result, RangeCmpResult::RangeEmpty);
    }

    #[test]
    fn test_completely_the_same() {
        let range1 = 2..10;
        let range2 = 2..10;
        let result = range1.compare(&range2);
        assert_eq!(result, RangeCmpResult::CompletelyTheSame);
    }

    #[test]
    fn test_not_included() {
        let range1 = 2..10;
        let range2 = 11..15;
        let result = range1.compare(&range2);
        assert_eq!(result, RangeCmpResult::NotIncludedBelow);
    }

    #[test]
    fn test_not_included_above() {
        let range1 = 11..15;
        let range2 = 2..10;
        let result = range1.compare(&range2);
        assert_eq!(result, RangeCmpResult::NotIncludedAbove);
    }

    #[test]
    fn test_completely_included() {
        let range1 = 2..10;
        let range2 = 1..11;
        let result = range1.compare(&range2);
        assert_eq!(
            result,
            RangeCmpResult::CompletelyIncluded {
                other_before: 1..2,
                other_after: 10..11,
                overlapping_part: 2..10,
            }
        );
    }

    #[test]
    fn test_end_included() {
        let range1 = 1..9;
        let range2 = 2..10;
        let result = range1.compare(&range2);
        assert_eq!(
            result,
            RangeCmpResult::EndIncluded {
                other_after: 9..10,
                original_part_which_is_not_included: 1..2,
                overlapping_part: 2..9,
            }
        );
    }

    #[test]
    fn test_start_included() {
        let range1 = 2..15;
        let range2 = 1..9;
        let result = range1.compare(&range2);
        assert_eq!(
            result,
            RangeCmpResult::StartIncluded {
                other_before: 1..2,
                original_part_which_is_not_included: 9..15,
                overlapping_part: 2..9,
            }
        );
    }

    #[test]
    fn test_middle_included() {
        let range1 = 1..20;
        let range2 = 4..15;
        let result = range1.compare(&range2);
        assert_eq!(
            result,
            RangeCmpResult::MiddleIncluded {
                overlapping_part: 4..15,
                original_before_not_included: 1..4,
                original_after_not_included: 15..20,
            }
        );
    }

    #[test]
    fn test_same_start_original_shorter() {
        let range1 = 1..10;
        let range2 = 1..15;
        let result = range1.compare(&range2);
        assert_eq!(
            result,
            RangeCmpResult::SameStartOriginalShorter {
                overlapping_part: 1..10,
                other_after_not_included: 10..15,
            }
        );
    }

    #[test]
    fn test_same_start_other_shorter() {
        let range1 = 1..15;
        let range2 = 1..10;
        let result = range1.compare(&range2);
        assert_eq!(
            result,
            RangeCmpResult::SameStartOtherShorter {
                overlapping_part: 1..10,
                original_after_not_included: 10..15,
            }
        );
    }

    #[test]
    fn test_same_end_original_shorter() {
        let range1 = 5..15;
        let range2 = 1..15;
        let result = range1.compare(&range2);
        assert_eq!(
            result,
            RangeCmpResult::SameEndOriginalShorter {
                overlapping_part: 5..15,
                other_before_not_included: 1..5,
            }
        );
    }

    #[test]
    fn test_same_end_other_shorter() {
        let range1 = 1..15;
        let range2 = 5..15;
        let result = range1.compare(&range2);
        assert_eq!(
            result,
            RangeCmpResult::SameEndOtherShorter {
                overlapping_part: 5..15,
                original_before_not_included: 1..5,
            }
        );
    }

    #[test]
    fn test_get_matching_part() {
        let range1 = 29..40;
        let range2 = 35..70;
        let result = range1.compare(&range2);
        let matching_part = result.get_matching_part();
        assert_eq!(matching_part, Some(35..40).as_ref());
    }
}
