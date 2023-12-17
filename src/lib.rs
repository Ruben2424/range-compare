use std::cmp::Ordering::*;
use std::ops::Range;

pub trait RangeExt<T> {
    fn compare(&self, other: &Range<T>) -> RangeCmpResult<T>;
}

impl<T> RangeExt<T> for Range<T>
where
    T: Ord + Eq + Copy,
{
    fn compare(&self, other: &Range<T>) -> RangeCmpResult<T> {
        if self.is_empty() || other.is_empty() {
            // when empty always not included
            return RangeCmpResult::NotIncluded;
        }

        match (
            self.start.cmp(&other.start),
            self.end.cmp(&other.end),
            self.start.cmp(&other.end),
            self.end.cmp(&other.start),
        ) {
            (Equal, Equal, _, _) => RangeCmpResult::CompletelyTheSame,
            // Greater or Equal because the range is exclusive above
            (_, _, Greater | Equal, _) => RangeCmpResult::NotIncluded,
            (_, _, _, Less | Equal) => RangeCmpResult::NotIncluded,
            (Less, Less, _, _) => RangeCmpResult::EndIndluded {
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
                overlapping: other.start..other.end,
                original_before_not_included: self.start..other.start,
                original_after_not_included: other.end..self.end,
            },
            (Greater, Less, _, _) => RangeCmpResult::CompletelyIncluded {
                other_before: other.start..self.start,
                other_after: self.end..other.end,
                overlapping_part: self.start..self.end,
            },
            (Equal, Less, _, _) => RangeCmpResult::SameStartOriginalShorter {
                original_included_part: self.start..self.end,
                other_after_not_included: self.end..other.end,
            },
            (Equal, Greater, _, _) => RangeCmpResult::SameStartOtherShorter {
                original_included_part: other.start..other.end,
                original_after_not_included: other.end..self.end,
            },
            (Less, Equal, _, _) => RangeCmpResult::SameEndOtherShorter {
                original_included_part: other.start..other.end,
                original_before_not_included: self.start..other.start,
            },
            (Greater, Equal, _, _) => RangeCmpResult::SameEndOriginalShorter {
                original_included_part: self.start..self.end,
                other_before_not_included: other.start..self.start,
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RangeCmpResult<T> {
    CompletelyTheSame,
    NotIncluded,
    CompletelyIncluded {
        other_before: Range<T>,
        other_after: Range<T>,
        overlapping_part: Range<T>,
    },
    EndIndluded {
        // The "rest" from the other range which is not included on the original one
        other_after: Range<T>,
        original_part_which_is_not_included: Range<T>,
        overlapping_part: Range<T>,
    },
    StartIncluded {
        other_before: Range<T>,
        original_part_which_is_not_included: Range<T>,
        overlapping_part: Range<T>,
    },
    MiddleIncluded {
        overlapping: Range<T>,
        original_before_not_included: Range<T>,
        original_after_not_included: Range<T>,
    },
    SameStartOriginalShorter {
        original_included_part: Range<T>,
        other_after_not_included: Range<T>,
    },
    SameStartOtherShorter {
        original_included_part: Range<T>,
        original_after_not_included: Range<T>,
    },
    SameEndOriginalShorter {
        original_included_part: Range<T>,
        other_before_not_included: Range<T>,
    },
    SameEndOtherShorter {
        original_included_part: Range<T>,
        original_before_not_included: Range<T>,
    },
}

impl<T> RangeCmpResult<T> {
    pub fn get_matching_part(&self) -> Option<&Range<T>> {
        match self {
            RangeCmpResult::CompletelyTheSame => None,
            RangeCmpResult::NotIncluded => None,
            RangeCmpResult::CompletelyIncluded {
                other_before: _,
                other_after: _,
                overlapping_part: original_included_part,
            } => Some(original_included_part),
            RangeCmpResult::EndIndluded {
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
                overlapping: original_included_part,
                original_before_not_included: _,
                original_after_not_included: _,
            } => Some(original_included_part),
            RangeCmpResult::SameStartOriginalShorter {
                original_included_part,
                other_after_not_included: _,
            } => Some(original_included_part),
            RangeCmpResult::SameStartOtherShorter {
                original_included_part,
                original_after_not_included: _,
            } => Some(original_included_part),
            RangeCmpResult::SameEndOriginalShorter {
                original_included_part,
                other_before_not_included: _,
            } => Some(original_included_part),
            RangeCmpResult::SameEndOtherShorter {
                original_included_part,
                original_before_not_included: _,
            } => Some(original_included_part),
        }
    }

    pub fn get_original_not_matching_parts(&self) -> [Option<&Range<T>>; 2] {
        match self {
            RangeCmpResult::CompletelyTheSame => [None, None],
            RangeCmpResult::NotIncluded => [None, None],
            // range is completely included, so there is no part which is not included
            RangeCmpResult::CompletelyIncluded {
                other_before: _,
                other_after: _,
                overlapping_part: _,
            } => [None, None],
            RangeCmpResult::EndIndluded {
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
                overlapping: _,
                original_before_not_included,
                original_after_not_included,
            } => [
                Some(original_before_not_included),
                Some(original_after_not_included),
            ],
            RangeCmpResult::SameStartOriginalShorter {
                original_included_part: _,
                other_after_not_included: _,
            } => [None, None],
            RangeCmpResult::SameStartOtherShorter {
                original_included_part: _,
                original_after_not_included,
            } => [Some(original_after_not_included), None],
            RangeCmpResult::SameEndOriginalShorter {
                original_included_part: _,
                other_before_not_included: _,
            } => [None, None],
            RangeCmpResult::SameEndOtherShorter {
                original_included_part: _,
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
            RangeCmpResult::EndIndluded {
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
            RangeCmpResult::EndIndluded {
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
            RangeCmpResult::EndIndluded {
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
            RangeCmpResult::EndIndluded {
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
            RangeCmpResult::EndIndluded {
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
            RangeCmpResult::EndIndluded {
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
            RangeCmpResult::EndIndluded {
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
            RangeCmpResult::EndIndluded {
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
            RangeCmpResult::EndIndluded {
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
            RangeCmpResult::EndIndluded {
                other_after: 10..15,
                original_part_which_is_not_included: 2..5,
                overlapping_part: 5..10,
            }
        );
    }

    // Test all possible results with just one Type

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
        assert_eq!(result, RangeCmpResult::NotIncluded);
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
            RangeCmpResult::EndIndluded {
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
                overlapping: 4..15,
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
                original_included_part: 1..10,
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
                original_included_part: 1..10,
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
                original_included_part: 5..15,
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
                original_included_part: 5..15,
                original_before_not_included: 1..5,
            }
        );
    }
}
