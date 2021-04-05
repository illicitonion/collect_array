//! Allows for collecting an Iterator into an exactly sized array.
//!
//! # Example
//!
//! ```
//! use collect_array::CollectArrayResult;
//!
//! let v = vec![0, 1, 2];
//! let result: CollectArrayResult<_, 3> = v.into_iter().collect();
//! assert_eq!(CollectArrayResult::Ok([0, 1, 2]), result);
//! ```

#![cfg_attr(not(test), no_std)]

use core::mem::MaybeUninit;

/// The result of collecting an Iterator into an exactly-sized array, or having failed to.
///
/// More than N elements may be consumed from the Iterator - if this is undesirable, consider
/// calling [`Iterator#take`] before collecting.
pub enum CollectArrayResult<T, const N: usize> {
    /// Returned if the Iterator contained exactly N elements.
    Ok([T; N]),
    /// Returned if the Iterator contained more than N elements.
    /// The underlying Iterator may not be exhausted, and remaining values may not be accessible.
    TooManyElements {
        /// The N values which were read.
        values: [T; N],
        /// The next value after the Nth.
        next_value: T,
    },
    /// Returned if the Iterator contained fewer than N elements.
    ///
    /// # Safety
    ///
    /// Only the first `init_count` elements will be init, the remaining elements must not be read.
    NotEnoughElements {
        /// The consumed values, only `init_count` of which will be init.
        values: [MaybeUninit<T>; N],
        /// How many elements in `values` are init.
        init_count: usize,
    },
}

impl<T, const N: usize> PartialEq<CollectArrayResult<T, N>> for CollectArrayResult<T, N>
where
    T: PartialEq,
{
    fn eq(&self, other: &CollectArrayResult<T, N>) -> bool {
        match (self, other) {
            (Self::Ok(lhs), Self::Ok(rhs)) => lhs == rhs,
            (Self::TooManyElements { .. }, Self::TooManyElements { .. }) => false,
            (
                Self::NotEnoughElements {
                    values: lhs,
                    init_count: lhs_count,
                },
                Self::NotEnoughElements {
                    values: rhs,
                    init_count: rhs_count,
                },
            ) if lhs_count == rhs_count => {
                for i in 0..*lhs_count {
                    if let Some(lhs) = lhs.get(i) {
                        if let Some(rhs) = rhs.get(i) {
                            unsafe {
                                if *lhs.as_ptr() != *rhs.as_ptr() {
                                    return false;
                                }
                            }
                        }
                    }
                }
                true
            }
            _ => false,
        }
    }
}

impl<T, const N: usize> core::fmt::Debug for CollectArrayResult<T, N>
where
    T: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Ok(arr) => arr.fmt(f),
            Self::TooManyElements { values, next_value: next } => write!(
                f,
                "CollectArrayResult::TooManyElements{{ values: {:?}, next: {:?} (possibly others...) }}",
                values, next,
            ),
            Self::NotEnoughElements { values, init_count } => {
                write!(
                    f,
                    "CollectArrayResult::NotEnoughElements{{ got: {:?}, expected: {:?}, values: [",
                    init_count, N
                )?;
                let mut i = 0;
                while i < *init_count {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{:?}", unsafe { &*values.get(i).unwrap().as_ptr() })?;
                    i += 1;
                }
                write!(f, "] }}")?;
                Ok(())
            }
        }
    }
}

impl<T, const N: usize> core::iter::FromIterator<T> for CollectArrayResult<T, N> {
    fn from_iter<It: IntoIterator<Item = T>>(it: It) -> Self {
        // TODO: Use MaybeUninit::uninit_array or [MaybeUninit::<T>::uninit(); N] when either stabilises.
        let mut values: [MaybeUninit<T>; N] =
            unsafe { MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init() };

        let mut added = 0_usize;

        let mut iter = it.into_iter();

        while added < N {
            if let Some(value) = iter.next() {
                values[added] = MaybeUninit::new(value);
                added += 1;
            } else {
                break;
            }
        }

        if added == N {
            // TODO: Use MaybeUninit::array_assume_init when it stabilises (https://github.com/rust-lang/rust/issues/80908).
            let values = unsafe { (&values as *const _ as *const [T; N]).read() };
            if let Some(next_value) = iter.next() {
                CollectArrayResult::TooManyElements { values, next_value }
            } else {
                CollectArrayResult::Ok(values)
            }
        } else {
            CollectArrayResult::NotEnoughElements {
                values,
                init_count: added,
            }
        }
    }
}

#[test]
fn ok() {
    let input = vec![0_i32, 1_i32, 2_i32];

    let output = input.into_iter().collect::<CollectArrayResult<_, 3>>();
    assert_eq!(output, CollectArrayResult::Ok([0, 1, 2]));
}

#[test]
fn want_more() {
    let input = vec![0_i32, 1_i32, 2_i32];

    let output = input.into_iter().collect::<CollectArrayResult<_, 4>>();
    assert_eq!(
        output,
        CollectArrayResult::NotEnoughElements {
            values: [
                MaybeUninit::new(0),
                MaybeUninit::new(1),
                MaybeUninit::new(2),
                MaybeUninit::uninit()
            ],
            init_count: 3
        }
    );
}

#[test]
fn want_fewer() {
    let input = vec![0_i32, 1_i32, 2_i32];

    let output = input.into_iter().collect::<CollectArrayResult<_, 2>>();
    let want_arr = [0_i32, 1_i32];
    let want_next = 2_i32;
    if let CollectArrayResult::TooManyElements {
        values,
        next_value: next,
    } = output
    {
        assert_eq!(values, want_arr);
        assert_eq!(next, want_next);
    } else {
        let want: CollectArrayResult<_, 2> = CollectArrayResult::TooManyElements {
            values: want_arr,
            next_value: want_next,
        };
        panic!(
            "Saw wrong elements; expected {:?} but saw {:?}",
            want, output
        );
    }
}

#[test]
fn debug() {
    assert_eq!(
        "[0, 1, 2]",
        format!("{:?}", CollectArrayResult::Ok([0, 1, 2]))
    );

    let not_enough: CollectArrayResult<_, 4> = vec![0, 1, 2].into_iter().collect();
    assert_eq!(
        "CollectArrayResult::NotEnoughElements{ got: 3, expected: 4, values: [0, 1, 2] }",
        format!("{:?}", not_enough)
    );

    assert_eq!(
        "CollectArrayResult::TooManyElements{ values: [0, 1], next: 2 (possibly others...) }",
        format!(
            "{:?}",
            CollectArrayResult::TooManyElements {
                values: [0, 1],
                next_value: 2
            }
        )
    );
}
