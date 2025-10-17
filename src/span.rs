//! The `Span` type and related items.
extern crate alloc;

use crate::Rational;
use alloc::{sync::Arc, vec::Vec};
use core::fmt;

/// A shorthand macro for constructing spans from rationals, e.g. `span!(0/1, 3/1)`.
#[macro_export]
macro_rules! span {
    ($n1:literal/$d1:literal, $n2:literal/$d2:literal) => {{
        span!($n1 / $d1, $crate::Rational::new_raw($n2, $d2))
    }};
    ($n1:literal/$d1:literal, $r2:expr) => {{
        span!($crate::Rational::new_raw($n1, $d1), $r2)
    }};
    ($r1:expr, $n2:literal/$d2:literal) => {{
        span!($r1, $crate::Rational::new_raw($n2, $d2))
    }};
    ($r1:expr, $r2:expr) => {{
        $crate::Span::new($r1, $r2)
    }};
    ($n:literal / $d:literal) => {{
        span!($crate::Rational::new_raw($n, $d))
    }};
    ($r:expr) => {{
        $crate::Span::instant($r)
    }};
}

/// A rational range over a single dimension, represented with a start and end.
#[derive(Clone, Copy, Eq, Hash, PartialEq, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Span {
    pub start: Rational,
    pub end: Rational,
}

impl Span {
    pub fn new(start: Rational, end: Rational) -> Self {
        Span { start, end }
    }

    pub fn instant(start @ end: Rational) -> Self {
        Span { start, end }
    }

    pub fn len(&self) -> Rational {
        self.end - self.start
    }

    pub fn cycles(self) -> impl Iterator<Item = Self> {
        let Span { mut start, end } = self;
        core::iter::from_fn(move || {
            if start >= end {
                None
            } else if start >= end.floor() {
                let span = Span { start, end };
                start = end;
                Some(span)
            } else {
                let this_end = start.floor() + 1;
                let span = Span {
                    start,
                    end: this_end,
                };
                start = this_end;
                Some(span)
            }
        })
    }

    /// Like [`cycles`][Self::cycles], but instead of iterating by single cycles, we step in increments given by the given `steps`.
    /// Returns the (stepped span (bounded by self), the whole stepped span, and the index of the step)
    pub fn step_cycles(
        self,
        steps: impl Iterator<Item = Rational>,
    ) -> impl Iterator<Item = (Self, Self, usize)> {
        let Span { mut start, end } = self;
        let steps = Arc::new(steps.collect::<Vec<_>>());
        let total_length: Rational = steps.iter().sum();

        // Calculate the current position within the step pattern
        let current_position = crate::rem_euclid(start, total_length);

        // Find which step we're currently in
        let mut current_step = Rational::from(0);
        let mut step_index = 0;
        for (i, &step) in steps.iter().enumerate() {
            if current_position < current_step + step {
                step_index = i;
                break;
            }
            current_step += step;
        }

        // Calculate the start of the current cycle in terms of the whole step
        let mut cycle_start = if start >= Rational::from(0) {
            (start / total_length).floor() * total_length
        } else {
            // For negative numbers, we add the current step to the cycle start
            ((start / total_length).floor() * total_length) + current_step
        };
        // Calculate the end of the current cycle in terms of the whole step
        let mut cycle_end = if start >= Rational::from(0) {
            // For positive numbers, we add the current step to the cycle end
            cycle_start + current_step + steps[step_index]
        } else {
            cycle_start + steps[step_index]
        };

        core::iter::from_fn(move || {
            if start >= end {
                None
            } else if total_length == Rational::from(0) {
                None
            } else {
                if cycle_end >= end {
                    let result = (
                        Span { start, end },
                        Span {
                            start: cycle_start,
                            end: cycle_end,
                        },
                        step_index,
                    );
                    start = end;
                    Some(result)
                } else {
                    let result = (
                        Span {
                            start,
                            end: cycle_end,
                        },
                        Span {
                            start: cycle_start,
                            end: cycle_end,
                        },
                        step_index,
                    );
                    start = cycle_end;
                    cycle_start = cycle_end;

                    // Move to next step in the pattern
                    step_index = (step_index + 1) % steps.len();
                    cycle_end = start + steps[step_index];

                    Some(result)
                }
            }
        })
    }

    pub fn map(self, f: impl Fn(Rational) -> Rational) -> Self {
        span!(f(self.start), f(self.end))
    }

    pub fn map_len(self, f: impl Fn(Rational) -> Rational) -> Self {
        let new_len = f(self.len());
        let new_end = self.start + new_len;
        span!(self.start, new_end)
    }

    /// Checks if point lies within the span exclusively.
    pub fn contains(&self, point: Rational) -> bool {
        self.start <= point && point < self.end
    }

    /// The intersecting span between `self` and `other`.
    ///
    /// NOTE: If either span's `start` is equal to its `end`, `None` is returned.
    pub fn intersect(self, other: Self) -> Option<Self> {
        let start = core::cmp::max(self.start, other.start);
        let end = core::cmp::min(self.end, other.end);
        if end <= start {
            None
        } else {
            Some(Span { start, end })
        }
    }

    /// The portions of `other` that do *not* intersect `self`.
    ///
    /// Returns preceding and succeeding diffs respectively.
    ///
    /// Returns `(None, None)` in the case that `other` is a subsection of `self`.
    pub fn difference(self, other: Self) -> (Option<Self>, Option<Self>) {
        let pre = if self.start <= other.start {
            None
        } else {
            Some(Span::new(
                other.start,
                core::cmp::min(self.start, other.end),
            ))
        };
        let post = if other.end <= self.end {
            None
        } else {
            Some(Span::new(core::cmp::max(self.end, other.start), other.end))
        };
        (pre, post)
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Span({}, {})", self.start, self.end)
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}, {})", self.start, self.end)
    }
}

#[test]
fn test_span_macro() {
    assert_eq!(
        span!(0 / 1, 1 / 1),
        Span::new(Rational::new(0, 1), Rational::new(1, 1))
    );
    assert_eq!(
        span!(Rational::new(1, 1), 4 / 1),
        span!(1 / 1, Rational::new(4, 1)),
    );
}

#[test]
#[cfg(feature = "std")]
fn test_span_fmt() {
    for n in 0..10 {
        let a = Rational::new(n, 10);
        let b = Rational::new(n + 1, 10);
        let span = span!(a, b);
        println!("{:?} | {}", span, span);
    }
}

#[test]
fn test_span_intersect() {
    assert_eq!(
        span!(0 / 1, 3 / 4).intersect(span!(1 / 4, 1 / 1)),
        Some(span!(1 / 4, 3 / 4))
    );
    assert_eq!(span!(0 / 1, 1 / 4).intersect(span!(3 / 4, 1 / 1)), None);
}

#[test]
fn test_span_difference() {
    let s1 = Span::new(Rational::new(2, 1), Rational::new(5, 1));

    // Case 1: other is entirely before self
    let other = Span::new(Rational::new(0, 1), Rational::new(1, 1));
    assert_eq!(s1.difference(other), (Some(other), None));

    // Case 2: other is entirely after self
    let other = Span::new(Rational::new(6, 1), Rational::new(8, 1));
    assert_eq!(s1.difference(other), (None, Some(other)));

    // Case 3: other intersects self at the start
    let other = Span::new(Rational::new(1, 1), Rational::new(3, 1));
    assert_eq!(
        s1.difference(other),
        (
            Some(Span::new(Rational::new(1, 1), Rational::new(2, 1))),
            None
        )
    );

    // Case 4: other intersects self at the end
    let other = Span::new(Rational::new(4, 1), Rational::new(6, 1));
    assert_eq!(
        s1.difference(other),
        (
            None,
            Some(Span::new(Rational::new(5, 1), Rational::new(6, 1)))
        )
    );

    // Case 5: other is entirely within self
    let other = Span::new(Rational::new(3, 1), Rational::new(4, 1));
    assert_eq!(s1.difference(other), (None, None));

    // Case 6: self is entirely within other
    let other = Span::new(Rational::new(1, 1), Rational::new(6, 1));
    assert_eq!(
        s1.difference(other),
        (
            Some(Span::new(Rational::new(1, 1), Rational::new(2, 1))),
            Some(Span::new(Rational::new(5, 1), Rational::new(6, 1)))
        )
    );
}

#[test]
fn test_cycles() {
    // Test basic cycles with integer boundaries
    let span = span!(0 / 1, 3 / 1);
    let cycles: Vec<_> = span.cycles().collect();
    assert_eq!(cycles.len(), 3);
    assert_eq!(cycles[0], span!(0 / 1, 1 / 1));
    assert_eq!(cycles[1], span!(1 / 1, 2 / 1));
    assert_eq!(cycles[2], span!(2 / 1, 3 / 1));

    // Test cycles with fractional start
    let span = span!(1 / 2, 3 / 1);
    let cycles: Vec<_> = span.cycles().collect();
    assert_eq!(cycles.len(), 3);
    assert_eq!(cycles[0], span!(1 / 2, 1 / 1));
    assert_eq!(cycles[1], span!(1 / 1, 2 / 1));
    assert_eq!(cycles[2], span!(2 / 1, 3 / 1));

    // Test cycles with fractional end
    let span = span!(0 / 1, 5 / 2);
    let cycles: Vec<_> = span.cycles().collect();
    assert_eq!(cycles.len(), 3);
    assert_eq!(cycles[0], span!(0 / 1, 1 / 1));
    assert_eq!(cycles[1], span!(1 / 1, 2 / 1));
    assert_eq!(cycles[2], span!(2 / 1, 5 / 2));

    // Test empty span
    let span = span!(1 / 1, 1 / 1);
    let cycles: Vec<_> = span.cycles().collect();
    assert_eq!(cycles.len(), 0);

    // Test span shorter than one cycle
    let span = span!(1 / 2, 3 / 4);
    let cycles: Vec<_> = span.cycles().collect();
    assert_eq!(cycles.len(), 1);
    assert_eq!(cycles[0], span!(1 / 2, 3 / 4));

    // Test negative start
    let span = span!(-1 / 1, 2 / 1);
    let cycles: Vec<_> = span.cycles().collect();
    assert_eq!(cycles.len(), 3);
    assert_eq!(cycles[0], span!(-1 / 1, 0 / 1));
    assert_eq!(cycles[1], span!(0 / 1, 1 / 1));
    assert_eq!(cycles[2], span!(1 / 1, 2 / 1));
}

#[test]
fn test_step_cycles() {
    use crate::Rational;
    use alloc::vec;

    // Test with simple step pattern [1, 1, 1] (equivalent to regular cycles)
    let span = span!(0 / 1, 3 / 1);
    let steps = vec![Rational::from(1), Rational::from(1), Rational::from(1)];
    let step_cycles: Vec<_> = span.step_cycles(steps.into_iter()).collect();
    assert_eq!(step_cycles.len(), 3);
    assert_eq!(
        step_cycles[0],
        (span!(0 / 1, 1 / 1), span!(0 / 1, 1 / 1), 0)
    );
    assert_eq!(
        step_cycles[1],
        (span!(1 / 1, 2 / 1), span!(1 / 1, 2 / 1), 1)
    );
    assert_eq!(
        step_cycles[2],
        (span!(2 / 1, 3 / 1), span!(2 / 1, 3 / 1), 2)
    );

    // Test with irregular step pattern [1, 2, 1]
    let span = span!(0 / 1, 4 / 1);
    let steps = vec![Rational::from(1), Rational::from(2), Rational::from(1)];
    let step_cycles: Vec<_> = span.step_cycles(steps.into_iter()).collect();
    assert_eq!(step_cycles.len(), 3);
    assert_eq!(
        step_cycles[0],
        (span!(0 / 1, 1 / 1), span!(0 / 1, 1 / 1), 0)
    );
    assert_eq!(
        step_cycles[1],
        (span!(1 / 1, 3 / 1), span!(1 / 1, 3 / 1), 1)
    );
    assert_eq!(
        step_cycles[2],
        (span!(3 / 1, 4 / 1), span!(3 / 1, 4 / 1), 2)
    );

    // Test with fractional steps
    let span = span!(0 / 1, 2 / 1);
    let steps = vec![
        Rational::new(1, 2),
        Rational::new(1, 2),
        Rational::new(1, 2),
        Rational::new(1, 2),
    ];
    let step_cycles: Vec<_> = span.step_cycles(steps.into_iter()).collect();
    assert_eq!(step_cycles.len(), 4);
    assert_eq!(
        step_cycles[0],
        (span!(0 / 1, 1 / 2), span!(0 / 1, 1 / 2), 0)
    );
    assert_eq!(
        step_cycles[1],
        (span!(1 / 2, 1 / 1), span!(1 / 2, 1 / 1), 1)
    );
    assert_eq!(
        step_cycles[2],
        (span!(1 / 1, 3 / 2), span!(1 / 1, 3 / 2), 2)
    );
    assert_eq!(
        step_cycles[3],
        (span!(3 / 2, 2 / 1), span!(3 / 2, 2 / 1), 3)
    );

    // Test with span that doesn't align with step pattern
    let span = span!(1 / 2, 3 / 1);
    let steps = vec![Rational::from(1), Rational::from(1)];
    let step_cycles: Vec<_> = span.step_cycles(steps.into_iter()).collect();
    assert_eq!(step_cycles.len(), 3);
    assert_eq!(
        step_cycles[0],
        (span!(1 / 2, 1 / 1), span!(0 / 1, 1 / 1), 0)
    );
    assert_eq!(
        step_cycles[1],
        (span!(1 / 1, 2 / 1), span!(1 / 1, 2 / 1), 1)
    );
    assert_eq!(
        step_cycles[2],
        (span!(2 / 1, 3 / 1), span!(2 / 1, 3 / 1), 0)
    );

    // Another test with span that doesn't align with step pattern
    let span = span!(15 / 4, 15 / 2);
    let steps = vec![Rational::from(2), Rational::from(1)];
    let step_cycles: Vec<_> = span.step_cycles(steps.into_iter()).collect();
    assert_eq!(step_cycles.len(), 3);
    assert_eq!(
        step_cycles[0],
        (span!(15 / 4, 5 / 1), span!(3 / 1, 5 / 1), 0)
    );
    assert_eq!(
        step_cycles[1],
        (span!(5 / 1, 6 / 1), span!(5 / 1, 6 / 1), 1)
    );
    assert_eq!(
        step_cycles[2],
        (span!(6 / 1, 15 / 2), span!(6 / 1, 8 / 1), 0)
    );

    // Test with empty span
    let span = span!(1 / 1, 1 / 1);
    let steps = vec![Rational::from(1), Rational::from(1)];
    let step_cycles: Vec<_> = span.step_cycles(steps.into_iter()).collect();
    assert_eq!(step_cycles.len(), 0);

    // Test with span shorter than one step
    let span = span!(1 / 2, 3 / 4);
    let steps = vec![Rational::from(1), Rational::from(1)];
    let step_cycles: Vec<_> = span.step_cycles(steps.into_iter()).collect();
    assert_eq!(step_cycles.len(), 1);
    assert_eq!(
        step_cycles[0],
        (span!(1 / 2, 3 / 4), span!(0 / 1, 1 / 1), 0)
    );

    // Test with single step
    let span = span!(0 / 1, 2 / 1);
    let steps = vec![Rational::from(2)];
    let step_cycles: Vec<_> = span.step_cycles(steps.into_iter()).collect();
    assert_eq!(step_cycles.len(), 1);
    assert_eq!(
        step_cycles[0],
        (span!(0 / 1, 2 / 1), span!(0 / 1, 2 / 1), 0)
    );

    // Test with multiple cycles of step pattern
    let span = span!(0 / 1, 6 / 1);
    let steps = vec![Rational::from(1), Rational::from(2)];
    let step_cycles: Vec<_> = span.step_cycles(steps.into_iter()).collect();
    assert_eq!(step_cycles.len(), 4);
    assert_eq!(
        step_cycles[0],
        (span!(0 / 1, 1 / 1), span!(0 / 1, 1 / 1), 0)
    );
    assert_eq!(
        step_cycles[1],
        (span!(1 / 1, 3 / 1), span!(1 / 1, 3 / 1), 1)
    );
    assert_eq!(
        step_cycles[2],
        (span!(3 / 1, 4 / 1), span!(3 / 1, 4 / 1), 0)
    );
    assert_eq!(
        step_cycles[3],
        (span!(4 / 1, 6 / 1), span!(4 / 1, 6 / 1), 1)
    );

    // Test with negative start
    let span = span!(-1 / 1, 2 / 1);
    let steps = vec![Rational::from(1), Rational::from(1)];
    let step_cycles: Vec<_> = span.step_cycles(steps.into_iter()).collect();
    assert_eq!(
        step_cycles.len(),
        3,
        "Expected 3 cycles, got {:?}",
        step_cycles
    );
    assert_eq!(
        step_cycles[0],
        (span!(-1 / 1, 0 / 1), span!(-1 / 1, 0 / 1), 1)
    );
    assert_eq!(
        step_cycles[1],
        (span!(0 / 1, 1 / 1), span!(0 / 1, 1 / 1), 0)
    );
    assert_eq!(
        step_cycles[2],
        (span!(1 / 1, 2 / 1), span!(1 / 1, 2 / 1), 1)
    );

    // Test with negative start and different steps
    let span = span!(-4 / 1, 1 / 1);
    let steps = vec![Rational::from(1), Rational::from(2)];
    let step_cycles: Vec<_> = span.step_cycles(steps.into_iter()).collect();
    assert_eq!(
        step_cycles.len(),
        4,
        "Expected 4 cycles, got {:?}",
        step_cycles
    );
    assert_eq!(
        step_cycles[0],
        (span!(-4 / 1, -3 / 1), span!(-5 / 1, -3 / 1), 1)
    );
    assert_eq!(
        step_cycles[1],
        (span!(-3 / 1, -2 / 1), span!(-3 / 1, -2 / 1), 0)
    );
    assert_eq!(
        step_cycles[2],
        (span!(-2 / 1, 0 / 1), span!(-2 / 1, 0 / 1), 1)
    );
    assert_eq!(
        step_cycles[3],
        (span!(0 / 1, 1 / 1), span!(0 / 1, 1 / 1), 0)
    );
}

#[test]
fn test_step_cycles_complex_patterns() {
    use crate::Rational;
    use alloc::vec;

    // Test with complex fractional pattern
    let span = span!(0 / 1, 2 / 1);
    let steps = vec![
        Rational::new(1, 3), // 1/3
        Rational::new(2, 3), // 2/3
        Rational::new(1, 1), // 1
    ];
    let step_cycles: Vec<_> = span.step_cycles(steps.into_iter()).collect();
    assert_eq!(step_cycles.len(), 3);
    assert_eq!(
        step_cycles[0],
        (span!(0 / 1, 1 / 3), span!(0 / 1, 1 / 3), 0)
    );
    assert_eq!(
        step_cycles[1],
        (span!(1 / 3, 1 / 1), span!(1 / 3, 1 / 1), 1)
    );
    assert_eq!(
        step_cycles[2],
        (span!(1 / 1, 2 / 1), span!(1 / 1, 2 / 1), 2)
    );

    // Test with very small steps
    let span = span!(0 / 1, 1 / 2);
    let steps = vec![
        Rational::new(1, 10), // 0.1
        Rational::new(1, 10), // 0.1
        Rational::new(1, 10), // 0.1
        Rational::new(1, 10), // 0.1
        Rational::new(1, 10), // 0.1
    ];
    let step_cycles: Vec<_> = span.step_cycles(steps.into_iter()).collect();
    assert_eq!(step_cycles.len(), 5);
    assert_eq!(
        step_cycles[0],
        (span!(0 / 1, 1 / 10), span!(0 / 1, 1 / 10), 0)
    );
    assert_eq!(
        step_cycles[1],
        (span!(1 / 10, 1 / 5), span!(1 / 10, 1 / 5), 1)
    );
    assert_eq!(
        step_cycles[2],
        (span!(1 / 5, 3 / 10), span!(1 / 5, 3 / 10), 2)
    );
    assert_eq!(
        step_cycles[3],
        (span!(3 / 10, 2 / 5), span!(3 / 10, 2 / 5), 3)
    );
    assert_eq!(
        step_cycles[4],
        (span!(2 / 5, 1 / 2), span!(2 / 5, 1 / 2), 4)
    );

    // Test with mixed step sizes
    let span = span!(0 / 1, 3 / 1);
    let steps = vec![
        Rational::new(1, 2), // 0.5
        Rational::new(3, 2), // 1.5
        Rational::new(1, 1), // 1.0
    ];
    let step_cycles: Vec<_> = span.step_cycles(steps.into_iter()).collect();
    assert_eq!(step_cycles.len(), 3);
    assert_eq!(
        step_cycles[0],
        (span!(0 / 1, 1 / 2), span!(0 / 1, 1 / 2), 0)
    );
    assert_eq!(
        step_cycles[1],
        (span!(1 / 2, 2 / 1), span!(1 / 2, 2 / 1), 1)
    );
    assert_eq!(
        step_cycles[2],
        (span!(2 / 1, 3 / 1), span!(2 / 1, 3 / 1), 2)
    );
}
