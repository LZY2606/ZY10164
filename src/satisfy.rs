//! Satisfiability and least-witness computation for [`VersionReq`].
//!
//! This module answers, at the level of comparator semantics rather than by
//! scanning a bounded list of candidate releases, whether the conjunction of
//! two version requirements admits *any* version, and if so what the least
//! such version is under Cargo's precedence ordering.
//!
//! See [`VersionReq::intersection`] for the public entry point.
//!
//! # How the least witness is found
//!
//! A comparator matches a set of versions which, projected onto the totally
//! ordered sequence of `major.minor.patch` triples, is an interval. At a
//! single triple the matching positions are an interval in the pre-release
//! order (possibly with the ordinary release as its top). [`classify`]
//! produces that interval symbolically for every [`Op`]: `=`, `>`, `>=`, `<`,
//! `<=`, `~`, `^`, and wildcard, including the missing-minor and
//! missing-patch forms.
//!
//! The conjunction of all comparators has its lowest triple at the maximum of
//! the comparators' lower edges. Only that triple, its immediate successor,
//! and the anchor triples of comparators carrying explicit pre-releases can
//! contain the least witness:
//!
//! - the first two cover interior stable triples and the open stable bound
//!   (`<I.J.0`) that makes the lowest triple pre-release-only;
//! - a pre-release witness can only be *authorized* (see below) by a
//!   comparator naming that exact triple with a pre-release, so no other
//!   triple can supply a lower pre-release witness.
//!
//! At each candidate triple the symbolic intervals are intersected and the
//! least admissible pre-release or the stable release is tried.
//!
//! # Pre-release authorization
//!
//! Cargo does not compare pre-releases as ordinary string bounds. Independently
//! for each [`VersionReq`], a pre-release satisfies the requirement only when
//! at least one of its comparators has the identical `major.minor.patch` and a
//! non-empty pre-release. For an intersection this authorization must hold in
//! *both* requirements. A strictly-greater pre-release bound such as
//! `>1.2.3-alpha` additionally admits pre-releases starting at the immediate
//! successor `1.2.3-alpha.0`, obtained by appending `.0`; that successor is
//! included as a candidate even though no comparator names it.
//!
//! # Discrete successors and what is never fabricated
//!
//! Within one triple, every non-empty pre-release interval has a least
//! element, and the successor of any identifier `p` is `p.0` (which always
//! exists and never overflows). Triples have checked lexicographic successors
//! on `u64`. The one order-theoretic gap without a successor lies immediately
//! below an ordinary release: there is no greatest pre-release. The algorithm
//! never invents a version across that gap, so an open bound like
//! `>1.2.3, <1.2.4` is reported unsatisfiable rather than matched by a
//! fabricated stable successor. Likewise, a lower edge that would increment a
//! component past `u64::MAX` reports [`ConflictReason::VersionSpaceExhausted`]
//! instead of wrapping.
//!
//! # Complexity
//!
//! `O(n + m)` time in the number of comparators of the two requirements, with
//! `O(n + m)` temporary storage for the candidate triples and pre-release
//! identifiers. The running time does not depend on the magnitude of any
//! version component.
//!
//! # Compatibility
//!
//! The new API is additive: existing types and `matches` behavior are
//! unchanged. Everything is `no_std` (relying only on `alloc`), and the
//! `serde` feature provides hand-written Serialize/Deserialize without
//! requiring serde's derive macros.

use crate::eval::pre_is_compatible;
use crate::{BuildMetadata, Comparator, Op, Prerelease, Version, VersionReq};
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt::{self, Display, Formatter};

/// The least possible pre-release identifier: the single numeric identifier
/// `0`. It is valid SemVer (one numeric identifier, no leading zero) and is
/// the least element of the pre-release ordering because every numeric
/// identifier is below every non-numeric one and `0` is the least numeric
/// identifier.
const PRE_ZERO: &str = "0";

/// A major.minor.patch triple ordered lexicographically.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
struct Triple {
    major: u64,
    minor: u64,
    patch: u64,
}

impl Triple {
    const fn new(major: u64, minor: u64, patch: u64) -> Self {
        Triple {
            major,
            minor,
            patch,
        }
    }

    /// Immediate lexicographic successor, without wrapping on overflow.
    fn next(self) -> Option<Self> {
        if self.patch < u64::MAX {
            Some(Triple::new(self.major, self.minor, self.patch + 1))
        } else if self.minor < u64::MAX {
            Some(Triple::new(self.major, self.minor + 1, 0))
        } else if self.major < u64::MAX {
            Some(Triple::new(self.major + 1, 0, 0))
        } else {
            None
        }
    }
}

/// Why a conjunction of requirements is unsatisfiable.
#[derive(Clone, Eq, PartialEq, Debug)]
#[non_exhaustive]
pub enum ConflictReason {
    /// The requirements impose incompatible ordering, such as `>=2.0.0`
    /// together with `<1.0.0`, or `>1.2.3, <1.2.4` where the only versions
    /// strictly between the two bounds would be pre-releases that neither
    /// requirement authorizes.
    DisjointBounds,
    /// Satisfying the requirements would need a component larger than
    /// `u64::MAX`, for example `>18446744073709551615` or
    /// `>18446744073709551615.18446744073709551615.18446744073709551615`.
    VersionSpaceExhausted,
}

/// Explanation returned by [`VersionReq::intersection`] when no version can
/// satisfy both requirements.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Conflict {
    /// Which kind of incompatibility was detected.
    pub reason: ConflictReason,
    /// Display representation of the first requirement.
    pub first: String,
    /// Display representation of the second requirement.
    pub second: String,
}

/// Result of computing the intersection of two [`VersionReq`]s.
///
/// When the requirements have any satisfying version in common, Cargo's
/// comparator semantics always single out a least one, which is returned as
/// [`Intersection::Witness`]. Otherwise [`Intersection::Unsatisfiable`]
/// explains why.
///
/// There is deliberately no third, "satisfiable but with no least version"
/// outcome. It cannot occur for conjunctions of Cargo comparators: the
/// pre-release ordering has a least identifier (`0`), a strictly-greater
/// pre-release always has an immediate successor obtained by appending `.0`,
/// and stable triples are discrete. The one order-theoretic gap that has no
/// successor — immediately *below* a stable release — can only surface as an
/// unsatisfiable conjunction, never as a least witness, so no successor is
/// fabricated across it.
#[derive(Clone, Eq, PartialEq, Debug)]
#[non_exhaustive]
pub enum Intersection {
    /// A version that satisfies both requirements, chosen to be the least
    /// such version by SemVer precedence (build metadata is never part of
    /// precedence, so the witness always carries empty build metadata).
    Witness(Version),
    /// No version satisfies both requirements.
    Unsatisfiable(Conflict),
}

/// Position of a pre-release bound at a fixed triple.
#[derive(Clone)]
enum PreLo {
    /// `pre >=` the given non-empty identifier.
    Ge(Prerelease),
    /// `pre >` the given non-empty identifier.
    Gt(Prerelease),
}

/// Position of an upper bound on pre-releases at a fixed triple.
#[derive(Clone)]
enum PreHi {
    /// No upper bound.
    Unbounded,
    /// Every pre-release but not the stable release (`pre < stable`).
    LtStable,
    /// `pre <=` the given identifier.
    Le(Prerelease),
    /// `pre <` the given identifier.
    Lt(Prerelease),
}

/// The set of positions matched by one comparator at one particular triple,
/// expressed symbolically in the pre-release order.
#[derive(Clone)]
struct TripleSet {
    /// Inclusive-or-exclusive lower bound on pre-releases. `None` means the
    /// comparator does not match any pre-release at this triple.
    pre_lo: Option<PreLo>,
    /// Upper bound on pre-releases.
    pre_hi: PreHi,
    /// Whether the ordinary (non-pre-release) release of the triple matches.
    stable: bool,
}

impl TripleSet {
    fn empty() -> Self {
        TripleSet {
            pre_lo: None,
            pre_hi: PreHi::LtStable,
            stable: false,
        }
    }

    fn all() -> Self {
        TripleSet {
            pre_lo: Some(PreLo::Ge(Prerelease::new(PRE_ZERO).unwrap())),
            pre_hi: PreHi::Unbounded,
            stable: true,
        }
    }

    fn stable_only() -> Self {
        TripleSet {
            pre_lo: None,
            pre_hi: PreHi::LtStable,
            stable: true,
        }
    }

    fn all_pre() -> Self {
        TripleSet {
            pre_lo: Some(PreLo::Ge(Prerelease::new(PRE_ZERO).unwrap())),
            pre_hi: PreHi::LtStable,
            stable: false,
        }
    }

    fn pre_point(pre: Prerelease) -> Self {
        TripleSet {
            pre_lo: Some(PreLo::Ge(pre.clone())),
            pre_hi: PreHi::Le(pre),
            stable: false,
        }
    }

    /// `pre >= lo`, and additionally the stable release when `stable`.
    fn pre_ge(lo: Prerelease, stable: bool) -> Self {
        TripleSet {
            pre_lo: Some(PreLo::Ge(lo)),
            pre_hi: PreHi::Unbounded,
            stable,
        }
    }

    /// `pre > lo`, and additionally the stable release when `stable`.
    fn pre_gt(lo: Prerelease, stable: bool) -> Self {
        TripleSet {
            pre_lo: Some(PreLo::Gt(lo)),
            pre_hi: PreHi::Unbounded,
            stable,
        }
    }

    fn pre_le(hi: Prerelease) -> Self {
        TripleSet {
            pre_lo: Some(PreLo::Ge(Prerelease::new(PRE_ZERO).unwrap())),
            pre_hi: PreHi::Le(hi),
            stable: false,
        }
    }

    fn pre_lt(hi: Prerelease) -> Self {
        TripleSet {
            pre_lo: Some(PreLo::Ge(Prerelease::new(PRE_ZERO).unwrap())),
            pre_hi: PreHi::Lt(hi),
            stable: false,
        }
    }

    fn is_empty(&self) -> bool {
        !self.stable && !self.raw_pre_nonempty()
    }

    /// Whether the raw pre-release interval contains any legal identifier,
    /// independently of authorization.
    fn raw_pre_nonempty(&self) -> bool {
        let Some(lo) = &self.pre_lo else {
            return false;
        };
        let least = match lo {
            PreLo::Ge(pre) => pre.clone(),
            PreLo::Gt(pre) => pre.successor(),
        };
        match &self.pre_hi {
            PreHi::Unbounded | PreHi::LtStable => true,
            PreHi::Le(hi) => least <= *hi,
            PreHi::Lt(hi) => least < *hi,
        }
    }

    /// Whether the given non-empty pre-release lies in this set.
    fn contains_pre(&self, pre: &Prerelease) -> bool {
        let above_lo = match &self.pre_lo {
            None => false,
            Some(PreLo::Ge(lo)) => pre >= lo,
            Some(PreLo::Gt(lo)) => pre > lo,
        };
        let below_hi = match &self.pre_hi {
            PreHi::Unbounded | PreHi::LtStable => true,
            PreHi::Le(hi) => pre <= hi,
            PreHi::Lt(hi) => pre < hi,
        };
        above_lo && below_hi
    }

    /// Intersection of two sets at the same triple.
    fn intersect(self, rhs: &TripleSet) -> TripleSet {
        let pre_lo = match (&self.pre_lo, &rhs.pre_lo) {
            (None, _) | (_, None) => None,
            (Some(left), Some(right)) => {
                // Pick the bound whose admitted set starts later. At equal
                // named identifiers the strict bound starts later.
                let key = |bound: &PreLo| match bound {
                    PreLo::Ge(pre) => (Mark::Pre(pre.clone()), false),
                    PreLo::Gt(pre) => (Mark::Pre(pre.clone()), true),
                };
                let (left_key, right_key) = (key(left), key(right));
                Some(if left_key > right_key {
                    left.clone()
                } else {
                    right.clone()
                })
            }
        };

        let pre_hi = match (&self.pre_hi, &rhs.pre_hi) {
            (PreHi::Unbounded, other) | (other, PreHi::Unbounded) => other.clone(),
            (PreHi::LtStable, other) | (other, PreHi::LtStable) => {
                if matches!(other, PreHi::Unbounded) {
                    PreHi::LtStable
                } else {
                    other.clone()
                }
            }
            (PreHi::Le(left), PreHi::Le(right)) => PreHi::Le(if left <= right {
                left.clone()
            } else {
                right.clone()
            }),
            (PreHi::Lt(left), PreHi::Lt(right)) => PreHi::Lt(if left <= right {
                left.clone()
            } else {
                right.clone()
            }),
            (PreHi::Le(le), PreHi::Lt(lt)) => {
                // The position `lt` is below the position `le` exactly when
                // `lt <= le`.
                if lt <= le {
                    PreHi::Lt(lt.clone())
                } else {
                    PreHi::Le(le.clone())
                }
            }
            (PreHi::Lt(lt), PreHi::Le(le)) => {
                if lt <= le {
                    PreHi::Lt(lt.clone())
                } else {
                    PreHi::Le(le.clone())
                }
            }
        };

        TripleSet {
            pre_lo,
            pre_hi,
            stable: self.stable && rhs.stable,
        }
    }
}

impl Prerelease {
    /// The immediate successor pre-release in the SemVer pre-release order:
    /// appending a `.0` identifier. This always exists and never overflows:
    /// `p < p.0` and there is no legal identifier strictly between the two,
    /// because `p.0` has `p` as a proper dot-separated prefix.
    fn successor(&self) -> Prerelease {
        let mut string = String::with_capacity(self.len() + 2);
        string.push_str(self.as_str());
        string.push('.');
        string.push('0');
        // SAFETY: appending ".0" to a legal pre-release identifier produces
        // a legal pre-release identifier.
        unsafe { Prerelease::new_unchecked(string) }
    }
}

/// The position at one triple from which a comparator's raw matching set
/// starts. This is only used to find the globally lowest candidate triple.
#[derive(Clone, Eq, PartialEq)]
enum LowMark {
    /// Every pre-release at the triple can match (low is below `0`).
    AllPre,
    /// Pre-releases starting at this position.
    At(Mark),
}

#[derive(Clone)]
enum Mark {
    Pre(Prerelease),
    Stable,
}

impl PartialEq for Mark {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Mark {}

impl Ord for Mark {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Mark::Pre(left), Mark::Pre(right)) => left.cmp(right),
            (Mark::Pre(_), Mark::Stable) => Ordering::Less,
            (Mark::Stable, Mark::Pre(_)) => Ordering::Greater,
            (Mark::Stable, Mark::Stable) => Ordering::Equal,
        }
    }
}

impl PartialOrd for Mark {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialOrd for LowMark {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for LowMark {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (LowMark::AllPre, LowMark::AllPre) => Ordering::Equal,
            (LowMark::AllPre, LowMark::At(_)) => Ordering::Less,
            (LowMark::At(_), LowMark::AllPre) => Ordering::Greater,
            (LowMark::At(left), LowMark::At(right)) => left.cmp(right),
        }
    }
}

/// Symbolic counterpart of `matches_impl` from `eval.rs`, specialized to one
/// triple: returns the set of pre-release/stable positions at that triple
/// which the comparator matches.
fn classify(cmp: &Comparator, ver: Triple) -> TripleSet {
    let Triple {
        major,
        minor,
        patch,
    } = ver;
    match cmp.op {
        Op::Exact | Op::Wildcard => classify_exact(cmp, major, minor, patch),
        Op::Greater => classify_greater(cmp, major, minor, patch),
        Op::GreaterEq => classify_greater_eq(cmp, major, minor, patch),
        Op::Less => classify_less(cmp, major, minor, patch),
        Op::LessEq => classify_less_eq(cmp, major, minor, patch),
        Op::Tilde => classify_tilde(cmp, major, minor, patch),
        Op::Caret => classify_caret(cmp, major, minor, patch),
    }
}

fn classify_exact(cmp: &Comparator, major: u64, minor: u64, patch: u64) -> TripleSet {
    if major != cmp.major {
        return TripleSet::empty();
    }
    if let Some(cmp_minor) = cmp.minor {
        if minor != cmp_minor {
            return TripleSet::empty();
        }
    }
    if let Some(cmp_patch) = cmp.patch {
        if patch != cmp_patch {
            return TripleSet::empty();
        }
    }
    if cmp.pre.is_empty() {
        TripleSet::stable_only()
    } else {
        TripleSet::pre_point(cmp.pre.clone())
    }
}

fn classify_greater(cmp: &Comparator, major: u64, minor: u64, patch: u64) -> TripleSet {
    if major != cmp.major {
        return if major > cmp.major {
            TripleSet::all()
        } else {
            TripleSet::empty()
        };
    }

    let Some(cmp_minor) = cmp.minor else {
        return TripleSet::empty();
    };

    if minor != cmp_minor {
        return if minor > cmp_minor {
            TripleSet::all()
        } else {
            TripleSet::empty()
        };
    }

    let Some(cmp_patch) = cmp.patch else {
        return TripleSet::empty();
    };

    if patch != cmp_patch {
        return if patch > cmp_patch {
            TripleSet::all()
        } else {
            TripleSet::empty()
        };
    }

    if cmp.pre.is_empty() {
        // Nothing is above the stable position.
        TripleSet::empty()
    } else {
        // Pre-releases strictly above the bound, plus the ordinary release
        // (which outranks every pre-release of the same triple).
        TripleSet::pre_gt(cmp.pre.clone(), true)
    }
}

fn classify_greater_eq(cmp: &Comparator, major: u64, minor: u64, patch: u64) -> TripleSet {
    if major != cmp.major {
        return if major > cmp.major {
            TripleSet::all()
        } else {
            TripleSet::empty()
        };
    }

    let Some(cmp_minor) = cmp.minor else {
        // `>=I` is `>=I.0.0` including pre-releases above other majors only;
        // at the anchor triple nothing below the stable release matches.
        return TripleSet::stable_only();
    };

    if minor != cmp_minor {
        return if minor > cmp_minor {
            TripleSet::all()
        } else {
            TripleSet::empty()
        };
    }

    let Some(cmp_patch) = cmp.patch else {
        // `>=I.J` behaves like `>=I.J.0`.
        return TripleSet::stable_only();
    };

    if patch != cmp_patch {
        return if patch > cmp_patch {
            TripleSet::all()
        } else {
            TripleSet::empty()
        };
    }

    if cmp.pre.is_empty() {
        TripleSet::stable_only()
    } else {
        TripleSet::pre_ge(cmp.pre.clone(), true)
    }
}

fn classify_less(cmp: &Comparator, major: u64, minor: u64, patch: u64) -> TripleSet {
    if major != cmp.major {
        return if major < cmp.major {
            TripleSet::all()
        } else {
            TripleSet::empty()
        };
    }

    let Some(cmp_minor) = cmp.minor else {
        return TripleSet::empty();
    };

    if minor != cmp_minor {
        return if minor < cmp_minor {
            TripleSet::all()
        } else {
            TripleSet::empty()
        };
    }

    let Some(cmp_patch) = cmp.patch else {
        return TripleSet::empty();
    };

    if patch != cmp_patch {
        return if patch < cmp_patch {
            TripleSet::all()
        } else {
            TripleSet::empty()
        };
    }

    if cmp.pre.is_empty() {
        TripleSet::all_pre()
    } else {
        TripleSet::pre_lt(cmp.pre.clone())
    }
}

fn classify_less_eq(cmp: &Comparator, major: u64, minor: u64, patch: u64) -> TripleSet {
    if major != cmp.major {
        return if major < cmp.major {
            TripleSet::all()
        } else {
            TripleSet::empty()
        };
    }

    let Some(cmp_minor) = cmp.minor else {
        // `<=I` is implemented as `exact(I) | less(I)`: within the anchor
        // major only stable versions match (`less` contributes nothing for a
        // major-only comparator).
        return TripleSet::stable_only();
    };

    if minor != cmp_minor {
        return if minor < cmp_minor {
            TripleSet::all()
        } else {
            TripleSet::empty()
        };
    }

    let Some(cmp_patch) = cmp.patch else {
        // `<=I.J` is `exact(I.J) | less(I.J)`; at the anchor triple only the
        // stable release matches.
        return TripleSet::stable_only();
    };

    if patch != cmp_patch {
        return if patch < cmp_patch {
            TripleSet::all()
        } else {
            TripleSet::empty()
        };
    }

    if cmp.pre.is_empty() {
        // Everything at the triple up to and including the stable release.
        TripleSet {
            pre_lo: Some(PreLo::Ge(Prerelease::new(PRE_ZERO).unwrap())),
            pre_hi: PreHi::Unbounded,
            stable: true,
        }
    } else {
        TripleSet::pre_le(cmp.pre.clone())
    }
}

fn classify_tilde(cmp: &Comparator, major: u64, minor: u64, patch: u64) -> TripleSet {
    if major != cmp.major {
        return TripleSet::empty();
    }
    if let Some(cmp_minor) = cmp.minor {
        if minor != cmp_minor {
            return TripleSet::empty();
        }
    }
    let Some(cmp_patch) = cmp.patch else {
        return TripleSet::stable_only();
    };
    if patch != cmp_patch {
        return if patch > cmp_patch {
            TripleSet::all()
        } else {
            TripleSet::empty()
        };
    }
    if cmp.pre.is_empty() {
        TripleSet::stable_only()
    } else {
        TripleSet::pre_ge(cmp.pre.clone(), true)
    }
}

fn classify_caret(cmp: &Comparator, major: u64, minor: u64, patch: u64) -> TripleSet {
    if major != cmp.major {
        return TripleSet::empty();
    }

    let Some(cmp_minor) = cmp.minor else {
        return TripleSet::stable_only();
    };

    let Some(cmp_patch) = cmp.patch else {
        if cmp.major > 0 {
            if minor >= cmp_minor {
                return TripleSet::stable_only();
            }
        } else if minor == cmp_minor {
            return TripleSet::stable_only();
        }
        return TripleSet::empty();
    };

    let same_triple = minor == cmp_minor && patch == cmp_patch;
    if cmp.major > 0 {
        if minor != cmp_minor {
            if minor > cmp_minor {
                return TripleSet::all();
            }
            return TripleSet::empty();
        } else if patch != cmp_patch {
            if patch > cmp_patch {
                return TripleSet::all();
            }
            return TripleSet::empty();
        }
    } else if cmp_minor > 0 {
        if minor != cmp_minor {
            return TripleSet::empty();
        } else if patch != cmp_patch {
            if patch > cmp_patch {
                return TripleSet::all();
            }
            return TripleSet::empty();
        }
    } else if !same_triple {
        return TripleSet::empty();
    }

    if cmp.pre.is_empty() {
        TripleSet::stable_only()
    } else {
        TripleSet::pre_ge(cmp.pre.clone(), true)
    }
}

/// The lowest position from which the comparator's raw matching set starts,
/// together with its triple. A `None` triple means the bound lies beyond the
/// representable version space.
fn comparator_low(cmp: &Comparator) -> (Option<Triple>, LowMark) {
    let anchor = Triple::new(cmp.major, cmp.minor.unwrap_or(0), cmp.patch.unwrap_or(0));

    match cmp.op {
        Op::Exact | Op::Wildcard => {
            let mark = if cmp.patch.is_some() && !cmp.pre.is_empty() {
                LowMark::At(Mark::Pre(cmp.pre.clone()))
            } else {
                LowMark::At(Mark::Stable)
            };
            (Some(anchor), mark)
        }
        Op::Greater => {
            if cmp.minor.is_none() {
                // `>I` means `>=(I+1).0.0`.
                let triple = cmp
                    .major
                    .checked_add(1)
                    .map(|major| Triple::new(major, 0, 0));
                (triple, LowMark::At(Mark::Stable))
            } else if cmp.patch.is_none() {
                // `>I.J` means `>=I.(J+1).0`; if the minor overflows the
                // requirement carries into the major component.
                let Some(minor) = cmp.minor else {
                    unreachable!("patch is only present when minor is present")
                };
                let triple = match minor.checked_add(1) {
                    Some(minor) => Some(Triple::new(cmp.major, minor, 0)),
                    None => cmp
                        .major
                        .checked_add(1)
                        .map(|major| Triple::new(major, 0, 0)),
                };
                (triple, LowMark::At(Mark::Stable))
            } else {
                // `>I.J.K-pre`: the ordinary release matches (it outranks
                // every pre-release), so the low edge is the stable position.
                //
                // `>I.J.K` with no pre-release needs the next triple; at the
                // numeric ceiling that is beyond the representable space.
                if cmp.pre.is_empty() {
                    (anchor.next(), LowMark::At(Mark::Stable))
                } else {
                    (Some(anchor), LowMark::At(Mark::Stable))
                }
            }
        }
        Op::GreaterEq | Op::Tilde | Op::Caret => {
            let mark = if cmp.pre.is_empty() {
                LowMark::At(Mark::Stable)
            } else {
                LowMark::At(Mark::Pre(cmp.pre.clone()))
            };
            (Some(anchor), mark)
        }
        // Upper-bound comparators constrain from below only at the global
        // minimum version; their anchor triple is the top, not the bottom.
        Op::Less | Op::LessEq => (Some(Triple::new(0, 0, 0)), LowMark::AllPre),
    }
}

/// Ordering of candidate low positions where a missing triple denotes a bound
/// beyond the representable space, which sorts above every real triple.
fn cmp_low(left: &(Option<Triple>, LowMark), right: &(Option<Triple>, LowMark)) -> Ordering {
    match (&left.0, &right.0) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Greater,
        (Some(_), None) => Ordering::Less,
        (Some(left_triple), Some(right_triple)) => left_triple
            .cmp(right_triple)
            .then_with(|| left.1.cmp(&right.1)),
    }
}

/// Find the least version satisfying every comparator in `groups`, applying
/// Cargo's pre-release authorization rule independently to each group (one
/// group per `VersionReq`).
pub(crate) fn solve(groups: &[&VersionReq]) -> Result<Version, ConflictReason> {
    let all_comparators: Vec<&Comparator> = groups
        .iter()
        .flat_map(|req| req.comparators.iter())
        .collect();

    // The least candidate triple is the maximum of all comparator low
    // positions. A bound that would increment past u64::MAX is unsatisfiable.
    let mut lowest: Option<(Option<Triple>, LowMark)> = None;
    for cmp in &all_comparators {
        let candidate = comparator_low(cmp);
        if candidate.0.is_none() {
            return Err(ConflictReason::VersionSpaceExhausted);
        }
        if lowest
            .as_ref()
            .map_or(true, |existing| cmp_low(existing, &candidate).is_lt())
        {
            lowest = Some(candidate);
        }
    }

    let start = lowest
        .and_then(|(triple, _)| triple)
        .unwrap_or(Triple::new(0, 0, 0));

    // Candidate triples that can hold the least witness:
    //
    // - `start`: the global low-edge triple;
    // - its immediate successor, which an open stable upper bound
    //   (`<I.J.0`-style) can render empty;
    // - the anchor triple of every comparator carrying a non-empty
    //   pre-release, because only such a comparator can authorize a
    //   pre-release witness, and the witness may be pinned to that anchor
    //   even when earlier triples are raw matches with no authorization.
    //
    // A stable interior triple without any pre-release comparator always has a
    // stable witness, so it never needs to be inspected explicitly.
    let mut candidates: Vec<Triple> = Vec::new();
    candidates.push(start);
    if let Some(successor) = start.next() {
        candidates.push(successor);
    }
    let mut candidate_pres: Vec<(Triple, Prerelease)> = Vec::new();
    for cmp in &all_comparators {
        if cmp.pre.is_empty() {
            continue;
        }
        let (Some(minor), Some(patch)) = (cmp.minor, cmp.patch) else {
            continue;
        };
        let triple = Triple::new(cmp.major, minor, patch);
        // The named identifier itself authorizes an inclusive position ...
        candidate_pres.push((triple, cmp.pre.clone()));
        // ... and a strict `>` bound's least admission is its successor.
        if cmp.op == Op::Greater {
            candidate_pres.push((triple, cmp.pre.successor()));
        }
    }
    for (triple, _) in &candidate_pres {
        candidates.push(*triple);
    }
    candidates.sort();
    candidates.dedup();

    for triple in candidates {
        if triple < start {
            continue;
        }
        if let Some(version) = witness_at(triple, &all_comparators, groups) {
            return Ok(version);
        }
    }

    Err(ConflictReason::DisjointBounds)
}

/// Pre-release identifiers that could be both authorized and be the least
/// admission at `triple`.
///
/// Cargo authorizes a pre-release only through a comparator that names the
/// identical `major.minor.patch` with a non-empty pre-release, so every named
/// identifier is a candidate. A strict `>` comparator additionally admits
/// identifiers starting at the successor of the one it names (appending
/// `.0`), which no comparator may name explicitly but which can still be the
/// least satisfying version.
fn candidate_pres(triple: Triple, comparators: &[&Comparator]) -> Vec<Prerelease> {
    let mut candidates: Vec<Prerelease> = Vec::new();
    // The global least pre-release identifier: an interval bounded only
    // above (such as `<I.J.K-alpha`) starts here even though no comparator
    // names it.
    candidates.push(Prerelease::new(PRE_ZERO).unwrap());
    for cmp in comparators {
        let same_triple = cmp.major == triple.major
            && cmp.minor == Some(triple.minor)
            && cmp.patch == Some(triple.patch);
        if !same_triple || cmp.pre.is_empty() {
            continue;
        }
        candidates.push(cmp.pre.clone());
        if cmp.op == Op::Greater {
            candidates.push(cmp.pre.successor());
        }
    }
    candidates.sort();
    candidates.dedup();
    candidates
}

/// Whether every group authorizes and matches the given pre-release.
fn groups_match(groups: &[&VersionReq], probe: &Version) -> bool {
    groups.iter().all(|req| {
        req.comparators
            .iter()
            .any(|cmp| pre_is_compatible(cmp, probe))
    }) && groups.iter().all(|req| req.matches(probe))
}

/// Construct the least satisfying version at one particular triple, after
/// intersecting every comparator's raw set and applying each group's
/// pre-release authorization.
fn witness_at(
    triple: Triple,
    comparators: &[&Comparator],
    groups: &[&VersionReq],
) -> Option<Version> {
    let mut intersection = TripleSet::all();
    for cmp in comparators {
        intersection = intersection.intersect(&classify(cmp, triple));
        if intersection.is_empty() {
            return None;
        }
    }

    // Pre-releases precede the ordinary release, so consider them first.
    for pre in candidate_pres(triple, comparators) {
        if !intersection.contains_pre(&pre) {
            continue;
        }
        let probe = Version {
            major: triple.major,
            minor: triple.minor,
            patch: triple.patch,
            pre,
            build: BuildMetadata::EMPTY,
        };
        if groups_match(groups, &probe) {
            return Some(probe);
        }
    }

    if intersection.stable {
        let stable = Version::new(triple.major, triple.minor, triple.patch);
        if groups.iter().all(|req| req.matches(&stable)) {
            return Some(stable);
        }
    }

    None
}

pub(crate) fn intersection(first: &VersionReq, second: &VersionReq) -> Intersection {
    match solve(&[first, second]) {
        Ok(version) => Intersection::Witness(version),
        Err(reason) => Intersection::Unsatisfiable(Conflict {
            reason,
            first: first.to_string(),
            second: second.to_string(),
        }),
    }
}

impl Display for ConflictReason {
    fn fmt(&self, formatter: &mut Formatter) -> fmt::Result {
        match self {
            ConflictReason::DisjointBounds => {
                formatter.write_str("the requirements have disjoint version bounds")
            }
            ConflictReason::VersionSpaceExhausted => formatter.write_str(
                "satisfying the requirements would exceed the maximum u64 \
                 version component",
            ),
        }
    }
}

impl Display for Conflict {
    fn fmt(&self, formatter: &mut Formatter) -> fmt::Result {
        write!(
            formatter,
            "no version satisfies both `{}` and `{}`: {}",
            self.first, self.second, self.reason,
        )
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl std::error::Error for Conflict {}
