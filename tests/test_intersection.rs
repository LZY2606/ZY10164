//! Tests for `VersionReq::intersection`: table-driven expectations plus a
//! bounded small-domain exhaustive cross-check against direct `matches`.

#![allow(clippy::needless_pass_by_value)]

use core::cmp::Ordering;
use semver::{ConflictReason, Intersection, Version, VersionReq};

fn req(text: &str) -> VersionReq {
    VersionReq::parse(text).unwrap_or_else(|err| panic!("failed to parse {text:?}: {err}"))
}

#[track_caller]
fn assert_witness(first: &str, second: &str, expected: &str) {
    let first_req = req(first);
    let second_req = req(second);
    match first_req.intersection(&second_req) {
        Intersection::Witness(found) => {
            assert_eq!(
                found.to_string(),
                expected,
                "intersection of {first:?} and {second:?} expected witness {expected}",
            );
            assert!(first_req.matches(&found));
            assert!(second_req.matches(&found));
        }
        Intersection::Unsatisfiable(conflict) => panic!(
            "intersection of {first:?} and {second:?} unexpectedly unsatisfiable: {conflict}"
        ),
        _ => unreachable!("Intersection is an exhaustive enum"),
    }
}

#[track_caller]
fn assert_unsatisfiable(first: &str, second: &str, expected: &ConflictReason) {
    let first_req = req(first);
    let second_req = req(second);
    match first_req.intersection(&second_req) {
        Intersection::Witness(found) => {
            panic!("intersection of {first:?} and {second:?} unexpectedly satisfied by {found}")
        }
        Intersection::Unsatisfiable(conflict) => {
            assert_eq!(
                &conflict.reason, expected,
                "intersection of {first:?} and {second:?} has wrong reason",
            );
            assert_eq!(conflict.first, first_req.to_string());
            assert_eq!(conflict.second, second_req.to_string());
        }
        _ => unreachable!("Intersection is an exhaustive enum"),
    }
}

/// Table-driven cases. Every witness is checked against both `matches`
/// directly by `assert_witness`.
#[test]
fn table_witnesses() {
    #[rustfmt::skip]
    let cases: &[(&str, &str, &str)] = &[
        // Unrestricted requirements start at the global minimum.
        ("*", "*", "0.0.0"),
        ("*", ">=0.0.0", "0.0.0"),
        ("*", ">=1.2.3", "1.2.3"),

        // Stable ranges from ordinary requirements.
        (">=1.0.0, <2.0.0", "^1.5", "1.5.0"),
        (">=1.0.0", ">=1.4.2", "1.4.2"),
        ("<1.0.0", ">0.9.0", "0.9.1"),
        ("<2.0.0", "^1", "1.0.0"),
        ("^0.2.0", "^0.2.5", "0.2.5"),
        ("~1.2.2", ">=1.2.3", "1.2.3"),
        ("1.2.*", ">=1.2.7", "1.2.7"),
        ("=1.2", ">=1.2.0, <1.3.0", "1.2.0"),
        ("=1", ">=1.9.0, <2.0.0", "1.9.0"),

        // Upper bound that is itself an ordinary release.
        ("<1.2.3", ">=1.2.0", "1.2.0"),
        ("<=1.2.3", ">=1.2.3", "1.2.3"),
        ("<=2.1.0", ">=2.0.0", "2.0.0"),

        // Greater with missing components.
        (">1.2", ">=1.3.0", "1.3.0"),
        (">1", ">=2.0.0", "2.0.0"),
        (">0.0.0", "<0.0.2", "0.0.1"),

        // Pre-releases authorized by both requirements.
        (">=2.1.0-alpha2", ">=2.1.0-alpha3", "2.1.0-alpha3"),
        ("=1.2.3-alpha", "=1.2.3-alpha", "1.2.3-alpha"),
        (">1.0.0-alpha", "=1.0.0-alpha.0", "1.0.0-alpha.0"),
        (">=1.0.0-alpha", "=1.0.0-alpha", "1.0.0-alpha"),
        ("~1.2.3-beta.2", "~1.2.3-beta.5", "1.2.3-beta.5"),
        (">1.0.0-a", "=1.0.0-a.0", "1.0.0-a.0"),
        // Strict bound successor is p.0, not a fabricated stable successor.
        (">1.0.0-a.0", "=1.0.0-a.0.0", "1.0.0-a.0.0"),
        // Two strict bounds: the greater strict bound's successor wins.
        (">1.0.0-a, >1.0.0-b", "=1.0.0-b.0", "1.0.0-b.0"),

        // Stable release outranks a pre-release when both are admitted.
        ("^0.5.1-alpha3", "<0.6", "0.5.1"),
        (">=1.0.0-a", "=1.0.0", "1.0.0"),
        ("^1.4.2-beta.5", "=1.4.2", "1.4.2"),
        // But excluding the stable release falls back to the pre-release.
        ("^1.4.2-beta.5, <1.4.2", "^1.4.2-beta.5, <1.4.2", "1.4.2-beta.5"),
        ("^0.5.1-alpha3, <0.5.1", "^0.5.1-alpha3, <0.5.1", "0.5.1-alpha3"),

        // Same requirement conjunction authorizing pre-releases on both sides.
        (">1.0.0-alpha, <1.0.0", ">1.0.0-alpha, <1.0.0", "1.0.0-alpha.0"),
        (">=1.0.0-0, <1.0.0", ">=1.0.0-0, <1.0.0", "1.0.0-0"),
        (">1.0.0-a, <1.0.0-z", ">1.0.0-a", "1.0.0-a.0"),
        (">=1.0.0-alpha, <2.0.0-beta", ">=1.0.0-alpha", "1.0.0-alpha"),

        // Caret requirements sharing the same pre-release both authorize it.
        ("1.2.3-alpha", "1.2.3-beta", "1.2.3-beta"),

        // Build metadata never participates in precedence.
        ("=1.0.0+foo", "=1.0.0+bar", "1.0.0"),
        (">=1.0.0+build", "=1.0.0", "1.0.0"),

        // Large but representable components.
        (
            ">=18446744073709551615.0.0",
            "<=18446744073709551615.0.0",
            "18446744073709551615.0.0",
        ),
        (
            "=18446744073709551615.18446744073709551615.18446744073709551615",
            "=18446744073709551615.18446744073709551615.18446744073709551615",
            "18446744073709551615.18446744073709551615.18446744073709551615",
        ),
    ];

    for (first, second, expected) in cases {
        assert_witness(first, second, expected);
        // Intersection is symmetric.
        assert_witness(second, first, expected);
    }
}

#[test]
fn table_unsatisfiable() {
    let disjoint = &ConflictReason::DisjointBounds;
    #[rustfmt::skip]
    let cases: &[(&str, &str)] = &[
        // Plain disjoint stable ranges.
        (">=2.0.0", "<1.0.0"),
        ("^1", "^2"),
        ("^0.2", "^0.3"),
        (">=1.2, <1.3", ">=1.3.0"),
        (">0.2.0", "<0.2.0"),

        // Adjacent open/closed stable endpoints: the gap holds only
        // pre-releases, which neither requirement authorizes.
        (">1.0.0", "<1.0.1"),
        (">1.0.0-alpha", "<1.0"),
        (">1.2.3", "<1.2.4-alpha"),

        // Identical triple but distinct exact pre-releases.
        ("=1.2.3-alpha", "=1.2.3-beta"),

        // A pre-release required by one side that the other cannot admit.
        ("=1.2.3-alpha", "*"),
        ("=1.2.3-alpha", "=1.2.3"),
        (">1.0.0-alpha, <1.0.0", "*"),
        ("^0.5.1-alpha3", "<0.5.1"),

        // Below the global minimum.
        ("<0.0.0", "*"),
        ("<0.0.0-alpha", "*"),

        // Empty pre-release interval between bounds.
        (">1.2.3-x", "<1.2.3-x"),
    ];

    for (first, second) in cases {
        assert_unsatisfiable(first, second, disjoint);
        assert_unsatisfiable(second, first, disjoint);
    }
}

#[test]
fn version_space_exhausted() {
    let exhausted = &ConflictReason::VersionSpaceExhausted;
    #[rustfmt::skip]
    let cases: &[(&str, &str)] = &[
        (">18446744073709551615", "*"),
        (">18446744073709551615.18446744073709551615.18446744073709551615", "*"),
    ];
    for (first, second) in cases {
        assert_unsatisfiable(first, second, exhausted);
    }
}

#[test]
fn witness_is_least_by_precedence() {
    // The witness must be the least satisfying version. This is verified
    // directly against a finite, predecessor-closed universe in
    // `exhaustive_cross_check`; here spot-check a few tricky minima.
    assert_witness(">=1.0.0-alpha", "=1.0.0-alpha", "1.0.0-alpha");
    assert_witness(">1.0.0-alpha", "=1.0.0-alpha.0", "1.0.0-alpha.0");
}

#[test]
fn display_conflict_is_descriptive() {
    let first = req(">=2.0.0");
    let second = req("<1.0.0");
    if let Intersection::Unsatisfiable(conflict) = first.intersection(&second) {
        let text = conflict.to_string();
        assert!(text.contains(">=2.0.0"), "text was {text}");
        assert!(text.contains("<1.0.0"), "text was {text}");
        assert!(text.contains("disjoint"), "text was {text}");
    } else {
        panic!("expected unsatisfiable");
    }
}

#[test]
fn self_intersection() {
    for text in [
        "*",
        "^1.0.0",
        "~0.2.3",
        "=1.2.3-alpha",
        ">=1.0.0, <2.0.0",
        "<1.0.0",
        "1.2.*",
        ">0.0.0",
    ] {
        let requirement = req(text);
        if let Intersection::Witness(found) = requirement.intersection(&requirement.clone()) {
            assert!(
                requirement.matches(&found),
                "self-intersection witness {found} did not match {text}"
            );
        } else {
            panic!("self-intersection of {text} unexpectedly unsatisfiable");
        }
    }
}

// ---------------------------------------------------------------------------
// Bounded small-domain exhaustive cross-validation.
//
// We construct a finite universe of versions and single-comparator
// requirements over small numeric components and a finite set of
// pre-release identifiers. For every ordered pair of requirements we:
//
//   1. compute the algorithmic intersection witness;
//   2. brute-force the universe with `matches`, sorting versions by
//      precedence (build metadata ignored);
//   3. assert the witness matches both requirements; and
//   4. when the brute-force minimum exists in the universe, assert it equals
//      the witness; otherwise assert that no in-universe version is smaller
//      than the witness.
//
// The numeric component domain is {0, 1, 2}, which is large enough to cover
// 0.x caret rules and adjacent bounds while keeping the pair count bounded.
// Pre-release identifiers are closed under the `.0` successor operation used
// by strict `>` bounds, whenever the successor is itself in the universe.
// ---------------------------------------------------------------------------

const COMPONENTS: [u64; 3] = [0, 1, 2];

// Includes identifiers that are named by generated comparators plus their
// `.0` successors, exercising the strict-bound minimum.
const PRE_IDENTIFIERS: &[&str] = &["0", "1", "a", "b", "a.0", "a.1", "b.0", "a.0.0"];

struct Universe {
    versions: Vec<Version>,
    requirements: Vec<VersionReq>,
}

fn build_universe() -> Universe {
    let mut versions: Vec<Version> = Vec::new();
    for &major in &COMPONENTS {
        for &minor in &COMPONENTS {
            for &patch in &COMPONENTS {
                versions.push(Version::new(major, minor, patch));
                for identifier in PRE_IDENTIFIERS {
                    versions.push(Version {
                        major,
                        minor,
                        patch,
                        pre: semver::Prerelease::new(identifier).unwrap(),
                        build: semver::BuildMetadata::EMPTY,
                    });
                }
            }
        }
    }
    // Sort by precedence (build metadata is always empty here).
    versions.sort_by(Version::cmp_precedence);
    versions.dedup();

    // Single-comparator requirements spanning every operator. Missing minor
    // and patch forms are included, as are non-empty pre-releases.
    let mut texts: Vec<String> = vec!["*".to_owned()];
    let ops = ["=", ">", ">=", "<", "<=", "~", "^"];
    for &major in &COMPONENTS {
        texts.push(format!("{major}.*"));
        for &minor in &COMPONENTS {
            texts.push(format!("{major}.{minor}.*"));
            for &patch in &COMPONENTS {
                for op in ops {
                    texts.push(format!("{op}{major}.{minor}.{patch}"));
                    for identifier in ["a", "b", "0", "a.0"] {
                        texts.push(format!("{op}{major}.{minor}.{patch}-{identifier}"));
                    }
                }
            }
        }
    }

    let mut requirements: Vec<VersionReq> = Vec::new();
    for text in &texts {
        if let Ok(requirement) = VersionReq::parse(text) {
            requirements.push(requirement);
        }
    }
    requirements.sort_by_key(|requirement| requirement.to_string());
    requirements.dedup();

    Universe {
        versions,
        requirements,
    }
}

#[test]
fn exhaustive_cross_check() {
    let universe = build_universe();
    let total = universe.requirements.len();
    assert!(total > 400, "unexpectedly small universe: {total}");

    let mut pairs_checked = 0usize;
    let mut witnesses_checked = 0usize;

    for (i, first) in universe.requirements.iter().enumerate() {
        for second in &universe.requirements[i..] {
            pairs_checked += 1;
            let result = first.intersection(second);

            // Brute-force least in-universe match.
            let brute: Vec<&Version> = universe
                .versions
                .iter()
                .filter(|candidate| first.matches(candidate) && second.matches(candidate))
                .collect();

            match &result {
                Intersection::Witness(found) => {
                    witnesses_checked += 1;
                    assert!(
                        first.matches(found),
                        "witness {found} does not match requirement {first}",
                    );
                    assert!(
                        second.matches(found),
                        "witness {found} does not match requirement {second}",
                    );
                    match brute.first() {
                        Some(least) => {
                            // When the least in-universe match equals the
                            // witness they must agree; if the witness is
                            // outside the finite universe it must still be
                            // strictly below every in-universe match.
                            let ordering = Version::cmp_precedence(found, least);
                            if ordering == Ordering::Equal {
                                assert_eq!(
                                    found, *least,
                                    "witness for {first} and {second} is not least: \
                                     got {found}, least {least}",
                                );
                            } else {
                                assert_eq!(
                                    ordering,
                                    Ordering::Less,
                                    "witness for {first} and {second} is not least: \
                                     got {found}, least {least}",
                                );
                                for candidate in &universe.versions {
                                    if first.matches(candidate) && second.matches(candidate) {
                                        assert!(
                                            Version::cmp_precedence(candidate, found).is_ge(),
                                            "in-universe {candidate} below witness {found} \
                                             for {first} and {second}",
                                        );
                                    }
                                }
                            }
                        }
                        None => {
                            // The witness lies outside the finite universe;
                            // that is fine as long as it really matches.
                        }
                    }
                }
                Intersection::Unsatisfiable(_) => {
                    assert!(
                        brute.is_empty(),
                        "algorithm reported {first} and {second} unsatisfiable but \
                         {brute:?} matches",
                    );
                }
                _ => unreachable!("Intersection is an exhaustive enum"),
            }
        }
    }

    // Guard against the test silently becoming trivial.
    assert!(pairs_checked > 80_000, "checked only {pairs_checked} pairs");
    assert!(
        witnesses_checked > 10_000,
        "saw only {witnesses_checked} witnesses"
    );
}

#[test]
fn exhaustive_two_comparator_conjunctions() {
    // A smaller targeted pass for multi-comparator requirements, including
    // requirements that themselves authorize pre-releases. Stress open
    // endpoints and 0.x carets where the subtle semantics live.
    let universe = build_universe();

    let templates: &[(&str, &str)] = &[
        (">1.0.0", "<1.0.1"),
        (">1.0.0-alpha", "<1.0.0"),
        (">=1.0.0-alpha", "<1.0.0"),
        (">1.0.0-alpha", "<1.0"),
        ("^0.0.1-alpha", "<0.0.2"),
        ("^0.1.0-alpha", "<0.2.0"),
        ("~1.0.0-alpha", "<1.1.0"),
        ("=1.0.0-alpha", ">=1.0.0-alpha"),
        (">0.0.0", "<1.0.0"),
        ("^0.0", ">=0.0.1"),
        ("^0.0.0-alpha", "<0.0.1"),
        (">1.0.0-a", "<1.0.0-b"),
    ];

    for (left_text, right_text) in templates {
        let left = req(left_text);
        for other_text in [right_text, "*"] {
            let right = req(other_text);
            let result = left.intersection(&right);
            let brute: Vec<&Version> = universe
                .versions
                .iter()
                .filter(|candidate| left.matches(candidate) && right.matches(candidate))
                .collect();
            if let Intersection::Witness(found) = &result {
                assert!(left.matches(found), "{found} !~ {left_text}");
                assert!(right.matches(found), "{found} !~ {other_text}");
                if let Some(least) = brute.first() {
                    assert_eq!(*found, **least, "{left_text} / {other_text}");
                }
            } else {
                assert!(brute.is_empty(), "{left_text} / {other_text} falsely unsat");
            }
        }
    }
}

#[cfg(feature = "serde")]
mod serde_form {
    use super::req;
    use semver::{ConflictReason, Intersection, ReqConflict};
    use serde::de::{self, Deserialize, DeserializeSeed, Deserializer, MapAccess, Visitor};
    use serde::ser::{Serialize, SerializeStruct, Serializer};
    use std::fmt::{self, Display};

    // ---------- A tiny serializer accepting string-fielded structs. ------

    struct Wrap;

    #[derive(Debug)]
    struct Unsupported;
    impl Display for Unsupported {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("unsupported")
        }
    }
    impl std::error::Error for Unsupported {}
    impl serde::ser::Error for Unsupported {
        fn custom<T: Display>(_: T) -> Self {
            Unsupported
        }
    }

    #[derive(Default)]
    struct StructCapture {
        rendered: String,
    }

    impl Serializer for &mut Wrap {
        type Ok = String;
        type Error = Unsupported;
        type SerializeSeq = serde::ser::Impossible<String, Unsupported>;
        type SerializeTuple = serde::ser::Impossible<String, Unsupported>;
        type SerializeTupleStruct = serde::ser::Impossible<String, Unsupported>;
        type SerializeTupleVariant = serde::ser::Impossible<String, Unsupported>;
        type SerializeMap = serde::ser::Impossible<String, Unsupported>;
        type SerializeStruct = StructCapture;
        type SerializeStructVariant = serde::ser::Impossible<String, Unsupported>;

        fn serialize_str(self, value: &str) -> Result<String, Unsupported> {
            Ok(value.to_owned())
        }
        fn serialize_struct(
            self,
            _name: &'static str,
            len: usize,
        ) -> Result<StructCapture, Unsupported> {
            Ok(StructCapture {
                rendered: String::with_capacity(len * 16),
            })
        }
        fn serialize_bool(self, _: bool) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_i8(self, _: i8) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_i16(self, _: i16) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_i32(self, _: i32) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_i64(self, _: i64) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_u8(self, _: u8) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_u16(self, _: u16) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_u32(self, _: u32) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_u64(self, _: u64) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_f32(self, _: f32) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_f64(self, _: f64) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_char(self, _: char) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_none(self) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_some<T: ?Sized + Serialize>(self, _: &T) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_unit(self) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_unit_struct(self, _: &'static str) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_unit_variant(
            self,
            _: &'static str,
            _: u32,
            _: &'static str,
        ) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_newtype_struct<T: ?Sized + Serialize>(
            self,
            _: &'static str,
            _: &T,
        ) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_newtype_variant<T: ?Sized + Serialize>(
            self,
            _: &'static str,
            _: u32,
            _: &'static str,
            _: &T,
        ) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_seq(self, _: Option<usize>) -> Result<Self::SerializeSeq, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_tuple(self, _: usize) -> Result<Self::SerializeTuple, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_tuple_struct(
            self,
            _: &'static str,
            _: usize,
        ) -> Result<Self::SerializeTupleStruct, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_tuple_variant(
            self,
            _: &'static str,
            _: u32,
            _: &'static str,
            _: usize,
        ) -> Result<Self::SerializeTupleVariant, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_map(self, _: Option<usize>) -> Result<Self::SerializeMap, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_bytes(self, _: &[u8]) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_i128(self, _: i128) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_u128(self, _: u128) -> Result<String, Unsupported> {
            Err(Unsupported)
        }
        fn serialize_struct_variant(
            self,
            _: &'static str,
            _: u32,
            _: &'static str,
            _: usize,
        ) -> Result<Self::SerializeStructVariant, Unsupported> {
            Err(Unsupported)
        }
    }

    impl SerializeStruct for StructCapture {
        type Ok = String;
        type Error = Unsupported;
        fn serialize_field<T: ?Sized + Serialize>(
            &mut self,
            key: &'static str,
            value: &T,
        ) -> Result<(), Unsupported> {
            let value = value.serialize(&mut Wrap)?;
            if !self.rendered.is_empty() {
                self.rendered.push(';');
            }
            use std::fmt::Write as _;
            let _ = write!(self.rendered, "{key}={value}");
            Ok(())
        }
        fn end(self) -> Result<String, Unsupported> {
            Ok(self.rendered)
        }
    }

    fn render(value: &Intersection) -> String {
        value.serialize(&mut Wrap).unwrap()
    }

    // ------- A tiny map-backed Deserializer for the struct shape. ---------

    #[derive(Clone)]
    struct MapDe {
        entries: Vec<(&'static str, String)>,
        index: usize,
    }

    impl<'de> MapAccess<'de> for MapDe {
        type Error = de::value::Error;

        fn next_key_seed<K: DeserializeSeed<'de>>(
            &mut self,
            seed: K,
        ) -> Result<Option<K::Value>, Self::Error> {
            if self.index >= self.entries.len() {
                return Ok(None);
            }
            let key = self.entries[self.index].0;
            self.index += 1;
            seed.deserialize(de::value::StrDeserializer::new(key))
                .map(Some)
        }

        fn next_value_seed<V: DeserializeSeed<'de>>(
            &mut self,
            seed: V,
        ) -> Result<V::Value, Self::Error> {
            let value = &self.entries[self.index - 1].1;
            seed.deserialize(de::value::StringDeserializer::new(value.clone()))
        }
    }

    struct IntersectionDe(MapDe);

    impl<'de> Deserializer<'de> for IntersectionDe {
        type Error = de::value::Error;

        fn deserialize_any<V: Visitor<'de>>(self, _: V) -> Result<V::Value, Self::Error> {
            Err(de::Error::custom("intersection must be a map"))
        }

        fn deserialize_struct<V: Visitor<'de>>(
            self,
            _name: &'static str,
            _fields: &'static [&'static str],
            visitor: V,
        ) -> Result<V::Value, Self::Error> {
            visitor.visit_map(self.0)
        }

        serde::forward_to_deserialize_any! {
            bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string
            bytes byte_buf option unit unit_struct newtype_struct seq tuple
            tuple_struct map enum identifier ignored_any
        }
    }

    fn from_map(entries: Vec<(&'static str, String)>) -> Intersection {
        Intersection::deserialize(IntersectionDe(MapDe { entries, index: 0 })).unwrap()
    }

    #[test]
    fn serialize_forms() {
        let value = req(">=1.0.0, <2.0.0").intersection(&req("^1.5"));
        let rendered = render(&value);
        assert!(rendered.contains("outcome=witness"), "got {rendered}");
        assert!(rendered.contains("version=1.5.0"), "got {rendered}");

        let value = req(">=2.0.0").intersection(&req("<1.0.0"));
        let rendered = render(&value);
        assert!(rendered.contains("outcome=unsatisfiable"), "got {rendered}");
        assert!(
            rendered.contains("reason=disjoint-bounds"),
            "got {rendered}"
        );
        assert!(rendered.contains("first=>=2.0.0"), "got {rendered}");
        assert!(rendered.contains("second=<1.0.0"), "got {rendered}");
    }

    #[test]
    fn deserialize_witness() {
        let value = from_map(vec![
            ("outcome", "witness".to_owned()),
            ("version", "1.5.0".to_owned()),
        ]);
        if let Intersection::Witness(version) = value {
            assert_eq!(version.to_string(), "1.5.0");
        } else {
            panic!("expected witness");
        }
    }

    #[test]
    fn deserialize_unsatisfiable() {
        let value = from_map(vec![
            ("outcome", "unsatisfiable".to_owned()),
            ("reason", "disjoint-bounds".to_owned()),
            ("first", ">=2.0.0".to_owned()),
            ("second", "<1.0.0".to_owned()),
        ]);
        match value {
            Intersection::Unsatisfiable(ReqConflict {
                reason,
                first,
                second,
            }) => {
                assert_eq!(reason, ConflictReason::DisjointBounds);
                assert_eq!(first, ">=2.0.0");
                assert_eq!(second, "<1.0.0");
            }
            _ => panic!("expected unsatisfiable"),
        }
    }

    #[test]
    fn round_trip_preserves_value() {
        let original = req(">=1.0.0, <2.0.0").intersection(&req("^1.5"));
        let rendered = render(&original);
        let entries = rendered
            .split(';')
            .map(|pair| {
                let (key, value) = pair.split_once('=').unwrap();
                let static_key: &'static str = match key {
                    "outcome" => "outcome",
                    "version" => "version",
                    "reason" => "reason",
                    "first" => "first",
                    "second" => "second",
                    other => unreachable!("{other}"),
                };
                (static_key, value.to_owned())
            })
            .collect();
        let parsed = from_map(entries);
        assert_eq!(original, parsed);
    }
}
