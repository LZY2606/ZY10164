use core::fmt;
use serde::de::{Deserialize, Deserializer, Error, Visitor};

use serde::ser::{Serialize, Serializer};

impl Serialize for Version {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.collect_str(self)
    }
}

impl Serialize for VersionReq {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.collect_str(self)
    }
}

impl Serialize for Comparator {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.collect_str(self)
    }
}

impl<'de> Deserialize<'de> for Version {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct VersionVisitor;

        impl<'de> Visitor<'de> for VersionVisitor {
            type Value = Version;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("semver version")
            }

            fn visit_str<E>(self, string: &str) -> Result<Self::Value, E>
            where
                E: Error,
            {
                string.parse().map_err(Error::custom)
            }
        }

        deserializer.deserialize_str(VersionVisitor)
    }
}

impl<'de> Deserialize<'de> for VersionReq {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct VersionReqVisitor;

        impl<'de> Visitor<'de> for VersionReqVisitor {
            type Value = VersionReq;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("semver version")
            }

            fn visit_str<E>(self, string: &str) -> Result<Self::Value, E>
            where
                E: Error,
            {
                string.parse().map_err(Error::custom)
            }
        }

        deserializer.deserialize_str(VersionReqVisitor)
    }
}

impl<'de> Deserialize<'de> for Comparator {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ComparatorVisitor;

        impl<'de> Visitor<'de> for ComparatorVisitor {
            type Value = Comparator;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("semver comparator")
            }

            fn visit_str<E>(self, string: &str) -> Result<Self::Value, E>
            where
                E: Error,
            {
                string.parse().map_err(Error::custom)
            }
        }

        deserializer.deserialize_str(ComparatorVisitor)
    }
}

use crate::satisfy::{Conflict, ConflictReason, Intersection};
use crate::{Comparator, Version, VersionReq};
use alloc::string::String;
use serde::de::{self, MapAccess};

impl Serialize for Intersection {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            Intersection::Witness(version) => {
                use serde::ser::SerializeStruct;
                let mut state = serializer.serialize_struct("Intersection", 2)?;
                state.serialize_field("outcome", "witness")?;
                state.serialize_field("version", version)?;
                state.end()
            }
            Intersection::Unsatisfiable(conflict) => {
                use serde::ser::SerializeStruct;
                let mut state = serializer.serialize_struct("Intersection", 4)?;
                state.serialize_field("outcome", "unsatisfiable")?;
                state.serialize_field("reason", &conflict.reason)?;
                state.serialize_field("first", &conflict.first)?;
                state.serialize_field("second", &conflict.second)?;
                state.end()
            }
        }
    }
}

impl Serialize for ConflictReason {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let tag = match self {
            ConflictReason::DisjointBounds => "disjoint-bounds",
            ConflictReason::VersionSpaceExhausted => "version-space-exhausted",
        };
        serializer.serialize_str(tag)
    }
}

impl Serialize for Conflict {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        use serde::ser::SerializeStruct;
        let mut state = serializer.serialize_struct("Conflict", 3)?;
        state.serialize_field("reason", &self.reason)?;
        state.serialize_field("first", &self.first)?;
        state.serialize_field("second", &self.second)?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for Intersection {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        enum Field {
            Outcome,
            Version,
            Reason,
            First,
            Second,
        }

        impl<'de> Deserialize<'de> for Field {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                struct FieldVisitor;

                impl<'de> Visitor<'de> for FieldVisitor {
                    type Value = Field;

                    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                        formatter.write_str("an intersection field name")
                    }

                    fn visit_str<E>(self, value: &str) -> Result<Field, E>
                    where
                        E: Error,
                    {
                        match value {
                            "outcome" => Ok(Field::Outcome),
                            "version" => Ok(Field::Version),
                            "reason" => Ok(Field::Reason),
                            "first" => Ok(Field::First),
                            "second" => Ok(Field::Second),
                            _ => Err(Error::unknown_field(value, FIELDS)),
                        }
                    }
                }

                deserializer.deserialize_identifier(FieldVisitor)
            }
        }

        const FIELDS: &[&str] = &["outcome", "version", "reason", "first", "second"];

        struct IntersectionVisitor;

        impl<'de> Visitor<'de> for IntersectionVisitor {
            type Value = Intersection;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a semver intersection")
            }

            fn visit_map<M>(self, mut map: M) -> Result<Self::Value, M::Error>
            where
                M: MapAccess<'de>,
            {
                let mut outcome: Option<String> = None;
                let mut version: Option<String> = None;
                let mut reason: Option<String> = None;
                let mut first: Option<String> = None;
                let mut second: Option<String> = None;

                while let Some(field) = map.next_key()? {
                    match field {
                        Field::Outcome => outcome = Some(map.next_value()?),
                        Field::Version => version = Some(map.next_value()?),
                        Field::Reason => reason = Some(map.next_value()?),
                        Field::First => first = Some(map.next_value()?),
                        Field::Second => second = Some(map.next_value()?),
                    }
                }

                match outcome.as_deref() {
                    Some("witness") => {
                        let text = version.ok_or_else(|| de::Error::missing_field("version"))?;
                        let parsed = text.parse::<crate::Version>().map_err(de::Error::custom)?;
                        Ok(Intersection::Witness(parsed))
                    }
                    Some("unsatisfiable") => {
                        let reason_tag = reason
                            .as_deref()
                            .ok_or_else(|| de::Error::missing_field("reason"))?;
                        let conflict_reason = match reason_tag {
                            "disjoint-bounds" => ConflictReason::DisjointBounds,
                            "version-space-exhausted" => ConflictReason::VersionSpaceExhausted,
                            other => {
                                return Err(de::Error::unknown_variant(
                                    other,
                                    &["witness", "unsatisfiable"],
                                ))
                            }
                        };
                        Ok(Intersection::Unsatisfiable(Conflict {
                            reason: conflict_reason,
                            first: first.ok_or_else(|| de::Error::missing_field("first"))?,
                            second: second.ok_or_else(|| de::Error::missing_field("second"))?,
                        }))
                    }
                    other => Err(de::Error::unknown_variant(
                        other.unwrap_or("<missing>"),
                        &["witness", "unsatisfiable"],
                    )),
                }
            }
        }

        deserializer.deserialize_struct(
            "Intersection",
            &["outcome", "version", "reason", "first", "second"],
            IntersectionVisitor,
        )
    }
}
