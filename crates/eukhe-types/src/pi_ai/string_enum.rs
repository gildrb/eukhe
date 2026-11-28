//! `string_enum!`: TS string-literal unions as Rust enums with their exact
//! wire strings, `as_str`, `parse`, `ALL`, and `Display`.

/// Declare a TS string-literal union. Each variant maps to its wire string.
macro_rules! string_enum {
    (
        $(#[$meta:meta])*
        $vis:vis enum $name:ident {
            $($(#[$variant_meta:meta])* $variant:ident => $value:literal,)+
        }
    ) => {
        $(#[$meta])*
        #[derive(
            Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash,
            serde::Serialize, serde::Deserialize,
        )]
        $vis enum $name {
            $($(#[$variant_meta])* #[serde(rename = $value)] $variant,)+
        }

        impl $name {
            /// Every member, in declaration order.
            pub const ALL: &'static [Self] = &[$(Self::$variant),+];

            /// The wire string.
            #[must_use]
            pub const fn as_str(self) -> &'static str {
                match self {
                    $(Self::$variant => $value,)+
                }
            }

            /// The member whose wire string is `value`.
            #[must_use]
            pub fn parse(value: &str) -> Option<Self> {
                match value {
                    $($value => Some(Self::$variant),)+
                    _ => None,
                }
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str(self.as_str())
            }
        }
    };
}

pub(crate) use string_enum;

/// Declare a TS string union with an open end (`Known | (string & {})`):
/// named variants plus an `Other(String)` that keeps any other wire value
/// as written, so unknown values round-trip. Gives `as_str`, `parse`,
/// `Display`, and string `Serialize`/`Deserialize`.
macro_rules! open_string_enum {
    (
        $(#[$meta:meta])*
        $vis:vis enum $name:ident {
            $($(#[$variant_meta:meta])* $variant:ident => $value:literal,)+
        }
    ) => {
        $(#[$meta])*
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        $vis enum $name {
            $($(#[$variant_meta])* $variant,)+
            /// Any other wire value, kept as written.
            Other(String),
        }

        impl $name {
            /// The wire string.
            #[must_use]
            pub fn as_str(&self) -> &str {
                match self {
                    $(Self::$variant => $value,)+
                    Self::Other(value) => value,
                }
            }

            /// The member named by a wire string; unknown strings land in
            /// [`Self::Other`](enum@Self::Other).
            #[must_use]
            pub fn parse(value: &str) -> Self {
                match value {
                    $($value => Self::$variant,)+
                    other => Self::Other(other.to_owned()),
                }
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str(self.as_str())
            }
        }

        impl serde::Serialize for $name {
            fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                serializer.serialize_str(self.as_str())
            }
        }

        impl<'de> serde::Deserialize<'de> for $name {
            fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                Ok(Self::parse(&String::deserialize(deserializer)?))
            }
        }
    };
}

pub(crate) use open_string_enum;
