//! The bridge between the environment of a child ([`super::child_env`],
//! with `eukhe_ai`'s credential test) and its Bend model
//! (`bend/child_env.bend`; the laws (G3) in `laws/child_env.bend`): both
//! run the same scenarios and must print the same transcript, byte for
//! byte.
//!
//! A scenario is the registry (every provider credential name), a keep
//! list, a base and an overlay drawn from a pool of names (provider names,
//! names a secret pattern matches, names that hold no secret, in mixed
//! case), and the names to look up (`bend/bridge_child_env.bend` documents
//! the format).

use std::collections::{BTreeSet, HashMap};
use std::fmt::Write as _;

use eukhe_ai::env_api_keys::{
    credential_env_vars, is_credential_env_var, is_provider_credential_env_var,
};
use eukhe_durable::testing::bridge::{compare, Rng, Scenario};

use super::child_env;
use crate::kernel::shared::KeptCredentials;

/// The names of the scenarios, besides a few drawn from the registry.
const POOL: &[&str] = &[
    "PATH",
    "HOME",
    "LANG",
    "SSH_AUTH_SOCK",
    "XAUTHORITY",
    "SSH_ASKPASS",
    "KEYTIMEOUT",
    "AWS_REGION",
    "AWS_PROFILE",
    "PRIME_TEAM_ID",
    "PASS",
    "TOKE",
    "APIKE",
    "TOKENIZERS_PARALLELISM",
    "OPENAI_API_KEY",
    "openai_api_key",
    "Hf_Token",
    "aws_secret_access_key",
    "GOOGLE_APPLICATION_CREDENTIALS",
    "GITHUB_TOKEN",
    "github_token",
    "SLACK_BOT_TOKEN",
    "MY_APIKEY",
    "Db_Password",
    "DB_PASSWD",
    "GPG_PASSPHRASE",
    "client_secret",
    "TLS_PRIVATE_KEY",
    "S3_ACCESS_KEY",
    "SERVICE_CREDENTIAL",
];

/// A case the scenarios must reach, so that the bridge checks every rule
/// of the model.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Case {
    /// A name that is no credential reaches the child.
    Plain,
    /// A credential name the keep list does not hold is stripped.
    Stripped,
    /// A credential name the keep list holds reaches the child.
    Kept,
    /// A provider name the keep list holds is stripped.
    ProviderKept,
    /// The overlay hides a variable of the base.
    Overlaid,
}

/// One scenario: its events and the Rust transcript.
fn scenario(rng: &mut Rng, registry: &[&str], reached: &mut BTreeSet<Case>) -> (String, String) {
    let mut pool: Vec<&str> = POOL.to_vec();
    for _ in 0..4 {
        let name = rng.pick(registry).unwrap();
        if !pool.contains(&name) {
            pool.push(name);
        }
    }
    let mut events = format!("r {}\nk", registry.join(" "));
    let mut kept = Vec::new();
    for name in &pool {
        if rng.chance(30) {
            write!(events, " {name}").unwrap();
            kept.push((*name).to_owned());
        }
    }
    events.push('\n');
    let mut base = Vec::new();
    let mut overlay = HashMap::new();
    for (at, name) in pool.iter().enumerate() {
        if rng.chance(60) {
            writeln!(events, "b {name} b{at}").unwrap();
            base.push(((*name).to_owned(), format!("b{at}")));
        }
        if rng.chance(30) {
            overlay.insert((*name).to_owned(), format!("o{at}"));
        }
    }
    let mut overlaid: Vec<(&String, &String)> = overlay.iter().collect();
    overlaid.sort();
    for (name, value) in overlaid {
        writeln!(events, "o {name} {value}").unwrap();
    }
    for name in &pool {
        writeln!(events, "q {name}").unwrap();
    }
    let keep = KeptCredentials::new(kept.iter().cloned());
    let env = child_env(base.iter().cloned(), &overlay, &keep);
    let mut transcript = String::new();
    for name in &pool {
        let credential = is_credential_env_var(name);
        let provider = is_provider_credential_env_var(name);
        let value = env
            .get(*name)
            .map_or_else(|| "-".to_owned(), |value| format!("={value}"));
        writeln!(
            transcript,
            "p {name} {} {} {value}",
            u8::from(credential),
            u8::from(provider)
        )
        .unwrap();
        let in_base = base.iter().any(|(base_name, _)| base_name == name);
        let listed = kept.iter().any(|kept_name| kept_name == name);
        if in_base || overlay.contains_key(*name) {
            reached.insert(match (credential, listed, provider) {
                (false, _, _) => Case::Plain,
                (true, false, _) => Case::Stripped,
                (true, true, false) => Case::Kept,
                (true, true, true) => Case::ProviderKept,
            });
        }
        if in_base && overlay.contains_key(*name) && !credential {
            reached.insert(Case::Overlaid);
        }
    }
    writeln!(transcript, "n {}", env.len()).unwrap();
    (events, transcript)
}

#[test]
fn the_rust_child_env_equals_the_bend_model() {
    let registry: Vec<&str> = credential_env_vars().collect();
    let mut rng = Rng(0x5eed_c4ed_e4b0_0001);
    let mut reached = BTreeSet::new();
    let scenarios: Vec<Scenario> = (0..120)
        .map(|at| {
            let (events, transcript) = scenario(&mut rng, &registry, &mut reached);
            Scenario {
                name: format!("child env {at}"),
                events,
                transcript,
            }
        })
        .collect();
    compare("bend/bridge_child_env.bend", scenarios);
    // The scenarios reach every rule of the model.
    assert_eq!(
        reached,
        BTreeSet::from([
            Case::Plain,
            Case::Stripped,
            Case::Kept,
            Case::ProviderKept,
            Case::Overlaid,
        ])
    );
}
