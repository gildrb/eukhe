//! The golden tasks: each asks for one file, gets three context messages,
//! a redirect, a status question and an unrelated request while its first
//! (long) tool call runs, and is scored by the file the work leaves
//! behind plus the unrelated request's answer.

/// One golden task.
pub struct Task {
    pub id: &'static str,
    /// The work order.
    pub prompt: &'static str,
    /// Three context messages for the running work (fold in, keep course).
    pub contexts: [&'static str; 3],
    /// A change of course.
    pub redirect: &'static str,
    /// The unrelated request and a substring its answer must hold.
    pub unrelated: (&'static str, &'static str),
    /// The file the finished work leaves and the substrings it must hold
    /// (the rubric).
    pub file: &'static str,
    pub must_hold: &'static [&'static str],
    /// The file the scripted (faux) worker writes: the rubric's answer.
    pub scripted_content: &'static str,
}

/// The status question every task gets.
pub const STATUS: &str = "How far along are you?";

/// The long tool call every task starts with (a real model is asked to run
/// it; the faux model runs it): the window the mid-task messages land in.
pub const BUILD_SECONDS: u64 = 8;

pub const TASKS: [Task; 10] = [
    Task {
        id: "T01-chores",
        prompt: "Create todo.md listing three chores for the weekend, one per line starting with '- '.",
        contexts: [
            "one chore is 'water the plants'",
            "another is 'fix the bike'",
            "the third is 'call grandma'",
        ],
        redirect: "actually, name the file weekend.md instead of todo.md",
        unrelated: ("Unrelated: what is 17 * 23?", "391"),
        file: "weekend.md",
        must_hold: &["water the plants", "fix the bike", "call grandma"],
        scripted_content: "- water the plants\n- fix the bike\n- call grandma\n",
    },
    Task {
        id: "T02-config",
        prompt: "Write app.toml with a [server] section.",
        contexts: [
            "the port is 8080",
            "the host is 0.0.0.0",
            "add log_level = \"info\"",
        ],
        redirect: "change of plan: use port 9090 instead of 8080",
        unrelated: ("Unrelated: what is 12 * 12?", "144"),
        file: "app.toml",
        must_hold: &["[server]", "9090", "0.0.0.0", "info"],
        scripted_content: "[server]\nhost = \"0.0.0.0\"\nport = 9090\nlog_level = \"info\"\n",
    },
    Task {
        id: "T03-csv",
        prompt: "Write people.csv with the header name,age.",
        contexts: ["add Ana, 31", "add Bo, 27", "add Cy, 45"],
        redirect: "actually, sort the rows by age, youngest first",
        unrelated: ("Unrelated: what is 9 * 11?", "99"),
        file: "people.csv",
        must_hold: &["name,age", "Bo,27", "Ana,31", "Cy,45"],
        scripted_content: "name,age\nBo,27\nAna,31\nCy,45\n",
    },
    Task {
        id: "T04-readme",
        prompt: "Write README.md for a command-line tool called zap.",
        contexts: [
            "zap compresses log files",
            "it needs Python 3.11",
            "the license is MIT",
        ],
        redirect: "rename the tool: call it zapr, not zap",
        unrelated: ("Unrelated: what is 25 * 4?", "100"),
        file: "README.md",
        must_hold: &["zapr", "compresses log files", "3.11", "MIT"],
        scripted_content: "# zapr\n\nzapr compresses log files.\n\nRequires Python 3.11. License: MIT.\n",
    },
    Task {
        id: "T05-json",
        prompt: "Write settings.json with a theme key.",
        contexts: ["the theme is dark", "fontSize is 14", "add tabs: false"],
        redirect: "make the theme light, not dark",
        unrelated: ("Unrelated: what is 13 * 7?", "91"),
        file: "settings.json",
        must_hold: &["light", "14", "false"],
        scripted_content: "{\"theme\": \"light\", \"fontSize\": 14, \"tabs\": false}\n",
    },
    Task {
        id: "T06-list",
        prompt: "Write list.txt, a shopping list, one item per line.",
        contexts: ["eggs", "milk", "bread"],
        redirect: "also start the file with a title line 'Groceries'",
        unrelated: ("Unrelated: what is 8 * 8?", "64"),
        file: "list.txt",
        must_hold: &["Groceries", "eggs", "milk", "bread"],
        scripted_content: "Groceries\neggs\nmilk\nbread\n",
    },
    Task {
        id: "T07-env",
        prompt: "Write .env.example listing the environment keys of a web app, KEY= per line.",
        contexts: ["it needs DATABASE_URL", "and REDIS_URL", "and SECRET_KEY"],
        redirect: "prefix every key with APP_",
        unrelated: ("Unrelated: what is 21 * 3?", "63"),
        file: ".env.example",
        must_hold: &["APP_DATABASE_URL", "APP_REDIS_URL", "APP_SECRET_KEY"],
        scripted_content: "APP_DATABASE_URL=\nAPP_REDIS_URL=\nAPP_SECRET_KEY=\n",
    },
    Task {
        id: "T08-changelog",
        prompt: "Write CHANGELOG.md for version 1.2.0.",
        contexts: [
            "added: dark mode",
            "fixed: a login crash",
            "changed: faster search",
        ],
        redirect: "the version is 1.3.0, not 1.2.0",
        unrelated: ("Unrelated: what is 15 * 15?", "225"),
        file: "CHANGELOG.md",
        must_hold: &["1.3.0", "dark mode", "login crash", "faster search"],
        scripted_content: "# 1.3.0\n\n- Added: dark mode\n- Fixed: a login crash\n- Changed: faster search\n",
    },
    Task {
        id: "T09-schema",
        prompt: "Write schema.sql creating a users table.",
        contexts: [
            "id is an integer primary key",
            "email is text and unique",
            "add created_at as a timestamp",
        ],
        redirect: "name the table accounts instead of users",
        unrelated: ("Unrelated: what is 19 * 2?", "38"),
        file: "schema.sql",
        must_hold: &["accounts", "email", "created_at"],
        scripted_content: "CREATE TABLE accounts (\n  id INTEGER PRIMARY KEY,\n  email TEXT UNIQUE,\n  created_at TIMESTAMP\n);\n",
    },
    Task {
        id: "T10-hosts",
        prompt: "Write hosts.txt listing the team's servers, one hostname per line.",
        contexts: ["web-1 is one", "db-1 is another", "cache-1 is the third"],
        redirect: "use the domain suffix .lan on every hostname",
        unrelated: ("Unrelated: what is 6 * 7?", "42"),
        file: "hosts.txt",
        must_hold: &["web-1.lan", "db-1.lan", "cache-1.lan"],
        scripted_content: "web-1.lan\ndb-1.lan\ncache-1.lan\n",
    },
];
