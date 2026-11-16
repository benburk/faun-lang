//! The decode benchmark in Rust: users read into structs by serde's derive,
//! refusing unknown fields as the Faun decoder does, and written back.

use std::io::Read;

use serde::{Deserialize, Serialize};

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Address {
    city: String,
    zip: String,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct User {
    id: u64,
    name: String,
    email: String,
    active: bool,
    score: f64,
    tags: Vec<String>,
    address: Address,
    friends: Vec<u64>,
    note: Option<String>,
}

fn main() {
    let mut text = String::new();
    std::io::stdin().read_to_string(&mut text).expect("standard input is UTF-8");
    let users: Vec<User> = serde_json::from_str(&text).expect("standard input holds users");
    let written = serde_json::to_string(&users).expect("users are written");
    let active = users.iter().filter(|user| user.active).count();
    let tags: usize = users.iter().map(|user| user.tags.len()).sum();
    println!("users {} active {active} tags {tags} bytes {}", users.len(), written.len());
}
