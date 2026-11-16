//! The parse benchmark in Rust, through `serde_json::Value`.

use std::io::Read;

use serde_json::Value;

fn tally(value: &Value, sums: &mut (u64, i128, usize)) {
    sums.0 += 1;
    match value {
        Value::Number(number) => {
            if let Some(n) = number.as_i64() {
                sums.1 += i128::from(n);
            } else if let Some(n) = number.as_u64() {
                sums.1 += i128::from(n);
            }
        }
        Value::String(text) => sums.2 += text.len(),
        Value::Array(values) => values.iter().for_each(|element| tally(element, sums)),
        Value::Object(members) => {
            for (name, member) in members {
                sums.2 += name.len();
                tally(member, sums);
            }
        }
        Value::Null | Value::Bool(_) => {}
    }
}

fn main() {
    let mut text = String::new();
    std::io::stdin().read_to_string(&mut text).expect("standard input is UTF-8");
    let value: Value = serde_json::from_str(&text).expect("standard input is JSON");
    let mut sums = (0, 0, 0);
    tally(&value, &mut sums);
    println!("values {} ints {} strings {}", sums.0, sums.1, sums.2);
}
