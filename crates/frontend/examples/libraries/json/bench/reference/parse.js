// The parse benchmark in JavaScript, integers summed exactly as BigInt.
const text = require("fs").readFileSync(0, "utf8");
let values = 0, ints = 0n, strings = 0;
function tally(value) {
  values += 1;
  if (typeof value === "number") {
    if (Number.isInteger(value)) ints += BigInt(value);
  } else if (typeof value === "string") {
    strings += Buffer.byteLength(value);
  } else if (Array.isArray(value)) {
    for (const element of value) tally(element);
  } else if (value !== null && typeof value === "object") {
    for (const [name, member] of Object.entries(value)) {
      strings += Buffer.byteLength(name);
      tally(member);
    }
  }
}
tally(JSON.parse(text));
console.log(`values ${values} ints ${ints} strings ${strings}`);
