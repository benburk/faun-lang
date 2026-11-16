// The decode benchmark in JavaScript: users read into classes, and written back.
class Address {
  constructor(r) { this.city = r.city; this.zip = r.zip; }
}
class User {
  constructor(r) {
    this.id = r.id; this.name = r.name; this.email = r.email; this.active = r.active;
    this.score = r.score; this.tags = r.tags; this.address = new Address(r.address);
    this.friends = r.friends; this.note = r.note;
  }
}
const users = JSON.parse(require("fs").readFileSync(0, "utf8")).map((r) => new User(r));
const text = JSON.stringify(users);
const active = users.filter((u) => u.active).length;
const tags = users.reduce((sum, u) => sum + u.tags.length, 0);
console.log(`users ${users.length} active ${active} tags ${tags} bytes ${Buffer.byteLength(text)}`);
