// Fixed-scale BigInt intervals, adapted from the local n=26 area certificate.
"use strict";

const S = 10n ** 24n;
const floor = (a, b) => a / b - (a % b < 0n ? 1n : 0n);
const ceil = (a, b) => -floor(-a, b);
const min = values => values.reduce((a, b) => a < b ? a : b);
const max = values => values.reduce((a, b) => a > b ? a : b);
const Q = (a, b = 1) => [floor(BigInt(a) * S, BigInt(b)), ceil(BigInt(a) * S, BigInt(b))];
const add = ([a, b], [c, d]) => [a + c, b + d];
const sub = ([a, b], [c, d]) => [a - d, b - c];
const mul = ([a, b], [c, d]) => {
  const p = [a * c, a * d, b * c, b * d];
  return [floor(min(p), S), ceil(max(p), S)];
};
const check = (p, message) => { if (!p) throw new Error(message); };
const div = ([a, b], [c, d]) => {
  check(c > 0n, "nonpositive interval divisor");
  return [min([floor(a * S, c), floor(a * S, d)]), max([ceil(b * S, c), ceil(b * S, d)])];
};
const sq = a => mul(a, a);
const gt = (a, b) => a[0] > b[1];

function isqrt(n) {
  check(n >= 0n, "negative radicand");
  if (n < 2n) return n;
  let x = n;
  let y = (x + 1n) / 2n;
  while (y < x) {
    x = y;
    y = (x + n / x) / 2n;
  }
  return x;
}

const sqrt = ([a, b]) => [isqrt(a * S), isqrt(b * S) + 1n];

function series(x, kind) {
  const limit = kind === "atan" ? S : 4n * S;
  check(x[0] >= 0n && x[1] <= limit, "Taylor argument out of range");
  let term = kind === "cos" ? Q(1) : x;
  let sum = term;
  for (let j = 1; j <= 12; j++) {
    const k = kind === "cos" ? 2 * j : 2 * j + 1;
    term = kind === "atan" ? div(mul(term, mul(sq(x), Q(k - 2))), Q(k))
                          : div(mul(term, sq(x)), Q(k * (k - 1)));
    const previous = sum;
    sum = j % 2 ? sub(sum, term) : add(sum, term);
    // The remainder terms after both partial sums decrease in magnitude.
    if (j === 12) return [previous[0], sum[1]];
  }
}

const sin = x => series(x, "sin");
const cos = x => series(x, "cos");
const pi = sub(mul(Q(16), series(Q(1, 5), "atan")), mul(Q(4), series(Q(1, 239), "atan")));

module.exports = {S, floor, min, max, Q, add, sub, mul, div, sq, sqrt, check, gt, sin, cos, pi};
