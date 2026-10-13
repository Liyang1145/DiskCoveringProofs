// d3_ints_audit.mjs  (member upper-audit, 2026-09-26)
//
// AUDIT OF THE D3 COORDINATE OBJECT.
// The published D3 driver js/scale/enc17.mjs does
//        const C = j[key].map(p => [Number(p[0]), Number(p[1])]);
//        m.encloseHigh(C, 17, 30)
// and encloseHigh -> certifiedInts() uses x.toFixed(17) as THE certified object.
// Its own diagnostic (countLiteralDifferences) compares toFixed(17)(double) against the
// SHORTEST round-trip repr of the SAME double -- it never looks at the JSON characters.
// This script compares, coordinate by coordinate, the certified integers against the
// integers read directly out of the cfg/cert_n12_othern.json strings, and additionally
// runs the engine on the literal integers themselves (encloseScaledInts) to see whether
// the two candidate objects give the same enclosure.
//
// run (from workspace root):
//   node research-2026/n12-global/members/upper-audit/js/d3_ints_audit.mjs [cfgPath]

import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

const m = await import(new URL('../../../../../n11/upper/enclose17.mjs', import.meta.url).href);

const cfgPath = process.argv[2]
  || fileURLToPath(new URL('../../../../session2/n1314/cfg/cert_n12_othern.json', import.meta.url));
const j = JSON.parse(readFileSync(cfgPath, 'utf8'));
const key = j.centers_dec17 ? 'centers_dec17' : 'centers';
const literals = j[key];
const DEC = 17;
const S = 10n ** BigInt(DEC);

function literalInt(s) {                      // exact BigInt of a "d.ddd" literal
  const neg = s.startsWith('-');
  const t = (neg ? s.slice(1) : s);
  const [ip, fp = ''] = t.split('.');
  if (fp.length !== DEC) throw new Error('literal does not carry exactly ' + DEC + ' decimals: ' + s);
  const v = BigInt(ip) * S + BigInt(fp);
  return neg ? -v : v;
}

const C = literals.map(p => [Number(p[0]), Number(p[1])]);
const cert = m.certifiedInts(C, DEC);          // = toFixed(17) integers  (the object D3 certifies)
const lit = m.literalInts(C, DEC);             // = shortest-repr integers (rounded to 17)
const raw = literals.map(p => [literalInt(p[0]), literalInt(p[1])]);   // exact JSON-literal integers

let diffCertVsJson = 0, diffCertVsShortest = 0, diffShortestVsJson = 0, roundedCount = lit.rounded;
const rows = [];
for (let i = 0; i < literals.length; i++) {
  for (let k = 0; k < 2; k++) {
    const jsonI = raw[i][k], certI = cert[i][k], litI = lit[i][k];
    const shortest = String(C[i][k]);
    const jsonStr = literals[i][k];
    const certStr = m.intsToStrings([[certI, certI]], DEC)[0][k];
    const dCert = jsonI - certI;                       // exact integer difference (units 1e-17)
    if (dCert !== 0n) diffCertVsJson++;
    if (certI !== litI) diffCertVsShortest++;
    if (litI !== jsonI) diffShortestVsJson++;
    rows.push({ i, k, jsonStr, shortest, certStr, dCert: dCert.toString(), shortestEqJson: shortest === jsonStr });
  }
}
console.log('cfg            =', cfgPath);
console.log('key            =', key, ' n =', literals.length, ' decimals =', DEC);
console.log('literalInts counted "rounded" (shortest repr longer than 17 decimals) =', roundedCount);
console.log('coordinate-wise differences over ' + (2 * literals.length) + ' coordinates:');
console.log('   certified(toFixed(17)) vs JSON literal        :', diffCertVsJson);
console.log('   certified(toFixed(17)) vs shortest-repr ints  :', diffCertVsShortest, '  (= the engine self-diagnostic number)');
console.log('   shortest-repr ints vs JSON literal ints       :', diffShortestVsJson);
const shift = rows.filter(r => r.dCert !== '0').map(r => `${r.i},${r.k}`);
console.log('   coordinates with certified != JSON-literal     :', shift.length ? shift.join(' ') : '(none)');
console.log('   distinct |difference| in units of 1e-17       :',
  [...new Set(rows.map(r => r.dCert).filter(d => d !== '0').map(d => d.replace('-', '')))].join(' ') || '(none)');
console.log('   coordinates whose shortest repr differs from the JSON string:',
  rows.filter(r => !r.shortestEqJson).map(r => `${r.i},${r.k}`).join(' ') || '(none)');
console.log('per-coordinate table (json string | shortest repr | toFixed(17) | jsonInt-certInt):');
for (const r of rows) console.log(`   [${r.i},${r.k}]  ${r.jsonStr.padEnd(21)} | ${r.shortest.padEnd(21)} | ${r.certStr.padEnd(21)} | ${r.dCert}`);

// ---- two-object enclosure comparison -------------------------------------------------
const digits = 30;
const asRun = m.encloseHigh(C, DEC, digits);                  // what enc17.mjs prints (double pipeline)
const literalA = m.encloseScaledInts(raw, DEC, Math.max(30, 2 * DEC + 6), digits);
const literalB = m.encloseScaledInts(raw, DEC, Math.max(36, 2 * DEC + 12), digits);
const literalX = (literalA.lo > literalB.lo ? literalA.lo : literalB.lo) <= (literalA.hi < literalB.hi ? literalA.hi : literalB.hi)
  ? { lo: (literalA.lo > literalB.lo ? literalA.lo : literalB.lo), hi: (literalA.hi < literalB.hi ? literalA.hi : literalB.hi) }
  : null;
console.log('\n== enclosures (outDigits = ' + digits + ') ==');
console.log('   as-run  encloseHigh(Number-converted)  [lo,hi] =', asRun.lo, asRun.hi,
  ' cross_consistent =', asRun.cross_consistent, ' valid =', asRun.valid,
  ' candidates =', asRun.a.candidates, ' included =', asRun.a.included, ' argmax =', asRun.a.hiArgKind);
console.log('   same engine on RAW JSON literal integers  [lo,hi] =',
  literalX ? literalX.lo + ' ' + literalX.hi : '(no cross-consistent intersection)',
  ' cross_consistent =', literalA.lo === literalB.lo && literalA.hi === literalB.hi,
  ' candidates =', literalA.candidates, ' included =', literalA.included, ' argmax =', literalA.hiArgKind);
console.log('   intervals identical ? ', asRun.lo === (literalX && literalX.lo) && asRun.hi === (literalX && literalX.hi));
console.log('   historic out/cert_n12_othern.json records d2_lo,d2_hi = 0.361102963744508672616920293903 0.361102963744508672616920293904');
