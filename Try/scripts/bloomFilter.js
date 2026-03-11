/**
 * bloom_filter.js — JavaScript port of bloom_filter.ml
 *
 * Faithful translation of the OCaml Bloom filter implementation.
 * Supports: create, createOptimal, add, mem, count, size, numHashes,
 * popcount, saturation, falsePositiveRate, isEmpty, union, ofList,
 * memAll, memAny, clear, copy, toString.
 *
 * Immutable — all mutation-like operations return new filter objects.
 */
'use strict';

/**
 * Simple string hash (djb2 variant).
 * @param {*} x - value to hash
 * @returns {number}
 */
function hash1(x) {
  const s = String(x);
  let h = 5381;
  for (let i = 0; i < s.length; i++) {
    h = ((h << 5) + h + s.charCodeAt(i)) | 0;
  }
  return h >>> 0;
}

/**
 * Second hash function (FNV-1a variant).
 * @param {*} x - value to hash
 * @returns {number}
 */
function hash2(x) {
  const s = String(x);
  let h = 2166136261;
  for (let i = 0; i < s.length; i++) {
    h ^= s.charCodeAt(i);
    h = Math.imul(h, 16777619) >>> 0;
  }
  return h >>> 0;
}

/**
 * Double hashing: h_i(x) = (h1(x) + i * h2(x)) mod m
 */
function hashI(m, h1, h2, i) {
  return ((h1 + i * h2) % m + m) % m;
}

/**
 * Get bit at position i in Uint8Array.
 */
function getBit(bits, i) {
  const byteIdx = Math.floor(i / 8);
  const bitIdx = i % 8;
  return (bits[byteIdx] & (1 << bitIdx)) !== 0;
}

/**
 * Set bit at position i in Uint8Array (mutates the array).
 */
function setBit(bits, i) {
  const byteIdx = Math.floor(i / 8);
  const bitIdx = i % 8;
  bits[byteIdx] = bits[byteIdx] | (1 << bitIdx);
}

/**
 * Create an empty Bloom filter.
 * @param {object} [opts]
 * @param {number} [opts.m=1024] - number of bits
 * @param {number} [opts.k=7]   - number of hash functions
 * @returns {object} Bloom filter
 */
function create({ m = 1024, k = 7 } = {}) {
  m = Math.max(8, m);
  k = Math.max(1, k);
  const byteCount = Math.ceil(m / 8);
  return Object.freeze({
    bits: new Uint8Array(byteCount),
    m,
    k,
    n: 0,
  });
}

/**
 * Create a Bloom filter sized for expected element count and
 * desired false-positive probability.
 * @param {number} expectedElements
 * @param {number} fpRate - desired false positive rate (0 < fpRate < 1)
 * @returns {object} Bloom filter
 */
function createOptimal(expectedElements, fpRate) {
  const nf = Math.max(1, expectedElements);
  const p = Math.max(0.0001, Math.min(0.5, fpRate));
  const mf = -(nf * Math.log(p)) / (Math.log(2) ** 2);
  const m = Math.max(8, Math.ceil(mf));
  const kf = (m / nf) * Math.log(2);
  const k = Math.max(1, Math.round(kf));
  return create({ m, k });
}

/**
 * Add an element to the filter. Returns a new filter.
 */
function add(x, bf) {
  const newBits = new Uint8Array(bf.bits);
  const h1v = hash1(x);
  const h2v = hash2(x);
  for (let i = 0; i < bf.k; i++) {
    const idx = hashI(bf.m, h1v, h2v, i);
    setBit(newBits, idx);
  }
  return Object.freeze({ bits: newBits, m: bf.m, k: bf.k, n: bf.n + 1 });
}

/**
 * Test if an element might be in the set.
 * Returns true if possibly present, false if definitely absent.
 */
function mem(x, bf) {
  const h1v = hash1(x);
  const h2v = hash2(x);
  for (let i = 0; i < bf.k; i++) {
    const idx = hashI(bf.m, h1v, h2v, i);
    if (!getBit(bf.bits, idx)) return false;
  }
  return true;
}

function count(bf) { return bf.n; }
function size(bf) { return bf.m; }
function numHashes(bf) { return bf.k; }

/**
 * Count of set bits (Kernighan's trick).
 */
function popcount(bf) {
  const byteCount = Math.ceil(bf.m / 8);
  let c = 0;
  for (let i = 0; i < byteCount; i++) {
    let b = bf.bits[i];
    while (b !== 0) {
      b = b & (b - 1);
      c++;
    }
  }
  const padding = byteCount * 8 - bf.m;
  if (padding > 0) {
    const lastByte = bf.bits[byteCount - 1];
    const validMask = (1 << (8 - padding)) - 1;
    let paddingBits = lastByte & ~validMask;
    while (paddingBits !== 0) {
      paddingBits = paddingBits & (paddingBits - 1);
      c--;
    }
  }
  return c;
}

function saturation(bf) {
  return popcount(bf) / bf.m;
}

function falsePositiveRate(bf) {
  if (bf.n === 0) return 0.0;
  return Math.pow(1.0 - Math.exp((-bf.k * bf.n) / bf.m), bf.k);
}

function isEmpty(bf) { return bf.n === 0; }

function union(bf1, bf2) {
  if (bf1.m !== bf2.m || bf1.k !== bf2.k) {
    throw new Error('BloomFilter.union: incompatible filters');
  }
  const byteCount = Math.ceil(bf1.m / 8);
  const newBits = new Uint8Array(byteCount);
  for (let i = 0; i < byteCount; i++) {
    newBits[i] = bf1.bits[i] | bf2.bits[i];
  }
  return Object.freeze({ bits: newBits, m: bf1.m, k: bf1.k, n: bf1.n + bf2.n });
}

function ofList(list, opts = {}) {
  return list.reduce((bf, x) => add(x, bf), create(opts));
}

function memAll(list, bf) {
  return list.every(x => mem(x, bf));
}

function memAny(list, bf) {
  return list.some(x => mem(x, bf));
}

function clear(bf) {
  return create({ m: bf.m, k: bf.k });
}

function copy(bf) {
  return Object.freeze({
    bits: new Uint8Array(bf.bits),
    m: bf.m,
    k: bf.k,
    n: bf.n,
  });
}

function toString(bf) {
  return `BloomFilter(m=${bf.m}, k=${bf.k}, n=${bf.n}, saturation=${(saturation(bf) * 100).toFixed(2)}%)`;
}

module.exports = {
  create, createOptimal, add, mem, count, size, numHashes,
  popcount, saturation, falsePositiveRate, isEmpty, union,
  ofList, memAll, memAny, clear, copy, toString,
  _hash1: hash1, _hash2: hash2, _hashI: hashI,
  _getBit: getBit, _setBit: setBit,
};
