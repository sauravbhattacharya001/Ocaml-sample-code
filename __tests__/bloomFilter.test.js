/**
 * @jest-environment node
 *
 * Tests for bloomFilter.js — JS port of bloom_filter.ml
 *
 * Covers: creation, add/mem, false-positive guarantees, popcount,
 * saturation, false-positive rate, union, ofList, memAll/memAny,
 * clear/copy, createOptimal, immutability, edge cases, statistics.
 */
'use strict';

const {
  create, createOptimal, add, mem, count, size, numHashes,
  popcount, saturation, falsePositiveRate, isEmpty, union,
  ofList, memAll, memAny, clear, copy, toString,
  _hash1, _hash2, _hashI, _getBit, _setBit,
} = require('../Try/scripts/bloomFilter');

describe('BloomFilter', () => {

  // ── Creation ────────────────────────────────────────
  describe('create', () => {
    test('creates with default parameters', () => {
      const bf = create();
      expect(size(bf)).toBe(1024);
      expect(numHashes(bf)).toBe(7);
      expect(count(bf)).toBe(0);
      expect(isEmpty(bf)).toBe(true);
    });

    test('creates with custom m and k', () => {
      const bf = create({ m: 256, k: 3 });
      expect(size(bf)).toBe(256);
      expect(numHashes(bf)).toBe(3);
    });

    test('clamps m to minimum 8', () => {
      const bf = create({ m: 2 });
      expect(size(bf)).toBe(8);
    });

    test('clamps k to minimum 1', () => {
      const bf = create({ k: 0 });
      expect(numHashes(bf)).toBe(1);
    });

    test('negative m is clamped to 8', () => {
      const bf = create({ m: -100 });
      expect(size(bf)).toBe(8);
    });

    test('bits array is correctly sized', () => {
      const bf = create({ m: 17 }); // 17 bits = 3 bytes
      expect(bf.bits.length).toBe(3);
    });

    test('all bits are initially zero', () => {
      const bf = create({ m: 64 });
      expect(bf.bits.every(b => b === 0)).toBe(true);
    });
  });

  // ── createOptimal ────────────────────────────────────
  describe('createOptimal', () => {
    test('creates filter for given parameters', () => {
      const bf = createOptimal(100, 0.01);
      expect(size(bf)).toBeGreaterThan(0);
      expect(numHashes(bf)).toBeGreaterThan(0);
      expect(count(bf)).toBe(0);
    });

    test('larger expected elements = larger filter', () => {
      const small = createOptimal(10, 0.01);
      const large = createOptimal(1000, 0.01);
      expect(size(large)).toBeGreaterThan(size(small));
    });

    test('lower fp rate = larger filter', () => {
      const loose = createOptimal(100, 0.1);
      const tight = createOptimal(100, 0.001);
      expect(size(tight)).toBeGreaterThan(size(loose));
    });

    test('clamps fp rate to valid range', () => {
      const bf = createOptimal(10, 0);
      expect(size(bf)).toBeGreaterThan(0);
    });
  });

  // ── add / mem ────────────────────────────────────────
  describe('add and mem', () => {
    test('added element is possibly present', () => {
      let bf = create({ m: 256, k: 5 });
      bf = add('hello', bf);
      expect(mem('hello', bf)).toBe(true);
    });

    test('non-added element is probably absent', () => {
      let bf = create({ m: 1024, k: 7 });
      bf = add('hello', bf);
      expect(mem('definitely-not-here-xyz-999', bf)).toBe(false);
    });

    test('multiple elements are all findable', () => {
      let bf = create({ m: 2048, k: 7 });
      const items = ['apple', 'banana', 'cherry', 'date', 'elderberry'];
      items.forEach(item => { bf = add(item, bf); });
      items.forEach(item => {
        expect(mem(item, bf)).toBe(true);
      });
    });

    test('count increments with each add', () => {
      let bf = create();
      expect(count(bf)).toBe(0);
      bf = add('a', bf);
      expect(count(bf)).toBe(1);
      bf = add('b', bf);
      expect(count(bf)).toBe(2);
    });

    test('add is immutable — does not modify original', () => {
      const bf1 = create({ m: 256, k: 3 });
      const bf2 = add('test', bf1);
      expect(count(bf1)).toBe(0);
      expect(count(bf2)).toBe(1);
      expect(mem('test', bf1)).toBe(false);
      expect(mem('test', bf2)).toBe(true);
    });

    test('numeric elements work', () => {
      let bf = create({ m: 512, k: 5 });
      bf = add(42, bf);
      bf = add(100, bf);
      expect(mem(42, bf)).toBe(true);
      expect(mem(100, bf)).toBe(true);
    });
  });

  // ── No false negatives (core Bloom filter guarantee) ──
  describe('no false negatives', () => {
    test('1000 elements — all found after insertion', () => {
      let bf = create({ m: 16384, k: 7 });
      const items = [];
      for (let i = 0; i < 1000; i++) {
        items.push(`item-${i}`);
        bf = add(`item-${i}`, bf);
      }
      const allFound = items.every(item => mem(item, bf));
      expect(allFound).toBe(true);
    });
  });

  // ── False positive rate ──────────────────────────────
  describe('false positive rate', () => {
    test('empty filter has 0 false positive rate', () => {
      const bf = create();
      expect(falsePositiveRate(bf)).toBe(0.0);
    });

    test('rate increases as elements are added', () => {
      let bf1 = create({ m: 256, k: 5 });
      bf1 = add('a', bf1);
      let bf2 = create({ m: 256, k: 5 });
      for (let i = 0; i < 50; i++) bf2 = add(`item-${i}`, bf2);
      expect(falsePositiveRate(bf2)).toBeGreaterThan(falsePositiveRate(bf1));
    });

    test('rate is between 0 and 1', () => {
      let bf = create({ m: 128, k: 3 });
      for (let i = 0; i < 20; i++) bf = add(`x${i}`, bf);
      const rate = falsePositiveRate(bf);
      expect(rate).toBeGreaterThan(0);
      expect(rate).toBeLessThanOrEqual(1);
    });
  });

  // ── popcount / saturation ────────────────────────────
  describe('popcount and saturation', () => {
    test('empty filter has popcount 0', () => {
      const bf = create();
      expect(popcount(bf)).toBe(0);
    });

    test('popcount increases after add', () => {
      let bf = create({ m: 256, k: 5 });
      const pc0 = popcount(bf);
      bf = add('hello', bf);
      expect(popcount(bf)).toBeGreaterThan(pc0);
    });

    test('popcount is at most m', () => {
      let bf = create({ m: 64, k: 3 });
      for (let i = 0; i < 100; i++) bf = add(`x${i}`, bf);
      expect(popcount(bf)).toBeLessThanOrEqual(64);
    });

    test('empty filter has saturation 0', () => {
      const bf = create();
      expect(saturation(bf)).toBe(0);
    });

    test('saturation is between 0 and 1', () => {
      let bf = create({ m: 128, k: 3 });
      for (let i = 0; i < 30; i++) bf = add(`s${i}`, bf);
      const s = saturation(bf);
      expect(s).toBeGreaterThan(0);
      expect(s).toBeLessThanOrEqual(1);
    });

    test('heavily loaded filter has high saturation', () => {
      let bf = create({ m: 32, k: 2 });
      for (let i = 0; i < 100; i++) bf = add(`heavy-${i}`, bf);
      expect(saturation(bf)).toBeGreaterThan(0.8);
    });
  });

  // ── isEmpty ──────────────────────────────────────────
  describe('isEmpty', () => {
    test('new filter is empty', () => {
      expect(isEmpty(create())).toBe(true);
    });

    test('filter with elements is not empty', () => {
      const bf = add('x', create());
      expect(isEmpty(bf)).toBe(false);
    });
  });

  // ── union ────────────────────────────────────────────
  describe('union', () => {
    test('union of two filters contains both elements', () => {
      let bf1 = create({ m: 512, k: 5 });
      bf1 = add('alpha', bf1);
      let bf2 = create({ m: 512, k: 5 });
      bf2 = add('beta', bf2);
      const combined = union(bf1, bf2);
      expect(mem('alpha', combined)).toBe(true);
      expect(mem('beta', combined)).toBe(true);
    });

    test('union count is sum of individual counts', () => {
      let bf1 = add('a', create({ m: 256, k: 3 }));
      let bf2 = add('b', add('c', create({ m: 256, k: 3 })));
      const combined = union(bf1, bf2);
      expect(count(combined)).toBe(3);
    });

    test('union throws for incompatible m', () => {
      const bf1 = create({ m: 128, k: 3 });
      const bf2 = create({ m: 256, k: 3 });
      expect(() => union(bf1, bf2)).toThrow('incompatible');
    });

    test('union throws for incompatible k', () => {
      const bf1 = create({ m: 256, k: 3 });
      const bf2 = create({ m: 256, k: 5 });
      expect(() => union(bf1, bf2)).toThrow('incompatible');
    });

    test('union with empty filter preserves original', () => {
      let bf1 = add('only-here', create({ m: 256, k: 3 }));
      const bf2 = create({ m: 256, k: 3 });
      const combined = union(bf1, bf2);
      expect(mem('only-here', combined)).toBe(true);
    });
  });

  // ── ofList ───────────────────────────────────────────
  describe('ofList', () => {
    test('creates filter from list', () => {
      const bf = ofList(['x', 'y', 'z'], { m: 512, k: 5 });
      expect(mem('x', bf)).toBe(true);
      expect(mem('y', bf)).toBe(true);
      expect(mem('z', bf)).toBe(true);
      expect(count(bf)).toBe(3);
    });

    test('empty list creates empty filter', () => {
      const bf = ofList([]);
      expect(isEmpty(bf)).toBe(true);
    });
  });

  // ── memAll / memAny ──────────────────────────────────
  describe('memAll and memAny', () => {
    test('memAll returns true when all present', () => {
      const bf = ofList(['a', 'b', 'c'], { m: 1024, k: 7 });
      expect(memAll(['a', 'b', 'c'], bf)).toBe(true);
    });

    test('memAll returns false when one is missing', () => {
      const bf = ofList(['a', 'b'], { m: 2048, k: 7 });
      expect(memAll(['a', 'missing-element-xyz'], bf)).toBe(false);
    });

    test('memAny returns true when at least one present', () => {
      const bf = ofList(['a', 'b'], { m: 1024, k: 7 });
      expect(memAny(['x-not-here', 'a'], bf)).toBe(true);
    });

    test('memAny returns false when none present', () => {
      const bf = ofList(['a', 'b'], { m: 2048, k: 7 });
      expect(memAny(['no-1-xyz', 'no-2-abc'], bf)).toBe(false);
    });

    test('memAll on empty list returns true', () => {
      const bf = create();
      expect(memAll([], bf)).toBe(true);
    });

    test('memAny on empty list returns false', () => {
      const bf = create();
      expect(memAny([], bf)).toBe(false);
    });
  });

  // ── clear / copy ─────────────────────────────────────
  describe('clear and copy', () => {
    test('clear produces empty filter with same m and k', () => {
      let bf = ofList(['a', 'b', 'c'], { m: 512, k: 5 });
      const cleared = clear(bf);
      expect(size(cleared)).toBe(512);
      expect(numHashes(cleared)).toBe(5);
      expect(count(cleared)).toBe(0);
      expect(isEmpty(cleared)).toBe(true);
    });

    test('copy produces identical filter', () => {
      let bf = ofList(['x', 'y'], { m: 256, k: 3 });
      const cp = copy(bf);
      expect(count(cp)).toBe(count(bf));
      expect(size(cp)).toBe(size(bf));
      expect(numHashes(cp)).toBe(numHashes(bf));
      expect(mem('x', cp)).toBe(true);
      expect(mem('y', cp)).toBe(true);
    });

    test('copy is independent — modifying copy does not affect original', () => {
      const bf = ofList(['a'], { m: 256, k: 3 });
      const cp = copy(bf);
      const cp2 = add('b', cp);
      expect(mem('b', cp2)).toBe(true);
      expect(count(bf)).toBe(1);
    });
  });

  // ── toString ─────────────────────────────────────────
  describe('toString', () => {
    test('includes m, k, n, and saturation', () => {
      const bf = create({ m: 128, k: 4 });
      const s = toString(bf);
      expect(s).toContain('m=128');
      expect(s).toContain('k=4');
      expect(s).toContain('n=0');
      expect(s).toContain('saturation=');
    });

    test('format matches BloomFilter(m=..., k=..., n=..., saturation=...%)', () => {
      const bf = add('x', create({ m: 64, k: 2 }));
      const s = toString(bf);
      expect(s).toMatch(/^BloomFilter\(m=\d+, k=\d+, n=\d+, saturation=[\d.]+%\)$/);
    });
  });

  // ── Internal helpers ─────────────────────────────────
  describe('internal helpers', () => {
    test('hash1 returns consistent values', () => {
      expect(_hash1('test')).toBe(_hash1('test'));
    });

    test('hash2 returns consistent values', () => {
      expect(_hash2('test')).toBe(_hash2('test'));
    });

    test('hash1 and hash2 produce different values', () => {
      expect(_hash1('hello')).not.toBe(_hash2('hello'));
    });

    test('hashI produces values in [0, m)', () => {
      for (let i = 0; i < 20; i++) {
        const idx = _hashI(100, 12345, 67890, i);
        expect(idx).toBeGreaterThanOrEqual(0);
        expect(idx).toBeLessThan(100);
      }
    });

    test('getBit / setBit round-trip', () => {
      const bits = new Uint8Array(4);
      expect(_getBit(bits, 5)).toBe(false);
      _setBit(bits, 5);
      expect(_getBit(bits, 5)).toBe(true);
      expect(_getBit(bits, 4)).toBe(false);
      expect(_getBit(bits, 6)).toBe(false);
    });

    test('setBit is idempotent', () => {
      const bits = new Uint8Array(2);
      _setBit(bits, 10);
      const after1 = bits[1];
      _setBit(bits, 10);
      expect(bits[1]).toBe(after1);
    });
  });

  // ── Edge cases ───────────────────────────────────────
  describe('edge cases', () => {
    test('minimum filter (m=8, k=1)', () => {
      let bf = create({ m: 8, k: 1 });
      bf = add('x', bf);
      expect(mem('x', bf)).toBe(true);
      expect(size(bf)).toBe(8);
      expect(numHashes(bf)).toBe(1);
    });

    test('adding same element twice increments count', () => {
      let bf = create({ m: 256, k: 3 });
      bf = add('dup', bf);
      bf = add('dup', bf);
      expect(count(bf)).toBe(2);
      expect(mem('dup', bf)).toBe(true);
    });

    test('empty string as element', () => {
      let bf = create({ m: 256, k: 5 });
      bf = add('', bf);
      expect(mem('', bf)).toBe(true);
    });

    test('very large k value', () => {
      let bf = create({ m: 1024, k: 100 });
      bf = add('test', bf);
      expect(mem('test', bf)).toBe(true);
    });

    test('popcount handles non-byte-aligned m', () => {
      let bf = create({ m: 13, k: 2 });
      const pc = popcount(bf);
      expect(pc).toBe(0);
    });

    test('union of two empty filters is empty', () => {
      const bf1 = create({ m: 128, k: 3 });
      const bf2 = create({ m: 128, k: 3 });
      const combined = union(bf1, bf2);
      expect(isEmpty(combined)).toBe(true);
      expect(popcount(combined)).toBe(0);
    });
  });

  // ── Statistical properties ───────────────────────────
  describe('statistical properties', () => {
    test('false positive rate is close to theoretical for optimal filter', () => {
      const targetFP = 0.01;
      let bf = createOptimal(100, targetFP);
      for (let i = 0; i < 100; i++) bf = add(`element-${i}`, bf);

      let falsePositives = 0;
      for (let i = 0; i < 1000; i++) {
        if (mem(`non-member-${i}`, bf)) falsePositives++;
      }
      const empiricalFP = falsePositives / 1000;
      expect(empiricalFP).toBeLessThan(targetFP * 5);
    });

    test('theoretical rate tracks saturation', () => {
      let bf = create({ m: 256, k: 5 });
      const rates = [];
      for (let i = 0; i < 50; i++) {
        bf = add(`item-${i}`, bf);
        rates.push(falsePositiveRate(bf));
      }
      for (let i = 1; i < rates.length; i++) {
        expect(rates[i]).toBeGreaterThanOrEqual(rates[i - 1]);
      }
    });
  });
});
