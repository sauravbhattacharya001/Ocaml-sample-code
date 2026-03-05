'use strict';

const {
  createCostEstimator,
  DEFAULT_MATERIAL_PRICES,
  DEFAULT_CONSUMABLE_PRICES,
  MACHINE_PROFILES,
  LABOR_PROFILES,
} = require('../Try/scripts/costEstimator');

describe('costEstimator', () => {
  let estimator;

  beforeEach(() => {
    estimator = createCostEstimator();
  });

  // ── Constants ─────────────────────────────────────────────

  describe('constants', () => {
    test('DEFAULT_MATERIAL_PRICES has bioinks', () => {
      expect(DEFAULT_MATERIAL_PRICES['GelMA 5%']).toBeDefined();
      expect(DEFAULT_MATERIAL_PRICES['GelMA 5%'].pricePerMl).toBeGreaterThan(0);
      expect(DEFAULT_MATERIAL_PRICES['GelMA 5%'].category).toBe('bioink');
    });

    test('DEFAULT_MATERIAL_PRICES has crosslinkers', () => {
      expect(DEFAULT_MATERIAL_PRICES['CaCl2 100mM']).toBeDefined();
      expect(DEFAULT_MATERIAL_PRICES['CaCl2 100mM'].category).toBe('crosslinker');
    });

    test('DEFAULT_CONSUMABLE_PRICES has needles', () => {
      expect(DEFAULT_CONSUMABLE_PRICES['needle_22G']).toBeDefined();
      expect(DEFAULT_CONSUMABLE_PRICES['needle_22G'].pricePerUnit).toBeGreaterThan(0);
    });

    test('MACHINE_PROFILES has entries', () => {
      expect(MACHINE_PROFILES['BioBots 1']).toBeDefined();
      expect(MACHINE_PROFILES['Generic']).toBeDefined();
      expect(MACHINE_PROFILES['BioBots 1'].hourlyRate).toBeGreaterThan(0);
    });

    test('LABOR_PROFILES has roles', () => {
      expect(LABOR_PROFILES['technician']).toBeDefined();
      expect(LABOR_PROFILES['researcher']).toBeDefined();
      expect(LABOR_PROFILES['technician'].hourlyRate).toBeGreaterThan(0);
    });
  });

  // ── Basic estimate ────────────────────────────────────────

  describe('estimate', () => {
    test('minimal params returns valid cost', () => {
      const result = estimator.estimate({ printTimeMin: 30 });
      expect(result.totalCost).toBeGreaterThan(0);
      expect(result.currency).toBe('USD');
      expect(result.breakdown).toBeDefined();
      expect(result.breakdown.materials).toBeDefined();
      expect(result.breakdown.machineTime).toBeDefined();
      expect(result.breakdown.energy).toBeDefined();
      expect(result.breakdown.consumables).toBeDefined();
      expect(result.breakdown.labor).toBeDefined();
    });

    test('throws on null params', () => {
      expect(() => estimator.estimate(null)).toThrow('params required');
    });

    test('throws on zero print time', () => {
      expect(() => estimator.estimate({ printTimeMin: 0 })).toThrow('printTimeMin must be positive');
    });

    test('throws on negative print time', () => {
      expect(() => estimator.estimate({ printTimeMin: -5 })).toThrow('printTimeMin must be positive');
    });

    test('includes material costs for bioinks', () => {
      const result = estimator.estimate({
        printTimeMin: 30,
        bioinks: [{ name: 'GelMA 5%', volumeMl: 2.0 }],
      });
      expect(result.breakdown.materials.total).toBeGreaterThan(0);
      expect(result.breakdown.materials.items.length).toBe(1);
      expect(result.breakdown.materials.items[0].name).toBe('GelMA 5%');
    });

    test('includes crosslinker costs', () => {
      const result = estimator.estimate({
        printTimeMin: 30,
        crosslinkers: [{ name: 'CaCl2 100mM', volumeMl: 5.0 }],
      });
      expect(result.breakdown.materials.total).toBeGreaterThan(0);
      const clItem = result.breakdown.materials.items.find(i => i.name === 'CaCl2 100mM');
      expect(clItem).toBeDefined();
      expect(clItem.category).toBe('crosslinker');
    });

    test('waste factor increases material cost', () => {
      const base = estimator.estimate({
        printTimeMin: 30,
        bioinks: [{ name: 'GelMA 5%', volumeMl: 1.0 }],
        wasteFactor: 1.0,
      });
      const withWaste = estimator.estimate({
        printTimeMin: 30,
        bioinks: [{ name: 'GelMA 5%', volumeMl: 1.0 }],
        wasteFactor: 1.30,
      });
      expect(withWaste.breakdown.materials.total).toBeGreaterThan(
        base.breakdown.materials.total
      );
    });

    test('machine time includes warmup and cooldown', () => {
      const result = estimator.estimate({
        printTimeMin: 60,
        machine: 'BioBots 1',
      });
      const mt = result.breakdown.machineTime;
      expect(mt.warmupMin).toBe(MACHINE_PROFILES['BioBots 1'].warmupMin);
      expect(mt.cooldownMin).toBe(MACHINE_PROFILES['BioBots 1'].cooldownMin);
      expect(mt.totalMin).toBe(60 + mt.warmupMin + mt.cooldownMin);
    });

    test('falls back to Generic machine', () => {
      const result = estimator.estimate({ printTimeMin: 30, machine: 'Unknown' });
      expect(result.breakdown.machineTime.hourlyRate).toBe(
        MACHINE_PROFILES['Generic'].hourlyRate
      );
    });

    test('energy cost computed from power and time', () => {
      const result = estimator.estimate({
        printTimeMin: 60,
        machine: 'BioBots 1',
      });
      expect(result.breakdown.energy.powerWatts).toBe(150);
      expect(result.breakdown.energy.kWh).toBeGreaterThan(0);
      expect(result.breakdown.energy.cost).toBeGreaterThan(0);
    });

    test('auto-detects consumables from needle gauge', () => {
      const result = estimator.estimate({
        printTimeMin: 30,
        needleGauge: 22,
      });
      const needleItem = result.breakdown.consumables.items.find(
        i => i.key === 'needle_22G'
      );
      expect(needleItem).toBeDefined();
      expect(needleItem.quantity).toBe(1);
    });

    test('auto-detects cartridge from bioink volume', () => {
      const result = estimator.estimate({
        printTimeMin: 30,
        bioinks: [{ name: 'Alginate 2%', volumeMl: 4.0 }],
      });
      const cartItem = result.breakdown.consumables.items.find(
        i => i.key.startsWith('cartridge_')
      );
      expect(cartItem).toBeDefined();
    });

    test('auto-detects labor with setup/monitor/post-process', () => {
      const result = estimator.estimate({ printTimeMin: 60 });
      expect(result.breakdown.labor.items.length).toBeGreaterThanOrEqual(2);
      expect(result.breakdown.labor.total).toBeGreaterThan(0);
    });

    test('cost per layer computed correctly', () => {
      const result = estimator.estimate({
        printTimeMin: 30,
        layerCount: 20,
      });
      expect(result.layerCount).toBe(20);
      expect(result.costPerLayer).toBeCloseTo(result.totalCost / 20, 1);
    });

    test('explicit consumables override auto-detect', () => {
      const result = estimator.estimate({
        printTimeMin: 30,
        consumables: [{ key: 'petri_60mm', quantity: 3 }],
      });
      expect(result.breakdown.consumables.items.length).toBe(1);
      expect(result.breakdown.consumables.items[0].key).toBe('petri_60mm');
      expect(result.breakdown.consumables.items[0].quantity).toBe(3);
    });

    test('explicit labor overrides auto-detect', () => {
      const result = estimator.estimate({
        printTimeMin: 30,
        labor: [{ role: 'pi', minutes: 120 }],
      });
      expect(result.breakdown.labor.items.length).toBe(1);
      expect(result.breakdown.labor.items[0].role).toBe('pi');
    });

    test('custom pricePerMl overrides database', () => {
      const result = estimator.estimate({
        printTimeMin: 30,
        bioinks: [{ name: 'CustomInk', volumeMl: 1.0, pricePerMl: 100 }],
        wasteFactor: 1.0,
      });
      expect(result.breakdown.materials.items[0].cost).toBe(100);
    });

    test('total is sum of all categories', () => {
      const result = estimator.estimate({
        printTimeMin: 30,
        bioinks: [{ name: 'Alginate 2%', volumeMl: 2.0 }],
        machine: 'BioBots 1',
        needleGauge: 25,
      });
      const sum = result.breakdown.materials.total +
                  result.breakdown.machineTime.cost +
                  result.breakdown.energy.cost +
                  result.breakdown.consumables.total +
                  result.breakdown.labor.total;
      expect(result.totalCost).toBeCloseTo(sum, 1);
    });
  });

  // ── Batch estimate ────────────────────────────────────────

  describe('batchEstimate', () => {
    test('returns results for all inputs', () => {
      const batch = estimator.batchEstimate([
        { printTimeMin: 30 },
        { printTimeMin: 60 },
        { printTimeMin: 90 },
      ]);
      expect(batch.results.length).toBe(3);
      expect(batch.summary.count).toBe(3);
    });

    test('summary statistics are correct', () => {
      const batch = estimator.batchEstimate([
        { printTimeMin: 30 },
        { printTimeMin: 60 },
      ]);
      expect(batch.summary.totalBatchCost).toBeCloseTo(
        batch.results[0].totalCost + batch.results[1].totalCost, 1
      );
      expect(batch.summary.minCost).toBeLessThanOrEqual(batch.summary.maxCost);
      expect(batch.summary.averageCost).toBeGreaterThan(0);
    });

    test('throws on empty list', () => {
      expect(() => estimator.batchEstimate([])).toThrow('non-empty');
    });

    test('results have index', () => {
      const batch = estimator.batchEstimate([
        { printTimeMin: 30 },
        { printTimeMin: 60 },
      ]);
      expect(batch.results[0].index).toBe(0);
      expect(batch.results[1].index).toBe(1);
    });
  });

  // ── Compare configurations ────────────────────────────────

  describe('compareConfigurations', () => {
    test('cheaper config identified', () => {
      const result = estimator.compareConfigurations(
        { printTimeMin: 30 },
        { printTimeMin: 120 }
      );
      expect(result.recommendation).toBe('CONFIG_A_CHEAPER');
      expect(result.difference).toBeGreaterThan(0);
      expect(result.percentChange).toBeGreaterThan(0);
    });

    test('equivalent configs when similar', () => {
      const result = estimator.compareConfigurations(
        { printTimeMin: 30 },
        { printTimeMin: 30 }
      );
      expect(result.recommendation).toBe('EQUIVALENT');
    });

    test('category diffs provided', () => {
      const result = estimator.compareConfigurations(
        { printTimeMin: 30, machine: 'BioBots 1' },
        { printTimeMin: 30, machine: 'Cellink BIO X' }
      );
      expect(result.categoryDiffs).toBeDefined();
      expect(result.categoryDiffs.machineTime).toBeDefined();
      expect(result.categoryDiffs.machineTime.configA).toBeGreaterThan(0);
      expect(result.categoryDiffs.machineTime.configB).toBeGreaterThan(0);
    });

    test('B cheaper than A detected', () => {
      const result = estimator.compareConfigurations(
        {
          printTimeMin: 60,
          bioinks: [{ name: 'Matrigel', volumeMl: 5.0 }],
        },
        {
          printTimeMin: 60,
          bioinks: [{ name: 'Alginate 2%', volumeMl: 5.0 }],
        }
      );
      expect(result.recommendation).toBe('CONFIG_B_CHEAPER');
      expect(result.difference).toBeLessThan(0);
    });
  });

  // ── Scale estimate ────────────────────────────────────────

  describe('scaleEstimate', () => {
    test('returns scaled costs for quantities', () => {
      const result = estimator.scaleEstimate(
        { printTimeMin: 30, bioinks: [{ name: 'Alginate 2%', volumeMl: 1.0 }] },
        [1, 5, 10, 50]
      );
      expect(result.scaled.length).toBe(4);
      expect(result.scaled[0].quantity).toBe(1);
      expect(result.scaled[1].quantity).toBe(5);
      expect(result.baseCost).toBeGreaterThan(0);
    });

    test('per-unit cost decreases at scale', () => {
      const result = estimator.scaleEstimate(
        { printTimeMin: 30 },
        [1, 100]
      );
      expect(result.scaled[1].perUnitCost).toBeLessThanOrEqual(
        result.scaled[0].perUnitCost
      );
    });

    test('throws on empty quantities', () => {
      expect(() => estimator.scaleEstimate({ printTimeMin: 30 }, [])).toThrow('non-empty');
    });
  });

  // ── List functions ────────────────────────────────────────

  describe('list functions', () => {
    test('listMaterials returns all materials', () => {
      const mats = estimator.listMaterials();
      expect(Object.keys(mats).length).toBeGreaterThan(10);
      expect(mats['GelMA 5%'].pricePerMl).toBe(12.50);
    });

    test('listConsumables returns all consumables', () => {
      const cons = estimator.listConsumables();
      expect(Object.keys(cons).length).toBeGreaterThan(10);
      expect(cons['needle_22G'].pricePerUnit).toBeGreaterThan(0);
    });

    test('listMachines returns all machines', () => {
      const machines = estimator.listMachines();
      expect(machines['BioBots 1']).toBeDefined();
      expect(machines['Generic']).toBeDefined();
    });

    test('listLaborRoles returns all roles', () => {
      const roles = estimator.listLaborRoles();
      expect(roles['technician']).toBeDefined();
      expect(roles['pi']).toBeDefined();
    });
  });

  // ── Custom options ────────────────────────────────────────

  describe('custom options', () => {
    test('custom currency', () => {
      const est = createCostEstimator({ currency: 'EUR' });
      const result = est.estimate({ printTimeMin: 30 });
      expect(result.currency).toBe('EUR');
    });

    test('custom energy rate', () => {
      const cheap = createCostEstimator({ energyRate: 0.05 });
      const expensive = createCostEstimator({ energyRate: 0.50 });
      const cheapResult = cheap.estimate({ printTimeMin: 60 });
      const expResult = expensive.estimate({ printTimeMin: 60 });
      expect(expResult.breakdown.energy.cost).toBeGreaterThan(
        cheapResult.breakdown.energy.cost
      );
    });

    test('custom material prices', () => {
      const est = createCostEstimator({
        customMaterials: {
          'SuperInk': { pricePerMl: 200.00, category: 'bioink' },
        },
      });
      const result = est.estimate({
        printTimeMin: 30,
        bioinks: [{ name: 'SuperInk', volumeMl: 1.0 }],
        wasteFactor: 1.0,
      });
      expect(result.breakdown.materials.items[0].cost).toBe(200);
    });
  });

  // ── Edge cases ────────────────────────────────────────────

  describe('edge cases', () => {
    test('no bioinks or crosslinkers is OK', () => {
      const result = estimator.estimate({ printTimeMin: 30 });
      expect(result.breakdown.materials.total).toBe(0);
    });

    test('unknown material uses zero price', () => {
      const result = estimator.estimate({
        printTimeMin: 30,
        bioinks: [{ name: 'UnknownInk', volumeMl: 5.0 }],
        wasteFactor: 1.0,
      });
      expect(result.breakdown.materials.items[0].cost).toBe(0);
    });

    test('large print time does not overflow', () => {
      const result = estimator.estimate({ printTimeMin: 10000 });
      expect(result.totalCost).toBeGreaterThan(0);
      expect(isFinite(result.totalCost)).toBe(true);
    });

    test('multiple bioinks sum correctly', () => {
      const result = estimator.estimate({
        printTimeMin: 30,
        bioinks: [
          { name: 'GelMA 5%', volumeMl: 1.0 },
          { name: 'Alginate 2%', volumeMl: 2.0 },
        ],
        wasteFactor: 1.0,
      });
      const expected = 12.50 + (3.20 * 2);
      expect(result.breakdown.materials.total).toBeCloseTo(expected, 1);
    });
  });
});
