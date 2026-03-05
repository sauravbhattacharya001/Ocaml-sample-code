'use strict';

/**
 * Bioprint Cost Estimator
 *
 * Estimates the total cost of a bioprinting job by accounting for:
 *   1. Material costs — bioink, crosslinker, support material, media
 *   2. Machine time — hourly rate × estimated print duration
 *   3. Energy — power consumption during printing + post-processing
 *   4. Consumables — needles, cartridges, petri dishes, well plates
 *   5. Labor — setup, monitoring, post-processing, QC
 *   6. Waste — failed prints, purging, calibration material
 *
 * Supports single prints, batch costing, and what-if comparisons.
 *
 * Usage:
 *   const { createCostEstimator } = require('./costEstimator');
 *   const estimator = createCostEstimator();
 *   const cost = estimator.estimate({
 *     bioinks: [{ name: 'GelMA 5%', volumeMl: 2.5 }],
 *     printTimeMin: 45,
 *     layerCount: 20,
 *     needleGauge: 22,
 *   });
 *   console.log(cost.totalCost, cost.breakdown);
 */

// ── Material Price Database (USD per mL / per unit) ─────────

const DEFAULT_MATERIAL_PRICES = Object.freeze({
  // Bioinks (per mL)
  'GelMA 5%':       { pricePerMl: 12.50, category: 'bioink' },
  'GelMA 10%':      { pricePerMl: 18.00, category: 'bioink' },
  'Alginate 2%':    { pricePerMl:  3.20, category: 'bioink' },
  'Alginate 4%':    { pricePerMl:  4.80, category: 'bioink' },
  'Collagen I':     { pricePerMl: 45.00, category: 'bioink' },
  'Fibrin':         { pricePerMl: 28.00, category: 'bioink' },
  'Hyaluronic Acid': { pricePerMl: 35.00, category: 'bioink' },
  'PEGDA':          { pricePerMl:  8.50, category: 'bioink' },
  'Matrigel':       { pricePerMl: 85.00, category: 'bioink' },
  'Silk Fibroin':   { pricePerMl: 22.00, category: 'bioink' },
  'Pluronic F-127': { pricePerMl:  2.80, category: 'support' },
  'dECM':           { pricePerMl: 95.00, category: 'bioink' },

  // Crosslinkers (per mL)
  'CaCl2 100mM':    { pricePerMl:  0.15, category: 'crosslinker' },
  'LAP photoinitiator': { pricePerMl: 5.00, category: 'crosslinker' },
  'Thrombin':       { pricePerMl: 18.00, category: 'crosslinker' },
  'Genipin':        { pricePerMl: 12.00, category: 'crosslinker' },

  // Cell culture media (per mL)
  'DMEM':           { pricePerMl: 0.08, category: 'media' },
  'RPMI-1640':      { pricePerMl: 0.09, category: 'media' },
  'FBS':            { pricePerMl: 1.20, category: 'media' },
});

// ── Consumable Price Database (USD per unit) ────────────────

const DEFAULT_CONSUMABLE_PRICES = Object.freeze({
  // Needles by gauge
  'needle_18G': { pricePerUnit: 0.45, description: '18G blunt needle' },
  'needle_20G': { pricePerUnit: 0.45, description: '20G blunt needle' },
  'needle_22G': { pricePerUnit: 0.50, description: '22G blunt needle' },
  'needle_25G': { pricePerUnit: 0.55, description: '25G blunt needle' },
  'needle_27G': { pricePerUnit: 0.65, description: '27G blunt needle' },
  'needle_30G': { pricePerUnit: 0.85, description: '30G blunt needle' },

  // Cartridges
  'cartridge_3ml':  { pricePerUnit: 2.50, description: '3mL syringe cartridge' },
  'cartridge_5ml':  { pricePerUnit: 3.00, description: '5mL syringe cartridge' },
  'cartridge_10ml': { pricePerUnit: 3.80, description: '10mL syringe cartridge' },
  'cartridge_30ml': { pricePerUnit: 5.50, description: '30mL syringe cartridge' },

  // Labware
  'petri_35mm':     { pricePerUnit: 0.85, description: '35mm petri dish' },
  'petri_60mm':     { pricePerUnit: 1.10, description: '60mm petri dish' },
  'petri_100mm':    { pricePerUnit: 1.50, description: '100mm petri dish' },
  'wellplate_6':    { pricePerUnit: 3.20, description: '6-well plate' },
  'wellplate_12':   { pricePerUnit: 3.80, description: '12-well plate' },
  'wellplate_24':   { pricePerUnit: 4.20, description: '24-well plate' },
  'wellplate_96':   { pricePerUnit: 5.50, description: '96-well plate' },
  'glass_slide':    { pricePerUnit: 0.60, description: 'glass coverslip' },
});

// ── Machine Profiles ────────────────────────────────────────

const MACHINE_PROFILES = Object.freeze({
  'BioBots 1': {
    hourlyRate: 15.00,
    powerWatts: 150,
    maxNozzles: 2,
    warmupMin: 10,
    cooldownMin: 5,
  },
  'BioBots 2': {
    hourlyRate: 25.00,
    powerWatts: 250,
    maxNozzles: 4,
    warmupMin: 8,
    cooldownMin: 5,
  },
  'Cellink BIO X': {
    hourlyRate: 35.00,
    powerWatts: 300,
    maxNozzles: 3,
    warmupMin: 15,
    cooldownMin: 10,
  },
  'Allevi 2': {
    hourlyRate: 20.00,
    powerWatts: 180,
    maxNozzles: 2,
    warmupMin: 12,
    cooldownMin: 5,
  },
  'Generic': {
    hourlyRate: 10.00,
    powerWatts: 200,
    maxNozzles: 1,
    warmupMin: 10,
    cooldownMin: 5,
  },
});

// ── Labor Rate Profiles ─────────────────────────────────────

const LABOR_PROFILES = Object.freeze({
  'technician':    { hourlyRate: 35.00,  label: 'Lab Technician' },
  'researcher':    { hourlyRate: 55.00,  label: 'Research Scientist' },
  'postdoc':       { hourlyRate: 45.00,  label: 'Postdoctoral Fellow' },
  'grad_student':  { hourlyRate: 25.00,  label: 'Graduate Student' },
  'pi':            { hourlyRate: 85.00,  label: 'Principal Investigator' },
});

// ── Energy Cost ─────────────────────────────────────────────

const DEFAULT_ENERGY_RATE = 0.12; // USD per kWh

// ── Core Estimator ──────────────────────────────────────────

function createCostEstimator(options) {
  const opts = options || {};
  const materialPrices = Object.assign(
    {}, DEFAULT_MATERIAL_PRICES, opts.customMaterials || {}
  );
  const consumablePrices = Object.assign(
    {}, DEFAULT_CONSUMABLE_PRICES, opts.customConsumables || {}
  );
  const energyRate = opts.energyRate || DEFAULT_ENERGY_RATE;
  const currency = opts.currency || 'USD';

  // ── Estimate material costs ────────

  function estimateMaterialCost(bioinks, crosslinkers, wasteFactor) {
    const waste = wasteFactor || 1.15; // 15% waste default
    let total = 0;
    const items = [];

    if (bioinks && bioinks.length > 0) {
      for (const ink of bioinks) {
        const name = ink.name;
        const vol = ink.volumeMl || 0;
        const profile = materialPrices[name];
        const pricePerMl = ink.pricePerMl || (profile ? profile.pricePerMl : 0);
        const cost = vol * pricePerMl * waste;
        total += cost;
        items.push({
          name: name,
          volumeMl: vol,
          pricePerMl: pricePerMl,
          wasteFactor: waste,
          cost: Math.round(cost * 100) / 100,
          category: profile ? profile.category : 'bioink',
        });
      }
    }

    if (crosslinkers && crosslinkers.length > 0) {
      for (const cl of crosslinkers) {
        const name = cl.name;
        const vol = cl.volumeMl || 0;
        const profile = materialPrices[name];
        const pricePerMl = cl.pricePerMl || (profile ? profile.pricePerMl : 0);
        const cost = vol * pricePerMl * waste;
        total += cost;
        items.push({
          name: name,
          volumeMl: vol,
          pricePerMl: pricePerMl,
          wasteFactor: waste,
          cost: Math.round(cost * 100) / 100,
          category: profile ? profile.category : 'crosslinker',
        });
      }
    }

    return { total: Math.round(total * 100) / 100, items: items };
  }

  // ── Estimate machine time cost ─────

  function estimateMachineTimeCost(printTimeMin, machineName) {
    const profile = MACHINE_PROFILES[machineName] || MACHINE_PROFILES['Generic'];
    const warmup = profile.warmupMin;
    const cooldown = profile.cooldownMin;
    const totalMin = warmup + printTimeMin + cooldown;
    const totalHours = totalMin / 60;
    const cost = totalHours * profile.hourlyRate;

    return {
      printTimeMin: printTimeMin,
      warmupMin: warmup,
      cooldownMin: cooldown,
      totalMin: totalMin,
      hourlyRate: profile.hourlyRate,
      cost: Math.round(cost * 100) / 100,
      machine: machineName || 'Generic',
    };
  }

  // ── Estimate energy cost ──────────

  function estimateEnergyCost(printTimeMin, machineName, postProcessMin) {
    const profile = MACHINE_PROFILES[machineName] || MACHINE_PROFILES['Generic'];
    const totalMin = (profile.warmupMin || 0) + printTimeMin +
                     (profile.cooldownMin || 0) + (postProcessMin || 0);
    const totalHours = totalMin / 60;
    const kWh = (profile.powerWatts / 1000) * totalHours;
    const cost = kWh * energyRate;

    return {
      powerWatts: profile.powerWatts,
      totalMin: totalMin,
      kWh: Math.round(kWh * 1000) / 1000,
      ratePerKwh: energyRate,
      cost: Math.round(cost * 100) / 100,
    };
  }

  // ── Estimate consumable costs ─────

  function estimateConsumableCost(consumables) {
    let total = 0;
    const items = [];

    if (!consumables || consumables.length === 0) return { total: 0, items: [] };

    for (const c of consumables) {
      const key = c.key || c.name;
      const qty = c.quantity || 1;
      const profile = consumablePrices[key];
      const pricePerUnit = c.pricePerUnit || (profile ? profile.pricePerUnit : 0);
      const cost = qty * pricePerUnit;
      total += cost;
      items.push({
        name: profile ? profile.description : key,
        key: key,
        quantity: qty,
        pricePerUnit: pricePerUnit,
        cost: Math.round(cost * 100) / 100,
      });
    }

    return { total: Math.round(total * 100) / 100, items: items };
  }

  // ── Estimate labor cost ──────────

  function estimateLaborCost(laborEntries) {
    let total = 0;
    const items = [];

    if (!laborEntries || laborEntries.length === 0) return { total: 0, items: [] };

    for (const entry of laborEntries) {
      const role = entry.role || 'technician';
      const profile = LABOR_PROFILES[role] || LABOR_PROFILES['technician'];
      const minutes = entry.minutes || 0;
      const hours = minutes / 60;
      const rate = entry.hourlyRate || profile.hourlyRate;
      const cost = hours * rate;
      total += cost;
      items.push({
        role: role,
        label: profile.label,
        minutes: minutes,
        hourlyRate: rate,
        cost: Math.round(cost * 100) / 100,
      });
    }

    return { total: Math.round(total * 100) / 100, items: items };
  }

  // ── Auto-detect consumables from print params ─────

  function autoDetectConsumables(params) {
    const consumables = [];

    // Needle based on gauge
    if (params.needleGauge) {
      const key = 'needle_' + params.needleGauge + 'G';
      if (consumablePrices[key]) {
        consumables.push({ key: key, quantity: params.needleCount || 1 });
      }
    }

    // Cartridge based on volume
    if (params.bioinks && params.bioinks.length > 0) {
      const totalVol = params.bioinks.reduce(function(s, b) {
        return s + (b.volumeMl || 0);
      }, 0);
      let cartKey = 'cartridge_3ml';
      if (totalVol > 5) cartKey = 'cartridge_10ml';
      else if (totalVol > 3) cartKey = 'cartridge_5ml';
      consumables.push({ key: cartKey, quantity: params.bioinks.length });
    }

    // Substrate
    if (params.substrate) {
      const key = params.substrate;
      if (consumablePrices[key]) {
        consumables.push({ key: key, quantity: params.substrateCount || 1 });
      }
    }

    return consumables;
  }

  // ── Auto-detect labor from print params ───────────

  function autoDetectLabor(params) {
    const labor = [];
    const printMin = params.printTimeMin || 30;

    // Setup time: ~15 min for simple, ~30 min for complex
    const setupMin = (params.bioinks && params.bioinks.length > 2) ? 30 : 15;
    labor.push({
      role: params.laborRole || 'technician',
      minutes: setupMin,
    });

    // Monitoring: ~10% of print time (operator checks)
    const monitorMin = Math.ceil(printMin * 0.1);
    if (monitorMin > 0) {
      labor.push({
        role: params.laborRole || 'technician',
        minutes: monitorMin,
      });
    }

    // Post-processing: crosslinking, washing, media change
    const postMin = params.postProcessingMin || 15;
    labor.push({
      role: params.laborRole || 'technician',
      minutes: postMin,
    });

    return labor;
  }

  // ── Full estimate ────────────────

  function estimate(params) {
    if (!params) throw new Error('params required');
    if (!params.printTimeMin || params.printTimeMin <= 0) {
      throw new Error('printTimeMin must be positive');
    }

    const machineName = params.machine || 'Generic';

    // Material costs
    const material = estimateMaterialCost(
      params.bioinks || [],
      params.crosslinkers || [],
      params.wasteFactor
    );

    // Machine time costs
    const machineTime = estimateMachineTimeCost(
      params.printTimeMin,
      machineName
    );

    // Energy costs
    const energy = estimateEnergyCost(
      params.printTimeMin,
      machineName,
      params.postProcessingMin || 0
    );

    // Consumables
    const consumables = estimateConsumableCost(
      params.consumables || autoDetectConsumables(params)
    );

    // Labor
    const labor = estimateLaborCost(
      params.labor || autoDetectLabor(params)
    );

    // Total
    const total = material.total + machineTime.cost + energy.cost +
                  consumables.total + labor.total;

    const breakdown = {
      materials:   material,
      machineTime: machineTime,
      energy:      energy,
      consumables: consumables,
      labor:       labor,
    };

    // Cost per layer
    const layerCount = params.layerCount || 1;
    const costPerLayer = total / layerCount;

    return {
      totalCost: Math.round(total * 100) / 100,
      currency: currency,
      costPerLayer: Math.round(costPerLayer * 100) / 100,
      layerCount: layerCount,
      breakdown: breakdown,
      params: {
        machine: machineName,
        printTimeMin: params.printTimeMin,
        bioinkCount: (params.bioinks || []).length,
        needleGauge: params.needleGauge || null,
      },
    };
  }

  // ── Batch estimate ───────────────

  function batchEstimate(paramsList) {
    if (!paramsList || paramsList.length === 0) {
      throw new Error('paramsList must be a non-empty array');
    }

    const results = paramsList.map(function(p, i) {
      const result = estimate(p);
      result.index = i;
      return result;
    });

    const costs = results.map(function(r) { return r.totalCost; });
    const totalBatch = costs.reduce(function(a, b) { return a + b; }, 0);
    const avgCost = totalBatch / results.length;
    const minCost = Math.min.apply(null, costs);
    const maxCost = Math.max.apply(null, costs);

    return {
      results: results,
      summary: {
        count: results.length,
        totalBatchCost: Math.round(totalBatch * 100) / 100,
        averageCost: Math.round(avgCost * 100) / 100,
        minCost: Math.round(minCost * 100) / 100,
        maxCost: Math.round(maxCost * 100) / 100,
        currency: currency,
      },
    };
  }

  // ── Compare two configurations ───

  function compareConfigurations(paramsA, paramsB) {
    const costA = estimate(paramsA);
    const costB = estimate(paramsB);

    const diff = costB.totalCost - costA.totalCost;
    const pctChange = costA.totalCost > 0
      ? Math.round((diff / costA.totalCost) * 10000) / 100
      : 0;

    const categoryDiffs = {};
    const categories = ['materials', 'machineTime', 'energy', 'consumables', 'labor'];
    for (const cat of categories) {
      const a = cat === 'machineTime'
        ? costA.breakdown[cat].cost
        : costA.breakdown[cat].total;
      const b = cat === 'machineTime'
        ? costB.breakdown[cat].cost
        : costB.breakdown[cat].total;
      categoryDiffs[cat] = {
        configA: Math.round(a * 100) / 100,
        configB: Math.round(b * 100) / 100,
        difference: Math.round((b - a) * 100) / 100,
      };
    }

    let recommendation;
    if (Math.abs(pctChange) < 2) {
      recommendation = 'EQUIVALENT';
    } else if (diff < 0) {
      recommendation = 'CONFIG_B_CHEAPER';
    } else {
      recommendation = 'CONFIG_A_CHEAPER';
    }

    return {
      configA: costA,
      configB: costB,
      difference: Math.round(diff * 100) / 100,
      percentChange: pctChange,
      categoryDiffs: categoryDiffs,
      recommendation: recommendation,
    };
  }

  // ── Scale estimate ───────────────

  function scaleEstimate(params, quantities) {
    if (!quantities || quantities.length === 0) {
      throw new Error('quantities must be a non-empty array');
    }

    const baseCost = estimate(params);
    const scaled = quantities.map(function(qty) {
      // Material and consumables scale linearly; machine/labor have setup overhead
      const materialScale = baseCost.breakdown.materials.total * qty;
      const consumableScale = baseCost.breakdown.consumables.total * qty;
      const machineScale = baseCost.breakdown.machineTime.cost * qty;
      const energyScale = baseCost.breakdown.energy.cost * qty;
      // Labor: setup is fixed, monitoring/post-process scales
      const laborItems = baseCost.breakdown.labor.items || [];
      let laborFixed = laborItems.length > 0 ? laborItems[0].cost : 0;
      let laborVariable = baseCost.breakdown.labor.total - laborFixed;
      const laborScale = laborFixed + (laborVariable * qty);

      const total = materialScale + consumableScale + machineScale +
                    energyScale + laborScale;
      const perUnit = total / qty;

      return {
        quantity: qty,
        totalCost: Math.round(total * 100) / 100,
        perUnitCost: Math.round(perUnit * 100) / 100,
        savingsPerUnit: Math.round((baseCost.totalCost - perUnit) * 100) / 100,
      };
    });

    return {
      baseCost: baseCost.totalCost,
      currency: currency,
      scaled: scaled,
    };
  }

  // ── List available items ─────────

  function listMaterials() {
    const result = {};
    for (const key of Object.keys(materialPrices)) {
      result[key] = {
        pricePerMl: materialPrices[key].pricePerMl,
        category: materialPrices[key].category,
      };
    }
    return result;
  }

  function listConsumables() {
    const result = {};
    for (const key of Object.keys(consumablePrices)) {
      result[key] = {
        pricePerUnit: consumablePrices[key].pricePerUnit,
        description: consumablePrices[key].description,
      };
    }
    return result;
  }

  function listMachines() {
    return Object.assign({}, MACHINE_PROFILES);
  }

  function listLaborRoles() {
    return Object.assign({}, LABOR_PROFILES);
  }

  // ── Public API ───────────────────

  return {
    estimate:               estimate,
    batchEstimate:          batchEstimate,
    compareConfigurations:  compareConfigurations,
    scaleEstimate:          scaleEstimate,
    listMaterials:          listMaterials,
    listConsumables:        listConsumables,
    listMachines:           listMachines,
    listLaborRoles:         listLaborRoles,
  };
}

// ── Exports ─────────────────────────────────────────────────

if (typeof module !== 'undefined' && module.exports) {
  module.exports = {
    createCostEstimator,
    DEFAULT_MATERIAL_PRICES,
    DEFAULT_CONSUMABLE_PRICES,
    MACHINE_PROFILES,
    LABOR_PROFILES,
  };
}
