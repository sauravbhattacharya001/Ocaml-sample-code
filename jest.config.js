/**
 * Jest configuration.
 *
 * `__tests__/` holds the real Jest test suites (jsdom-based UI tests +
 * unit tests). `tests/` historically holds standalone Node smoke scripts
 * that are *not* Jest tests — most are executed directly via
 * `node tests/<file>.js` and several call `process.exit(...)` at the
 * top level, which Jest must not pick up.
 *
 * We ignore `tests/` so `npm test` is deterministic and doesn't accidentally
 * execute the standalone scripts.
 */
module.exports = {
  testPathIgnorePatterns: ['/node_modules/', '/tests/'],
};
